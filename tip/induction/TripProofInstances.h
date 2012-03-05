/****************************************************************************[TripProofInstances.h]
Copyright (c) 2011, Niklas Sorensson
Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Tip_TripProofInstances_h
#define Tip_TripProofInstances_h

#include "minisat/simp/SimpSolver.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/TripTypes.h"

namespace Tip {

    //===================================================================================================
    // Helper class, should maybe be internal later:
    class InstanceModel {
        LMap<char> true_map;
        vec<Lit>   inputs;

    public:
        InstanceModel(const vec<Lit>& inps, const SimpSolver& s)
            {
                for (int i = 0; i < inps.size(); i++){
                    assert(s.modelValue(inps[i]) != l_Undef);
                    inputs.push(inps[i] ^ (s.modelValue(inps[i]) == l_False));
                }
            }
        InstanceModel(const vec<Lit>& inps){ copy(inps, inputs); }

        int   size      ()       const { return inputs.size(); }
        Lit   operator[](int i)  const { return inputs[i]; }
        void  copyTo    (vec<Lit>& out) const { inputs.copyTo(out); }

        lbool value     (Gate g, const GMap<Lit>& umap) const
        {
            // TODO: naive implementation for now.
            return find(inputs, umap[g]) ? l_True : find(inputs, ~umap[g]) ? l_False : l_Undef; 
        }
    };


    class LitSet {
        LMap<char> in_set;
        vec<Lit>   set;

        void clear()
        {
            for (int i = 0; i < set.size(); i++)
                in_set[set[i]] = 0;
            set.clear();
        }

    public:
        void fromModel(const vec<Lit>& xs, const SimpSolver& s)
        {
            clear();
            in_set.reserve(~mkLit(s.nVars()-1), 0);

            for (int i = 0; i < xs.size(); i++){
                assert(s.modelValue(xs[i]) != l_Undef);
                Lit x = xs[i] ^ (s.modelValue(xs[i]) == l_False);
                if (!has(x)){
                    set.push(x);
                    in_set[x] = 1;
                }
            }
        }

        void fromVec(const vec<Lit>& xs)
        {
            clear();
            for (int i = 0; i < xs.size(); i++){
                set.push(xs[i]);
                in_set.reserve(xs[i], 0);
                assert(in_set[xs[i]] == 0);
                in_set[xs[i]] = 1;
            }
        }

        int   size      ()       const { return set.size(); }
        Lit   operator[](int i)  const { return set[i]; }
        Lit   last      ()       const { return set.last(); }
        void  pop       ()             { 
            // Note: assumes that there were no duplicates in the 'set' vector:
            Lit x = set.last();
            set.pop();
            assert(in_set[x] == 1);
            in_set[x] = 0;
        }

        void  push      (Lit l){ 
            set.push(l);
            in_set.reserve(l, 0);
            assert(in_set[l] == 0);
            in_set[l] = 1;
        }

        void  copyTo    (vec<Lit>& out) const { set.copyTo(out); }

        lbool has(Var v) const { 
            if (in_set.has(mkLit(v)) && in_set[mkLit(v)])
                return l_True;
            else if (in_set.has(~mkLit(v)) && in_set[~mkLit(v)])
                return l_False;
            else
                return l_Undef;
        }

        bool  has(Lit l) const { return in_set.has(l) && in_set[l]; }
    };

    struct EventCounter {
        unsigned k;
        Sig      q;
        Sig      h;
        //EventCounter() : k(0), x(sig_True){}
    };


    //===================================================================================================
    class InitInstance {
        const TipCirc& tip;
        
        SimpSolver     solver;
        GMap<Lit>      umapl[2];
        vec<Lit>       inputs;
        LitSet         lset;
        double         cpu_time;
        int            cnf_level;  // Effort level for CNF simplification.
        
        void reset();
        
    public:
        InitInstance(const TipCirc& t_, int cnf_level_);
        ~InitInstance();
        
        bool prove(const Clause& c, const Clause& bot, Clause& yes, SharedRef<ScheduledClause>& no, SharedRef<ScheduledClause> next = NULL);
        bool prove(const Clause& c, const Clause& bot, Clause& yes);

        void reduceClause(Clause& c);

        void extendLiveness();

        uint64_t props();
        uint64_t solves();
        double   time();

        void printStats();
    };


    //===================================================================================================
    class PropInstance {
        const TipCirc&            tip;
        const vec<vec<Clause*> >& F;
        const vec<Clause*>&       F_inv;
        const vec<EventCounter>&  event_cnts;
        
        UnrolledCirc   uc;              // Unrolled circuit.
        SimpSolver     *solver;
        Clausifyer<SimpSolver>
                       *cl;             // Clausifyer for unrolled circuit.

        vec<vec<Sig> > needed_flops;    // Flops reachable from constraints or properties in each cycle.
        vec<Sig>       inputs;
        vec<Sig>       outputs;

        Lit            act_cycle;
        Lit            act_cnstrs;
        LitSet         lset;
        double         cpu_time;

        // Options:
        int            cnf_level;  // Effort level for CNF simplification.
    public:
        unsigned       depth;      // Depth of the unrolling.
        bool           use_ind;    // Use property in induction hypothesis.
    private:
        bool           use_uniq;   // Use unique state induction.
        
        //lbool evaluate(const InstanceModel& model, Sig p);
    public:
        void reset       (unsigned new_depth);

        void clearClauses();
        void addClause   (const Clause& c);
        
        PropInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, const vec<Clause*>& F_inv_, const vec<EventCounter>& event_cnts_,
                     int cnf_level_, int depth_, bool use_ind_, bool use_uniq_);
        ~PropInstance();
        
        lbool prove(Sig p, SharedRef<ScheduledClause>& no, unsigned cycle);

        void extendLiveness(Gate f, Sig f_next);

        uint64_t props();
        uint64_t solves();
        double   time();

        void printStats();
    };


    //===================================================================================================
    class StepInstance {
        const TipCirc&            tip;
        const vec<vec<Clause*> >& F;
        
        SimpSolver     solver;
        Clausifyer<SimpSolver> cl;
        GMap<Sig>      umap;
        Gate           prev_lastgate;
        vec<Sig>       inputs;
        vec<Sig>       outputs;

        vec<Lit>       activate;
        vec<unsigned>  cycle_clauses;
        Lit            act_cnstrs;
        LitSet         lset;
        double         cpu_time;
        int            cnf_level;  // Effort level for CNF simplification.
        
        void reset();
        void evaluate(vec<Sig>& clause);
        
    public:
        void addClause(const Clause& c);

        void resetCycle(unsigned cycle, unsigned num_clauses);

        StepInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, int cnf_level_);
        ~StepInstance();
        
        bool prove(const Clause& c, Clause& yes, SharedRef<ScheduledClause>& no, SharedRef<ScheduledClause> next = NULL);
        bool prove(const Clause& c, Clause& yes);

        void extendLiveness(Gate f, Sig f_next);

        uint64_t props();
        uint64_t solves();
        double   time();

        void printStats();
    };
    
//=================================================================================================
} // namespace Tip
#endif
