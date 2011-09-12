/****************************************************************************[RelativeInduction.cc]
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

#include "minisat/simp/SimpSolver.h"
#include "minisat/mtl/Sort.h"
#include "tip/induction/Induction.h"

namespace Tip {

    namespace {

        class Clause {
            unsigned sz;
            Sig*     lits;
        public:
            unsigned cycle;

            template<class Lits>
            Clause(const Lits& xs, unsigned cycle_) : sz(xs.size()), cycle(cycle_)
            {
                lits = new Sig[sz];
                for (unsigned i = 0; i < sz; i++)
                    lits[i] = xs[i];
            }
            ~Clause(){ delete [] lits; }

            Clause(const Clause& c) : sz(c.sz), cycle(c.cycle)
            {
                delete [] lits;
                lits = new Sig[sz];
                for (unsigned i = 0; i < sz; i++)
                    lits[i] = c[i];
            }

            Sig      operator[](unsigned i) const { assert(i < sz); return lits[i]; }
            unsigned size() const { return sz; }
        };


        class Inputs {
            unsigned sz;
            lbool*   inputs;
        public:
            template<class Inps>
            Inputs(const Inps& is) : sz(is.size()){
                inputs = new lbool[sz];
                for (unsigned i = 0; i < sz; i++)
                    inputs[i] = is[i];
            }

            Inputs(const Inputs& is) : sz(is.sz){
                delete [] inputs;
                inputs = new lbool[sz];
                for (unsigned i = 0; i < sz; i++)
                    inputs[i] = is[i];
            }

            ~Inputs(){ delete [] inputs; }

            unsigned size() const { return sz; }
            lbool operator[](unsigned i) const { assert(i < sz); return inputs[i]; }
        };


        struct ScheduledClause : public Clause {
            Inputs           inputs;
            ScheduledClause* next;
            template<class Lits, class Inps>
            ScheduledClause(const Lits& xs, unsigned cycle_, const Inps& is, ScheduledClause* next_)
                : Clause(xs, cycle_), inputs(is), next(next_){}

            ScheduledClause(const ScheduledClause& sc)
                : Clause(sc), inputs(sc.inputs), next(sc.next){}

            // TODO:
            // ~ScheduledClause()
            // {
            // ???
            // }
        };

        //===================================================================================================
        // Temporal Relative Induction Prover
        class Trip {
            TipCirc&             tip;

            // Solver independent data:
            // ClauseSet            cset;
            // vec<vec<ClauseRef> > F;
            vec<vec<Clause*> >          F;
            vec<vec<ScheduledClause*> > clause_queue;

            // Solver data. Should be rederivable from only independent data:
            SimpSolver           init;
            GMap<Lit>            init_map;

            SimpSolver           step;
            GMap<Lit>            step_map;
            vec<Lit>             step_tags;

            SimpSolver           prop;
            GMap<Lit>            prop_map;
            Lit                  prop_tag;

            void                 mkInitInstance();
            void                 mkStepInstance();
            void                 mkPropInstance();


            // PROVE:   Init ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in cycle 1,
            //       or False and the starting point of a counter-example trace.
            bool             proveInit(const Clause& c, Clause*& true_d, ScheduledClause*& false_trace);

            // PROVE:   let k = c.cycle: F[k-1] ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in some cycle >= k,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveStep(const Clause& c, Clause*& true_d, ScheduledClause*& false_trace);

            // PROVE:   let k = F.size()-1: F[k] ^ Trans => prop'
            // RETURNS: True and a new frame F[k+1] can be opened,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveProp(Sig prop, ScheduledClause*& false_trace);

            // Prove all scheduled clauses. Returns true if all properties are decided, and false otherwise.
            bool             propagate    ();

            // Try to push clauses forwards, particularily push clauses forward into the newly opened last
            // frame. Returns true if an invariant is found and false otherwise.
            bool             push         ();

            // Add a proved clause 'c'. Returns true if this causes an invariant to be found, and false
            // otherwise.
            bool             addClause    (Clause* c);

            // Check if clause 'c' is subsumed by any previously proved clause. Returns true if it is and
            // false otherwise.
            bool             fwdSubsumed  (Clause* c);

            // Find and remove all previously proved claues that are subsumed by the new clause 'c'. If an
            // invariant is found true is returned, otherwise false.
            bool             bwdSubsume   (Clause* c);

            void             enqueueClause(ScheduledClause* sc);
            ScheduledClause* getMinClause ();

            // Returns the failing property, extracts the trace that leads to the failure, and removes all
            // scheduled clauses rooted in the same property.
            SafeProp         extractTrace (ScheduledClause* trace, vec<vec<lbool> >& frames);

        public:
            Trip(TipCirc& tip_) : tip(tip_)
            {
                F.push();
            }

            // Prove or disprove all properties using depth k. Returns true if all properties are decided, and
            // false if there are still some unresolved property.
            bool decideCycle();

            // Prove that the necessary number of initial cycles are bug free. Returns true if all properties
            // are resolved (i.e. all properties were falsifiable), and false otherwise.
            bool baseCase();

            void printStats();
        };


        void Trip::mkInitInstance()
        {
        }


        void Trip::mkStepInstance()
        {
        }


        void Trip::mkPropInstance()
        {
        }


        void Trip::enqueueClause(ScheduledClause* sc)
        {
            clause_queue.growTo(sc->cycle+1);
            clause_queue[sc->cycle].push(sc);
        }


        ScheduledClause* Trip::getMinClause()
        {
            // Naive implementation:
            int i;
            for (i = 0; i < clause_queue.size() && clause_queue[i].size() == 0; i++)
                ;

            if (i == clause_queue.size())
                return NULL;

            ScheduledClause* result = clause_queue[i].last();
            clause_queue[i].pop();
            return result;
        }


        bool Trip::addClause(Clause* c)
        {
            assert(!fwdSubsumed(c));
            F[c->cycle].push(c);
            return bwdSubsume(c);
        }
        

        bool Trip::fwdSubsumed(Clause* c)
        {
            return false;
        }
        

        bool Trip::bwdSubsume(Clause* c)
        {
            return false;
        }


        bool Trip::propagate()
        {
            for (;;){
                ScheduledClause* sc = getMinClause();

                if (sc == NULL)
                    break;

                ScheduledClause* pred;
                Clause*          minimized;

                if (sc->cycle == 0){
                    // Handle initial cycle:
                    if (proveInit(*sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized->cycle+1;
                        if (sc->cycle < (unsigned)F.size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        Trace             cex    = tip.newTrace();
                        vec<vec<lbool> >& frames = tip.traces[cex].frames;
                        SafeProp          p      = extractTrace(pred, frames);
                        tip.safe_props[p].stat   = pstat_Falsified;
                        tip.safe_props[p].cex    = cex;
                        delete sc;
                        delete pred;
                    }

                }else{
                    // Handle arbitrary non-initial cycle:
                    if (proveStep(*sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized->cycle+1;
                        if (sc->cycle < (unsigned)F.size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        enqueueClause(pred);
                        enqueueClause(sc);
                    }
                }
            }

            return false;
        }


        bool Trip::decideCycle()
        {
            ScheduledClause* pred;
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat != pstat_Unknown)
                    if (!proveProp(tip.safe_props[p].sig, pred)){
                        enqueueClause(pred);
                        if (propagate())
                            return true;
                    }

            // At this point we know that all properties are implied in cycle k+1. Expand a new frame and push
            // clauses forward as much as possible:
            F.push();
            return push();
        }


        void Trip::printStats()
        {
            printf("%d: ", F.size());
            for (int i = 0; i < F.size(); i++)
                printf("%d ", F[i].size());
        }

    };




    void relativeInduction(TipCirc& tip)
    {
        Trip trip(tip);

        if (!trip.baseCase())
            while (!trip.decideCycle())
                trip.printStats();
    }


//=================================================================================================
} // namespace Tip
