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

#include "tip/induction/TripTypes.h"

namespace Tip {

    //===================================================================================================
    // Helper class, should maybe be internal later:
    class InstanceModel {
        vec<Lit> inputs;
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


    //===================================================================================================
    class InitInstance {
        const TipCirc& tip;
        
        SimpSolver*    solver;
        GMap<Lit>      umapl[2];
        vec<Lit>       inputs;
        
        void reset();
        
    public:
        InitInstance(const TipCirc& t_);
        ~InitInstance();
        
        bool prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next = NULL);
    };


    //===================================================================================================
    class PropInstance {
        const TipCirc&            tip;
        const vec<vec<Clause*> >& F;
        
        SimpSolver*         solver;
        GMap<Lit>           umapl[2];
        vec<Lit>            inputs;
        Lit                 trigg;
        
        void reset();
        lbool evaluate(const InstanceModel& model, Sig p);

    public:
        void clearClauses();
        void addClause   (const Clause& c);
        
        PropInstance(const TipCirc& t, const vec<vec<Clause*> >& F_);
        ~PropInstance();
        
        lbool prove(Sig p, ScheduledClause*& no, unsigned cycle);
    };


    //===================================================================================================
    class StepInstance {
        const TipCirc&            tip;
        const vec<vec<Clause*> >& F;
        
        SimpSolver*    solver;
        GMap<Lit>      umapl;
        vec<Lit>       inputs;
        vec<Lit>       outputs;
        vec<Lit>       activate;
        
        void reset();
        void evaluate(const InstanceModel& model, vec<Sig>& clause);
        
    public:
        void addClause(const Clause& c);

        StepInstance(const TipCirc& t, const vec<vec<Clause*> >& F_);
        ~StepInstance();
        
        bool prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next = NULL);
    };
    
//=================================================================================================
} // namespace Tip
#endif
