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
        const TipCirc&      tip;
        const vec<Clause*>& proved;
        
        SimpSolver*         solver;
        GMap<Lit>           umapl[2];
        vec<Lit>            inputs;
        vec<Lit>            outputs;
        
        void reset();
    public:
        void clearClauses();
        void addClause   (const Clause& c);
        
        PropInstance(const TipCirc& t, const vec<Clause*>& pr);
        ~PropInstance();
        
        bool prove(Sig p, ScheduledClause*& no, unsigned cycle);
    };


    //===================================================================================================
    class StepInstance {
        const TipCirc&      tip;
        const vec<Clause*>& proved;
        
        SimpSolver*    solver;
        GMap<Lit>      umapl;
        vec<Lit>       inputs;
        vec<Lit>       outputs;
        vec<Lit>       activate;
        
        void reset();
        
    public:
        void addClause(const Clause& c);

        StepInstance(const TipCirc& t, const vec<Clause*>& pr);
        ~StepInstance();
        
        bool prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next = NULL);
    };
    
//=================================================================================================
} // namespace Tip
#endif
