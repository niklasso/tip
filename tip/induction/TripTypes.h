/*************************************************************************************[TripTypes.h]
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

#ifndef Tip_TripTypes_h
#define Tip_TripTypes_h

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "tip/TipCirc.h"

namespace Tip {

    typedef uint32_t Cycle;
    enum { cycle_Undef = UINT32_MAX };

    // A class to represent a clause over circuit signals (Sig):
    class Clause {
        unsigned sz     : 31;
        unsigned active :  1;
        Sig*     lits;
        
    public:
        Cycle cycle;
        
        template<class Lits>
        Clause(const Lits& xs, Cycle cycle_) : sz(xs.size()), active(1), cycle(cycle_)
        {
            lits = new Sig[sz];
            for (unsigned i = 0; i < sz; i++)
                lits[i] = xs[i];
            sort(lits, sz);
        }
        Clause() : sz(0), active(1), lits(NULL), cycle(0){}
        
        // Copy constructor:
        Clause(const Clause& c) : sz(c.sz), active(c.active), cycle(c.cycle)
        {
            lits = new Sig[sz];
            for (unsigned i = 0; i < sz; i++)
                lits[i] = c[i];
        }
        
        // Assignment operator:
        Clause& operator=(const Clause& c){
            // this->~Clause();
            // new (this) Clause(c);
            delete [] lits;
            sz     = c.sz;
            active = c.active;
            cycle  = c.cycle;
            lits = new Sig[sz];
            for (unsigned i = 0; i < sz; i++)
                lits[i] = c[i];            
            return *this;
        }
        
        ~Clause(){ delete [] lits; }
        
        Sig      operator[](unsigned i) const { assert(i < sz); return lits[i]; }
        unsigned size      ()           const { return sz; }
        void     deactivate()                 { active = 0; }
        bool     isActive  ()           const { return active; }
    };

    // A class to represent circuit inputs for a time-frame:
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

        Inputs() : sz(0), inputs(NULL){}

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


    // A class to represent scheduled proof obligations for the relative induction algorithm. To
    // extract counter-example traces each scheduled clause has a pointer to the parent clause, and
    // the set of input values needed to connect them.
    struct ScheduledClause : public Clause {
        Inputs                 inputs;
        const ScheduledClause* next;
        template<class Lits, class Inps>
        ScheduledClause(const Lits& xs, Cycle cycle_, const Inps& is, const ScheduledClause* next_)
            : Clause(xs, cycle_), inputs(is), next(next_){}

        ScheduledClause() : next(NULL){}
    };

    // Check if clause 'c' subsumes 'd'. This means that 'c' is a subset of 'd' and 'c' holds
    // longer than (or as long as) 'd'.
    inline bool subsumes(const Clause& c, const Clause& d)
    {
        if (c.size() > d.size() || c.cycle < d.cycle)
            return false;

        unsigned i,j;
        for (i = j = 0; i < c.size(); j++)
            if (j == d.size() || c[i] < d[j])
                return false;
            else if (c[i] == d[j])
                i++;
        return true;
    }


    inline void printClause(const TipCirc& tip, const Clause& c)
    {
        printf("{ ");
        for (unsigned i = 0; i < c.size(); i++){
            if (i > 0) printf(", ");
            if (sign(c[i])) printf("~");
            if (tip.flps.isFlop(gate(c[i])))
                printf("f");
            else if (type(c[i]) == gtype_Inp)
                printf("i");
            else
                assert(false);
            printf("%d", tip.main.number(gate(c[i])));
        }
        if (c.cycle == cycle_Undef)
            printf(" }@inv");
        else
            printf(" }@%d", c.cycle);
    }


    // TODO: move this to some more general place?
#ifdef NDEBUG
#define check(x) x
#else
#define check(x) assert(x)
#endif
    
//=================================================================================================
} // namespace Tip
#endif
