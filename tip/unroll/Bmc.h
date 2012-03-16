/*******************************************************************************************[Bmc.h]
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

#ifndef Tip_Bmc_h
#define Tip_Bmc_h

#include "mcl/Clausify.h"
#include "tip/TipCirc.h"
#include "tip/unroll/Unroll.h"

namespace Tip {

//=================================================================================================
// BMC classes:



class BasicBmc : public UnrolledCirc {
    TipCirc&           tip;
    double             solve_time;

    // Circ               uc;         // Unrolled circuit.
    // vec<IFrame>        ui;         // Unrolled set of input frames.
    // UnrollCirc         unroll;     // Unroller-helper object.
    // GMap<Sig>          umap;       // Reusable unroll-map.
    Solver             s;           // SAT-solver and clausifyer for unrolled circuit.
    Clausifyer<Solver> cl;

    int                cycle;       // Current cycle the circuit is unrolled to.
    bool               check_live;  // Indicates if liveness properties should be checked.
    unsigned           orig_nflops; // Original number of flops (to be used for loop detection).

    unsigned           unresolved_safety;
    unsigned           unresolved_liveness;

    struct LiveCycle {
        Lit      loop_now;     // True iff loop starts in this cycle.
        Lit      loop_before;  // True iff there was some loop starting in a previous cycle.
        vec<Lit> live_in_loop; // For each liveness property, true iff it was true some time during a loop.
    };

    vec<Lit>       looping_state;
    vec<LiveCycle> live_data;

    void nextLiveness();
    void extractTrace(vec<vec<lbool> >& frames);

public:
    BasicBmc(TipCirc& t, bool check_live_ = true);

    bool proveSig   (Sig x);
    void unrollCycle();
    void decideCycle();
    bool done       ();
    void printStats (bool final = false);

    uint64_t props  ();
    uint64_t solves ();
    double   time   ();
    int      depth  ();
};

//=================================================================================================
// Different BMC implementations:

void basicBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle, bool check_live = true);
void simpBmc (TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle);
void simpBmc2(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle);

//=================================================================================================

};

#endif
