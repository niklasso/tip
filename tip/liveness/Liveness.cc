/*************************************************************************************[Liveness.cc]
Copyright (c) 2011, Niklas Sorensson, Koen Claessen

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

#include "minisat/core/Solver.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "tip/liveness/Liveness.h"
#include "tip/induction/Induction.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Liveness Checking:
//

void checkLiveness(TipCirc& tip, LiveProp p, int k)
{
    printf("=== Liveness checking of property #%d with k=%d ===\n", p, k);
        
    // preparing "just" signal
    Sig just = tip.live_props[p].sigs[0];
    if ( tip.cnstrs.size() > 0 ) {
        printf("Preparing for %d constraints.\n", tip.cnstrs.size());
        Sig conj = sig_True;
        for ( uint32_t i = 0; i < tip.cnstrs.size(); i++ ) {
            ;
            if ( tip.cnstrs[i].size() > 0 )
                for ( int j = 0; j < tip.cnstrs[i].size(); j++ )
                    conj = tip.main.mkAnd(conj, tip.main.mkOr(~(j > 0 ? tip.cnstrs[i][j-1] : tip.cnstrs[i].last()), tip.cnstrs[i][j]));
        }

        Gate next_conj = gate(tip.main.mkInp());
        Sig conj_ = tip.main.mkAnd(mkSig(next_conj), conj);
        tip.flps.define(next_conj, conj_, sig_True);
        just = tip.main.mkAnd(just, conj_);
    }
    
    Sig x = sig_True;
    for ( int i = 0; i < k; i++ ) {
        Gate y = gate(tip.main.mkInp());
        Sig justx = tip.main.mkAnd(just,x);
        tip.flps.define(y, tip.main.mkOr(justx,mkSig(y)));
        x = mkSig(y);
        tip.newSafeProp(~x);
    }
    printf("--- calling safety checker ---\n");
    relativeInduction(tip);
}

void checkLiveness(TipCirc& tip)
{
    for( LiveProp p = 0; p < tip.live_props.size(); p++ ) {
        printf("=== liveness property #%d\n", p);
        checkLiveness(tip, p, 10);
    }
}

};

