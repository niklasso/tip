/********************************************************************************[EmbedFairness.cc]
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

#include "tip/liveness/EmbedFairness.h"
#include "minisat/mtl/Alg.h"

namespace Tip {

void embedFairness(TipCirc& tip)
{
    printf("Embedding fairness constraints...\n");
    for (LiveProp i = 0; i < tip.live_props.size(); i++) {
        if (tip.live_props[i].stat != pstat_Unknown)
            continue;

        // gather all justify constraints for this proof obligation
        vec<Sig> justs;
        append(tip.fairs,justs);
        append(tip.live_props[i].sigs,justs);
        int n = justs.size();
        printf("Joining %d triggers for liveness property #%d...\n", n, i);

        Sig accept = sig_True;
        // check if we have more than 1 signal to take care of
        // (this also works when n==0, in which case accept becomes sig_True)
        if (n != 1) {
            // (this method creates helper flops for every fairness signal
            // an alternative would be to do this once for all flops)

            // prepare the flops
            vec<Gate> flops;
            for (int j = 0; j < n; j++)
                flops.push(gate(tip.main.mkInp()));

            // create trigger signals and accept signal
            vec<Sig> triggers;
            accept = sig_True;
            for (int j = 0; j < n; j++) {
                triggers.push(tip.main.mkOr(justs[j],mkSig(flops[j])));
                accept = tip.main.mkAnd(accept, triggers[j]);
            }

            // define the flops
            //Sig reset = accept;  // old implementation
            Sig reset = tip.main.mkOr(tip.main.mkInp(),accept);
            for (int j = 0; j < n; j++)
                tip.flps.define(flops[j], tip.main.mkAnd(~reset, triggers[j]));
        }
        else
            accept = justs[0];

        // set the new accept signal
        tip.live_props[i].sigs.clear();
        tip.live_props[i].sigs.push(accept);
    }

    // clear fairness constraints (they are embedded in the liveness props now)
    tip.fairs.clear();
}

//=================================================================================================
} // namespace Tip

