/*************************************************************************************[BasicBmc.cc]
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

#include "minisat/core/Solver.h"
#include "minisat/utils/System.h"
#include "mcl/CircPrelude.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/unroll/Bmc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Implementation of Basic BMC:
//

void basicBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    double             time_before = cpuTime();
    double             solve_time  = 0;
    Circ               uc;                        // Unrolled circuit.
    vec<IFrame>        ui;                        // Unrolled set of input frames.
    UnrollCirc         unroll(tip, ui, uc, true); // Unroller-helper object.
    Solver             s;                         // SAT-solver and clausifyer for unrolled circuit.
    Clausifyer<Solver> cl(uc, s);
    GMap<Sig>          umap;                      // Reusable unroll-map.

    //s.verbosity = 1;
    for (uint32_t i = 0; i < stop_cycle; i++){
        unroll(umap);

        // Assert all constraints:
        for (unsigned j = 0; j < tip.cnstrs.size(); j++){
            Sig cx = tip.cnstrs[j][0];
            Lit lx = cl.clausify(umap[gate(cx)] ^ sign(cx));
            for (int k = 1; k < tip.cnstrs[j].size(); k++){
                Sig cy = tip.cnstrs[j][k];
                Lit ly = cl.clausify(umap[gate(cy)] ^ sign(cy));
                s.addClause(~lx, ly);
                s.addClause(~ly, lx);
            }
        }

        if (i < begin_cycle)
            continue;

        // Do SAT-tests:
        int unresolved_safety = 0;
        for (SafeProp p = 0; p < tip.safe_props.size(); p++){
            if (tip.safe_props[p].stat != pstat_Unknown)
                continue;
            
            Sig psig_orig   = tip.safe_props[p].sig;
            Sig psig_unroll = umap[gate(psig_orig)] ^ sign(psig_orig);
            assert(psig_unroll != sig_Undef);
            Lit plit = cl.clausify(psig_unroll);

            double total_time = cpuTime() - time_before;
            if (tip.verbosity >= 1){
                printf(" --- k=%3d, vrs=%8.3g, cls=%8.3g, con=%8.3g",
                       i, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
                if (tip.verbosity >= 2)
                    printf(", time(solve=%6.1f s, total=%6.1f s)\n",
                           solve_time, total_time);
                else
                    printf("\n");
            }

            double solve_time_before = cpuTime();
            bool ret = s.solve(~plit);
            solve_time += cpuTime() - solve_time_before;

            if (ret){
                // Property falsified, create and extract trace:
                Trace             cex    = tip.newTrace();
                vec<vec<lbool> >& frames = tip.traces[cex].frames;
                for (int k = 0; k < ui.size(); k++){
                    frames.push();
                    for (int l = 0; l < ui[k].size(); l++)
                        frames.last().push(cl.modelValue(ui[k][l]));
                }
                tip.safe_props[p].stat = pstat_Falsified;
                tip.safe_props[p].cex  = cex;
            }else{
                unresolved_safety++;
            }
        }

        // Terminate if all safety properties resolved:
        if (unresolved_safety == 0)
            break;
    }
    if (tip.verbosity >= 1){
        double total_time = cpuTime() - time_before;
        printf(" --- done,  vrs=%8.3g, cls=%8.3g, con=%8.3g",
               (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts);
        if (tip.verbosity >= 2)
            printf(", time(solve=%6.1f s, total=%6.1f s)\n",
                   solve_time, total_time);
        else
            printf("\n");
        s.printStats();
    }
}

};
