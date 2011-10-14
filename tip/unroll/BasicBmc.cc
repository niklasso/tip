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
#include "tip/unroll/Bmc.h"
#include "tip/liveness/EmbedFairness.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Implementation of Basic BMC class:
//

void BasicBmc::nextLiveness()
{
    // Initialize live_data for next cycle:
    live_data.push();
    live_data.last().loop_now    = mkLit(s.newVar());
    live_data.last().loop_before = mkLit(s.newVar());
    live_data.last().live_in_loop.growTo(tip.live_props.size(), lit_Undef);

    LiveCycle&       next = live_data.last();
    const LiveCycle& prev = live_data[live_data.size()-2];

    // Loop logic for next cycle:
    for (int i = 0; i < unroll.numFlops(); i++){
        Sig x = umap[gate(tip.flps.next(tip.flps[i]))] ^ sign(tip.flps.next(tip.flps[i]));
        Lit l = cl.clausify(x);
        s.addClause(~next.loop_now, ~l,  looping_state[i]);
        s.addClause(~next.loop_now,  l, ~looping_state[i]);
    }

    // next.loop_before == prev.loop_before or prev.loop_now
    s.addClause(~prev.loop_before, next.loop_before);
    s.addClause(~prev.loop_now,    next.loop_before);
    s.addClause(~next.loop_before, prev.loop_before, prev.loop_now);

    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown){
            assert(tip.live_props[p].sigs.size() == 1);
            Sig q  = umap[gate(tip.live_props[p].sigs[0])] ^ sign(tip.live_props[p].sigs[0]);
            Lit lq = cl.clausify(q);
            next.live_in_loop[p] = mkLit(s.newVar());

            // next.live_in_loop[p] == prev.live_in_loop[p] || (next.loop_before && q)
            s.addClause(~next.live_in_loop[p], prev.live_in_loop[p], next.loop_before);
            s.addClause(~next.live_in_loop[p], prev.live_in_loop[p], lq);
            s.addClause( next.live_in_loop[p], ~prev.live_in_loop[p]);
            s.addClause( next.live_in_loop[p], ~next.loop_before, ~lq);
        }
}


BasicBmc::BasicBmc(TipCirc& t) 
  : tip(t), 
    solve_time(0),
    unroll(tip, ui, uc, true),
    cl(uc, s),
    cycle(0),
    unresolved_safety(0),
    unresolved_liveness(0)
{
    for (SafeProp p = 0; p < tip.safe_props.size(); p++)
        if (tip.safe_props[p].stat == pstat_Unknown)
            unresolved_safety++;

    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown)
            unresolved_liveness++;
    
    // Handle liveness-encoding:
    if (unresolved_liveness > 0){

        // Create looping state variables:
        for (int i = 0; i < unroll.numFlops(); i++)
            looping_state.push(mkLit(s.newVar()));

        // Initialize live_data for cycle 0:
        live_data.push();
        live_data[0].loop_now    = mkLit(s.newVar());
        live_data[0].loop_before = cl.clausify(sig_False);
        live_data[0].live_in_loop.growTo(tip.live_props.size(), lit_Undef);
        for (LiveProp p = 0; p < tip.live_props.size(); p++)
            if (tip.live_props[p].stat == pstat_Unknown)
                live_data[0].live_in_loop[p] = cl.clausify(sig_False);

        // Loop logic for cycle 0:
        Lit& loop0 = live_data[0].loop_now;
        for (int i = 0; i < unroll.numFlops(); i++){
            Sig x = unroll.front(i);
            Lit l = cl.clausify(x);
            s.addClause(~loop0, ~l,  looping_state[i]);
            s.addClause(~loop0,  l, ~looping_state[i]);
        }
    }
}


void BasicBmc::unrollCycle()
{
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

    if (unresolved_liveness > 0)
        nextLiveness();

    cycle++;
}


void BasicBmc::decideCycle()
{
    double time_before = cpuTime();
    // Do SAT-tests:
    unresolved_safety = 0;
    for (SafeProp p = 0; p < tip.safe_props.size(); p++){
        if (tip.safe_props[p].stat != pstat_Unknown)
            continue;
            
        Sig psig_orig   = tip.safe_props[p].sig;
        Sig psig_unroll = umap[gate(psig_orig)] ^ sign(psig_orig);
        assert(psig_unroll != sig_Undef);
        Lit plit = cl.clausify(psig_unroll);

        if (s.solve(~plit)){
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
        }else
            unresolved_safety++;
    }

    // Do SAT-tests:
    unresolved_liveness = 0;
    for (LiveProp p = 0; p < tip.live_props.size(); p++){
        if (tip.live_props[p].stat != pstat_Unknown)
            continue;
            
        Lit loop_now     = live_data.last().loop_now;
        Lit live_in_loop = live_data.last().live_in_loop[p];

        assert(loop_now != lit_Undef);
        assert(live_in_loop != lit_Undef);

        if (s.solve(loop_now, live_in_loop)){
#if 0
            // Debug:
            for (int i = 0; i < live_data.size(); i++){
                printf("... live_data[%d].loop_now = %c\n", i,
                       s.modelValue(live_data[i].loop_now) == l_Undef ? 'x' :
                       s.modelValue(live_data[i].loop_now) == l_True  ? '1' : '0');
            }

            for (int i = 0; i < live_data.size(); i++)
                printf("... live_data[%d].loop_before = %c\n", i,
                       s.modelValue(live_data[i].loop_before) == l_Undef ? 'x' :
                       s.modelValue(live_data[i].loop_before) == l_True  ? '1' : '0');
#endif

            // Property falsified, create and extract trace:
            Trace             cex    = tip.newTrace();
            vec<vec<lbool> >& frames = tip.traces[cex].frames;
            for (int k = 0; k < ui.size(); k++){
                frames.push();
                for (int l = 0; l < ui[k].size(); l++)
                    frames.last().push(cl.modelValue(ui[k][l]));
            }
            tip.live_props[p].stat = pstat_Falsified;
            tip.live_props[p].cex  = cex;
        }else
            unresolved_liveness++;
    }

    solve_time += cpuTime() - time_before;
}


bool BasicBmc::done()
{
    return unresolved_safety == 0 && unresolved_liveness == 0;
}


void BasicBmc::printStats(bool final)
{
    if (tip.verbosity >= 1){
        printf("[bmc] k=%3d, vrs=%8.3g, cls=%8.3g, con=%8.3g, time=%.1f s\n",
               cycle-1, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts, solve_time);
        if (final)
            s.printStats();
    }
}

uint64_t BasicBmc::props (){ return s.propagations; }
uint64_t BasicBmc::solves(){ return s.solves; }
double   BasicBmc::time  (){ return solve_time; }
int      BasicBmc::depth (){ return cycle; }


//=================================================================================================
// Implementation of Basic BMC:
//

void basicBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle)
{
    BasicBmc bmc(tip);

    for (uint32_t i = 0; i < begin_cycle; i++)
        bmc.unrollCycle();

    for (uint32_t i = begin_cycle; !bmc.done() && i < stop_cycle; i++){
        bmc.unrollCycle();
        bmc.printStats ();
        bmc.decideCycle();
    }
    bmc.printStats(true);
}


};
