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
    assert(check_live);

    // Initialize live_data for next cycle:
    live_data.push();
    live_data.last().loop_now    = mkLit(s.newVar());
    live_data.last().loop_before = mkLit(s.newVar());
    live_data.last().live_in_loop.growTo(tip.live_props.size(), lit_Undef);

    LiveCycle&       next = live_data.last();
    const LiveCycle& prev = live_data[live_data.size()-2];

    // Loop logic for next cycle:
    for (unsigned i = 0; i < orig_nflops; i++){
        Sig x = unroll(tip.flps.next(tip.flps[i]), cycle);
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
            Sig q  = unroll(tip.live_props[p].sigs[0], cycle);
            Lit lq = cl.clausify(q);
            next.live_in_loop[p] = mkLit(s.newVar());

            // next.live_in_loop[p] == prev.live_in_loop[p] || (next.loop_before && q)
            s.addClause(~next.live_in_loop[p], prev.live_in_loop[p], next.loop_before);
            s.addClause(~next.live_in_loop[p], prev.live_in_loop[p], lq);
            s.addClause( next.live_in_loop[p], ~prev.live_in_loop[p]);
            s.addClause( next.live_in_loop[p], ~next.loop_before, ~lq);
        }
}


BasicBmc::BasicBmc(TipCirc& t, bool check_live_)
  : UnrolledCirc(t, false),
    tip(t), 
    solve_time(0),
    cl(*this, s),
    cycle(-1),
    check_live(check_live_),
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
    if (check_live && unresolved_liveness > 0){
        orig_nflops = tip.flps.size();

        // Create looping state variables:
        for (unsigned i = 0; i < orig_nflops; i++)
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
        for (unsigned i = 0; i < orig_nflops; i++){
            Sig x = unroll(tip.flps[i], 0);
            Lit l = cl.clausify(x);
            s.addClause(~loop0, ~l,  looping_state[i]);
            s.addClause(~loop0,  l, ~looping_state[i]);
        }
    }
}


void BasicBmc::unrollCycle()
{
    cycle++;

    // Assert all constraints:
    for (unsigned j = 0; j < tip.cnstrs.size(); j++){
        Sig cx = tip.cnstrs[j][0];
        Lit lx = cl.clausify(unroll(cx, cycle));
        for (int k = 1; k < tip.cnstrs[j].size(); k++){
            Sig cy = tip.cnstrs[j][k];
            Lit ly = cl.clausify(unroll(cy, cycle));
            s.addClause(~lx, ly);
            s.addClause(~ly, lx);
        }
    }

    if (check_live && unresolved_liveness > 0)
        nextLiveness();
}


void BasicBmc::extractTrace(vec<vec<lbool> >& frames)
{
    frames.push();
    for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd() ; ++iit)
        if (tip.init.number(*iit) != UINT32_MAX){
            frames.last().growTo(tip.init.number(*iit)+1, l_Undef);
            frames.last()[tip.init.number(*iit)] = cl.modelValue(lookupInit(*iit));
        }

    for (int i = 0; i <= cycle; i++){
        frames.push();
        for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
            if (tip.main.number(*iit) != UINT32_MAX){
                frames.last().growTo(tip.main.number(*iit)+1, l_Undef);
                Sig   x = lookup(*iit, i);
                // Lit   l = cl.lookup(x);
                // lbool b = s.modelValue(l);
                // printSig(x);
                // printf(":%s%d:%c ", sign(l)?"-":"", var(l), b == l_Undef ? 'x' : b == l_True ? '1' : '0');
                //printf("%c", x == sig_Undef ? 'x' : x == sig_True ? '1' : x == sig_False ? '0' : '*');
                frames.last()[tip.main.number(*iit)] = cl.modelValue(lookup(*iit, i));
            }
        }
        //printf("\n");
    }

    tip.adaptTrace(frames);
}


bool BasicBmc::proveSig(Sig x)
{
    double time_before = cpuTime();
    bool   ret         = s.solve(~cl.clausify(unroll(x, cycle)));
    solve_time += cpuTime() - time_before;
    return !ret;
}


void BasicBmc::decideCycle()
{
    double time_before = cpuTime();

#if 0
    // TODO: enable this? Should work but will cause problems for instance in invariant
    // verification.

    // Check if constraints are satisfiable at this point:
    if (!s.solve()){
        // All remaining properties are true:
        for (SafeProp p = 0; p < tip.safe_props.size(); p++)
            if (tip.safe_props[p].stat == pstat_Unknown)
                tip.safe_props[p].stat = pstat_Proved;

        for (LiveProp p = 0; p < tip.live_props.size(); p++)
            if (tip.live_props[p].stat != pstat_Unknown)
                tip.live_props[p].stat = pstat_Proved;
    }
#endif

    // Do SAT-tests:
    unresolved_safety = 0;
    for (SafeProp p = 0; p < tip.safe_props.size(); p++){
        if (tip.safe_props[p].stat != pstat_Unknown)
            continue;
            
        Sig psig_orig   = tip.safe_props[p].sig;
        Sig psig_unroll = unroll(psig_orig, cycle);
        Lit plit        = cl.clausify(psig_unroll);

        if (s.solve(~plit)){
            // Property falsified, create and extract trace:
            Trace             cex    = tip.newTrace();
            vec<vec<lbool> >& frames = tip.traces[cex].frames;
            extractTrace(frames);
            tip.setFalsifiedSafe(p, cex, "bmc");
        }else {
            unresolved_safety++;
            tip.setRadiusSafe(p, depth()+1, "bmc");
        }
    }

    // Do SAT-tests:
    if (check_live){
        unresolved_liveness = 0;
        for (LiveProp p = 0; p < tip.live_props.size(); p++){
            if (tip.live_props[p].stat != pstat_Unknown)
                continue;
            
            Lit loop_now     = live_data.last().loop_now;
            Lit live_in_loop = live_data.last().live_in_loop[p];

            assert(loop_now != lit_Undef);
            assert(live_in_loop != lit_Undef);

            if (s.solve(loop_now, live_in_loop)){
                // Property falsified, create and extract trace:
                Trace             cex    = tip.newTrace();
                vec<vec<lbool> >& frames = tip.traces[cex].frames;
                extractTrace(frames);
                tip.setFalsifiedLive(p, cex, "bmc");
            }else
                unresolved_liveness++;
        }
    }

    solve_time += cpuTime() - time_before;
}


bool BasicBmc::done()
{
    return unresolved_safety == 0 && (!check_live || unresolved_liveness == 0);
}


void BasicBmc::printStats(bool final)
{
    if (tip.verbosity >= 1){
        printf("[bmc] k=%3d, vrs=%8.3g, cls=%8.3g, con=%8.3g, time=%.1f s\n",
               cycle, (double)s.nFreeVars(), (double)s.nClauses(), (double)s.conflicts, solve_time);
        if (final)
            s.printStats();
        fflush(stdout);
    }
}

uint64_t BasicBmc::props (){ return s.propagations; }
uint64_t BasicBmc::solves(){ return s.solves; }
double   BasicBmc::time  (){ return solve_time; }
int      BasicBmc::depth (){ return cycle; }


//=================================================================================================
// Implementation of Basic BMC:
//

void basicBmc(TipCirc& tip, uint32_t begin_cycle, uint32_t stop_cycle, bool check_live)
{
    if (begin_cycle >= stop_cycle)
        return;

    BasicBmc bmc(tip, check_live);

    if (bmc.done()) // Escape here for cosmetic reasons.
        return;

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
