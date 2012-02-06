/***************************************************************************[TripProofInstances.cc]
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
#include "minisat/utils/System.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/TripProofInstances.h"

//#define VERBOSE_DEBUG

namespace Tip {

    namespace {

        template<class Lits>
        void printLits(const Lits& cs){
            for (int i = 0; i < cs.size(); i++)
                printf("%s%d ", sign(cs[i])?"-":"", var(cs[i]));
        }

        struct SigLitPair {
            Sig x;
            Lit l;
        };
        
        struct SigLitCmp {
            bool operator()(SigLitPair p1, SigLitPair p2) const {
                return p1.l < p2.l;
            }
        };



        void extractResetInputs(const TipCirc& tip, const GMap<Sig>& umap, 
                                Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit){
                Sig inp = umap[*iit];
                Lit lit = cl.clausify(inp);
                umapl[*iit] = lit;
                solver.freezeVar(var(lit));
                xs.push(lit);
            }
        }

        void extractInputs(const TipCirc& tip, const GMap<Sig>& umap,
                           Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
                Sig inp = umap[*iit];
                Lit lit = cl.clausify(inp);
                umapl[*iit] = lit;
                solver.freezeVar(var(lit));
                xs.push(lit);
            }
        }

        void extractFlopIns(const TipCirc& tip, const GMap<Sig>& umap,
                            Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Gate flp_in   = *flit;
                Lit  lit_in   = cl.clausify(umap[flp_in]);
                umapl[flp_in] = lit_in;
                solver.freezeVar(var(lit_in));
                xs.push(lit_in);
            }
        }

        void extractFlopOuts(const TipCirc& tip, const GMap<Sig>& umap,
                             Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Sig  flp_out         = tip.flps.next(*flit);
                Lit  lit_out         = cl.clausify(umap[gate(flp_out)] ^ sign(flp_out));
                umapl[gate(flp_out)] = lit_out ^ sign(flp_out);
                solver.freezeVar(var(lit_out));
                xs.push(lit_out);
            }
        }

        void extractInputs(const TipCirc& tip, const GMap<Sig>& umap,
                           Clausifyer<SimpSolver>& cl, SimpSolver& solver, vec<Sig>& xs)
        {
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
                Sig inp = umap[*iit];
                Lit lit = cl.clausify(inp);
                solver.freezeVar(var(lit));
                xs.push(inp);
            }
        }

        void extractFlopIns(const TipCirc& tip, const GMap<Sig>& umap,
                            Clausifyer<SimpSolver>& cl, SimpSolver& solver, vec<Sig>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Sig flp_in = umap[*flit];
                Lit lit_in = cl.clausify(flp_in);
                solver.freezeVar(var(lit_in));
                xs.push(flp_in);
            }
        }

        void extractFlopOuts(const TipCirc& tip, const GMap<Sig>& umap,
                             Clausifyer<SimpSolver>& cl, SimpSolver& solver)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Sig  flp_out = tip.flps.next(*flit);
                Lit  lit_out = cl.clausify(umap[gate(flp_out)] ^ sign(flp_out));
                solver.freezeVar(var(lit_out));
            }
        }

        void extractFlopReset(const TipCirc& tip, const GMap<Sig>& umap,
                              Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Sig  flp_res         = tip.flps.init(*flit);
                Lit  lit_res         = cl.clausify(umap[gate(flp_res)] ^ sign(flp_res));
                umapl[gate(flp_res)] = lit_res ^ sign(flp_res);
                solver.freezeVar(var(lit_res));
            }
        }


        void extractSafeProps(const TipCirc& tip, const GMap<Sig>& umap,
                              Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl)
        {
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown){
                    Sig prop          = tip.safe_props[p].sig;
                    Lit lit           = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    umapl[gate(prop)] = lit ^ sign(prop);
                    solver.freezeVar(var(lit));
                }
        }


        void extractSafeProps(const TipCirc& tip, const GMap<Sig>& umap,
                              Clausifyer<SimpSolver>& cl, SimpSolver& solver)
        {
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown){
                    Sig prop = tip.safe_props[p].sig;
                    Lit lit  = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    solver.freezeVar(var(lit));
                }
        }


        void extractLiveProps(const TipCirc& tip, const GMap<Sig>& umap,
                              Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl)
        {
            for (LiveProp p = 0; p < tip.live_props.size(); p++)
                if (tip.live_props[p].stat == pstat_Unknown){
                    assert(tip.live_props[p].sigs.size() == 1);
                    Sig prop          = tip.live_props[p].sigs[0];
                    Lit lit           = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    umapl[gate(prop)] = lit ^ sign(prop);
                    solver.freezeVar(var(lit));
                }
        }


        void extractLiveProps(const TipCirc& tip, const GMap<Sig>& umap,
                              Clausifyer<SimpSolver>& cl, SimpSolver& solver)
        {
            for (LiveProp p = 0; p < tip.live_props.size(); p++)
                if (tip.live_props[p].stat == pstat_Unknown){
                    assert(tip.live_props[p].sigs.size() == 1);
                    Sig prop = tip.live_props[p].sigs[0];
                    Lit lit  = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    solver.freezeVar(var(lit));
                }
        }


        void extractConstraints(const TipCirc& tip, const GMap<Sig>& umap, Lit activate,
                                Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (unsigned i = 0; i < tip.cnstrs.size(); i++){
                Sig x = tip.cnstrs[i][0];
                Lit p = cl.clausify(umap[gate(x)] ^ sign(x));
                solver.freezeVar(var(p));
                xs.push(p);
                for (int j = 1; j < tip.cnstrs[i].size(); j++){
                    Sig y = tip.cnstrs[i][j];
                    Lit q = cl.clausify(umap[gate(y)] ^ sign(y));
                    solver.freezeVar(var(q));
                    solver.addClause(~activate, ~p, q);
                    solver.addClause(~activate, ~q, p);
                    xs.push(q);
                }
            }
        }


        void extractConstraints(const TipCirc& tip, const GMap<Sig>& umap, Lit activate,
                                Clausifyer<SimpSolver>& cl, SimpSolver& solver, vec<Sig>& xs)
        {
            for (unsigned i = 0; i < tip.cnstrs.size(); i++){
                Sig x  = tip.cnstrs[i][0];
                Sig ux = umap[gate(x)] ^ sign(x);
                Lit p = cl.clausify(ux);
                solver.freezeVar(var(p));
                xs.push(ux);
                for (int j = 1; j < tip.cnstrs[i].size(); j++){
                    Sig y  = tip.cnstrs[i][j];
                    Sig uy = umap[gate(y)] ^ sign(y);
                    Lit q  = cl.clausify(uy);
                    solver.freezeVar(var(q));
                    solver.addClause(~activate, ~p, q);
                    solver.addClause(~activate, ~q, p);
                    xs.push(uy);
                }
            }
        }


        void shrinkConflict(SimpSolver& s, LitSet& keep, vec<Lit>& try_remove)
        {
            vec<Lit> ass;
            vec<Lit> smaller;
            s.extend_model = false;

            // Remove elements from 'try_remove' that already exists in 'keep':
            int i,j;
            for (i = j = 0; i < try_remove.size(); i++)
                if (!keep.has(try_remove[i]))
                    try_remove[j++] = try_remove[i];
            try_remove.shrink(i - j);

            while(try_remove.size() > 0){
                keep.copyTo(ass);
                for (int i = 0; i < try_remove.size()-1; i++)
                    ass.push(try_remove[i]);

                if (s.solve(ass)){
                    keep.push(try_remove.last());
                    try_remove.pop();
                }else{
                    smaller.clear();
                    for (int i = 0; i < s.conflict.size(); i++)
                        if (!keep.has(~s.conflict[i]))
                            smaller.push(~s.conflict[i]);
                    assert(smaller.size() < try_remove.size());
                    smaller.moveTo(try_remove);
                }
            }
            s.extend_model = true;
        }


        void shrinkModelOnce(SimpSolver& s, LitSet& xs, const vec<Lit>& top)
        {
            for (int i = 0; i < xs.size(); i++)
                assert(s.modelValue(xs[i]) == l_True);

            for (int i = 0; i < top.size(); i++)
                assert(s.modelValue(top[i]) == l_True);

            // Simple variant for now:
            Lit      trigg = mkLit(s.newVar());
            vec<Lit> clause;
            for (int i = 0; i < top.size(); i++)
                clause.push(~top[i]);
            clause.push(~trigg);
            s.addClause(clause);

            vec<Lit> assume;
            xs.copyTo(assume);
            assume.push(trigg);
            check(!s.solve(assume));

            s.releaseVar(~trigg);

            // Check 's.conflict' and remove literals not present there:
            vec<Lit> out;
            for (int i = 0; i < s.conflict.size(); i++)
                if (xs.has(~s.conflict[i]))
                    out.push(~s.conflict[i]);
            xs.fromVec(out);
        }


        void traceResetInputs(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
                if (tip.init.number(*iit) != UINT32_MAX){
                    Gate inp = *iit;
                    Lit  l   = umapl[inp];
                    frames.last().growTo(tip.init.number(inp)+1, l_Undef);
                    frames.last()[tip.init.number(inp)] = lset.has(var(l)) ^ sign(l);
                }
        }


        void traceInputs(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
                if (tip.main.number(*iit) != UINT32_MAX){
                    Gate inp = *iit;
                    Lit  l   = umapl[inp];
                    frames.last().growTo(tip.main.number(inp)+1, l_Undef);
                    frames.last()[tip.main.number(inp)] = lset.has(var(l)) ^ sign(l);
                }
        }


        void traceInputs(const TipCirc& tip, const LitSet& lset, const GMap<Sig>& umap, Clausifyer<SimpSolver>& cl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
                if (tip.main.number(*iit) != UINT32_MAX){
                    Gate inp = *iit;
                    Lit  l   = cl.lookup(umap[inp]);
                    frames.last().growTo(tip.main.number(inp)+1, l_Undef);
                    frames.last()[tip.main.number(inp)] = lset.has(var(l)) ^ sign(l);
                }
        }


        void getClause(const TipCirc& tip, const LitSet& lset, const GMap<Lit>& umapl, vec<Sig>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Lit   l   = umapl[*flit];
                lbool val = lset.has(var(l)) ^ sign(l);
                if (val != l_Undef)
                    xs.push(mkSig(*flit, val == l_True));
            }
        }


        void getClause(const TipCirc& tip, const LitSet& lset, const GMap<Sig>& umap, Clausifyer<SimpSolver>& cl, vec<Sig>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Lit   l   = cl.lookup(umap[*flit]);
                lbool val = lset.has(var(l)) ^ sign(l);
                if (val != l_Undef)
                    xs.push(mkSig(*flit, val == l_True));
            }
        }
    }

    //===================================================================================================
    // Implementation of InitInstance:

    void InitInstance::reset()
    {
        if (cnf_level == 0)
            solver.eliminate(true);

        umapl[0].clear();
        umapl[0].growTo(tip.init.lastGate(), lit_Undef);
        inputs.clear();

        // Unroll proper number of steps:
        Clausifyer<SimpSolver> cl(tip.init, solver);

        // FIXME: ugly, but will do for now.
        GMap<Sig> id(tip.init.lastGate(), sig_Undef);
        for (GateIt git = tip.init.begin0(); git != tip.init.end(); ++git)
            id[*git] = mkSig(*git);

        // Extract all needed references:
        extractResetInputs(tip, id, cl, solver, umapl[0], inputs);
        extractFlopReset  (tip, id, cl, solver, umapl[0]);
        umapl[0][gate_True] = cl.clausify(gate_True);

        // Simplify CNF:
        if (cnf_level >= 2){
            solver.use_asymm = true;
            solver.grow = 2;
        }
        solver.eliminate(true);
        solver.thaw();
    }

    void InitInstance::reduceClause(Clause& c)
    {
        vec<SigLitPair> slits;
        for (unsigned i = 0; i < c.size(); i++){
            SigLitPair p;
            p.x   = c[i];
            Sig x = tip.flps.init(gate(p.x)) ^ sign(p.x);
            p.l   = umapl[0][gate(x)] ^ sign(x);
            slits.push(p);
        }

        sort(slits, SigLitCmp());
        
        // TODO: maybe prefer "larger" flops while removing duplicates.
        int i,j;
        for (i = j = 1; i < slits.size(); i++)
            if (slits[i].l != slits[j-1].l)
                slits[j++] = slits[i];
        slits.shrink(i-j);

        vec<Sig> d;
        for (i = 0; i < slits.size(); i++)
            d.push(slits[i].x);

        c = Clause(d, c.cycle);
    }


    bool InitInstance::prove(const Clause& c_, const Clause& bot, 
                             Clause& yes, SharedRef<ScheduledClause>& no, SharedRef<ScheduledClause> next)
    {
        assert(next == NULL || &c_ == (Clause*)&*next);
        assert(subsumes(bot, c_));

        double time_before = cpuTime();

        // printf("[InitInstance::prove] proving c_ = ");
        // printClause(tip, c_);
        // printf("\n");

        Clause c = c_;
        reduceClause(c);

        // TODO: special-cases for trivially satisfiable/unsatisfiable situations?

        vec<Lit> assumes;
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.init(gate(c[i])) ^ sign(c[i]);
            Lit l = umapl[0][gate(x)] ^ sign(x);
            assert(l != lit_Undef);
            assumes.push(~l);
        }

        if (next == NULL)
            solver.extend_model = false;
        bool result;

        bool sat = solver.solve(assumes);

        if (sat){
            // Found a counter-example:
            if (next != NULL){
                lset.fromModel(inputs, solver);
                const vec<Lit>& shrink_roots = assumes;
                shrinkModelOnce(solver, lset, shrink_roots);

                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceResetInputs(tip, lset, umapl[0], frames);

                vec<Sig>         dummy;
                SharedRef<ScheduledClause> pred_rst(new ScheduledClause(dummy, 0, frames[0], next));

                no = pred_rst;
            }
            result = false;
        }else{
            assert(solver.conflict.size() > 0);
            // Proved the clause:

            vec<Sig> subset;
            lset.fromVec(solver.conflict);
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.init(gate(c[i])) ^ sign(c[i]);
                Lit l = umapl[0][gate(x)] ^ sign(x);
                if (lset.has(l))
                    subset.push(c[i]);
            }

            yes    = bot + Clause(subset, 0);
            result = true;
        }
        solver.extend_model = true;
        cpu_time += cpuTime() - time_before;

        return result;
    }


    void InitInstance::extendLiveness()
    {
        assert(umapl[0][gate_True] != lit_Undef);
    }


    bool InitInstance::prove(const Clause& c, const Clause& bot, Clause& yes)
    {
        SharedRef<ScheduledClause> dummy;
        return prove(c, bot, yes, dummy);
    }


    InitInstance::InitInstance(const TipCirc& t, int cnf_level_) 
        : tip(t), cpu_time(0), cnf_level(cnf_level_)
    {
        reset();
    }


    InitInstance::~InitInstance(){ }

    uint64_t InitInstance::props (){ return solver.propagations; }
    uint64_t InitInstance::solves(){ return solver.solves; }
    double   InitInstance::time  (){ return cpu_time; }

    void InitInstance::printStats()
    {
        printf("[init-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver.nFreeVars(), (double)solver.nClauses(), (double)solver.conflicts);
    }
    
    //===================================================================================================
    // Implementation of PropInstance:

    Sig PropInstance::unrollSig (Sig x, unsigned cycle){
        return unrollGate(gate(x), cycle) ^ sign(x);
    }

    Sig PropInstance::unrollGate(Gate g, unsigned cycle)
    {
        // printf(" ... unrollGate (cycle=%d): ", cycle);
        // printGate(g);
        // printf("\n");

        //assert(cycle < umap.size());
        assert(cycle < 2);
        umap[cycle].growTo(g, sig_Undef);
        if (umap[cycle][g] != sig_Undef){
            //printf(" ... got here cycle=%d (cache)\n", cycle);
            return umap[cycle][g];
        }

        Sig ret = sig_Undef;
        if (type(g) == gtype_And){
            //printf(" ... got here cycle=%d (and)\n", cycle);
            Sig xl = tip.main.lchild(g);
            Sig xr = tip.main.rchild(g);
            ret = uc.mkAnd(unrollSig(xl, cycle), unrollSig(xr, cycle));
        }else if (type(g) == gtype_Inp && cycle > 0 && tip.flps.isFlop(g)){
            //printf(" ... got here cycle=%d (flop-next)\n", cycle);
            ret = unrollSig(tip.flps.next(g), cycle-1);
        }else if (type(g) == gtype_Inp){
            ret = uc.mkInp();
            //printf(" ... got here cycle=%d (input)\n", cycle);
            // if (tip.flps.isFlop(g))
            //     inputs.push(mkSig(g));
        }else{
            //printf(" ... got here cycle=%d (const)\n", cycle);
            assert(type(g) == gtype_Const);
            ret = sig_True;
        }

        umap[cycle][g] = ret;
        return ret;
    }

    void PropInstance::clearClauses()
    {
        solver.releaseVar(~act_cycle);
        act_cycle = mkLit(solver.newVar());
    }

    void PropInstance::addClause(const Clause& c)
    {
        // Add the clause if it is an invariant, or if it belongs to the last cycle:
        if (c.cycle == (unsigned)F.size()-1 || c.cycle == cycle_Undef){
            vec<Lit> xs;
            if (c.cycle != cycle_Undef)
                xs.push(~act_cycle);
            for (unsigned i = 0; i < c.size(); i++){
                assert(cl.lookup(umap[0][gate(c[i])] ^ sign(c[i])) != lit_Undef);
                xs.push(cl.lookup(umap[0][gate(c[i])] ^ sign(c[i])));
            }
            solver.addClause(xs);
        }
    }


    void PropInstance::reset()
    {
        if (cnf_level == 0)
            solver.eliminate(true);

        act_cycle  = mkLit(solver.newVar());
        act_cnstrs = mkLit(solver.newVar());
        solver.freezeVar(var(act_cycle));
        solver.freezeVar(var(act_cnstrs));

        // Unroll proper number of steps:
        UnrollCirc2            unroll(tip, uc); // Unroller-helper object.
        unroll(umap[0]);
        unroll(umap[1]);

        // Extract all needed references:
        extractInputs     (tip, umap[0], cl, solver, inputs);
        extractLiveProps  (tip, umap[0], cl, solver);
        extractInputs     (tip, umap[1], cl, solver, inputs);
        extractFlopIns    (tip, umap[0], cl, solver, inputs);
        extractSafeProps  (tip, umap[1], cl, solver);
        extractLiveProps  (tip, umap[1], cl, solver);

        // TMP: remove at some point. This is kept to keep identical behavior.
        cl.clausify(gate_True);

        if (tip.cnstrs.size() > 0){
            extractConstraints(tip, umap[0], act_cnstrs, cl, solver, outputs);
            extractConstraints(tip, umap[1], act_cnstrs, cl, solver, outputs);
        }else
            solver.addClause(act_cnstrs);

        // Simplify CNF:
        if (cnf_level >= 2){
            solver.use_asymm = true;
            solver.grow = 2;
        }
        solver.eliminate(true);
        solver.thaw();
    }


    lbool PropInstance::prove(Sig p, SharedRef<ScheduledClause>& no, unsigned cycle)
    {
        double   time_before = cpuTime();
        Lit      l = cl.lookup(umap[1][gate(p)] ^ sign(p));
        vec<Lit> assumps;
        lbool    result;
        vec<Lit> inputs;
        for (int i = 0; i < this->inputs.size(); i++){
            Sig x = this->inputs[i];
            assert(cl.lookup(x) != lit_Undef);
            inputs.push(cl.lookup(x));
        }

        if (solver.solve(~l, act_cycle, act_cnstrs)){
            assert(solver.modelValue(l) == l_False);
            // Found predecessor state to a bad state:
            lset.fromModel(inputs, solver);
            vec<Lit> shrink_roots;
            for (int i = 0; i < outputs.size(); i++){
                assert(cl.lookup(outputs[i]) != lit_Undef);
                shrink_roots.push(cl.lookup(outputs[i]));
            }
            shrink_roots.push(~l);
            shrinkModelOnce(solver, lset, shrink_roots);

            vec<vec<lbool> > frames;
            vec<Sig>         clause;
            traceInputs(tip, lset, umap[0], cl, frames);
            traceInputs(tip, lset, umap[1], cl, frames);
            getClause  (tip, lset, umap[0], cl, clause);

            vec<Sig> dummy;
            ScheduledClause* apa = new ScheduledClause(dummy,  cycle+1, frames[1], NULL);
            assert(apa != NULL);
            SharedRef<ScheduledClause> last(apa);
            //SharedRef<ScheduledClause> last(new ScheduledClause(dummy,  cycle+1, frames[1], NULL));
            SharedRef<ScheduledClause> pred(new ScheduledClause(clause, cycle,   frames[0], last));
            //printf("[PropInstance::prove] last = %p, pred = %p\n", last, pred);
            no     = pred;
            result = l_False;
        }else if (!solver.solve(~l, act_cnstrs))
            // Property is implied already by invariants:
            result = l_True;
        else
            result = l_Undef;
        cpu_time += cpuTime() - time_before;

        return result;
    }


    void PropInstance::extendLiveness(Gate f, Sig f_next)
    {
        Sig x  = unrollSig(f_next, 1);
        assert(x != sig_Undef);
        cl.clausify(x);

        Sig slask = unrollGate(f, 0);
        Lit fl    = cl.clausify(slask);
        //inputs.push(fl);
        inputs.push(slask);
    }


    PropInstance::PropInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, int cnf_level_)
        : tip(t), F(F_), cl(uc, solver), act_cnstrs(lit_Undef), cpu_time(0), cnf_level(cnf_level_)
    {
        reset();
    }


    PropInstance::~PropInstance(){ }

    uint64_t PropInstance::props (){ return solver.propagations; }
    uint64_t PropInstance::solves(){ return solver.solves; }
    double   PropInstance::time  (){ return cpu_time; }

    void PropInstance::printStats()
    {
        printf("[prop-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver.nFreeVars(), (double)solver.nClauses(), (double)solver.conflicts);
    }

    //===================================================================================================
    // Implementation of StepInstance:


    void StepInstance::addClause(const Clause& c)
    {
        vec<Lit> xs;
        // Add the clause unconditionally if it is an invariant, otherwise make it triggered by the
        // cycle's activation literal:
        if (c.cycle != cycle_Undef){
            activate.growTo(c.cycle+1, lit_Undef);
            if (activate[c.cycle] == lit_Undef)
                activate[c.cycle] = mkLit(solver.newVar());
            xs.push(~activate[c.cycle]);

            cycle_clauses.growTo(c.cycle+1, 0);
            cycle_clauses[c.cycle]++;
        }

        for (unsigned i = 0; i < c.size(); i++)
            xs.push(cl.lookup(c[i]));
        solver.addClause(xs);
    }


    void StepInstance::resetCycle(unsigned cycle, unsigned num_clauses)
    {
        assert(cycle != cycle_Undef);
        if ((int)cycle < cycle_clauses.size() && (cycle_clauses[cycle] / 2) > num_clauses){
            // Disable all clauses added to this cycle:
            solver.releaseVar(~activate[cycle]);
            cycle_clauses[cycle] = 0;

            // Introduce new activation literal:
            activate[cycle] = mkLit(solver.newVar());

            // Re-add all clauses from this cycle:
            for (int i = 0; i < F[cycle].size(); i++)
                if (F[cycle][i]->isActive())
                    addClause(*F[cycle][i]);

            // Force a solver simplify:
            solver.simplify();
        }
    }


    void StepInstance::reset()
    {
        if (cnf_level == 0)
            solver.eliminate(true);

        act_cnstrs = mkLit(solver.newVar());
        solver.freezeVar(var(act_cnstrs));

        // FIXME: ugly, but will do for now.
        umap.growTo(tip.main.lastGate(), sig_Undef);
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
            umap[*git] = mkSig(*git);
        prev_lastgate = tip.main.lastGate();

        // Extract all needed references:
        extractInputs   (tip, umap, cl, solver, inputs);
        extractFlopIns  (tip, umap, cl, solver, inputs);
        extractFlopOuts (tip, umap, cl, solver);
        extractLiveProps(tip, umap, cl, solver);

        // TMP: remove at some point. This is kept to keep identical behavior.
        cl.clausify(gate_True);
        if (tip.cnstrs.size() > 0)
            extractConstraints(tip, umap, act_cnstrs, cl, solver, outputs);
        else
            solver.addClause(act_cnstrs);

        // Simplify CNF:
        if (cnf_level >= 2){
            solver.use_asymm = true;
            solver.grow = 2;
        }
        solver.eliminate(true);
        solver.thaw();
    }


    bool StepInstance::prove(const Clause& c, Clause& yes, SharedRef<ScheduledClause>& no, SharedRef<ScheduledClause> next)
    {
        assert(next == NULL || &c == (Clause*)&*next);
        assert(c.cycle > 0);
        double   time_before = cpuTime();
        vec<Lit> shrink_root;
        vec<Lit> inputs;
        vec<Lit> assumes;
        //outputs.copyTo(shrink_root);
        //this->inputs.copyTo(inputs);
        for (int i = 0; i < outputs.size(); i++)
            shrink_root.push(cl.lookup(outputs[i]));
        for (int i = 0; i < this->inputs.size(); i++)
            inputs.push(cl.lookup(this->inputs[i]));

        // Assume proved clauses:
        if (c.cycle != cycle_Undef)
            for (int i = c.cycle-1; i < activate.size(); i++)
                if (activate[i] != lit_Undef){
                    assumes.push(activate[i]);
                    inputs .push(activate[i]);
                }

        // Assume negation of clause 'c' (outgoing):
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
            Lit l = cl.lookup(x);
            assert(l != lit_Undef);
            shrink_root.push(~l);
            assumes.push(~l);
        }
        // Assume constraints:
        assumes.push(act_cnstrs);

        // Try to satisfy clause 'c' (incoming):
        vec<Lit> cls;
        for (unsigned i = 0; i < c.size(); i++){
            Lit l = cl.lookup(c[i]);
            assert(l != lit_Undef);
            solver.setPolarity(var(l), lbool(!sign(l)));
            cls.push(l);
        }

        if (next == NULL) solver.extend_model = false;
        bool sat = solver.solve(assumes);

        // Undo polarity preference:
        for (int i = 0; i < cls.size(); i++)
            solver.setPolarity(var(cls[i]), l_Undef);

        if (sat){
            // Check if incoming clause was satisfied:
            bool clause_sat = false;
            for (int i = 0; i < cls.size() && !clause_sat; i++)
                if (solver.modelValue(cls[i]) == l_True)
                    clause_sat = true;

            if (!clause_sat){
                // Look for a new model where the clause is guaranteed to be true:
                Lit trigg = mkLit(solver.newVar());
                cls.push(~trigg);
                solver.addClause(cls);
                assumes.push(trigg);
                sat = solver.solve(assumes);
                solver.releaseVar(~trigg);
                // printf("[StepInstance::prove] needed to add induction hypothesis => sat=%d\n", sat);
            }else{
                // printf("[StepInstance::prove] did NOT need to add induction hypothesis.\n");
            }
        }
        solver.extend_model = true;

        bool result;
        if (sat){
            // Found a counter-example:
            if (next != NULL){
                lset.fromModel(inputs, solver);
                shrinkModelOnce(solver, lset, shrink_root);

                vec<vec<lbool> > frames;
                vec<Sig>         clause;

                traceInputs     (tip, lset, umap, cl, frames);
                getClause       (tip, lset, umap, cl, clause);

                SharedRef<ScheduledClause> pred(new ScheduledClause(clause, c.cycle-1, frames[0], next));
                //printf("[StepInstance::prove] pred = %p\n", pred);
                no = pred;
            }

            result = false;
        }else{
            // Proved the clause:
            vec<Sig> subset;
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                Lit l = cl.lookup(x);
                if (find(solver.conflict, l))
                    subset.push(c[i]);
            }
            // What level was sufficient?
            unsigned k = cycle_Undef;
            if (c.cycle != cycle_Undef)
                for (int i = c.cycle-1; i < activate.size(); i++)
                    if (find(solver.conflict, ~activate[i])){
                        k = i+1;
                        break;
                    }

            assert(solver.okay());

            // TODO: is this ok? When it doesn't hold it means that the clause didn't hold in the
            // previous cycle, and assuming the induction-hyptothesis was enough to derive the
            // contradiction. This is suprising but may be ok in some situations.
            // assert(subset.size() > 0);

            yes = Clause(subset, k);
            //printf("[StepInstance::prove] &yes = %p\n", &yes);
            result = true;
        }
        cpu_time += cpuTime() - time_before;

        return result;
    }


    void StepInstance::extendLiveness(Gate f, Sig f_next)
    {
        // Update identity 'umap' to contain all new gates:
        umap.growTo(tip.main.lastGate(), sig_Undef);
        for (GateIt git(tip.main, prev_lastgate); git != tip.main.end(); ++git)
            umap[*git] = mkSig(*git);
        prev_lastgate = tip.main.lastGate();

        Sig x  = umap[gate(f_next)] ^ sign(f_next);
        assert(x != sig_Undef);
        cl.clausify(x);
        Lit fl = cl.clausify(f);
        assert(fl != lit_Undef);
        inputs.push(mkSig(f));
    }


    bool StepInstance::prove(const Clause& c, Clause& yes)
    {
        SharedRef<ScheduledClause> dummy;
        return prove(c, yes, dummy);
    }

    StepInstance::StepInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, int cnf_level_)
        : tip(t), F(F_), cl(t.main, solver), cpu_time(0), cnf_level(cnf_level_)
    {
        reset();
    }


    StepInstance::~StepInstance(){ }

    uint64_t StepInstance::props (){ return solver.propagations; }
    uint64_t StepInstance::solves(){ return solver.solves; }
    double   StepInstance::time  (){ return cpu_time; }

    void StepInstance::printStats()
    {
        printf("[step-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver.nFreeVars(), (double)solver.nClauses(), (double)solver.conflicts);
    }


//=================================================================================================
} // namespace Tip
