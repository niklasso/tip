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
#define CNF_ASYMM_LIMIT 16000 // FIXME: do something nicer than this limit.

namespace Tip {

    namespace {

        template<class Lits>
        void printLits(const Lits& cs){
            for (int i = 0; i < cs.size(); i++)
                printf("%s%d ", sign(cs[i])?"-":"", var(cs[i]));
        }

        void printSSet(const TipCirc& tip, const char* prefix, const vec<Sig>& xs, unsigned cycle = cycle_Undef){
            printf("%s", prefix);
            Clause tmp(xs, cycle);
            printClause(tip, tmp);
            printf("\n");
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

        // (stolen from Solver.h)
        static inline double drand(double& seed) {
            seed *= 1389796;
            int q = (int)(seed / 2147483647);
            seed -= (double)q * 2147483647;
            return seed / 2147483647; }

        // (stolen from Solver.h)
        static inline int irand(double& seed, int size) {
            return (int)(drand(seed) * size); }
        

        template<class T>
        static void randomShuffle(double& seed, vec<T>& xs)
        {
            for (int i = 0; i < xs.size(); i++){
                int pick = i + irand(seed, xs.size() - i);
                
                assert(pick < xs.size());

                T tmp = xs[i];
                xs[i] = xs[pick];
                xs[pick] = tmp;
            }
        }


        void shrinkModel(SimpSolver& s, Clausifyer<SimpSolver>& cl,
                         const vec<Sig>& fixed, vec<Sig>& xs, const vec<Sig>& top,
                         const vec<Lit>& fixed_lits, unsigned iters = 32, bool verbose = false)
        {
            // printf("[shrinkModel] begin\n");

            int size_first = xs.size();
#ifndef NDEBUG
            for (int i = 0; i < fixed.size(); i++)
                assert(cl.modelValue(fixed[i]) == l_True);

            for (int i = 0; i < xs.size(); i++)
                assert(cl.modelValue(xs[i]) == l_True);

            for (int i = 0; i < top.size(); i++)
                assert(cl.modelValue(top[i]) == l_True);
#endif

            // Simple variant for now:
            Lit      trigg = mkLit(s.newVar());
            vec<Lit> clause;
            for (int i = 0; i < top.size(); i++)
                clause.push(~cl.lookup(top[i]));
            clause.push(~trigg);
            s.addClause(clause);

            vec<Lit> fix;
            fixed_lits.copyTo(fix);
            for (int i = 0; i < fixed.size(); i++)
                fix.push(cl.lookup(fixed[i]));

            if (verbose)
                printf("[shrinkModel] %d", size_first);

            vec<Lit> assume;
            unsigned fails = 0;
            for (uint32_t i = 0; fails < 2 && i < iters; i++){
                int size_before = xs.size();

                // Shuffle the order of literals to increase chance of other removal opportunities,
                // except in first iteration:
                static double seed = 12345678;
                if (i > 0){
                    randomShuffle(seed, xs);
                    randomShuffle(seed, fix); }

                // Join the set of fixed literals + plus the current minimized set 'xs'. It is
                // important to place 'xs' last as this increases the likelyhood of those literals
                // being removed by the solver 'analyzeFinal()':
                fix.copyTo(assume);
                assume.push(trigg);
                for (int j = 0; j < xs.size(); j++)
                    assume.push(cl.lookup(xs[j]));

                check(!s.solve(assume));

                // Copy the literals in 'xs' that were still needed in the conflict:
                int j,k;
                for (j = k = 0; j < xs.size(); j++)
                    if (s.conflict.has(~cl.lookup(xs[j])))
                        xs[k++] = xs[j];
                xs.shrink(j - k);

                if (xs.size() < size_before){
                    if (verbose) printf(".%d", xs.size());
                }else{
                    fails++;
                    if (verbose) printf("x");
                }

            }
            if (verbose) printf("\n");

            s.releaseVar(~trigg);
        }

        void shrinkModel(SimpSolver& s, Clausifyer<SimpSolver>& cl,
                         const vec<Sig>& fixed, vec<Sig>& xs, const vec<Sig>& top, unsigned iters = 32, bool verbose = false)
        {
            vec<Lit> empty;
            shrinkModel(s, cl, fixed, xs, top, empty, iters, verbose);
        }


        void shrinkModel(SimpSolver& s, Clausifyer<SimpSolver>& cl,
                         const SSet& fixed, SSet& xs, const SSet& top, const vec<Lit>& fixed_lits, unsigned iters = 32, bool verbose = false)
        {
            // Copy the set 'xs':
            vec<Sig> ys; xs.toVec().copyTo(ys);

            shrinkModel(s, cl, fixed.toVec(), ys, top.toVec(), fixed_lits, iters, verbose);

            // Copy back the reduced set 'ys':
            xs.clear();
            for (int i = 0; i < ys.size(); i++)
                xs.insert(ys[i]);
        }


        void shrinkModel(SimpSolver& s, Clausifyer<SimpSolver>& cl,
                         const SSet& fixed, SSet& xs, const SSet& top, unsigned iters = 32, bool verbose = false)
        {
            vec<Lit> empty;
            shrinkModel(s, cl, fixed, xs, top, empty, iters, verbose);
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


        void traceInputs(const TipCirc& tip, const SSet& submodel, const UnrolledCirc& uc, unsigned cycle, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit)
                if (tip.main.number(*iit) != UINT32_MAX){
                    Gate inp = *iit;
                    Sig  x   = uc.lookup(inp, cycle);
                    frames.last().growTo(tip.main.number(inp)+1, l_Undef);
                    if (x != sig_Undef){
                        if (submodel.has(x))
                            frames.last()[tip.main.number(inp)] = l_True;
                        else if (submodel.has(~x))
                            frames.last()[tip.main.number(inp)] = l_False;
                        else
                            frames.last()[tip.main.number(inp)] = l_Undef;
                    }else
                        frames.last()[tip.main.number(inp)] = l_Undef;
                }
        }


        void traceResetInputs(const TipCirc& tip, const SSet& submodel, const UnrolledCirc& uc, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit)
                if (tip.init.number(*iit) != UINT32_MAX){
                    Gate inp = *iit;
                    Sig  x   = uc.lookupInit(inp);
                    frames.last().growTo(tip.init.number(inp)+1, l_Undef);
                    if (x != sig_Undef){
                        if (submodel.has(x))
                            frames.last()[tip.init.number(inp)] = l_True;
                        else if (submodel.has(~x))
                            frames.last()[tip.init.number(inp)] = l_False;
                        else
                            frames.last()[tip.init.number(inp)] = l_Undef;
                    }else
                        frames.last()[tip.init.number(inp)] = l_Undef;
                }
        }


        void getClause(const TipCirc& tip, const SSet& submodel, const UnrolledCirc& uc, unsigned cycle, vec<Sig>& xs)
        {
            xs.clear();
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
                if (uc.lookup(*flit, cycle) != sig_Undef){
                    Sig q = uc.lookup(*flit, cycle);
                    if (submodel.has(q))
                        xs.push(~mkSig(*flit));
                    else if (submodel.has(~q))
                        xs.push(mkSig(*flit));
                }
        }


        // NOTE: Ignores sign of signals in 'xs':
        void subModel(const vec<Sig>& xs, Clausifyer<SimpSolver>& cl, SSet& set)
        {
            set.clear();
            for (int i = 0; i < xs.size(); i++){
                Gate g = gate(xs[i]);
                assert(cl.modelValue(g) != l_Undef);
                set.insert(mkSig(g, cl.modelValue(g) == l_False));
            }
        }

    }


    //===================================================================================================
    // Implementation of InitInstance:

    void InitInstance::reset()
    {
        if (solver != NULL) delete solver;
        if (cl != NULL)     delete cl;

        solver = new SimpSolver();
        cl     = new Clausifyer<SimpSolver>(uc, *solver);

        inputs .clear();

        if (cnf_level == 0)
            solver->eliminate(true);

        vec<Sig> used;
        uc.unrollFlops(0, used);
        uc.extractUsedInitInputs(inputs);

        // Clausify and freeze used input variables:
        for (int i = 0; i < inputs.size(); i++)
            solver->freezeVar(var(cl->clausify(inputs[i])));

        // Clausify and freeze used flop variables:
        for (int i = 0; i < used.size(); i++)
            solver->freezeVar(var(cl->clausify(used[i])));

        // Simplify CNF:
        if (cnf_level >= 2){
            solver->use_asymm = tip.main.nGates() < CNF_ASYMM_LIMIT;
            solver->grow = 2;
        }

        //printf(" (before) #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());
        solver->eliminate(true);
        solver->thaw();
        //printf(" (after)  #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());
    }


    void InitInstance::reduceClause(Clause& c)
    {
        vec<SigLitPair> slits;
        for (unsigned i = 0; i < c.size(); i++){
            SigLitPair p;
            p.x   = c[i];
            Sig x = uc.unroll(p.x, 0);
            p.l   = cl->lookup(x);
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
        Clause cand_;
        Clause rest;

        if (bot.size() == 0){
            cand_ = c_;
        }else{
            cand_ = bot;
            rest  = c_ - bot;
        }

        reduceClause(cand_);
        reduceClause(rest);

        vec<Sig> cand;
        for (unsigned i = 0; i < cand_.size(); i++) cand.push(cand_[i]);

        vec<Lit> assumes;
        bool     result;

        for (int i = 0; i < cand.size(); i++){
            Sig x = uc.unroll(cand[i], 0);
            Lit l = cl->lookup(x);
            assert(l != lit_Undef);
            assumes.push(~l);
        }

        if (next == NULL)
            solver->extend_model = false;

        bool sat;
        bool bad_model;
        do {
            // printf("[InitInstance::prove] cand = ");
            // printSigs(cand);
            // printf("\n");
            bad_model = false;
            sat       = solver->solve(assumes);
            if (sat)
                for (unsigned i = 0; i < rest.size(); i++){
                    Sig x = uc.unroll(rest[i], 0);
                    Lit l = cl->lookup(x);
                    assert(solver->modelValue(l) != l_Undef);
                    if (solver->modelValue(l) == l_True){
                        cand.push(rest[i]);
                        assumes.push(~l);
                        bad_model = true;
                    }
                }
        }while (bad_model);

        if (sat){
            // Found a counter-example:
            if (next != NULL){
                subModel(inputs,  *cl, inputs_set);
                vec<vec<lbool> > frames;
                vec<Sig>         dummy;
                traceResetInputs(tip, inputs_set, uc, frames);
                SharedRef<ScheduledClause> pred_rst(new ScheduledClause(dummy, 0, frames[0], next));
                    
                no = pred_rst;
            }
            result = false;
        }else{
            assert(solver->conflict.size() > 0);
            // Proved the clause:
            
            vec<Sig> subset;
            for (int i = 0; i < cand.size(); i++){
                Sig x = uc.unroll(cand[i], 0);
                Lit l = cl->lookup(x);
                if (solver->conflict.has(l))
                    subset.push(cand[i]);
            }
                
            yes    = bot + Clause(subset, 0);
            result = true;
        }

        solver->extend_model = true;
        cpu_time += cpuTime() - time_before;
        
        return result;
    }

    bool InitInstance::prove(const Clause& c, const Clause& bot, Clause& yes)
    {
        SharedRef<ScheduledClause> dummy;
        return prove(c, bot, yes, dummy);
    }


    InitInstance::InitInstance(const TipCirc& t, int cnf_level_) 
        : tip(t), uc(t, false), solver(NULL), cl(NULL), cpu_time(0), cnf_level(cnf_level_)
    {
        reset();
    }


    InitInstance::~InitInstance(){ }

    uint64_t InitInstance::props (){ return solver->propagations; }
    uint64_t InitInstance::solves(){ return solver->solves; }
    double   InitInstance::time  (){ return cpu_time; }

    void InitInstance::printStats()
    {
        printf("[init-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nFreeVars(), (double)solver->nClauses(), (double)solver->conflicts);
    }
    
    //===================================================================================================
    // Implementation of PropInstance:

    void PropInstance::clearClauses(unsigned safe_lim)
    {
        // printf("[PropInstance::clearClauses]\n");
        solver->releaseVar(~act_cycle);
        act_cycle = mkLit(solver->newVar());

        for (int i = safe_lim; i < F.size(); i++)
            for (int j = 0; j < F[i].size(); j++){
                assert(F[i][j]->isActive());
                addClause(*F[i][j]);
            }
    }


    void PropInstance::addClause(const Clause& c)
    {
        // printf("[PropInstance::addClause] c = ");
        // printClause(tip, c);
        // printf("\n");

        vec<Lit> xs;
        if (c.cycle != cycle_Undef)
            xs.push(~act_cycle);
        for (unsigned i = 0; i < c.size(); i++)
            xs.push(cl->clausify(uc.unroll(c[i], 0)));
        solver->addClause(xs);
    }


    void PropInstance::reset(unsigned safe_lim, unsigned new_depth)
    {
        depth_ = new_depth;

        if (solver != NULL) delete solver;
        if (cl != NULL)     delete cl;

        solver = new SimpSolver();
        cl     = new Clausifyer<SimpSolver>(uc, *solver);

        needed_flops.clear();
        inputs .clear();
        outputs.clear();
        flops  .clear();

        if (cnf_level == 0)
            solver->eliminate(true);

        act_cycle  = mkLit(solver->newVar());
        act_cnstrs = mkLit(solver->newVar());
        solver->freezeVar(var(act_cycle));
        solver->freezeVar(var(act_cnstrs));

        vec<Sig>       props;
        vec<vec<Sig> > cnstrs;

        // Unroll constraints and liveness properties:
        for (unsigned cycle = 0; cycle <= depth(); cycle++){
            uc.unrollConstraints(cycle, cnstrs);
            uc.unrollLiveProps  (cycle, props);
        }

        // Unroll property in last frame:
        uc.unrollSafeProps(depth(), props);

        // Unroll previous event counters in all frames:
        for (unsigned cycle = 0; cycle <= depth(); cycle++)
            for (LiveProp p = 0; p < event_cnts.size(); p++)
                if (tip.live_props[p].stat == pstat_Unknown)
                    props.push(uc.unroll(event_cnts[p].q, cycle));

        // Extract and unroll internal flops needed for unique state induction:
        if (use_uniq){
            for (unsigned i = 0; i <= depth(); i++){
                needed_flops.push();
                for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                    Sig flp = uc.lookup(*flit, i);
                    if (flp != sig_Undef)
                        needed_flops.last().push(mkSig(*flit));
                }
                // printf("[reset] %d reachable in cycle %d: ", needed_flops.last().size(), i);
                // printSigs(needed_flops.last());
                // printf("\n");
            }

            SSet front;
            for (int i = depth(); i >= 0; i--){
                for (int j = 0; j < needed_flops[i].size(); j++)
                    front.insert(needed_flops[i][j]);
                for (int j = 0; j < front.size(); j++)
                    props.push(uc.unroll(front[j], i));
            }            
        }

        if (use_ind)
            // Unroll property in remaining frames:
            for (unsigned cycle = 0; cycle < depth(); cycle++)
                uc.unrollSafeProps(cycle, props);

        // Extract inputs + flops used in unrolling:
        for (unsigned cycle = 0; cycle <= depth(); cycle++)
            uc.extractUsedInputs(cycle, inputs);
        //uc.extractUsedFlops(0, inputs);
        uc.extractUsedFlops(0, flops);

        // Clausify constant gate:
        cl->clausify(gate_True);

        // Clausify and freeze used input variables:
        for (int i = 0; i < inputs.size(); i++)
            solver->freezeVar(var(cl->clausify(inputs[i])));

        // Clausify and freeze used flop variables:
        for (int i = 0; i < flops.size(); i++)
            solver->freezeVar(var(cl->clausify(flops[i])));

        // Clausify and freeze constraint variables:
        if (cnstrs.size() > 0){
            for (unsigned cycle = 0; cycle <= depth(); cycle++)
                for (int i = 0; i < cnstrs.size(); i++){
                    Sig x = cnstrs[i][0];
                    Lit p = cl->clausify(x);
                    solver->freezeVar(var(p));
                    outputs.push(x);
                    for (int j = 1; j < cnstrs[i].size(); j++){
                        Sig y = cnstrs[i][j];
                        Lit q = cl->clausify(y);
                        solver->freezeVar(var(q));
                        solver->addClause(~act_cnstrs, ~p, q);
                        solver->addClause(~act_cnstrs, ~q, p);
                        outputs.push(y);
                    }
                }
        }

        for (int i = 0; i < props.size(); i++)
            solver->freezeVar(var(cl->clausify(props[i])));

        // Simplify CNF:
        if (cnf_level >= 2){
            solver->use_asymm = tip.main.nGates() < CNF_ASYMM_LIMIT;
            solver->grow = 2;
        }

        //printf(" (before) #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());
        solver->eliminate(true);
        solver->thaw();
        //printf(" (after)  #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());

        // Add all previously existing clauses relevant to the prop-instance:
        for (int i = safe_lim; i < F.size(); i++)
            for (int j = 0; j < F[i].size(); j++){
                assert(F[i][j]->isActive());
                addClause(*F[i][j]);
            }

        for (int i = 0; i < F_inv.size(); i++)
            addClause(*F_inv[i]);
    }


    lbool PropInstance::prove(Sig p, SharedRef<ScheduledClause>& no, unsigned cycle)
    {
        double   time_before = cpuTime();
        Lit      l = cl->clausify(uc.unroll(p, depth()));
        vec<Lit> assumps;
        lbool    result;

        if (use_ind)
            for (unsigned i = 0; i < depth(); i++){
                Sig x = uc.unroll(p, i);
                Lit l = cl->clausify(x);
                assumps.push(l);
            }
        assumps.push(~l);
        assumps.push(act_cnstrs);
        assumps.push(act_cycle);

        //uint32_t conflicts_before = solver->conflicts;
        bool sat;
        for (bool trace_ok = false; !trace_ok; ){
            sat = solver->solve(assumps);
            if (sat && use_uniq){
                // Check for equal states:
                for (int i = depth(); i > 0; i--)
                    for (int j = 0; j < i; j++){
                        bool equal = true;
                        for (int k = 0; equal && k < needed_flops[i].size(); k++){
                            Sig f_i = uc.lookup(needed_flops[i][k], i);
                            Sig f_j = uc.lookup(needed_flops[i][k], j);
                            assert(f_i != sig_Undef);
                            assert(f_j != sig_Undef);
                            assert(cl->lookup(f_i) != lit_Undef);
                            assert(cl->lookup(f_j) != lit_Undef);
                            equal &= (cl->modelValue(f_i) == cl->modelValue(f_j));
                        }

                        if (equal){
                            printf("[prove] equal states %d and %d!\n", j, i);

                            vec<Lit> cls;
                            for (int k = 0; equal && k < needed_flops[i].size(); k++){
                                Lit l_i = cl->lookup(uc.lookup(needed_flops[i][k], i));
                                Lit l_j = cl->lookup(uc.lookup(needed_flops[i][k], j));
                                Lit q   = mkLit(solver->newVar());
                                cls.push(q);

                                solver->addClause(~act_cnstrs, ~q, ~l_i, ~l_j);
                                solver->addClause(~act_cnstrs, ~q,  l_i,  l_j);
                            }
                            solver->addClause(cls);
                            goto next;
                        }
                    }
            }

            trace_ok = true;
        next:;
        }

        if (sat){
            assert(solver->modelValue(l) == l_False);
            // Found predecessor state to a bad state:
            flops.clear();
#if 1
                for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
                    if (uc.lookup(*flit, 0) != sig_Undef)
                        flops.push(mkSig(*flit));
                sort(flops, SigActGt(flop_act));
                //sort(flops, SigActLt(flop_act));
                for (int i = 0; i < flops.size(); i++)
                    flops[i] = uc.lookup(flops[i], 0);
#else
                uc.extractUsedFlops(0, flops);
#endif
            subModel(flops,   *cl, flops_set);
            subModel(inputs,  *cl, inputs_set);
            subModel(outputs, *cl, outputs_set);
            outputs_set.insert(~uc.lookup(p, depth()));
            assert(cl->modelValue(~uc.lookup(p, depth())) == l_True);
            shrinkModel(*solver, *cl, inputs_set, flops_set, outputs_set, max_min_tries, tip.verbosity >= 3);

            vec<vec<lbool> > frames;
            vec<Sig>         clause;
            for (unsigned k = 0; k <= depth(); k++)
                traceInputs(tip, inputs_set, uc, k, frames);
            getClause(tip, flops_set, uc, 0, clause);

            vec<Sig> dummy;
            SharedRef<ScheduledClause> pred(NULL);
            for (unsigned k = depth(); k > 0; k--)
                pred = SharedRef<ScheduledClause>(new ScheduledClause(dummy, cycle+k, frames[k], pred));
            pred = SharedRef<ScheduledClause>(new ScheduledClause(clause, cycle, frames[0], pred));
            DEB(printf("[PropInstance::prove] pred = "));
            DEB(printClause(tip, *pred));
            DEB(printf("\n"));

            no     = pred;
            result = l_False;
        }else{
            // Take away 'act_cycle' and solve again:
            assumps.pop();
            if (!solver->solve(assumps))
                // Property is implied already by invariants:
                result = l_True;
            else
                result = l_Undef;
        }
        cpu_time += cpuTime() - time_before;

        // printf("[prove] conflicts: %d\n", (int)solver->conflicts - conflicts_before);

        return result;
    }


    PropInstance::PropInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, const vec<Clause*>& F_inv_, const vec<EventCounter>& event_cnts_, GMap<float>& flop_act_,
                               int cnf_level_, uint32_t max_min_tries_, int depth, bool use_ind_, bool use_uniq_)
        : tip(t), F(F_), F_inv(F_inv_), event_cnts(event_cnts_), flop_act(flop_act_), 
          uc(t), solver(NULL), cl(NULL), act_cnstrs(lit_Undef), cpu_time(0),
          cnf_level(cnf_level_), max_min_tries(max_min_tries_), depth_(depth), use_ind(use_ind_), use_uniq(use_uniq_)
    {
        reset(0, depth_);
    }


    PropInstance::~PropInstance(){ }

    uint64_t PropInstance::props (){ return solver->propagations; }
    uint64_t PropInstance::solves(){ return solver->solves; }
    double   PropInstance::time  (){ return cpu_time; }
    unsigned PropInstance::depth (){ return depth_; }

    void PropInstance::printStats()
    {
        printf("[prop-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nFreeVars(), (double)solver->nClauses(), (double)solver->conflicts);
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
                activate[c.cycle] = mkLit(solver->newVar());
            xs.push(~activate[c.cycle]);

            cycle_clauses.growTo(c.cycle+1, 0);
            cycle_clauses[c.cycle]++;
        }

        for (unsigned i = 0; i < c.size(); i++)
            xs.push(cl->clausify(uc.unroll(c[i], 0)));
        solver->addClause(xs);
    }


    void StepInstance::resetCycle(unsigned cycle, unsigned num_clauses)
    {
        assert(cycle != cycle_Undef);
        if ((int)cycle < cycle_clauses.size() && (cycle_clauses[cycle] / 2) > num_clauses){
            // Disable all clauses added to this cycle:
            solver->releaseVar(~activate[cycle]);
            cycle_clauses[cycle] = 0;

            // Introduce new activation literal:
            activate[cycle] = mkLit(solver->newVar());

            // Re-add all clauses from this cycle:
            for (int i = 0; i < F[cycle].size(); i++)
                if (F[cycle][i]->isActive())
                    addClause(*F[cycle][i]);

            // Force a solver simplify:
            solver->simplify();
        }
    }


    void StepInstance::reset()
    {
        if (solver != NULL) delete solver;
        if (cl != NULL)     delete cl;

        solver = new SimpSolver();
        cl     = new Clausifyer<SimpSolver>(uc, *solver);

        activate.clear();
        cycle_clauses.clear();
        inputs .clear();
        outputs.clear();
        flops  .clear();

        if (cnf_level == 0)
            solver->eliminate(true);

        act_cnstrs = mkLit(solver->newVar());
        solver->freezeVar(var(act_cnstrs));

        vec<Sig>       props;
        vec<vec<Sig> > cnstrs;

        // Unroll constraints and liveness properties:
        uc.unrollConstraints(0, cnstrs);
        uc.unrollFlopsNext  (0, props);
        uc.unrollLiveProps  (0, props);

        // Unroll previous event counters:
        for (LiveProp p = 0; p < event_cnts.size(); p++)
            if (tip.live_props[p].stat == pstat_Unknown)
                props.push(uc.unroll(event_cnts[p].q, 0));

        // Extract inputs + flops used in unrolling:
        uc.extractUsedInputs(0, inputs);
        uc.extractUsedFlops (0, flops);

        // Clausify and freeze used input variables:
        for (int i = 0; i < inputs.size(); i++)
            solver->freezeVar(var(cl->clausify(inputs[i])));

        // Clausify and freeze used flop variables:
        for (int i = 0; i < flops.size(); i++)
            solver->freezeVar(var(cl->clausify(flops[i])));

        // Clausify and freeze constraint variables:
        if (cnstrs.size() > 0){
            for (int i = 0; i < cnstrs.size(); i++){
                Sig x = cnstrs[i][0];
                Lit p = cl->clausify(x);
                solver->freezeVar(var(p));
                outputs.push(x);
                for (int j = 1; j < cnstrs[i].size(); j++){
                    Sig y = cnstrs[i][j];
                    Lit q = cl->clausify(y);
                    solver->freezeVar(var(q));
                    solver->addClause(~act_cnstrs, ~p, q);
                    solver->addClause(~act_cnstrs, ~q, p);
                    outputs.push(y);
                }
            }
        }

        for (int i = 0; i < props.size(); i++)
            solver->freezeVar(var(cl->clausify(props[i])));

        // Simplify CNF:
        if (cnf_level >= 2){
            solver->use_asymm = tip.main.nGates() < CNF_ASYMM_LIMIT;
            solver->grow = 2;
        }

        //printf(" (before) #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());
        solver->eliminate(true);
        solver->thaw();
        //printf(" (after)  #vars = %d, #clauses = %d\n", solver->nFreeVars(), solver->nClauses());

        // Add all previously existing clauses:
        for (int i = 0; i < F.size(); i++)
            for (int j = 0; j < F[i].size(); j++)
                addClause(*F[i][j]);

        for (int i = 0; i < F_inv.size(); i++)
            addClause(*F_inv[i]);

    }


    bool StepInstance::prove(const Clause& c, Clause& yes, SharedRef<ScheduledClause>& no, SharedRef<ScheduledClause> next)
    {
        DEB(printf("[StepInstance::prove] next = "));
        DEB( (&*next != NULL) ? printClause(tip, *next) : (void)printf("<null>") );
        DEB(printf("\n"));

        assert(next == NULL || &c == (Clause*)&*next);
        assert(c.cycle > 0);
        double   time_before = cpuTime();
        vec<Lit> assumes;
        vec<Lit> actives;

        // Assume proved clauses:
        if (c.cycle != cycle_Undef)
            for (int i = c.cycle-1; i < activate.size(); i++)
                if (activate[i] != lit_Undef){
                    assumes.push(activate[i]);
                    actives.push(activate[i]);
                }

        vec<Sig> clause;
        for (unsigned i = 0; i < c.size(); i++)
            clause.push(c[i]);
        //sort(clause, SigActLt(flop_act));
        sort(clause, SigActGt(flop_act));

        // Assume negation of clause 'c' (outgoing):
        for (int i = 0; i < clause.size(); i++){
            Sig x = tip.flps.next(gate(clause[i])) ^ sign(clause[i]);
            Lit l = cl->clausify(uc.unroll(x, 0));
            assumes.push(~l);
        }
        // Assume constraints:
        assumes.push(act_cnstrs);

        // Try to satisfy clause 'c' (incoming):
        vec<Lit> cls;
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = uc.unroll(c[i], 0);
            Lit l = cl->clausify(x);
            solver->setPolarity(var(l), lbool(!sign(l)));
            cls.push(l);
        }

        if (next == NULL) solver->extend_model = false;
        bool sat = solver->solve(assumes);

        // Undo polarity preference:
        for (int i = 0; i < cls.size(); i++)
            solver->setPolarity(var(cls[i]), l_Undef);

        if (sat){
            // Check if incoming clause was satisfied:
            bool clause_sat = false;
            for (int i = 0; i < cls.size() && !clause_sat; i++)
                if (solver->modelValue(cls[i]) == l_True)
                    clause_sat = true;

            if (!clause_sat){
                // Look for a new model where the clause is guaranteed to be true:
                Lit trigg = mkLit(solver->newVar());
                cls.push(~trigg);
                solver->addClause(cls);
                assumes.push(trigg);
                sat = solver->solve(assumes);
                solver->releaseVar(~trigg);
                // printf("[StepInstance::prove] needed to add induction hypothesis => sat=%d\n", sat);
            }else{
                // printf("[StepInstance::prove] did NOT need to add induction hypothesis.\n");
            }
        }
        solver->extend_model = true;

        bool result;
        if (sat){
            // Found a counter-example:
            if (next != NULL){
                flops.clear();
#if 1
                for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
                    if (uc.lookup(*flit, 0) != sig_Undef)
                        flops.push(mkSig(*flit));

                //sort(flops, SigActLt(flop_act));
                sort(flops, SigActGt(flop_act));
                for (int i = 0; i < flops.size(); i++)
                    flops[i] = uc.lookup(flops[i], 0);
#else
                uc.extractUsedFlops(0, flops);
#endif
                subModel(flops,   *cl, flops_set);
                subModel(inputs,  *cl, inputs_set);

                for (unsigned i = 0; i < c.size(); i++){
                    Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                    outputs.push(uc.lookup(x, 0));
                }
                
                subModel(outputs, *cl, outputs_set);
                outputs.shrink(c.size());

                shrinkModel(*solver, *cl, inputs_set, flops_set, outputs_set, max_min_tries, tip.verbosity >= 3);

                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceInputs(tip, inputs_set, uc, 0, frames);
                getClause(tip, flops_set, uc, 0, clause);

                SharedRef<ScheduledClause> pred(new ScheduledClause(clause, c.cycle-1, frames[0], next));
                DEB(printf("[StepInstance::prove] pred = "));
                DEB(printClause(tip, *pred));
                DEB(printf("\n"));
                no = pred;
            }

            result = false;
        }else{
            // Proved the clause:
            vec<Sig> subset;
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                Lit l = cl->lookup(uc.lookup(x, 0));
                if (solver->conflict.has(l))
                    subset.push(c[i]);
            }
            // What level was sufficient?
            unsigned k = cycle_Undef;
            if (c.cycle != cycle_Undef)
                for (int i = c.cycle-1; i < activate.size(); i++)
                    if (solver->conflict.has(~activate[i])){
                        k = i+1;
                        break;
                    }

            assert(solver->okay());

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


    bool StepInstance::prove(const Clause& c, Clause& yes)
    {
        SharedRef<ScheduledClause> dummy;
        return prove(c, yes, dummy);
    }

    StepInstance::StepInstance(const TipCirc& t, const vec<vec<Clause*> >& F_, const vec<Clause*>& F_inv_, const vec<EventCounter>& event_cnts_, GMap<float>& flop_act_,
                               int cnf_level_, uint32_t max_min_tries_)
        : tip(t), F(F_), F_inv(F_inv_), event_cnts(event_cnts_), flop_act(flop_act_),
          uc(t), solver(NULL), cl(NULL), act_cnstrs(lit_Undef), cpu_time(0), cnf_level(cnf_level_), max_min_tries(max_min_tries_)
    {
        reset();
    }


    StepInstance::~StepInstance(){ }

    uint64_t StepInstance::props (){ return solver->propagations; }
    uint64_t StepInstance::solves(){ return solver->solves; }
    double   StepInstance::time  (){ return cpu_time; }

    void StepInstance::printStats()
    {
        printf("[step-stats] vrs=%8.3g, cls=%8.3g, con=%8.3g\n", 
               (double)solver->nFreeVars(), (double)solver->nClauses(), (double)solver->conflicts);
    }


//=================================================================================================
} // namespace Tip
