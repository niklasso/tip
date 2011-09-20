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
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/TripProofInstances.h"

namespace Tip {

    namespace {

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


        void extractProps(const TipCirc& tip, const GMap<Sig>& umap,
                          Clausifyer<SimpSolver>& cl, SimpSolver& solver, GMap<Lit>& umapl, vec<Lit>& xs)
        {
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat == pstat_Unknown){
                    Sig prop          = tip.safe_props[p].sig;
                    Lit lit           = cl.clausify(umap[gate(prop)] ^ sign(prop));
                    umapl[gate(prop)] = lit ^ sign(prop);
                    solver.freezeVar(var(lit));
                    xs.push(lit);
                }
        }


        // Minimize set of 'xs' that falsifies one of 'top':
        void shrinkModelOnce(SimpSolver& s, vec<Lit>& xs, const vec<Lit>& top)
        {
            // printf(" ... xs-in: {");
            for (int i = 0; i < xs.size(); i++){
                assert(s.modelValue(xs[i]) == l_True);
                // printf("%s%d ", sign(xs[i])?"-":"", var(xs[i]));
            }
            // printf("}\n");

            for (int i = 0; i < top.size(); i++)
                assert(s.modelValue(top[i]) == l_True);

            // Simple variant for now:
            Lit      trigg = mkLit(s.newVar());
            vec<Lit> clause;
            for (int i = 0; i < top.size(); i++)
                clause.push(~top[i]);
            clause.push(~trigg);
            s.addClause(clause);

            xs.push(trigg);
            bool res = s.solve(xs);
            xs.pop();
            assert(res == false);
            s.addClause(~trigg);

            // Check 's.conflict' and remove literals not present there:
            int i,j;
            for (i = j = 0; i < xs.size(); i++)
                if (find(s.conflict, ~xs[i]))
                    xs[j++] = xs[i];
            xs.shrink(i - j);

            // printf(" ... xs-out: { ");
            // for (int i = 0; i < xs.size(); i++)
            //     printf("%s%d ", sign(xs[i])?"-":"", var(xs[i]));
            // printf("}\n");
        }


        class InstanceModel {
            vec<Lit> inputs;
        public:
            InstanceModel(const vec<Lit>& inps, const SimpSolver& s)
            {
                for (int i = 0; i < inps.size(); i++){
                    assert(s.modelValue(inps[i]) != l_Undef);
                    inputs.push(inps[i] ^ (s.modelValue(inps[i]) == l_False));
                }
            }
            InstanceModel(const vec<Lit>& inps){ copy(inps, inputs); }

            int   size      ()       const { return inputs.size(); }
            Lit   operator[](int i)  const { return inputs[i]; }
            void  copyTo    (vec<Lit>& out) const { inputs.copyTo(out); }

            lbool value     (Gate g, const GMap<Lit>& umap) const
            {
                // TODO: naive implementation for now.
                return find(inputs, umap[g]) ? l_True : find(inputs, ~umap[g]) ? l_False : l_Undef; 
            }
        };

        void traceResetInputs(const TipCirc& tip, const InstanceModel& model, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (InpIt iit = tip.init.inpBegin(); iit != tip.init.inpEnd(); ++iit){
                Gate inp = *iit;
                assert(tip.init.number(inp) != UINT32_MAX); // Inputs must be numbered.
                frames.last().growTo(tip.init.number(inp)+1, l_Undef);
                frames.last()[tip.init.number(inp)] = model.value(inp, umapl);
            }
        }


        void traceInputs(const TipCirc& tip, const InstanceModel& model, const GMap<Lit>& umapl, vec<vec<lbool> >& frames)
        {
            frames.push();
            for (TipCirc::InpIt iit = tip.inpBegin(); iit != tip.inpEnd(); ++iit){
                Gate inp = *iit;
                assert(tip.main.number(inp) != UINT32_MAX); // Inputs must be numbered.
                frames.last().growTo(tip.main.number(inp)+1, l_Undef);
                frames.last()[tip.main.number(inp)] = model.value(inp, umapl);
            }
        }


        void getClause(const TipCirc& tip, const InstanceModel& model, const GMap<Lit>& umapl, vec<Sig>& xs)
        {
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                lbool val = model.value(*flit, umapl);
                if (val != l_Undef)
                    xs.push(mkSig(*flit, val == l_True));
            }
        }
    }

    //===================================================================================================
    // Implementation of InitInstance:

    void InitInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl[0].clear();
        umapl[0].growTo(tip.init.lastGate(), lit_Undef);
        umapl[1].clear();
        umapl[1].growTo(tip.main.lastGate(), lit_Undef);

        // Unroll proper number of steps:
        Circ                   uc;                       // Unrolled circuit.
        GMap<Sig>              umap[2];                  // Map for circuit unrollings.
        UnrollCirc2            unroll(tip, uc, umap[0]); // Unroller-helper object.
        Clausifyer<SimpSolver> cl(uc, *solver);
        unroll(umap[1]);

        // Extract all needed references:
        extractResetInputs(tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[1], cl, *solver, umapl[1], inputs);
        extractFlopOuts   (tip, umap[1], cl, *solver, umapl[1], inputs);

        // Simplify CNF:
        solver->eliminate(true);
        solver->thaw();
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

    bool InitInstance::prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next)
    {
        assert(next == NULL || &c == (Clause*)next);

        vec<Lit> assumes;
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
            Lit l = umapl[1][gate(x)] ^ sign(x);
            assert(l != lit_Undef);
            assumes.push(~l);
        }

        if (solver->solve(assumes)){
            // Found a counter-example:
            if (next != NULL){
                InstanceModel model(inputs, *solver);
                vec<Lit> shrunk; model.copyTo(shrunk);
                shrinkModelOnce(*solver, shrunk, assumes);

                InstanceModel    shrunk_model(shrunk);
                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceResetInputs(tip, shrunk_model, umapl[0], frames);
                traceInputs     (tip, shrunk_model, umapl[1], frames);

                vec<Sig>         dummy;
                ScheduledClause* pred0    = new ScheduledClause(dummy, 0, frames[1], next);
                ScheduledClause* pred_rst = new ScheduledClause(dummy, 0, frames[0], pred0);
                //printf("[InitInstance::prove] pred0 = %p, pred_rst = %p\n", pred0, pred_rst);
                no = pred_rst;
            }

            return false;
        }else{
#if 0
            // Proved the clause:
            // does not shrink properly when multiple signals map to the same literal:
            vec<Sig> subset;
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                Lit l = umapl[1][gate(x)] ^ sign(x);
                if (find(solver->conflict, l))
                    subset.push(c[i]);
            }
            yes = Clause(subset, 0);
            //printf("[InitInstance::prove] &yes = %p\n", &yes);
            return true;
#else
            vec<SigLitPair> slits;
            for (unsigned i = 0; i < c.size(); i++){
                SigLitPair p;
                p.x   = c[i];
                Sig x = tip.flps.next(gate(p.x)) ^ sign(p.x);
                p.l   = umapl[1][gate(x)] ^ sign(x);
                slits.push(p);
            }

            sort(slits, SigLitCmp());

            // printf(" .. slits-before = ");
            // for (int i = 0; i < slits.size(); i++)
            //     printf("%s%d:%s%d ", 
            //            sign(slits[i].x)?"~":"", index(gate(slits[i].x)),
            //            sign(slits[i].l)?"~":"", var(slits[i].l));
            // printf("\n");
            
            int i,j;
            for (i = j = 1; i < slits.size(); i++)
                if (slits[i].l != slits[j-1].l)
                    slits[j++] = slits[i];
            slits.shrink(i-j);

            // if (i - j > 0)
            //     printf("[InitInstance::prove] potential reason shrunk with: %d\n", i - j);
            
            // printf(" .. slits-after = ");
            // for (int i = 0; i < slits.size(); i++)
            //     printf("%s%d:%s%d ", 
            //            sign(slits[i].x)?"~":"", index(gate(slits[i].x)),
            //            sign(slits[i].l)?"~":"", var(slits[i].l));
            // printf("\n");

            vec<Sig> subset;
            for (int i = 0; i < slits.size(); i++)
                if (find(solver->conflict, slits[i].l))
                    subset.push(slits[i].x);
            yes = Clause(subset, 0);

            return true;
#endif

        }
    }


    InitInstance::InitInstance(const TipCirc& t) : tip(t), solver(NULL)
    {
        reset();
    }


    InitInstance::~InitInstance(){ delete solver; }

    //===================================================================================================
    // Implementation of PropInstance:

    void PropInstance::clearClauses(){ reset(); }
    void PropInstance::addClause(const Clause& c)
    {
        vec<Lit> xs;
        for (unsigned i = 0; i < c.size(); i++)
            xs.push(umapl[0][gate(c[i])] ^ sign(c[i]));
        solver->addClause(xs);
    }


    void PropInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl[0].clear();
        umapl[0].growTo(tip.main.lastGate(), lit_Undef);
        umapl[1].clear();
        umapl[1].growTo(tip.main.lastGate(), lit_Undef);

        // Unroll proper number of steps:
        Circ                   uc;              // Unrolled circuit.
        GMap<Sig>              umap[2];         // Map for circuit unrollings.
        UnrollCirc2            unroll(tip, uc); // Unroller-helper object.
        Clausifyer<SimpSolver> cl(uc, *solver);
        unroll(umap[0]);
        unroll(umap[1]);

        // Extract all needed references:
        extractFlopIns    (tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[0], cl, *solver, umapl[0], inputs);
        extractInputs     (tip, umap[1], cl, *solver, umapl[1], inputs);
        extractProps      (tip, umap[1], cl, *solver, umapl[1], outputs);

        // Simplify CNF:
        solver->eliminate(true);
        solver->thaw();
    }


    bool PropInstance::prove(Sig p, ScheduledClause*& no, unsigned cycle)
    {
        Lit l = umapl[1][gate(p)] ^ sign(p);
        if (solver->solve(~l)){
            // Found predecessor state to a bad state:
            InstanceModel model(inputs, *solver);
            vec<Lit> shrunk; model.copyTo(shrunk);
            vec<Lit> outputs;
            outputs.push(~l);
            shrinkModelOnce(*solver, shrunk, outputs);
                
            InstanceModel    shrunk_model(shrunk);
            vec<vec<lbool> > frames;
            vec<Sig>         clause;
            traceInputs(tip, shrunk_model, umapl[0], frames);
            traceInputs(tip, shrunk_model, umapl[1], frames);
            getClause  (tip, shrunk_model, umapl[0], clause);

            vec<Sig> dummy;
            ScheduledClause* last = new ScheduledClause(dummy,  cycle+1, frames[1], NULL);
            ScheduledClause* pred = new ScheduledClause(clause, cycle,   frames[0], last);
            //printf("[PropInstance::prove] last = %p, pred = %p\n", last, pred);
            no = pred;

            return false;
        }else
            return true;
    }

    PropInstance::PropInstance(const TipCirc& t, const vec<Clause*>& pr)
        : tip(t), proved(pr), solver(NULL)
    {
        reset();
    }


    PropInstance::~PropInstance(){ delete solver; }

    //===================================================================================================
    // Implementation of StepInstance:


    void StepInstance::addClause(const Clause& c)
    {
        vec<Lit> xs;
        assert(c.cycle != UINT_MAX);
        activate.growTo(c.cycle+1, lit_Undef);
        if (activate[c.cycle] == lit_Undef)
            activate[c.cycle] = mkLit(solver->newVar());
        xs.push(~activate[c.cycle]);

        for (unsigned i = 0; i < c.size(); i++)
            xs.push(umapl[gate(c[i])] ^ sign(c[i]));
        solver->addClause(xs);
    }


    void StepInstance::reset()
    {
        // Clear solver & gate to solver maps:
        delete solver;
        solver = new SimpSolver();
        umapl.clear();
        umapl.growTo(tip.main.lastGate(), lit_Undef);

        // Unroll proper number of steps:
        Clausifyer<SimpSolver> cl(tip.main, *solver);

        // FIXME: ugly, but will do for now.
        GMap<Sig> id(tip.main.lastGate(), sig_Undef);
        for (GateIt git = tip.main.begin0(); git != tip.main.end(); ++git)
            id[*git] = mkSig(*git);

        // Extract all needed references:
        extractFlopIns (tip, id, cl, *solver, umapl, inputs);
        extractInputs  (tip, id, cl, *solver, umapl, inputs);
        extractFlopOuts(tip, id, cl, *solver, umapl, outputs);

        // Simplify CNF:
        solver->eliminate(true);
        solver->thaw();
    }


    bool StepInstance::prove(const Clause& c, Clause& yes, ScheduledClause*& no, const ScheduledClause* next)
    {
        assert(next == NULL || &c == (Clause*)next);
        assert(c.cycle > 0);
        vec<Lit> outputs;
        vec<Lit> inputs;
        vec<Lit> assumes;
        this->inputs.copyTo(inputs);

        // Assume negation of clause 'c':
        for (unsigned i = 0; i < c.size(); i++){
            Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
            Lit l = umapl[gate(x)] ^ sign(x);
            assert(l != lit_Undef);
            outputs.push(~l);
            assumes.push(~l);
        }

        // Assume proved clauses:
        for (int i = c.cycle-1; i < activate.size(); i++)
            if (activate[i] != lit_Undef){
                assumes.push(activate[i]);
                inputs .push(activate[i]);
            }

        // TODO: also assume the clause itself!

        if (solver->solve(assumes)){
            // Found a counter-example:
            if (next != NULL){
                InstanceModel model(inputs, *solver);
                vec<Lit> shrunk; model.copyTo(shrunk);
                shrinkModelOnce(*solver, shrunk, outputs);

                InstanceModel    shrunk_model(shrunk);
                vec<vec<lbool> > frames;
                vec<Sig>         clause;
                traceInputs     (tip, shrunk_model, umapl, frames);
                getClause       (tip, shrunk_model, umapl, clause);

                ScheduledClause* pred = new ScheduledClause(clause, c.cycle-1, frames[0], next);
                //printf("[StepInstance::prove] pred = %p\n", pred);
                no = pred;
            }

            return false;
        }else{
            // Proved the clause:
            vec<Sig> subset;
            for (unsigned i = 0; i < c.size(); i++){
                Sig x = tip.flps.next(gate(c[i])) ^ sign(c[i]);
                Lit l = umapl[gate(x)] ^ sign(x);
                if (find(solver->conflict, l))
                    subset.push(c[i]);
            }

            // What level was sufficient?
            int k = UINT32_MAX;
            for (int i = c.cycle-1; i < activate.size(); i++)
                if (find(solver->conflict, ~activate[i])){
                    k = i+1;
                    break;
                }

            yes = Clause(subset, k);
            //printf("[StepInstance::prove] &yes = %p\n", &yes);
            return true;
        }
    }

    StepInstance::StepInstance(const TipCirc& t, const vec<Clause*>& pr)
        : tip(t), proved(pr), solver(NULL)
    {
        reset();
    }


    StepInstance::~StepInstance(){ delete solver; }




//=================================================================================================
} // namespace Tip
