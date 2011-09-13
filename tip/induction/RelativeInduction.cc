/****************************************************************************[RelativeInduction.cc]
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
#include "minisat/mtl/Sort.h"
#include "mcl/Clausify.h"
#include "tip/unroll/Unroll.h"
#include "tip/induction/Induction.h"

namespace Tip {

    namespace {

        class Clause {
            unsigned sz     : 31;
            unsigned active :  1;
            Sig*     lits;

        public:
            unsigned cycle;

            template<class Lits>
            Clause(const Lits& xs, unsigned cycle_) : sz(xs.size()), active(1), cycle(cycle_)
            {
                lits = new Sig[sz];
                for (unsigned i = 0; i < sz; i++)
                    lits[i] = xs[i];
                sort(lits, sz);
            }
            Clause() : sz(0), active(1), lits(NULL), cycle(0){}

            Clause(const Clause& c) : sz(c.sz), cycle(c.cycle)
            {
                delete [] lits;
                lits = new Sig[sz];
                for (unsigned i = 0; i < sz; i++)
                    lits[i] = c[i];
                sort(lits, sz);
            }
            ~Clause(){ delete [] lits; }

            Sig      operator[](unsigned i) const { assert(i < sz); return lits[i]; }
            unsigned size      ()           const { return sz; }
            void     deactivate()                 { active = 0; }
            bool     isActive  ()           const { return active; }
        };


        // Check that d contains c (uses the fact that c and d are sorted).
        bool subsumes(const Clause& c, const Clause& d)
        {
            if (d.size() > c.size() || d.cycle > c.cycle)
                return false;

            unsigned i,j;
            for (i = j = 0; i < c.size(); j++)
                if (c[i] < d[j])
                    return false;
                else if (c[i] == d[j])
                    i++;
            return true;
        }


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


        struct ScheduledClause : public Clause {
            Inputs           inputs;
            ScheduledClause* next;
            template<class Lits, class Inps>
            ScheduledClause(const Lits& xs, unsigned cycle_, const Inps& is, ScheduledClause* next_)
                : Clause(xs, cycle_), inputs(is), next(next_){}

            ScheduledClause() : next(NULL){}

            ScheduledClause(const ScheduledClause& sc)
                : Clause(sc), inputs(sc.inputs), next(sc.next){}

            // TODO:
            // ~ScheduledClause()
            // {
            // ???
            // }
        };

        class InitInstance {
            const TipCirc&      tip;
            const vec<Clause*>& proved;

            SimpSolver*    init;
            GMap<Lit>      init_map;
            VMap<Sig>      init_map_inv;
            vec<Lit>       init_inp0;
            vec<Lit>       init_inp1;

            void reset();

        public:
            InitInstance(const TipCirc& tip_, const vec<Clause*>& proved_);
            ~InitInstance();

            bool prove(const ScheduledClause* c, Clause& yes, ScheduledClause*& no);
            bool prove(const Clause& c,          Clause& yes);
        };


        void InitInstance::reset()
        {
            // Clear solver:
            delete init;
            init = new SimpSolver();

            // Unroll proper number of steps:
            Circ                   uc;                        // Unrolled circuit.
            vec<IFrame>            ui;                        // Unrolled set of input frames.
            UnrollCirc             unroll(tip, ui, uc, true); // Unroller-helper object.
            Clausifyer<SimpSolver> cl(uc, *init);
            GMap<Sig>              umap;
            unroll(umap);

            // Extract the references to literals that is relevant for the instance (flop inputs and outputs):
            init_map.clear();
            init_map.growTo(tip.main.lastGate(), lit_Undef);
            for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
                Gate flp_in  = *flit;
                Sig  flp_out = tip.flps.next(flp_in);
                Lit  lit_in  = cl.clausify(flp_in);
                Lit  lit_out = cl.clausify(flp_out);

                init_map[flp_in]        = lit_in;
                init_map[gate(flp_out)] = lit_out ^ sign(flp_out);
                init->freezeVar(var(lit_in));
                init->freezeVar(var(lit_out));

                init_map_inv.reserve(var(lit_in),  sig_Undef);
                init_map_inv.reserve(var(lit_out), sig_Undef);
                init_map_inv[var(lit_in)]  = mkSig(flp_in);
                init_map_inv[var(lit_out)] = flp_out ^ sign(lit_out);
            }

            // Extract inverse map:
            init_map_inv.clear();
            for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git){
                Lit l = init_map[*git];
                if (l != lit_Undef)
                    init_map_inv[var(l)] = mkSig(*git, sign(l));
            }

            // Simplify CNF:
            init->eliminate(true);
            init->thaw();

            
        }


        bool InitInstance::prove(const ScheduledClause* c, Clause& yes, ScheduledClause*& no)
        {
            // TODO: also assume 'c' in cycle 0.
            vec<Lit> assumes;
            for (int i = 0; i < c.size(); i++){
                Sig x = ~(tip.flps.next(gate(c[i])) ^ sign(x));
                assumes.push(init_map[gate(x)] ^ sign(x));
            }

            if (init->solve(assumes)){
                // Found a counter-example:

            }else{
            }
        }

        bool InitInstance::prove(const Clause& c, Clause& true_d, ScheduledClause*& false_trace)
        {
            // TODO: also assume 'c' in cycle 0.
            vec<Lit> assumes;
            for (int i = 0; i < c.size(); i++){
                Sig x = ~(tip.flps.next(gate(c[i])) ^ sign(x));
                assumes.push(init_map[gate(x)] ^ sign(x));
            }

            if (init->solve(assumes)){
                // Found a counter-example:
            }else{
            }
        }


        InitInstance::InitInstance(const TipCirc& tip_, const vec<Clause*>& proved_) : tip(tip_), proved(proved_)
        {
            reset();
        }


        InitInstance::~InitInstance(){ delete init; }


        //===================================================================================================
        // Temporal Relative Induction Prover
        class Trip {
            TipCirc&             tip;

            // Solver independent data:

            //vec<vec<Clause*> >   F; // Is this really needed?
            vec<Clause*>         proved;     // All proved clauses.
            vec<unsigned>        cycle_size; // Number of proved clauses in each cycle.

            vec<vec<ScheduledClause*> > 
                                 clause_queue;
            SMap<vec<Clause*> >  bwd_occurs;
            SMap<vec<Clause*> >  fwd_occurs;

            // Solver data. Should be rederivable from only independent data:

            SimpSolver*          step;
            GMap<Lit>            step_map;
            vec<Lit>             step_tags;
            vec<Lit>             step_inp0;

            SimpSolver*          prop;
            GMap<Lit>            prop_map;
            Lit                  prop_tag;
            vec<Lit>             prop_inp0;
            vec<Lit>             prop_inp1;

            void                 mkInitInstance();
            void                 mkStepInstance();
            void                 mkPropInstance();


            // PROVE:   Init ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in cycle 1,
            //       or False and the starting point of a counter-example trace.
            bool             proveInit(const Clause& c, Clause& true_d, ScheduledClause*& false_trace);

            // PROVE:   let k = c.cycle: F[k-1] ^ c ^ Trans => c'
            // RETURNS: True and a stronger clause d (subset of c) that holds in some cycle >= k,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveStep(const Clause& c, Clause& true_d, ScheduledClause*& false_trace);
            bool             proveStep(const Clause& c, Clause& true_d);

            // PROVE:   let k = F.size()-1: F[k] ^ Trans => prop'
            // RETURNS: True and a new frame F[k+1] can be opened,
            //       or False and a new clause predecessor to be proved in cycle k-1.
            bool             proveProp(Sig prop, ScheduledClause*& false_trace);

            // Prove all scheduled clauses. Returns true if all properties are decided, and false otherwise.
            bool             propagate    ();

            // Try to push clauses forwards, particularily push clauses forward into the newly opened last
            // frame. Returns true if an invariant is found and false otherwise.
            bool             push         ();

            // Add a proved clause 'c'. Returns true if this causes an invariant to be found, and false
            // otherwise.
            bool             addClause    (const Clause& c);

            // Remove a proved clause 'c'. Returns true if this causes an invariant to be found,
            // and false otherwise.
            bool             removeClause (Clause* c);

            // Check if clause 'c' is subsumed by any previously proved clause. Returns true if it is and
            // false otherwise.
            bool             fwdSubsumed  (Clause* c);

            // Find and remove all previously proved claues that are subsumed by the new clause 'c'. If an
            // invariant is found true is returned, otherwise false.
            bool             bwdSubsume   (Clause* c);

            void             enqueueClause(ScheduledClause* sc);
            ScheduledClause* getMinClause ();

            // Returns the failing property, extracts the trace that leads to the failure, and removes all
            // scheduled clauses rooted in the same property.
            SafeProp         extractTrace (ScheduledClause* trace, vec<vec<lbool> >& frames);

            // Returns number of states in unrolling.
            unsigned         size() const;

            // Fill all active clauses such that the clause 'c' is in out[c.cycle].
            void             clausesByCycle(vec<vec<Clause*> >& out);

        public:
            Trip(TipCirc& tip_) : tip(tip_)
            {
                cycle_size.push(0);
            }

            // Prove or disprove all properties using depth k. Returns true if all properties are decided, and
            // false if there are still some unresolved property.
            bool decideCycle();

            // Prove that the necessary number of initial cycles are bug free. Returns true if all properties
            // are resolved (i.e. all properties were falsifiable), and false otherwise.
            bool baseCase();

            void printStats();
        };


        void Trip::mkInitInstance()
        {
            // SimpSolver*          init;
            // GMap<Lit>            init_map;

            // TODO: would like this.
            // init.clear();

        }


        void Trip::mkStepInstance()
        {
            // SimpSolver           step;
            // GMap<Lit>            step_map;
            // vec<Lit>             step_tags;

        }


        void Trip::mkPropInstance()
        {
            // SimpSolver           prop;
            // GMap<Lit>            prop_map;
            // Lit                  prop_tag;

        }


        void Trip::enqueueClause(ScheduledClause* sc)
        {
            clause_queue.growTo(sc->cycle+1);
            clause_queue[sc->cycle].push(sc);
        }


        ScheduledClause* Trip::getMinClause()
        {
            // Naive implementation:
            int i;
            for (i = 0; i < clause_queue.size() && clause_queue[i].size() == 0; i++)
                ;

            if (i == clause_queue.size())
                return NULL;

            ScheduledClause* result = clause_queue[i].last();
            clause_queue[i].pop();
            return result;
        }


        bool Trip::removeClause(Clause* c)
        {
            // Don't remove clauses from the last frame. The last frame is not yet completed and if
            // it becomes empty this does not indicate that an invariant has been found.
            assert(c->cycle < cycle_size.size()-1);

            --cycle_size[c->cycle];
            c->deactivate();

            // Assume that there was no empty set before:
            assert(cycle_size[c->cycle] > 0 || cycle_size[c->cycle+1] > 0);

            return cycle_size[c->cycle] == 0;
        }

        unsigned Trip::size() const { return cycle_size.size(); }


        bool Trip::addClause(const Clause& c_)
        {
            assert(!fwdSubsumed(&c_));

            // TODO: more here?
            proved.push(new Clause(c_));
            const Clause& c = *proved.last();
            cycle_size[c.cycle]++;

            // Attach to backward subsumption index:
            for (unsigned i = 0; i < c.size(); i++){
                bwd_occurs.growTo(c[i]);
                bwd_occurs[c[i]].push(proved.last());
            }

            // Attach to forward subsumption index:
            int min_index = 0;
            int min_size  = fwd_occurs.has(c[0]) ? fwd_occurs[c[0]].size() : 0;
            for (unsigned i = 1; i < c.size(); i++){
                Sig x    = c[i];
                int size = fwd_occurs.has(x) ? fwd_occurs[x].size() : 0;
                if (size < min_size){
                    min_size  = size;
                    min_index = i;
                }
            }
            fwd_occurs.growTo(c[min_index]);
            fwd_occurs[c[min_index]].push(proved.last());

            return bwdSubsume(proved.last());
        }
        

        // PRECONDITION: (incomplete?) 'c' must not already exist in the forward subsumption index.
        bool Trip::fwdSubsumed(Clause* c)
        {
            for (unsigned i = 0; i < c->size(); i++){
                Sig x = (*c)[i];
                if (!fwd_occurs.has(x))
                    continue;

                for (int j = 0; j < fwd_occurs[x].size(); j++)
                    if (fwd_occurs[x][j]->isActive() && subsumes(*fwd_occurs[x][j], *c))
                        return true;
            }
            return false;
        }
        

        bool Trip::bwdSubsume(Clause* c)
        {
            assert(bwd_occurs.has((*c)[0]));
            int min_index = 0;
            int min_size  = bwd_occurs[(*c)[0]].size();
            for (unsigned i = 1; i < c->size(); i++){
                assert(bwd_occurs.has((*c)[i]));
                Sig x    = (*c)[i];
                int size = bwd_occurs[x].size();
                if (size < min_size){
                    min_size  = size;
                    min_index = i;
                }
            }

            const vec<Clause*>& occ = bwd_occurs[(*c)[min_index]];

            for (int i = 0; i < occ.size(); i++)
                if (occ[i] != c && occ[i]->isActive() && subsumes(*c, *occ[i]))
                    removeClause(occ[i]);

            return false;
        }


        bool Trip::push()
        {
            vec<vec<Clause*> > F; clausesByCycle(F);
            Clause d;
            for (unsigned i = 1; i < size()-1; i++)
                for (int j = 0; j < F[i].size(); j++){
                    // NOTE: it is assumed here that proveStep will at least try to prove the
                    // clause in the next cycle as well.
                    if (proveStep(*F[i][j], d)){
                        if (addClause(d))
                            return true;
                        if (removeClause(F[i][j]))
                            return true;
                    }
                }

            return false;
        }

        bool Trip::propagate()
        {
            for (;;){
                ScheduledClause* sc = getMinClause();

                if (sc == NULL)
                    break;

                ScheduledClause* pred;
                Clause           minimized;

                if (sc->cycle == 0){
                    // Handle initial cycle:
                    if (proveInit(*sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized.cycle+1;
                        if (sc->cycle < size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        Trace             cex    = tip.newTrace();
                        vec<vec<lbool> >& frames = tip.traces[cex].frames;
                        SafeProp          p      = extractTrace(pred, frames);
                        tip.safe_props[p].stat   = pstat_Falsified;
                        tip.safe_props[p].cex    = cex;
                        delete sc;
                        delete pred;
                    }

                }else{
                    // Handle arbitrary non-initial cycle:
                    if (proveStep(*sc, minimized, pred)){
                        addClause(minimized);
                        sc->cycle = minimized.cycle+1;
                        if (sc->cycle < size())
                            enqueueClause(sc);
                        else
                            delete sc;
                    }else{
                        enqueueClause(pred);
                        enqueueClause(sc);
                    }
                }
            }

            return false;
        }


        bool Trip::decideCycle()
        {
            ScheduledClause* pred;
            for (SafeProp p = 0; p < tip.safe_props.size(); p++)
                if (tip.safe_props[p].stat != pstat_Unknown)
                    if (!proveProp(tip.safe_props[p].sig, pred)){
                        enqueueClause(pred);
                        if (propagate())
                            return true;
                    }

            // At this point we know that all properties are implied in cycle k+1. Expand a new frame and push
            // clauses forward as much as possible:
            cycle_size.push(0);
            return push();
        }


        void Trip::printStats()
        {
            vec<vec<Clause*> > F; clausesByCycle(F);
            printf("%d: ", size());
            for (unsigned i = 0; i < size(); i++)
                printf("%d ", F[i].size());
        }


        void Trip::clausesByCycle(vec<vec<Clause*> >& out)
        {
            for (int i = 0; i < proved.size(); i++)
                if (proved[i]->isActive()){
                    out.growTo(proved[i]->cycle+1);
                    out[proved[i]->cycle].push(proved[i]);
                }
        }

    };


    void relativeInduction(TipCirc& tip)
    {
        Trip trip(tip);

        if (!trip.baseCase())
            while (!trip.decideCycle())
                trip.printStats();
    }


//=================================================================================================
} // namespace Tip
