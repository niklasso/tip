/**************************************************************************************[Extract.cc]
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
#include "minisat/utils/System.h"
#include "mcl/Circ.h"
#include "mcl/Clausify.h"
#include "tip/constraints/Extract.h"
#include "tip/unroll/Unroll.h"

namespace Tip {

namespace {

template<class Clausifyer>
bool initializeCands            (const TipCirc& tip, Solver& s, Clausifyer& cl, vec<Sig>& cands, bool only_coi);

bool refineCandsBaseInSequence  (const TipCirc& tip, vec<Sig>& cands, bool only_coi = false);
void refineCandsStepInSequence  (const TipCirc& tip, vec<Sig>& cands);
bool refineCandsBaseWithMinimize(const TipCirc& tip, vec<Sig>& cands, bool only_coi = false);
void refineCandsStepWithMinimize(const TipCirc& tip, vec<Sig>& cands);

bool solveMinimum(Solver& s, const vec<Lit>& assumps, const vec<Lit>& ps, vec<lbool>& min_model, Lit trigger = lit_Undef);
bool solveMinimum(Solver& s, const vec<Lit>& ps, vec<lbool>& min_model, Lit trigger = lit_Undef)
{
    vec<Lit> dummy_assumps;
    return solveMinimum(s, dummy_assumps, ps, min_model, trigger);
}

//=================================================================================================
// File Local helpers:

// TODO: this should be moved to some general library of algorithms / techniques.
bool solveMinimum(Solver& s, const vec<Lit>& assumps, const vec<Lit>& ps, vec<lbool>& min_model, Lit trigger)
{
    for (int i = 0; i < ps.size(); i++)
        s.setPolarity(var(ps[i]), lbool(!sign(ps[i])));

    vec<Lit> assume;
    bool     satisfied = false;

    // TODO: simplify use of assume, maybe use litset?
    assumps.copyTo(assume);
    for (;;){
        if (trigger != lit_Undef)
            assume.push(trigger);

        if (s.solve(assume)){
            satisfied = true;
            s.model.copyTo(min_model);

            assumps.copyTo(assume);
            vec<Lit> blocking_clause;
            for (int i = 0; i < ps.size(); i++)
                if (s.modelValue(ps[i]) == l_False)
                    assume.push(~ps[i]);
                else
                    blocking_clause.push(~ps[i]);

            // printf("[solveMinimum] #true = %d\n", blocking_clause.size());

            if (trigger != lit_Undef)
                blocking_clause.push(~trigger);

            s.addClause(blocking_clause);
        }else
            break;
    }

    for (int i = 0; i < ps.size(); i++)
        s.setPolarity(var(ps[i]), l_Undef);

    return satisfied;
}

template<class Clausifyer>
bool initializeCands(const TipCirc& tip, Solver& s, Clausifyer& cl, vec<Sig>& cands, bool only_coi)
{
#if 0
    // For testing: make sure that all of the circuit is included as candidates:
    for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git)
        cl.clausify(*git);
#endif

    // If we dont only want what is in the property cone-of-influence as candidates, also clausify
    // what's reachable from flops:
    if (!only_coi)
        for (SeqCirc::FlopIt f = tip.flpsBegin(); f != tip.flpsEnd(); ++f)
            cl.clausify(tip.flps.next(*f));
    // TODO: do we miss important candidates with the skipped gates (not in cone-of-influence of
    // some property)? Yes, but check how much!
    
    // State that some property should be false:
    vec<Lit> some_bad;
    for (SafeProp p = 0; p < tip.safe_props.size(); p++)
        if (tip.safe_props[p].stat == pstat_Unknown)
            some_bad.push(~cl.clausify(tip.safe_props[p].sig));
    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown)
            // NOTE: this is sound but weaker than what is possible.
            for (int i = 0; i < tip.live_props[p].sigs.size(); i++)
                some_bad.push(cl.clausify(tip.live_props[p].sigs[i]));
    s.addClause(some_bad);
    
    if (!s.solve()) return false;

    GMap<lbool> model;
    int         n_skipped = 0;
    for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git){
        lbool val = cl.modelValue(*git, model);
        if (val != l_Undef)
            cands.push(mkSig(*git, val == l_False));
        else
            n_skipped++;
    }
    if (tip.verbosity >= 2)
        printf("[initializeCands] prepared %d initial constraint candidates, skipping %d.\n",
               cands.size(), n_skipped);

    return true;
}


// Note: candidate outputs are topologically ordered which may be useful ...
bool refineCandsBaseInSequence(const TipCirc& tip, vec<Sig>& cands, bool only_coi)
{
    Solver             s;
    Clausifyer<Solver> cl(tip.main, s);
    int                n_skipped = 0;

    if (!initializeCands(tip, s, cl, cands, only_coi))
        return false;

    // Set preferred polarity for candidates to try to falsify as many as possible in each model:
    for (int i = 0; i < cands.size(); i++){
        Lit l = cl.lookup(cands[i]);
        if (l != lit_Undef)
            s.setPolarity(var(l), lbool(!sign(l)));
    }

    for (int i = 0; i < cands.size(); ){
        if (tip.verbosity >= 2)
            printf("[refineCandsBaseInSequence] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        if (s.solve(cl.clausify(~cands[i]))){
            // Candidate not implied by the bad states, remove it and all others that also are
            // false:
            GMap<lbool> model;
            int         j,k;
            for (j = k = i; j < cands.size(); j++){
                if (cl.modelValue(cands[j], model) == l_True)
                    cands[k++] = cands[j];
                else {
                    if (cl.modelValue(cands[j], model) == l_Undef)
                        n_skipped++;

                    // Unset preferred polarity:
                    Lit l = cl.lookup(cands[j]);
                    if (l != lit_Undef)
                        s.setPolarity(var(l), l_Undef);
                }
            }
            cands.shrink(j - k);
        }else
            i++;
    }

    if (tip.verbosity >= 2)
        printf("[refineCandsBaseInSequence] prepared %d final constraint candidates, skipping %d.\n",
               cands.size(), n_skipped);

    return true;
}


// Note: candidate outputs are topologically ordered which may be useful ...
bool refineCandsBaseWithMinimize(const TipCirc& tip, vec<Sig>& cands, bool only_coi)
{
    Solver                           s;
    Clausifyer<Solver, false, false> cl(tip.main, s);
    vec<lbool>                       min_model;
    int                              i,j;

    if (!initializeCands(tip, s, cl, cands, only_coi))
        return false;

    for (unsigned int i = 0; i < tip.cnstrs.size(); i++) {
        Lit rep = cl.clausify(tip.cnstrs[i][0]);
        for (int j = 1; j < tip.cnstrs[i].size(); j++)
          cl.clausifyAs(tip.cnstrs[i][j],rep);
    }

    do {
        if (tip.verbosity >= 2)
            printf("[refineCandsBaseWithMinimize] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        vec<Lit> cands_lit;
        for (int k = 0; k < cands.size(); k++)
            cands_lit.push(cl.clausify(cands[k]));

        if (!solveMinimum(s, cands_lit, min_model))
            break;

        for (i = j = 0; i < cands.size(); i++){
            Lit   l   = cl.lookup(cands[i]);            assert(l != lit_Undef);
            lbool val = min_model[var(l)] ^ sign(l);    assert(val != l_Undef);
            if (val == l_True)
                cands[j++] = cands[i];
        }
        cands.shrink(i - j);
    } while (j < i);

    if (tip.verbosity >= 2)
        printf("[refineCandsBaseWithMinimize] prepared %d final constraint candidates.\n", cands.size());

    return true;
}


void refineCandsStepInSequence(const TipCirc& tip, vec<Sig>& cands)
{
    Circ               uc;
    vec<IFrame>        ui;           // Unused here.
    UnrollCirc         unroller(tip, ui, uc, false);
    GMap<Sig>          umap0;
    GMap<Sig>          umap1;
    Solver             s;
    Clausifyer<Solver> cl(uc, s);

    unroller(umap0);
    unroller(umap1);

    // Pre-clausify candidates in both time step 0 and 1. This is to guarantee that candidates have
    // a defined value in all models:
    for (int i = 0; i < cands.size(); i++){
        Lit l0 = cl.clausify(umap0[gate(cands[i])] ^ sign(cands[i]));
        Lit l1 = cl.clausify(umap1[gate(cands[i])] ^ sign(cands[i]));
    }

    for (int i = 0; i < cands.size(); ){
        Lit l0 = cl.lookup(umap0[gate(cands[i])] ^ sign(cands[i]));
        Lit l1 = cl.lookup(umap1[gate(cands[i])] ^ sign(cands[i]));
        assert(l0 != lit_Undef && l1 != lit_Undef);

        if (tip.verbosity >= 2)
            printf("[refineCandsStepInSequence] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        if (s.solve(~l0, l1)){
            // Candidate does not imply itself in the next state, remove it and all others with the
            // same property (in this model):
            int j,k;
            for (j = k = i; j < cands.size(); j++){
                Lit p0 = cl.lookup(umap0[gate(cands[j])] ^ sign(cands[j]));
                Lit p1 = cl.lookup(umap1[gate(cands[j])] ^ sign(cands[j]));
                if (s.modelValue(p0) == l_True || s.modelValue(p1) == l_False)
                    cands[k++] = cands[j];
                else{
                    assert(s.modelValue(p0) != l_Undef);
                    assert(s.modelValue(p1) != l_Undef);
                }
            }
            cands.shrink(j - k);
        }else
            i++;
    }
    if (tip.verbosity >= 2){
        printf("[refineCandsStepInSequence] %d final proper constraints.\n", cands.size());
        printf("[refineCandsStepInSequence] cands = ");
        printSigs(cands);
        printf("\n"); }
}

void refineCandsStepWithMinimize(const TipCirc& tip, vec<Sig>& cands)
{
    Circ               uc;
    vec<IFrame>        ui;           // Unused here.
    UnrollCirc         unroller(tip, ui, uc, false);
    GMap<Sig>          umap0;
    GMap<Sig>          umap1;
    Solver             s;
    Clausifyer<Solver> cl(uc, s);

    unroller(umap0);
    unroller(umap1);

    for (unsigned int i = 0; i < tip.cnstrs.size(); i++) {
        Lit rep0 = cl.clausify(umap0[gate(tip.cnstrs[i][0])]^sign(tip.cnstrs[i][0]));
        Lit rep1 = cl.clausify(umap1[gate(tip.cnstrs[i][0])]^sign(tip.cnstrs[i][0]));
        for (int j = 1; j < tip.cnstrs[i].size(); j++) {
          cl.clausifyAs(umap0[gate(tip.cnstrs[i][j])]^sign(tip.cnstrs[i][j]),rep0);
          cl.clausifyAs(umap1[gate(tip.cnstrs[i][j])]^sign(tip.cnstrs[i][j]),rep1);
        }
    }

    // loop:
    //   add clause (~cands) in umap0
    //   solve(assuming cands in umap1)
    //    - if no model, we are done
    //    - if model, remove all cands that are false from the vector
    while ( 1 ) {
        if (tip.verbosity >= 2)
            printf("[refineCandsStepWithMinimize] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        // create set to minimize in umap0 (minimizing here means "~cands")
        // create assumption "cands" in umap1
        vec<Lit> assumps;
        vec<Lit> mins;
        for (int i = 0; i < cands.size(); i++) {
            mins.push(cl.clausify(umap0[gate(cands[i])]^sign(cands[i])));
            assumps.push(cl.clausify(umap1[gate(cands[i])]^sign(cands[i])));
        }
        
        // solve, minimizing true literals in mins
        vec<lbool> min_model;
        if (!solveMinimum(s, assumps, mins, min_model))
            break;
        
        // save only the candidates that are true in the model    
        int i,j;
        for (i = j = 0; i < cands.size(); i++) {
            lbool b = min_model[var(mins[i])]^sign(mins[i]);
            if ( b == l_True )
                cands[j++] = cands[i]; // saving
            else
                assert(b != l_Undef);
        }
        cands.shrink(i-j);
        
        // stop if nothing changed
        if ( i == j )
            break;
    }
        
#if 0
    int i,j;
    do {
        if (tip.verbosity >= 2)
            printf("[refineCandsStepWithMinimize] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        if (!solveMinimum(s, bad_cands, min_model))
            break;

        for (i = j = 0; i < cands.size(); i++){
            Lit   l0   = cl.lookup(umap0[gate(cands[i])] ^ sign(cands[i]));            assert(l0 != lit_Undef);
            lbool val0 = min_model[var(l0)] ^ sign(l0);                                assert(val0 != l_Undef);
            Lit   l1   = cl.lookup(umap1[gate(cands[i])] ^ sign(cands[i]));            assert(l1 != lit_Undef);
            lbool val1 = min_model[var(l1)] ^ sign(l1);                                assert(val1 != l_Undef);

            if (val0 == l_True || val1 == l_False){
                cands[j]       = cands[i];
                bad_cands[j++] = bad_cands[i];
            }
        }
        cands.shrink(i - j);
        bad_cands.shrink(i - j);
        // assert(j < i);  // should not be here?
    } while (j < i);
#endif

    printf("[refineCandsStepWithMinimize] %d final proper constraints.\n", cands.size());
    printf("[refineCandsStepWithMinimize] cands = ");
    printSigs(cands);
    printf("\n");
}


    class MonotonicSignals {
        const TipCirc&     tip;
        LiveProp           live_p;
        int                effort_level;
        bool               use_prop;

        Circ               uc;
        GMap<Sig>          umap0;
        GMap<Sig>          umap1;
        Solver             s;
        Clausifyer<Solver> cl;
        vec<Lit>           justs;

    public:
        unsigned nSolves() const { return s.solves; }
        unsigned nConflicts() const { return s.conflicts; }
        unsigned nDecisions() const { return s.decisions; }

        MonotonicSignals(const TipCirc& t, LiveProp p, int level, bool use_prop_) :
            tip(t), live_p(p), effort_level(level), use_prop(use_prop_), cl(uc, s)
        {
            vec<IFrame>        ui; // Unused here.
            UnrollCirc         unroller(tip, ui, uc, false);

            unroller(umap0);
            unroller(umap1);
            
            // setting constraints
            for (unsigned int i = 0; i < tip.cnstrs.size(); i++) {
                Lit rep0 = cl.clausify(umap0[gate(tip.cnstrs[i][0])]^sign(tip.cnstrs[i][0]));
                Lit rep1 = cl.clausify(umap1[gate(tip.cnstrs[i][0])]^sign(tip.cnstrs[i][0]));
                for (int j = 1; j < tip.cnstrs[i].size(); j++) {
                    cl.clausifyAs(umap0[gate(tip.cnstrs[i][j])]^sign(tip.cnstrs[i][j]),rep0);
                    cl.clausifyAs(umap1[gate(tip.cnstrs[i][j])]^sign(tip.cnstrs[i][j]),rep1);
                }
            }

            // computing all justice signals (in umap0)
            for ( int i = 0; i < tip.fairs.size(); i++ ) {
                Sig j = tip.fairs[i];
                justs.push(cl.clausify(umap0[gate(j)]^sign(j)));
                if (effort_level >= 4) justs.push(cl.clausify(umap1[gate(j)]^sign(j)));
            }
            for ( int i = 0; i < tip.live_props[live_p].sigs.size(); i++ ) {
                Sig j = tip.live_props[live_p].sigs[i];
                justs.push(cl.clausify(umap0[gate(j)]^sign(j)));
                if (effort_level >= 4) justs.push(cl.clausify(umap1[gate(j)]^sign(j)));
            }
            printf("found %d justice signals\n", justs.size());
        }

        // Check if current set of constraints are consistent:
        bool okay() { return s.solve(); }

#if 0
        // Check if monotone signal 'x' is compatible with all fairness signals: (Simple Implementation)
        bool checkCompatWithProp(Sig x, vec<Sig>& trues)
        {
            Lit x0 = cl.clausify(umap0[gate(x)] ^ sign(x));
            for (int k = 0; k < justs.size(); k++)
                if (!s.solve(justs[k],x0)){
                    s.addClause(~x0);
                    trues.push(~x);
                    return false;
                }
            return true;
        }
#else
        // Check if monotone signal 'x' is compatible with all fairness signals: (Fast Implementation)
        bool checkCompatWithProp(Sig x, vec<Sig>& trues)
        {
            Lit x0 = cl.clausify(umap0[gate(x)] ^ sign(x));
            Lit x1 = cl.clausify(umap1[gate(x)] ^ sign(x));

            vec<Lit> assumps; 
            justs.copyTo(assumps);
            assumps.push(x0);
            assumps.push(x1);

            // If simultaneusly compatible with all fairness signals, return true directly:
            if (s.solve(assumps))
                return true;

            int num_conf_prop = 0;
            for (int i = 0; i < s.conflict.size(); i++)
                if (~s.conflict[i] != x0 && ~s.conflict[i] != x1)
                    num_conf_prop++;

            // At most one property literal in conflicting set. I.e. only '~x0' and/or '~x1 and
            // potentially one property literal. We can then return directly because we know that
            // the conflict was not between two (or more) fairness signals:
            if (num_conf_prop <= 1){
                s.addClause(~x0);
                trues.push(~x);
                return false; }

            // Check compatibility with each fairness signal. For each model, filter away all
            // fairness signals that are true and thus also is compatible with 'x':
            assumps.pop();
            assumps.pop();
            for (int k = 0; k < assumps.size(); k++)
                if (!s.solve(assumps[k], x0, x1)){
                    s.addClause(~x0);
                    trues.push(~x);
                    return false;
                }else{
                    for (int i = k+1; i < assumps.size(); i++)
                        if (s.modelValue(assumps[i]) == l_True){
                            Lit tmp      = assumps[i];
                            assumps[i]   = assumps[k+1];
                            assumps[k+1] = tmp;
                            k++;
                        }
                }

            return true;
        }
#endif


        bool upgradeMonotonic(vec<Sig>& monos, vec<Sig>& trues)
        {
            bool improved = false;
            if (use_prop){
                int i,j;
                for (i = j = 0; i < monos.size(); i++){
                    if (!checkCompatWithProp(monos[i], trues)){
                        printf("monotonic signal x incompatible with just; setting to 0 (upgraded).\n");
                        improved = true;
                    }else if (!checkCompatWithProp(~monos[i], trues)){
                        printf("monotonic signal x incompatible with just; setting to 1 (upgraded).\n");
                        improved = true;
                    }else
                        monos[j++] = monos[i];
                }
                monos.shrink(i - j);
            }
            return improved;
        }


        bool refineCandsMonotonicPol(bool sig, vec<Gate>& cands, vec<Sig>& monos, vec<Sig>& trues)
        {
            bool improved = false;
            // trying out all candidates 
            for (int i = 0; i < cands.size(); i++){
                Sig x  = mkSig(cands[i], sig);
                Lit x0 = cl.clausify(umap0[gate(x)] ^ sign(x));
                Lit x1 = cl.clausify(umap1[gate(x)] ^ sign(x));
                printf(" #cands-left: %d\n", cands.size() - i);
                
                // monotonic?
                s.rnd_pol = true;
                if (!s.solve(x0,~x1)){
                    improved = true;
                    s.rnd_pol = false;
                    // setting x as stable (both ways!)
                    s.addClause(~x0,x1);
                    s.addClause(~x1,x0);
                    monos.push(mkSig(gate(x)));

                    // checking compatability with justice signals
                    if (use_prop)
                        if (!checkCompatWithProp(x, trues) || !checkCompatWithProp(~x,trues))
                            monos.pop();

                    // remove from candidates
                    cands[i] = cands.last();
                    cands.pop();
                    i--;
                }else{
                    s.rnd_pol = false;
                    // Reduce candidates:
                    for (int j = i+1; j < cands.size(); j++){
                        Sig x  = mkSig(cands[j], sig);
                        Lit x0 = cl.clausify(umap0[gate(x)] ^ sign(x));
                        Lit x1 = cl.clausify(umap1[gate(x)] ^ sign(x));

                        if (s.modelValue(x0) == l_True && s.modelValue(x1) == l_False){
                            Gate tmp = cands[j];
                            cands[j] = cands[i+1];
                            cands[i+1] = tmp;
                            i++;
                        }
                    }
                }
            }

            return improved;
        }


        void refineCandsMonotonic(vec<Gate>& cands, vec<Sig>& monos, vec<Sig>& trues)
        {
            assert(tip.live_props[live_p].stat == pstat_Unknown);

            // trying out all candidates 
            for ( int i = 0; i < cands.size(); i++ ) {
                Lit x0 = cl.clausify(umap0[cands[i]]);
                Lit x1 = cl.clausify(umap1[cands[i]]);
                    
                // monotonic?
                if (!s.solve(x0,~x1) || !s.solve(~x0,x1)) {
                    // setting x as stable (both ways!)
                    s.addClause(~x0,x1);
                    s.addClause(~x1,x0);
                    monos.push(mkSig(cands[i]));

                    // checking compatability with justice signals
                    if (use_prop)
                        for ( int j = 0; j < justs.size(); j++ ) {
                            if (!s.solve(justs[j],x0)) {
                                //printf("monotonic signal x incompatible with just; setting to 0.\n");
                                s.addClause(~x0);
                                monos.pop();
                                trues.push(~mkSig(cands[i]));
                                break;
                            }
                            else if (!s.solve(justs[j],~x0)) {
                                //printf("monotonic signal x incompatible with just; setting to 1.\n");
                                s.addClause(x0);
                                monos.pop();
                                trues.push(mkSig(cands[i]));
                                break;
                            }
                        }

                    // remove from candidates
                    cands[i] = cands.last();
                    cands.pop();
                    i--;
                }
            }
        }
    };


void printMonotones(const TipCirc& tip, const vec<Sig>& monos)
{
    GMap<Sig> inv_flops; inv_flops.growTo(tip.main.lastGate(), sig_Undef);
    for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
        Gate f    = *flit;
        Sig  next = tip.flps.next(f);
        inv_flops[gate(next)] = mkSig(f) ^ sign(next);
    }

    printf("{ ");
    for (int i = 0; i < monos.size(); i++){
        if (i > 0)
            printf(", ");

        tip.printSig(monos[i]);
        if (tip.flps.isFlop(gate(monos[i]))){
            printf(":next(");
            tip.printSig(tip.flps.next(gate(monos[i])) ^ sign(monos[i]));
            printf(")");
        }else if (inv_flops[gate(monos[i])] != sig_Undef){
            printf(":prev(");
            tip.printSig(inv_flops[gate(monos[i])] ^ sign(monos[i]));
            printf(")");
        }
    }
    printf("}");
}


void analyzeMonotones(const TipCirc& tip, const vec<Sig>& monos, const vec<Sig>& trues)
{
    GMap<Sig> inv_flops; inv_flops.growTo(tip.main.lastGate(), sig_Undef);
    for (TipCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit){
        Gate f    = *flit;
        Sig  next = tip.flps.next(f);
        inv_flops[gate(next)] = mkSig(f) ^ sign(next);
    }

    for (int i = 0; i < monos.size(); i++)
        if (inv_flops[gate(monos[i])] != sig_Undef){
            Sig prev = inv_flops[gate(monos[i])] ^ sign(monos[i]);
            printf(" ... flop of monotone driver: ");
            tip.printSig(monos[i]);
            printf(":prev(");
            tip.printSig(prev);
            printf(")");

            if (!find(monos, prev) && !find(monos, ~prev)){
                if (!find(trues, prev) && !find(trues, ~prev)){
                    printf(" NOT in monos or trues!\n");
                }else{
                    printf(" NOT in monos but in trues!\n");
                }
            }else
                printf(" is in monos.\n");
        }

    for (int i = 0; i < trues.size(); i++)
        if (inv_flops[gate(trues[i])] != sig_Undef){
            Sig prev = inv_flops[gate(trues[i])] ^ sign(trues[i]);
            printf(" ... flop of constant monotone driver: ");
            tip.printSig(trues[i]);
            printf(":prev(");
            tip.printSig(prev);
            printf(")");

            if (!find(trues, prev) && !find(trues, ~prev)){
                if (!find(monos, prev) && !find(monos, ~prev)){
                    printf(" NOT in trues or monos!\n");
                }else{
                    printf(" NOT in trues but in monos!\n");
                }
            }else
                printf(" is in trues.\n");
        }
}


void addDenseFairnessConstraint(TipCirc& tip, LiveProp live_p, const vec<Sig>& monos, const vec<Sig>& trues, int effort_level)
{
    printf("monotonic signals (%d): ", monos.size());
    printSigs(monos);
    //printMonotones(tip, monos);
    printf("\n");
    printf("true signals (%d): ", trues.size());
    printSigs(trues);
    //printMonotones(tip, trues);
    printf("\n");

    printf("analysing monotones...\n");
    //analyzeMonotones(tip, monos, trues);

    // adding these to the just signals
    printf("adding circuitry...\n");

    // computing stable signal, only on flops for now
    Sig stable = sig_True;
    int k = 0;
    for ( int i = 0; i < trues.size(); i++ ) {
        Sig x0 = trues[i];
        stable = tip.main.mkAnd(stable, x0);
        k++;
    }

    if (effort_level <= 2){
        // Keep only trues + monotonic flops.
        for ( int i = 0; i < tip.flps.size(); i++ ) {
            Sig x0 = mkSig(tip.flps[i]);
            Sig x1 = tip.flps.next(gate(x0));
                
            for ( int j = 0; j < monos.size(); j++ ) {
                if ( x0 == monos[j] || x0 == ~monos[j] ) {
                    stable = tip.main.mkAnd(stable, ~tip.main.mkXor(x0,x1));
                    k++;
                }
            }
        }
    }else{
        // Keep all and add flops when necessary (Can be improved).
        for (int i = 0; i < monos.size(); i++)
            if (tip.flps.isFlop(gate(monos[i]))){
                Sig x0 = mkSig(gate(monos[i]));
                Sig x1 = tip.flps.next(gate(x0));
                stable = tip.main.mkAnd(stable, ~tip.main.mkXor(x0,x1));
                k++;
            }else{
                Sig x0 = tip.main.mkInp();
                Sig x1 = mkSig(gate(monos[i]));
                tip.flps.define(gate(x0), x1, tip.init.mkInp());
                stable = tip.main.mkAnd(stable, ~tip.main.mkXor(x0,x1));
                k++;
            }
    }

    printf("created stable signal with %d conjuncts.\n", k);
  
    if ( k > 0 ) {
        // computing fairness signal
        Sig chal  = tip.main.mkInp();
        Sig check = tip.main.mkInp();
        Sig ok    = tip.main.mkInp();
  
        Sig check_ = tip.main.mkOr(check, chal);
        Sig ok_    = tip.main.mkAnd(ok, tip.main.mkOr(~check_, stable));

        tip.flps.define(gate(check),check_);
        tip.flps.define(gate(ok),ok_,sig_True);

        Sig out = tip.main.mkAnd(ok, tip.main.mkAnd(check_, stable));
        if (tip.live_props[live_p].sigs.size() >= 1)
#if 1
            tip.live_props[live_p].sigs[0] = tip.main.mkAnd(tip.live_props[live_p].sigs[0], out);
#else
            // NOTE: maybe helps constraint extraction to pick up
            // the subset of "monos" that really are constraints?
            for (int i = 0; i < tip.live_props[live_p].sigs.size(); i++)
                tip.live_props[live_p].sigs[i] = tip.main.mkAnd(tip.live_props[live_p].sigs[i], out);
#endif
        else
            tip.live_props[live_p].sigs.push(out);
      
        printf("created new fairness constraint based on monotonic signals.\n");
    }
}

}


void semanticConstraintExtraction(TipCirc& tip, bool use_minimize_alg, bool only_coi)
{
    // testInitialize(tip);
    double time_before = cpuTime();

    // FIXME: assumes no previous constraints for now.
    // assert(tip.cnstrs.size() == 0);
    // // FIXME: assumes no liveness properties for now.
    // assert(tip.live_props.size() == 0);

    vec<Sig> cnstrs;
    bool     result = use_minimize_alg ? refineCandsBaseWithMinimize(tip, cnstrs, only_coi) 
                                       : refineCandsBaseInSequence  (tip, cnstrs, only_coi) ;

    if (!result){
        printf("All properties combinationally proved! Setting constraint 'true = false'.\n");
        tip.cnstrs.merge(sig_False,sig_True);
        return;
    }

    if (use_minimize_alg)
        refineCandsStepWithMinimize(tip, cnstrs);
    else
        refineCandsStepInSequence(tip, cnstrs);

    // All constraints proved valid at this point, merge with previous constrainst:
    for (int i = 0; i < cnstrs.size(); i++)
        tip.cnstrs.merge(sig_True, cnstrs[i]);

    if (tip.verbosity >= 2)
        printf(" [semanticConstraintExtraction] CPU-time: %6.2f\n", cpuTime() - time_before);
}


void fairnessConstraintExtraction(TipCirc& tip, int level, bool use_prop)
{
    double time_before = cpuTime();
    printf("\n*** Extracting monotonic signals v2...\n\n");
    
    vec<Gate> gates;
    if (level > 1)
        for (GateIt git = tip.main.begin(); git != tip.main.end(); ++git)
            gates.push(*git);
    else
        for (SeqCirc::FlopIt flit = tip.flpsBegin(); flit != tip.flpsEnd(); ++flit)
            gates.push(*flit);

    for (LiveProp p = 0; p < tip.live_props.size(); p++)
        if (tip.live_props[p].stat == pstat_Unknown){
            double time_before_prop = cpuTime();
            MonotonicSignals ms(tip, p, level, use_prop);
            vec<Sig>         monos;
            vec<Sig>         trues;
            vec<Gate>        cands; gates.copyTo(cands);
            
            do{
                while (ms.refineCandsMonotonicPol(true,  cands, monos, trues)
                     | ms.refineCandsMonotonicPol(false, cands, monos, trues))
                    printf("found %d monotonic signals, %d constant signals...\n", monos.size(), trues.size());
            }while(ms.upgradeMonotonic(monos, trues));

            if (ms.okay())
                addDenseFairnessConstraint(tip, p, monos, trues, level);
            else{
                printf("*** Derived fairness constraints trivially solves property!\n");
                tip.setProvenLive(p, "fce");
            }

            printf("[fce] Liveness property %d: time=%.1f s, #solves=%d, #confl=%d, #dec=%d\n", 
                   p, cpuTime() - time_before_prop,
                   ms.nSolves(), ms.nConflicts(), ms.nDecisions());
        }
    
    printf("\n*** Monotonic Signals CPU-time: %.1f s\n", cpuTime() - time_before);
    printf("*** Done monotonic signals! v2\n\n");
}


//=================================================================================================
} // namespace Tip
