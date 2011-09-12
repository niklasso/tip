/**************************************************************************************[Extract.cc]
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
#include "mcl/Circ.h"
#include "mcl/Clausify.h"
#include "tip/constraints/Extract.h"
#include "tip/unroll/Unroll.h"

namespace Tip {

namespace {

template<class Clausifyer>
bool initializeCands            (const TipCirc& tip, Solver& s, Clausifyer& cl, vec<Sig>& cands, bool only_coi);

template<class Clausifyer>
bool initializeCandsIter        (const TipCirc& tip, Solver& s, Clausifyer& cl, vec<Sig>& cands, bool only_coi);

bool refineCandsBaseInSequence  (const TipCirc& tip, vec<Sig>& cands, bool only_coi = false);
void refineCandsStepInSequence  (const TipCirc& tip, vec<Sig>& cands);
bool refineCandsBaseWithMinimize(const TipCirc& tip, vec<Sig>& cands, bool only_coi = false);
void refineCandsStepWithMinimize(const TipCirc& tip, vec<Sig>& cands);

bool solveMinimum               (Solver& s, const vec<Lit>& ps, vec<lbool>& min_model, Lit trigger = lit_Undef);


//=================================================================================================
// File Local helpers:

// TODO: this should be moved to some general library of algorithms / techniques.
bool solveMinimum(Solver& s, const vec<Lit>& ps, vec<lbool>& min_model, Lit trigger)
{
    for (int i = 0; i < ps.size(); i++)
        s.setPolarity(var(ps[i]), lbool(!sign(ps[i])));

    vec<Lit> assume;
    bool     satisfied = false;

    for (;;){
        if (trigger != lit_Undef)
            assume.push(trigger);

        if (s.solve(assume)){
            satisfied = true;
            s.model.copyTo(min_model);

            assume.clear();
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
        some_bad.push(~cl.clausify(tip.safe_props[p].sig));
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


template<class Clausifyer>
bool initializeCandsIter(const TipCirc& tip, Solver& s, Clausifyer& cl, vec<Sig>& cands, bool only_coi)
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
        some_bad.push(~cl.clausify(tip.safe_props[p].sig));
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

    s.rnd_pol = true;
    for (int iters = 0; iters < 100; iters++){
#if 0
        vec<Lit> blocking_clause;
        for (InpIt iit = tip.main.inpBegin(); iit != tip.main.inpEnd(); ++iit){
            lbool ival = cl.modelValue(*iit);
            if (ival != l_Undef)
                blocking_clause.push(cl.lookup(*iit) ^ (ival == l_True));
        }
        assert(blocking_clause.size() > 0);
        s.addClause(blocking_clause);
#endif

        if (tip.verbosity >= 2)
            printf("[initializeCandsIter] #cand=%8d, #vars=%8d, #clauses=%8d, #learnts=%6d, #conf=%6d, #solves=%4d, cpu-time=%6.2f\n",
                   cands.size(),
                   s.nVars(), s.nClauses(), s.nLearnts(), (int)s.conflicts, (int)s.solves, cpuTime());

        if (!s.solve())
            break;

        int i, j;
        for (i = j = 0; i < cands.size(); i++){
            if (cl.modelValue(cands[i], model) == l_True)
                cands[j++] = cands[i];
            else {
                if (cl.modelValue(cands[i], model) == l_Undef)
                    n_skipped++;
            }
        }
        cands.shrink(i - j);
    }
    s.rnd_pol = false;

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

    // Pre-clausify candidates in both time step 0 and 1. This is to guarantee that candidates have
    // a defined value in all models:
    vec<Lit> bad_cands;
    for (int i = 0; i < cands.size(); i++){
        Lit l0       = cl.clausify(umap0[gate(cands[i])] ^ sign(cands[i]));
        Lit l1       = cl.clausify(umap1[gate(cands[i])] ^ sign(cands[i]));
        Lit bad_cand = mkLit(s.newVar());
        s.addClause(bad_cand, ~l0);
        s.addClause(bad_cand,  l1);
        bad_cands.push(bad_cand);
    }

    vec<lbool> min_model;
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
        assert(j < i);
    } while (j < i);
    printf("[refineCandsStepWithMinimize] %d final proper constraints.\n", cands.size());
    printf("[refineCandsStepWithMinimize] cands = ");
    printSigs(cands);
    printf("\n");
}


}


void semanticConstraintExtraction(TipCirc& tip, bool use_minimize_alg, bool only_coi)
{
    // testInitialize(tip);
    double time_before = cpuTime();

    // FIXME: assumes no previous constraints for now.
    assert(tip.cnstrs.size() == 0);
    // FIXME: assumes no liveness properties for now.
    assert(tip.live_props.size() == 0);

    vec<Sig> cnstrs;
    bool     result = use_minimize_alg ? refineCandsBaseWithMinimize(tip, cnstrs, only_coi) 
                                       : refineCandsBaseInSequence  (tip, cnstrs, only_coi) ;

    if (!result){
        printf("UNIMPLEMENTED: all properties combinationally proved.\n");
        exit(1); }

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


//=================================================================================================
} // namespace Tip
