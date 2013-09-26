/**************************************************************************************[TipCirc.cc]
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

#include "minisat/utils/System.h"
#include "mcl/Aiger.h"
#include "mcl/CircPrelude.h"
#include "tip/TipCirc.h"
#include "tip/unroll/Bmc.h"
#include "tip/constraints/Extract.h"
#include "tip/induction/Induction.h"

using namespace Minisat;

namespace Tip {

    void TipCirc::readAiger(const char* file){
        clear();
#if 0
        // Parse with AIGER v1
        vec<Sig> outs;
        ::readAiger(file, *this, outs);

        // Set up properties:
        for (int i = 0; i < outs.size(); i++)
            props.push(property_set.newProperty(~outs[i], ptype_Safety));
#else
        // Parse with AIGER v1.9
        AigerSections sects;
        readAiger_v19(file, *this, sects);

        // Assume file is AIGER v1 if no properties exists but circuit has outputs:
        if (sects.outs.size() > 0 && sects.cnstrs.size() == 0 && sects.fairs.size() == 0 &&
            sects.bads.size() == 0 && sects.justs.size() == 0)
            sects.outs.moveTo(sects.bads);

        // Set up properties:
        for (int i = 0; i < sects.bads.size(); i++)
            newSafeProp(~sects.bads[i]);

        // Set up liveness properties:
        for (int i = 0; i < sects.justs.size(); i++)
            newLiveProp(sects.justs[i]);

        // Set up constraints:
        for (int i = 0; i < sects.cnstrs.size(); i++)
            cnstrs.merge(sig_True, sects.cnstrs[i]);

        // Set up fairness:
        sects.fairs.copyTo(fairs);

        // Set up trace adaptor to fix AIGER witness style:
        AigerInitTraceAdaptor* trad = new AigerInitTraceAdaptor();
        tradaptor = trad;
        for (int i = 0; i < flps.size(); i++){
            Sig x = flps.init(flps[i]);
            if (x == sig_False)
                trad->flop(i, l_False);
            else if (x == sig_True)
                trad->flop(i, l_True);
            else{
                assert(type(x) == gtype_Inp);
                assert(init.number(gate(x)) != UINT32_MAX);
                trad->flop(i, l_Undef, init.number(gate(x)));
            }
        }
#endif
    }


    void TipCirc::writeAiger(const char* file) const
    {
        vec<Sig> outs;
        for (SafeProp p = 0; p < safe_props.size(); p++)
            outs.push(~safe_props[p].sig);
        ::writeAiger(file, *this, outs);
    }


    void TipCirc::bmc(uint32_t begin_cycle, uint32_t stop_cycle, BmcVersion bver){
        if (bver == bmc_Basic)
            basicBmc(*this, begin_cycle, stop_cycle);
        else if (bver == bmc_Simp)
            simpBmc (*this, begin_cycle, stop_cycle);
        else{
            assert(bver == bmc_Simp2);
            simpBmc2(*this, begin_cycle, stop_cycle);
        }
    }


    void TipCirc::sce(bool use_minimize_alg, bool only_coi){ 
        semanticConstraintExtraction(*this, use_minimize_alg, only_coi);
    }

    void TipCirc::trip(RipBmcMode bmc_mode){
        relativeInduction(*this, bmc_mode);
    }


    void TipCirc::selSafe(SafeProp p)
    {
        if (p >= safe_props.size())
            printf("ERROR! Safety property %d does not exist.\n", p), exit(1);

        live_props.clear();
        for (SafeProp q = 0; q < safe_props.size(); q++)
            if (q != p)
                safe_props[q].stat = pstat_Discarded;
    }

    void TipCirc::selLive(LiveProp p)
    {
        if (p >= live_props.size())
            printf("ERROR! Liveness property %d does not exist.\n", p), exit(1);

        safe_props.clear();
        for (LiveProp q = 0; q < live_props.size(); q++)
            if (q != p)
                live_props[q].stat = pstat_Discarded;
    }


    void TipCirc::stats()
    {
        printf("circ-stats: #flops=%d, #gates=%d, #inps=%d, #reset-gates=%d, #reset-inps=%d\n", 
               flps.size(), main.nGates(), main.nInps() - flps.size(),
               init.nGates(), init.nInps());

        int num_safes = 0;
        int num_lives = 0;
        int num_cnstrs = 0;

        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Unknown)
                num_safes++;

        for (LiveProp p = 0; p < live_props.size(); p++)
            if (live_props[p].stat == pstat_Unknown)
                num_lives++;

        for (unsigned i = 0; i < cnstrs.size(); i++)
            num_cnstrs += cnstrs[i].size()-1;

        printf("prop-stats: #safes=%d, #lives=%d, #cnstrs=%d, #fairs=%d\n",
               num_safes, num_lives, num_cnstrs, fairs.size());
               
    }

    void TipCirc::setProvenSafe   (SafeProp p, const char* engine)
    {
        if (verbosity >= 1){
            printf("[tip] Safety property %d was proved", p);
            if (engine != NULL)
                printf(" (%s)", engine);
            printf("\n");
        }
        safe_props[p].stat = pstat_Proved;
        writeResultSafe(p);
    }

    void TipCirc::setRadiusSafe   (SafeProp p, unsigned radius, const char* engine)
    {
        tradaptor->adaptRadius(radius);
        if (safe_props[p].radius < radius) {
            safe_props[p].radius = radius;
            if (verbosity >= 3){
                printf("[tip] Property %d reached radius %d", p, radius);
                if (engine != NULL)
                    printf(" (%s)", engine);
                printf("\n");
                fflush(stdout);
            }
            writeResultSafe(p);
        }
            
    }


    void TipCirc::setProvenLive   (LiveProp p, const char* engine)
    {
        if (verbosity >= 1){
            printf("[tip] Liveness property %d was proved", p);
            if (engine != NULL)
                printf(" (%s)", engine);
            printf("\n");
        }
        live_props[p].stat = pstat_Proved;
        writeResultLive(p);
    }

    void TipCirc::setFalsifiedSafe(SafeProp p, Trace cex, const char* engine)
    {
        if (verbosity >= 1){
            printf("[tip] Safety property %d was falsified", p);
            if (engine != NULL)
                printf(" (%s)", engine);
            printf("\n");
        }
        safe_props[p].stat = pstat_Falsified;
        safe_props[p].cex  = cex;
        writeResultSafe(p);
    }


    void TipCirc::setFalsifiedLive(LiveProp p, Trace cex, const char* engine)
    {
        if (verbosity >= 1){
            printf("[tip] Liveness property %d was falsified", p);
            if (engine != NULL)
                printf(" (%s)", engine);
            printf("\n");
        }
        live_props[p].stat = pstat_Falsified;
        live_props[p].cex  = cex;
        writeResultLive(p);
    }


    void TipCirc::printResults() const
    {
        int n_proved    = 0;
        int n_falsified = 0;
        int n_unknown   = 0;

        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Proved)
                n_proved++;
            else if (safe_props[p].stat == pstat_Falsified)
                n_falsified++;
            else
                n_unknown++;

        for (LiveProp p = 0; p < live_props.size(); p++)
            if (live_props[p].stat == pstat_Proved)
                n_proved++;
            else if (live_props[p].stat == pstat_Falsified)
                n_falsified++;
            else
                n_unknown++;

        double time    = cpuTime();
        double peakMem = memUsedPeak(true);

        printf("Resources used\n");
        printf("================================================================================\n");
        printf("  CPU time:       %.2f s\n",  time);
        if (peakMem > 0) {
          printf("  Peak memory:    %.1f Mb\n", peakMem);
        } else {
          printf("  Current memory: %.1f Mb\n", memUsed());
        }
        printf("\n");

        printf("Verification results\n");
        printf("================================================================================\n");
        printf("  Proved:     %d\n", n_proved);
        printf("  Falsified:  %d\n", n_falsified);
        printf("  Unknown:    %d\n", n_unknown);
    }

    void TipCirc::openResultFile(const char* file)
    {
        if ( resultFile )
            printf("ERROR! resultFile is already in use.\n"), exit(1);
        resultFile = fopen(file, "w");
        if (!resultFile)
             printf("ERROR! Failed to open results file: %s\n", file), exit(1);
    }

    void TipCirc::writeResultSafe(SafeProp p)
    {
        if ( resultFile ) {
            if (safe_props[p].stat == pstat_Falsified){
                fprintf(resultFile, "1\nb%d\n", p);
                printTraceAiger(resultFile, safe_props[p].cex);
                fprintf(resultFile, ".\n");
            }else if (safe_props[p].stat == pstat_Proved){
                fprintf(resultFile, "0\nb%d\n", p);
                fprintf(resultFile, ".\n");
            }else{
                // fprintf(resultFile, "0 %d\nb%d\n", safe_props[p].radius, p);
                // fprintf(resultFile, ".\n");
            }
            fflush(resultFile);
        }
    }

    void TipCirc::writeResultLive(LiveProp p)
    {
        if ( resultFile ) {
            if (live_props[p].stat == pstat_Falsified){
                fprintf(resultFile, "1\nj%d\n", p);
                printTraceAiger(resultFile, live_props[p].cex);
                fprintf(resultFile, ".\n");
            }else if (live_props[p].stat == pstat_Proved){
                fprintf(resultFile, "0\nj%d\n", p);
                fprintf(resultFile, ".\n");
            }
            fflush(resultFile);
        }
    }

    void TipCirc::writeResultsAiger(FILE* out) const {
        // TODO: Collapse properties that use the same counter example trace.
        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Falsified){
                fprintf(out, "1\nb%d\n", p);
                printTraceAiger(out, safe_props[p].cex);
                fprintf(out, ".\n");
            }else if (safe_props[p].stat == pstat_Proved){
                fprintf(out, "0\nb%d\n", p);
                fprintf(out, ".\n");
            }

        for (LiveProp p = 0; p < live_props.size(); p++)
            if (live_props[p].stat == pstat_Falsified){
                fprintf(out, "1\nj%d\n", p);
                printTraceAiger(out, live_props[p].cex);
                fprintf(out, ".\n");
            }else if (live_props[p].stat == pstat_Proved){
                fprintf(out, "0\nj%d\n", p);
                fprintf(out, ".\n");
            }

    }

    void TipCirc::printTrace(FILE* out, const vec<vec<lbool> >& frames) const
    {
        for (int i = 0; i < frames.size(); i++){
            for (int j = 0; j < frames[i].size(); j++)
                if (frames[i][j] == l_Undef)
                    fprintf(out, "x");
                else if (frames[i][j] == l_False)
                    fprintf(out, "0");
                else{
                    assert(frames[i][j] == l_True);
                    fprintf(out, "1");
                }
            fprintf(out, "\n");
        }
    }


    void TipCirc::printTrace(FILE* out, Trace tid) const
    {
        if (tid == trace_Undef)
            printf("ERROR! Trying to print an undefined trace.\n");
        else
            printTrace(out, traces[tid].frames);
    }


    void TipCirc::printTraceAiger(FILE* out, Trace tid) const
    {
        if (tid == trace_Undef)
            fprintf(out, "c WARNING! Trace %d is undefined.\n", tid);
        else
            printTrace(out, traces[tid].frames);
    }


    void TipCirc::clear()
    {
        // TODO: this should be SeqCirc::clear();
        main.clear();
        init.clear();
        flps.clear();

        delete tradaptor;
        tradaptor = NULL;

        traces.clear();
        safe_props.clear();
        live_props.clear();
        cnstrs.clear();
        fairs.clear();

        verbosity = 0;
    }


    void TipCirc::moveTo(TipCirc& to)
    {
        // TODO: this should be SeqCirc::moveTo();
        main.moveTo(to.main);
        init.moveTo(to.init);
        flps.moveTo(to.flps);

        to.tradaptor = tradaptor;
        tradaptor = NULL;

        traces    .moveTo(to.traces);
        safe_props.moveTo(to.safe_props);
        live_props.moveTo(to.live_props);
        cnstrs    .moveTo(to.cnstrs);
        fairs     .moveTo(to.fairs);

        to.verbosity = verbosity;
        verbosity = 0;
    }


    void TipCirc::printSig(Sig x) const
    {
        if (x == sig_Undef)
            printf("x");
        else if (x == sig_True)
            printf("1");
        else if (x == sig_False)
            printf("0");
        else
            printf("%s%c%d", sign(x)?"-":"", type(x)==gtype_Inp?(flps.isFlop(gate(x))?'f':'i'):'a', index(gate(x)));
    }

    void TipCirc::printCirc() const
    {
        // Print main circuit:
        printf("MAIN:\n");
        for (GateIt git = main.begin(); git != main.end(); ++git)
            if (type(*git) == gtype_Inp)
                if (flps.isFlop(*git)){
                    printf("next("); printGate(*git); printf(") = "); printSig(flps.next(*git)); printf("\n");
                    printf("init("); printGate(*git); printf(") = "); printSig(flps.init(*git)); printf("\n");
                }else{
                    printGate(*git); printf(" = <inp>\n");
                }
            else{
                printGate(*git); printf(" = "); 
                printSig(main.lchild(*git)); printf(" & "); printSig(main.rchild(*git)); printf("\n");
            }

        // Print init circuit:
        printf("INIT:\n");
        for (GateIt git = init.begin(); git != init.end(); ++git)
            if (type(*git) == gtype_Inp){
                printGate(*git); printf(" = <inp>\n");
            }else{
                printGate(*git); printf(" = "); 
                printSig(main.lchild(*git)); printf(" & "); printSig(main.rchild(*git)); printf("\n");
            }

        printf("SAFETY PROPERTIES:\n");
        for (SafeProp p = 0; p < safe_props.size(); p++){
            Sig psig = safe_props[p].sig;
            printSig(psig);
            printf("\n");
        }

        printf("CONSTRAINTS:\n");
        for (unsigned i = 0; i < cnstrs.size(); i++){
            printf("{ ");
            for (int j = 0; j < cnstrs[i].size(); j++){
                if (j > 0) printf(", ");
                printSig(cnstrs[i][j]);
            }
            printf(" }\n");
        }


        printf("LIVENESS PROPERTIES:\n");
        for (LiveProp p = 0; p < live_props.size(); p++){
            printSigs(live_props[p].sigs);
            printf("\n");
        }
    }


    void TipCirc::extractRoots(vec<Sig>& xs)
    {
        // All safety properties:
        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Unknown)
            xs.push(safe_props[p].sig);
            else
                safe_props[p].sig = sig_Undef;
        
        // All liveness properties:
        for (LiveProp p = 0; p < live_props.size(); p++)
            if (live_props[p].stat == pstat_Unknown){
                for (int i = 0; i < live_props[p].sigs.size(); i++)
                    xs.push(live_props[p].sigs[i]);
            }else{
                for (int i = 0; i < live_props[p].sigs.size(); i++)
                    live_props[p].sigs[i] = sig_Undef;
            }
        
        // All constraints:
        for (unsigned i = 0; i < cnstrs.size(); i++)
            for (int j = 0; j < cnstrs[i].size(); j++)
                xs.push(cnstrs[i][j]);
        
        // All fairness constraints:
        for (int i = 0; i < fairs.size(); i++)
            xs.push(fairs[i]);
    }
    

    void TipCirc::updateRoots (GMap<Sig>& cmap)
    {
        // All safety properties:
        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Unknown)
                safe_props[p].sig = cmap[gate(safe_props[p].sig)] ^ sign(safe_props[p].sig);

        // All liveness properties:
        for (LiveProp p = 0; p < live_props.size(); p++)
            if (live_props[p].stat == pstat_Unknown)
                for (int i = 0; i < live_props[p].sigs.size(); i++)
                    live_props[p].sigs[i] = cmap[gate(live_props[p].sigs[i])] ^ sign(live_props[p].sigs[i]);
        
        // All constraints:
        Equivs ceq;
        for (unsigned i = 0; i < cnstrs.size(); i++){
            Sig x = cmap[gate(cnstrs[i][0])] ^ sign(cnstrs[i][0]);
            for (int j = 1; j < cnstrs[i].size(); j++){
                Sig y = cmap[gate(cnstrs[i][j])] ^ sign(cnstrs[i][j]);
                ceq.merge(x,y);
            }
        }
        ceq.moveTo(cnstrs);

        // All fairness constraints:
        map(cmap, fairs);
    }

};
