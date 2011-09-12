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

#include "mcl/Aiger.h"
#include "mcl/CircPrelude.h"
#include "tip/TipCirc.h"
#include "tip/unroll/Bmc.h"
#include "tip/constraints/Extract.h"

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
        ::readAiger_v19(file, *this, sects);

        // Assume file is AIGER v1 if no properties exists but circuit has outputs:
        if (sects.outs.size() > 0 && sects.cnstrs.size() == 0 && sects.fairs.size() == 0 &&
            sects.bads.size() == 0 && sects.justs.size() == 0)
            sects.outs.moveTo(sects.bads);

        // Set up properties:
        for (int i = 0; i < sects.bads.size(); i++)
            newSafeProp(~sects.bads[i]);

        // Set up constraints:
        for (int i = 0; i < sects.cnstrs.size(); i++)
            cnstrs.merge(sig_True, sects.cnstrs[i]);

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


    void TipCirc::writeResultsAiger(FILE* out) const {
        // TODO: Collapse properties that use the same counter example trace.
        for (SafeProp p = 0; p < safe_props.size(); p++)
            if (safe_props[p].stat == pstat_Falsified){
                fprintf(out, "1\nb%d\n", p);
                printTraceAiger(out, safe_props[p].cex);
                fprintf(out, ".\n");
                break;
            }else if (safe_props[p].stat == pstat_Proved){
                fprintf(out, "0\nb%d", p);
                fprintf(out, ".\n");
                break;
            }
    }

    void TipCirc::printTrace(FILE* out, const vec<vec<lbool> >& tr) const
    {
        // Apply the trace adaptor before printing it:
        vec<vec<lbool> > frames;
        copy(tr, frames);
        if (tradaptor != NULL) tradaptor->adapt(frames);

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

        // TODO: print constraints?

        printf("LIVENESS PROPERTIES:\n");
        for (LiveProp p = 0; p < live_props.size(); p++){
            Sig psig = live_props[p].sig;
            printSig(psig);
            printf("\n");
        }
    }

};
