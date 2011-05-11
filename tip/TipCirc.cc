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
#include "tip/bmc/Bmc.h"

using namespace Minisat;

namespace Tip {

    void TipCirc::readAiger(const char* file){
        Box b;
        ::readAiger(file, main, b, flps);

        // Set up input-frames:
        inps_main.push();
        for (int i = 0; i < b.inps.size(); i++)
            inps_main.last().push(b.inps[i]);

        // Set up properties:
        for (int i = 0; i < b.outs.size(); i++)
            all_props.push(properties.newProperty(~b.outs[i], ptype_Safety));
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


    void TipCirc::printTrace(FILE* out, Trace tid)
    {
        const vec<vec<lbool> >& tr = traces.getFrames(tid);
        for (int i = 0; i < tr.size(); i++){
            for (int j = 0; j < tr[i].size(); j++)
                if (tr[i][j] == l_Undef)
                    fprintf(out, "x");
                else if (tr[i][j] == l_False)
                    fprintf(out, "0");
                else{
                    assert(tr[i][j] == l_True);
                    fprintf(out, "1");
                }
            fprintf(out, "\n");
        }
    }

    void TipCirc::printResults(FILE* out)
    {
        // NOTE: Currently only prints the first counter-example!
        for (int i = 0; i < all_props.size(); i++)
            if (properties.propStatus(all_props[i]) == pstat_Falsifiable){
                printTrace(out, all_props[i]);
                break;
            }
    }

    void TipCirc::printCirc()
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

        printf("PROPS:\n");
        for (int i = 0; i < all_props.size(); i++){
            Property p = all_props[i];
            Sig      psig = properties.propSig(p);
            printSig(psig);
            printf("\n");
        }
    }

};
