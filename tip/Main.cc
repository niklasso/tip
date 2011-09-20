/*****************************************************************************************[Main.cc]
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

#include "minisat/utils/Options.h"
#include "tip/TipCirc.h"

using namespace Minisat;
using namespace Tip;

int main(int argc, char** argv)
{
    setlinebuf(stdout);
    setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input is in plain or gzipped binary AIGER.\n");
    IntOption bver ("MAIN", "bv",   "Version of BMC to be used.", 0, IntRange(0,2));
    IntOption depth("MAIN", "k",    "Maximal depth of unrolling.", INT32_MAX, IntRange(0,INT32_MAX));
    IntOption verb ("MAIN", "verb", "Verbosity level.", 1, IntRange(0,10));
    IntOption sce  ("MAIN", "sce",  "Use semantic constraint extraction (0=off, 1=minimize-algorithm, 2=basic-algorithm).", 0, IntRange(0,2));

    parseOptions(argc, argv, true);

    if (argc < 2 || argc > 3)
        printUsageAndExit(argc, argv);

    TipCirc tc;
    tc.verbosity = verb;

    // Simple algorithm flow for testing:
    tc.readAiger(argv[1]);
    if (sce > 0) tc.sce(sce == 1, false);

    //tc.bmc(0,depth, (TipCirc::BmcVersion)(int)bver);
    tc.trip();
    tc.printResults();

    if (argc == 3){
        FILE* res = fopen(argv[2], "w");
        if (!res) printf("ERROR! Failed to open results file: %s\n", argv[2]), exit(1);
        tc.writeResultsAiger(res);
        fclose(res);
    }

    exit(0);
}
