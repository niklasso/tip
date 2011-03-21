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

    void TipCirc::bmc(uint32_t begin_cycle, uint32_t stop_cycle, bool simp){
        if (simp)
            simpBmc (*this, begin_cycle, stop_cycle); 
        else
            basicBmc(*this, begin_cycle, stop_cycle); 
    }

};
