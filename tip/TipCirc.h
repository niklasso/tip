/***************************************************************************************[TipCirc.h]
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

#ifndef Tip_TipCirc_h
#define Tip_TipCirc_h

#include "mcl/SeqCirc.h"

namespace Tip {

using namespace Minisat;

//=================================================================================================
// Basic types:

typedef enum { ptype_Safety = 0, ptype_Liveness = 1 }                     PropType;
typedef enum { pstat_True = 0, pstat_Falsifiable = 1, pstat_Unknown = 2 } PropStatus;

typedef vec<Gate> IFrame;
typedef uint32_t  Trace;
typedef uint32_t  Property;

enum { trace_Undef = UINT32_MAX };
enum { prop_Undef  = UINT32_MAX };

// TODO: these classes are sketchy at the moment.

//=================================================================================================
// A simple class to represent a set of circuit traces:

class TraceSet {
public:
    Trace             newTrace ()         { trace_set.push(); return trace_set.size()-1; }
    vec<vec<lbool> >& getFrames(Trace tr) { assert(tr < (Trace)trace_set.size()); return trace_set[tr].frames; }
    uint32_t&         getLoop  (Trace tr) { assert(tr < (Trace)trace_set.size()); return trace_set[tr].loop; }

    enum { loop_none = UINT32_MAX };

private:
    struct TraceData {
        vec<vec<lbool> > frames;
        uint32_t         loop;
        TraceData() : loop(loop_none){}
    };
    vec<TraceData> trace_set;
};

//=================================================================================================
// A class to represent a set of properties and their verification statuses:

class PropertySet {
public:
    Property   newProperty      (Sig s, PropType t)    { prop_set.push(PropData(s,t)); return prop_set.size()-1; }
    void       setPropTrue      (Property p)           { assert(p < (Property)prop_set.size()); prop_set[p].stat = pstat_True; }
    void       setPropFalsified (Property p, Trace cex){ assert(p < (Property)prop_set.size()); prop_set[p].stat = pstat_True; prop_set[p].cex = cex; }
    Sig        propSig          (Property p) const     { assert(p < (Property)prop_set.size()); return prop_set[p].sig; }
    PropType   propType         (Property p) const     { assert(p < (Property)prop_set.size()); return prop_set[p].type; }
    PropStatus propStatus       (Property p) const     { assert(p < (Property)prop_set.size()); return prop_set[p].stat; }
    Trace      propCex          (Property p) const     { assert(p < (Property)prop_set.size()); return prop_set[p].cex; }
private:
    struct PropData {
        Sig        sig;
        PropType   type;
        PropStatus stat;
        Trace      cex;
        PropData(Sig s, PropType t) : sig(s), type(t), stat(pstat_Unknown), cex(trace_Undef){}
    };
    vec<PropData> prop_set;
};

//=================================================================================================
// A class for representing a sequential circuit together with properties and their current
// verification status. Additionally, extra references to inputs are kept to allow extraction of
// traces (counter-examples). All major transformations and proof-engines should exist as a method
// of this class.

class TipCirc : public SeqCirc {
public:
    void readAiger     (const char* file);
    void writeAiger    (const char* file);
    void printAigerRes (const char* file);

    typedef enum { bmc_Basic = 0, bmc_Simp = 1, bmc_Simp2 = 2 } BmcVersion;
    void bmc           (uint32_t begin_cycle, uint32_t stop_cycle, BmcVersion bver = bmc_Basic);

    // Helpers:
    void printTrace    (Trace t);
    void printCirc     ();

    //TODO: hide data somehow?
    // private:
    vec<IFrame>   inps_init;  // Set of input frames for the init circuit.
    vec<IFrame>   inps_main;  // Set of input frames for the main circuit.

    TraceSet      traces;
    PropertySet   properties;

    vec<Property> all_props;  // Set of properties and their current status.
};

//=================================================================================================

};

#endif
