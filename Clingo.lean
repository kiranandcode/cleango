import Alloy.C
import Lean
open Lean Elab Command Term Meta

open scoped Alloy.C

alloy c include <stdint.h> <stdlib.h> <string.h> <lean/lean.h>  "clingo.h"

alloy c section
typedef struct {
  uint32_t      major;
  uint32_t      minor;
  uint32_t      patch;
} ClingoVersion;

end

alloy c opaque_extern_type ClingoVersion => ClingoVersion where
  finalize(s) := free(s)


alloy c extern def clingoVersion (tt : Unit) : ClingoVersion := {
    ClingoVersion* s = (ClingoVersion*)malloc(sizeof(ClingoVersion))
    clingo_version(&s->major, &s->minor, &s->patch);
    return to_lean<ClingoVersion>(s);
}



alloy c extern def ClingoVersionMajor (c : @& ClingoVersion) : UInt32 := { return of_lean<ClingoVersion>(c)->major; }
alloy c extern def ClingoVersionMinor (c : @& ClingoVersion) : UInt32 := { return of_lean<ClingoVersion>(c)->minor; }
alloy c extern def ClingoVersionPatch (c : @& ClingoVersion) : UInt32 := { return of_lean<ClingoVersion>(c)->patch; }

namespace ClingoVersion
  def major := ClingoVersionMajor
  def minor := ClingoVersionMinor
  def patch := ClingoVersionPatch
end ClingoVersion


instance ClingoVersionToString : ToString ClingoVersion where
   toString s := s!"{s.major}.{s.minor}.{s.patch}"
   
