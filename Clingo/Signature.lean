import Clingo.Types
open Lean

namespace Clingo
namespace Signature
@[extern "lean_clingo_signature_mk"]
opaque createSignatureRaw : @& String -> Uint32 -> Bool -> IO (Except String Signature)

def mk (name : String) (arity : Uint32) (positive : Bool := false) := createSignatureRaw name arity positive

@[extern "lean_clingo_signature_name"]
opaque name (sig : Signature) : String

@[extern "lean_clingo_signature_arity"]
opaque arity (sig : Signature) : UInt32


@[extern "lean_clingo_signature_is_positive"]
opaque isPositive (sig : Signature) : Bool


@[extern "lean_clingo_signature_is_negative"]
opaque isNegative (sig : Signature) : Bool


@[extern "lean_clingo_signature_beq"]
opaque beq (s1 : Signature) (s2 : Signature) : Bool

@[extern "lean_clingo_signature_blt"]
opaque blt (s1 : Signature) (s2 : Signature) : Bool

@[extern "lean_clingo_signature_hash"]
opaque hash (s1 : Signature) : UInt64

instance SignatureBeq : BEq Signature where beq := beq

end Signature

end Clingo
