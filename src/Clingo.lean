open Lean

namespace Clingo

structure Version where
  major : Int
  minor : Int
  revision : Int
instance VersionToString : ToString Version where toString v := s!"{v.major}.{v.minor}.{v.revision}"

@[extern "lean_clingo_version"]
opaque version : IO Version

abbrev Literal := Int
abbrev Atom := UInt32
abbrev Id := UInt32
abbrev Weight := UInt32

inductive Error where | success | runtime | logic | badAlloc | unknown
deriving Repr

@[extern "lean_clingo_error_code"]
opaque error_code : IO Error

@[extern "lean_clingo_error_message"]
opaque error_message : IO (Option String)

inductive Warning where | undefinedOperation | runtimeError | undefinedAtom | fileIncludedMultipleTimes | unboundVariable | globalVariableInTupleOfAggregate | other
deriving Repr

inductive TruthValue where | free | true | false
deriving Repr

structure Location where
   beginFile : String
   endFile : String
   beginLine : Int
   endLine : Int
   beginColumn : Int
   endColumn : Int

def Signature := UInt64
deriving Repr
instance SignatureToString : ToString Signature where toString (s : Signature) := by unfold Signature at s; exact (s! "Signature@{s}")

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

-- @[extern "lean_test"]
-- opaque test : Except Uint32 UInt32 -> IO Unit

inductive SymbolType where | Infimum | Number | String | Function | Supremum
deriving Repr, Inhabited

def Symbol := UInt64
deriving Repr

namespace Symbol

@[extern "lean_clingo_symbol_mk_number"]
opaque mk_number : Int -> IO Symbol

@[extern "lean_clingo_symbol_mk_supremum"]
opaque mk_supremum : IO Symbol

@[extern "lean_clingo_symbol_mk_infimum"]
opaque mk_infimum : IO Symbol

@[extern "lean_clingo_symbol_mk_string"]
opaque mk_string : @& String -> IO Symbol

@[extern "lean_clingo_symbol_mk_id"]
opaque mk_id : @& String -> Bool -> IO Symbol

@[extern "lean_clingo_symbol_mk_fun"]
opaque mk_fun : @& String -> @& Array (@& Symbol) -> Bool -> IO Symbol

@[extern "lean_clingo_symbol_number"]
opaque number? : Symbol -> Option Int

@[extern "lean_clingo_symbol_name"]
opaque name? : Symbol -> Option String

@[extern "lean_clingo_symbol_string"]
opaque string? : Symbol -> Option String

@[extern "lean_clingo_symbol_positive"]
opaque isPositive? : Symbol -> Option Bool

@[extern "lean_clingo_symbol_negative"]
opaque isNegative? : Symbol -> Option Bool

@[extern "lean_clingo_symbol_arguments"]
opaque args? : Symbol -> Option (Array Symbol)

@[extern "lean_clingo_symbol_type"]
opaque type : Symbol -> SymbolType 

@[extern "lean_clingo_symbol_to_string"]
opaque toString : Symbol -> String

instance SymbolToString : ToString Symbol where toString v := toString v

@[extern "lean_clingo_symbol_beq"]
opaque beq : Symbol -> Symbol -> Bool

instance SignatureBeq : BEq Symbol where beq := beq

@[extern "lean_clingo_symbol_blt"]
opaque blt (s1 : Symbol) (s2 : Symbol) : Bool

end Symbol


end Clingo
