open Lean

namespace Clingo
inductive Error where | success | runtime | logic | badAlloc | unknown
deriving Repr

end Clingo

namespace Clingo
private def max_uint64 := (UInt64.shiftLeft 1 63) + ((UInt64.shiftLeft 1 63) - 2)

structure Version where
  major : Int
  minor : Int
  revision : Int
instance VersionToString : ToString Version where toString v := s!"{v.major}.{v.minor}.{v.revision}"

@[extern "lean_clingo_version"]
opaque version : IO Version

abbrev Literal := UInt32
-- deriving Repr

abbrev Atom := UInt32
abbrev Id := UInt32
abbrev Weight := UInt32


@[extern "lean_clingo_error_code"]
opaque error_code : IO Error

@[extern "lean_clingo_error_message"]
opaque error_message : IO (Option String)

inductive Warning where | undefinedOperation | runtimeError | undefinedAtom | fileIncludedMultipleTimes | unboundVariable | globalVariableInTupleOfAggregate | other
deriving Repr

def Logger := Warning -> String -> IO Unit 

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

@[extern "lean_clingo_signature_hash"]
opaque hash (s1 : Symbol) : UInt64


def Iterator := UInt64
deriving Repr

namespace Iterator

end Iterator

end Symbol

opaque Model : Type

inductive ModelType where | Stable | Brave | Cautious
deriving Repr, Inhabited

namespace Model

structure FilterFlags where
   select_CSP_assignments : Bool
   select_shown : Bool
   select_all_atoms: Bool
   select_all_terms: Bool
   select_all: Bool
   select_complement: Bool
deriving Repr, Inhabited

@[extern "lean_clingo_model_type"]
opaque type: @& Model -> ModelType

@[extern "lean_clingo_model_number"]
opaque id: @& Model -> UInt64

@[extern "lean_clingo_model_size"]
opaque size: @& Model -> @& FilterFlags -> USize

@[extern "lean_clingo_model_symbols"]
private opaque symbols_inner: @& Model -> @& FilterFlags -> Array Symbol

def symbols (m : @& Model ) (flags : @& FilterFlags := default) : Array Symbol := symbols_inner m flags

@[extern "lean_clingo_model_contains"]
opaque contains?: @& Model -> Atom -> Bool

@[extern "lean_clingo_model_is_true"]
opaque is_true?: @& Model -> Literal -> Bool

@[extern "lean_clingo_model_costs"]
opaque costs: @& Model -> Array Int

@[extern "lean_clingo_model_optimality_proven"]
opaque optimal?: @& Model -> Bool

end Model

opaque Statistics : Type

inductive StatisticsType where | Empty | Value | Array | Map
deriving Repr, Inhabited

namespace Statistics

@[extern "lean_clingo_statistics_root"]
opaque root: @& Statistics -> UInt64

@[extern "lean_clingo_statistics_type"]
opaque type: @& Statistics -> UInt64 -> StatisticsType

@[extern "lean_clingo_statistics_array_size"]
opaque arraySize: @& Statistics -> UInt64 -> USize

@[extern "lean_clingo_statistics_array_ref"]
opaque arrayRef: @& Statistics -> (key: UInt64) -> (offset: USize) -> UInt64

@[extern "lean_clingo_statistics_map_size"]
opaque mapSize: @& Statistics -> UInt64 -> USize

@[extern "lean_clingo_statistics_map_has_key"]
opaque mapHasKey?: @& Statistics -> (key: UInt64) -> (name : @& String) -> Bool

@[extern "lean_clingo_statistics_map_ref"]
opaque mapRef: @& Statistics -> (key: UInt64) -> (name : @& String) -> UInt64

@[extern "lean_clingo_statistics_value_get"]
opaque valueGet: @& Statistics -> (key: UInt64) -> Float



end Statistics

structure SolveResult where
  satisfiable : Bool
  unsatisfiable : Bool
  exhausted : Bool
  interrupted : Bool
deriving Repr

inductive SolveMode where | Neither | Async | Yield | AsyncYield

inductive SolveEvent where
| ModelFound (m : Option Model)
| StatsUpdated (perStep : Statistics) (accum : Statistics)
| Finished (res: SolveResult)

def SolveEventCallback := SolveEvent -> IO Bool


opaque SolveHandle : Type

namespace SolveHandle
end SolveHandle


private opaque ControlP : NonemptyType
def Control := ControlP.type

namespace Control

@[extern "lean_clingo_control_mk_unsafe"]
private opaque mk_unsafe : @& Array String -> Logger -> UInt64 ->  IO Control

@[extern "lean_clingo_control_mk_safe"]
private opaque mk_safe : @& Array String -> Logger -> UInt64 ->  IO (Except Error Control)

def mk(args : @& Array String := #[]) (logger : Logger := fun _ _ => return ()) (limit : UInt64 := max_uint64) :=
  mk_safe args logger limit

def mk! (args : @& Array String := #[]) (logger : Logger := fun _ _ => return ()) (limit : UInt64 := max_uint64) :=
  mk_unsafe args logger limit

@[extern "lean_clingo_control_load"]
opaque load: @& Control -> @& String -> IO (Except (Prod Error String) Unit)

@[extern "lean_clingo_control_add"]
opaque add : @& Control -> (name : @& String) -> (params: @& Array String) -> (program: @& String) -> IO (Except Error Unit)

-- @[extern "lean_clingo_control_ground"]
-- opaque ground : @& Control -> (name : @& String) -> (parts: @& Array (@& Part)) -> (callback: @& GroundCallback) -> IO (Except Error Unit)

@[extern "lean_clingo_solve"]
opaque solve: @& Control -> SolveMode -> @& Array Literal -> SolveEventCallback -> IO (Except Error SolveHandle)


@[extern "lean_clingo_control_statistics"]
opaque statistics : @& Control -> IO (Except Error Statistics)

@[extern "lean_clingo_control_interrupt"]
opaque interrupt : @& Control -> IO Unit

instance : Repr Control where
   reprPrec _ _ := s!"(Clingo.Control.mk)"

end Control




end Clingo
