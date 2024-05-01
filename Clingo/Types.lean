open Lean

namespace Clingo

structure Version where
  major : Int
  minor : Int
  revision : Int
instance VersionToString : ToString Version where toString v := s!"{v.major}.{v.minor}.{v.revision}"

structure Part where
  name : String
  params : Array String
instance PartToString : ToString Part where toString v := s!"{v.name}({v.params})"

def Literal := UInt32
deriving Repr
def Atom := UInt32
deriving Repr

def Id := UInt32
def Weight := UInt32

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
deriving Repr, Inhabited

def Signature := UInt64
deriving Repr
instance SignatureToString : ToString Signature where toString (s : Signature) := by unfold Signature at s; exact (s! "Signature@{s}")

def Symbol := UInt64
deriving Repr, Inhabited

def SymbolCallback := Array Symbol -> IO Unit
def GroundCallback :=
    Location -> String -> Array Symbol -> SymbolCallback -> IO Bool

opaque Model : Type

opaque Statistics : Type

opaque SolveHandle : Type

opaque Backend : Type

opaque ProgramBuilder : Type

opaque Control : Type

end Clingo
