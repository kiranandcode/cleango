import Clingo.Types
open Lean

namespace Clingo

namespace Model

inductive ModelType where | Stable | Brave | Cautious
deriving Repr, Inhabited

structure FilterFlags where
   CSP_assignments : Bool
   shown : Bool
   all_atoms: Bool
   all_terms: Bool
   all: Bool
   complement: Bool
deriving Repr, Inhabited

namespace FilterFlags

def selectCSPAssignments :=
   FilterFlags.mk
     (CSP_assignments := true)
     (shown := false)
     (all_atoms := false)
     (all_terms := false)
     (all := false)
     (complement := false)

def selectShown :=
   FilterFlags.mk
     (CSP_assignments := false)
     (shown := true)
     (all_atoms := false)
     (all_terms := false)
     (all := false)
     (complement := false)

def selectAllAtoms :=
   FilterFlags.mk
     (CSP_assignments := false)
     (shown := false)
     (all_atoms := true)
     (all_terms := false)
     (all := false)
     (complement := false)

def selectAllTerms :=
   FilterFlags.mk
     (CSP_assignments := false)
     (shown := false)
     (all_atoms := false)
     (all_terms := true)
     (all := false)
     (complement := false)

def selectAll :=
   FilterFlags.mk
     (CSP_assignments := false)
     (shown := false)
     (all_atoms := false)
     (all_terms := false)
     (all := true)
     (complement := false)

def selectComplement :=
   FilterFlags.mk
     (CSP_assignments := false)
     (shown := false)
     (all_atoms := false)
     (all_terms := false)
     (all := false)
     (complement := true)

end FilterFlags


@[extern "lean_clingo_model_type"]
opaque type: @& Model -> ModelType

@[extern "lean_clingo_model_number"]
opaque id: @& Model -> UInt64

@[extern "lean_clingo_model_size"]
private opaque size_inner: @& Model -> @& FilterFlags -> USize

def size (m : @& Model ) (flags : @& FilterFlags := FilterFlags.selectAll) : USize := size_inner m flags


@[extern "lean_clingo_model_symbols"]
private opaque symbols_inner: @& Model -> @& FilterFlags -> Array Symbol

def symbols (m : @& Model ) (flags : @& FilterFlags := FilterFlags.selectAll) : Array Symbol := symbols_inner m flags

@[extern "lean_clingo_model_contains"]
opaque contains?: @& Model -> Atom -> Bool

@[extern "lean_clingo_model_is_true"]
opaque is_true?: @& Model -> Literal -> Bool

@[extern "lean_clingo_model_costs"]
opaque costs: @& Model -> Array Int

@[extern "lean_clingo_model_optimality_proven"]
opaque optimal?: @& Model -> Bool

end Model
end Clingo
