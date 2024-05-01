import Lean.Parser
import Lean.Parser.Term
import Lean.Elab.Term
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

structure Part where
  name : String
  params : Array String
instance PartToString : ToString Part where toString v := s!"{v.name}({v.params})"


@[extern "lean_clingo_version"]
opaque version : IO Version

def Literal := UInt32
-- deriving Repr

def Atom := UInt32
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
deriving Repr, Inhabited
def x : Int := 0


namespace Symbol

@[extern "lean_clingo_symbol_mk_number"]
opaque mk_number : Int -> Symbol

@[extern "lean_clingo_symbol_mk_supremum"]
private opaque mk_supremum_inner : Unit -> Symbol
def mk_supremum := mk_supremum_inner ()

@[extern "lean_clingo_symbol_mk_infimum"]
private opaque mk_infimum_inner : Unit -> Symbol
def mk_infimum := mk_infimum_inner ()

@[extern "lean_clingo_symbol_mk_string"]
opaque mk_string : @& String -> Symbol

@[extern "lean_clingo_symbol_mk_id"]
opaque mk_id : @& String -> Bool -> Symbol

@[extern "lean_clingo_symbol_mk_fun"]
opaque mk_fun : @& String -> @& Array (@& Symbol) -> Bool -> Symbol

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

@[extern "lean_clingo_symbol_hash"]
opaque hash (s1 : Symbol) : UInt64

/-- Type class for the canonical homomorphism `Symbol → R`. -/
class SymbolCast (R : Type u) where
  /-- The canonical map `Nat → R`. -/
  protected symCast : Symbol → R

instance : SymbolCast Symbol where symCast n := n

@[coe, reducible, match_pattern] protected def Symbol.cast {R : Type u} [SymbolCast R] : Symbol → R :=
  SymbolCast.symCast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [SymbolCast R] : CoeTail Symbol R where coe := Symbol.cast

-- see the notes about coercions into arbitrary types in the module doc-string
instance [SymbolCast R] : CoeHTCT Symbol R where coe := Symbol.cast

inductive Repr where
 | Infimum
 | Number (n : Int)
 | String (s : String)
 | Function (name : String) (args : Array Repr) (is_positive : Bool)
 | Supremum
deriving Repr, Inhabited

@[extern "lean_clingo_repr"]
opaque repr (s1 : Symbol) : Repr

@[extern "lean_clingo_mk"]
opaque mk (s1 : @& Repr) : Symbol


instance : SymbolCast Repr where symCast := repr

namespace Repr

  def toSymbol : Repr -> Symbol := fun r => Symbol.mk r

  def Variable v := Function v #[] true

end Repr 

def matchAlts : Lean.Parser.Parser := Lean.Parser.Term.matchAlts (rhsParser := Lean.Parser.termParser)
-- 

open Elab

elab_rules : term
| `(term| match $x:term with $m:matchAlts) => do
   let x_stx <- Term.elabTerm x (some (mkConst ``Symbol))
   let ty <- Meta.inferType x_stx
   let is_sym <- Meta.isDefEq ty (mkConst ``Symbol)
   if not is_sym then throwUnsupportedSyntax
   Term.elabTerm (<- `(term| match Symbol.repr $x:term with $m:matchAlts)) none

def f (n : Symbol) :=
 match n with
 | Repr.Infimum => 0
 | Repr.Supremum => 0
 | Repr.Function name args positive => 0
 | Repr.String s => 0
 | Repr.Number n => 0

end Symbol

def SymbolCallback := Array Symbol -> IO Unit
def GroundCallback := Location -> String -> Array Symbol -> SymbolCallback -> IO Bool

opaque Model : Type

inductive ModelType where | Stable | Brave | Cautious
deriving Repr, Inhabited

namespace Model

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
deriving Repr, Inhabited

inductive SolveMode where | Neither | Async | Yield | AsyncYield

inductive SolveEvent where
| ModelFound (m : Option Model)
| StatsUpdated (perStep : Statistics) (accum : Statistics)
| Finished (res: SolveResult)

def SolveEventCallback := SolveEvent -> IO Bool


opaque SolveHandle : Type

namespace SolveHandle

@[extern "lean_clingo_solve_handle_get"]
opaque get: @& SolveHandle -> IO (Except (Error × String) SolveResult)

@[extern "lean_clingo_solve_handle_wait"]
opaque wait: @& SolveHandle -> @& Float -> IO Bool

@[extern "lean_clingo_solve_handle_model"]
opaque model: @& SolveHandle -> IO (Except (Error × String) (Option Model))

@[extern "lean_clingo_solve_handle_resume"]
opaque resume: @& SolveHandle -> IO (Except (Error × String) Unit)

@[extern "lean_clingo_solve_handle_cancel"]
opaque cancel: @& SolveHandle -> IO (Except (Error × String) Unit)

@[extern "lean_clingo_solve_handle_close"]
opaque close: SolveHandle -> IO (Except (Error × String) Unit)

end SolveHandle

inductive ExternalType where | AssignFreely | AssignTrue | AsisgnFalse | Release

opaque Backend : Type

namespace Backend

-- @[extern "lean_clingo_backend_begin"]
-- opaque begin_modify: @& Backend -> IO Unit

-- @[extern "lean_clingo_backend_end"]
-- opaque end_modify: @& Backend -> IO Unit

-- @[extern "lean_clingo_backend_rule"]
-- opaque add_rule: @& Backend -> Bool -> Array Atom -> Array Literal -> IO Unit

-- @[extern "lean_clingo_backend_weighted_rule"]
-- opaque add_weighted_rule: @& Backend -> Bool -> Array Atom -> (weight: Int) -> (weighted_literals: Array (Literal × Int)) -> IO Unit

-- @[extern "lean_clingo_backend_minimize_constraint"]
-- opaque add_minimize_constraint: @& Backend -> (priority: Int) -> (weighted_literals: Array (Literal × Int)) -> IO Unit

-- @[extern "lean_clingo_backend_project"]
-- opaque add_projection_directive: @& Backend -> Array Atom -> IO Unit

-- @[extern "lean_clingo_backend_external"]
-- opaque add_external: @& Backend -> Atom -> ExternalType -> IO Unit

-- @[extern "lean_clingo_backend_assume"]
-- opaque add_assumptions: @& Backend -> Array Literal -> IO Unit

-- @[extern "lean_clingo_backend_add_atom"]
-- opaque add_atom: @& Backend -> Option Symbol -> IO Atom

end Backend

namespace Ast
inductive Sign where | None | Negation | DoubleNegation
namespace Comparison inductive Operator where | GT | LT | LEQ | GEQ | NEQ | EQ end Comparison
namespace UnaryOperator inductive Operator where | Minus | Negation | Absolute end UnaryOperator
namespace BinaryOperator inductive Operator where | XOR | OR | AND | PLUS | MINUS | MULTIPLICATION | DIVISION | MODULO | POWER end BinaryOperator


mutual

  inductive Term where
  | mk (location : Location) (data : Term.Data)

  inductive Term.Data where
  | Symbol (sym: Symbol)
  | Variable (var : String)
  | UnaryOperator (op: UnaryOperator.Operator) (argument : Term)
  | BinaryOperator (op: BinaryOperator.Operator) (l r : Term)
  | Interval (l r : Term)
  | Function (name : String) (arguments : Array Term)
  | ExternalFunction (name : String) (arguments : Array Term)
  | Pool (arguments : Array Term)

end

structure Comparison where
    operator: Comparison.Operator
    left : Term
    right : Term

structure CSPProductTerm where
  location: Location
  coefficient: Term
  variable_: Term

structure CSPSumTerm where
  location: Location
  terms: Array CSPProductTerm

structure CSPGuard where
  comparison: Comparison.Operator
  term: CSPSumTerm

structure CSPLiteral where
   term : CSPSumTerm
   guards: Array CSPGuard

namespace Literal
inductive Data where
| Boolean (b : Bool)
| Symbolic (t : Term)
| Comparison (comparison : Comparison)
| Csp (cspLiteral : CSPLiteral)
end Literal

structure Literal where
   location: Location
   sign : Sign
   data: Literal.Data

structure ConditionalLiteral where
   literal: Literal
   condition: Array Literal

structure AggregateGuard where
  comparison: Comparison.Operator
  term: Term

structure Aggregate where
  elements : List ConditionalLiteral
  left: AggregateGuard
  right: AggregateGuard

inductive Aggregrate.Function where | Count | Sum | Sump | Min | Max

structure Aggregrate.Head.Element where
  tuple : Array Term
  conditional_literal: ConditionalLiteral

structure Aggregate.Body.Element where
  tuple: Array Term
  condition: Array Literal

structure Aggregate.Head where
   function: Aggregrate.Function
   elements: Array Aggregrate.Head.Element
   left: AggregateGuard
   right: AggregateGuard

structure Aggregate.Body where
   function: Aggregrate.Function
   elements: Array Aggregate.Body.Element
   left: AggregateGuard
   right: AggregateGuard

namespace Theory
private abbrev ASTTerm := Term

mutual
    inductive Term.Data where
    | Symbol (symbol: Symbol)
    | Variable (name : String)
    | Tuple (tuple: Array Term)
    | List (list: Array Term)
    | Set (set: Array Term)
    | Function (function: Function)
    | UnparsedTerm (unparsedTerm: Array UnparsedTerm)

   inductive Term where
   | mk (location : Location) (data : Term.Data)

   inductive Function where
   | mk (name: String) (args: Array Term)

   inductive UnparsedTerm where
   | mk (operator: Array String) (term: Term)

end

structure AtomElement where
  tuple: Array Term
  condition: Array Literal

structure Guard where
  operatorName: String
  term: Term

structure Atom where
  term: ASTTerm
  elements: Array AtomElement
  guard: Guard

inductive OperatorType where | Unary | BinaryLeft | BinaryRight

structure OperatorDefinition where
  location : Location
  name: String
  priority: UInt64
  type: OperatorType

structure TermDefinition where
  location: Location
  name: String
  operators: Array OperatorDefinition

structure GuardDefinition where
  term: String
  operators: Array String
  
inductive AtomDefinition.Type where | Head | Body | Any | Directive

structure AtomDefinition where
  location: Location
  type: AtomDefinition.Type
  name: String
  arity: UInt64
  elements: String
  guard: GuardDefinition

end Theory

structure DisjointElement where
  location : Location
  tuple: Array Term
  term: CSPSumTerm
  condition: Array Literal

inductive HeadLiteral.Data where
| Literal (literal: Literal)

| Disjunction (elements: Array ConditionalLiteral)

| Aggregate (aggregate : Aggregate)

| HeadAggregate (headAggregate : Aggregate.Head)

| TheoryAtom (theoryAtom: Theory.Atom)

structure HeadLiteral where
  location : Location
  data : HeadLiteral.Data

inductive BodyLiteral.Data where
| Literal (literal: Literal)
| Conditional (conditional : ConditionalLiteral)
| Aggregate (aggregate : Aggregate)
| BodyAggregate (bodyAggregate : Aggregate.Body)
| TheoryAtom (theoryAtom : Theory.Atom)
| Disjoint (disjoint : Array DisjointElement)

structure BodyLiteral where
  location : Location
  sign: Sign
  data : BodyLiteral.Data

structure Definition where
  name : String
  value : Term
  isDefault: Bool

inductive ScriptType where | Lua | Python

structure Id where
  location : Location
  id: String

end Ast

inductive Ast.Statement.Data where
| Rule (head: Ast.HeadLiteral) (body : Array Ast.BodyLiteral)          --   clingo_ast_statement_type_rule
| Const (definition : Ast.Definition)                                  --   clingo_ast_statement_type_const
| ShowSignature (signature : Signature) (csp: Bool)                --   clingo_ast_statement_type_show_signature
| ShowTerm (term : Ast.Term) (body: Array Ast.BodyLiteral) (csp: Bool) --   clingo_ast_statement_type_show_term
| Minimize (weight : Ast.Term) (priority : Ast.Term) (tuple : Array Ast.Term) (body: Array Ast.BodyLiteral) --   clingo_ast_statement_type_minimize
| Script (type : Ast.ScriptType) (code : String) --    clingo_ast_statement_type_script   
| Program (name : String) (params : Array Ast.Id) --   clingo_ast_statement_type_program  
| External (atom: Ast.Term) (body : Array Ast.BodyLiteral) (type: Ast.Term) --    clingo_ast_statement_type_external 
| Edge (u v : Ast.Term) (body : Array Ast.BodyLiteral) --   clingo_ast_statement_type_edge                  
| Heuristic (atom : Ast.Term) (body : Array Ast.BodyLiteral) (bias priority modifier: Ast.Term) --   clingo_ast_statement_type_heuristic             
| ProjectAtom (atom : Ast.Term) (body : Array Ast.BodyLiteral) --   clingo_ast_statement_type_project_atom          
| ProjectAtomSignature (signature : Signature) --   clingo_ast_statement_type_project_atom_signature
| TheoryDefinition (name : String) (terms : Array Ast.Theory.TermDefinition) (atoms : Array Ast.Theory.AtomDefinition) --   clingo_ast_statement_type_theory_definition     
| Defined (signature : Signature)  --   clingo_ast_statement_type_defined               
structure Ast.Statement where
   location : Location
   data: Ast.Statement.Data

namespace Ast

end Ast

opaque ProgramBuilder : Type

namespace ProgramBuilder

@[extern "lean_clingo_program_builder_begin"]
private opaque begin_modify: @& ProgramBuilder -> IO Unit


@[extern "lean_clingo_program_builder_end"]
private opaque end_modify: @& ProgramBuilder -> IO Unit


@[extern "lean_clingo_program_builder_add"]
opaque addStatement: @& ProgramBuilder -> @& Ast.Statement -> IO Unit

end ProgramBuilder

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

@[extern "lean_clingo_control_ground"]
opaque ground : @& Control -> (parts: @& Array (@& Part)) -> (callback: @& GroundCallback) -> IO (Except Error Unit)

@[extern "lean_clingo_solve"]
opaque solve: @& Control -> SolveMode -> @& Array Literal -> SolveEventCallback -> IO (Except Error SolveHandle)

@[extern "lean_clingo_control_statistics"]
opaque statistics : @& Control -> IO (Except Error Statistics)

@[extern "lean_clingo_control_interrupt"]
opaque interrupt : @& Control -> IO Unit

instance : Repr Control where
   reprPrec _ _ := s!"(Clingo.Control.mk)"

@[extern "lean_clingo_control_program_builder"]
private opaque programBuilder: @& Control -> IO ProgramBuilder

def withProgramBuilder (ctrl : Control) (f : ProgramBuilder -> IO A) : IO A := do
    let pb <- ctrl.programBuilder
    pb.begin_modify
    let res <- f pb
    pb.end_modify
    return res

end Control

end Clingo
