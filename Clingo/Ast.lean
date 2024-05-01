import Clingo.Types
open Lean

namespace Clingo

namespace Ast
inductive Sign where | None | Negation | DoubleNegation
deriving Repr, Inhabited
inductive Comparison.Operator where | GT | LT | LEQ | GEQ | NEQ | EQ
deriving Repr, Inhabited
inductive UnaryOperator.Operator where | Minus | Negation | Absolute
deriving Repr, Inhabited
inductive BinaryOperator.Operator where | XOR | OR | AND | PLUS | MINUS | MULTIPLICATION | DIVISION | MODULO | POWER
deriving Repr, Inhabited

mutual

  inductive Term where
  | mk (location : Location) (data : Term.Data)
   deriving Repr

  inductive Term.Data where
  | Symbol (sym: Symbol)
  | Variable (var : String)
  | UnaryOperator (op: UnaryOperator.Operator) (argument : Term)
  | BinaryOperator (op: BinaryOperator.Operator) (l r : Term)
  | Interval (l r : Term)
  | Function (name : String) (arguments : Array Term)
  | ExternalFunction (name : String) (arguments : Array Term)
  | Pool (arguments : Array Term)
   deriving Repr, Inhabited

end

instance : Inhabited Term where default := Term.mk default default

structure Comparison where
    operator: Comparison.Operator
    left : Term
    right : Term
deriving Repr, Inhabited


structure CSPProductTerm where
  location: Location
  coefficient: Term
  variable_: Term
deriving Repr, Inhabited

structure CSPSumTerm where
  location: Location
  terms: Array CSPProductTerm
deriving Repr, Inhabited

structure CSPGuard where
  comparison: Comparison.Operator
  term: CSPSumTerm
deriving Repr, Inhabited

structure CSPLiteral where
   term : CSPSumTerm
   guards: Array CSPGuard
deriving Repr, Inhabited

inductive Literal.Data where
| Boolean (b : Bool)
| Symbolic (t : Term)
| Comparison (comparison : Comparison)
| Csp (cspLiteral : CSPLiteral)
deriving Repr, Inhabited


structure Literal where
   location: Location
   sign : Sign
   data: Literal.Data
deriving Repr, Inhabited

structure ConditionalLiteral where
   literal: Literal
   condition: Array Literal
deriving Repr, Inhabited

structure AggregateGuard where
  comparison: Comparison.Operator
  term: Term
deriving Repr, Inhabited

structure Aggregate where
  elements : List ConditionalLiteral
  left: AggregateGuard
  right: AggregateGuard
deriving Repr, Inhabited

inductive Aggregrate.Function where | Count | Sum | Sump | Min | Max
deriving Repr, Inhabited

structure Aggregrate.Head.Element where
  tuple : Array Term
  conditional_literal: ConditionalLiteral
deriving Repr, Inhabited

structure Aggregate.Body.Element where
  tuple: Array Term
  condition: Array Literal
deriving Repr, Inhabited

structure Aggregate.Head where
   function: Aggregrate.Function
   elements: Array Aggregrate.Head.Element
   left: AggregateGuard
   right: AggregateGuard
deriving Repr, Inhabited

structure Aggregate.Body where
   function: Aggregrate.Function
   elements: Array Aggregate.Body.Element
   left: AggregateGuard
   right: AggregateGuard
deriving Repr, Inhabited

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
    deriving Repr, Inhabited

   inductive Term where
   | mk (location : Location) (data : Term.Data)
    deriving Repr, Inhabited

   inductive Function where
   | mk (name: String) (args: Array Term)
    deriving Repr, Inhabited

   inductive UnparsedTerm where
   | mk (operator: Array String) (term: Term)
    deriving Repr, Inhabited

end

structure AtomElement where
  tuple: Array Term
  condition: Array Literal
deriving Repr, Inhabited

structure Guard where
  operatorName: String
  term: Term
deriving Repr, Inhabited

structure Atom where
  term: ASTTerm
  elements: Array AtomElement
  guard: Guard
deriving Repr, Inhabited

inductive OperatorType where | Unary | BinaryLeft | BinaryRight
deriving Repr, Inhabited

structure OperatorDefinition where
  location : Location
  name: String
  priority: UInt64
  type: OperatorType
deriving Repr, Inhabited

structure TermDefinition where
  location: Location
  name: String
  operators: Array OperatorDefinition
deriving Repr, Inhabited

structure GuardDefinition where
  term: String
  operators: Array String
deriving Repr, Inhabited
  
inductive AtomDefinition.Type where | Head | Body | Any | Directive
deriving Repr, Inhabited

structure AtomDefinition where
  location: Location
  type: AtomDefinition.Type
  name: String
  arity: UInt64
  elements: String
  guard: GuardDefinition
deriving Repr, Inhabited

end Theory

structure DisjointElement where
  location : Location
  tuple: Array Term
  term: CSPSumTerm
  condition: Array Literal
deriving Repr, Inhabited

inductive HeadLiteral.Data where
| Literal (literal: Literal)

| Disjunction (elements: Array ConditionalLiteral)

| Aggregate (aggregate : Aggregate)

| HeadAggregate (headAggregate : Aggregate.Head)

| TheoryAtom (theoryAtom: Theory.Atom)
deriving Repr, Inhabited

structure HeadLiteral where
  location : Location
  data : HeadLiteral.Data
deriving Repr, Inhabited

inductive BodyLiteral.Data where
| Literal (literal: Literal)
| Conditional (conditional : ConditionalLiteral)
| Aggregate (aggregate : Aggregate)
| BodyAggregate (bodyAggregate : Aggregate.Body)
| TheoryAtom (theoryAtom : Theory.Atom)
| Disjoint (disjoint : Array DisjointElement)
deriving Repr, Inhabited

structure BodyLiteral where
  location : Location
  sign: Sign
  data : BodyLiteral.Data
deriving Repr, Inhabited

structure Definition where
  name : String
  value : Term
  isDefault: Bool
deriving Repr, Inhabited

inductive ScriptType where | Lua | Python
deriving Repr, Inhabited

structure Id where
  location : Location
  id: String
deriving Repr, Inhabited

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
deriving Repr, Inhabited

structure Ast.Statement where
   location : Location
   data: Ast.Statement.Data
deriving Repr, Inhabited

end Clingo
