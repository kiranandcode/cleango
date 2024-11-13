import Clingo.Symbol
import Clingo.Ast
import Lean.Elab

open Lean Elab Meta


namespace Clingo.Lang

declare_syntax_cat clingo_symbol

syntax "#inf" : clingo_symbol
syntax "#sup" : clingo_symbol
syntax num : clingo_symbol
syntax str : clingo_symbol
syntax ident : clingo_symbol

declare_syntax_cat clingo_term
-- symbol
syntax (name := clingo_term_symbolic) clingo_symbol : clingo_term
-- unary operators
syntax "-" clingo_term : clingo_term
syntax "~" clingo_term : clingo_term
syntax "|" clingo_term "|" : clingo_term
-- binary operators
syntax:10 clingo_term:10 " ^ " clingo_term:11 : clingo_term
syntax:20 clingo_term:20 " ? " clingo_term:21 : clingo_term
syntax:30 clingo_term:30 " & " clingo_term:31 : clingo_term
syntax:40 clingo_term:40 " + " clingo_term:41 : clingo_term
syntax:50 clingo_term:50 " - " clingo_term:51 : clingo_term
syntax:60 clingo_term:60 " * " clingo_term:61 : clingo_term
syntax:70 clingo_term:70 " / " clingo_term:71 : clingo_term
syntax:80 clingo_term:80 " \\\\ " clingo_term:81 : clingo_term
syntax:90 clingo_term:90 " ** " clingo_term:91 : clingo_term
-- interval
syntax:1 clingo_term:1 " .. " clingo_term:2 : clingo_term
-- function
syntax ident "(" clingo_term,* ")" : clingo_term
-- external function
syntax "@" ident "(" clingo_term,* ")" : clingo_term
syntax "(" clingo_term,+ ")" : clingo_term


declare_syntax_cat clingo_comparison_op
syntax " > " : clingo_comparison_op
syntax " < " : clingo_comparison_op
syntax " >= " : clingo_comparison_op
syntax " <= " : clingo_comparison_op
syntax " = " : clingo_comparison_op
syntax " != " : clingo_comparison_op

declare_syntax_cat clingo_comparison
syntax clingo_term clingo_comparison_op clingo_term : clingo_comparison

declare_syntax_cat clingo_csp_mul_term
syntax "$ " clingo_term " $* " clingo_term : clingo_csp_mul_term
syntax clingo_term " $* " "$ " clingo_term : clingo_csp_mul_term
syntax "$ " clingo_term : clingo_csp_mul_term
syntax clingo_term : clingo_csp_mul_term

declare_syntax_cat clingo_csp_add_term
syntax clingo_csp_add_term  " $+ " clingo_csp_mul_term : clingo_csp_add_term
syntax clingo_csp_add_term  " $- " clingo_csp_mul_term : clingo_csp_add_term
syntax clingo_csp_mul_term : clingo_csp_add_term

declare_syntax_cat clingo_csp_literal

syntax clingo_csp_literal " $< " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_literal " $> " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_literal " $<= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_literal " $>= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_literal " $= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_literal " $!= " clingo_csp_add_term : clingo_csp_literal

syntax clingo_csp_add_term " $< " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_add_term " $> " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_add_term " $<= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_add_term " $>= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_add_term " $= " clingo_csp_add_term : clingo_csp_literal
syntax clingo_csp_add_term " $!= " clingo_csp_add_term : clingo_csp_literal

declare_syntax_cat clingo_bool_const
syntax "true" : clingo_bool_const
syntax "false" : clingo_bool_const

declare_syntax_cat clingo_literal
syntax clingo_bool_const : clingo_literal
syntax "not" clingo_bool_const : clingo_literal
syntax "not" "not" clingo_bool_const : clingo_literal

syntax clingo_term : clingo_literal
syntax "not" clingo_term : clingo_literal
syntax "not" "not" clingo_term : clingo_literal

syntax clingo_comparison : clingo_literal
syntax "not" clingo_comparison : clingo_literal
syntax "not" "not" clingo_comparison : clingo_literal

syntax clingo_csp_literal : clingo_literal
syntax "not" clingo_csp_literal : clingo_literal
syntax "not" "not" clingo_csp_literal : clingo_literal

declare_syntax_cat clingo_condition_literal
syntax clingo_literal ":" clingo_literal,+ : clingo_condition_literal
syntax clingo_literal : clingo_condition_literal

declare_syntax_cat clingo_condition_literal_seq
syntax clingo_condition_literal_seq ";" clingo_condition_literal : clingo_condition_literal_seq
syntax clingo_condition_literal : clingo_condition_literal_seq


declare_syntax_cat clingo_aggregate_empty_body
syntax "{" "}" : clingo_aggregate_empty_body

declare_syntax_cat clingo_aggregate_base_body
syntax clingo_aggregate_empty_body : clingo_aggregate_base_body
syntax "{" clingo_condition_literal_seq "}" : clingo_aggregate_base_body

declare_syntax_cat clingo_aggregate
syntax clingo_aggregate_base_body : clingo_aggregate
syntax clingo_term clingo_comparison_op clingo_aggregate_base_body : clingo_aggregate
syntax clingo_aggregate_base_body clingo_comparison_op clingo_term : clingo_aggregate
syntax clingo_term clingo_comparison_op clingo_aggregate_base_body clingo_comparison_op clingo_term : clingo_aggregate

declare_syntax_cat clingo_head_aggregate_element
syntax clingo_term,+ : clingo_head_aggregate_element
syntax clingo_term,+ ":" clingo_condition_literal : clingo_head_aggregate_element

declare_syntax_cat clingo_head_aggregate_element_seq
syntax clingo_head_aggregate_element_seq ";" clingo_head_aggregate_element : clingo_head_aggregate_element_seq
syntax clingo_head_aggregate_element : clingo_head_aggregate_element_seq

declare_syntax_cat clingo_aggregate_function
syntax "count" : clingo_aggregate_function
syntax "sum" : clingo_aggregate_function
syntax "sump" : clingo_aggregate_function
syntax "min" : clingo_aggregate_function
syntax "max" : clingo_aggregate_function

declare_syntax_cat clingo_aggregate_head_body
syntax clingo_aggregate_function clingo_aggregate_empty_body : clingo_aggregate_head_body
syntax clingo_aggregate_function "{" clingo_head_aggregate_element_seq "}" : clingo_aggregate_head_body


declare_syntax_cat clingo_aggregate_head
syntax clingo_aggregate_head_body : clingo_aggregate_head
syntax clingo_term clingo_comparison_op clingo_aggregate_head_body : clingo_aggregate_head
syntax clingo_aggregate_head_body clingo_comparison_op clingo_term : clingo_aggregate_head
syntax clingo_term clingo_comparison_op clingo_aggregate_head_body clingo_comparison_op clingo_term : clingo_aggregate_head

declare_syntax_cat clingo_body_aggregate_element
syntax clingo_term,+ : clingo_body_aggregate_element
syntax clingo_term,+ ":" clingo_literal,+ : clingo_body_aggregate_element

declare_syntax_cat clingo_body_aggregate_element_seq
syntax clingo_body_aggregate_element_seq ";" clingo_body_aggregate_element : clingo_body_aggregate_element_seq
syntax clingo_body_aggregate_element : clingo_body_aggregate_element_seq

declare_syntax_cat clingo_aggregate_body_body
syntax clingo_aggregate_function clingo_aggregate_empty_body : clingo_aggregate_body_body
syntax clingo_aggregate_function "{" clingo_body_aggregate_element_seq "}" : clingo_aggregate_body_body

declare_syntax_cat clingo_aggregate_body
syntax clingo_aggregate_body_body : clingo_aggregate_body
syntax clingo_term clingo_comparison_op clingo_aggregate_body_body : clingo_aggregate_body
syntax clingo_aggregate_body_body clingo_comparison_op clingo_term : clingo_aggregate_body
syntax clingo_term clingo_comparison_op clingo_aggregate_body_body clingo_comparison_op clingo_term : clingo_aggregate_body

declare_syntax_cat clingo_head_literal
syntax clingo_condition_literal_seq : clingo_head_literal
syntax clingo_aggregate : clingo_head_literal
syntax clingo_aggregate_head : clingo_head_literal

declare_syntax_cat clingo_body_literal
syntax clingo_condition_literal : clingo_body_literal
syntax clingo_aggregate : clingo_body_literal
syntax clingo_aggregate_body : clingo_body_literal
syntax "not " clingo_condition_literal : clingo_body_literal
syntax "not " clingo_aggregate : clingo_body_literal
syntax "not " clingo_aggregate_body : clingo_body_literal
syntax  "not " "not " clingo_condition_literal : clingo_body_literal
syntax  "not " "not " clingo_aggregate : clingo_body_literal
syntax  "not " "not " clingo_aggregate_body : clingo_body_literal

declare_syntax_cat clingo_body_literal_seq
syntax clingo_body_literal_seq ";" clingo_body_literal : clingo_body_literal_seq
syntax clingo_body_literal : clingo_body_literal_seq


declare_syntax_cat clingo_definition
syntax "#const " ident " = " clingo_term "." : clingo_definition

declare_syntax_cat clingo_statement
syntax clingo_head_literal "." : clingo_statement
syntax clingo_head_literal " :- " clingo_body_literal_seq "." : clingo_statement
syntax " :- " clingo_body_literal_seq "." : clingo_statement
syntax clingo_definition : clingo_statement

-- declare_syntax_cat clingo_body_aggregate_op
-- syntax "sum" : clingo_body_aggregate_op
-- syntax "sump" : clingo_body_aggregate_op
-- syntax "min" : clingo_body_aggregate_op
-- syntax "max" : clingo_body_aggregate_op
-- syntax "count" : clingo_body_aggregate_op


-- declare_syntax_cat clingo_body_aggregate_vec_elem
-- syntax clingo_term,* ":" clingo_literal,+  : clingo_body_aggregate_vec_elem
-- syntax clingo_term,*  : clingo_body_aggregate_vec_elem

-- declare_syntax_cat clingo_body_aggregate_vec
-- syntax:10 clingo_body_aggregate_vec_elem : clingo_body_aggregate_vec
-- syntax:10 clingo_body_aggregate_vec_elem:10 ";" clingo_body_aggregate_vec:11 : clingo_body_aggregate_vec

-- declare_syntax_cat clingo_body_aggregate
-- syntax "{" "}" : clingo_body_aggregate
-- syntax "{" clingo_body_aggregate_vec "}" : clingo_body_aggregate
-- syntax clingo_body_aggregate_op "{" "}" : clingo_body_aggregate
-- syntax clingo_body_aggregate_op "{" clingo_body_aggregate_vec "}" : clingo_body_aggregate

-- declare_syntax_cat clingo_body_aggregate_lub
-- syntax clingo_body_aggregate : clingo_body_aggregate_lub
-- syntax clingo_body_aggregate clingo_term : clingo_body_aggregate_lub
-- syntax clingo_term clingo_body_aggregate : clingo_body_aggregate_lub
-- syntax clingo_term clingo_body_aggregate clingo_term : clingo_body_aggregate_lub
-- syntax clingo_body_aggregate clingo_comparison_op clingo_term : clingo_body_aggregate_lub
-- syntax clingo_term clingo_comparison_op clingo_body_aggregate : clingo_body_aggregate_lub
-- syntax clingo_term clingo_body_aggregate clingo_comparison_op clingo_term : clingo_body_aggregate_lub
-- syntax clingo_term clingo_comparison_op clingo_body_aggregate clingo_term : clingo_body_aggregate_lub
-- syntax clingo_term clingo_comparison_op clingo_body_aggregate clingo_comparison_op clingo_term : clingo_body_aggregate_lub


-- declare_syntax_cat clingo_conjunction
-- syntax clingo_term ": " clingo_term,* : clingo_conjunction

-- declare_syntax_cat clingo_disjunction
-- syntax clingo_term "; " clingo_conjunction : clingo_disjunction
-- syntax clingo_conjunction : clingo_disjunction


-- declare_syntax_cat clingo_body_elem
-- syntax clingo_term : clingo_body_elem
-- syntax clingo_body_aggregate_lub : clingo_body_elem
-- syntax "not" clingo_body_aggregate_lub : clingo_body_elem
-- syntax clingo_conjunction : clingo_body_elem

-- declare_syntax_cat clingo_head
-- syntax clingo_term : clingo_head
-- syntax clingo_body_aggregate_lub : clingo_head
-- syntax clingo_disjunction : clingo_head


-- declare_syntax_cat clingo_statement
-- syntax clingo_head  "." : clingo_statement
-- syntax clingo_head ":-" "." : clingo_statement
-- syntax clingo_head ":-" clingo_body_elem,* "." : clingo_statement
-- syntax ":-" clingo_body_elem,* "." : clingo_statement

def getEndPos? (s: Lean.SourceInfo) : Option String.Pos :=
  match s with
  | SourceInfo.original _ _ _ endPos => endPos
  | SourceInfo.synthetic _ endPos _ => endPos
  | _ => .none

def mkLocation (s : Syntax) : TermElabM Expr := do
        let filename := Syntax.mkStrLit (<- getFileName)
        let fileMap <- getFileMap
        let info := SourceInfo.fromRef s
        let pos := info.getPos?.getD 0
        let endPos := (getEndPos? info).getD pos
        let pos := fileMap.toPosition $ pos
        let endPos := fileMap.toPosition $ endPos
        let locStx :=
               `(Clingo.Location.mk
                            $filename:str $filename:str
                            $(Syntax.mkNumLit s!"{pos.line}") $(Syntax.mkNumLit s!"{endPos.line}")
                            $(Syntax.mkNumLit s!"{pos.column}") $(Syntax.mkNumLit s!"{endPos.column}"))
        Term.elabTerm (<- locStx) none

def mkTerm (stx : Syntax) (data : Expr) : TermElabM Expr := do
   let mkTerm := mkConst `Clingo.Ast.Term.mk
   let loc <- mkLocation stx
   return mkApp2 mkTerm loc data

def mkTermUnaryOp (stx : Syntax) (unOp : Name) (arg : Expr) :=
   mkTerm stx $ mkApp2 (mkConst `Clingo.Ast.Term.Data.UnaryOperator) (mkConst unOp) arg

def mkTermBinaryOp (stx : Syntax) (binOp : Name) (arg1 arg2 : Expr) :=
   mkTerm stx $ mkApp3 (mkConst `Clingo.Ast.Term.Data.BinaryOperator) (mkConst binOp) arg1 arg2

def mkTermInterval (stx : Syntax) (l r : Expr) :=
  mkTerm stx $ mkApp2 (mkConst `Clingo.Ast.Term.Data.Interval) l r

def mkTermFunction (stx : Syntax) (f : Expr) (args : List Expr): TermElabM Expr := do
   mkTerm stx $ mkApp2 (mkConst `Clingo.Ast.Term.Data.Function) f (<- mkArrayLit (mkConst `Clingo.Ast.Term) args)

def mkTermExternalFunction (stx : Syntax) (f : Expr) (args : List Expr) : TermElabM Expr := do
   mkTerm stx $ mkApp2 (mkConst `Clingo.Ast.Term.Data.ExternalFunction) f (<- mkArrayLit (mkConst `Clingo.Ast.Term) args)

def mkTermPool (stx : Syntax) (args : List Expr) : TermElabM Expr := do
   mkTerm stx $ mkApp (mkConst `Clingo.Ast.Term.Data.Pool) (<- mkArrayLit (mkConst `Clingo.Ast.Term) args)


def mkSymbol (expr : Expr) : TermElabM Expr := do
   let mkSymbol := mkConst `Clingo.Symbol.mk
   return mkApp mkSymbol expr

def mkComparison (op: Name) (l r : Expr) : TermElabM Expr := do
   let mkComparison := mkConst `Clingo.Ast.Comparison.mk
   return mkApp3 mkComparison (mkConst op) l r

def elabEnsureComparison (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.Comparison)


def mkCSPProductTerm (stx: Syntax) (coeff var : Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.CSPProductTerm.mk
   return mkApp3 mk loc coeff var

def mkCSPSumTerm (stx: Syntax) (terms : List Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.CSPSumTerm.mk
   return mkApp2 mk loc (<- mkArrayLit (mkConst `Clingo.Ast.CSPProductTerm) terms)

def mkCSPGuard (op : Name) (expr : Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.CSPGuard.mk
   return mkApp2 mk (mkConst op) expr

def mkCSPLiteral (stx: Syntax) (term: Expr) (guards : List Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.CSPLiteral.mk
   return mkApp2 mk term (<- mkArrayLit (mkConst `Clingo.Ast.CSPGuard) guards)

def mkLiteral (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.mk
   let none := mkConst `Clingo.Ast.Sign.None
   let loc <- mkLocation stx
   return mkApp3 mk loc none data

def mkLiteralNeg (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.mk
   let none := mkConst `Clingo.Ast.Sign.Negation
   let loc <- mkLocation stx
   return mkApp3 mk loc none data

def mkLiteralDoubleNeg (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.mk
   let none := mkConst `Clingo.Ast.Sign.DoubleNegation
   let loc <- mkLocation stx
   return mkApp3 mk loc none data


def mkLiteralDataBool (b: Bool) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.Data.Boolean
   return mkApp mk (mkConst <| if b then ``Bool.true else ``Bool.false)

def mkLiteralDataSym (e: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.Data.Symbolic
   return mkApp mk e

def mkLiteralDataComparison (e: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.Data.Comparison
   return mkApp mk e

def mkLiteralDataCSP (e: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Literal.Data.Csp
   return mkApp mk e

def mkLiteralDefaultFalse (stx: Syntax) : TermElabM Expr := do
   let data <- mkLiteralDataBool Bool.false
   mkLiteral stx data

def mkLiteralDefaultTrue (stx: Syntax) : TermElabM Expr := do
   let data <- mkLiteralDataBool Bool.true
   mkLiteral stx data

def mkConditionLiteral (lit: Expr) (args: List Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.ConditionalLiteral.mk
   return mkApp2 mk lit (<- mkArrayLit (mkConst `Clingo.Ast.Literal) args)

def mkAggregateGuard (comparisonOp: Name) (term: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.AggregateGuard.mk
   let cmp := mkConst comparisonOp
   return mkApp2 mk cmp term

def mkInfinumum (stx: Syntax) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Term.mk
   let loc <- mkLocation stx
   let data :=
      mkApp
       (mkConst `Clingo.Ast.Term.Data.Symbol)
       (mkConst `Clingo.Symbol.mk_infimum)
   return (mkApp2 mk loc data)

def mkSupremum (stx: Syntax) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Term.mk
   let loc <- mkLocation stx
   let data :=
      mkApp
       (mkConst `Clingo.Ast.Term.Data.Symbol)
       (mkConst `Clingo.Symbol.mk_supremum)
   return (mkApp2 mk loc data)


def mkAggregateGuardDefaultLow (stx: Syntax) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.AggregateGuard.mk
   let cmp := mkConst `Clingo.Ast.Comparison.Operator.LT
   let term <- mkInfinumum stx
   return mkApp2 mk cmp term

def mkAggregateGuardDefaultHigh (stx: Syntax) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.AggregateGuard.mk
   let cmp := mkConst `Clingo.Ast.Comparison.Operator.LT
   let term <- mkSupremum stx
   return mkApp2 mk cmp term

def mkAggregate (elements: List Expr) (left: Expr) (right: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Aggregate.mk
   return (
     mkApp3 mk
       (<- mkArrayLit (mkConst `Clingo.Ast.ConditionalLiteral) elements)
       left right)

def mkAggregateHeadElement (tuple: List Expr) (cond: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Aggregate.Head.Element.mk
   return mkApp2 mk
        (<- mkArrayLit (mkConst `Clingo.Ast.Term) tuple)
        cond

def mkAggregateHead (func: Name) (elements: List Expr) (left: Expr) (right: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Aggregate.Head.mk
   return mkApp4 mk
        (mkConst func)
        (<- mkArrayLit (mkConst `Clingo.Ast.Aggregate.Head.Element) elements)
        left
        right

def mkAggregateBodyElement (tuple: List Expr) (cond: List Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Aggregate.Body.Element.mk
   return mkApp2 mk
        (<- mkArrayLit (mkConst `Clingo.Ast.Term) tuple)
        (<- mkArrayLit (mkConst `Clingo.Ast.Literal) cond)

def mkAggregateBody (func: Name) (elements: List Expr) (left: Expr) (right: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Aggregate.Body.mk
   return mkApp4 mk
        (mkConst func)
        (<- mkArrayLit (mkConst `Clingo.Ast.Aggregate.Body.Element) elements)
        left
        right

def mkDefinition (name: String) (value: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Definition.mk
   return mkApp3 mk
        (mkStrLit name)
        value
        (mkConst `Bool.true)

def mkHeadLiteral (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.HeadLiteral.mk
   return mkApp2 mk
        loc
        data

def mkHeadLiteralLiteral (stx: Syntax) (lit: Expr) : TermElabM Expr := do
   let data := mkApp (mkConst `Clingo.Ast.HeadLiteral.Data.Literal) lit
   mkHeadLiteral stx data

def mkHeadLiteralDisjunction (stx: Syntax) (elems: List Expr) : TermElabM Expr := do
   let data := mkApp (mkConst `Clingo.Ast.HeadLiteral.Data.Disjunction)
                (<- mkArrayLit (mkConst `Clingo.Ast.ConditionLiteral) elems)
   mkHeadLiteral stx data

def mkHeadLiteralAggregate (stx: Syntax) (agg: Expr) : TermElabM Expr := do
   let data := mkApp (mkConst `Clingo.Ast.HeadLiteral.Data.Aggregate) agg
   mkHeadLiteral stx data

def mkHeadLiteralHeadAggregate (stx: Syntax) (agg: Expr) : TermElabM Expr := do
   let data := mkApp (mkConst `Clingo.Ast.HeadLiteral.Data.HeadAggregate) agg
   mkHeadLiteral stx data

def mkHeadLiteralDefaultFalse (stx: Syntax) : TermElabM Expr := do
   let falseLit <- mkLiteralDefaultFalse stx
   let data := mkApp (mkConst `Clingo.Ast.HeadLitera.Data.Literal) falseLit
   mkHeadLiteral stx data
       

def mkBodyLiteral (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.BodyLiteral.mk
   return mkApp3 mk
        loc
        (mkConst `Clingo.Ast.Sign.None)
        data

def mkBodyLiteralNegation (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.BodyLiteral.mk
   return mkApp3 mk
        loc
        (mkConst `Clingo.Ast.Sign.Negation)
        data

def mkBodyLiteralDoubleNegation (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.BodyLiteral.mk
   return mkApp3 mk
        loc
        (mkConst `Clingo.Ast.Sign.DoubleNegation)
        data


def mkBodyLiteralDataLiteral (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.BodyLiteral.Data.Literal
   return mkApp mk data

def mkBodyLiteralDataConditional (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.BodyLiteral.Data.Conditional
   return mkApp mk data

def mkBodyLiteralDataAggregate (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.BodyLiteral.Data.Aggregate
   return mkApp mk data

def mkBodyLiteralDataBodyAggregate (data: Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.BodyLiteral.Data.BodyAggregate
   return mkApp mk data

def mkAstStatement (stx: Syntax) (data: Expr) : TermElabM Expr := do
   let loc <- mkLocation stx
   let mk := mkConst `Clingo.Ast.Statement.mk
   return mkApp2 mk loc data

def mkAstStatementDataRule (head : Expr) (body: List Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Statement.Data.Rule
   return mkApp2 mk head (<- mkArrayLit (mkConst `Clingo.Ast.BodyLiteral) body)

def mkAstStatementDataConst (data : Expr) : TermElabM Expr := do
   let mk := mkConst `Clingo.Ast.Statement.Data.Const
   return mkApp mk data

def elabTermEnsureTerm (t: Syntax) : TermElabM Expr := do
   let expr <- Term.elabTerm t none
   let ty <- inferType expr
   if <- isDefEq ty (mkConst `Clingo.Symbol.Repr)
   then mkTerm t (mkApp (mkConst `Clingo.Ast.Term.Data.Symbol) (<- mkSymbol expr))
   else return expr

def elabEnsureCSPSumTerm (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.CSPSumTerm)

def elabEnsureCSPLiteral (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.CSPLiteral)

def elabEnsureLiteral (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.Literal)

def elabEnsureConditionLiteral (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.ConditionalLiteral)

def elabEnsureAggregate (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.Aggregate)

def elabEnsureHeadAggregateElement (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.Aggregate.Head.Element)

def elabEnsureHeadAggregate (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.Aggregate.Head)

def elabEnsureBodyAggregateElement (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.Aggregate.Body.Element)

def elabEnsureBodyAggregate (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.Aggregate.Body)

def elabEnsureDefinition (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.Definition)

def elabEnsureBodyLiteral (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.BodyLiteral)

def elabEnsureHeadLiteral (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.HeadLiteral)

def elabEnsureStatement (t: Syntax) : TermElabM Expr := do
   Term.elabTerm t (mkConst `Clingo.Ast.Statement)


def buildArgs (t : TSyntaxArray `clingo_term) : TermElabM (Expr × Bool × Expr) := do
    -- elaborate each of the arguments and infer types
    let args_and_tys <- 
            t.mapM (fun stx => do
                let expr <- Term.elabTerm stx none
                let expr_ty <- inferType expr
                return ⟨expr, expr_ty, stx⟩
             )
    -- if any argument is a term, then result must be a term
    let is_term <- args_and_tys.anyM (fun (v : Expr × Expr × Syntax) => do
              let ⟨e,e_ty,stx⟩ := v
              isDefEq e_ty (mkConst `Clingo.Ast.Term))
    let res_ty := mkConst (if is_term then `Clingo.Ast.Term else `Clingo.Symbol.Repr)
    let res <-
        args_and_tys.mapM (fun (expr_and_ty : Expr × Expr × Syntax) => do
            let ⟨expr, e_ty, stx⟩ := expr_and_ty
            if e_ty.isMVar then
               Lean.MVarId.assign e_ty.mvarId! $ res_ty
            -- if it's a symbol, embed into term
            if (<- isDefEq e_ty (mkConst `Clingo.Symbol.Repr)) && is_term
            then mkTerm stx $ mkApp (mkConst `Clingo.Ast.Term.Data.Symbol) (<- mkSymbol expr)
            else return expr)
    let argsList <- mkArrayLit res_ty res.toList
    return ⟨argsList, is_term, res_ty⟩

elab_rules : term
| `(clingo_term| $x:ident) => do
    let xStr := Syntax.mkStrLit x.getId.toString
    if Char.isUpper $ x.getId.toString.get! 0
    then do
       let var <- Term.elabTerm (<- `(Clingo.Ast.Term.Data.Variable $xStr:str)) none
       mkTerm x.raw var
    else Term.elabTerm (<- `(term| Clingo.Symbol.Repr.Function $xStr:str #[] Bool.true)).raw none
| `(clingo_term| - $x:ident) => do
    let xStr := Syntax.mkStrLit x.getId.toString
    if Char.isUpper $ x.getId.toString.get! 0
    then do
       let var <- Term.elabTerm (<- `(Clingo.Ast.Term.Data.Variable $xStr:str)) none
       mkTermUnaryOp x `Clingo.Ast.UnaryOperator.Minus $ (<- mkTerm x.raw var)
    else Term.elabTerm (<- `(term| Clingo.Symbol.Repr.Function $xStr:str #[] Bool.false)).raw none
| `(clingo_term| $x:num) => do
    let xStr := Syntax.mkNumLit (reprStr x.getNat)
    Term.elabTerm (<- `(Clingo.Symbol.Repr.Number $xStr:num)) none
| `(clingo_term| - $x:num) => do
    let xStr := Syntax.mkNumLit (reprStr x.getNat)
    Term.elabTerm (<- `(Clingo.Symbol.Repr.Number (- $xStr:num))) none
| `(clingo_term| $x:str) => do
    Term.elabTerm (<- `(Clingo.Symbol.Repr.String $x:str)) none
| `(clingo_term| #inf) => do
    Term.elabTerm (<- `(Clingo.Symbol.Repr.Infimum)) none
| `(clingo_term| #sup) => do
    Term.elabTerm (<- `(Clingo.Symbol.Repr.Supremum)) none
| `(clingo_term| -$fStx:ident($t:clingo_term,*)) => do
    let f := mkStrLit fStx.getId.toString
    let args_and_tys <- buildArgs t.getElems
    let ⟨argsList, is_term, res_ty⟩ := args_and_tys
    match is_term with
    | Bool.true => 
        let fApp <- mkTerm fStx (mkAppN
              (mkConst `Clingo.Ast.Term.Data.Function)
              (#[f, argsList]))
        mkTermUnaryOp fStx `Clingo.Ast.UnaryOperator.Minus fApp
    | Bool.false => 
         return (mkAppN
              (mkConst `Clingo.Symbol.Repr.Function)
              (#[f, argsList, (mkConst ``Bool.false)]))

| `(clingo_term| $fStx:ident($t:clingo_term,*)) => do
    let f := mkStrLit fStx.getId.toString
    let args_and_tys <- buildArgs t.getElems
    let ⟨argsList, is_term, res_ty⟩ := args_and_tys
    match is_term with
    | Bool.true => 
        mkTerm fStx (mkAppN
              (mkConst `Clingo.Ast.Term.Data.Function)
              (#[f, argsList]))
    | Bool.false => 
         return (mkAppN
              (mkConst `Clingo.Symbol.Repr.Function)
              (#[f, argsList, (mkConst ``Bool.true)]))

| `(clingo_term| @ $fStx:ident($t:clingo_term,*)) => do
    let f := mkStrLit fStx.getId.toString
    let argsList <- t.getElems.mapM (fun t => elabTermEnsureTerm t)
    let argsList <- mkArrayLit (mkConst `Clingo.Ast.Term) argsList.toList
    mkTerm fStx (mkAppN
         (mkConst `Clingo.Ast.Term.Data.ExternalFunction)
         (#[f, argsList]))

| `(clingo_term| - $t:clingo_term) => do
   let expr <- elabTermEnsureTerm t
   mkTermUnaryOp t `Clingo.Ast.UnaryOperator.Minus expr

| `(clingo_term| ~ $t:clingo_term) => do
   let expr <- elabTermEnsureTerm t
   mkTermUnaryOp t `Clingo.Ast.UnaryOperator.Negation expr

| `(clingo_term| | $t:clingo_term |) => do
   let expr <- elabTermEnsureTerm t
   mkTermUnaryOp t `Clingo.Ast.UnaryOperator.Absolute expr

| `(clingo_term|  $l:clingo_term ^ $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.XOR lExpr rExpr

| `(clingo_term|  $l:clingo_term ? $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.OR lExpr rExpr

| `(clingo_term|  $l:clingo_term & $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.AND lExpr rExpr

| `(clingo_term|  $l:clingo_term + $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.PLUS lExpr rExpr

| `(clingo_term|  $l:clingo_term - $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.MINUS lExpr rExpr

| `(clingo_term|  $l:clingo_term * $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.MULTIPLICATION lExpr rExpr

| `(clingo_term|  $l:clingo_term / $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.DIVISION lExpr rExpr

| `(clingo_term|  $l:clingo_term \\ $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.MODULO lExpr rExpr


| `(clingo_term|  $l:clingo_term ** $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermBinaryOp l `Clingo.Ast.BinaryOperator.POWER lExpr rExpr

| `(clingo_term|  $l:clingo_term .. $r:clingo_term ) => do
   let lExpr <- elabTermEnsureTerm l
   let rExpr <- elabTermEnsureTerm r
   mkTermInterval l lExpr rExpr

| `(clingo_term|  ( $l:clingo_term ) ) => do
   let lExpr <- elabTermEnsureTerm l
   return lExpr

| `(clingo_term|  ( $l:clingo_term,* ) ) => do
   let args <- l.getElems.mapM (fun v => elabTermEnsureTerm v)
   mkTermPool (l.getElems.get! 0) args.toList


elab_rules : term
| `(clingo_comparison| $t1:clingo_term < $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.LT (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_comparison| $t1:clingo_term > $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.GT (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_comparison| $t1:clingo_term <= $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.LEQ (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_comparison| $t1:clingo_term >= $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.GEQ (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_comparison| $t1:clingo_term = $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.EQ (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_comparison| $t1:clingo_term != $t2:clingo_term) => do
   mkComparison `Clingo.Ast.Comparison.Operator.NEQ (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)

elab_rules : term
| `(clingo_csp_mul_term| $ $t1:clingo_term $* $t2:clingo_term) => do
    mkCSPProductTerm t1 (<- elabTermEnsureTerm t1) (<- elabTermEnsureTerm t2)
| `(clingo_csp_mul_term| $t1:clingo_term $* $ $t2:clingo_term) => do
    mkCSPProductTerm t1 (<- elabTermEnsureTerm t2) (<- elabTermEnsureTerm t1)
| `(clingo_csp_mul_term| $ $t1:clingo_term) => do
    mkCSPProductTerm t1
        (<- elabTermEnsureTerm (<- `(clingo_term| 1)))
        (<- elabTermEnsureTerm t1)
| `(clingo_csp_mul_term| $t1:clingo_term) => do
    mkCSPProductTerm t1
        (<- elabTermEnsureTerm t1)
        (<- elabTermEnsureTerm (<- `(clingo_term| 1)))

partial def build_csp_sum_term (rstx: Syntax) (acc : List Expr) (stx : Syntax) : TermElabM Expr :=
   match stx with
   | `(clingo_csp_add_term| $t1:clingo_csp_add_term $+ $t2:clingo_csp_mul_term) => do
       build_csp_sum_term rstx (List.cons (<- Term.elabTerm t2 .none) acc) t1
   | `(clingo_csp_add_term| $t1:clingo_csp_add_term $- $t2:clingo_csp_mul_term) => do
       let loc <- mkLocation t2
       let fStx <- `(term| (fun loc (pt: Clingo.Ast.CSPProductTerm) =>
                             Clingo.Ast.CSPProductTerm.mk
                                loc
                                (Clingo.Ast.Term.mk loc
                                   (Clingo.Ast.Term.Data.UnaryOperator .Negation pt.coefficient))
                                pt.variable_))
       let f <- Term.elabTerm fStx .none
       let t2 <- Term.elabTerm t2 .none
       let t2 := mkApp2 f loc t2
       build_csp_sum_term rstx (List.cons t2 acc) t1
   | `(clingo_csp_add_term| $t1:clingo_csp_mul_term) => do
       mkCSPSumTerm rstx (List.cons (<- Term.elabTerm t1 .none) acc)
   | _ => do throwUnsupportedSyntax

elab_rules : term
| `(clingo_csp_add_term| $t1:clingo_csp_add_term $+ $t2:clingo_csp_mul_term) => do
   build_csp_sum_term t1 [] (<- `(clingo_csp_add_term| $t1 $+ $t2))
| `(clingo_csp_add_term| $t1:clingo_csp_add_term $- $t2:clingo_csp_mul_term) => do
   build_csp_sum_term t1 [] (<- `(clingo_csp_add_term| $t1 $- $t2))
| `(clingo_csp_add_term| $t1:clingo_csp_mul_term) => do
   build_csp_sum_term t1 [] (<- `(clingo_csp_add_term| $t1:clingo_csp_mul_term))

partial def build_clingo_csp_literal_term (guards : List Expr) (stx : Syntax) : TermElabM Expr :=
  match stx with
  | `(clingo_csp_literal| $t1:clingo_csp_literal $< $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LT (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1
  | `(clingo_csp_literal| $t1:clingo_csp_literal $> $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GT (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1
  | `(clingo_csp_literal| $t1:clingo_csp_literal $<= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1
  | `(clingo_csp_literal| $t1:clingo_csp_literal $>= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1
  | `(clingo_csp_literal| $t1:clingo_csp_literal $= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.EQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1
  | `(clingo_csp_literal| $t1:clingo_csp_literal $!= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.NEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term (List.cons guard guards) t1

  | `(clingo_csp_literal| $t1:clingo_csp_add_term $< $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LT (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards)
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | `(clingo_csp_literal| $t1:clingo_csp_add_term $> $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GT (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards).reverse
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | `(clingo_csp_literal| $t1:clingo_csp_add_term $<= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LEQ (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards)
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | `(clingo_csp_literal| $t1:clingo_csp_add_term $>= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GEQ (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards)
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | `(clingo_csp_literal| $t1:clingo_csp_add_term $= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.EQ (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards)
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | `(clingo_csp_literal| $t1:clingo_csp_add_term $!= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.NEQ (<- elabEnsureCSPSumTerm t2)
     let guards := (List.cons guard guards)
     mkCSPLiteral stx (<- elabEnsureCSPSumTerm t1) guards
  | _ => do throwUnsupportedSyntax

elab_rules : term
| `(clingo_csp_literal| $t1:clingo_csp_literal $< $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LT (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard]  t1
| `(clingo_csp_literal| $t1:clingo_csp_literal $> $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GT (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard] t1
| `(clingo_csp_literal| $t1:clingo_csp_literal $<= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard] t1
| `(clingo_csp_literal| $t1:clingo_csp_literal $>= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard] t1
| `(clingo_csp_literal| $t1:clingo_csp_literal $= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.EQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard] t1
| `(clingo_csp_literal| $t1:clingo_csp_literal $!= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.NEQ (<- elabEnsureCSPSumTerm t2)
     build_clingo_csp_literal_term [guard] t1
| `(clingo_csp_literal| $t1:clingo_csp_add_term $< $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LT (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards
| `(clingo_csp_literal| $t1:clingo_csp_add_term $> $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GT (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards
| `(clingo_csp_literal| $t1:clingo_csp_add_term $<= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.LEQ (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards
| `(clingo_csp_literal| $t1:clingo_csp_add_term $>= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.GEQ (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards
| `(clingo_csp_literal| $t1:clingo_csp_add_term $= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.EQ (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards
| `(clingo_csp_literal| $t1:clingo_csp_add_term $!= $t2:clingo_csp_add_term) => do
     let guard <- mkCSPGuard `Clingo.Ast.Comparison.Operator.NEQ (<- elabEnsureCSPSumTerm t2)
     let guards := [guard]
     mkCSPLiteral t1 (<- elabEnsureCSPSumTerm t1) guards

elab_rules : term
| `(clingo_literal| $x:clingo_bool_const) => do
   let data <- mkLiteralDataBool (x.raw.getAtomVal == "true")
   mkLiteral x data

| `(clingo_literal| not $x:clingo_bool_const) => do
   let data <- mkLiteralDataBool (x.raw.getAtomVal == "true")
   mkLiteralNeg x data

| `(clingo_literal| not not $x:clingo_bool_const) => do
   let data <- mkLiteralDataBool (x.raw.getAtomVal == "true")
   mkLiteralDoubleNeg x data

| `(clingo_literal| $cmpStx:clingo_comparison) => do
   let cmp <- elabEnsureComparison cmpStx
   let data <- mkLiteralDataComparison cmp
   mkLiteral cmpStx data

| `(clingo_literal| not $cmpStx:clingo_comparison) => do
   let cmp <- elabEnsureComparison cmpStx
   let data <- mkLiteralDataComparison cmp
   mkLiteralNeg cmpStx data

| `(clingo_literal| not not $cmpStx:clingo_comparison) => do
   let cmp <- elabEnsureComparison cmpStx
   let data <- mkLiteralDataComparison cmp
   mkLiteralDoubleNeg cmpStx data

| `(clingo_literal| $cmpStx:clingo_term) => do
   let cmp <- elabTermEnsureTerm cmpStx
   let data <- mkLiteralDataSym cmp
   mkLiteral cmpStx data

| `(clingo_literal| not $cmpStx:clingo_term) => do
   let cmp <- elabTermEnsureTerm cmpStx
   let data <- mkLiteralDataSym cmp
   mkLiteralNeg cmpStx data

| `(clingo_literal| not not $cmpStx:clingo_term) => do
   let cmp <- elabTermEnsureTerm cmpStx
   let data <- mkLiteralDataSym cmp
   mkLiteralDoubleNeg cmpStx data

| `(clingo_literal| $cmpStx:clingo_csp_literal) => do
   let cmp <- elabEnsureCSPLiteral cmpStx
   let data <- mkLiteralDataCSP cmp
   mkLiteral cmpStx data

| `(clingo_literal| not $cmpStx:clingo_csp_literal) => do
   let cmp <- elabEnsureCSPLiteral cmpStx
   let data <- mkLiteralDataCSP cmp
   mkLiteralNeg cmpStx data

| `(clingo_literal| not not $cmpStx:clingo_csp_literal) => do
   let cmp <- elabEnsureCSPLiteral cmpStx
   let data <- mkLiteralDataCSP cmp
   mkLiteralDoubleNeg cmpStx data


elab_rules : term
| `(clingo_condition_literal| $cStx:clingo_literal : $constrsStx:clingo_literal,*) => do
   let data <- elabEnsureLiteral cStx
   let args <- constrsStx.getElems.mapM elabEnsureLiteral
   mkConditionLiteral data args.toList

| `(clingo_condition_literal| $cStx:clingo_literal) => do
   let data <- elabEnsureLiteral cStx
   mkConditionLiteral data []

partial def build_clingo_condition_literal_seq (acc : List Expr) (stx : Syntax) : TermElabM (List Expr) :=
   match stx with
   | `(clingo_condition_literal_seq| $t1:clingo_condition_literal_seq; $t2:clingo_condition_literal) => do
       let t2 <- elabEnsureConditionLiteral t2
       build_clingo_condition_literal_seq (acc.cons t2) t1
   | `(clingo_condition_literal_seq| $t1:clingo_condition_literal) => do
       let t1 <- elabEnsureConditionLiteral t1
       return (List.cons t1 acc)
   | _ => do throwUnsupportedSyntax


partial def extract_clingo_comparison_op (stx : Syntax) : TermElabM Name :=
   match stx with
   | `(clingo_comparison_op| >) => do
      return `Clingo.Ast.Comparison.Operator.GT
   | `(clingo_comparison_op| <) => do
      return `Clingo.Ast.Comparison.Operator.LT
   | `(clingo_comparison_op| >=) => do
      return `Clingo.Ast.Comparison.Operator.GEQ
   | `(clingo_comparison_op| <=) => do
      return `Clingo.Ast.Comparison.Operator.LEQ
   | `(clingo_comparison_op| !=) => do
      return `Clingo.Ast.Comparison.Operator.NEQ
   | `(clingo_comparison_op| =) => do
      return `Clingo.Ast.Comparison.Operator.EQ
   | _ => do throwUnsupportedSyntax




elab_rules : term
| `(clingo_aggregate| $s:clingo_aggregate_empty_body) => do
   mkAggregate []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate| $t1:clingo_term $cmp:clingo_comparison_op $s:clingo_aggregate_empty_body) => do
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregate []
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate| $s:clingo_aggregate_empty_body $cmp:clingo_comparison_op $t2:clingo_term) => do
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregate []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)

| `(clingo_aggregate| $t1:clingo_term $cmp1:clingo_comparison_op  {  }  $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregate []
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)


| `(clingo_aggregate| { $s:clingo_condition_literal_seq }) => do
   let terms <- build_clingo_condition_literal_seq [] s
   mkAggregate terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate| $t1:clingo_term $cmp:clingo_comparison_op { $s:clingo_condition_literal_seq }) => do
   let terms <- build_clingo_condition_literal_seq [] s
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregate terms
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate|  { $s:clingo_condition_literal_seq }  $cmp:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_condition_literal_seq [] s
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregate terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)

| `(clingo_aggregate| $t1:clingo_term $cmp1:clingo_comparison_op  { $s:clingo_condition_literal_seq }  $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_condition_literal_seq [] s
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregate terms
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)

-- elab_rules : command
-- | `(command| x)


elab_rules : term
| `(clingo_head_aggregate_element| $t:clingo_term,* ) => do
   let tExprs <- t.getElems.mapM elabTermEnsureTerm
   let lit <- mkLiteralDefaultTrue (t.getElems.get! 0)
   mkAggregateHeadElement tExprs.toList lit

| `(clingo_head_aggregate_element| $t:clingo_term,* : $clit:clingo_condition_literal ) => do
   let tExprs <- t.getElems.mapM elabTermEnsureTerm
   let clit <- elabEnsureConditionLiteral clit
   mkAggregateHeadElement tExprs.toList clit

partial def build_clingo_head_aggregate_element_seq (acc : List Expr) (stx : Syntax) : TermElabM (List Expr) :=
   match stx with
   | `(clingo_head_aggregate_element_seq| $t1:clingo_head_aggregate_element_seq; $t2:clingo_head_aggregate_element) => do
       let t2 <- elabEnsureHeadAggregateElement t2
       build_clingo_head_aggregate_element_seq (acc.cons t2) t1
   | `(clingo_head_aggregate_element_seq| $t1:clingo_head_aggregate_element) => do
       let t1 <- elabEnsureHeadAggregateElement t1
       return (List.cons t1 acc)
   | _ => do throwUnsupportedSyntax



partial def extract_clingo_aggregate_func (stx : Syntax) : TermElabM Name :=
   match stx with
   | `(clingo_aggregate_function| count) => do
      return `Clingo.Ast.Aggregate.Function.Count
   | `(clingo_aggregate_function| sum) => do
      return `Clingo.Ast.Aggregate.Function.Sum
   | `(clingo_aggregate_function| sump) => do
      return `Clingo.Ast.Aggregate.Function.Sump
   | `(clingo_aggregate_function| min) => do
      return `Clingo.Ast.Aggregate.Function.Min
   | `(clingo_aggregate_function| max) => do
      return `Clingo.Ast.Aggregate.Function.Max
   | _ => do throwUnsupportedSyntax


elab_rules : term
| `(clingo_aggregate_head| $func:clingo_aggregate_function $s:clingo_aggregate_empty_body) => do
   let func <- extract_clingo_aggregate_func func
   mkAggregateHead func []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_head| $t1:clingo_term $cmp:clingo_comparison_op $func:clingo_aggregate_function $s:clingo_aggregate_empty_body) => do
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregateHead func []
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_head| $func:clingo_aggregate_function $s:clingo_aggregate_empty_body $cmp:clingo_comparison_op $t2:clingo_term) => do
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregateHead func []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)

| `(clingo_aggregate_head| $t1:clingo_term $cmp1:clingo_comparison_op $func:clingo_aggregate_function $s:clingo_aggregate_empty_body $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let func <- extract_clingo_aggregate_func func
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregateHead func []
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)

| `(clingo_aggregate_head| $func:clingo_aggregate_function { $s:clingo_head_aggregate_element_seq }) => do
   let terms <- build_clingo_head_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   mkAggregateHead func terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_head| $t1:clingo_term $cmp:clingo_comparison_op $func:clingo_aggregate_function { $s:clingo_head_aggregate_element_seq }) => do
   let terms <- build_clingo_head_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregateHead func terms
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_head|  $func:clingo_aggregate_function { $s:clingo_head_aggregate_element_seq } $cmp:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_head_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregateHead func terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)


| `(clingo_aggregate_head|  $t1:clingo_term $cmp1:clingo_comparison_op $func:clingo_aggregate_function { $s:clingo_head_aggregate_element_seq }  $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_head_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregateHead func terms
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)


elab_rules : term
| `(clingo_body_aggregate_element| $t:clingo_term,* ) => do
   let tExprs <- t.getElems.mapM elabTermEnsureTerm
   let lit <- mkLiteralDefaultTrue (t.getElems.get! 0)
   mkAggregateBodyElement tExprs.toList [lit]

| `(clingo_body_aggregate_element| $t:clingo_term,* : $clit:clingo_literal,* ) => do
   let tExprs <- t.getElems.mapM elabTermEnsureTerm
   let clit <- clit.getElems.mapM elabEnsureLiteral
   mkAggregateBodyElement tExprs.toList clit.toList


partial def build_clingo_body_aggregate_element_seq (acc : List Expr) (stx : Syntax) : TermElabM (List Expr) :=
   match stx with
   | `(clingo_body_aggregate_element_seq| $t1:clingo_body_aggregate_element_seq; $t2:clingo_body_aggregate_element) => do
       let t2 <- elabEnsureBodyAggregateElement t2
       build_clingo_body_aggregate_element_seq (acc.cons t2) t1
   | `(clingo_body_aggregate_element_seq| $t1:clingo_body_aggregate_element) => do
       let t1 <- elabEnsureBodyAggregateElement t1
       return (List.cons t1 acc)
   | _ => do throwUnsupportedSyntax

elab_rules : term
| `(clingo_aggregate_body| $func:clingo_aggregate_function $s:clingo_aggregate_empty_body) => do
   let func <- extract_clingo_aggregate_func func
   mkAggregateBody func []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_body| $t1:clingo_term $cmp:clingo_comparison_op $func:clingo_aggregate_function $s:clingo_aggregate_empty_body) => do
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregateBody func []
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_body| $func:clingo_aggregate_function $s:clingo_aggregate_empty_body $cmp:clingo_comparison_op $t2:clingo_term) => do
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregateBody func []
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)

| `(clingo_aggregate_body| $t1:clingo_term $cmp1:clingo_comparison_op $func:clingo_aggregate_function $s:clingo_aggregate_empty_body $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let func <- extract_clingo_aggregate_func func
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregateBody func []
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)

| `(clingo_aggregate_body| $func:clingo_aggregate_function { $s:clingo_body_aggregate_element_seq }) => do
   let terms <- build_clingo_body_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   mkAggregateBody func terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_body| $t1:clingo_term $cmp:clingo_comparison_op $func:clingo_aggregate_function { $s:clingo_body_aggregate_element_seq }) => do
   let terms <- build_clingo_body_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t1 <- elabTermEnsureTerm t1
   mkAggregateBody func terms
      (<- mkAggregateGuard cmp t1)
      (<- mkAggregateGuardDefaultHigh s)

| `(clingo_aggregate_body|  $func:clingo_aggregate_function { $s:clingo_body_aggregate_element_seq } $cmp:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_body_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp <- extract_clingo_comparison_op cmp
   let t2 <- elabTermEnsureTerm t2
   mkAggregateBody func terms
      (<- mkAggregateGuardDefaultLow s)
      (<- mkAggregateGuard cmp t2)


| `(clingo_aggregate_body|  $t1:clingo_term $cmp1:clingo_comparison_op $func:clingo_aggregate_function { $s:clingo_body_aggregate_element_seq }  $cmp2:clingo_comparison_op $t2:clingo_term) => do
   let terms <- build_clingo_body_aggregate_element_seq [] s
   let func <- extract_clingo_aggregate_func func
   let cmp1 <- extract_clingo_comparison_op cmp1
   let cmp2 <- extract_clingo_comparison_op cmp2
   let t1 <- elabTermEnsureTerm t1
   let t2 <- elabTermEnsureTerm t2
   mkAggregateBody func terms
      (<- mkAggregateGuard cmp1 t1)
      (<- mkAggregateGuard cmp2 t2)


elab_rules : term
| `(clingo_head_literal| $clitStx:clingo_literal) => do
   let clit <- elabEnsureLiteral clitStx
   mkHeadLiteralLiteral clitStx clit
| `(clingo_head_literal| $clitStx:clingo_condition_literal_seq) => do
   let clit <- build_clingo_condition_literal_seq [] clitStx
   mkHeadLiteralDisjunction clitStx clit
| `(clingo_head_literal| $aggStx:clingo_aggregate) => do
   let agg <- elabEnsureAggregate aggStx
   mkHeadLiteralAggregate aggStx agg
| `(clingo_head_literal| $aggStx:clingo_aggregate_head) => do
   let agg <- elabEnsureHeadAggregate aggStx
   mkHeadLiteralHeadAggregate aggStx agg

elab_rules : term
| `(clingo_body_literal| $clitStx:clingo_literal) => do
   let clit <- elabEnsureLiteral clitStx
   mkBodyLiteral clitStx (<- mkBodyLiteralDataLiteral clit)
| `(clingo_body_literal| $clitStx:clingo_condition_literal) => do
   let clit <- elabEnsureConditionLiteral clitStx
   mkBodyLiteral clitStx (<- mkBodyLiteralDataConditional clit)
| `(clingo_body_literal| $clitStx:clingo_aggregate) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteral clitStx (<- mkBodyLiteralDataAggregate clit)
| `(clingo_body_literal| $clitStx:clingo_aggregate_body) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteral clitStx (<- mkBodyLiteralDataBodyAggregate clit)


| `(clingo_body_literal| not $clitStx:clingo_literal) => do
   let clit <- elabEnsureLiteral clitStx
   mkBodyLiteralNegation clitStx (<- mkBodyLiteralDataLiteral clit)
| `(clingo_body_literal| not $clitStx:clingo_condition_literal) => do
   let clit <- elabEnsureConditionLiteral clitStx
   mkBodyLiteralNegation clitStx (<- mkBodyLiteralDataConditional clit)
| `(clingo_body_literal| not $clitStx:clingo_aggregate) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteralNegation clitStx (<- mkBodyLiteralDataAggregate clit)
| `(clingo_body_literal| not $clitStx:clingo_aggregate_body) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteralNegation clitStx (<- mkBodyLiteralDataBodyAggregate clit)


| `(clingo_body_literal| not not $clitStx:clingo_literal) => do
   let clit <- elabEnsureLiteral clitStx
   mkBodyLiteralDoubleNegation clitStx (<- mkBodyLiteralDataLiteral clit)
| `(clingo_body_literal| not not $clitStx:clingo_condition_literal) => do
   let clit <- elabEnsureConditionLiteral clitStx
   mkBodyLiteralDoubleNegation clitStx (<- mkBodyLiteralDataConditional clit)
| `(clingo_body_literal| not not $clitStx:clingo_aggregate) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteralDoubleNegation clitStx (<- mkBodyLiteralDataAggregate clit)
| `(clingo_body_literal| not not $clitStx:clingo_aggregate_body) => do
   let clit <- elabEnsureAggregate clitStx
   mkBodyLiteralDoubleNegation clitStx (<- mkBodyLiteralDataBodyAggregate clit)

elab_rules : term
| `(clingo_definition| #const  $name:ident = $t:clingo_term .) => do
   let s := name.getId.toString
   let vl <- elabTermEnsureTerm t
   mkDefinition s vl

partial def build_clingo_body_literal_seq (acc : List Expr) (stx : Syntax) : TermElabM (List Expr) :=
   match stx with
   | `(clingo_body_literal_seq| $t1:clingo_body_literal_seq; $t2:clingo_body_literal) => do
       let t2 <- elabEnsureBodyLiteral t2
       build_clingo_body_literal_seq (acc.cons t2) t1
   | `(clingo_body_literal_seq| $t1:clingo_body_literal) => do
       let t1 <- elabEnsureBodyLiteral t1
       return (List.cons t1 acc)
   | _ => do throwUnsupportedSyntax


elab_rules : term
| `(clingo_statement| $cdefStx:clingo_definition) => do
    let cdef <- elabEnsureDefinition cdefStx
    mkAstStatement cdefStx
       (<- mkAstStatementDataConst cdef)
| `(clingo_statement| $headStx:clingo_head_literal :- $bodyStx:clingo_body_literal_seq .) => do
    let body <- build_clingo_body_literal_seq [] bodyStx
    let head <- elabEnsureHeadLiteral headStx
    mkAstStatement headStx
       (<- mkAstStatementDataRule head body)
| `(clingo_statement| $headStx:clingo_head_literal .) => do
    let head <- elabEnsureHeadLiteral headStx
    mkAstStatement headStx
       (<- mkAstStatementDataRule head [])
| `(clingo_statement| :- $bodyStx:clingo_body_literal_seq .) => do
    let body <- build_clingo_body_literal_seq [] bodyStx
    let head <- mkHeadLiteralDefaultFalse bodyStx
    mkAstStatement bodyStx
       (<- mkAstStatementDataRule head body)


def build_term (t: Syntax): TSyntax `term := TSyntax.mk t

syntax "add_clingo_query!" term ":" (colGt clingo_statement)*  : term
macro_rules 
| `(term| add_clingo_query! $control:term : $cs:clingo_statement*) =>
    `(($control : Clingo.Control).withProgramBuilder fun pb => do
        pb.addStatements [$(Syntax.TSepArray.ofElems <| cs.raw.map build_term),*]
        return ()
     )

syntax "clingo_term!" "(" clingo_term ")" : term
elab_rules : term
| `(term| clingo_term!($s:clingo_term)) => do
    Term.elabTerm s none

syntax "clingo_csp_term!" "(" clingo_csp_add_term ")" : term
elab_rules : term
| `(term| clingo_csp_term!($s:clingo_csp_add_term)) => do
    let t <- Term.elabTerm s none
    return t

syntax "clingo_comparison!" "(" clingo_comparison ")" : term
elab_rules : term
| `(term| clingo_comparison!($s:clingo_comparison)) => do
    Term.elabTerm s none

syntax "clingo_csp_literal!" "(" clingo_csp_literal ")" : term
elab_rules : term
| `(term| clingo_csp_literal!($s:clingo_csp_literal)) => do
    Term.elabTerm s none

syntax "clingo_literal!" "(" clingo_literal ")" : term
elab_rules : term
| `(term| clingo_literal!($s:clingo_literal)) => do
    Term.elabTerm s none

syntax "clingo_condition_literal!" "(" clingo_condition_literal ")" : term
elab_rules : term
| `(term| clingo_condition_literal!($s:clingo_condition_literal)) => do
    Term.elabTerm s none

syntax "clingo_aggregate!" "(" clingo_aggregate ")" : term
elab_rules : term
| `(term| clingo_aggregate!($s:clingo_aggregate)) => do
    Term.elabTerm s none

syntax "clingo_aggregate_head!" "(" clingo_aggregate_head ")" : term
elab_rules : term
| `(term| clingo_aggregate_head!($s:clingo_aggregate_head)) => do
    Term.elabTerm s none

syntax "clingo_aggregate_body!" "(" clingo_aggregate_body ")" : term
elab_rules : term
| `(term| clingo_aggregate_body!($s:clingo_aggregate_body)) => do
    Term.elabTerm s none

syntax "clingo_statement!" "(" clingo_statement ")" : term
elab_rules : term
| `(term| clingo_statement!($s:clingo_statement)) => do
    Term.elabTerm s none


def z := clingo_literal!(f(a) $< f(b))
-- #print z

def z' := clingo_condition_literal!(f(a) $< f(b))
-- #print z'

def z'' := clingo_aggregate!({})
-- #print z''


def z''' := clingo_aggregate!({f : x, y, z} <= 3)
-- #print z'''


def z'''' := clingo_aggregate_head!(2 = sum{f : x} <= 3)
-- #print z''''
def z''''' := clingo_aggregate_body!(2 = sum{f : x} <= 3)
-- #print z'''''


def z'''''' := clingo_statement!(f(x) .)
-- #print z''''''


def fAB := clingo_term!(f(a,b))

def z2 := clingo_term!(f(A,~g(a), |x| + (z * (2 + 1) * @g(A) * -A)))
-- #print z2


def c := clingo_comparison!(1 < 2)
-- #print c

def e := clingo_csp_term!($ x $- z $+ 2 $- 3 $+ y)
-- #print e

def f := clingo_csp_literal!($ x $- z $+ 2 $- 3 $+ y $< 3 $- z $< 10 $= 20)
-- #print f

syntax "clingo!" "(" clingo_symbol ")" : term
macro_rules
| `(term| clingo!($s:clingo_symbol)) => do
    let res <- expandMacros s
    let res := TSyntax.mk res
    `(term| Symbol.mk $res:term)

def x loc := Clingo.Ast.Term.mk loc (Clingo.Ast.Term.Data.Symbol Clingo.Symbol.mk_infimum)
#print x

end Clingo.Lang
