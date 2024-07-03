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


declare_syntax_cat clingo_comparison
syntax clingo_term " < " clingo_term : clingo_comparison
syntax clingo_term " > " clingo_term : clingo_comparison
syntax clingo_term " <= " clingo_term : clingo_comparison
syntax clingo_term " >= " clingo_term : clingo_comparison
syntax clingo_term " = " clingo_term : clingo_comparison
syntax clingo_term " != " clingo_term : clingo_comparison

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

declare_syntax_cat clingo_literal
syntax "true" : clingo_literal
syntax "false" : clingo_literal
syntax clingo_term : clingo_literal
syntax clingo_comparison : clingo_literal
syntax clingo_csp_literal : clingo_literal

def mkLocation (s : Syntax) : TermElabM Expr := do
        let filename := Syntax.mkStrLit (<- getFileName)
        let fileMap <- getFileMap
        let info := SourceInfo.fromRef s
        let pos := info.getPos?.getD 0
        let endPos := info.getPos?.getD pos
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


def elabTermEnsureTerm (t: Syntax) : TermElabM Expr := do
   let expr <- Term.elabTerm t none
   let ty <- inferType expr
   if <- isDefEq ty (mkConst `Clingo.Symbol.Repr)
   then mkTerm t (mkApp (mkConst `Clingo.Ast.Term.Data.Symbol) (<- mkSymbol expr))
   else return expr

def elabEnsureCSPSumTerm (t: Syntax) : TermElabM Expr := do
    Term.elabTerm t (mkConst `Clingo.Ast.CSPSumTerm)


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


def fAB := clingo_term!(f(a,b))

def z := clingo_term!(f(A,~g(a), |x| + (z * (2 + 1) * @g(A) * -A)))
#print z


def c := clingo_comparison!(1 < 2)
#print c

def e := clingo_csp_term!($ x $- z $+ 2 $- 3 $+ y)
#print e

def f := clingo_csp_literal!($ x $- z $+ 2 $- 3 $+ y $< 3 $- z $< 10 $= 20)
#print f

syntax "clingo!" "(" clingo_symbol ")" : term
macro_rules
| `(term| clingo!($s:clingo_symbol)) => do
    let res <- expandMacros s
    let res := TSyntax.mk res
    `(term| Symbol.mk $res:term)

end Clingo.Lang
