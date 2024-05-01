import Clingo.Symbol
import Clingo.Ast
import Lean.Elab

open Lean Elab Meta

namespace Clingo.Lang

declare_syntax_cat clingo_symbol

syntax "#inf" : clingo_symbol
syntax "#sup" : clingo_symbol
syntax num : clingo_symbol
syntax "-" num : clingo_symbol
syntax str : clingo_symbol
syntax ident : clingo_symbol
syntax ident  "(" clingo_symbol,+ ")"  : clingo_symbol
syntax "-" ident : clingo_symbol
syntax "-" ident  "(" clingo_symbol,+ ")"  : clingo_symbol

declare_syntax_cat clingo_term
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
-- symbol
syntax (name := clingo_term_symbolic) clingo_symbol : clingo_term


def mkLocation : MacroM (TSyntax `term) := do
        let ctx := (<- read)
        let filename := ctx.mainModule.toString
        let filename := Syntax.mkStrLit filename
        let info := SourceInfo.fromRef ctx.ref
        match info with
        | .none =>
          `(term| Clingo.Location.mk
                       $filename:str $filename:str
                       0 0
                       0 0)
        | .original _ startP _ endP =>
          let startP := Syntax.mkNumLit s!"{startP.byteIdx}"
          let endP := Syntax.mkNumLit s!"{endP.byteIdx}"
          `(term| Clingo.Location.mk
                       $filename:str $filename:str
                       0 0
                       $startP:num $endP:num)
        | .synthetic startP endP _ =>
          let startP := Syntax.mkNumLit s!"{startP.byteIdx}"
          let endP := Syntax.mkNumLit s!"{endP.byteIdx}"
          `(term| Clingo.Location.mk
                       $filename:str $filename:str
                       0 0
                       $startP:num $endP:num)

elab_rules : term
| `(clingo_term| $x:ident) => do
    let xStr := Syntax.mkStrLit x.getId.toString
    if Char.isUpper $ x.getId.toString.get! 0
    then Term.elabTerm (<- `(term| Clingo.Ast.Term.mk default (.Variable $xStr:str))).raw none
    else Term.elabTerm (<- `(term| Clingo.Symbol.Repr.Function $xStr:str #[] true)).raw none
| `(clingo_term| $x:num) => do
    let xStr := Syntax.mkNumLit (reprStr x.getNat)
    Term.elabTerm (<- `(term| Clingo.Symbol.Repr.Number $xStr:num)).raw none
| `(clingo_term| $x:str) => do
    Term.elabTerm (<- `(term| Clingo.Symbol.Repr.String $x:str)).raw none
| `(clingo_term| $f:ident($t:clingo_term,*)) => do
    let f := mkStrLit f.getId.toString
    let ty <- ST.mkRef none
    let t <- ST.run $ t.getElems.mapM (fun stx => do
         let expr <- Term.elabTerm stx none
         let expr_ty <- inferType expr
         match <- ty.get with
         | none =>
            if !expr_ty.isMVar then
               ST.Ref.set ty (some expr_ty)
         | some ty =>
             if !ty.isMVar && ! (<- isDefEq ty expr_ty) then
                throwErrorAt stx "argument to function {stx} had wrong type"
         return expr
    )
    let res_typ <- ST.Ref.get ty
    match res_typ with
    | none => 
        return (mkAppN
              (mkConst `Clingo.Ast.Term.Data.Function)
              (#[f] ++ t))
    | some ty => do
       if <- isDefEq ty (mkConst `Clingo.AST.Term)
       then
         return (mkAppN
              (mkConst `Clingo.Ast.Term.Data.Function)
              (#[f] ++ t))
       else
         return (mkAppN
              (mkConst `Clingo.Symbol.Repr.Function)
              (#[f] ++ t))       
    -- Term.elabTerm (<- `(term| Clingo.Symbol.Repr.Number $xStr:num #[] true)).raw none


syntax "clingo_term!" "(" clingo_term ")" : term
elab_rules : term
| `(term| clingo_term!($s:clingo_term)) => do
    Term.elabTerm s none

def y := clingo_term!(x)


syntax "clingo!" "(" clingo_symbol ")" : term
macro_rules
| `(term| clingo!($s:clingo_symbol)) => do
    let res <- expandMacros s
    let res := TSyntax.mk res
    `(term| Symbol.mk $res:term)

end Clingo.Lang
