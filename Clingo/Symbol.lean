import Clingo.Types
import Lean.Elab.Term

open Lean

namespace Clingo
inductive SymbolType where | Infimum | Number | String | Function | Supremum
deriving Repr, Inhabited

inductive Symbol.Repr where
 | Infimum
 | Number (n : Int)
 | String (s : String)
 | Function (name : String) (args : Array Symbol.Repr) (is_positive : Bool)
 | Supremum
deriving Repr, Inhabited

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

end Symbol
end Clingo
