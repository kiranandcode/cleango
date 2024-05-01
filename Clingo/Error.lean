open Lean

namespace Clingo
inductive Error where | success | runtime | logic | badAlloc | unknown
deriving Repr

end Clingo
