import Lean.Parser
import Lean.Parser.Term
import Lean.Elab.Term
import Clingo.Error
import Clingo.Types
import Clingo.Signature
import Clingo.Symbol
import Clingo.Model
import Clingo.Statistics
import Clingo.SolveHandle
import Clingo.Backend
import Clingo.Ast
import Clingo.Control
import Clingo.Lang

open Lean

namespace Clingo

@[extern "lean_clingo_version"]
opaque version : IO Version

@[extern "lean_clingo_error_code"]
opaque error_code : IO Error

@[extern "lean_clingo_error_message"]
opaque error_message : IO (Option String)

end Clingo
