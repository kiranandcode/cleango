import Clingo.Types
import Clingo.Model
import Clingo.Error
open Lean

namespace Clingo

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


end Clingo
