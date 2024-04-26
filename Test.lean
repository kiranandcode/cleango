import Clingo


def main : IO Unit := do
   println! "hello"
   let res : ClingoVersion := clingoVersion ()
   
   println! "done! ==> {res}"
