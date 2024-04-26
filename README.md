# Deriving Such That for Lean

This repository includes an implementation of the program derivation
tactic [deriving such
that](https://coq.inria.fr/doc/V8.18.0/refman/addendum/miscellaneous-extensions.html)
extension from the Rocq proof assistant in Lean.


## Example of use

```lean
derive p such that (k * n) + (k * m) = p as h := by
   instantiate ?p := k * (n + m)
   simp [p, Nat.mul_add]

#eval (p 1 2 3)
-- produces 9
```


Note: vanilla lean doesn't really expect users to use evariables, it
doesn't provide any tactics to instantiate evars, so this library
provides one.
