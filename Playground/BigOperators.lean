
import Mathlib

namespace BigOperators
open Std.ExtendedBinder

/-- `∑ S` is notation for `Finset.sum S id`. It is the sum of all elements of `S`. -/
scoped syntax (name := bigsumset) "∑ " extBinder : term
scoped macro_rules (kind := bigsumset)
  | `(∑ $s:ident) => `(Finset.sum $s (fun x => x))

end BigOperators
