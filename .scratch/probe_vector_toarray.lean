import Mathlib

-- What's the name for (a ++ b).toArray = a.toArray ++ b.toArray?
example (a : Vector Nat 3) (b : Vector Nat 4) : (a ++ b).toArray = a.toArray ++ b.toArray := by
  exact?
