import Mathlib

example (a : Vector Nat 3) (b : Vector Nat 4) : (a ++ b).toArray = a.toArray ++ b.toArray := by
  rw [Vector.toArray_append]

-- Try the actual goal pattern from Table/Theorems
example (a : Array Nat) (b : Array Nat) (c : Array Nat) : a ++ (b ++ c) = (a ++ (b ++ c)) := rfl

-- Vector to Array distribution
example {n m : ℕ} (a : Vector Nat n) (b : Vector Nat m) :
    a.toArray ++ b.toArray = (a ++ b).toArray := by
  rw [Vector.toArray_append]
