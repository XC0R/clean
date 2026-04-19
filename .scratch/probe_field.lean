import Mathlib.Algebra.Field.ZMod

example (n n' : ℕ) (p_prime : Fact (Nat.Prime (n' + 1))) (lt : n < n' + 1) :
    (↑n : ZMod (n' + 1)) = ⟨n, lt⟩ := by
  apply Fin.ext
  exact ZMod.val_natCast_of_lt lt
