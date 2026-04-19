import Clean.Utils.Field
import Clean.Utils.Primes

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- Probe: can omega handle n % 256 % p < 256 when p > 512?
example (n : ℕ) (hp : p > 512) : n % 256 % p < 256 := by
  rw [Nat.mod_eq_of_lt (by omega : n % 256 < p)]
  omega

-- Probe: Fin coercion
example (x : Fin 256) : (↑x : ℕ) % p = ↑x := by
  exact Nat.mod_eq_of_lt (by linarith [x.is_lt, p_large_enough.elim])

-- Probe: Fin coercion normalized
example (x : Fin 256) : (↑x : ℕ) % p < 256 := by
  rw [Nat.mod_eq_of_lt (by linarith [x.is_lt, p_large_enough.elim])]
  exact x.is_lt

end
