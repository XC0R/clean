import Clean.Utils.Field
import Clean.Utils.Primes

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- Probe 1: What does the goal look like after simp?
example (x : ℕ) : ZMod.val (n:=p) (x % 256 : ℕ) < 256 := by
  have : x % 256 < 256 := Nat.mod_lt _ (by norm_num)
  -- Try erw
  erw [FieldUtils.val_lt_p (x % 256)]
  · assumption
  · linarith [p_large_enough.elim]

-- Probe 2: fromByte_value pattern
example (x : Fin 256) : ZMod.val (n:=p) (↑x : ℕ) = ↑x := by
  erw [FieldUtils.val_lt_p (↑x)]
  linarith [x.is_lt, p_large_enough.elim]

-- Probe 3: fromByte_normalized rewrite pattern
example (x : Fin 256) : ZMod.val (n:=p) (↑x : ℕ) < 256 := by
  erw [FieldUtils.val_lt_p (↑x)]
  · exact x.is_lt
  · linarith [x.is_lt, p_large_enough.elim]

-- Probe 4: The eval_of_literal struct equality
-- Testing if rfl closes a struct eq goal
example (a b c d : F p) :
    ({ x0 := a, x1 := b, x2 := c, x3 := d } : { x0 : F p // True } × { x1 : F p // True } × { x2 : F p // True } × { x3 : F p // True }) =
    { x0 := a, x1 := b, x2 := c, x3 := d } := by rfl

end
