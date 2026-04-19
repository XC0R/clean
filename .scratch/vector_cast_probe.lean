import Clean.Utils.Vector

open Vector in
#check @cast_eq_iff_heq

-- Just try to build the lemma up to the cast_eq_iff_heq step
-- to see what the goal looks like
variable {α : Type} {n : ℕ}

open Vector in
example {motive : {n : ℕ} → Vector α n → Sort u}
  {nil : motive #v[]}
  {push' : ∀ {n : ℕ} (as : Vector α n) (a : α), motive as → motive (as.push a)}
  (xs : Vector α n) (x a : α) :
    inductPush nil push' (listCons x (xs.push a)) =
      push' (listCons x xs) a (inductPush nil push' (listCons x xs)) := by
  conv => lhs; simp only [listCons, inductPush]
  -- What does the goal look like here?
  trace_state
  sorry
