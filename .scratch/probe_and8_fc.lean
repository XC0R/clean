import Clean.Gadgets.And.And8

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- Check ProvableStruct components
#check @ProvableStruct.components Gadgets.And.And8.Inputs

-- Check if fromComponents_reduce fires within simp only [circuit_norm]
set_option trace.Meta.Tactic.simp.rewrite true in
example (x y : F p) :
    @fromComponents (Gadgets.And.And8.Inputs) _ (F p) (.cons x (.cons y .nil)) =
    Gadgets.And.And8.Inputs.mk x y := by
  simp only [circuit_norm]
  rfl
