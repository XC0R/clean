import Clean.Utils.Tactics
import Clean.Types.U64
import Clean.Gadgets.And.And8

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- And8.Inputs has 2 fields: x y : F
-- The stuck match is: fromComponents (cons a (cons b nil)) for And8.Inputs
-- This is identical to the Or8.Inputs case

-- Can we write a general tactic or use a different strategy?
-- Idea: after circuit_norm decomposes h_holds into subcircuit soundness,
-- each one has: And8.Assumptions (fromComponents (cons ... (cons ... nil))) → ...
-- The fromComponents is defeq to And8.Inputs.mk a b
-- We need to either:
-- 1. Add a @[simp] lemma for fromComponents on And8.Inputs (per-struct)
-- 2. Use replace/change to cast (verbose for 8 subcircuits)
-- 3. Find a way to make simp do iota reduction

-- Approach: use a general tactic that replaces all ProvableTypeList match
-- Actually, let me try: simp with ProvableStruct.toComponents_fromComponents
-- or better: add the fromComponents reduction to circuit_norm

-- First, check if we can add it to the Subcircuit.lean or similar

-- Actually, the cleanest approach: add a @[circuit_norm] lemma in each file
-- For And8.Inputs:
@[simp] theorem And8.Inputs.fromComponents_reduce {F : Type} (x y : F) :
    @fromComponents (Gadgets.And.And8.Inputs) _ F (.cons x (.cons y .nil)) =
    Gadgets.And.And8.Inputs.mk x y := rfl

-- Now test: does this help And64's proof?
-- The key is getting this lemma to fire BEFORE fromComponents is unfolded by circuit_norm

-- The issue: circuit_norm includes fromComponents as a def unfold.
-- simp processes def unfolds AFTER rewrite lemmas.
-- So this @[simp] lemma should fire BEFORE fromComponents is unfolded!
-- (simp tries rewrite lemmas first, then def unfolds)

-- Let me verify this assumption...
#check @And8.Inputs.fromComponents_reduce
