import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U32
import Clean.Gadgets.Addition32.Theorems
import Clean.Utils.Primes
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics

namespace Gadgets.Addition32Full
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: U32 F
  y: U32 F
  carryIn: F
deriving ProvableStruct

@[simp, circuit_norm] theorem Inputs.fromComponents_reduce {F : Type} (x y : U32 F) (carryIn : F) :
    @fromComponents Inputs _ F (.cons x (.cons y (.cons carryIn .nil))) = Inputs.mk x y carryIn := rfl

@[simp, circuit_norm] theorem Inputs.fromComponents_x {F : Type} (x y : U32 F) (carryIn : F) :
    (@fromComponents Inputs _ F (.cons x (.cons y (.cons carryIn .nil)))).x = x := rfl

@[simp, circuit_norm] theorem Inputs.fromComponents_y {F : Type} (x y : U32 F) (carryIn : F) :
    (@fromComponents Inputs _ F (.cons x (.cons y (.cons carryIn .nil)))).y = y := rfl

@[simp, circuit_norm] theorem Inputs.fromComponents_carryIn {F : Type} (x y : U32 F) (carryIn : F) :
    (@fromComponents Inputs _ F (.cons x (.cons y (.cons carryIn .nil)))).carryIn = carryIn := rfl

@[simp, circuit_norm] theorem Inputs.eval_reduce {F : Type} [Field F]
    (env : Environment F) (v : Var Inputs F) :
    ProvableStruct.eval env v = Inputs.mk (ProvableType.eval env v.x) (ProvableType.eval env v.y)
      (Expression.eval env v.carryIn) := by
  unfold ProvableStruct.eval instProvableStructInputs
  simp only [ProvableStruct.eval.go, ProvableType.eval]
  split
  rename_i _ x y carryIn heq
  cases heq
  simp [ProvableType.eval, explicit_provable_type, toVars, fromElements, Vector.map]

structure Outputs (F : Type) where
  z: U32 F
  carryOut: F
deriving Repr, ProvableStruct

@[simp, circuit_norm] theorem Outputs.fromComponents_reduce {F : Type} (z : U32 F) (carryOut : F) :
    @fromComponents Outputs _ F (.cons z (.cons carryOut .nil)) = Outputs.mk z carryOut := rfl

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input
  let { z := z0, carryOut := c0 } ← Addition8FullCarry.main ⟨ x.x0, y.x0, carryIn ⟩
  let { z := z1, carryOut := c1 } ← Addition8FullCarry.main ⟨ x.x1, y.x1, c0 ⟩
  let { z := z2, carryOut := c2 } ← Addition8FullCarry.main ⟨ x.x2, y.x2, c1 ⟩
  let { z := z3, carryOut := c3 } ← Addition8FullCarry.main ⟨ x.x3, y.x3, c2 ⟩
  return { z := U32.mk z0 z1 z2 z3, carryOut := c3 }

def Assumptions (input : Inputs (F p)) :=
  input.x.Normalized ∧ input.y.Normalized ∧ IsBool input.carryIn

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  out.z.value = (input.x.value + input.y.value + input.carryIn.val) % 2^32
  ∧ out.carryOut.val = (input.x.value + input.y.value + input.carryIn.val) / 2^32
  ∧ out.z.Normalized ∧ IsBool out.carryOut

/--
Elaborated circuit data can be found as follows:
```
#eval (main (p:=p_babybear) default).localLength
#eval (main (p:=p_babybear) default).output
```
-/
instance elaborated : ElaboratedCircuit (F p) Inputs Outputs where
  main
  localLength _ := 8
  -- unfortunately, `rfl` in default tactic times out here
  localLength_eq _ i0 := by
    simp only [circuit_norm, main, Addition8FullCarry.main]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  subst h_input
  delta elaborated main Assumptions at h_holds h_assumptions
  simp only [circuit_norm, Addition8FullCarry.main, ByteTable, U32.Normalized,
             explicit_provable_type] at h_holds h_assumptions
  simp only [Spec, circuit_norm, explicit_provable_type, U32.Normalized] at ⊢

  obtain ⟨ hz0, hc0, h0, hz1, hc1, h1, hz2, hc2, h2, hz3, hc3, h3 ⟩ := h_holds
  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm

  -- h0..h3 have form: a + b + c + -z + -(carry*256) = 0
  -- add32_soundness needs: a + b + c = carry*256 + z
  -- Convert using: if h : LHS = 0 then LHS + (z + carry*256) = z + carry*256
  -- which ring-simplifies to a + b + c = carry*256 + z
  -- Convert constraint equations from "a+b+c + -z + -(carry*256) = 0" to "a+b+c = carry*256+z"
  -- using abelian group manipulation (ring/linear_combination don't work on ZMod p)
  have convert_eq : ∀ (a b : F p), a + -b = 0 → a = b := by
    intro a b h
    have := congr_arg (· + b) h
    simp [add_assoc, neg_add_cancel, zero_add] at this
    exact this
  have rearrange : ∀ (a b c d e : F p), a + b + c + -d + -(e * 256) = 0 →
      a + b + c = e * 256 + d := by
    intro a b c d e h
    apply convert_eq; have : a + b + c + -(e * 256 + d) = a + b + c + -d + -(e * 256) := by abel
    rw [this]; exact h

  have eq0 := rearrange _ _ _ _ _ h0
  have eq1 := rearrange _ _ _ _ _ h1
  have eq2 := rearrange _ _ _ _ _ h2
  have eq3 := rearrange _ _ _ _ _ h3

  have key := Addition32.Theorems.add32_soundness
    x0_byte x1_byte x2_byte x3_byte
    y0_byte y1_byte y2_byte y3_byte
    hz0 hz1 hz2 hz3
    carry_in_bool hc0 hc1 hc2 hc3
    eq0 eq1 eq2 eq3
  exact ⟨ key.1, key.2, ⟨ hz0, hz1, hz2, hz3 ⟩, hc3 ⟩

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i₀ env input_var h_env input h_input h_assumptions
  subst h_input
  delta elaborated main Assumptions at *
  simp only [circuit_norm, Addition8FullCarry.main, ByteTable, U32.Normalized,
             explicit_provable_type] at *

  -- introduce intermediate variables, like in the circuit
  set z0 := env.get i₀
  set c0 := env.get (i₀ + 1)
  set z1 := env.get (i₀ + 2)
  set c1 := env.get (i₀ + 3)
  set z2 := env.get (i₀ + 4)
  set c2 := env.get (i₀ + 5)
  set z3 := env.get (i₀ + 6)
  set c3 := env.get (i₀ + 7)
  obtain ⟨ hz0, hc0, hz1, hc1, hz2, hc2, hz3, hc3 ⟩ := h_env

  -- the add8 completeness proof, four times
  have add8_completeness {x y c_in z c_out : F p}
    (hz : z = mod256 (x + y + c_in)) (hc_out : c_out = floorDiv256 (x + y + c_in)) :
    x.val < 256 → y.val < 256 → IsBool c_in →
    z.val < 256 ∧ IsBool c_out ∧ x + y + c_in + -z + -(c_out * 256) = 0
  := by
    intro x_byte y_byte hc
    have : z.val < 256 := hz ▸ ByteUtils.mod256_lt (x + y + c_in)
    use this
    have carry_lt_2 : c_in.val < 2 := IsBool.val_lt_two hc
    have : (x + y + c_in).val < 512 :=
      ByteUtils.byte_sum_and_bit_lt_512 x y c_in x_byte y_byte carry_lt_2
    use (hc_out ▸ ByteUtils.floorDiv256_bool this)
    rw [ByteUtils.mod_add_div256 (x + y + c_in), hz, hc_out]
    ring

  have ⟨ x_norm, y_norm, carry_in_bool ⟩ := h_assumptions
  have ⟨ x0_byte, x1_byte, x2_byte, x3_byte ⟩ := x_norm
  have ⟨ y0_byte, y1_byte, y2_byte, y3_byte ⟩ := y_norm
  have ⟨ z0_byte, c0_bool, h0 ⟩ := add8_completeness hz0 hc0 x0_byte y0_byte carry_in_bool
  have ⟨ z1_byte, c1_bool, h1 ⟩ := add8_completeness hz1 hc1 x1_byte y1_byte c0_bool
  have ⟨ z2_byte, c2_bool, h2 ⟩ := add8_completeness hz2 hc2 x2_byte y2_byte c1_bool
  have ⟨ z3_byte, c3_bool, h3 ⟩ := add8_completeness hz3 hc3 x3_byte y3_byte c2_bool

  exact ⟨ z0_byte, c0_bool, h0, z1_byte, c1_bool, h1, z2_byte, c2_bool, h2, z3_byte, c3_bool, h3 ⟩

def circuit : FormalCircuit (F p) Inputs Outputs where
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Addition32Full
