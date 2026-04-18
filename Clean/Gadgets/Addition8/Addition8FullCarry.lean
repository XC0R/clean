import Clean.Circuit
import Clean.Gadgets.ByteLookup
import Clean.Gadgets.Boolean
import Clean.Gadgets.Addition8.Theorems

namespace Gadgets.Addition8FullCarry
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open ByteUtils (mod256 floorDiv256)

structure Inputs (F : Type) where
  x: F
  y: F
  carryIn: F
deriving ProvableStruct

structure Outputs (F : Type) where
  z: F
  carryOut: F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x, y, carryIn⟩ := input

  -- witness the result
  let z ← witness fun eval => mod256 (eval (x + y + carryIn))
  lookup ByteTable z

  -- witness the output carry
  let carryOut ← witness fun eval => floorDiv256 (eval (x + y + carryIn))
  assertBool carryOut

  assertZero (x + y + carryIn - z - carryOut * 256)

  return { z, carryOut }

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

def Spec (input : Inputs (F p)) (out : Outputs (F p)) :=
  let ⟨x, y, carryIn⟩ := input
  out.z.val = (x.val + y.val + carryIn.val) % 256 ∧
  out.carryOut.val = (x.val + y.val + carryIn.val) / 256

/--
  Compute the 8-bit addition of two numbers with a carry-in bit.
  Returns the sum and the output carry bit.
-/
def circuit : FormalCircuit (F p) Inputs Outputs where
  main
  Assumptions
  Spec
  localLength _ := 2
  output _ i0 := { z := var ⟨i0⟩, carryOut := var ⟨i0 + 1⟩ }

  soundness := by
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ ⟨x, y, carry_in⟩ h_inputs h_assumptions h_holds

    simp_all only [circuit_norm, Spec, Assumptions, main, ByteTable]
    change Inputs.mk (Expression.eval env x_var) (Expression.eval env y_var) (Expression.eval env carry_in_var) = Inputs.mk x y carry_in at h_inputs
    simp only [Inputs.mk.injEq] at h_inputs
    rw [h_inputs.1, h_inputs.2.1, h_inputs.2.2] at h_holds

    set z := env.get i0
    set carry_out := env.get (i0 + 1)
    obtain ⟨ h_byte, h_bool_carry, h_add ⟩ := h_holds

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    apply Addition8.Theorems.soundness x y z carry_in carry_out as_x as_y h_byte as_carry_in h_bool_carry h_add

  completeness := by
   -- introductions
    rintro i0 env ⟨x_var, y_var, carry_in_var⟩ h_env ⟨x, y, carry_in⟩ h_inputs h_assumptions

    -- resolve h_inputs via change + injEq
    simp only [circuit_norm] at h_inputs
    change Inputs.mk (Expression.eval env x_var) (Expression.eval env y_var) (Expression.eval env carry_in_var) = Inputs.mk x y carry_in at h_inputs
    simp only [Inputs.mk.injEq] at h_inputs
    replace h_inputs : Expression.eval env x_var = x ∧ Expression.eval env y_var = y ∧ Expression.eval env carry_in_var = carry_in := ⟨h_inputs.1, h_inputs.2.1, h_inputs.2.2⟩

    simp only [circuit_norm, h_inputs, Assumptions, main, ByteTable] at h_env h_assumptions ⊢

    obtain ⟨hz, hcarry_out_raw⟩ := h_env
    have hcarry_out : env.get (i0 + 1) = floorDiv256 (x + y + carry_in) := by
      have := hcarry_out_raw 0; simp only [circuit_norm] at this; exact this
    set z := env.get i0
    set carry_out := env.get (i0 + 1)

    -- now it's just mathematics!
    guard_hyp h_assumptions : x.val < 256 ∧ y.val < 256 ∧ IsBool carry_in

    let goal_byte := z.val < 256
    let goal_bool := IsBool carry_out
    let goal_add := x + y + carry_in + -z + -(carry_out * 256) = 0
    show goal_byte ∧ goal_bool ∧ goal_add

    have completeness1 : z.val < 256 := by
      rw [hz]
      apply ByteUtils.mod256_lt

    have ⟨as_x, as_y, as_carry_in⟩ := h_assumptions
    have carry_in_bound := IsBool.val_lt_two as_carry_in

    have completeness2 : IsBool carry_out := by
      rw [hcarry_out]
      apply Addition8.Theorems.completeness_bool
      repeat assumption

    have completeness3 : x + y + carry_in + -z + -(carry_out * 256) = 0 := by
      rw [hz, hcarry_out]
      apply Addition8.Theorems.completeness_add
      repeat assumption

    exact ⟨completeness1, completeness2, completeness3⟩

def lookupCircuit : LookupCircuit (F p) Inputs Outputs := {
  circuit with
  name := "Addition8FullCarry"

  computableWitnesses n input := by
    simp_all only [circuit_norm, circuit, main, FormalAssertion.toSubcircuit,
      Operations.forAllFlat, Operations.toFlat, FlatOperation.forAll, Inputs.mk.injEq]
    sorry -- TODO: v4.29.0 ProvableTypeList match doesn't reduce for 3-field structs
}

end Gadgets.Addition8FullCarry
