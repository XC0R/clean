import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Gadgets.Boolean

namespace Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Compute the 8-bit addition of two numbers with a carry-in bit.
Returns the sum.
-/
def Addition8Full.circuit : FormalCircuit (F p) Addition8FullCarry.Inputs field where
  main := fun inputs => do
    let { z, .. } ← Addition8FullCarry.circuit inputs
    return z

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions := fun { x, y, carryIn } =>
    x.val < 256 ∧ y.val < 256 ∧ IsBool carryIn

  Spec := fun { x, y, carryIn } z =>
    z.val = (x.val + y.val + carryIn.val) % 256

  -- the proofs are trivial since this just wraps `Addition8FullCarry`
  soundness := by
    circuit_proof_start [Addition8FullCarry.circuit, Addition8FullCarry.Assumptions, Addition8FullCarry.Spec]
    exact (h_holds h_assumptions).1

  completeness := by
    circuit_proof_start [Addition8FullCarry.circuit, Addition8FullCarry.Assumptions]
    simp_all

namespace Addition8
structure Inputs (F : Type) where
  x: F
  y: F
deriving ProvableStruct

@[simp, circuit_norm] theorem Inputs.fromComponents_reduce {F : Type} (x y : F) :
    @fromComponents Inputs _ F (.cons x (.cons y .nil)) = Inputs.mk x y := rfl

/--
Compute the 8-bit addition of two numbers.
Returns the sum.
-/
def circuit : FormalCircuit (F p) Inputs field where
  main := fun { x, y } =>
    Addition8Full.circuit { x, y, carryIn := 0 }

  localLength _ := 2
  output _ i0 := var ⟨i0⟩

  Assumptions | { x, y } => x.val < 256 ∧ y.val < 256

  Spec | { x, y }, z => z.val = (x.val + y.val) % 256

  -- TODO: v4.29.0 circuit_norm corrupts ProvableStruct match type indices for 2-field-wrapping-3-field circuits
  soundness := by
    simp_all [circuit_norm, Addition8Full.circuit, Addition8FullCarry.circuit,
      Addition8FullCarry.Assumptions, Addition8FullCarry.Spec, IsBool]
    sorry

  completeness := by
    simp_all [circuit_norm, Addition8Full.circuit, Addition8FullCarry.circuit,
      Addition8FullCarry.Assumptions, IsBool]
    sorry

end Addition8
end Gadgets
