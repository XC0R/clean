import Clean.Circuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Gadgets.Equality
import Clean.Gadgets.Boolean

namespace Circomlib
open Circuit
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/mux2.circom
-/

namespace MultiMux2

structure Inputs (n : ℕ) (F : Type) where
  c : ProvableVector (fields 4) n F  -- n vectors of 4 constants each
  s : Vector F 2                      -- 2-bit selector
deriving ProvableStruct

@[simp, circuit_norm] lemma Inputs.fromComponents_reduce {n : ℕ} {F : Type}
    (c : ProvableVector (fields 4) n F) (s : Vector F 2) :
    @fromComponents (Inputs n) _ F (.cons c (.cons s .nil)) = ⟨c, s⟩ := rfl

/-
template MultiMux2(n) {
    signal input c[n][4];  // Constants
    signal input s[2];   // Selector
    signal output out[n];

    signal a10[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    signal  s10;
    s10 <== s[1] * s[0];

    for (var i=0; i<n; i++) {
          a10[i] <==  ( c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s10;
           a1[i] <==  ( c[i][ 2]-c[i][ 0] ) * s[1];
           a0[i] <==  ( c[i][ 1]-c[i][ 0] ) * s[0];
            a[i] <==  ( c[i][ 0] );

          out[i] <==  (  a10[i] +  a1[i] +  a0[i] +  a[i] );
    }
}
-/
def main (n : ℕ) (input : Var (Inputs n) (F p)) := do
  let { c, s } := input

  let s10 <== s[1] * s[0]

  -- Witness and constrain output vector
  let out <== c.map fun ci =>
    let a10 := (ci[3] - ci[2] - ci[1] + ci[0]) * s10
    let a1 := (ci[2] - ci[0]) * s[1]
    let a0 := (ci[1] - ci[0]) * s[0]
    let a := ci[0]
    a10 + a1 + a0 + a

  return out

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n + 1
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    omega

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1]

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      let s0 := (if s[0] = 0 then 0 else 1)
      let s1 := (if s[1] = 0 then 0 else 1)
      let idx := 2 * s1 + s0
      have : idx < 4 := by
        simp only [idx, s0, s1]
        split <;> split <;> decide
      output[i] = (c[i])[idx]

  soundness := by
    simp only [circuit_norm, main]
    intro offset env input_var input h_input h_assumptions h_output
    obtain ⟨h_s10, h_out_vec⟩ := h_output
    -- We need to show the spec holds for all i < n
    intro i hi
    -- The output at position i is computed from the multilinear interpolation formula
    -- We need to show this equals c[i][idx] where idx is determined by the selector bits

    -- Get the i-th element equality from h_output
    have h_output_i := congrArg (fun v => v[i]) h_out_vec
    simp only [Vector.getElem_map] at h_output_i
    simp only [Vector.getElem_mapRange] at h_output_i
    simp only [circuit_norm] at h_output_i
    simp only [h_output_i]

    rw [← h_input] at h_assumptions ⊢
    simp only [Inputs.fromComponents_reduce] at h_assumptions ⊢
    obtain ⟨h_s0, h_s1⟩ := h_assumptions

    simp only [Vector.getElem_map] at h_s0 h_s1
    cases h_s0 <;> cases h_s1 <;>
      (rename_i h_s0 h_s1
       simp only [h_s0, h_s1, h_s10, ← getElem_eval_vector, ← ProvableType.getElem_eval_fields,
         Vector.getElem_map, show (0 : F p) ≠ 1 from by norm_num,
         show (1 : F p) ≠ 0 from by norm_num, ite_true, ite_false, if_pos, if_neg]
       ring)

  completeness := by
    circuit_proof_start
    obtain ⟨_, h_env⟩ := h_env
    constructor
    · assumption
    · ext i hi
      simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval, circuit_norm]
      have h_env_i := h_env ⟨i, hi⟩
      simp only [toElements, Vector.getElem_map, Function.comp] at h_env_i
      rw [h_env_i]
      simp only [Expression.eval]
      ring

end MultiMux2

namespace Mux2

structure Inputs (F : Type) where
  c : Vector F 4  -- 4 constants
  s : Vector F 2  -- 2-bit selector
deriving ProvableStruct

@[simp, circuit_norm] lemma Inputs.fromComponents_reduce {F : Type} (c : Vector F 4) (s : Vector F 2) :
    @fromComponents Inputs _ F (.cons c (.cons s .nil)) = ⟨c, s⟩ := rfl

/-
template Mux2() {
    var i;
    signal input c[4];  // Constants
    signal input s[2];   // Selector
    signal output out;

    component mux = MultiMux2(1);

    for (i=0; i<4; i++) {
        mux.c[0][i] <== c[i];
    }

    for (i=0; i<2; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out[0] ==> out;
}
-/
def main (input : Var Inputs (F p)) := do
  let { c, s } := input

  -- Call MultiMux2 with n=1
  let mux_out ← MultiMux2.circuit 1 { c := #v[c], s }
  return mux_out[0]

def circuit : FormalCircuit (F p) Inputs field where
  main := main

  localLength _ := 2
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    rfl

  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s[0] ∧ IsBool s[1]

  Spec input output :=
    let ⟨c, s⟩ := input
    let s0 := (if s[0] = 0 then 0 else 1)
    let s1 := (if s[1] = 0 then 0 else 1)
    let idx := 2 * s1 + s0
    have : idx < 4 := by
      simp only [idx, s0, s1]
      split <;> split <;> decide
    output = c[idx]

  soundness := by
    simp only [circuit_norm, main]
    intro _ _ _ input h_input h_assumptions h_subcircuit_sound
    rw [← h_input] at *; clear input h_input
    simp only [MultiMux2.circuit, circuit_norm, Inputs.fromComponents_reduce,
      MultiMux2.Inputs.fromComponents_reduce] at h_subcircuit_sound h_assumptions ⊢
    specialize h_subcircuit_sound h_assumptions 0 (by omega)
    rw [h_subcircuit_sound]
    simp only [eval_vector, Vector.getElem_map, circuit_norm]

  completeness := by
    simp only [circuit_norm, main]
    intro offset env input_var h_env input h_input h_s
    simp only [MultiMux2.circuit, circuit_norm, Inputs.fromComponents_reduce,
      MultiMux2.Inputs.fromComponents_reduce]
    rw [← h_input] at h_s
    simp only [Inputs.fromComponents_reduce, Vector.getElem_map] at h_s
    exact h_s

end Mux2

end Circomlib
