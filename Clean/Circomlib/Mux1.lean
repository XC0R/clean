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
https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom
-/

namespace MultiMux1

structure Inputs (n : ℕ) (F : Type) where
  c : ProvableVector fieldPair n F  -- n pairs of constants
  s : F                              -- selector
deriving ProvableStruct

@[simp, circuit_norm] lemma Inputs.fromComponents_reduce {n : ℕ} {F : Type}
    (c : ProvableVector fieldPair n F) (s : F) :
    @fromComponents (Inputs n) _ F (.cons c (.cons s .nil)) = ⟨c, s⟩ := rfl
/-
template MultiMux1(n) {
    signal input c[n][2]; // Constants
    signal input s; // Selector
    signal output out[n];

    for (var i=0; i < n; i++) {
        out[i] <== (c[i][1] - c[i][0])*s + c[i][0];
    }
}
-/
def main (n : ℕ) (input : Var (Inputs n) (F p)) := do
  let { c, s } := input

  -- Witness and constrain output vector
  let out <== c.map fun (c0, c1) =>
    (c1 - c0) * s + c0
  return out

lemma Vector.mapRange_one {α : Type} (f : ℕ → α) :
  Vector.mapRange 1 f = #v[f 0] := by
    rfl

-- Helper lemmas for vector operations (to be proved later)
lemma Vector.getElem_flatten_singleton {α : Type} {n : ℕ} (v : Vector (Vector α 1) n) (i : ℕ) (hi : i < n) :
    v.flatten[i] = (v[i])[0] := by
  simp only [Vector.getElem_flatten, Nat.div_one]
  congr
  omega

lemma Vector.getElem_map_singleton_flatten {α β : Type} {n : ℕ} (v : Vector α n) (f : α → β) (i : ℕ) (hi : i < n) :
    (v.map (fun x => #v[f x])).flatten[i] = f (v[i]) := by
  rw [Vector.getElem_flatten_singleton (v.map (fun x => #v[f x])) i hi]
  simp only [Vector.getElem_map (fun x => #v[f x]) hi]
  rfl

@[simp, circuit_norm] lemma eval_fieldPair {F : Type} [Field F] (env : Environment F) (a b : Expression F) :
    ProvableType.eval env (α := fieldPair) (a, b) = (Expression.eval env a, Expression.eval env b) := by
  ext <;> simp [ProvableType.eval, toVars, toElements, fromElements, Vector.map, Vector.toArray]

def circuit (n : ℕ) : FormalCircuit (F p) (Inputs n) (fields n) where
  main := main n

  localLength _ := n

  Assumptions input :=
    let ⟨c, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    ∀ i (_ : i < n),
      output[i] = if s = 0 then (c[i]).1 else (c[i]).2

  soundness := by
    simp only [circuit_norm, main]
    intro offset env input_var input h_input h_assumptions h_output i hi
    -- The output at position i is (c[i][1] - c[i][0]) * s + c[i][0]
    -- We need to show this equals if s = 0 then c[i][0] else c[i][1]

    -- h_output gives us the equality of evaluated vectors

    -- Get the i-th element equality from h_output
    -- h_output gives us equality of vectors, extract element i
    have h_output_i := congrArg (fun v => v[i]) h_output
    -- Simplify the outer Vector.map on both sides
    simp only [Vector.getElem_map] at h_output_i
    -- Now we need to show that (Vector.mapRange n fun i => var { index := offset + i })[i] = var { index := offset + i }
    simp only [Vector.getElem_mapRange] at h_output_i

    simp only [circuit_norm] at h_output_i
    simp only [h_output_i]

    -- Fix stuck fromComponents match via definitional equality
    change Inputs.mk (eval env input_var.c) (Expression.eval env input_var.s) = input at h_input
    rw [← h_input] at h_assumptions ⊢
    simp only [eval_vector, Vector.getElem_map] at h_assumptions ⊢
    have eval_c (j : ℕ) (hj : j < n) :
        ProvableType.eval (α := fieldPair) env input_var.c[j] =
          (Expression.eval env input_var.c[j].1, Expression.eval env input_var.c[j].2) := by
      rw [← Prod.eta (input_var.c[j])]; exact eval_fieldPair env _ _
    cases h_assumptions with
      | inl h0 =>
        rw [h0]; simp [eval_c i hi]
      | inr h1 =>
        rw [h1]; simp [eval_c i hi]

  completeness := by
    circuit_proof_start
    ext i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval, circuit_norm]
    have h_env_i := h_env ⟨i, hi⟩
    simp only [toElements, Vector.getElem_map] at h_env_i
    rw [h_env_i]
    simp only [Expression.eval]
    ring

end MultiMux1

namespace Mux1

structure Inputs (F : Type) where
  c : Vector F 2  -- 2 constants
  s : F           -- selector
deriving ProvableStruct

@[simp, circuit_norm] lemma Inputs.fromComponents_reduce {F : Type} (c : Vector F 2) (s : F) :
    @fromComponents Inputs _ F (.cons c (.cons s .nil)) = ⟨c, s⟩ := rfl

/-
template Mux1() {
    var i;
    signal input c[2]; // Constants
    signal input s; // Selector
    signal output out;

    component mux = MultiMux1(1);

    for (i=0; i<2; i++) {
        mux.c[0][i] <== c[i];
    }

    s ==> mux.s;

    mux.out[0] ==> out;
}
-/
def main (input : Var Inputs (F p)) := do
  let { c, s } := input

  -- Call MultiMux1 with n=1
  let mux_out ← MultiMux1.circuit 1 { c := #v[(c[0], c[1])], s }
  return mux_out[0]

def circuit : FormalCircuit (F p) Inputs field where
  main := main

  localLength _ := 1
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
    -- The goal is about MultiMux1.circuit's localLength with n=1
    -- which is defined as n = 1
    rfl
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]

  Assumptions input :=
    let ⟨_, s⟩ := input
    IsBool s

  Spec input output :=
    let ⟨c, s⟩ := input
    output = if s = 0 then c[0] else c[1]

  soundness := by
    simp only [circuit_norm, main]
    intro _ env input_var input h_input h_assumptions h_subcircuit_sound
    change Inputs.mk (Vector.map (Expression.eval env) input_var.c) (Expression.eval env input_var.s) = input at h_input
    subst h_input
    simp only [MultiMux1.circuit, circuit_norm, eval_vector] at h_subcircuit_sound h_assumptions ⊢
    change IsBool (Expression.eval env input_var.s) at h_assumptions
    specialize h_subcircuit_sound h_assumptions 0 (by omega)
    change _ = if Expression.eval env input_var.s = 0 then _ else _ at h_subcircuit_sound
    rw [h_subcircuit_sound]
    congr 1
    all_goals (change _ = Expression.eval env _; congr 1)

  completeness := by
    simp only [circuit_norm, main]
    intros offset env input_var h_env input h_input h_s
    change Inputs.mk (Vector.map (Expression.eval env) input_var.c) (Expression.eval env input_var.s) = input at h_input
    subst h_input
    simp only [MultiMux1.circuit, circuit_norm]
    exact h_s

end Mux1

end Circomlib
