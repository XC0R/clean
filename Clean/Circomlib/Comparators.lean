import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify
import Mathlib.Data.Int.Basic
/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/comparators.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace IsZero
/-
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}
-/
def main (input : Expression (F p)) := do
  let inv ← witness fun env =>
    let x := input.eval env
    if x ≠ 0 then x⁻¹ else 0

  let out <== -input * inv + 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 2

  Spec input output :=
    output = (if input = 0 then 1 else 0)

  soundness := by
    intro i₀ env input_var input h_input _ h_holds
    subst h_input
    simp only [circuit_norm, main] at h_holds ⊢
    obtain ⟨h1, h2⟩ := h_holds
    rw [h1]
    by_cases h : Expression.eval env input_var = 0
    · rw [ProvableType.eval_field, h]; simp; exact (if_pos rfl).symm
    · rw [h1] at h2
      have h_result := (mul_eq_zero.mp h2).resolve_left h
      rw [ProvableType.eval_field]
      convert h_result using 1
      exact if_neg h

  completeness := by
    intro i₀ env input_var h_env _ h_input _
    subst h_input
    simp only [circuit_norm, main] at h_env ⊢
    rcases h_env with ⟨left, right⟩
    simp only [left, ne_eq, id_eq, ite_not, mul_ite, mul_zero] at right
    simp only [id_eq, right, left, ne_eq, ite_not, mul_ite, mul_zero, mul_eq_zero, true_and]
    split_ifs with h
    · left; exact h
    · right
      have h_inv := mul_inv_cancel₀ h
      calc -(Expression.eval env input_var * (Expression.eval env input_var)⁻¹) + 1
          = -(1 : F p) + 1 := by rw [h_inv]
        _ = 0 := by ring

end IsZero

namespace IsEqual
/-
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 - input.2
  let out ← IsZero.circuit diff
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 2

  Spec input output :=
    output = (if input.1 = input.2 then 1 else 0)

  completeness := by
    simp only [circuit_norm, main, IsZero.circuit]

  soundness := by
    circuit_proof_start
    rw [← h_input]
    simp only [id_eq]

    have h1 : Expression.eval env input_var.1 = input.1 := by
      rw [← h_input]
    have h2 : Expression.eval env input_var.2 = input.2 := by
      rw [← h_input]

    rw [h1, h2] at h_holds
    simp only [IsZero.circuit] at h_holds ⊢
    replace h_holds := h_holds trivial

    rw [h_holds, h1, h2]

    apply ite_congr
    · sorry -- v4.29.0: field (F p) vs F p typeclass resolution for sub_eq_zero/add_neg_eq_zero
    · intro; rfl
    · intro; rfl

end IsEqual

namespace ForceEqualIfEnabled
/-
template ForceEqualIfEnabled() {
    signal input enabled;
    signal input in[2];

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    (1 - isz.out)*enabled === 0;
}
-/
structure Inputs (F : Type) where
  enabled : F
  inp : fieldPair F
deriving ProvableStruct

def main (inputs : Var Inputs (F p)) := do
  let { enabled, inp } := inputs
  let isz ← IsZero.circuit (inp.2 - inp.1)
  enabled * (1 - isz) === 0

def circuit : FormalAssertion (F p) Inputs where
  main
  localLength _ := 2

  Assumptions := fun { enabled, inp } =>
    enabled = 0 ∨ enabled = 1

  Spec := fun { enabled, inp } =>
    enabled = 1 → inp.1 = inp.2

  soundness := by
    intro i₀ env input_var input h_input h_assumptions h_holds
    subst h_input
    simp only [circuit_norm, main, IsZero.circuit, ProvableType.eval_field] at h_holds ⊢
    intro h_ie
    obtain ⟨h_isz, h_mul⟩ := h_holds
    sorry

  completeness := by
    intro i₀ env input_var h_env input h_input h_assumptions
    subst h_input
    simp only [circuit_norm, main, IsZero.circuit, ProvableType.eval_field] at h_env ⊢
    sorry

end ForceEqualIfEnabled

namespace LessThan
/-
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1 << n) - in[1];

    out <== 1-n2b.out[n];
}
-/
def main (n : ℕ) (hn : 2^(n+1) < p) (input : Expression (F p) × Expression (F p)) := do
  let diff := input.1 + (2^n : F p) - input.2
  let bits ← Num2Bits.circuit (n + 1) hn diff
  let out <== 1 - bits[n]
  return out

def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := main n hn
  localLength _ := n + 2
  localLength_eq := by
    simp only [circuit_norm, main, Num2Bits.circuit, Gadgets.Equality.elaborated]
  output _ i := var ⟨ i + n + 1 ⟩
  output_eq := by simp +arith [circuit_norm, main, Num2Bits.circuit]

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val ≤ 2^n

  Spec := fun (x, y) output =>
    output = (if x.val < y.val then 1 else 0)

  soundness := by
    circuit_proof_start
    sorry
    rcases h_assumptions with ⟨hx, hy⟩
    have hx_eval : Expression.eval env input_var.1 = input.1 := by
      simpa using congrArg Prod.fst h_input
    have hy_eval : Expression.eval env input_var.2 = input.2 := by
      simpa using congrArg Prod.snd h_input

    simp only [hx_eval, hy_eval, id_eq] at h_holds

    set out := env.get (i₀ + n + 1) with hout
    have two_exp_n_small : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by gcongr; repeat linarith
      exact lt_of_le_of_lt this hn

    have heq: ZMod.val ((2 : F p)^n) = 2^n := by
      rw [ZMod.val_pow]
      rw [ZMod.val_ofNat_of_lt]
      · simp_all [Fact.out]
      convert two_exp_n_small
      rw [ZMod.val_ofNat_of_lt]
      simp_all [Fact.out]

    by_cases hlt : ZMod.val input.1 < ZMod.val input.2

    -- CASE input.1 < input.2
    simp only [id_eq, hlt, ↓reduceIte]

    have hdiff_lt : ZMod.val (input.1 + 2^n - input.2) < 2^n := by
      rw [ZMod.val_sub]
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2^n - ZMod.val input.2 <  ZMod.val input.2 + 2^n - ZMod.val input.2 := by omega
            _ = 2^n := by omega
        · have easy_lemma: 2 * 2^n = 2^(n+1) := by
            rw [pow_succ, two_mul]
            omega
          omega
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2^n = 2^(n+1) := by
            rw [pow_succ, two_mul]
            omega
          omega

    -- split h_holds to h1 h2 h3
    have h3 := h_holds.right
    have h2 := h_holds.left.right

    rw [add_assoc] at hout
    rw [← hout] at h3
    rw [h3]
    --simp the goal basic math

    unfold fieldToBits at h2
    unfold toBits at h2
    --now I need to use that On Nat, shift is equivalent to a / 2 ^ b.

    apply congrArg (fun v => v[n]) at h2
    simp only [Vector.getElem_map, Vector.getElem_mapRange,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, circuit_norm] at h2

    simp only [← sub_eq_add_neg, Nat.testBit_eq_false_of_lt hdiff_lt, Bool.false_eq_true,
      ↓reduceIte] at h2
    rw [h2]
    simp only [neg_zero, add_zero]

    -- CASE input.1 >= input.2
    simp only [id_eq, hlt, ↓reduceIte]
    have hdiff_ge : ZMod.val (input.1 + 2^n - input.2) >= 2^n := by
      rw [ZMod.val_sub]
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2^n - ZMod.val input.2 ≥ ZMod.val input.1 + 2^n - ZMod.val input.1 := by omega
            _ = 2^n := by omega
        · have easy_lemma: 2 * 2^n = 2^(n+1) := by
            rw [pow_succ, two_mul]
            omega
          omega
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2^n = 2^(n+1) := by
            rw [pow_succ, two_mul]
            omega
          omega

    -- split h_holds to h1 h2 h3
    have h3 := h_holds.right
    have h2 := h_holds.left.right
    have h1 := h_holds.left.left

    rw [add_assoc] at hout
    rw [← hout] at h3
    rw [h3]
    --simp the goal basic math
    unfold fieldToBits at h2
    unfold toBits at h2
    --now I need to use that On Nat, shift is equivalent to a / 2 ^ b.

    apply congrArg (fun v => v[n]) at h2
    simp only [Vector.getElem_map, Vector.getElem_mapRange,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, circuit_norm] at h2

    have hf: (ZMod.val (input.1 + 2^n + -input.2)).testBit n = true := by
      have hpos : 0 < 2^n := pow_pos (by decide) n
      have hlt2 : (ZMod.val (input.1 + 2^n + -input.2)) / 2^n < 2 := by
        have : (ZMod.val (input.1 + 2^n + -input.2)) < 2^n * 2 := by simpa [pow_succ, two_mul, mul_two] using h1
        exact Nat.div_lt_of_lt_mul this

      have hge1 : 1 ≤ (ZMod.val (input.1 + 2^n + -input.2)) / 2^n :=
        (Nat.le_div_iff_mul_le hpos).mpr (by simpa [one_mul, sub_eq_add_neg] using hdiff_ge)

      have hxdiv : (ZMod.val (input.1 + 2^n + -input.2)) / 2^n = 1 :=
        le_antisymm (Nat.lt_succ_iff.mp hlt2) hge1

      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hxdiv]

    simp only [hf, ↓reduceIte] at h2
    simp only [h2, add_neg_cancel]

  completeness := by
    circuit_proof_start
    simp only [circuit_norm, Num2Bits.circuit] at *
    rcases h_assumptions with ⟨hx, hy⟩
    have hx_eval : Expression.eval env input_var.1 = input.1 := by
      simpa using congrArg Prod.fst h_input
    have hy_eval : Expression.eval env input_var.2 = input.2 := by
      simpa using congrArg Prod.snd h_input
    simp only [hx_eval, hy_eval, Prod.mk.eta, id_eq] at *
    set out := env.get (i₀ + n + 1) with hout
    have two_exp_n_small : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by gcongr; repeat linarith
      exact lt_of_le_of_lt this hn

    have heq: ZMod.val ((2 : F p) ^ n) = 2^n := by
      rw [ZMod.val_pow]
      rw [ZMod.val_ofNat_of_lt]
      · simp_all [Fact.out]
      convert two_exp_n_small
      rw [ZMod.val_ofNat_of_lt]
      simp_all [Fact.out]

    have hdiff_lt_basic : ZMod.val (input.1 + 2^n - input.2) < 2^(n+1) := by
      rw [ZMod.val_sub]
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          calc
            ZMod.val input.1 + 2^n - ZMod.val input.2 <  2^n + 2^n := by omega
            _ = 2^(n + 1) := by rw[pow_succ, mul_two]
        · have easy_lemma: 2 * 2^n = 2^(n + 1) := by
            rw [pow_succ, two_mul]
            omega
          omega
      · rw [ZMod.val_add_of_lt]
        · simp only [heq] at *
          omega
        · have easy_lemma: 2 * 2^n = 2^(n + 1) := by
            rw [pow_succ, two_mul]
            omega
          omega

    have h2 := h_env.right
    refine And.intro ?_ ?_
    · simpa [sub_eq_add_neg] using hdiff_lt_basic
    · exact h2

end LessThan

namespace LessEqThan
/-
template LessEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[0];
    lt.in[1] <== in[1]+1;
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (x, y + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val <= y.val then 1 else 0)

  soundness := by
    intro i env input (x, y) h_input h_assumptions h_holds
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have two_exp_n_lt_p : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by
        simp [pow_succ]
      exact lt_of_le_of_lt this hn

    have hy_p : y.val + 1 < p :=
      lt_of_le_of_lt (Nat.succ_le_of_lt h_assumptions.right) two_exp_n_lt_p

    have hy_val : (y + 1).val = y.val + 1 := by
      have hy_p' : y.val + (1 : F p).val < p := by
        simpa [ZMod.val_one] using hy_p
      simpa [ZMod.val_one] using (ZMod.val_add_of_lt hy_p')

    have hy_le : (y + 1).val ≤ 2^n := by
      rw [hy_val]
      exact Nat.succ_le_of_lt h_assumptions.right

    have h_lt := h_holds hy_le
    simpa [hy_val, Nat.lt_add_one_iff] using h_lt

  completeness := by
    intro i env input h_env (x, y) h_input h_assumptions
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have two_exp_n_lt_p : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by
        simp [pow_succ]
      exact lt_of_le_of_lt this hn

    have hy_p : y.val + 1 < p :=
      lt_of_le_of_lt (Nat.succ_le_of_lt h_assumptions.right) two_exp_n_lt_p

    have hy_val : (y + 1).val = y.val + 1 := by
      have hy_p' : y.val + (1 : F p).val < p := by
        simpa [ZMod.val_one] using hy_p
      simpa [ZMod.val_one] using (ZMod.val_add_of_lt hy_p')

    have hy_le : (y + 1).val ≤ 2^n := by
      rw [hy_val]
      exact Nat.succ_le_of_lt h_assumptions.right

    exact hy_le
end LessEqThan

namespace GreaterThan
/-
template GreaterThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0];
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n

  Spec := fun (x, y) output =>
    output = (if x.val > y.val then 1 else 0)

  soundness := by
    intro i env input (x, y) h_input h_assumptions h_holds
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have hx_le : x.val ≤ 2^n := Nat.le_of_lt h_assumptions.left
    have h_lt := h_holds hx_le
    simpa using h_lt

  completeness := by
    intro i env input h_env (x, y) h_input h_assumptions
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have hx_le : x.val ≤ 2^n := Nat.le_of_lt h_assumptions.left
    exact hx_le
end GreaterThan

namespace GreaterEqThan
/-
template GreaterEqThan(n) {
    signal input in[2];
    signal output out;

    component lt = LessThan(n);

    lt.in[0] <== in[1];
    lt.in[1] <== in[0]+1;
    lt.out ==> out;
}
-/
def circuit (n : ℕ) (hn : 2^(n+1) < p) : FormalCircuit (F p) fieldPair field where
  main := fun (x, y) =>
    LessThan.circuit n hn (y, x + 1)

  localLength _ := n + 2

  Assumptions := fun (x, y) => x.val < 2^n ∧ y.val < 2^n
  Spec := fun (x, y) output =>
    output = (if x.val >= y.val then 1 else 0)

  soundness := by
    intro i env input (x, y) h_input h_assumptions h_holds
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have two_exp_n_lt_p : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by
        simp [pow_succ]
      exact lt_of_le_of_lt this hn

    have hx_p : x.val + 1 < p :=
      lt_of_le_of_lt (Nat.succ_le_of_lt h_assumptions.left) two_exp_n_lt_p

    have hx_val : (x + 1).val = x.val + 1 := by
      have hx_p' : x.val + (1 : F p).val < p := by
        simpa [ZMod.val_one] using hx_p
      simpa [ZMod.val_one] using (ZMod.val_add_of_lt hx_p')

    have hx_le : (x + 1).val ≤ 2^n := by
      rw [hx_val]
      exact Nat.succ_le_of_lt h_assumptions.left

    have h_lt := h_holds hx_le
    simpa [hx_val, Nat.lt_add_one_iff] using h_lt

  completeness := by
    intro i env input h_env (x, y) h_input h_assumptions
    simp_all only [circuit_norm, LessThan.circuit, Prod.mk.injEq]

    have two_exp_n_lt_p : 2^n < p := by
      have : 2^n ≤ 2^(n+1) := by
        simp [pow_succ]
      exact lt_of_le_of_lt this hn

    have hx_p : x.val + 1 < p :=
      lt_of_le_of_lt (Nat.succ_le_of_lt h_assumptions.left) two_exp_n_lt_p

    have hx_val : (x + 1).val = x.val + 1 := by
      have hx_p' : x.val + (1 : F p).val < p := by
        simpa [ZMod.val_one] using hx_p
      simpa [ZMod.val_one] using (ZMod.val_add_of_lt hx_p')

    have hx_le : (x + 1).val ≤ 2^n := by
      rw [hx_val]
      exact Nat.succ_le_of_lt h_assumptions.left

    exact hx_le
end GreaterEqThan

end Circomlib
