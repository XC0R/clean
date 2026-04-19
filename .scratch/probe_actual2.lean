import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

variable {S : Type*} [DecidableEq S]

def countTransitionInPath2 [DecidableEq S] (t : S × S) (path : List S) : ℕ :=
  (path.zip path.tail).count t

example (x y : S) (path : List S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_not_in : (x, y) ∉ path.zip path.tail) :
    countTransitionInPath2 (x, y) (path ++ [y]) = 1 := by
  unfold countTransitionInPath2
  obtain ⟨h, t', rfl⟩ := List.exists_cons_of_ne_nil h_nonempty
  rw [List.cons_append, List.tail_cons]
  induction t' generalizing h with
  | nil =>
    have : x = h := by simpa using h_last.symm
    subst this; simp
  | cons h2 t2 ih =>
    sorry
