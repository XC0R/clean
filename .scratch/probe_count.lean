import Mathlib.Data.List.Basic

variable {S : Type*} [DecidableEq S]

-- Test: reducing List.count on a concrete 1-element list
example (s : S) (t : S × S) (h_t : t = (s, s)) : List.count t [(s, s)] = 1 := by
  subst h_t; simp

example (s : S) (t : S × S) (h_t : t = (s, s)) : List.count t [(s, s)] ≤ 1 := by
  subst h_t; simp

-- Test: reducing List.count when t ≠ element
example (s : S) (t : S × S) (h_t : t ≠ (s, s)) : List.count t [(s, s)] = 0 := by
  simp [List.count_cons, List.count_nil, h_t]

-- Test: List.count on 2-element list with one match
example (a b : S) (h_ne : a ≠ b) : List.count (a, b) [(a, b), (b, a)] = 1 := by
  simp [List.count_cons, List.count_nil, Prod.mk.injEq, h_ne]
