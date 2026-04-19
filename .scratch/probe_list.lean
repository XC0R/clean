import Mathlib.Data.List.Basic

-- Test List.count on singleton
example {S : Type*} [DecidableEq S] (a : S × S) : List.count a [a] = 1 := by
  simp [List.count_cons, List.count_nil]

example {S : Type*} [DecidableEq S] (a : S × S) : List.count a [a] = 1 := by
  exact List.count_singleton_self a
