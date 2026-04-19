import Mathlib.Data.List.Sort

-- Probe 1: List.Pairwise for concrete list
def ts_ord (x y : ℕ × ℕ × ℕ × ℕ) := match x, y with
| (t2, _, _, _), (t1, _, _, _) => t1 < t2

-- Can simp prove Pairwise for concrete lists?
example : List.Pairwise ts_ord [(4, 1, 43, 46), (3, 2, 0, 45), (2, 0, 42, 44), (1, 1, 0, 43), (0, 0, 0, 42)] := by
  simp [ts_ord, List.pairwise_cons, List.Pairwise]

-- Probe 2: filter_cons + decide
example (tail : List (ℕ × ℕ × ℕ × ℕ)) (addr _t a _r _w : ℕ) :
    List.filter (fun x => match x with | (_, addr', _, _) => decide (addr' = addr)) ((_t, a, _r, _w) :: tail) =
    if a = addr then
      (_t, a, _r, _w) :: List.filter (fun x => match x with | (_, addr', _, _) => decide (addr' = addr)) tail
    else
      List.filter (fun x => match x with | (_, addr', _, _) => decide (addr' = addr)) tail := by
  simp [List.filter_cons]
