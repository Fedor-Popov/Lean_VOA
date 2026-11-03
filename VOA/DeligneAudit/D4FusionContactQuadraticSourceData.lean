import VOA.DeligneAudit.D4FusionContactQuadraticData
import VOA.DeligneAudit.D4FusionContactTable

/-! Exact finite Levi derivations on the symmetric quadratic columns.
These are source-independent integer data; their link to actual current
operators is proved in the companion Source module. -/
namespace VOA.DeligneAudit.D4FusionContact.Quadratic.Source

open scoped BigOperators
set_option linter.style.longLine false

def first (j : Fin 36) : Fin 8 :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 6, 6, 7]).getD j.val 0

def second (j : Fin 36) : Fin 8 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 7, 3, 4, 5, 6, 7, 4, 5, 6, 7, 5, 6, 7, 6, 7, 7]).getD j.val 0

def column (a b : Fin 8) : Fin 36 :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 13, 14, 2, 9, 15, 16, 17, 18, 19, 20, 3, 10, 16, 21, 22, 23, 24, 25, 4, 11, 17, 22, 26, 27, 28, 29, 5, 12, 18, 23, 27, 30, 31, 32, 6, 13, 19, 24, 28, 31, 33, 34, 7, 14, 20, 25, 29, 32, 34, 35]).getD (a.val * 8 + b.val) 0

def target (i : Fin 3) (a : Fin 8) : Fin 8 :=
  (([[1, 0, 4, 5, 0, 0, 7, 0], [2, 4, 0, 6, 0, 7, 0, 0], [3, 5, 6, 0, 7, 0, 0, 0]]).getD i.val []).getD a.val 0

def sign (i : Fin 3) (a : Fin 8) : ℤ :=
  (([[1, 0, -1, -1, 0, 0, -1, 0], [1, -1, 0, -1, 0, -1, 0, 0], [-1, 1, 1, 0, 1, 0, 0, 0]]).getD i.val []).getD a.val 0

def transition (i : Fin 3) (j k : Fin 36) : ℤ :=
  (if k = column (target i (first j)) (second j) then sign i (first j) else 0) +
  (if k = column (first j) (target i (second j)) then sign i (second j) else 0)

def derive (i : Fin 3) (c : Fin 36 → ℤ) (k : Fin 36) : ℤ :=
  ∑ j : Fin 36, c j * transition i j k

def previous (r : Fin 27) : Fin 27 :=
  ([0, 0, 1, 0, 3, 4, 3, 6, 7, 0, 9, 10, 9, 12, 13, 12, 15, 16, 9, 18, 19, 18, 21, 22, 21, 24, 25]).getD r.val 0

def direction (r : Fin 27) : Fin 3 :=
  ([0, 2, 2, 1, 2, 2, 1, 2, 2, 0, 2, 2, 1, 2, 2, 1, 2, 2, 0, 2, 2, 1, 2, 2, 1, 2, 2]).getD r.val 0

theorem pair_indices : ∀ j : Fin 36,
    pair j = (radIndex (first j).castSucc, radIndex (second j).castSucc) := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic.Source
