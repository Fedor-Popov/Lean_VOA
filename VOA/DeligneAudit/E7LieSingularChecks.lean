/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieForm

/-!
# Kernel checks for the `E₇` singular vector (light imports)

The unchanged integer `J(1)`, `J(2)` coefficients `oneZ`, `twoZ` of the
highest-weight vector vanish.
-/

namespace VOA.DeligneAudit.E7Lie

/-- First factors of the highest-weight vector. -/
def ta : Fin 5 → Fin 133 := ![52, 56, 59, 62, 64]
/-- Second factors. -/
def tb : Fin 5 → Fin 133 := ![69, 68, 67, 66, 65]
/-- Coefficients (relation `0`). -/
def cz : Fin 5 → ℤ := ![-1, -1, -1, 1, -1]

theorem sum_sZ_mul (c e : Fin 133) (F : Fin 133 → ℤ) :
    ∑ d, sZ c e d * F d = ((sL c e).map fun t => t.2 * F t.1).sum := by
  unfold sZ
  induction sL c e with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The integer `J(1)` coefficients (`k = -4`). -/
def oneZ (c e : Fin 133) : ℤ :=
  ∑ i, cz i * (-4 * Gz c (tb i) * (if ta i = e then 1 else 0) +
    -4 * Gz c (ta i) * (if tb i = e then 1 else 0) +
    ((sL c (ta i)).map fun t => t.2 * sZ t.1 (tb i) e).sum)

/-- The integer `J(2)` coefficients. -/
def twoZ (c : Fin 133) : ℤ :=
  ∑ i, cz i * ((sL c (ta i)).map fun t => t.2 * (-4 * Gz t.1 (tb i))).sum

theorem oneZ_ok0 : ∀ c : Fin 133, 0 ≤ c.val → c.val < 19 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok1 : ∀ c : Fin 133, 19 ≤ c.val → c.val < 38 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok2 : ∀ c : Fin 133, 38 ≤ c.val → c.val < 57 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok3 : ∀ c : Fin 133, 57 ≤ c.val → c.val < 76 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok4 : ∀ c : Fin 133, 76 ≤ c.val → c.val < 95 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok5 : ∀ c : Fin 133, 95 ≤ c.val → c.val < 114 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok6 : ∀ c : Fin 133, 114 ≤ c.val → c.val < 133 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem twoZ_ok : ∀ c, twoZ c = 0 := by decide +kernel

theorem oneZ_eq (c e : Fin 133) : oneZ c e = 0 := by
  have hc := c.isLt
  by_cases h0 : c.val < 19; · exact oneZ_ok0 c (by omega) h0 e
  by_cases h1 : c.val < 38; · exact oneZ_ok1 c (by omega) h1 e
  by_cases h2 : c.val < 57; · exact oneZ_ok2 c (by omega) h2 e
  by_cases h3 : c.val < 76; · exact oneZ_ok3 c (by omega) h3 e
  by_cases h4 : c.val < 95; · exact oneZ_ok4 c (by omega) h4 e
  by_cases h5 : c.val < 114; · exact oneZ_ok5 c (by omega) h5 e
  exact oneZ_ok6 c (by omega) (by omega) e

end VOA.DeligneAudit.E7Lie
