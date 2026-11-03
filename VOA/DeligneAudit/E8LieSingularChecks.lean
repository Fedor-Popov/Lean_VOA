/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieForm

/-!
# Kernel checks for the `E₈` singular vector (light imports)

The integer `J(1)`, `J(2)` coefficients `oneZ`, `twoZ` of the highest-weight vector vanish.
-/

namespace VOA.DeligneAudit.E8Lie

/-- First factors of the highest-weight vector. -/
def ta : Fin 7 → Fin 248 := ![107, 110, 113, 115, 117, 119, 120]
/-- Second factors. -/
def tb : Fin 7 → Fin 248 := ![127, 126, 125, 124, 123, 122, 121]
/-- Coefficients (relation `0`). -/
def cz : Fin 7 → ℤ := ![-1, -1, -1, -1, -1, -1, 1]

theorem sum_sZ_mul (c e : Fin 248) (F : Fin 248 → ℤ) :
    ∑ d, sZ c e d * F d = ((sL c e).map fun t => t.2 * F t.1).sum := by
  unfold sZ
  induction sL c e with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The integer `J(1)` coefficients (`k = -6`). -/
def oneZ (c e : Fin 248) : ℤ :=
  ∑ i, cz i * (-6 * Gz c (tb i) * (if ta i = e then 1 else 0) +
    -6 * Gz c (ta i) * (if tb i = e then 1 else 0) +
    ((sL c (ta i)).map fun t => t.2 * sZ t.1 (tb i) e).sum)

/-- The integer `J(2)` coefficients. -/
def twoZ (c : Fin 248) : ℤ :=
  ∑ i, cz i * ((sL c (ta i)).map fun t => t.2 * (-6 * Gz t.1 (tb i))).sum

theorem oneZ_ok0 : ∀ c : Fin 248, 0 ≤ c.val → c.val < 19 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok1 : ∀ c : Fin 248, 19 ≤ c.val → c.val < 38 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok2 : ∀ c : Fin 248, 38 ≤ c.val → c.val < 57 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok3 : ∀ c : Fin 248, 57 ≤ c.val → c.val < 76 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok4 : ∀ c : Fin 248, 76 ≤ c.val → c.val < 95 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok5 : ∀ c : Fin 248, 95 ≤ c.val → c.val < 114 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok6 : ∀ c : Fin 248, 114 ≤ c.val → c.val < 133 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok7 : ∀ c : Fin 248, 133 ≤ c.val → c.val < 152 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok8 : ∀ c : Fin 248, 152 ≤ c.val → c.val < 171 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok9 : ∀ c : Fin 248, 171 ≤ c.val → c.val < 190 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok10 : ∀ c : Fin 248, 190 ≤ c.val → c.val < 209 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok11 : ∀ c : Fin 248, 209 ≤ c.val → c.val < 228 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok12 : ∀ c : Fin 248, 228 ≤ c.val → c.val < 247 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem oneZ_ok13 : ∀ c : Fin 248, 247 ≤ c.val → c.val < 248 → ∀ e, oneZ c e = 0 := by
  decide +kernel

theorem twoZ_ok : ∀ c, twoZ c = 0 := by decide +kernel

theorem oneZ_eq (c e : Fin 248) : oneZ c e = 0 := by
  have hc := c.isLt
  by_cases h0 : c.val < 19; · exact oneZ_ok0 c (by omega) h0 e
  by_cases h1 : c.val < 38; · exact oneZ_ok1 c (by omega) h1 e
  by_cases h2 : c.val < 57; · exact oneZ_ok2 c (by omega) h2 e
  by_cases h3 : c.val < 76; · exact oneZ_ok3 c (by omega) h3 e
  by_cases h4 : c.val < 95; · exact oneZ_ok4 c (by omega) h4 e
  by_cases h5 : c.val < 114; · exact oneZ_ok5 c (by omega) h5 e
  by_cases h6 : c.val < 133; · exact oneZ_ok6 c (by omega) h6 e
  by_cases h7 : c.val < 152; · exact oneZ_ok7 c (by omega) h7 e
  by_cases h8 : c.val < 171; · exact oneZ_ok8 c (by omega) h8 e
  by_cases h9 : c.val < 190; · exact oneZ_ok9 c (by omega) h9 e
  by_cases h10 : c.val < 209; · exact oneZ_ok10 c (by omega) h10 e
  by_cases h11 : c.val < 228; · exact oneZ_ok11 c (by omega) h11 e
  by_cases h12 : c.val < 247; · exact oneZ_ok12 c (by omega) h12 e
  exact oneZ_ok13 c (by omega) (by omega) e

end VOA.DeligneAudit.E8Lie
