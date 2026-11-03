/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6CarrierTables
import VOA.AffineGeneral.E6LieDataTab

/-!
# E₆ vacuum relation: Boolean checks

* `e6casRow i`: row `i` of `3 · Σⱼ κ⁻¹ᵢⱼ XᵢXⱼ` (`κ⁻¹ᵢⱼ = coef (e6dl i) j / e6D i`, `e6D i ∣ 3`);
  `e6cas_check`: `3 · casPoly = 2 · Q` as sparse quadratics (so `casPoly = (2/3) Q`).
* `e6hw_bracket_shadow`, `e6hw_form_shadow`: `Σ cₛ [a_s, b_s] = 0` and `Σ cₛ κ(a_s, b_s) = 0` for the
  singular vector `J²⁹J⁴¹ + J³²J⁴⁰ − J³⁵J³⁹ + J³⁷J³⁸`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.AffineGeneral.SCLie VOA.DeligneAudit.E6Sparse

/-- Row `i` of `3 · casPoly` (integer coefficients). -/
def e6casRow (i : Fin 78) : List (ℕ × ℕ × ℤ) :=
  scaleQ (3 / e6D i) ((e6dl i).map fun p => ((i : ℕ), p.1, p.2))

/-- `3 · casPoly` as a sparse quadratic. -/
def e6casList : List (ℕ × ℕ × ℤ) := (List.finRange 78).flatMap e6casRow

theorem e6cas_check : quadZero (e6casList ++ scaleQ (-2) qQ) = true := by decide +kernel

theorem e6D_dvd : (List.finRange 78).all (fun i => decide (e6D i * (3 / e6D i) = 3) &&
    inRange 78 (e6dl i)) = true := by decide +kernel

theorem e6hw_bracket_shadow : (List.range 78).all (fun e =>
    coef (entry e6T 29 41) e + coef (entry e6T 32 40) e - coef (entry e6T 35 39) e
      + coef (entry e6T 37 38) e == 0) = true := by decide +kernel

theorem e6hw_form_shadow : formV e6Gm [(29, 1)] [(41, 1)] + formV e6Gm [(32, 1)] [(40, 1)]
    - formV e6Gm [(35, 1)] [(39, 1)] + formV e6Gm [(37, 1)] [(38, 1)] = 0 := by decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E6
