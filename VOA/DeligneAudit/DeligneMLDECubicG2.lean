/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDECubic
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters

/-!
# `l2` of the `G2Level3Core` from the heat equation at a cube root of unity

Given the Lambert form of the `A₂` theta series, `θ_{A₂} = 1 + 6 L₀` (`L₀ = ∑χ₋₃(k)q^{dk}`),
`level3_sq` gives `l2 : 2a² = 3E₂(q³) - E₂(q)`.
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat VOA.DeligneAudit.DeligneMLDE.HeatK

theorem E2q_eq_P1 : E2q = 1 - 24 * P1 := by
  rw [E2q, eisQ_eq 2 (-24) P1 coeff_P1, map_neg, map_ofNat]; ring

/-- **`l2` from the Lambert form of `θ_{A₂}`.** -/
theorem l2_of_lambert (hA : AQ = 1 + 6 * L0) : 2 * AQ ^ 2 = 3 * E2q3 - E2q := by
  have h3 : E2q3 = 1 - 24 * ex3 P1 := by
    rw [E2q3, E2q_eq_P1, map_sub, map_one, map_mul, map_ofNat]
  rw [hA, h3, E2q_eq_P1]
  linear_combination 2 * level3_sq

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.l2_of_lambert
end AxiomAudit
