/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SimpleVnat
import VOA.Moonshine.M8h0Gap

/-!
# The Moonshine module `V♮`: the assembled statement  (step M9, conditional form)

This file collects every target of the construction into one theorem about the
FLM construction `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+`:

* a `VertexOperatorAlgebra` structure on `Vnat` whose vertex map is the genuine block map
  (untwisted fields, the skew intertwiner `W` and its nondegenerate adjoint `W̄`),
* central charge `24`,
* `V♮₁ = 0`,
* `dim V♮₂ = 196884`,
* `dim V♮ₙ = [qⁿ] (q·J)` for every `n` (graded dimension `J = j − 744`),
* simplicity (which excludes the square-zero extension `V_Λ^+ ⋉ (V_Λ^T)^+`, a
  non-simple VOA with the same graded dimension).

## Status

The unconditional theorem is `Moonshine.moonshine` (`TopPairs.lean`).  This file keeps the
conditional form on the direct route.

The theorem `moonshine_of_frameLocality` is `#print axioms`-clean but **conditional**: it provides
two explicit vectors `x 0 ∈ T₀⁺`, `x 1 ∈ T₁⁺` and concludes everything above from the four
instances `TPBlockLocal leechWbar (x i) (x j)` of DGM (4.23) — twisted × twisted locality on the
twisted sector — which is the single open input of this route (step M8h). V♮ is NOT
constructed unconditionally by this file alone; the unconditional statement is `Moonshine.moonshine`.
-/

namespace VOA.Moonshine

open Module VnatAxioms

/-- **The Moonshine module, conditional on step M8h.** There are explicit twisted-sector
vectors `x s ∈ T_s⁺` such that, if DGM (4.23) holds on the four pairs `(x i, x j)`, then `Vnat`
carries a simple vertex operator algebra structure with the genuine FLM block vertex map, central
charge `24`, `V♮₁ = 0`, `dim V♮₂ = 196884`, and graded dimension `q·J`. -/
theorem moonshine_of_frameLocality :
    ∃ x : ZMod 2 → TP, (∀ s, x s ∈ TPframe s) ∧
      ((∀ i j, TPBlockLocal leechWbar (x i) (x j)) →
        ∃ V : VertexOperatorAlgebra Vnat,
          V.Y = Ynat wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
          V.centralCharge = 24 ∧
          V.grading 1 = ⊥ ∧
          finrank ℂ (V.grading 2) = 196884 ∧
          (∀ n : ℕ, (finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
          V.IsSimple) := by
  obtain ⟨x, hx, h⟩ := SimpleNat.vnat_isSimple_of_TPBlockLocal_frame
  refine ⟨x, hx, fun h423 => ?_⟩
  obtain ⟨V, hY, hvac, hω, hc, hgr, hs⟩ := h h423
  refine ⟨V, hY, hvac, hω, hc, ?_, ?_, ?_, hs⟩
  · rw [hgr]; exact gradingNat_one
  · rw [hgr]; exact finrank_gradingNat_two
  · intro n; rw [hgr]; exact finrank_gradingNat_eq_coeff_JShift n

end VOA.Moonshine
