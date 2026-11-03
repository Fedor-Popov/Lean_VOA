/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorCyclic

/-!
# `E₇` as sector data (`E7sector : DeligneSectorData`)

The relations, Casimir and U3 are `E7data` (`E7sector_carrier : … = E7data` by `rfl`); structure
constants `fE7` (the cert table, Jacobi from `e7Lie`), stability of `I₂` from the 14 Chevalley generators,
`c₀ = 132` (weight `-θ`), depth-2 coadjoint cyclicity.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E7

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-- `(θ, α)` for the weight `α = -wt x` of a negative root vector. -/
def thetaPair (x : Fin 133) : ℤ := -E7Lie.formZ (fun k => thetaV k) (E7Lie.wt x)

/-- **The fusion set**: `f_α` with `(θ,α) = 1`, and `f_θ`. -/
def fusionE7 (x : Fin 133) : Prop := 70 ≤ x.val ∧ (thetaPair x = 1 ∨ x.val = 132)

/-- **E₇ as sector data.** -/
def E7sector : DeligneSectorData where
  n := E7data.n
  ρ := E7data.ρ
  rel := E7data.rel
  cas := E7data.cas
  u3 := E7data.u3
  ρFin := inferInstanceAs (Fintype (Fin 1539))
  f := fE7
  jacobi := e7_jacobi
  stable := e7_stable
  c₀ := (132 : Fin 133)
  diag := e7_diag
  raising := fun e => 7 ≤ e.val ∧ e.val < 70
  raising_table := e7_raising
  cartan := fun h => h.val < 7
  thetaH := thetaH
  cartan_table := e7_cartan
  hθ := (0 : Fin 133)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering := fun i => i.val ∈ [76, 75, 74, 73, 72, 71, 70]
  lowExp := lowExpE7
  R := 7
  wt := E7Lie.wt
  table_wt := e7_table_wt
  lowering_noweight := e7_noweight
  fusion := fusionE7
  depth := 2
  cyclic := e7_cyclic

theorem E7sector_carrier : E7sector.toDeligneCarrierData = E7data := rfl

end

end VOA.DeligneAudit.DeligneCarrier.E7

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E7.E7sector
end AxiomAudit
