/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorCyclic

/-!
# `E₈` as sector data (`E8sector : DeligneSectorData`)

The relations, Casimir and U3 are `E8data` (`E8sector_carrier : … = E8data` by `rfl`); structure
constants `fE8` (the cert table, Jacobi from `e8Lie`), stability of `I₂` from the 16 Chevalley generators,
`c₀ = 247` (weight `-θ`), depth-2 coadjoint cyclicity.  `cartanN`/`thetaN`/`cartanN_table` keep their
defaults (simply laced).

Port of the `E7SectorData`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E8

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

/-- `(θ, α)` for the weight `α = -wt x` of a negative root vector. -/
def thetaPair (x : Fin 248) : ℤ := -E8Lie.formZ (fun k => thetaV k) (E8Lie.wt x)

/-- **The fusion set**: `f_α` with `(θ,α) = 1`, and `f_θ`. -/
def fusionE8 (x : Fin 248) : Prop := 128 ≤ x.val ∧ (thetaPair x = 1 ∨ x.val = 247)

/-- **E₈ as sector data.** -/
def E8sector : DeligneSectorData where
  n := E8data.n
  ρ := E8data.ρ
  rel := E8data.rel
  cas := E8data.cas
  u3 := E8data.u3
  ρFin := inferInstanceAs (Fintype (Fin 3875))
  f := fE8
  jacobi := e8_jacobi
  stable := e8_stable
  c₀ := (247 : Fin 248)
  diag := e8_diag
  raising := fun e => 8 ≤ e.val ∧ e.val < 128
  raising_table := e8_raising
  cartan := fun h => h.val < 8
  thetaH := thetaH
  cartan_table := e8_cartan
  hθ := (7 : Fin 248)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering := fun i => i.val ∈ [135, 134, 133, 132, 131, 130, 129, 128]
  lowExp := lowExpE8
  R := 8
  wt := E8Lie.wt
  table_wt := e8_table_wt
  lowering_noweight := e8_noweight
  fusion := fusionE8
  depth := 2
  cyclic := e8_cyclic

theorem E8sector_carrier : E8sector.toDeligneCarrierData = E8data := rfl

end

end VOA.DeligneAudit.DeligneCarrier.E8

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E8.E8sector
#print axioms VOA.DeligneAudit.DeligneCarrier.E8.E8sector_carrier
end AxiomAudit
