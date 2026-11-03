/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorWeyl
import VOA.DeligneAudit.E6SectorCyclicA
import VOA.DeligneAudit.E6SectorCyclicB
import VOA.DeligneAudit.E6SectorCyclicC

set_option linter.style.longLine false

/-!
# E₆ as sector data (`E6sector : DeligneSectorData`)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem e6_cyclic : ∀ c : Fin 78, (Pi.single c 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 := by
  intro c
  fin_cases c
  · exact cyc0
  · exact cyc1
  · exact cyc2
  · exact cyc3
  · exact cyc4
  · exact cyc5
  · exact cyc6
  · exact cyc7
  · exact cyc8
  · exact cyc9
  · exact cyc10
  · exact cyc11
  · exact cyc12
  · exact cyc13
  · exact cyc14
  · exact cyc15
  · exact cyc16
  · exact cyc17
  · exact cyc18
  · exact cyc19
  · exact cyc20
  · exact cyc21
  · exact cyc22
  · exact cyc23
  · exact cyc24
  · exact cyc25
  · exact cyc26
  · exact cyc27
  · exact cyc28
  · exact cyc29
  · exact cyc30
  · exact cyc31
  · exact cyc32
  · exact cyc33
  · exact cyc34
  · exact cyc35
  · exact cyc36
  · exact cyc37
  · exact cyc38
  · exact cyc39
  · exact cyc40
  · exact cyc41
  · exact cyc42
  · exact cyc43
  · exact cyc44
  · exact cyc45
  · exact cyc46
  · exact cyc47
  · exact cyc48
  · exact cyc49
  · exact cyc50
  · exact cyc51
  · exact cyc52
  · exact cyc53
  · exact cyc54
  · exact cyc55
  · exact cyc56
  · exact cyc57
  · exact cyc58
  · exact cyc59
  · exact cyc60
  · exact cyc61
  · exact cyc62
  · exact cyc63
  · exact cyc64
  · exact cyc65
  · exact cyc66
  · exact cyc67
  · exact cyc68
  · exact cyc69
  · exact cyc70
  · exact cyc71
  · exact cyc72
  · exact cyc73
  · exact cyc74
  · exact cyc75
  · exact cyc76
  · exact cyc77


/-! ## The sector data -/

/-- `(θ, α)` for the weight `α = -wt x` of a negative root vector (simply laced: `θᵀ C α`). -/
def thetaPair (x : Fin 78) : ℤ := -∑ i : Fin 6, ∑ j : Fin 6, thetaV i * cartanE6 i j * wtE6 x j

/-- **The fusion set**: `f_α` with `(θ,α) = 1`, and `f_θ`. -/
def fusionE6 (x : Fin 78) : Prop := 42 ≤ x.val ∧ (thetaPair x = 1 ∨ x.val = 77)

/-- **E₆ as sector data.** -/
def E6sector : DeligneSectorData where
  n := E6data.n
  ρ := E6data.ρ
  rel := E6data.rel
  cas := E6data.cas
  u3 := E6data.u3
  ρFin := inferInstanceAs (Fintype (Fin 650))
  f := fE6
  jacobi := e6_jacobi
  stable := e6_stable
  c₀ := (77 : Fin 78)
  diag := e6_diag
  raising := fun e => 6 ≤ e.val ∧ e.val < 42
  raising_table := e6_raising
  cartan := fun h => h.val < 6
  thetaH := thetaH
  cartan_table := e6_cartan
  hθ := (1 : Fin 78)
  hθ_cartan := by decide
  hθ_ne := by decide
  lowering := fun i => i.val ∈ [47, 46, 45, 44, 43, 42]
  lowExp := lowExpE6
  R := 6
  wt := wtE6
  table_wt := e6_table_wt
  lowering_noweight := e6_noweight
  fusion := fusionE6
  depth := 3
  cyclic := e6_cyclic

theorem E6sector_carrier : E6sector.toDeligneCarrierData = E6data := rfl


section AxiomAudit
open VOA.DeligneAudit.DeligneCarrier.E6
#print axioms E6sector
end AxiomAudit

end

end VOA.DeligneAudit.DeligneCarrier.E6
