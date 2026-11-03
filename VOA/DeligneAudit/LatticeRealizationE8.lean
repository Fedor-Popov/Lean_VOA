/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.LatticeRealizationGeneric
import VOA.DeligneAudit.LatticeRealizationE8Bridge
import VOA.DeligneAudit.LatticeRealizationE8Checks
import VOA.DeligneAudit.E8LieData
import VOA.DeligneAudit.E8SectorData
import VOA.DeligneAudit.DeligneCharacterExceptional

/-!
# The lattice realization of `D(1, Nθ)` for `E₈`

On `V_{E₈}` (`e8`, the lattice VOA) with the cert basis `E8Lie.xs` (`E8Lie.bracket_xs`):

* `fE8_eq_sZ`: the sector table `fE8 = e8T` is the lattice-model cert table `E8Lie.sZ` (`table_eq_sL`, one
  kernel check per row in `LatticeRealizationE8Rows*`; both are the `structure` of `casimir_cert/cert_E8.json`);
* `e8LatData : LatData E8sector e8 …`: `X i = xs i`, roots `wt i`, coroots `α_i`, `θ = wt 127` (the highest root);
* **`e8_lattice_sat`**: `e^{Nθ}` satisfies `ravFam E8sector N 0` (the relations half of U7), unconditional;
* named **`E8LatticeDim N`** (the dimension half), `e8_demazureRealization`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E8

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.E8Lie (xs wt u f hvec formZ e8_form_eq sZ sL bracket_xs xs_root xs_cartan)
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector fE8 thetaH lowExpE8 fusionE8 thetaPair)

noncomputable section

/-! ## The sector table is the lattice-model cert table -/

theorem coef_map {n : ℕ} (l : List (Fin n × ℤ)) (c : Fin n) :
    VOA.AffineGeneral.SCLie.coef (l.map fun t => ((t.1 : ℕ), t.2)) c =
      (l.map fun t => if t.1 = c then t.2 else 0).sum := by
  unfold VOA.AffineGeneral.SCLie.coef
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, Fin.val_inj]

theorem fE8_eq_sZ (a b c : Fin 248) : fE8 a b c = (sZ a b c : ℂ) := by
  show ((VOA.AffineGeneral.SCLie.coef (VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E8.e8T a b) c : ℤ) : ℂ) = _
  rw [table_eq_sL, coef_map]
  rfl

/-! ## The realization data -/

theorem lowering_ge {i : Fin 248} (hi : i.val ∈ [135, 134, 133, 132, 131, 130, 129, 128]) : 128 ≤ i.val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

/-- **`E₈` lattice realization data**: the cert basis of `(V_{E₈})₁`. -/
def e8LatData : LatData E8sector e8 e8_even e8_posDef where
  X i := (xs i : LatModuleGen e8)
  mem i := (xs i).2
  br c d := by
    have h := congrArg Subtype.val (bracket_xs c d)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    refine h.trans (Finset.sum_congr rfl fun e _ => ?_)
    exact congrArg (· • _) (fE8_eq_sZ c d e).symm
  cart i := decide (i.val < 8)
  rt := wt
  sg i := (u i : ℂ) * f (wt i)
  cv := hvec
  root i hi := by
    have : 8 ≤ i.val := by simpa using hi
    rw [xs_root i this]
    rfl
  coroot i hi := by
    rw [xs_cartan i (by simpa using hi)]
    rfl
  θ := wt 127
  raising e he := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := he.1; omega,
    by rw [e8_form_eq]; exact chk_raising e he⟩
  cartan h hc := ⟨by simpa using hc, by rw [e8_form_eq]; exact chk_cartan h hc⟩
  cartanN h hc := hc.elim
  lowering i hi := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := lowering_ge hi; omega,
    by rw [e8_form_eq]; exact (chk_lowering i hi).1, by rw [e8_form_eq]; exact (chk_lowering i hi).2⟩
  fusion x hx := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := hx.1; omega,
    by rw [e8_form_eq]; exact chk_fusion x hx.1⟩

theorem e8_hθ : e8.form e8LatData.θ e8LatData.θ = 2 := by
  change e8.form (wt 127) (wt 127) = 2
  rw [e8_form_eq]; exact chk_theta

/-- **`e^{Nθ} ∈ V_{E₈}` satisfies the relations of `M_{N,0}`** (unconditional). -/
theorem e8_lattice_sat (N : ℕ) : Sat E8sector.f e8LatData.ρ (e8LatData.vN N) (ravFam E8sector N 0) :=
  e8LatData.sat e8_hθ N

/-- **Named (the dimension half of U7 for `E₈`)**: the degree pieces of `U(𝔤[t]) e^{Nθ} ⊂ V_{E₈}` dominate the
`E₈` Demazure series. -/
def E8LatticeDim (N : ℕ) : Prop :=
  e8LatData.LatDim (DeligneCarrier.hilbSeries DeligneCharacter.e8DemazureHilb) N

theorem e8_demazureRealization {N : ℕ} (h : E8LatticeDim N) :
    DemazureRealizationG E8sector (ravFam E8sector) (DeligneCarrier.hilbSeries DeligneCharacter.e8DemazureHilb) N :=
  e8LatData.demazureRealizationG e8_hθ h

end

end VOA.DeligneAudit.LatticeRealization.E8

section AxiomAudit
#print axioms VOA.DeligneAudit.LatticeRealization.E8.fE8_eq_sZ
#print axioms VOA.DeligneAudit.LatticeRealization.E8.e8_lattice_sat
end AxiomAudit
