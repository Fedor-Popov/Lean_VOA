/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.LatticeRealizationGeneric
import VOA.DeligneAudit.LatticeRealizationE7Bridge
import VOA.DeligneAudit.LatticeRealizationE7Checks
import VOA.DeligneAudit.E7LieData
import VOA.DeligneAudit.E7SectorData
import VOA.DeligneAudit.E7FusionKernelFinal

/-!
# The lattice realization of `D(1, Nθ)` for `E₇`

On `V_{E₇}` (`e7`, the lattice VOA) with the cert basis `E7Lie.xs` (`E7Lie.bracket_xs`):

* `fE7_eq_sZ`: the sector table `fE7 = e7T` is the lattice-model cert table `E7Lie.sZ` (`table_eq_sL`, one
  kernel check per row in `LatticeRealizationE7Rows*`; both are the `structure` of `casimir_cert/cert_E7.json`);
* `e7LatData : LatData E7sector e7 …`: `X i = xs i`, roots `wt i`, coroots `α_i`, `θ = wt 69` (the highest root);
* **`e7_lattice_sat`**: `e^{Nθ}` satisfies `ravFam E7sector N 0` (the relations half of U7), unconditional;
* named **`E7LatticeDim N`** (the dimension half), `e7_demazureRealization`, and
  `e7_classicallyFree_of_totalBound_latDim` (the E₇ headline with U7 replaced by `E7LatticeDim`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.E7Lie (xs wt u f hvec formZ e7_form_eq sZ sL bracket_xs xs_root xs_cartan)
open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector fE7 thetaH lowExpE7 fusionE7 thetaPair)

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

theorem fE7_eq_sZ (a b c : Fin 133) : fE7 a b c = (sZ a b c : ℂ) := by
  show ((VOA.AffineGeneral.SCLie.coef (VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T a b) c : ℤ) : ℂ) = _
  rw [table_eq_sL, coef_map]
  rfl

/-! ## The realization data -/

theorem lowering_ge {i : Fin 133} (hi : i.val ∈ [76, 75, 74, 73, 72, 71, 70]) : 70 ≤ i.val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

/-- **`E₇` lattice realization data**: the cert basis of `(V_{E₇})₁`. -/
def e7LatData : LatData E7sector e7 e7_even e7_posDef where
  X i := (xs i : LatModuleGen e7)
  mem i := (xs i).2
  br c d := by
    have h := congrArg Subtype.val (bracket_xs c d)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    refine h.trans (Finset.sum_congr rfl fun e _ => ?_)
    exact congrArg (· • _) (fE7_eq_sZ c d e).symm
  cart i := decide (i.val < 7)
  rt := wt
  sg i := (u i : ℂ) * f (wt i)
  cv := hvec
  root i hi := by
    have : 7 ≤ i.val := by simpa using hi
    rw [xs_root i this]
    rfl
  coroot i hi := by
    rw [xs_cartan i (by simpa using hi)]
    rfl
  θ := wt 69
  raising e he := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := he.1; omega,
    by rw [e7_form_eq]; exact chk_raising e he⟩
  cartan h hc := ⟨by simpa using hc, by rw [e7_form_eq]; exact chk_cartan h hc⟩
  cartanN h hc := hc.elim
  lowering i hi := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := lowering_ge hi; omega,
    by rw [e7_form_eq]; exact (chk_lowering i hi).1, by rw [e7_form_eq]; exact (chk_lowering i hi).2⟩
  fusion x hx := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := hx.1; omega,
    by rw [e7_form_eq]; exact chk_fusion x hx.1⟩

theorem e7_hθ : e7.form e7LatData.θ e7LatData.θ = 2 := by
  change e7.form (wt 69) (wt 69) = 2
  rw [e7_form_eq]; exact chk_theta

/-- **`e^{Nθ} ∈ V_{E₇}` satisfies the relations of `M_{N,0}`** (unconditional). -/
theorem e7_lattice_sat (N : ℕ) : Sat E7sector.f e7LatData.ρ (e7LatData.vN N) (ravFam E7sector N 0) :=
  e7LatData.sat e7_hθ N

/-- **Named (the dimension half of U7 for `E₇`)**: the degree pieces of `U(𝔤[t]) e^{Nθ} ⊂ V_{E₇}` dominate the
`E₇` Demazure series. -/
def E7LatticeDim (N : ℕ) : Prop :=
  e7LatData.LatDim (DeligneCarrier.hilbSeries DeligneCharacter.e7DemazureHilb) N

theorem e7_demazureRealization {N : ℕ} (h : E7LatticeDim N) :
    DemazureRealizationG E7sector (ravFam E7sector) (DeligneCarrier.hilbSeries DeligneCharacter.e7DemazureHilb) N :=
  e7LatData.demazureRealizationG e7_hθ h

/-- **The `E₇` case** from `FusionTotalBoundG`, the lattice dimension half, the count and the star bound. -/
theorem e7_classicallyFree_of_totalBound_latDim (hF : FusionTotalBoundG E7sector)
    (hdim : ∀ N, E7LatticeDim N) (hcount : E7FusionCount) (hB : DeligneCharacter.E7StarBound) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .E7 E7Lie.W7 E7Lie.explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass E7Lie.W7 1 ⟨E7Lie.explicitPresentation7.gen i,
          E7Lie.explicitPresentation7.gen_weight_one i⟩).toRingHom =
        E7Lie.explicitPresentation7.ideal :=
  e7_classicallyFree_of_totalBound_starBound hF (fun n => e7_demazureRealization (hdim n)) hcount hB

end

end VOA.DeligneAudit.LatticeRealization.E7

section AxiomAudit
#print axioms VOA.DeligneAudit.LatticeRealization.E7.fE7_eq_sZ
#print axioms VOA.DeligneAudit.LatticeRealization.E7.e7_lattice_sat
#print axioms VOA.DeligneAudit.LatticeRealization.E7.e7_classicallyFree_of_totalBound_latDim
end AxiomAudit
