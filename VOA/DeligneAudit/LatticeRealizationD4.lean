/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.LatticeRealizationGeneric
import VOA.DeligneAudit.LatticeRealizationD4Bridge
import VOA.DeligneAudit.D4LieData
import VOA.DeligneAudit.DeligneSectorD4
import VOA.DeligneAudit.DeligneCharacterD4Positivity
import VOA.DeligneAudit.D4FusionKernelTheta

/-!
# The lattice realization of `D(1, Nθ)` for `D₄`

On `V_{D₄}` (`d4`, the lattice VOA) with the cert basis `D4Lie.xs` (`bracket_xs`):

* `fD4_eq_sZ`: the sector table `fD4` (`DeligneSectorD4Table.br`) is the cert table `sZ` (both are the field
  `structure` of `casimir_cert/cert_D4.json`; `table_eq_sL`, one kernel check per row in `LatticeRealizationD4Rows*`);
* `d4LatData : LatData D4sector d4 …`: `X i = xs i`, roots `wt i` with signs `u_i f(wt i)`, coroots `α_i`,
  `θ = wt 15 = (1,2,1,1)`; the sign conditions of `ravFam` by `decide`;
* **`d4_lattice_sat`**: `e^{Nθ}` satisfies `ravFam D4sector N 0` (the relations half of U7), unconditional;
* named **`D4LatticeDim N`** (the dimension half), `d4_demazureRealization`, and
  `d4_classicallyFree_of_totalBound_latDim` (the D₄ headline with U7 replaced by `D4LatticeDim`).
-/

namespace VOA.DeligneAudit.LatticeRealization.D4

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.D4Lie (xs wt u f hvec formZ d4_form_eq sZ sL bracket_xs xs_root xs_cartan wt_norm)
open VOA.DeligneAudit.DeligneSector.D4 (D4sector fD4 thetaD4 lowExpD4)

noncomputable section

/-! ## The sector table is the cert table -/

theorem sget_map {n : ℕ} (l : List (Fin n × ℤ)) (c : Fin n) :
    sget (l.map fun t => ((t.1 : ℕ), t.2)) c = (l.map fun t => if t.1 = c then t.2 else 0).sum := by
  unfold sget
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, Fin.val_inj]

theorem fD4_eq_sZ (a b c : Fin 28) : fD4 a b c = (sZ a b c : ℂ) := by
  show ((sget (DeligneSector.D4.br a b) c : ℤ) : ℂ) = _
  rw [table_eq_sL, sget_map]
  rfl

/-! ## The realization data -/

theorem chk_raising : ∀ e : Fin 28, 4 ≤ e.val ∧ e.val < 16 → 0 ≤ formZ (wt e) (wt 15) := by decide +kernel

theorem chk_cartan : ∀ h : Fin 28, h.val < 4 → formZ (hvec h) (wt 15) = (thetaD4 h : ℤ) := by decide +kernel

theorem chk_lowering : ∀ i : Fin 28, 16 ≤ i.val ∧ i.val < 20 →
    formZ (wt i) (wt i) = 2 ∧ -(lowExpD4 i : ℤ) ≤ formZ (wt i) (wt 15) := by decide +kernel

theorem chk_fusion : ∀ x : Fin 28, 16 ≤ x.val →
    (if x = (27 : Fin 28) then (-2 : ℤ) else -1) ≤ formZ (wt x) (wt 15) := by decide +kernel

theorem chk_theta : formZ (wt 15) (wt 15) = 2 := by decide +kernel

/-- **`D₄` lattice realization data**: the cert basis of `(V_{D₄})₁`. -/
def d4LatData : LatData D4sector d4 d4_even d4_posDef where
  X i := (xs i : LatModuleGen d4)
  mem i := (xs i).2
  br c d := by
    have h := congrArg Subtype.val (bracket_xs c d)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    refine h.trans (Finset.sum_congr rfl fun e _ => ?_)
    exact congrArg (· • _) (fD4_eq_sZ c d e).symm
  cart i := decide (i.val < 4)
  rt := wt
  sg i := (u i : ℂ) * f (wt i)
  cv := hvec
  root i hi := by
    have : 4 ≤ i.val := by simpa using hi
    rw [xs_root i this]
    rfl
  coroot i hi := by
    rw [xs_cartan i (by simpa using hi)]
    rfl
  θ := wt 15
  raising e he := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := he.1; omega,
    by rw [d4_form_eq]; exact chk_raising e he⟩
  cartan h hc := ⟨by simpa using hc, by rw [d4_form_eq]; exact chk_cartan h hc⟩
  cartanN h hc := hc.elim
  lowering i hi := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := hi.1; omega,
    by rw [d4_form_eq]; exact (chk_lowering i hi).1, by rw [d4_form_eq]; exact (chk_lowering i hi).2⟩
  fusion x hx := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have : 16 ≤ x.val := hx; omega,
    by rw [d4_form_eq]; exact chk_fusion x hx⟩

theorem d4_hθ : d4.form d4LatData.θ d4LatData.θ = 2 := by
  change d4.form (wt 15) (wt 15) = 2
  rw [d4_form_eq]; exact chk_theta

/-- **`e^{Nθ} ∈ V_{D₄}` satisfies the relations of `M_{N,0}`** (unconditional). -/
theorem d4_lattice_sat (N : ℕ) : Sat D4sector.f d4LatData.ρ (d4LatData.vN N) (ravFam D4sector N 0) :=
  d4LatData.sat d4_hθ N

/-- **Named (the dimension half of U7 for `D₄`)**: the degree pieces of `U(𝔤[t]) e^{Nθ} ⊂ V_{D₄}` dominate the
`D₄` Demazure series `hilbSeriesZ N`. -/
def D4LatticeDim (N : ℕ) : Prop :=
  d4LatData.LatDim DeligneCharacter.D4Wp.hilbSeriesZ N

theorem d4_demazureRealization {N : ℕ} (h : D4LatticeDim N) :
    DemazureRealizationG D4sector (ravFam D4sector) DeligneCharacter.D4Wp.hilbSeriesZ N :=
  d4LatData.demazureRealizationG d4_hθ h

/-- **The `D₄` case** from `FusionTotalBoundG` and the lattice dimension half `D4LatticeDim`. -/
theorem d4_classicallyFree_of_totalBound_latDim (hF : FusionTotalBoundG D4sector)
    (hdim : ∀ N, D4LatticeDim N) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4 D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  d4_classicallyFree_of_totalBound hF fun n => d4_demazureRealization (hdim n)

end

end VOA.DeligneAudit.LatticeRealization.D4

section AxiomAudit
#print axioms VOA.DeligneAudit.LatticeRealization.D4.fD4_eq_sZ
#print axioms VOA.DeligneAudit.LatticeRealization.D4.d4_lattice_sat
#print axioms VOA.DeligneAudit.LatticeRealization.D4.d4_classicallyFree_of_totalBound_latDim
end AxiomAudit
