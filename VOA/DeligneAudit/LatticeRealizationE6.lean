/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.LatticeRealizationGeneric
import VOA.DeligneAudit.LatticeRealizationE6Bridge
import VOA.DeligneAudit.E6LatBracket
import VOA.DeligneAudit.E6SectorData
import VOA.DeligneAudit.E6FusionKernelFinal

/-!
# The lattice realization of `D(1, Nθ)` for `E₆`

On `V_{E₆}` (`e6`, the lattice VOA) with the cert basis `E6Lat.xs` (`E6Lat.bracket_xs`, the port of the
E₇ lattice model):

* `fE6_eq_sZ`: the sector table `fE6 = SCLie.e6T` is the lattice-model cert table `E6Lat.sZ` (`table_eq_sL`, one
  kernel check per row in `LatticeRealizationE6Rows*`; both are the `structure` of `casimir_cert/cert_E6.json`);
* `e6LatData : LatData E6sector e6 …`: `X i = xs i`, roots `wt i`, coroots `α_i`, `θ = wt 41 = (1,2,2,3,2,1)`;
* **`e6_lattice_sat`**: `e^{Nθ}` satisfies `ravFam E6sector N 0` (the relations half of U7), unconditional;
* named **`E6LatticeDim N`** (the dimension half), `e6_demazureRealization`, and
  `e6_classicallyFree_of_totalBound_latDim` (the E₆ headline with U7 replaced by `E6LatticeDim`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.E6Lat (xs wt u f hvec formZ e6_form_eq sZ sL bracket_xs xs_root xs_cartan)
open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector fE6 thetaH lowExpE6 fusionE6 thetaPair)

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

theorem fE6_eq_sZ (a b c : Fin 78) : fE6 a b c = (sZ a b c : ℂ) := by
  show ((VOA.AffineGeneral.SCLie.coef (VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T a b) c : ℤ) : ℂ) = _
  rw [table_eq_sL, coef_map]
  rfl

/-! ## The realization data -/

theorem chk_raising : ∀ e : Fin 78, 6 ≤ e.val ∧ e.val < 42 → 0 ≤ formZ (wt e) (wt 41) := by decide +kernel

theorem chk_cartan : ∀ h : Fin 78, h.val < 6 → formZ (hvec h) (wt 41) = (thetaH h : ℤ) := by decide +kernel

theorem chk_lowering : ∀ i : Fin 78, i.val ∈ [47, 46, 45, 44, 43, 42] →
    formZ (wt i) (wt i) = 2 ∧ -(lowExpE6 i : ℤ) ≤ formZ (wt i) (wt 41) := by decide +kernel

theorem chk_fusion : ∀ x : Fin 78, 42 ≤ x.val →
    (if x = (77 : Fin 78) then (-2 : ℤ) else -1) ≤ formZ (wt x) (wt 41) := by decide +kernel

theorem chk_theta : formZ (wt 41) (wt 41) = 2 := by decide +kernel

theorem lowering_ge {i : Fin 78} (hi : i.val ∈ [47, 46, 45, 44, 43, 42]) : 42 ≤ i.val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  omega

/-- **`E₆` lattice realization data**: the cert basis of `(V_{E₆})₁`. -/
def e6LatData : LatData E6sector e6 e6_even e6_posDef where
  X i := (xs i : LatModuleGen e6)
  mem i := (xs i).2
  br c d := by
    have h := congrArg Subtype.val (bracket_xs c d)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul] at h
    refine h.trans (Finset.sum_congr rfl fun e _ => ?_)
    exact congrArg (· • _) (fE6_eq_sZ c d e).symm
  cart i := decide (i.val < 6)
  rt := wt
  sg i := (u i : ℂ) * f (wt i)
  cv := hvec
  root i hi := by
    have : 6 ≤ i.val := by simpa using hi
    rw [xs_root i this]
    rfl
  coroot i hi := by
    rw [xs_cartan i (by simpa using hi)]
    rfl
  θ := wt 41
  raising e he := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := he.1; omega,
    by rw [e6_form_eq]; exact chk_raising e he⟩
  cartan h hc := ⟨by simpa using hc, by rw [e6_form_eq]; exact chk_cartan h hc⟩
  cartanN h hc := hc.elim
  lowering i hi := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := lowering_ge hi; omega,
    by rw [e6_form_eq]; exact (chk_lowering i hi).1, by rw [e6_form_eq]; exact (chk_lowering i hi).2⟩
  fusion x hx := ⟨by simp only [decide_eq_false_iff_not]; exact fun h => by have := hx.1; omega,
    by rw [e6_form_eq]; exact chk_fusion x hx.1⟩

theorem e6_hθ : e6.form e6LatData.θ e6LatData.θ = 2 := by
  change e6.form (wt 41) (wt 41) = 2
  rw [e6_form_eq]; exact chk_theta

/-- **`e^{Nθ} ∈ V_{E₆}` satisfies the relations of `M_{N,0}`** (unconditional). -/
theorem e6_lattice_sat (N : ℕ) : Sat E6sector.f e6LatData.ρ (e6LatData.vN N) (ravFam E6sector N 0) :=
  e6LatData.sat e6_hθ N

/-- **Named (the dimension half of U7 for `E₆`)**: the degree pieces of `U(𝔤[t]) e^{Nθ} ⊂ V_{E₆}` dominate the
`E₆` Demazure series. -/
def E6LatticeDim (N : ℕ) : Prop :=
  e6LatData.LatDim (DeligneCarrier.hilbSeries DeligneCharacter.e6DemazureHilb) N

theorem e6_demazureRealization {N : ℕ} (h : E6LatticeDim N) :
    DemazureRealizationG E6sector (ravFam E6sector) (DeligneCarrier.hilbSeries DeligneCharacter.e6DemazureHilb) N :=
  e6LatData.demazureRealizationG e6_hθ h

/-- **The `E₆` case** from `FusionTotalBoundG`, the lattice dimension half, the count and the star bound. -/
theorem e6_classicallyFree_of_totalBound_latDim (hF : FusionTotalBoundG E6sector)
    (hdim : ∀ N, E6LatticeDim N) (hcount : E6K.E6FusionCount) (hB : DeligneCharacter.E6StarBound) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .E6 DeligneCarrier.E6.W6
        DeligneCarrier.E6.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass DeligneCarrier.E6.W6 1 ⟨DeligneCarrier.E6.explicitPresentation.gen i,
          DeligneCarrier.E6.explicitPresentation.gen_weight_one i⟩).toRingHom =
        DeligneCarrier.E6.explicitPresentation.ideal :=
  e6_classicallyFree_of_totalBound_starBound hF (fun n => e6_demazureRealization (hdim n)) hcount hB

end

end VOA.DeligneAudit.LatticeRealization.E6

section AxiomAudit
#print axioms VOA.DeligneAudit.LatticeRealization.E6.fE6_eq_sZ
#print axioms VOA.DeligneAudit.LatticeRealization.E6.e6_lattice_sat
#print axioms VOA.DeligneAudit.LatticeRealization.E6.e6_classicallyFree_of_totalBound_latDim
end AxiomAudit
