/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiNegativeExponential
import VOA.Modules.RationalityLattice

/-!
# The honest unbounded weight grading of the inverse-DS Pi carrier

The isotropic exponential `exp(q eta)` has conformal weight `q`.  Consequently the inverse-DS
carrier is not of CFT type and its fixed-weight pieces are generally infinite-dimensional.  This
file constructs the correct internal `ℤ`-grading without imposing positivity or finiteness.

We first split the carrier by oscillator weight and integral charge.  The conformal grading is
then the fibrewise collapse along `(w,q) |-> w+q`.  The general `fibreSup_isInternal` theorem shows
that this collapse preserves an internal direct sum even though every fibre is infinite.
-/

namespace VOA
namespace InverseDSPi

open scoped BigOperators TensorProduct DirectSum
open RationalityLattice

noncomputable section

/-- Insert the oscillator Fock space into the charge-`q` sector. -/
def piStateMap (q : ℤ) : HyperFock →ₗ[ℂ] PiFockCarrier :=
  (TensorProduct.mk ℂ HyperFock EtaChargeLine).flip (etaChargeBasis q)

@[simp] theorem piStateMap_apply (q : ℤ) (p : HyperFock) :
    piStateMap q p = piFockState p q := rfl

/-- The simultaneous oscillator-weight/charge decomposition. -/
def piBigrading (wq : ℤ × ℤ) : Submodule ℂ PiFockCarrier :=
  (HeisenbergN.gradingZN 2 wq.1).map (piStateMap wq.2)

/-- Extract the oscillator coordinate in the charge-`q` sector. -/
def piChargeCoord (q : ℤ) : PiFockCarrier →ₗ[ℂ] HyperFock :=
  (TensorProduct.rid ℂ HyperFock).toLinearMap.comp
    (LinearMap.lTensor HyperFock (Finsupp.lapply q))

theorem piChargeCoord_state (q r : ℤ) (p : HyperFock) :
    piChargeCoord q (piFockState p r) = if q = r then p else 0 := by
  rw [piChargeCoord, LinearMap.comp_apply, piFockState, LinearMap.lTensor_tmul]
  show (TensorProduct.rid ℂ HyperFock)
      (p ⊗ₜ[ℂ] (Finsupp.lapply q) (etaChargeBasis r)) = _
  rw [etaChargeBasis, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : r = q
  · rw [if_pos h, if_pos h.symm, TensorProduct.rid_tmul, one_smul]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), TensorProduct.tmul_zero, map_zero]

/-- The oscillator internal-decomposition equivalence. -/
def piBosonEquiv :
    (⨁ w : ℤ, (HeisenbergN.gradingZN 2 w : Submodule ℂ HyperFock)) ≃ₗ[ℂ] HyperFock :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (HeisenbergN.gradingZN 2))
    (HeisenbergN.gradingZN_isInternal 2)

/-- Projection to oscillator weight `w`. -/
def piBosonProj (w : ℤ) : HyperFock →ₗ[ℂ] HyperFock :=
  (HeisenbergN.gradingZN 2 w).subtype.comp
    ((DirectSum.component ℂ ℤ
      (fun n => (HeisenbergN.gradingZN 2 n : Submodule ℂ HyperFock)) w).comp
      piBosonEquiv.symm.toLinearMap)

theorem piBosonProj_same {w : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) : piBosonProj w p = p := by
  rw [piBosonProj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show ((piBosonEquiv.symm p) w : HyperFock) = p
  rw [piBosonEquiv, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem _ hp]

theorem piBosonProj_of_ne {w w' : ℤ} (hww : w ≠ w') {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w') : piBosonProj w p = 0 := by
  rw [piBosonProj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  show ((piBosonEquiv.symm p) w : HyperFock) = 0
  rw [piBosonEquiv, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne _ hww.symm hp]
  rfl

/-- A detector for one simultaneous oscillator-weight/charge component. -/
def piBigradingDetector (w q : ℤ) : PiFockCarrier →ₗ[ℂ] HyperFock :=
  (piBosonProj w).comp (piChargeCoord q)

theorem piBigradingDetector_state {w : ℤ} (q r : ℤ) {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    piBigradingDetector w q (piFockState p r) = if q = r then p else 0 := by
  rw [piBigradingDetector, LinearMap.comp_apply, piChargeCoord_state]
  by_cases h : q = r
  · rw [if_pos h, piBosonProj_same hp]
  · rw [if_neg h, map_zero]

theorem piBigrading_le_detectorKer_of_ne (w q w' q' : ℤ)
    (hne : (w', q') ≠ (w, q)) :
    piBigrading (w', q') ≤ LinearMap.ker (piBigradingDetector w q) := by
  rintro x ⟨p, hp, rfl⟩
  rw [LinearMap.mem_ker, piBigradingDetector, LinearMap.comp_apply, piStateMap_apply,
    piChargeCoord_state]
  by_cases hq : q = q'
  · subst q'
    have hw : w ≠ w' := fun h => hne (by rw [h])
    rw [if_pos rfl, piBosonProj_of_ne hw hp]
  · rw [if_neg hq, map_zero]

theorem piBigrading_iSupIndep : iSupIndep piBigrading := by
  rw [iSupIndep_def]
  rintro ⟨w, q⟩
  rw [Submodule.disjoint_def]
  intro x hx hxsup
  obtain ⟨p, hp, hpx⟩ := hx
  have hker : (⨆ j, ⨆ (_ : j ≠ (w, q)), piBigrading j) ≤
      LinearMap.ker (piBigradingDetector w q) := by
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    exact piBigrading_le_detectorKer_of_ne w q j.1 j.2 (by simpa using hj)
  have hx0 : piBigradingDetector w q x = 0 := by
    rw [← LinearMap.mem_ker]
    exact hker hxsup
  have hxp : piBigradingDetector w q x = p := by
    rw [← hpx, piStateMap_apply]
    simpa using (piBigradingDetector_state (w := w) q q hp)
  rw [hxp] at hx0
  rw [← hpx, hx0, map_zero]

theorem piStateMap_mem_iSup (q : ℤ) (p : HyperFock) :
    piStateMap q p ∈ iSup piBigrading := by
  have hmem : piStateMap q p ∈ ⨆ w : ℤ, piBigrading (w, q) := by
    have hmap : (⨆ w : ℤ, HeisenbergN.gradingZN 2 w).map (piStateMap q)
        = ⨆ w : ℤ, piBigrading (w, q) := by
      rw [Submodule.map_iSup]
      rfl
    have hp : p ∈ ⨆ w : ℤ, HeisenbergN.gradingZN 2 w := by
      rw [HeisenbergN.gradingZN_iSup_eq_top 2]
      trivial
    have : piStateMap q p ∈ (⨆ w : ℤ, HeisenbergN.gradingZN 2 w).map (piStateMap q) :=
      Submodule.mem_map_of_mem hp
    rwa [hmap] at this
  exact (iSup_le (fun w => le_iSup piBigrading (w, q))) hmem

theorem piBigrading_iSup_eq_top : iSup piBigrading = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ HyperFock EtaChargeLine,
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction_linear with
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g₁ g₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
  | single q c =>
      rw [show (Finsupp.single q c : EtaChargeLine) = c • etaChargeBasis q by
        rw [etaChargeBasis, Finsupp.smul_single, smul_eq_mul, mul_one],
        TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ c (piStateMap_mem_iSup q p)

theorem piBigrading_isInternal : DirectSum.IsInternal piBigrading :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    piBigrading_iSupIndep piBigrading_iSup_eq_top

/-- Total conformal weight: oscillator weight plus integral null charge. -/
def piTotalWeight (wq : ℤ × ℤ) : ℤ := wq.1 + wq.2

/-- The honest Pi conformal grading, with no positivity or finite-dimensionality assertion. -/
def piWeightGrading : ℤ → Submodule ℂ PiFockCarrier :=
  fibreSup piBigrading piTotalWeight

theorem piBigrading_le_weight (w q : ℤ) :
    piBigrading (w, q) ≤ piWeightGrading (w + q) := by
  exact le_fibreSup piBigrading piTotalWeight (w, q)

theorem piWeightGrading_iSupIndep : iSupIndep piWeightGrading :=
  fibreSup_iSupIndep piBigrading_iSupIndep piTotalWeight

theorem piWeightGrading_iSup_eq_top : iSup piWeightGrading = ⊤ := by
  rw [show iSup piWeightGrading = iSup piBigrading from
    fibreSup_iSup piBigrading piTotalWeight]
  exact piBigrading_iSup_eq_top

/-- The Pi conformal grading is an internal direct sum despite its infinite fibres. -/
theorem piWeightGrading_isInternal : DirectSum.IsInternal piWeightGrading :=
  fibreSup_isInternal piBigrading_iSupIndep piBigrading_iSup_eq_top piTotalWeight

theorem piFockExponential_mem_weight (q : ℤ) :
    piFockExponential q ∈ piWeightGrading q := by
  have hmem : piFockExponential q ∈ piBigrading (0, q) := by
    change piStateMap q hyperVacuum ∈ piBigrading (0, q)
    refine ⟨hyperVacuum, ?_, rfl⟩
    rw [HeisenbergN.gradingZN_zero_eq_span_vacuum 2]
    exact Submodule.mem_span_singleton_self hyperVacuum
  simpa using (piBigrading_le_weight 0 q) hmem

theorem piFockVacuum_mem_weight_zero : piFockVacuum ∈ piWeightGrading 0 := by
  simpa [piFockExponential_zero] using piFockExponential_mem_weight 0

/-! ## Grading covariance of the concrete generating fields -/

/-- A field of Pi weight `D`: its coefficient `j` raises total weight by `D+j`. -/
def PiGradedField (a : FormalDist (Module.End ℂ PiFockCarrier)) (D : ℤ) : Prop :=
  ∀ (j n : ℤ) (x : PiFockCarrier), x ∈ piWeightGrading n →
    a j x ∈ piWeightGrading (D + n + j)

/-- It suffices to check grading covariance on simultaneous oscillator-weight/charge pieces. -/
theorem PiGradedField.of_bigrad {a : FormalDist (Module.End ℂ PiFockCarrier)} {D : ℤ}
    (h : ∀ (j w q : ℤ) (p : HyperFock), p ∈ HeisenbergN.gradingZN 2 w →
      a j (piFockState p q) ∈ piWeightGrading (D + (w + q) + j)) :
    PiGradedField a D := by
  intro j n x hx
  refine (?_ : piWeightGrading n ≤ (piWeightGrading (D + n + j)).comap (a j)) hx
  rw [piWeightGrading, fibreSup_def]
  refine iSup_le (fun wq => iSup_le (fun hwq => ?_))
  rintro y ⟨p, hp, rfl⟩
  rw [Submodule.mem_comap, piStateMap_apply]
  have hy := h j wq.1 wq.2 p hp
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hwq
  change wq.1 + wq.2 = n at hwq
  change a j (piFockState p wq.2) ∈ piWeightGrading (D + n + j)
  rwa [hwq] at hy

/-- Every complex oscillator direction shifts polynomial weight by minus its mode number. -/
theorem directionOsc_mem_gradingZN (v : Fin 2 → ℂ) (m w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    directionOsc v m p ∈ HeisenbergN.gradingZN 2 (w - m) := by
  rw [directionOsc, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hw : 0 ≤ w
  · rw [HeisenbergN.gradingZN_of_nonneg hw] at hp
    have hm := HeisenbergN.oscN_mem_gradingZN 2 1 a m hp
    rwa [Int.toNat_of_nonneg hw] at hm
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact HeisenbergN.zero_mem_gradingZN 2 _

theorem xiOsc_mem_gradingZN (m w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    xiOsc m p ∈ HeisenbergN.gradingZN 2 (w - m) :=
  directionOsc_mem_gradingZN xiDirection m w p hp

/-- The null current has Pi weight one. -/
theorem etaCurrentField_graded : PiGradedField etaCurrentField 1 := by
  refine PiGradedField.of_bigrad (fun j w q p hp => ?_)
  rw [etaCurrentField_piFockState]
  have hosc := etaOsc_mem_gradingZN (-j - 1) hp
  have hmem := piBigrading_le_weight (w + j + 1) q
    (show piFockState (etaOsc (-j - 1) p) q ∈ piBigrading (w + j + 1, q) from
      ⟨etaOsc (-j - 1) p, by
        rw [← show w - (-j - 1) = w + j + 1 by ring]
        exact hosc, rfl⟩)
  rwa [show (w + j + 1) + q = 1 + (w + q) + j by ring] at hmem

/-- The transverse current, including its charge zero mode, has Pi weight one. -/
theorem xiCurrentField_graded : PiGradedField xiCurrentField 1 := by
  refine PiGradedField.of_bigrad (fun j w q p hp => ?_)
  rw [xiCurrentField_piFockState]
  refine Submodule.add_mem _ ?_ ?_
  · have hosc := xiOsc_mem_gradingZN (-j - 1) w p hp
    have hmem := piBigrading_le_weight (w + j + 1) q
      (show piFockState (xiOsc (-j - 1) p) q ∈ piBigrading (w + j + 1, q) from
        ⟨xiOsc (-j - 1) p, by
          rw [← show w - (-j - 1) = w + j + 1 by ring]
          exact hosc, rfl⟩)
    rwa [show (w + j + 1) + q = 1 + (w + q) + j by ring] at hmem
  · by_cases hj : j = -1
    · rw [if_pos hj]
      refine Submodule.smul_mem _ _ ?_
      have hmem := piBigrading_le_weight w q
        (show piFockState p q ∈ piBigrading (w, q) from ⟨p, hp, rfl⟩)
      subst j
      simpa using hmem
    · rw [if_neg hj]
      exact Submodule.zero_mem _

theorem etaCreationCoeff_mem_gradingZN_Z (N : ℕ) {w : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaCreationCoeff N p ∈ HeisenbergN.gradingZN 2 (w + N) := by
  induction N using Nat.strong_induction_on generalizing w p with
  | _ N ih =>
      match N with
      | 0 => simpa using hp
      | M + 1 =>
          rw [etaCreationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply]
          have hrec := ih (M - m) (by omega) hp
          have hmode := etaOsc_mem_gradingZN (-((m : ℤ) + 1)) hrec
          have heq : w + (M - m : ℕ) - (-((m : ℤ) + 1)) = w + ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [heq] at hmode

theorem etaAnnihilationCoeff_mem_gradingZN_Z (N : ℕ) {w : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaAnnihilationCoeff N p ∈ HeisenbergN.gradingZN 2 (w - N) := by
  induction N using Nat.strong_induction_on generalizing w p with
  | _ N ih =>
      match N with
      | 0 => simpa using hp
      | M + 1 =>
          rw [etaAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, LinearMap.neg_apply]
          refine Submodule.neg_mem _ ?_
          have hrec := ih (M - m) (by omega) hp
          have hmode := etaOsc_mem_gradingZN ((m : ℤ) + 1) hrec
          have heq : w - (M - m : ℕ) - ((m : ℤ) + 1) = w - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [heq] at hmode

theorem etaEminus_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaEminus t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  by_cases ht : 0 ≤ t
  · rw [etaEminus_nonneg ht]
    have h := etaCreationCoeff_mem_gradingZN_Z t.toNat hp
    rwa [Int.toNat_of_nonneg ht] at h
  · rw [etaEminus_neg (by omega), LinearMap.zero_apply]
    exact HeisenbergN.zero_mem_gradingZN 2 _

theorem etaEplus_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaEplus t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  by_cases ht : t ≤ 0
  · rw [etaEplus_nonpos ht]
    have h := etaAnnihilationCoeff_mem_gradingZN_Z (-t).toNat hp
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)] at h
    rwa [show w - -t = w + t by ring] at h
  · rw [etaEplus_pos (by omega), LinearMap.zero_apply]
    exact HeisenbergN.zero_mem_gradingZN 2 _

theorem etaDress_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaDress t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  rw [etaDress_apply_conv]
  rw [finsum_eq_finsetSum_of_support_subset _
    (s := (etaDress_marg_support_finite t p).toFinset)
    (by rw [(etaDress_marg_support_finite t p).coe_toFinset])]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  have hp1 := etaEplus_mem_grading (t - m) w p hp
  have hp2 := etaEminus_mem_grading m (w + (t - m)) (etaEplus (t - m) p) hp1
  rwa [show w + (t - m) + m = w + t by ring] at hp2

/-- The charge-one exponential has Pi weight one. -/
theorem etaExponentialField_graded : PiGradedField etaExponentialField 1 := by
  refine PiGradedField.of_bigrad (fun t w q p hp => ?_)
  rw [etaExponentialField_piFockState]
  have hdress := etaDress_mem_grading t w p hp
  have hmem := piBigrading_le_weight (w + t) (q + 1)
    (show piFockState (etaDress t p) (q + 1) ∈ piBigrading (w + t, q + 1) from
      ⟨etaDress t p, hdress, rfl⟩)
  rwa [show (w + t) + (q + 1) = 1 + (w + q) + t by ring] at hmem

theorem etaNegCreationCoeff_mem_gradingZN_Z (N : ℕ) {w : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaNegCreationCoeff N p ∈ HeisenbergN.gradingZN 2 (w + N) := by
  induction N using Nat.strong_induction_on generalizing w p with
  | _ N ih =>
      match N with
      | 0 => simpa using hp
      | M + 1 =>
          rw [etaNegCreationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, etaNegCreationAtom, LinearMap.neg_apply]
          refine Submodule.neg_mem _ ?_
          have hrec := ih (M - m) (by omega) hp
          have hmode := etaOsc_mem_gradingZN (-((m : ℤ) + 1)) hrec
          have heq : w + (M - m : ℕ) - (-((m : ℤ) + 1)) = w + ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [heq] at hmode

theorem etaNegAnnihilationCoeff_mem_gradingZN_Z (N : ℕ) {w : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaNegAnnihilationCoeff N p ∈ HeisenbergN.gradingZN 2 (w - N) := by
  induction N using Nat.strong_induction_on generalizing w p with
  | _ N ih =>
      match N with
      | 0 => simpa using hp
      | M + 1 =>
          rw [etaNegAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, etaNegAnnihilationAtom]
          have hrec := ih (M - m) (by omega) hp
          have hmode := etaOsc_mem_gradingZN ((m : ℤ) + 1) hrec
          have heq : w - (M - m : ℕ) - ((m : ℤ) + 1) = w - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [heq] at hmode

theorem etaNegEminus_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaNegEminus t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  by_cases ht : 0 ≤ t
  · rw [etaNegEminus_nonneg ht]
    have h := etaNegCreationCoeff_mem_gradingZN_Z t.toNat hp
    rwa [Int.toNat_of_nonneg ht] at h
  · rw [etaNegEminus_neg (by omega), LinearMap.zero_apply]
    exact HeisenbergN.zero_mem_gradingZN 2 _

theorem etaNegEplus_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaNegEplus t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  by_cases ht : t ≤ 0
  · rw [etaNegEplus_nonpos ht]
    have h := etaNegAnnihilationCoeff_mem_gradingZN_Z (-t).toNat hp
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)] at h
    rwa [show w - -t = w + t by ring] at h
  · rw [etaNegEplus_pos (by omega), LinearMap.zero_apply]
    exact HeisenbergN.zero_mem_gradingZN 2 _

theorem etaNegDress_mem_grading (t w : ℤ) (p : HyperFock)
    (hp : p ∈ HeisenbergN.gradingZN 2 w) :
    etaNegDress t p ∈ HeisenbergN.gradingZN 2 (w + t) := by
  rw [etaNegDress, nprod_apply]
  have hsupport : (Function.support (fun m : ℤ =>
      normalOrdered etaNegEminus etaNegEplus m (t - m) p)).Finite :=
    normalOrdered_diag_support_finite etaNegEminus_isField etaNegEplus_isField t p
  rw [finsum_eq_finsetSum_of_support_subset _ (s := hsupport.toFinset)
    (by rw [hsupport.coe_toFinset])]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
    have hp1 := etaNegEplus_mem_grading (t - m) w p hp
    have hp2 := etaNegEminus_mem_grading m (w + (t - m)) (etaNegEplus (t - m) p) hp1
    rwa [show w + (t - m) + m = w + t by ring] at hp2
  · rw [if_neg hm, Module.End.mul_apply]
    have hp1 := etaNegEminus_mem_grading m w p hp
    have hp2 := etaNegEplus_mem_grading (t - m) (w + m) (etaNegEminus m p) hp1
    rwa [show w + m + (t - m) = w + t by ring] at hp2

/-- The charge-minus-one exponential has Pi weight minus one. -/
theorem etaNegativeExponentialField_graded : PiGradedField etaNegativeExponentialField (-1) := by
  refine PiGradedField.of_bigrad (fun t w q p hp => ?_)
  rw [etaNegativeExponentialField_piFockState]
  have hdress := etaNegDress_mem_grading t w p hp
  have hmem := piBigrading_le_weight (w + t) (q - 1)
    (show piFockState (etaNegDress t p) (q - 1) ∈ piBigrading (w + t, q - 1) from
      ⟨etaNegDress t p, hdress, rfl⟩)
  -- With the chosen background charge, `exp(-eta)` has weight `-1`, not `+1`.
  rwa [show (w + t) + (q - 1) = (-1 : ℤ) + (w + q) + t by ring] at hmem

end
end InverseDSPi
end VOA
