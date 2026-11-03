/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoFelderStart
import VOA.Examples.InverseDSScreeningCoset

/-!
# The first shifted Fock carrier in the lattice `W(2)` Felder sequence

Let `L_2 = Z alpha`, with `<alpha,alpha> = 4`, and put `delta = -alpha/2`.  The first
short-screening current leaves the lattice charge line: it maps the ambient lattice carrier
`V_{L_2}` into the coset carrier `V_{L_2+delta}`.  This file constructs that target as a genuinely
different charge type, its exact background-charge grading, and the heterotypic exponential field
whose residue is the first candidate Felder differential.

For the coset label `n`, representing charge `(n-1/2) alpha`, the charged ground state has weight

`q_delta(n) = 2*n^2 - 3*n + 1`.

This is a nonnegative integer.  Consequently the oscillator/charge grading is internal, has
finite-dimensional pieces, and is bounded below.  Since `<delta,m alpha> = -2m`, all powers of the
short-screening field on `V_{L_2}` are integral.  Its residue preserves the deformed integer
weight exactly.

The charge shift below uses unit sector phase.  This is sufficient for the present bare
heterotypic field.  Compatibility with a lattice-coset cocycle is part of the future module
construction and is not asserted here.

## Deliberate boundary

No `WeakModule` or `OrdVModule` is asserted here.  The repository does not yet have either a
lattice-coset module reconstruction theorem or the odd-half-lattice super vertex map.  In
particular, a lower-truncated heterotypic field is not by itself a module action, and this file
makes no claim of Felder exactness, image--kernel equality, or a logarithmic module.
-/

set_option linter.style.longLine false

namespace VOA.LatGen.WpTwoFelderCarrier

open scoped BigOperators TensorProduct DirectSum
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.InverseDS VOA.InverseDSPi
open VOA.InverseDS.HalfLattice VOA.InverseDS.ScreeningCoset
open VOA.LatGen VOA.LatGen.Triplet

noncomputable section

/-! ## The shifted charge carrier -/

/-- A label for the coset charge `(n-1/2) alpha`.  This is deliberately not the source lattice's
integer charge type. -/
structure WpTwoCosetCharge where
  label : ℤ
  deriving DecidableEq

/-- The coset label reached from the source charge `m alpha` by adding `delta=-alpha/2`. -/
def wpTwoCosetCharge (m : ℤ) : WpTwoCosetCharge := ⟨m⟩

/-- The represented coefficient of `alpha`: `n-1/2`. -/
def WpTwoCosetCharge.value (q : WpTwoCosetCharge) : ℂ := (q.label : ℂ) - 1 / 2

/-- The charged ground-state weight for `(n-1/2) alpha` in the `c=-2` background. -/
def wpTwoCosetGroundWeight (q : WpTwoCosetCharge) : ℤ :=
  2 * q.label ^ 2 - 3 * q.label + 1

theorem wpTwoCosetGroundWeight_eq (n : ℤ) :
    wpTwoCosetGroundWeight (wpTwoCosetCharge n) = 2 * n ^ 2 - 3 * n + 1 := rfl

/-- Every coset ground weight is nonnegative.  The two bottom states occur at labels `0` and `1`,
with weights `1` and `0`, respectively. -/
theorem wpTwoCosetGroundWeight_nonneg (q : WpTwoCosetCharge) :
    0 ≤ wpTwoCosetGroundWeight q := by
  rcases le_or_gt q.label 0 with h | h
  · simp only [wpTwoCosetGroundWeight]
    nlinarith [sq_nonneg q.label]
  · have h1 : 1 ≤ q.label := by omega
    simp only [wpTwoCosetGroundWeight]
    nlinarith [sq_nonneg (q.label - 1)]

@[simp] theorem wpTwoCosetGroundWeight_zero :
    wpTwoCosetGroundWeight (wpTwoCosetCharge 0) = 1 := by
  norm_num [wpTwoCosetGroundWeight, wpTwoCosetCharge]

@[simp] theorem wpTwoCosetGroundWeight_one :
    wpTwoCosetGroundWeight (wpTwoCosetCharge 1) = 0 := by
  norm_num [wpTwoCosetGroundWeight, wpTwoCosetCharge]

/-- The short momentum `delta=-alpha/2` has conformal weight one. -/
theorem shortMomentum_weight_one :
    wpTwoCosetGroundWeight (wpTwoCosetCharge 0) = 1 := wpTwoCosetGroundWeight_zero

/-- The source Fock space.  Keeping the rank in the general-lattice form avoids any unsafe
identification of `Fin (rank L_2)` with `Fin 1`. -/
abbrev WpTwoFock := FockN (rank (latP 2))

/-- The group-algebra vector space of the shifted coset. -/
abbrev WpTwoCosetChargeLine := WpTwoCosetCharge →₀ ℂ

/-- The shifted Fock carrier `V_{L_2-alpha/2}`. -/
abbrev WpTwoCosetCarrier := WpTwoFock ⊗[ℂ] WpTwoCosetChargeLine

/-- Basis vector of a shifted charge sector. -/
def wpTwoCosetChargeBasis (q : WpTwoCosetCharge) : WpTwoCosetChargeLine :=
  Finsupp.single q 1

/-- A pure oscillator/coset-charge state. -/
def wpTwoCosetState (p : WpTwoFock) (q : WpTwoCosetCharge) : WpTwoCosetCarrier :=
  p ⊗ₜ[ℂ] wpTwoCosetChargeBasis q

/-- Exact decomposition by shifted charge. -/
def wpTwoCosetChargeDecomp : WpTwoCosetCarrier ≃ₗ[ℂ] WpTwoCosetCharge →₀ WpTwoFock :=
  TensorProduct.finsuppScalarRight ℂ ℂ WpTwoFock WpTwoCosetCharge

@[simp] theorem wpTwoCosetChargeDecomp_state (p : WpTwoFock) (q : WpTwoCosetCharge) :
    wpTwoCosetChargeDecomp (wpTwoCosetState p q) = Finsupp.single q p := by
  apply wpTwoCosetChargeDecomp.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change p ⊗ₜ[ℂ] Finsupp.single q 1 =
    wpTwoCosetChargeDecomp.symm (Finsupp.single q p)
  exact (TensorProduct.finsuppScalarRight_symm_apply_single
    (R := ℂ) (S := ℂ) (M := WpTwoFock) q p).symm

/-- The exact sector of one shifted charge. -/
def wpTwoCosetSector (q : WpTwoCosetCharge) : Submodule ℂ WpTwoCosetCarrier :=
  (Finsupp.supported WpTwoFock ℂ {q}).comap wpTwoCosetChargeDecomp.toLinearMap

@[simp] theorem wpTwoCosetState_mem_sector (p : WpTwoFock) (q : WpTwoCosetCharge) :
    wpTwoCosetState p q ∈ wpTwoCosetSector q := by
  change wpTwoCosetChargeDecomp (wpTwoCosetState p q) ∈ Finsupp.supported WpTwoFock ℂ {q}
  rw [wpTwoCosetChargeDecomp_state, Finsupp.mem_supported]
  intro y hy
  by_contra hyq
  exact (Finsupp.mem_support_iff.mp hy) (Finsupp.single_eq_of_ne hyq)

/-! ## The oscillator/charge bigrading -/

/-- Injection of the Fock space into one shifted charge sector. -/
def wpTwoCosetStateMap (q : WpTwoCosetCharge) : WpTwoFock →ₗ[ℂ] WpTwoCosetCarrier :=
  (TensorProduct.mk ℂ WpTwoFock WpTwoCosetChargeLine).flip (wpTwoCosetChargeBasis q)

@[simp] theorem wpTwoCosetStateMap_apply (q : WpTwoCosetCharge) (p : WpTwoFock) :
    wpTwoCosetStateMap q p = wpTwoCosetState p q := rfl

/-- The product bigrading by oscillator level and shifted charge. -/
def wpTwoCosetBigrading (wq : ℤ × WpTwoCosetCharge) : Submodule ℂ WpTwoCosetCarrier :=
  (gradingZN (rank (latP 2)) wq.1).map (wpTwoCosetStateMap wq.2)

/-- Coordinate extraction at one shifted charge. -/
def wpTwoCosetChargeCoord (q : WpTwoCosetCharge) : WpTwoCosetCarrier →ₗ[ℂ] WpTwoFock :=
  (TensorProduct.rid ℂ WpTwoFock).toLinearMap.comp
    (LinearMap.lTensor WpTwoFock (Finsupp.lapply q))

theorem wpTwoCosetChargeCoord_state (q r : WpTwoCosetCharge) (p : WpTwoFock) :
    wpTwoCosetChargeCoord q (wpTwoCosetState p r) = if q = r then p else 0 := by
  rw [wpTwoCosetChargeCoord, LinearMap.comp_apply, wpTwoCosetState, LinearMap.lTensor_tmul]
  change (TensorProduct.rid ℂ WpTwoFock)
      (p ⊗ₜ[ℂ] (Finsupp.lapply q) (wpTwoCosetChargeBasis r)) = _
  rw [wpTwoCosetChargeBasis, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : r = q
  · rw [if_pos h, if_pos h.symm, TensorProduct.rid_tmul, one_smul]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), TensorProduct.tmul_zero, map_zero]

/-- The internal-decomposition equivalence for the oscillator grading. -/
def wpTwoCosetBosonEquiv :
    (⨁ w : ℤ, (gradingZN (rank (latP 2)) w : Submodule ℂ WpTwoFock)) ≃ₗ[ℂ] WpTwoFock :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (gradingZN (rank (latP 2))))
    (gradingZN_isInternal (rank (latP 2)))

/-- Projection to one oscillator level. -/
def wpTwoCosetBosonProj (w : ℤ) : WpTwoFock →ₗ[ℂ] WpTwoFock :=
  (gradingZN (rank (latP 2)) w).subtype.comp
    ((DirectSum.component ℂ ℤ
      (fun n => (gradingZN (rank (latP 2)) n : Submodule ℂ WpTwoFock)) w).comp
      wpTwoCosetBosonEquiv.symm.toLinearMap)

theorem wpTwoCosetBosonProj_same {w : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) w) : wpTwoCosetBosonProj w p = p := by
  rw [wpTwoCosetBosonProj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  change ((wpTwoCosetBosonEquiv.symm p) w : WpTwoFock) = p
  rw [wpTwoCosetBosonEquiv, DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem _ hp]

theorem wpTwoCosetBosonProj_of_ne {w w' : ℤ} (hww : w ≠ w') {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) w') : wpTwoCosetBosonProj w p = 0 := by
  rw [wpTwoCosetBosonProj, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← DirectSum.apply_eq_component]
  change ((wpTwoCosetBosonEquiv.symm p) w : WpTwoFock) = 0
  rw [wpTwoCosetBosonEquiv,
    DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne _ hww.symm hp]
  rfl

/-- Retraction detecting one bigraded piece. -/
def wpTwoCosetBigradingDetector (w : ℤ) (q : WpTwoCosetCharge) :
    WpTwoCosetCarrier →ₗ[ℂ] WpTwoFock :=
  (wpTwoCosetBosonProj w).comp (wpTwoCosetChargeCoord q)

theorem wpTwoCosetBigradingDetector_state {w : ℤ} (q r : WpTwoCosetCharge) {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) w) :
    wpTwoCosetBigradingDetector w q (wpTwoCosetState p r) = if q = r then p else 0 := by
  rw [wpTwoCosetBigradingDetector, LinearMap.comp_apply, wpTwoCosetChargeCoord_state]
  by_cases h : q = r
  · rw [if_pos h, wpTwoCosetBosonProj_same hp]
  · rw [if_neg h, map_zero]

theorem wpTwoCosetBigrading_le_detectorKer_of_ne
    (w : ℤ) (q : WpTwoCosetCharge) (w' : ℤ) (q' : WpTwoCosetCharge)
    (hne : (w', q') ≠ (w, q)) :
    wpTwoCosetBigrading (w', q') ≤ LinearMap.ker (wpTwoCosetBigradingDetector w q) := by
  rintro x ⟨p, hp, rfl⟩
  rw [LinearMap.mem_ker, wpTwoCosetBigradingDetector, LinearMap.comp_apply,
    wpTwoCosetStateMap_apply, wpTwoCosetChargeCoord_state]
  by_cases hq : q = q'
  · subst q'
    have hw : w ≠ w' := fun h => hne (by rw [h])
    rw [if_pos rfl, wpTwoCosetBosonProj_of_ne hw hp]
  · rw [if_neg hq, map_zero]

theorem wpTwoCosetBigrading_iSupIndep : iSupIndep wpTwoCosetBigrading := by
  rw [iSupIndep_def]
  rintro ⟨w, q⟩
  rw [Submodule.disjoint_def]
  intro x hx hxsup
  obtain ⟨p, hp, hpx⟩ := hx
  have hker : (⨆ j, ⨆ (_ : j ≠ (w, q)), wpTwoCosetBigrading j) ≤
      LinearMap.ker (wpTwoCosetBigradingDetector w q) := by
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    exact wpTwoCosetBigrading_le_detectorKer_of_ne w q j.1 j.2 (by simpa using hj)
  have hx0 : wpTwoCosetBigradingDetector w q x = 0 := by
    rw [← LinearMap.mem_ker]
    exact hker hxsup
  have hxp : wpTwoCosetBigradingDetector w q x = p := by
    rw [← hpx, wpTwoCosetStateMap_apply]
    simpa using (wpTwoCosetBigradingDetector_state (w := w) q q hp)
  rw [hxp] at hx0
  rw [← hpx, hx0, map_zero]

theorem wpTwoCosetStateMap_mem_iSup (q : WpTwoCosetCharge) (p : WpTwoFock) :
    wpTwoCosetStateMap q p ∈ iSup wpTwoCosetBigrading := by
  have hmem : wpTwoCosetStateMap q p ∈
      (⨆ w : ℤ, wpTwoCosetBigrading (w, q)) := by
    have hmap : (⨆ w : ℤ, gradingZN (rank (latP 2)) w).map (wpTwoCosetStateMap q) =
        ⨆ w : ℤ, wpTwoCosetBigrading (w, q) := by
      rw [Submodule.map_iSup]
      rfl
    have hp : p ∈ ⨆ w : ℤ, gradingZN (rank (latP 2)) w := by
      rw [gradingZN_iSup_eq_top (rank (latP 2))]
      trivial
    have : wpTwoCosetStateMap q p ∈
        (⨆ w : ℤ, gradingZN (rank (latP 2)) w).map (wpTwoCosetStateMap q) :=
      Submodule.mem_map_of_mem hp
    rwa [hmap] at this
  exact (iSup_le (fun w => le_iSup wpTwoCosetBigrading (w, q))) hmem

theorem wpTwoCosetBigrading_iSup_eq_top : iSup wpTwoCosetBigrading = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ WpTwoFock WpTwoCosetChargeLine,
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction_linear with
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g₁ g₂ h₁ h₂ => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h₁ h₂
  | single q c =>
      rw [show (Finsupp.single q c : WpTwoCosetChargeLine) = c • wpTwoCosetChargeBasis q by
        rw [wpTwoCosetChargeBasis, Finsupp.smul_single, smul_eq_mul, mul_one],
        TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ c (wpTwoCosetStateMap_mem_iSup q p)

/-- The oscillator/shifted-charge bigrading is an internal direct sum. -/
theorem wpTwoCosetBigrading_isInternal : DirectSum.IsInternal wpTwoCosetBigrading :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    wpTwoCosetBigrading_iSupIndep wpTwoCosetBigrading_iSup_eq_top

/-! ## Collapse to the background-charge grading -/

/-- The integer conformal-weight grading of the shifted carrier. -/
def wpTwoCosetGrading (k : ℤ) : Submodule ℂ WpTwoCosetCarrier :=
  ⨆ q : WpTwoCosetCharge,
    wpTwoCosetBigrading (k - wpTwoCosetGroundWeight q, q)

theorem wpTwoCosetBigrading_eq_bot_of_neg {w : ℤ} (q : WpTwoCosetCharge) (hw : w < 0) :
    wpTwoCosetBigrading (w, q) = ⊥ := by
  rw [wpTwoCosetBigrading, gradingZN_of_neg hw, Submodule.map_bot]

theorem wpTwoCosetBigrading_le_grading (w : ℤ) (q : WpTwoCosetCharge) :
    wpTwoCosetBigrading (w, q) ≤
      wpTwoCosetGrading (w + wpTwoCosetGroundWeight q) := by
  have h : wpTwoCosetBigrading (w, q) =
      wpTwoCosetBigrading
        (w + wpTwoCosetGroundWeight q - wpTwoCosetGroundWeight q, q) := by
    rw [add_sub_cancel_right]
  rw [h]
  exact le_iSup (fun r => wpTwoCosetBigrading
    (w + wpTwoCosetGroundWeight q - wpTwoCosetGroundWeight r, r)) q

theorem wpTwoCosetGrading_iSup_eq_top : iSup wpTwoCosetGrading = ⊤ := by
  rw [eq_top_iff, ← wpTwoCosetBigrading_iSup_eq_top]
  refine iSup_le (fun wq => ?_)
  obtain ⟨w, q⟩ := wq
  exact le_trans (wpTwoCosetBigrading_le_grading w q)
    (le_iSup wpTwoCosetGrading (w + wpTwoCosetGroundWeight q))

def wpTwoCosetLevelMap (k : ℤ) : WpTwoCosetCharge → ℤ × WpTwoCosetCharge :=
  fun q => (k - wpTwoCosetGroundWeight q, q)

theorem range_wpTwoCosetLevelMap (k : ℤ) :
    Set.range (wpTwoCosetLevelMap k) =
      {p : ℤ × WpTwoCosetCharge | p.1 + wpTwoCosetGroundWeight p.2 = k} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp only [wpTwoCosetLevelMap, Set.mem_setOf_eq]
    ring
  · intro hp
    refine ⟨p.2, ?_⟩
    simp only [wpTwoCosetLevelMap, Set.mem_setOf_eq] at hp ⊢
    rw [Prod.ext_iff]
    exact ⟨by omega, rfl⟩

theorem wpTwoCosetGrading_eq_biSup (k : ℤ) :
    wpTwoCosetGrading k =
      ⨆ p ∈ {p : ℤ × WpTwoCosetCharge |
        p.1 + wpTwoCosetGroundWeight p.2 = k}, wpTwoCosetBigrading p := by
  rw [wpTwoCosetGrading, ← range_wpTwoCosetLevelMap k, iSup_range]
  rfl

def wpTwoCosetFiberPos (k : ℤ) : Set (ℤ × WpTwoCosetCharge) :=
  {p | p.1 + wpTwoCosetGroundWeight p.2 = k ∧ 0 ≤ p.1}

/-- The contributing charge labels at one total weight form a finite interval. -/
theorem wpTwoCosetFiberPos_finite (k : ℤ) : (wpTwoCosetFiberPos k).Finite := by
  let charges : Set WpTwoCosetCharge :=
    {q | -k ≤ q.label ∧ q.label ≤ k + 1}
  have hcharges : charges.Finite := by
    let f : WpTwoCosetCharge → ℤ := WpTwoCosetCharge.label
    have hinj : Function.Injective f := by
      intro q r h
      cases q
      cases r
      simp only [f] at h
      simp_all
    have hpre : (f ⁻¹' Set.Icc (-k) (k + 1)).Finite :=
      Set.Finite.preimage (Set.injOn_of_injective hinj) (Set.finite_Icc (-k) (k + 1))
    simpa [charges, f] using hpre
  apply Set.Finite.subset (Set.Finite.image (wpTwoCosetLevelMap k) hcharges)
  rintro ⟨w, q⟩ ⟨hwq, hw⟩
  simp only at hwq hw
  have hqk : wpTwoCosetGroundWeight q ≤ k := by omega
  have hlo : -k ≤ q.label := by
    simp only [wpTwoCosetGroundWeight] at hqk
    nlinarith [sq_nonneg q.label, sq_nonneg (q.label - 1)]
  have hhi : q.label ≤ k + 1 := by
    simp only [wpTwoCosetGroundWeight] at hqk
    nlinarith [sq_nonneg (q.label - 1)]
  refine ⟨q, ⟨hlo, hhi⟩, ?_⟩
  simp only [wpTwoCosetLevelMap]
  rw [Prod.ext_iff]
  exact ⟨by omega, rfl⟩

theorem wpTwoCosetGrading_eq_biSup_pos (k : ℤ) :
    wpTwoCosetGrading k =
      ⨆ p ∈ wpTwoCosetFiberPos k, wpTwoCosetBigrading p := by
  rw [wpTwoCosetGrading_eq_biSup k]
  apply le_antisymm
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    by_cases hpw : 0 ≤ p.1
    · exact le_biSup wpTwoCosetBigrading ⟨hp, hpw⟩
    · rw [show wpTwoCosetBigrading p = ⊥ from
          wpTwoCosetBigrading_eq_bot_of_neg p.2 (by omega : p.1 < 0)]
      exact bot_le
  · exact iSup_le (fun p => iSup_le (fun hp => le_biSup wpTwoCosetBigrading hp.1))

theorem iSup_ne_wpTwoCosetGrading_eq_biSup (k : ℤ) :
    (⨆ (k' : ℤ) (_ : k' ≠ k), wpTwoCosetGrading k') =
      ⨆ p ∈ {p : ℤ × WpTwoCosetCharge |
        p.1 + wpTwoCosetGroundWeight p.2 ≠ k}, wpTwoCosetBigrading p := by
  apply le_antisymm
  · refine iSup_le (fun k' => iSup_le (fun hk' => ?_))
    rw [wpTwoCosetGrading_eq_biSup k']
    refine iSup_le (fun p => iSup_le (fun hp => ?_))
    have hpk : p.1 + wpTwoCosetGroundWeight p.2 ≠ k := by
      simp only [Set.mem_setOf_eq] at hp
      rw [hp]
      exact hk'
    exact le_biSup wpTwoCosetBigrading (Set.mem_setOf_eq ▸ hpk)
  · refine iSup_le (fun p => iSup_le (fun hp => ?_))
    simp only [Set.mem_setOf_eq] at hp
    refine le_trans (wpTwoCosetBigrading_le_grading p.1 p.2) ?_
    calc
      wpTwoCosetGrading (p.1 + wpTwoCosetGroundWeight p.2) ≤
          ⨆ (_ : p.1 + wpTwoCosetGroundWeight p.2 ≠ k),
            wpTwoCosetGrading (p.1 + wpTwoCosetGroundWeight p.2) :=
        le_iSup (fun _ : p.1 + wpTwoCosetGroundWeight p.2 ≠ k =>
          wpTwoCosetGrading (p.1 + wpTwoCosetGroundWeight p.2)) hp
      _ ≤ _ := le_iSup (fun k' => ⨆ (_ : k' ≠ k), wpTwoCosetGrading k')
        (p.1 + wpTwoCosetGroundWeight p.2)

theorem wpTwoCosetGrading_iSupIndep : iSupIndep wpTwoCosetGrading := by
  rw [iSupIndep_def]
  intro k
  rw [wpTwoCosetGrading_eq_biSup_pos k, iSup_ne_wpTwoCosetGrading_eq_biSup k]
  apply iSupIndep.disjoint_biSup_biSup' wpTwoCosetBigrading_iSupIndep
  · rw [Set.disjoint_left]
    rintro p hp hp'
    simp only [Set.mem_setOf_eq] at hp'
    exact hp' hp.1
  · exact wpTwoCosetFiberPos_finite k

/-- The integer conformal-weight grading is an internal direct sum. -/
theorem wpTwoCosetGrading_isInternal : DirectSum.IsInternal wpTwoCosetGrading :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    wpTwoCosetGrading_iSupIndep wpTwoCosetGrading_iSup_eq_top

instance wpTwoCosetBigrading_finiteDimensional (p : ℤ × WpTwoCosetCharge) :
    FiniteDimensional ℂ (wpTwoCosetBigrading p) := by
  have : FiniteDimensional ℂ (gradingZN (rank (latP 2)) p.1) :=
    gradingZN_finrank (rank (latP 2)) p.1
  rw [wpTwoCosetBigrading]
  infer_instance

/-- Each integer conformal-weight piece is finite-dimensional. -/
theorem wpTwoCosetGrading_finrank (k : ℤ) :
    FiniteDimensional ℂ (wpTwoCosetGrading k) := by
  rw [wpTwoCosetGrading_eq_biSup_pos k, ← iSup_subtype'']
  have : Finite (wpTwoCosetFiberPos k) := wpTwoCosetFiberPos_finite k
  infer_instance

/-- The shifted carrier is bounded below by zero. -/
theorem wpTwoCosetGrading_positivity (k : ℤ) (hk : k < 0) :
    wpTwoCosetGrading k = ⊥ := by
  rw [wpTwoCosetGrading]
  refine le_bot_iff.mp (iSup_le (fun q => ?_))
  rw [wpTwoCosetBigrading_eq_bot_of_neg q (by
    have := wpTwoCosetGroundWeight_nonneg q
    omega : k - wpTwoCosetGroundWeight q < 0)]

/-! ## The complex-indexed form needed by a future ordinary module -/

/-- Extension of the integer grading by zero away from integer complex weights. -/
def wpTwoCosetWeight (a : ℂ) : Submodule ℂ WpTwoCosetCarrier :=
  ⨆ (k : ℤ) (_ : (k : ℂ) = a), wpTwoCosetGrading k

theorem wpTwoCosetWeight_cast (k : ℤ) :
    wpTwoCosetWeight (k : ℂ) = wpTwoCosetGrading k := by
  unfold wpTwoCosetWeight
  simp only [Int.cast_inj]
  exact iSup_iSup_eq_left

theorem wpTwoCosetWeight_eq_bot {a : ℂ} (hne : ∀ k : ℤ, (k : ℂ) ≠ a) :
    wpTwoCosetWeight a = ⊥ :=
  iSup_eq_bot.mpr (fun k => iSup_eq_bot.mpr (fun h => absurd h (hne k)))

theorem wpTwoCosetWeight_isInternal : DirectSum.IsInternal wpTwoCosetWeight := by
  have hZ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
    wpTwoCosetGrading).mp wpTwoCosetGrading_isInternal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · refine iSupIndep_extend wpTwoCosetGrading wpTwoCosetWeight (fun k => (k : ℂ)) ?_ ?_ hZ.1
    · intro a ha
      exact wpTwoCosetWeight_eq_bot (fun k hk => ha k hk)
    · exact wpTwoCosetWeight_cast
  · rw [← hZ.2]
    apply le_antisymm
    · refine iSup_le (fun a => ?_)
      unfold wpTwoCosetWeight
      exact iSup_le (fun k => iSup_le (fun _ => le_iSup wpTwoCosetGrading k))
    · exact iSup_le (fun k => le_iSup_of_le (k : ℂ) (by rw [wpTwoCosetWeight_cast k]))

theorem wpTwoCosetWeight_finrank (a : ℂ) :
    FiniteDimensional ℂ (wpTwoCosetWeight a) := by
  by_cases h : ∃ k : ℤ, (k : ℂ) = a
  · obtain ⟨k, rfl⟩ := h
    rw [wpTwoCosetWeight_cast]
    exact wpTwoCosetGrading_finrank k
  · rw [wpTwoCosetWeight_eq_bot (not_exists.mp h)]
    infer_instance

theorem wpTwoCosetWeight_boundedBelow :
    ∃ B : ℝ, ∀ a : ℂ, wpTwoCosetWeight a ≠ ⊥ → B ≤ a.re := by
  refine ⟨0, ?_⟩
  intro a ha
  by_cases h : ∃ k : ℤ, (k : ℂ) = a
  · obtain ⟨k, rfl⟩ := h
    rw [wpTwoCosetWeight_cast] at ha
    have hk : 0 ≤ k := by
      by_contra hc
      exact ha (wpTwoCosetGrading_positivity k (not_le.mp hc))
    simp only [Complex.intCast_re]
    exact_mod_cast hk
  · exact absurd (wpTwoCosetWeight_eq_bot (not_exists.mp h)) ha

/-! ## The short-momentum oscillator exponential -/

/-- Oscillator mode in the direction `delta=-alpha/2`.  On the orthonormal rank-one Fock
realization this scaling must be made at the generic-lattice `chargeOsc`; it is not the same
normalization as the older `LatExp.EEC` rank-one field. -/
def shortOsc (n : ℤ) : End ℂ WpTwoFock :=
  (-1 / 2 : ℂ) • chargeOsc (latP 2) (alphaP 2) n

theorem shortOsc_mem_gradingZN (n d : ℤ) {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortOsc n p ∈ gradingZN (rank (latP 2)) (d - n) := by
  rw [shortOsc, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (chargeOsc_mem_gradingZN (latP 2) (alphaP 2) n hp)

/-- Creation atom of `exp(delta)`. -/
def shortCreationAtom (m : ℕ) : End ℂ WpTwoFock :=
  shortOsc (-((m : ℤ) + 1))

/-- Annihilation atom of `exp(delta)`, including the minus sign in `E^+`. -/
def shortAnnihilationAtom (m : ℕ) : End ℂ WpTwoFock :=
  -(shortOsc ((m : ℤ) + 1))

/-- Newton coefficients of the creation exponential. -/
def shortCreationCoeff (N : ℕ) : End ℂ WpTwoFock :=
  newtonCoeff shortCreationAtom N

/-- Newton coefficients of the annihilation exponential. -/
def shortAnnihilationCoeff (N : ℕ) : End ℂ WpTwoFock :=
  newtonCoeff shortAnnihilationAtom N

@[simp] theorem shortCreationCoeff_zero : shortCreationCoeff 0 = LinearMap.id := by
  rw [shortCreationCoeff, newtonCoeff_zero]

@[simp] theorem shortAnnihilationCoeff_zero : shortAnnihilationCoeff 0 = LinearMap.id := by
  rw [shortAnnihilationCoeff, newtonCoeff_zero]

theorem shortCreationCoeff_succ (N : ℕ) :
    shortCreationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ •
      ∑ m ∈ Finset.range (N + 1),
        (shortCreationAtom m).comp (shortCreationCoeff (N - m)) := by
  rw [shortCreationCoeff, newtonCoeff_succ]
  rfl

theorem shortAnnihilationCoeff_succ (N : ℕ) :
    shortAnnihilationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ •
      ∑ m ∈ Finset.range (N + 1),
        (shortAnnihilationAtom m).comp (shortAnnihilationCoeff (N - m)) := by
  rw [shortAnnihilationCoeff, newtonCoeff_succ]
  rfl

/-- The creation coefficient of energy `N` raises oscillator degree by `N`. -/
theorem shortCreationCoeff_mem_gradingZN (N : ℕ) {d : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortCreationCoeff N p ∈ gradingZN (rank (latP 2)) (d + N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 =>
          rw [shortCreationCoeff_zero, LinearMap.id_apply, Nat.cast_zero, add_zero]
          exact hp
      | M + 1 =>
          rw [shortCreationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, shortCreationAtom]
          have hrec := ih (M - m) (by omega)
          have hmode := shortOsc_mem_gradingZN (-((m : ℤ) + 1))
            (d + (M - m : ℕ)) hrec
          have hgoal : d + (M - m : ℕ) - (-((m : ℤ) + 1)) =
              d + ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [hgoal] at hmode

/-- The annihilation coefficient of energy `N` lowers oscillator degree by `N`. -/
theorem shortAnnihilationCoeff_mem_gradingZN (N : ℕ) {d : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortAnnihilationCoeff N p ∈ gradingZN (rank (latP 2)) (d - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 =>
          rw [shortAnnihilationCoeff_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
          exact hp
      | M + 1 =>
          rw [shortAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, shortAnnihilationAtom, LinearMap.neg_apply]
          refine Submodule.neg_mem _ ?_
          have hrec := ih (M - m) (by omega)
          have hmode := shortOsc_mem_gradingZN ((m : ℤ) + 1)
            (d - (M - m : ℕ)) hrec
          have hgoal : d - (M - m : ℕ) - ((m : ℤ) + 1) =
              d - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [hgoal] at hmode

/-- The annihilation exponential fixes the Fock vacuum only in degree zero. -/
theorem shortAnnihilationCoeff_vacuum (N : ℕ) :
    shortAnnihilationCoeff N (vacuumN (rank (latP 2))) =
      if N = 0 then vacuumN (rank (latP 2)) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp
      | M + 1 =>
          rw [shortAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          have hz : ∀ m ∈ Finset.range (M + 1),
              ((shortAnnihilationAtom m).comp (shortAnnihilationCoeff (M - m)))
                (vacuumN (rank (latP 2))) = 0 := by
            intro m hm
            rw [LinearMap.comp_apply, ih (M - m) (by
              simp only [Finset.mem_range] at hm
              omega)]
            split_ifs with h
            · rw [shortAnnihilationAtom, LinearMap.neg_apply, shortOsc,
                LinearMap.smul_apply,
                chargeOsc_vacuum (latP 2) (alphaP 2) ((m : ℤ) + 1) (by omega),
                smul_zero, neg_zero]
            · rw [map_zero]
          rw [Finset.sum_eq_zero hz, smul_zero]
          simp

/-- Creation half of the short-momentum exponential. -/
def shortEminus : FormalDist (End ℂ WpTwoFock) :=
  fun t => if 0 ≤ t then shortCreationCoeff t.toNat else 0

/-- Annihilation half of the short-momentum exponential. -/
def shortEplus : FormalDist (End ℂ WpTwoFock) :=
  fun t => if t ≤ 0 then shortAnnihilationCoeff (-t).toNat else 0

theorem shortEminus_nonneg {t : ℤ} (ht : 0 ≤ t) :
    shortEminus t = shortCreationCoeff t.toNat := by rw [shortEminus, if_pos ht]

theorem shortEminus_neg {t : ℤ} (ht : t < 0) : shortEminus t = 0 := by
  rw [shortEminus, if_neg (by omega)]

theorem shortEplus_nonpos {t : ℤ} (ht : t ≤ 0) :
    shortEplus t = shortAnnihilationCoeff (-t).toNat := by rw [shortEplus, if_pos ht]

theorem shortEplus_pos {t : ℤ} (ht : 0 < t) : shortEplus t = 0 := by
  rw [shortEplus, if_neg (by omega)]

theorem shortEminus_isField : IsField shortEminus := by
  intro x
  exact ⟨0, fun n hn => by rw [shortEminus_neg hn, LinearMap.zero_apply]⟩

theorem shortEplus_isField : IsField shortEplus := by
  classical
  intro x
  obtain ⟨c, rfl⟩ := (gradingWN_isInternal (rank (latP 2))).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le c.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [shortEplus_nonpos hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := shortAnnihilationCoeff_mem_gradingZN (-n).toNat
    (mem_gradingZN_of_gradingWN (c w).2)
  rw [gradingZN_of_neg (by omega :
    (w : ℤ) - (((-n).toNat : ℕ) : ℤ) < 0), Submodule.mem_bot] at hmem
  exact hmem

/-- The normal-ordered oscillator dressing of `exp(delta)`. -/
def shortDress : FormalDist (End ℂ WpTwoFock) :=
  nprod shortEminus_isField shortEplus_isField

theorem shortDress_isField : IsField shortDress :=
  IsField.nprod shortEminus_isField shortEplus_isField

theorem shortEminus_memZ (t : ℤ) {d : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortEminus t p ∈ gradingZN (rank (latP 2)) (d + t) := by
  by_cases ht : 0 ≤ t
  · rw [shortEminus_nonneg ht]
    have h := shortCreationCoeff_mem_gradingZN t.toNat hp
    rwa [Int.toNat_of_nonneg ht] at h
  · rw [shortEminus_neg (by omega), LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem shortEplus_memZ (t : ℤ) {d : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortEplus t p ∈ gradingZN (rank (latP 2)) (d + t) := by
  by_cases ht : t ≤ 0
  · rw [shortEplus_nonpos ht]
    have h := shortAnnihilationCoeff_mem_gradingZN (-t).toNat hp
    rwa [show d - (((-t).toNat : ℕ) : ℤ) = d + t by omega] at h
  · rw [shortEplus_pos (by omega), LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- The full oscillator dressing coefficient `s` shifts oscillator degree by `s`. -/
theorem shortDress_mem_gradingZN (s : ℤ) {d : ℤ} {p : WpTwoFock}
    (hp : p ∈ gradingZN (rank (latP 2)) d) :
    shortDress s p ∈ gradingZN (rank (latP 2)) (d + s) := by
  rw [shortDress, nprod_apply]
  refine finsumFockN_mem_submodule (latP 2) _ _
    (normalOrdered_diag_support_finite shortEminus_isField shortEplus_isField s p)
    (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have h1 := shortEplus_memZ (s - m) hp
    have h2 := shortEminus_memZ m h1
    rwa [show d + (s - m) + m = d + s from by ring] at h2
  · rw [if_neg h0, Module.End.mul_apply]
    have h1 := shortEminus_memZ m hp
    have h2 := shortEplus_memZ (s - m) h1
    rwa [show d + m + (s - m) = d + s from by ring] at h2

/-! ## Assembly of the heterotypic short-screening field -/

/-- In the rank-one lattice, the charge `m alpha` is the carrier element `m`. -/
theorem sourceCharge_eq (m : ℤ) :
    m • alphaP 2 = (show (latP 2).carrier from m) := by
  change m * 1 = m
  ring

/-- The short momentum pairs with the source charge `m alpha` as `-2m`; hence the oscillator
coefficient at total power `t` is indexed by `t+2m`. -/
theorem shortMomentum_pair_source (m : ℤ) :
    (-1 / 2 : ℂ) *
        (((latP 2).form (alphaP 2) (m • alphaP 2) : ℤ) : ℂ) =
      -2 * (m : ℂ) := by
  rw [sourceCharge_eq]
  rw [latP_form]
  simp only [alphaP, mul_one]
  push_cast
  ring

/-- Sectorwise family used to assemble `Y(exp(delta),z) : V_{L_2} -> V_{L_2+delta}`. -/
def shortScreeningFam (t : ℤ) (m : (latP 2).carrier) :
    ℂ →ₗ[ℂ] (WpTwoFock →ₗ[ℂ] WpTwoCosetCarrier) :=
  LinearMap.toSpanSingleton ℂ (WpTwoFock →ₗ[ℂ] WpTwoCosetCarrier)
    (((TensorProduct.mk ℂ WpTwoFock WpTwoCosetChargeLine).flip
      (wpTwoCosetChargeBasis (wpTwoCosetCharge (show ℤ from m)))).comp
      (shortDress (t + 2 * (show ℤ from m))))

/-- The short-screening current as an integer-power heterotypic field. -/
def shortScreeningField :
    FormalDist (LatModuleGen (latP 2) →ₗ[ℂ] WpTwoCosetCarrier) :=
  fun t => TensorProduct.lift (Finsupp.lsum ℂ (shortScreeningFam t)).flip

/-- Defining action on a charged Fock basis state. -/
theorem shortScreeningField_latStateGen
    (t m : ℤ) (p : WpTwoFock) :
    shortScreeningField t (latStateGen (latP 2) p m) =
      wpTwoCosetState (shortDress (t + 2 * m) p) (wpTwoCosetCharge m) := by
  rw [shortScreeningField, latStateGen, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (shortScreeningFam t)) (eGen (latP 2) m) p = _
  rw [eGen, Finsupp.lsum_single, shortScreeningFam, LinearMap.toSpanSingleton_apply,
    one_smul, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

/-- The short-screening current is lower truncated on every source state. -/
theorem shortScreeningField_isHeterotypicField :
    IsHeterotypicField shortScreeningField := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => map_zero _⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero =>
          refine ⟨0, fun n _ => ?_⟩
          erw [TensorProduct.tmul_zero]
          exact map_zero _
      | add g₁ g₂ h₁ h₂ =>
          obtain ⟨B₁, hB₁⟩ := h₁
          obtain ⟨B₂, hB₂⟩ := h₂
          refine ⟨min B₁ B₂, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add, map_add]
          rw [hB₁ n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB₂ n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single m a =>
          obtain ⟨B, hB⟩ := shortDress_isField p
          refine ⟨B - 2 * (show ℤ from m), fun t ht => ?_⟩
          rw [← Finsupp.smul_single_one]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen (latP 2) m = latStateGen (latP 2) p m from rfl,
            shortScreeningField_latStateGen]
          have hz := hB (t + 2 * (show ℤ from m)) (by omega)
          rw [hz, wpTwoCosetState, TensorProduct.zero_tmul, smul_zero]

/-- The first candidate Felder differential: the residue of the short-screening current. -/
def shortScreening : LatModuleGen (latP 2) →ₗ[ℂ] WpTwoCosetCarrier :=
  externalZeroMode shortScreeningField

@[simp] theorem shortScreening_eq_coeff_neg_one :
    shortScreening = shortScreeningField (-1) := by
  exact externalZeroMode_eq_coeff_neg_one shortScreeningField

theorem shortScreening_latStateGen (m : ℤ) (p : WpTwoFock) :
    shortScreening (latStateGen (latP 2) p m) =
      wpTwoCosetState (shortDress (-1 + 2 * m) p) (wpTwoCosetCharge m) := by
  rw [shortScreening_eq_coeff_neg_one, shortScreeningField_latStateGen]

/-- A heterotypic coefficient preserves the source charge label and adds the fixed coset shift
`-alpha/2`. -/
def ShiftsToWpTwoCoset
    (S : FormalDist (LatModuleGen (latP 2) →ₗ[ℂ] WpTwoCosetCarrier)) : Prop :=
  ∀ (m : (latP 2).carrier) (t : ℤ), ∀ x ∈ chargeSec (latP 2) m,
    S t x ∈ wpTwoCosetSector (wpTwoCosetCharge m)

theorem shortScreeningField_shiftsToCoset :
    ShiftsToWpTwoCoset shortScreeningField := by
  intro m t x hx
  obtain ⟨p, rfl⟩ := hx
  rw [← BgB.latStateGen_eq_mkEα, shortScreeningField_latStateGen]
  exact wpTwoCosetState_mem_sector _ _

theorem shortScreening_mem_cosetSector (m : (latP 2).carrier)
    (x : LatModuleGen (latP 2)) (hx : x ∈ chargeSec (latP 2) m) :
    shortScreening x ∈ wpTwoCosetSector (wpTwoCosetCharge m) := by
  rw [shortScreening_eq_coeff_neg_one]
  exact shortScreeningField_shiftsToCoset m (-1) x hx

/-! ## Exact preservation of the background-charge weight -/

/-- Arithmetic balance for the residue.  Its oscillator shift `-1+2m` exactly compensates the
difference between the source and shifted-coset ground weights. -/
theorem shortScreening_weight_balance (w m : ℤ) :
    w + (-1 + 2 * m) + wpTwoCosetGroundWeight (wpTwoCosetCharge m) =
      w + qZP 2 m := by
  simp only [wpTwoCosetGroundWeight, wpTwoCosetCharge, qZP]
  ring

/-- On one source bigraded piece, the residue lands in the same total deformed weight. -/
theorem shortScreening_bigrading_mem (w m : ℤ) {x : LatModuleGen (latP 2)}
    (hx : x ∈ bigradα (latP 2) (w, m)) :
    shortScreening x ∈ wpTwoCosetGrading (w + qZP 2 m) := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [← BgB.latStateGen_eq_mkEα, shortScreening_latStateGen]
  have hdress := shortDress_mem_gradingZN (-1 + 2 * m) hp
  have hbig : wpTwoCosetState (shortDress (-1 + 2 * m) p) (wpTwoCosetCharge m) ∈
      wpTwoCosetBigrading (w + (-1 + 2 * m), wpTwoCosetCharge m) :=
    ⟨_, hdress, rfl⟩
  have hle := wpTwoCosetBigrading_le_grading
    (w + (-1 + 2 * m)) (wpTwoCosetCharge m) hbig
  rwa [shortScreening_weight_balance] at hle

/-- The residue preserves every integer deformed weight of the ambient lattice carrier. -/
theorem shortScreening_preserves_gradTrip (k : ℤ) (x : LatModuleGen (latP 2))
    (hx : x ∈ gradTrip 2 k) : shortScreening x ∈ wpTwoCosetGrading k := by
  rw [gradTrip_eq_iSup] at hx
  refine Submodule.iSup_induction
    (fun m : (latP 2).carrier => bigradα (latP 2) (k - qZP 2 m, m))
    (motive := fun y => shortScreening y ∈ wpTwoCosetGrading k) hx ?_ ?_ ?_
  · intro m y hy
    have h := shortScreening_bigrading_mem (k - qZP 2 m) m hy
    simpa only [sub_add_cancel] using h
  · change shortScreening (0 : LatModuleGen (latP 2)) ∈ wpTwoCosetGrading k
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- Weight preservation in the exact complex-indexed form expected of a future ordinary-module
homomorphism.  This theorem only compares the already constructed gradings; it does not assert a
module action on the target. -/
theorem shortScreening_preserves_weight (hp : 1 ≤ 2) (a : ℂ)
    (x : LatModuleGen (latP 2))
    (hx : x ∈ (Wp.tripletAmbientOrdModuleTwo hp).weight a) :
    shortScreening x ∈ wpTwoCosetWeight a := by
  by_cases h : ∃ k : ℤ, (k : ℂ) = a
  · obtain ⟨k, rfl⟩ := h
    change x ∈ adjWeight (tripletLatticeVOA 2 hp) (k : ℂ) at hx
    rw [adjWeight_cast] at hx
    change x ∈ gradTrip 2 k at hx
    rw [wpTwoCosetWeight_cast]
    exact shortScreening_preserves_gradTrip k x hx
  · have hx0 : x = 0 := by
      change x ∈ adjWeight (tripletLatticeVOA 2 hp) a at hx
      rw [adjWeight_eq_bot _ (not_exists.mp h), Submodule.mem_bot] at hx
      exact hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

end
end VOA.LatGen.WpTwoFelderCarrier
