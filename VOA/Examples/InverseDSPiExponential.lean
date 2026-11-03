/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiHeisenberg

/-!
# The first isotropic exponential field on the inverse-DS Pi carrier

This file constructs the charge-one exponential along the null direction `eta` on the honest
carrier from `InverseDSPiHeisenberg`.  Because all allowed charges are multiples of `eta`, the
pairing of the field charge with every charge sector is zero.  Consequently:

* the normalized cocycle on the charge line may be chosen to be the trivial cocycle;
* the zero-mode monomial has exponent zero and produces no sector-dependent mode shift;
* the creation and annihilation oscillator halves commute, since `eta` is null.

The resulting formal distribution is lower-truncated, creates the charge-one state, and is
self-local with bound zero.  This is still not a vertex algebra: reconstruction additionally
needs the transverse current relation, translation covariance, a conformal vector, and locality
for a generating family.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDSPi

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN

noncomputable section

/-! ## Newton coefficients for the two oscillator halves -/

/-- Creation-exponential coefficients for the null current. -/
noncomputable def etaCreationCoeff : ℕ → End ℂ HyperFock
  | 0 => LinearMap.id
  | N + 1 => ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (etaOsc (-((m : ℤ) + 1))).comp (etaCreationCoeff (N - m))

/-- Annihilation-exponential coefficients for the null current. -/
noncomputable def etaAnnihilationCoeff : ℕ → End ℂ HyperFock
  | 0 => LinearMap.id
  | N + 1 => ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (-(etaOsc ((m : ℤ) + 1))).comp (etaAnnihilationCoeff (N - m))

@[simp] theorem etaCreationCoeff_zero : etaCreationCoeff 0 = LinearMap.id := by
  simp only [etaCreationCoeff]

@[simp] theorem etaAnnihilationCoeff_zero : etaAnnihilationCoeff 0 = LinearMap.id := by
  simp only [etaAnnihilationCoeff]

theorem etaCreationCoeff_succ (N : ℕ) :
    etaCreationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (etaOsc (-((m : ℤ) + 1))).comp (etaCreationCoeff (N - m)) := by
  simp only [etaCreationCoeff]

theorem etaAnnihilationCoeff_succ (N : ℕ) :
    etaAnnihilationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (-(etaOsc ((m : ℤ) + 1))).comp (etaAnnihilationCoeff (N - m)) := by
  simp only [etaAnnihilationCoeff]

/-- Every pair of null-current modes commutes. -/
theorem etaOsc_commute (m n : ℤ) : Commute (etaOsc m) (etaOsc n) := by
  exact sub_eq_zero.mp (etaOsc_comm m n)

/-- Every creation coefficient commutes with every null-current mode. -/
theorem etaCreationCoeff_commute_osc (N : ℕ) (j : ℤ) :
    Commute (etaCreationCoeff N) (etaOsc j) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [etaCreationCoeff_zero]; exact Commute.one_left _
      | M + 1 =>
          rw [etaCreationCoeff_succ]
          refine Commute.smul_left ?_ _
          refine Commute.sum_left _ _ _ (fun m hm => ?_)
          refine Commute.mul_left (etaOsc_commute _ _) (ih (M - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

/-- Every annihilation coefficient commutes with every null-current mode. -/
theorem etaAnnihilationCoeff_commute_osc (N : ℕ) (j : ℤ) :
    Commute (etaAnnihilationCoeff N) (etaOsc j) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [etaAnnihilationCoeff_zero]; exact Commute.one_left _
      | M + 1 =>
          rw [etaAnnihilationCoeff_succ]
          refine Commute.smul_left ?_ _
          refine Commute.sum_left _ _ _ (fun m hm => ?_)
          refine Commute.mul_left (etaOsc_commute _ _).neg_left (ih (M - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

/-- Creation coefficients commute pairwise. -/
theorem etaCreationCoeff_commute (M N : ℕ) :
    Commute (etaCreationCoeff M) (etaCreationCoeff N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [etaCreationCoeff_zero]; exact Commute.one_right _
      | K + 1 =>
          rw [etaCreationCoeff_succ]
          refine Commute.smul_right ?_ _
          refine Commute.sum_right _ _ _ (fun m hm => ?_)
          refine Commute.mul_right (etaCreationCoeff_commute_osc M _)
            (ih (K - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

/-- Annihilation coefficients commute pairwise. -/
theorem etaAnnihilationCoeff_commute (M N : ℕ) :
    Commute (etaAnnihilationCoeff M) (etaAnnihilationCoeff N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [etaAnnihilationCoeff_zero]; exact Commute.one_right _
      | K + 1 =>
          rw [etaAnnihilationCoeff_succ]
          refine Commute.smul_right ?_ _
          refine Commute.sum_right _ _ _ (fun m hm => ?_)
          refine Commute.mul_right (etaAnnihilationCoeff_commute_osc M _).neg_right
            (ih (K - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

/-- Creation and annihilation coefficients commute; this is precisely where nullness is used. -/
theorem etaCreationCoeff_commute_annihilation (M N : ℕ) :
    Commute (etaCreationCoeff M) (etaAnnihilationCoeff N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => rw [etaAnnihilationCoeff_zero]; exact Commute.one_right _
      | K + 1 =>
          rw [etaAnnihilationCoeff_succ]
          refine Commute.smul_right ?_ _
          refine Commute.sum_right _ _ _ (fun m hm => ?_)
          refine Commute.mul_right (etaCreationCoeff_commute_osc M _).neg_right
            (ih (K - m) ?_)
          simp only [Finset.mem_range] at hm
          omega

/-! ## Half fields and lower truncation -/

/-- The creation half, supported on nonnegative powers. -/
noncomputable def etaEminus : FormalDist (End ℂ HyperFock) :=
  fun t => if 0 ≤ t then etaCreationCoeff t.toNat else 0

/-- The annihilation half, supported on nonpositive powers. -/
noncomputable def etaEplus : FormalDist (End ℂ HyperFock) :=
  fun t => if t ≤ 0 then etaAnnihilationCoeff (-t).toNat else 0

theorem etaEminus_nonneg {t : ℤ} (ht : 0 ≤ t) :
    etaEminus t = etaCreationCoeff t.toNat := by rw [etaEminus, if_pos ht]

theorem etaEminus_neg {t : ℤ} (ht : t < 0) : etaEminus t = 0 := by
  rw [etaEminus, if_neg (by omega)]

theorem etaEplus_nonpos {t : ℤ} (ht : t ≤ 0) :
    etaEplus t = etaAnnihilationCoeff (-t).toNat := by rw [etaEplus, if_pos ht]

theorem etaEplus_pos {t : ℤ} (ht : 0 < t) : etaEplus t = 0 := by
  rw [etaEplus, if_neg (by omega)]

theorem etaEminus_isField : IsField etaEminus := by
  intro x
  exact ⟨0, fun n hn => by rw [etaEminus_neg hn, LinearMap.zero_apply]⟩

/-- The annihilation coefficients fix the vacuum only in degree zero. -/
theorem etaAnnihilationCoeff_vacuum (N : ℕ) :
    etaAnnihilationCoeff N hyperVacuum = if N = 0 then hyperVacuum else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp
      | M + 1 =>
          rw [etaAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          have hz : ∀ m ∈ Finset.range (M + 1),
              ((-(etaOsc ((m : ℤ) + 1))).comp (etaAnnihilationCoeff (M - m)))
                hyperVacuum = 0 := by
            intro m hm
            rw [LinearMap.comp_apply, ih (M - m) (by simp only [Finset.mem_range] at hm; omega)]
            split_ifs with h
            · rw [LinearMap.neg_apply, etaOsc_vacuum ((m : ℤ) + 1) (by omega), neg_zero]
            · rw [map_zero]
          rw [Finset.sum_eq_zero hz, smul_zero]
          simp

/-- The annihilation half fixes the vacuum in degree zero and vanishes in every other degree. -/
theorem etaEplus_vacuum (t : ℤ) :
    etaEplus t hyperVacuum = if t = 0 then hyperVacuum else 0 := by
  rw [etaEplus]
  by_cases h : t ≤ 0
  · rw [if_pos h, etaAnnihilationCoeff_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬(-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬t = 0), LinearMap.zero_apply]

/-- Directional modes respect the standard polynomial weight grading. -/
theorem etaOsc_mem_gradingZN (n : ℤ) {d : ℤ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingZN 2 d) :
    etaOsc n p ∈ HeisenbergN.gradingZN 2 (d - n) := by
  rw [etaOsc, directionOsc, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have h := HeisenbergN.oscN_mem_gradingZN 2 1 a n hp
    rwa [Int.toNat_of_nonneg hd] at h
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact HeisenbergN.zero_mem_gradingZN 2 _

/-- The annihilation coefficient of energy `N` lowers polynomial weight by `N`. -/
theorem etaAnnihilationCoeff_mem_gradingZN (N : ℕ) {w : ℕ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingWN 2 w) :
    etaAnnihilationCoeff N p ∈ HeisenbergN.gradingZN 2 ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 =>
          rw [etaAnnihilationCoeff_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
          exact HeisenbergN.mem_gradingZN_of_gradingWN hp
      | M + 1 =>
          rw [etaAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, LinearMap.neg_apply]
          refine Submodule.neg_mem _ ?_
          have hrec := ih (M - m) (by omega)
          have h := etaOsc_mem_gradingZN ((m : ℤ) + 1) hrec
          have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1)
              = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [hgoal] at h

/-- The annihilation half is lower-truncated on every polynomial Fock state. -/
theorem etaEplus_isField : IsField etaEplus := by
  classical
  intro x
  obtain ⟨c, rfl⟩ := (HeisenbergN.gradingWN_isInternal 2).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le c.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [etaEplus_nonpos hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := etaAnnihilationCoeff_mem_gradingZN (-n).toNat (c w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega :
    (w : ℤ) - ((-n).toNat : ℤ) < 0), Submodule.mem_bot] at hmem
  exact hmem

/-! ## The null boson dressing -/

/-- The normal-ordered null exponential dressing. -/
noncomputable def etaDress : FormalDist (End ℂ HyperFock) :=
  nprod etaEminus_isField etaEplus_isField

theorem etaDress_isField : IsField etaDress :=
  IsField.nprod etaEminus_isField etaEplus_isField

/-- The creation state of oscillator energy `N`. -/
noncomputable def etaSchurState (N : ℕ) : HyperFock := etaCreationCoeff N hyperVacuum

@[simp] theorem etaSchurState_zero : etaSchurState 0 = hyperVacuum := by
  rw [etaSchurState, etaCreationCoeff_zero, LinearMap.id_apply]

/-- The dressing creates the null-current Schur tower from the vacuum. -/
theorem etaDress_vacuum (t : ℤ) :
    etaDress t hyperVacuum = if 0 ≤ t then etaSchurState t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered etaEminus etaEplus m (t - m) hyperVacuum = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, etaEplus_vacuum,
        if_neg (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, etaEminus_neg (by omega),
        LinearMap.zero_apply, map_zero]
  rw [etaDress, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply, show t - t = (0 : ℤ) from by ring,
      etaEplus_vacuum, if_pos rfl,
      etaEminus_nonneg ht, etaSchurState]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, etaEminus_neg (by omega),
      LinearMap.zero_apply, map_zero]

/-! ## Exact commutativity of the null dressing -/

theorem etaEminus_comm (a b : ℤ) :
    (etaEminus a).comp (etaEminus b) = (etaEminus b).comp (etaEminus a) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [etaEminus_nonneg ha, etaEminus_nonneg hb]
      exact (etaCreationCoeff_commute _ _).eq
    · rw [etaEminus_neg (t := b) (by omega)]
      simp
  · rw [etaEminus_neg (by omega)]
    simp

theorem etaEplus_comm (a b : ℤ) :
    (etaEplus a).comp (etaEplus b) = (etaEplus b).comp (etaEplus a) := by
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · rw [etaEplus_nonpos ha, etaEplus_nonpos hb]
      exact (etaAnnihilationCoeff_commute _ _).eq
    · rw [etaEplus_pos (t := b) (by omega)]
      simp
  · rw [etaEplus_pos (by omega)]
    simp

/-- The two halves commute exactly, rather than acquiring a contraction factor. -/
theorem etaEplus_comm_Eminus (a b : ℤ) :
    (etaEplus a).comp (etaEminus b) = (etaEminus b).comp (etaEplus a) := by
  by_cases ha : a ≤ 0
  · by_cases hb : 0 ≤ b
    · rw [etaEplus_nonpos ha, etaEminus_nonneg hb]
      exact (etaCreationCoeff_commute_annihilation _ _).symm.eq
    · rw [etaEminus_neg (by omega)]
      simp
  · rw [etaEplus_pos (by omega)]
    simp

theorem etaEminus_commute_osc (a m : ℤ) : Commute (etaEminus a) (etaOsc m) := by
  by_cases ha : 0 ≤ a
  · rw [etaEminus_nonneg ha]
    exact etaCreationCoeff_commute_osc _ _
  · rw [etaEminus_neg (by omega)]
    exact Commute.zero_left _

theorem etaEplus_commute_osc (a m : ℤ) : Commute (etaEplus a) (etaOsc m) := by
  by_cases ha : a ≤ 0
  · rw [etaEplus_nonpos ha]
    exact etaAnnihilationCoeff_commute_osc _ _
  · rw [etaEplus_pos (by omega)]
    exact Commute.zero_left _

theorem etaEplus_shift_support_finite (b : ℤ) (y : HyperFock) :
    (Function.support (fun q : ℤ => etaEplus (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := etaEplus_isField y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [etaEplus_pos (show 0 < b - q by omega)]; rfl)
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

theorem etaDress_marg_support_finite (s : ℤ) (x : HyperFock) :
    (Function.support (fun q : ℤ => etaEminus q (etaEplus (s - q) x))).Finite := by
  apply Set.Finite.subset (etaEplus_shift_support_finite s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (by rw [h, map_zero])

/-- The dressing is the honest coefficient convolution of its two halves. -/
theorem etaDress_apply_conv (s : ℤ) (x : HyperFock) :
    etaDress s x = ∑ᶠ m : ℤ, etaEminus m (etaEplus (s - m) x) := by
  rw [etaDress, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, etaEminus_neg (by omega)]
    simp

theorem etaEplusEplus_support_finite (a b : ℤ) (x : HyperFock) :
    (Function.support
      (fun pq : ℤ × ℤ => etaEplus (a - pq.1) (etaEplus (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => etaEplus (b - q) x) with hSq
  have hSqfin : Sq.Finite := etaEplus_shift_support_finite b x
  set P := ⋃ q ∈ Sq, Function.support (fun p : ℤ => etaEplus (a - p) (etaEplus (b - q) x))
    with hP
  have hPfin : P.Finite := hSqfin.biUnion
    (fun q _ => etaEplus_shift_support_finite a (etaEplus (b - q) x))
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]
    intro h
    exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]
  exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)

theorem etaFourfold_support_finite (a b : ℤ) (x : HyperFock) :
    (Function.support (fun pq : ℤ × ℤ =>
      etaEminus pq.1 (etaEminus pq.2
        (etaEplus (a - pq.1) (etaEplus (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (etaEplusEplus_support_finite a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h
  exact hpq (by rw [h, map_zero, map_zero])

/-- The symmetric four-fold normal ordering of two null dressings. -/
noncomputable def etaFourfold (C D : ℤ) (x : HyperFock) : HyperFock :=
  ∑ᶠ pq : ℤ × ℤ,
    etaEminus pq.1 (etaEminus pq.2
      (etaEplus (C - pq.1) (etaEplus (D - pq.2) x)))

theorem etaFourfold_symm (C D : ℤ) (x : HyperFock) :
    etaFourfold C D x = etaFourfold D C x := by
  rw [etaFourfold, etaFourfold, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => etaEminus pq.1 (etaEminus pq.2
      (etaEplus (D - pq.1) (etaEplus (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hM := DFunLike.congr_fun (etaEminus_comm p q)
    (etaEplus (C - p) (etaEplus (D - q) x))
  have hP := DFunLike.congr_fun (etaEplus_comm (C - p) (D - q)) x
  simp only [LinearMap.comp_apply] at hM hP
  rw [hM, hP]

theorem etaFourfold_eq_nested (C D : ℤ) (x : HyperFock) :
    etaFourfold C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      etaEminus p (etaEminus q
        (etaEplus (C - p) (etaEplus (D - q) x))) := by
  rw [etaFourfold, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => etaEminus pq.1 (etaEminus pq.2
      (etaEplus (C - pq.1) (etaEplus (D - pq.2) x))))]
  rw [finsum_curry _ ((etaFourfold_support_finite C D x).preimage
    ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

theorem etaDress_nested (c d : ℤ) (x : HyperFock) :
    etaDress c (etaDress d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      etaEminus p (etaEplus (c - p)
        (etaEminus q (etaEplus (d - q) x))) := by
  rw [etaDress_apply_conv d x,
    map_finsum (etaDress c) (etaDress_marg_support_finite d x)]
  refine finsum_congr fun q => ?_
  rw [etaDress_apply_conv c]

/-- Nullness removes the FLM contraction entirely, so the dressing coefficients commute. -/
theorem etaDress_comm_apply (c d : ℤ) (x : HyperFock) :
    etaDress c (etaDress d x) = etaDress d (etaDress c x) := by
  have hnest : (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      etaEminus p (etaEplus (c - p) (etaEminus q (etaEplus (d - q) x))))
      = etaFourfold c d x := by
    rw [etaFourfold_eq_nested]
    refine finsum_congr fun q => finsum_congr fun p => ?_
    have h := DFunLike.congr_fun (etaEplus_comm_Eminus (c - p) q)
      (etaEplus (d - q) x)
    simp only [LinearMap.comp_apply] at h
    rw [h]
  have hnest' : (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      etaEminus p (etaEplus (d - p) (etaEminus q (etaEplus (c - q) x))))
      = etaFourfold d c x := by
    rw [etaFourfold_eq_nested]
    refine finsum_congr fun q => finsum_congr fun p => ?_
    have h := DFunLike.congr_fun (etaEplus_comm_Eminus (d - p) q)
      (etaEplus (c - q) x)
    simp only [LinearMap.comp_apply] at h
    rw [h]
  rw [etaDress_nested, etaDress_nested, hnest, hnest', etaFourfold_symm]

theorem etaDress_comm (c d : ℤ) :
    (etaDress c).comp (etaDress d) = (etaDress d).comp (etaDress c) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  exact etaDress_comm_apply c d x

/-- Every null-current mode commutes with every coefficient of its exponential dressing. -/
theorem etaDress_commute_osc (t m : ℤ) : Commute (etaDress t) (etaOsc m) := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply]
  rw [etaDress_apply_conv t (etaOsc m p), etaDress_apply_conv t p,
    map_finsum (etaOsc m) (etaDress_marg_support_finite t p)]
  refine finsum_congr fun q => ?_
  have hp := DFunLike.congr_fun (etaEplus_commute_osc (t - q) m).eq p
  have hm := DFunLike.congr_fun (etaEminus_commute_osc q m).eq
    (etaEplus (t - q) p)
  simp only [Module.End.mul_apply] at hp hm
  rw [hp, hm]

/-! ## The charge-line shift and its exact cocycle -/

/-- The normalized cocycle on the isotropic rank-one charge line.  Since every pairing is zero,
the trivial cocycle has the required commutation sign. -/
def etaLineCocycle (_q _r : ℤ) : ℂ := 1

@[simp] theorem etaLineCocycle_apply (q r : ℤ) : etaLineCocycle q r = 1 := rfl

theorem etaLineCocycle_cocycle (q r s : ℤ) :
    etaLineCocycle q r * etaLineCocycle (q + r) s
      = etaLineCocycle r s * etaLineCocycle q (r + s) := by
  simp

theorem etaLineCocycle_comm (q r : ℤ) :
    etaLineCocycle q r = etaLineCocycle r q := by
  simp

/-- Translation by `q eta` on the charge-line group algebra. -/
noncomputable def etaShiftLine (q : ℤ) : Module.End ℂ EtaChargeLine :=
  Finsupp.lsum ℂ (fun r : ℤ => etaLineCocycle q r •
    (Finsupp.lsingle (q + r) : ℂ →ₗ[ℂ] EtaChargeLine))

@[simp] theorem etaShiftLine_basis (q r : ℤ) :
    etaShiftLine q (etaChargeBasis r) = etaChargeBasis (q + r) := by
  rw [etaShiftLine, etaChargeBasis, Finsupp.lsum_single, LinearMap.smul_apply,
    Finsupp.lsingle_apply, etaLineCocycle_apply, one_smul]
  rfl

/-- The charge shift on the full Pi Fock carrier. -/
noncomputable def etaShift (q : ℤ) : Module.End ℂ PiFockCarrier :=
  LinearMap.lTensor HyperFock (etaShiftLine q)

@[simp] theorem etaShift_piFockState (q r : ℤ) (p : HyperFock) :
    etaShift q (piFockState p r) = piFockState p (q + r) := by
  rw [etaShift, piFockState, LinearMap.lTensor_tmul, etaShiftLine_basis]
  rfl

/-- The `eta` zero mode is zero on every allowed charge sector. -/
noncomputable def etaZeroMode : Module.End ℂ PiFockCarrier := 0

@[simp] theorem etaZeroMode_piFockState (p : HyperFock) (q : ℤ) :
    etaZeroMode (piFockState p q) = 0 := by
  rw [etaZeroMode, LinearMap.zero_apply]

/-- The formal zero-mode exponent is identically zero on the charge line. -/
theorem eta_zeroMode_exponent (q : ℤ) : piLattice.form eta (etaCharge q) = 0 := by
  rw [piLattice_form]
  simp [eta]

/-! ## The charge-one isotropic exponential field -/

/-- The sectorwise linear family used to assemble the charge-one field.  There is no index shift:
the omitted exponent is exactly `eta_zeroMode_exponent`. -/
noncomputable def etaExponentialFam (t : ℤ) (q : ℤ) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiFockCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiFockCarrier)
    (((TensorProduct.mk ℂ HyperFock EtaChargeLine).flip (etaChargeBasis (q + 1))).comp
      (etaDress t))

/-- The charge-one isotropic exponential formal distribution on `PiFockCarrier`. -/
noncomputable def etaExponentialField : FormalDist (End ℂ PiFockCarrier) :=
  fun t => TensorProduct.lift (Finsupp.lsum ℂ (etaExponentialFam t)).flip

/-- Defining action on an oscillator state in charge sector `q eta`. -/
theorem etaExponentialField_piFockState (t q : ℤ) (p : HyperFock) :
    etaExponentialField t (piFockState p q)
      = piFockState (etaDress t p) (q + 1) := by
  rw [etaExponentialField, piFockState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (etaExponentialFam t)) (etaChargeBasis q) p = _
  rw [etaChargeBasis, Finsupp.lsum_single, etaExponentialFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

/-- The charge-one exponential is a genuine lower-truncated field on the tensor carrier. -/
theorem etaExponentialField_isField : IsField etaExponentialField := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (etaExponentialField n).map_zero⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero =>
          exact ⟨0, fun n _ => by
            erw [TensorProduct.tmul_zero]
            exact (etaExponentialField n).map_zero⟩
      | add g1 g2 h1 h2 =>
          obtain ⟨B1, hB1⟩ := h1
          obtain ⟨B2, hB2⟩ := h2
          refine ⟨min B1 B2, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [hB1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single q a =>
          obtain ⟨Bp, hBp⟩ := etaDress_isField p
          refine ⟨Bp, fun n hn => ?_⟩
          rw [(Finsupp.smul_single_one q a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] etaChargeBasis q = piFockState p q from rfl,
            etaExponentialField_piFockState, hBp n hn]
          rw [piFockState, TensorProduct.zero_tmul, smul_zero]

/-- The full creation series on the carrier vacuum. -/
theorem etaExponentialField_vacuum (t : ℤ) :
    etaExponentialField t piFockVacuum
      = if 0 ≤ t then piFockState (etaSchurState t.toNat) 1 else 0 := by
  rw [piFockVacuum, etaExponentialField_piFockState,
    show (0 : ℤ) + 1 = 1 from by ring, etaDress_vacuum]
  split_ifs with ht
  · rfl
  · rw [piFockState, TensorProduct.zero_tmul]

/-- The constant term creates the bare charge-one state. -/
theorem etaExponentialField_creation_z0 :
    etaExponentialField 0 piFockVacuum = piFockExponential 1 := by
  rw [etaExponentialField_vacuum, if_pos le_rfl, Int.toNat_zero,
    etaSchurState_zero]
  rfl

theorem etaExponentialField_mode_neg_one_vacuum :
    mode etaExponentialField (-1) piFockVacuum = piFockExponential 1 := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring,
    etaExponentialField_creation_z0]

/-- All nonnegative modes annihilate the vacuum. -/
theorem etaExponentialField_creation_nonneg {n : ℤ} (hn : 0 ≤ n) :
    mode etaExponentialField n piFockVacuum = 0 := by
  rw [mode_apply, etaExponentialField_vacuum, if_neg (by omega)]

/-- Pointwise exact commutativity on every pure charge state. -/
theorem etaExponentialField_bracket_piFockState (j k q : ℤ) (p : HyperFock) :
    bracketDist etaExponentialField etaExponentialField j k (piFockState p q) = 0 := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, etaExponentialField_piFockState]
  rw [etaDress_comm_apply, sub_self]

/-- The isotropic charge-one field commutes with itself as an operator-valued distribution. -/
theorem etaExponentialField_bracket_zero :
    bracketDist etaExponentialField etaExponentialField = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist etaExponentialField etaExponentialField j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single q a =>
          rw [(Finsupp.smul_single_one q a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] etaChargeBasis q = piFockState p q from rfl,
            etaExponentialField_bracket_piFockState, smul_zero]

/-- Self-locality has bound zero because the null exponential fields commute exactly. -/
theorem etaExponentialField_local :
    Local etaExponentialField etaExponentialField :=
  local_of_bracketDist_eq_zero etaExponentialField_bracket_zero

/-! ## The null current relation -/

/-- The null Heisenberg current lifted to the full Pi carrier. -/
noncomputable def etaCurrentField : FormalDist (End ℂ PiFockCarrier) :=
  fun j => liftHyperOsc (etaOsc (-j - 1))

@[simp] theorem etaCurrentField_piFockState (j q : ℤ) (p : HyperFock) :
    etaCurrentField j (piFockState p q)
      = piFockState (etaOsc (-j - 1) p) q := by
  exact liftHyperOsc_piFockState _ _ _

/-- The null current and the null exponential commute on every pure charge state. -/
theorem etaCurrentField_comm_exponential_piFockState (j t q : ℤ) (p : HyperFock) :
    bracketDist etaCurrentField etaExponentialField j t (piFockState p q) = 0 := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, etaCurrentField_piFockState,
    etaExponentialField_piFockState]
  have h := DFunLike.congr_fun (etaDress_commute_osc t (-j - 1)).eq p
  simp only [Module.End.mul_apply] at h
  rw [h, sub_self]

theorem etaCurrentField_comm_exponential_zero :
    bracketDist etaCurrentField etaExponentialField = 0 := by
  refine FormalDist₂.ext fun j t => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist etaCurrentField etaExponentialField j t y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single q a =>
          rw [(Finsupp.smul_single_one q a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] etaChargeBasis q = piFockState p q from rfl,
            etaCurrentField_comm_exponential_piFockState, smul_zero]

/-- The null current is mutually local with its charge-one exponential with bound zero. -/
theorem etaCurrentField_local_exponential :
    Local etaCurrentField etaExponentialField :=
  local_of_bracketDist_eq_zero etaCurrentField_comm_exponential_zero

end
end InverseDSPi
end VOA
