/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSPiTransverse

/-!
# The charge-minus-one isotropic exponential for inverse DS

The lowering current in the inverse-DS realization contains the lattice field
`exp(-eta)`.  The first Pi construction only supplied `exp(eta)`.  This file constructs the
opposite-charge dressing directly from the same null Heisenberg modes.  It does not use a
positive-definite lattice, a conformal grading, or a reconstructed vertex algebra.

The main results are lower truncation and the exact vacuum-creation formula.  Locality with the
positive-charge exponential is proved in the following field-OPE layer; separating the two files
keeps this basic construction usable independently of the eventual NearVOA reconstruction.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDSPi

open scoped BigOperators TensorProduct
open Module (End)

noncomputable section

/-! ## Opposite-charge oscillator halves -/

/-- Creation atoms for charge `-eta`. -/
def etaNegCreationAtom (m : ℕ) : End ℂ HyperFock :=
  -(etaOsc (-((m : ℤ) + 1)))

/-- Annihilation atoms for charge `-eta`; the two minus signs in the exponential cancel. -/
def etaNegAnnihilationAtom (m : ℕ) : End ℂ HyperFock :=
  etaOsc ((m : ℤ) + 1)

/-- Newton coefficients of the charge-minus-one creation exponential. -/
noncomputable def etaNegCreationCoeff (N : ℕ) : End ℂ HyperFock :=
  newtonCoeff etaNegCreationAtom N

/-- Newton coefficients of the charge-minus-one annihilation exponential. -/
noncomputable def etaNegAnnihilationCoeff (N : ℕ) : End ℂ HyperFock :=
  newtonCoeff etaNegAnnihilationAtom N

@[simp] theorem etaNegCreationCoeff_zero :
    etaNegCreationCoeff 0 = LinearMap.id := by
  rw [etaNegCreationCoeff, newtonCoeff_zero]

@[simp] theorem etaNegAnnihilationCoeff_zero :
    etaNegAnnihilationCoeff 0 = LinearMap.id := by
  rw [etaNegAnnihilationCoeff, newtonCoeff_zero]

theorem etaNegCreationCoeff_succ (N : ℕ) :
    etaNegCreationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (etaNegCreationAtom m).comp (etaNegCreationCoeff (N - m)) := by
  rw [etaNegCreationCoeff, newtonCoeff_succ]
  rfl

theorem etaNegAnnihilationCoeff_succ (N : ℕ) :
    etaNegAnnihilationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (etaNegAnnihilationAtom m).comp (etaNegAnnihilationCoeff (N - m)) := by
  rw [etaNegAnnihilationCoeff, newtonCoeff_succ]
  rfl

/-- The charge-minus-one creation half, supported on nonnegative powers. -/
noncomputable def etaNegEminus : FormalDist (End ℂ HyperFock) :=
  fun t => if 0 ≤ t then etaNegCreationCoeff t.toNat else 0

/-- The charge-minus-one annihilation half, supported on nonpositive powers. -/
noncomputable def etaNegEplus : FormalDist (End ℂ HyperFock) :=
  fun t => if t ≤ 0 then etaNegAnnihilationCoeff (-t).toNat else 0

theorem etaNegEminus_nonneg {t : ℤ} (ht : 0 ≤ t) :
    etaNegEminus t = etaNegCreationCoeff t.toNat := by
  rw [etaNegEminus, if_pos ht]

theorem etaNegEminus_neg {t : ℤ} (ht : t < 0) : etaNegEminus t = 0 := by
  rw [etaNegEminus, if_neg (by omega)]

theorem etaNegEplus_nonpos {t : ℤ} (ht : t ≤ 0) :
    etaNegEplus t = etaNegAnnihilationCoeff (-t).toNat := by
  rw [etaNegEplus, if_pos ht]

theorem etaNegEplus_pos {t : ℤ} (ht : 0 < t) : etaNegEplus t = 0 := by
  rw [etaNegEplus, if_neg (by omega)]

theorem etaNegEminus_isField : IsField etaNegEminus := by
  intro x
  exact ⟨0, fun n hn => by rw [etaNegEminus_neg hn, LinearMap.zero_apply]⟩

/-- The opposite-charge annihilation coefficients fix the vacuum only in degree zero. -/
theorem etaNegAnnihilationCoeff_vacuum (N : ℕ) :
    etaNegAnnihilationCoeff N hyperVacuum = if N = 0 then hyperVacuum else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp
      | M + 1 =>
          rw [etaNegAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          have hz : ∀ m ∈ Finset.range (M + 1),
              ((etaNegAnnihilationAtom m).comp (etaNegAnnihilationCoeff (M - m)))
                hyperVacuum = 0 := by
            intro m hm
            rw [LinearMap.comp_apply, ih (M - m) (by
              simp only [Finset.mem_range] at hm
              omega)]
            split_ifs with h
            · rw [etaNegAnnihilationAtom,
                etaOsc_vacuum ((m : ℤ) + 1) (by omega)]
            · rw [map_zero]
          rw [Finset.sum_eq_zero hz, smul_zero]
          simp

theorem etaNegEplus_vacuum (t : ℤ) :
    etaNegEplus t hyperVacuum = if t = 0 then hyperVacuum else 0 := by
  rw [etaNegEplus]
  by_cases h : t ≤ 0
  · rw [if_pos h, etaNegAnnihilationCoeff_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬(-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬t = 0), LinearMap.zero_apply]

/-- The opposite-charge annihilation coefficient of energy `N` lowers polynomial weight by
`N`. -/
theorem etaNegAnnihilationCoeff_mem_gradingZN (N : ℕ) {w : ℕ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingWN 2 w) :
    etaNegAnnihilationCoeff N p ∈ HeisenbergN.gradingZN 2 ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 =>
          rw [etaNegAnnihilationCoeff_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
          exact HeisenbergN.mem_gradingZN_of_gradingWN hp
      | M + 1 =>
          rw [etaNegAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, etaNegAnnihilationAtom]
          have hrec := ih (M - m) (by omega)
          have hmode := etaOsc_mem_gradingZN ((m : ℤ) + 1) hrec
          have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1)
              = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [hgoal] at hmode

/-- The opposite-charge annihilation half is lower-truncated on every polynomial Fock state. -/
theorem etaNegEplus_isField : IsField etaNegEplus := by
  classical
  intro x
  obtain ⟨c, rfl⟩ := (HeisenbergN.gradingWN_isInternal 2).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le c.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [etaNegEplus_nonpos hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := etaNegAnnihilationCoeff_mem_gradingZN (-n).toNat (c w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega :
    (w : ℤ) - ((-n).toNat : ℤ) < 0), Submodule.mem_bot] at hmem
  exact hmem

/-! ## Dressing and charge-shifting field -/

/-- The normal-ordered charge-minus-one oscillator dressing. -/
noncomputable def etaNegDress : FormalDist (End ℂ HyperFock) :=
  nprod etaNegEminus_isField etaNegEplus_isField

theorem etaNegDress_isField : IsField etaNegDress :=
  IsField.nprod etaNegEminus_isField etaNegEplus_isField

/-- The charge-minus-one creation state at oscillator energy `N`. -/
noncomputable def etaNegSchurState (N : ℕ) : HyperFock :=
  etaNegCreationCoeff N hyperVacuum

@[simp] theorem etaNegSchurState_zero : etaNegSchurState 0 = hyperVacuum := by
  rw [etaNegSchurState, etaNegCreationCoeff_zero, LinearMap.id_apply]

theorem etaNegDress_vacuum (t : ℤ) :
    etaNegDress t hyperVacuum = if 0 ≤ t then etaNegSchurState t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered etaNegEminus etaNegEplus m (t - m) hyperVacuum = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, etaNegEplus_vacuum,
        if_neg (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, etaNegEminus_neg (by omega),
        LinearMap.zero_apply, map_zero]
  rw [etaNegDress, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply,
      show t - t = (0 : ℤ) from by ring, etaNegEplus_vacuum, if_pos rfl,
      etaNegEminus_nonneg ht, etaNegSchurState]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, etaNegEminus_neg (by omega),
      LinearMap.zero_apply, map_zero]

/-- Sectorwise family for the charge-minus-one exponential. -/
noncomputable def etaNegativeExponentialFam (t : ℤ) (q : ℤ) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiFockCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiFockCarrier)
    (((TensorProduct.mk ℂ HyperFock EtaChargeLine).flip (etaChargeBasis (q - 1))).comp
      (etaNegDress t))

/-- The charge-minus-one isotropic exponential formal distribution. -/
noncomputable def etaNegativeExponentialField : FormalDist (End ℂ PiFockCarrier) :=
  fun t => TensorProduct.lift (Finsupp.lsum ℂ (etaNegativeExponentialFam t)).flip

theorem etaNegativeExponentialField_piFockState (t q : ℤ) (p : HyperFock) :
    etaNegativeExponentialField t (piFockState p q)
      = piFockState (etaNegDress t p) (q - 1) := by
  rw [etaNegativeExponentialField, piFockState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (etaNegativeExponentialFam t)) (etaChargeBasis q) p = _
  rw [etaChargeBasis, Finsupp.lsum_single, etaNegativeExponentialFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

/-- The opposite-charge exponential is a genuine lower-truncated field. -/
theorem etaNegativeExponentialField_isField : IsField etaNegativeExponentialField := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (etaNegativeExponentialField n).map_zero⟩
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
            exact (etaNegativeExponentialField n).map_zero⟩
      | add g1 g2 h1 h2 =>
          obtain ⟨B1, hB1⟩ := h1
          obtain ⟨B2, hB2⟩ := h2
          refine ⟨min B1 B2, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [hB1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single q a =>
          obtain ⟨Bp, hBp⟩ := etaNegDress_isField p
          refine ⟨Bp, fun n hn => ?_⟩
          rw [(Finsupp.smul_single_one q a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] etaChargeBasis q = piFockState p q from rfl,
            etaNegativeExponentialField_piFockState, hBp n hn]
          rw [piFockState, TensorProduct.zero_tmul, smul_zero]

theorem etaNegativeExponentialField_vacuum (t : ℤ) :
    etaNegativeExponentialField t piFockVacuum
      = if 0 ≤ t then piFockState (etaNegSchurState t.toNat) (-1) else 0 := by
  rw [piFockVacuum, etaNegativeExponentialField_piFockState,
    show (0 : ℤ) - 1 = -1 from by ring, etaNegDress_vacuum]
  split_ifs with ht
  · rfl
  · rw [piFockState, TensorProduct.zero_tmul]

/-- The constant term creates the bare charge-minus-one state. -/
theorem etaNegativeExponentialField_creation_z0 :
    etaNegativeExponentialField 0 piFockVacuum = piFockExponential (-1) := by
  rw [etaNegativeExponentialField_vacuum, if_pos le_rfl, Int.toNat_zero,
    etaNegSchurState_zero]
  rfl

theorem etaNegativeExponentialField_mode_neg_one_vacuum :
    mode etaNegativeExponentialField (-1) piFockVacuum = piFockExponential (-1) := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring,
    etaNegativeExponentialField_creation_z0]

theorem etaNegativeExponentialField_creation_nonneg {n : ℤ} (hn : 0 ≤ n) :
    mode etaNegativeExponentialField n piFockVacuum = 0 := by
  rw [mode_apply, etaNegativeExponentialField_vacuum, if_neg (by omega)]

end
end InverseDSPi
end VOA
