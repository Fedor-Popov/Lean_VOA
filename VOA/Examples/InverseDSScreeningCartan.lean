/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSScreeningCoset

/-!
# Cartan-current intertwining for the shifted screening field

The inverse-DS Cartan current has Pi direction `h = 2 mu`, where
`mu = xi + (k/4) eta`.  The screening momentum is
`nu = xi - (k/4) eta`, and `mu` is orthogonal to `nu`.  This file turns that scalar identity
into coefficientwise commutation of the concrete Newton dressing, includes the equal source and
target zero-mode actions, and proves the full heterotypic Cartan-current identity for every
half-power coefficient of `exp(nu)`.

Thus the `h` part of the three-current screening obstruction is solved on the Pi factor.  The
remaining `e` and `f` identities involve exponential-current cocycles and the Virasoro
intertwining field, respectively.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace ScreeningCoset

open Module (End)
open scoped BigOperators TensorProduct
open InverseDSPi
open HalfLattice

noncomputable section

/-! ## Orthogonal oscillator directions -/

theorem muNuOsc_commute (m n : ℤ) :
    Commute (directionOsc (muDirection boundaryLevel85) m)
      (directionOsc (nuDirection boundaryLevel85) n) := by
  have h := directionOsc_comm (muDirection boundaryLevel85)
    (nuDirection boundaryLevel85) m n
  rw [muDirection_nuDirection] at h
  have hzero :
      directionOsc (muDirection boundaryLevel85) m *
          directionOsc (nuDirection boundaryLevel85) n -
        directionOsc (nuDirection boundaryLevel85) n *
          directionOsc (muDirection boundaryLevel85) m = 0 := by
    simpa using h
  exact sub_eq_zero.mp hzero

theorem muOsc_commute_nuCreationAtom (r : ℤ) (m : ℕ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuCreationAtom m) :=
  muNuOsc_commute r (-((m : ℤ) + 1))

theorem muOsc_commute_nuAnnihilationAtom (r : ℤ) (m : ℕ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuAnnihilationAtom m) := by
  exact (muNuOsc_commute r ((m : ℤ) + 1)).neg_right

theorem muOsc_commute_nuCreationCoeff (r : ℤ) (N : ℕ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuCreationCoeff N) := by
  rw [nuCreationCoeff]
  exact commute_newtonCoeff _ _ (muOsc_commute_nuCreationAtom r) N

theorem muOsc_commute_nuAnnihilationCoeff (r : ℤ) (N : ℕ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuAnnihilationCoeff N) := by
  rw [nuAnnihilationCoeff]
  exact commute_newtonCoeff _ _ (muOsc_commute_nuAnnihilationAtom r) N

theorem muOsc_commute_nuEminus (r t : ℤ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuEminus t) := by
  by_cases ht : 0 ≤ t
  · rw [nuEminus_nonneg ht]
    exact muOsc_commute_nuCreationCoeff r _
  · rw [nuEminus_neg (by omega)]
    exact Commute.zero_right _

theorem muOsc_commute_nuEplus (r t : ℤ) :
    Commute (directionOsc (muDirection boundaryLevel85) r) (nuEplus t) := by
  by_cases ht : t ≤ 0
  · rw [nuEplus_nonpos ht]
    exact muOsc_commute_nuAnnihilationCoeff r _
  · rw [nuEplus_pos (by omega)]
    exact Commute.zero_right _

/-! ## Commutation with the full normal-ordered dressing -/

theorem nuEplus_shift_support_finite (b : ℤ) (y : HyperFock) :
    (Function.support (fun q : ℤ => nuEplus (b - q) y)).Finite := by
  obtain ⟨B₀, hB₀⟩ := nuEplus_isField y
  apply Set.Finite.subset (Set.finite_Icc b (b - B₀))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [nuEplus_pos (show 0 < b - q by omega)]; rfl)
  · by_contra h
    exact hq (hB₀ (b - q) (by omega))

theorem nuDress_marg_support_finite (s : ℤ) (x : HyperFock) :
    (Function.support (fun q : ℤ => nuEminus q (nuEplus (s - q) x))).Finite := by
  apply Set.Finite.subset (nuEplus_shift_support_finite s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (by rw [h, map_zero])

theorem nuDress_apply_conv (s : ℤ) (x : HyperFock) :
    nuDress s x = ∑ᶠ m : ℤ, nuEminus m (nuEplus (s - m) x) := by
  rw [nuDress, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, nuEminus_neg (by omega)]
    simp

/-- Orthogonality of `mu` and `nu` propagates from oscillator atoms to every coefficient of the
normal-ordered `nu` dressing. -/
theorem nuDress_commute_muOsc (t r : ℤ) :
    Commute (nuDress t) (directionOsc (muDirection boundaryLevel85) r) := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply]
  rw [nuDress_apply_conv t (directionOsc (muDirection boundaryLevel85) r p),
    nuDress_apply_conv t p,
    map_finsum (directionOsc (muDirection boundaryLevel85) r)
      (nuDress_marg_support_finite t p)]
  refine finsum_congr fun q => ?_
  have hp := DFunLike.congr_fun (muOsc_commute_nuEplus r (t - q)).eq p
  have hm := DFunLike.congr_fun (muOsc_commute_nuEminus r q).eq
    (nuEplus (t - q) p)
  simp only [Module.End.mul_apply] at hp hm
  rw [← hp, ← hm]

theorem nuHalfDress_commute_muOsc (t : ℤ) (q : HalfEtaCharge) (r : ℤ) :
    Commute (nuHalfDress t q) (directionOsc (muDirection boundaryLevel85) r) := by
  classical
  by_cases h : HalfPowerMatch t q
  · rw [nuHalfDress, dif_pos h]
    exact nuDress_commute_muOsc _ _
  · rw [nuHalfDress, dif_neg h]
    exact Commute.zero_left _

/-! ## Source and shifted-target Cartan currents -/

/-- Lift an oscillator operator to the source half-lattice Pi carrier. -/
def liftHalfOsc (T : End ℂ HyperFock) : End ℂ PiHalfFockCarrier :=
  LinearMap.rTensor HalfEtaChargeLine T

/-- Lift an oscillator operator to the shifted `nu` coset carrier. -/
def liftNuCosetOsc (T : End ℂ HyperFock) : End ℂ PiNuCosetCarrier :=
  LinearMap.rTensor NuCosetChargeLine T

@[simp] theorem liftHalfOsc_state (T : End ℂ HyperFock) (p : HyperFock)
    (q : HalfEtaCharge) :
    liftHalfOsc T (piHalfFockState p q) = piHalfFockState (T p) q := by
  rw [liftHalfOsc, piHalfFockState, LinearMap.rTensor_tmul]
  rfl

@[simp] theorem liftNuCosetOsc_state (T : End ℂ HyperFock) (p : HyperFock)
    (q : NuCosetCharge) :
    liftNuCosetOsc T (piNuCosetState p q) = piNuCosetState (T p) q := by
  rw [liftNuCosetOsc, piNuCosetState, LinearMap.rTensor_tmul]
  rfl

/-- The `mu(0)` eigenvalue on source charge `(r/2) eta` is `r/2`. -/
def sourceMuMomentum : End ℂ PiHalfFockCarrier :=
  LinearMap.lTensor HyperFock halfEtaChargeMomentum

/-- Momentum on the target coset line.  Orthogonality `mu dot nu = 0` means the target
`mu(0)` eigenvalue is still `r/2`. -/
def nuCosetMuMomentumLine : End ℂ NuCosetChargeLine :=
  Finsupp.lsum ℂ (fun q : NuCosetCharge => ((q.label : ℂ) / 2) •
    (Finsupp.lsingle q : ℂ →ₗ[ℂ] NuCosetChargeLine))

def targetMuMomentum : End ℂ PiNuCosetCarrier :=
  LinearMap.lTensor HyperFock nuCosetMuMomentumLine

@[simp] theorem sourceMuMomentum_state (p : HyperFock) (q : HalfEtaCharge) :
    sourceMuMomentum (piHalfFockState p q) =
      q.value • piHalfFockState p q := by
  rw [sourceMuMomentum, piHalfFockState, LinearMap.lTensor_tmul,
    halfEtaChargeMomentum_basis, TensorProduct.tmul_smul]

@[simp] theorem nuCosetMuMomentumLine_basis (q : NuCosetCharge) :
    nuCosetMuMomentumLine (nuCosetChargeBasis q) =
      ((q.label : ℂ) / 2) • nuCosetChargeBasis q := by
  rw [nuCosetMuMomentumLine, nuCosetChargeBasis, Finsupp.lsum_single,
    LinearMap.smul_apply, Finsupp.lsingle_apply]

@[simp] theorem targetMuMomentum_state (p : HyperFock) (q : HalfEtaCharge) :
    targetMuMomentum (piNuCosetState p (nuCosetCharge q)) =
      q.value • piNuCosetState p (nuCosetCharge q) := by
  rw [targetMuMomentum, piNuCosetState, LinearMap.lTensor_tmul,
    nuCosetMuMomentumLine_basis, TensorProduct.tmul_smul]
  rfl

/-- Source `mu` current on `Pi(0)^(1/2)`. -/
def sourceMuCurrentField : FormalDist (End ℂ PiHalfFockCarrier) :=
  fun j => liftHalfOsc (directionOsc (muDirection boundaryLevel85) (-j - 1)) +
    if j = -1 then sourceMuMomentum else 0

/-- Shifted-module action of the `mu` current. -/
def targetMuCurrentField : FormalDist (End ℂ PiNuCosetCarrier) :=
  fun j => liftNuCosetOsc (directionOsc (muDirection boundaryLevel85) (-j - 1)) +
    if j = -1 then targetMuMomentum else 0

theorem sourceMuCurrentField_state (j : ℤ) (p : HyperFock) (q : HalfEtaCharge) :
    sourceMuCurrentField j (piHalfFockState p q) =
      piHalfFockState (directionOsc (muDirection boundaryLevel85) (-j - 1) p) q +
        (if j = -1 then q.value • piHalfFockState p q else 0) := by
  rw [sourceMuCurrentField, LinearMap.add_apply, liftHalfOsc_state]
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, sourceMuMomentum_state]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]

theorem targetMuCurrentField_state (j : ℤ) (p : HyperFock) (q : HalfEtaCharge) :
    targetMuCurrentField j (piNuCosetState p (nuCosetCharge q)) =
      piNuCosetState (directionOsc (muDirection boundaryLevel85) (-j - 1) p)
          (nuCosetCharge q) +
        (if j = -1 then q.value • piNuCosetState p (nuCosetCharge q) else 0) := by
  rw [targetMuCurrentField, LinearMap.add_apply, liftNuCosetOsc_state]
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, targetMuMomentum_state]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]

/-! ## The solved Cartan intertwining identity -/

/-- Heterotypic coefficient commutator `J_target S - S J_source`. -/
def heterotypicBracketCoeff
    {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (JT : End ℂ B) (S : A →ₗ[ℂ] B) (JS : End ℂ A) : A →ₗ[ℂ] B :=
  JT.comp S - S.comp JS

/-- The `mu` current commutes with every half-power coefficient of `exp(nu)` on a pure source
charge state. -/
theorem muCurrent_intertwines_nuExponential_state
    (j t : ℤ) (p : HyperFock) (q : HalfEtaCharge) :
    targetMuCurrentField j
        (nuExponentialHalfField t (piHalfFockState p q)) =
      nuExponentialHalfField t
        (sourceMuCurrentField j (piHalfFockState p q)) := by
  rw [nuExponentialHalfField_piHalfFockState,
    targetMuCurrentField_state, sourceMuCurrentField_state, map_add,
    nuExponentialHalfField_piHalfFockState]
  have hcomm := DFunLike.congr_fun
    (nuHalfDress_commute_muOsc t q (-j - 1)).eq p
  simp only [Module.End.mul_apply] at hcomm
  rw [hcomm]
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, map_smul,
      nuExponentialHalfField_piHalfFockState]
  · rw [if_neg hj, if_neg hj, map_zero]

/-- Operator identity for every coefficient of the `mu` current and the half-power screening
field. -/
theorem muCurrent_intertwines_nuExponential (j t : ℤ) :
    heterotypicBracketCoeff (targetMuCurrentField j) (nuExponentialHalfField t)
      (sourceMuCurrentField j) = 0 := by
  refine LinearMap.ext fun x => ?_
  change (heterotypicBracketCoeff (targetMuCurrentField j)
      (nuExponentialHalfField t) (sourceMuCurrentField j)) x = 0
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add x y hx hy =>
      rw [map_add, hx, hy, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g₁ g₂ h₁ h₂ =>
          erw [TensorProduct.tmul_add, map_add, h₁, h₂, add_zero]
      | single q a =>
          rw [← Finsupp.smul_single_one]
          erw [TensorProduct.tmul_smul, map_smul]
          change a • (targetMuCurrentField j
              (nuExponentialHalfField t (piHalfFockState p q)) -
            nuExponentialHalfField t
              (sourceMuCurrentField j (piHalfFockState p q))) = 0
          rw [muCurrent_intertwines_nuExponential_state, sub_self, smul_zero]

/-- The inverse-DS Cartan current is `h = 2 mu`; its Pi screening intertwining identity follows
immediately. -/
theorem hCurrent_intertwines_nuExponential (j t : ℤ) :
    heterotypicBracketCoeff ((2 : ℂ) • targetMuCurrentField j) (nuExponentialHalfField t)
      ((2 : ℂ) • sourceMuCurrentField j) = 0 := by
  have h := muCurrent_intertwines_nuExponential j t
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun h x
  simp only [heterotypicBracketCoeff, LinearMap.sub_apply,
    LinearMap.comp_apply] at hx ⊢
  change (2 : ℂ) • targetMuCurrentField j (nuExponentialHalfField t x) -
      nuExponentialHalfField t ((2 : ℂ) • sourceMuCurrentField j x) = 0
  rw [map_smul]
  simpa only [smul_sub, smul_zero, LinearMap.zero_apply] using
    congrArg ((2 : ℂ) • ·) hx

end
end ScreeningCoset
end InverseDS
end VOA
