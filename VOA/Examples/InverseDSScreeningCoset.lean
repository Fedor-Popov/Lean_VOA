/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSHalfLatticeScreening
import VOA.Examples.InverseDSPiGrading
import VOA.Examples.InverseDSPiTransverse

/-!
# The shifted Pi coset and the `exp(nu)` half-power field

At level `k = -8/5`, the Adamović--Milas screening momentum is
`nu = xi + (2/5) eta`.  Acting on charge `(r/2) eta` produces the coset charge
`nu + (r/2) eta`, so the target is not the original half-lattice carrier.

This file constructs that shifted carrier and the oscillator part of `exp(nu)` using the
direction-free Newton recursion.  The Pi exponential has powers in `(1/2) Z`: on charge label
`r` its powers are `s + r/2`.  We index a coefficient by the numerator `t`, meaning the power
`t/2`; thus the coefficient is the oscillator dressing at `s` exactly when `t = 2s + r`.

This makes the genuine obstruction precise.  `exp(nu)` alone is not an ordinary integer-power
field on `Pi(0)^(1/2)`.  The Virasoro intertwining field in the full screening current must carry
the complementary fractional powers before an ordinary residue can be taken.
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

universe u v

/-! ## The shifted charge carrier -/

/-- Label for the coset charge `nu + (r/2) eta`.  It is a distinct type from
`HalfEtaCharge`, so maps into the shifted module cannot be mistaken for endomorphisms. -/
structure NuCosetCharge where
  label : ℤ
  deriving DecidableEq

/-- The coset label associated to a source half-lattice charge. -/
def nuCosetCharge (q : HalfEtaCharge) : NuCosetCharge := ⟨q.label⟩

/-- Group-algebra carrier of the shifted `nu + (1/2) Z eta` coset. -/
abbrev NuCosetChargeLine := NuCosetCharge →₀ ℂ

/-- Basis vector of a shifted coset charge. -/
def nuCosetChargeBasis (q : NuCosetCharge) : NuCosetChargeLine := Finsupp.single q 1

/-- Oscillator Fock space tensored with the shifted coset charge line. -/
abbrev PiNuCosetCarrier := HyperFock ⊗[ℂ] NuCosetChargeLine

/-- A pure state of charge `nu + (r/2) eta`. -/
def piNuCosetState (p : HyperFock) (q : NuCosetCharge) : PiNuCosetCarrier :=
  p ⊗ₜ[ℂ] nuCosetChargeBasis q

/-- Bare shifted coset vacuum of label `r`. -/
def piNuCosetVacuum (q : HalfEtaCharge) : PiNuCosetCarrier :=
  piNuCosetState hyperVacuum (nuCosetCharge q)

/-- Linear charge shift from the half-lattice line to the `nu` coset line. -/
def nuCosetShiftLine : HalfEtaChargeLine →ₗ[ℂ] NuCosetChargeLine :=
  Finsupp.lsum ℂ (fun q : HalfEtaCharge =>
    (Finsupp.lsingle (nuCosetCharge q) : ℂ →ₗ[ℂ] NuCosetChargeLine))

@[simp] theorem nuCosetShiftLine_basis (q : HalfEtaCharge) :
    nuCosetShiftLine (halfEtaChargeBasis q) = nuCosetChargeBasis (nuCosetCharge q) := by
  rw [nuCosetShiftLine, halfEtaChargeBasis, Finsupp.lsum_single, Finsupp.lsingle_apply]
  rfl

/-! ## Direction-parametric Newton dressing at `nu` -/

/-- Creation atom of the `nu` exponential. -/
def nuCreationAtom (m : ℕ) : End ℂ HyperFock :=
  directionOsc (nuDirection boundaryLevel85) (-((m : ℤ) + 1))

/-- Annihilation atom of the `nu` exponential. -/
def nuAnnihilationAtom (m : ℕ) : End ℂ HyperFock :=
  -(directionOsc (nuDirection boundaryLevel85) ((m : ℤ) + 1))

/-- Creation Newton coefficients of `exp(nu)`. -/
def nuCreationCoeff (N : ℕ) : End ℂ HyperFock := newtonCoeff nuCreationAtom N

/-- Annihilation Newton coefficients of `exp(nu)`. -/
def nuAnnihilationCoeff (N : ℕ) : End ℂ HyperFock := newtonCoeff nuAnnihilationAtom N

@[simp] theorem nuCreationCoeff_zero : nuCreationCoeff 0 = LinearMap.id := by
  rw [nuCreationCoeff, newtonCoeff_zero]

@[simp] theorem nuAnnihilationCoeff_zero : nuAnnihilationCoeff 0 = LinearMap.id := by
  rw [nuAnnihilationCoeff, newtonCoeff_zero]

theorem nuCreationCoeff_succ (N : ℕ) :
    nuCreationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (nuCreationAtom m).comp (nuCreationCoeff (N - m)) := by
  rw [nuCreationCoeff, newtonCoeff_succ]
  rfl

theorem nuAnnihilationCoeff_succ (N : ℕ) :
    nuAnnihilationCoeff (N + 1) = ((N + 1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N + 1),
      (nuAnnihilationAtom m).comp (nuAnnihilationCoeff (N - m)) := by
  rw [nuAnnihilationCoeff, newtonCoeff_succ]
  rfl

/-- The annihilation coefficients fix the Fock vacuum only in degree zero. -/
theorem nuAnnihilationCoeff_vacuum (N : ℕ) :
    nuAnnihilationCoeff N hyperVacuum = if N = 0 then hyperVacuum else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 => simp
      | M + 1 =>
          rw [nuAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          have hz : ∀ m ∈ Finset.range (M + 1),
              ((nuAnnihilationAtom m).comp (nuAnnihilationCoeff (M - m)))
                hyperVacuum = 0 := by
            intro m hm
            rw [LinearMap.comp_apply, ih (M - m) (by
              simp only [Finset.mem_range] at hm
              omega)]
            split_ifs with h
            · rw [nuAnnihilationAtom, LinearMap.neg_apply, hyperVacuum,
                directionOsc_vacuum _ ((m : ℤ) + 1) (by omega), neg_zero]
            · rw [map_zero]
          rw [Finset.sum_eq_zero hz, smul_zero]
          simp

/-- The annihilation coefficient of energy `N` lowers polynomial weight by `N`. -/
theorem nuAnnihilationCoeff_mem_gradingZN (N : ℕ) {w : ℕ} {p : HyperFock}
    (hp : p ∈ HeisenbergN.gradingWN 2 w) :
    nuAnnihilationCoeff N p ∈ HeisenbergN.gradingZN 2 ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      match N with
      | 0 =>
          rw [nuAnnihilationCoeff_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
          exact HeisenbergN.mem_gradingZN_of_gradingWN hp
      | M + 1 =>
          rw [nuAnnihilationCoeff_succ, LinearMap.smul_apply, LinearMap.sum_apply]
          refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
          simp only [Finset.mem_range] at hm
          rw [LinearMap.comp_apply, nuAnnihilationAtom, LinearMap.neg_apply]
          refine Submodule.neg_mem _ ?_
          have hrec := ih (M - m) (by omega)
          have hmode := directionOsc_mem_gradingZN (nuDirection boundaryLevel85)
            ((m : ℤ) + 1) ((w : ℤ) - (M - m : ℕ))
            (nuAnnihilationCoeff (M - m) p) hrec
          have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1) =
              (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_sub (by omega : m ≤ M)]
            push_cast
            ring
          rwa [hgoal] at hmode

/-- Creation half of the `nu` oscillator exponential. -/
def nuEminus : FormalDist (End ℂ HyperFock) :=
  fun t => if 0 ≤ t then nuCreationCoeff t.toNat else 0

/-- Annihilation half of the `nu` oscillator exponential. -/
def nuEplus : FormalDist (End ℂ HyperFock) :=
  fun t => if t ≤ 0 then nuAnnihilationCoeff (-t).toNat else 0

theorem nuEminus_nonneg {t : ℤ} (ht : 0 ≤ t) :
    nuEminus t = nuCreationCoeff t.toNat := by rw [nuEminus, if_pos ht]

theorem nuEminus_neg {t : ℤ} (ht : t < 0) : nuEminus t = 0 := by
  rw [nuEminus, if_neg (by omega)]

theorem nuEplus_nonpos {t : ℤ} (ht : t ≤ 0) :
    nuEplus t = nuAnnihilationCoeff (-t).toNat := by rw [nuEplus, if_pos ht]

theorem nuEplus_pos {t : ℤ} (ht : 0 < t) : nuEplus t = 0 := by
  rw [nuEplus, if_neg (by omega)]

theorem nuEminus_isField : IsField nuEminus := by
  intro x
  exact ⟨0, fun n hn => by rw [nuEminus_neg hn, LinearMap.zero_apply]⟩

/-- The annihilation half is lower truncated on every polynomial Fock state. -/
theorem nuEplus_isField : IsField nuEplus := by
  classical
  intro x
  obtain ⟨c, rfl⟩ := (HeisenbergN.gradingWN_isInternal 2).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le c.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [nuEplus_nonpos hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := nuAnnihilationCoeff_mem_gradingZN (-n).toNat (c w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega :
    (w : ℤ) - ((-n).toNat : ℤ) < 0), Submodule.mem_bot] at hmem
  exact hmem

/-- Full normal-ordered oscillator dressing of `exp(nu)`. -/
def nuDress : FormalDist (End ℂ HyperFock) := nprod nuEminus_isField nuEplus_isField

theorem nuDress_isField : IsField nuDress :=
  IsField.nprod nuEminus_isField nuEplus_isField

/-! ## Half-power assembly -/

/-- The coefficient label `t` represents the formal power `t/2`. -/
def halfPowerValue (t : ℤ) : ℂ := (t : ℂ) / 2

/-- On source charge label `r`, oscillator coefficient `s` contributes to half-power label
`t = 2s + r`. -/
def HalfPowerMatch (t : ℤ) (q : HalfEtaCharge) : Prop :=
  ∃ s : ℤ, t = 2 * s + q.label

/-- The unique oscillator index matching a half-power label and charge sector. -/
noncomputable def matchedOscillatorIndex (t : ℤ) (q : HalfEtaCharge)
    (h : HalfPowerMatch t q) : ℤ := Classical.choose h

theorem matchedOscillatorIndex_spec (t : ℤ) (q : HalfEtaCharge)
    (h : HalfPowerMatch t q) :
    t = 2 * matchedOscillatorIndex t q h + q.label := Classical.choose_spec h

theorem matchedOscillatorIndex_unique (t s : ℤ) (q : HalfEtaCharge)
    (h : t = 2 * s + q.label) :
    matchedOscillatorIndex t q ⟨s, h⟩ = s := by
  have hs := matchedOscillatorIndex_spec t q ⟨s, h⟩
  omega

/-- The oscillator dressing selected by a half-power coefficient on charge sector `q`. -/
noncomputable def nuHalfDress (t : ℤ) (q : HalfEtaCharge) : End ℂ HyperFock := by
  classical
  exact if h : HalfPowerMatch t q then nuDress (matchedOscillatorIndex t q h) else 0

theorem nuHalfDress_of_eq (t s : ℤ) (q : HalfEtaCharge)
    (h : t = 2 * s + q.label) : nuHalfDress t q = nuDress s := by
  rw [nuHalfDress, dif_pos ⟨s, h⟩]
  congr 1
  exact matchedOscillatorIndex_unique t s q h

theorem nuHalfDress_of_not_match (t : ℤ) (q : HalfEtaCharge)
    (h : ¬ HalfPowerMatch t q) : nuHalfDress t q = 0 := by
  rw [nuHalfDress, dif_neg h]

/-- Sectorwise family used to assemble the heterotypic half-power exponential. -/
def nuExponentialHalfFam (t : ℤ) (q : HalfEtaCharge) :
    ℂ →ₗ[ℂ] (HyperFock →ₗ[ℂ] PiNuCosetCarrier) :=
  LinearMap.toSpanSingleton ℂ (HyperFock →ₗ[ℂ] PiNuCosetCarrier)
    (((TensorProduct.mk ℂ HyperFock NuCosetChargeLine).flip
      (nuCosetChargeBasis (nuCosetCharge q))).comp (nuHalfDress t q))

/-- The Pi part of `Y(exp(nu),z)`, indexed by half-power numerators. -/
def nuExponentialHalfField :
    FormalDist (PiHalfFockCarrier →ₗ[ℂ] PiNuCosetCarrier) :=
  fun t => TensorProduct.lift (Finsupp.lsum ℂ (nuExponentialHalfFam t)).flip

/-- Defining action on a pure source half-charge state. -/
theorem nuExponentialHalfField_piHalfFockState
    (t : ℤ) (q : HalfEtaCharge) (p : HyperFock) :
    nuExponentialHalfField t (piHalfFockState p q) =
      piNuCosetState (nuHalfDress t q p) (nuCosetCharge q) := by
  rw [nuExponentialHalfField, piHalfFockState, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (nuExponentialHalfFam t)) (halfEtaChargeBasis q) p = _
  rw [halfEtaChargeBasis, Finsupp.lsum_single, nuExponentialHalfFam,
    LinearMap.toSpanSingleton_apply, one_smul, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  rfl

theorem nuExponentialHalfField_piHalfFockState_of_eq
    (t s : ℤ) (q : HalfEtaCharge) (p : HyperFock)
    (h : t = 2 * s + q.label) :
    nuExponentialHalfField t (piHalfFockState p q) =
      piNuCosetState (nuDress s p) (nuCosetCharge q) := by
  rw [nuExponentialHalfField_piHalfFockState, nuHalfDress_of_eq t s q h]

theorem nuExponentialHalfField_piHalfFockState_of_not_match
    (t : ℤ) (q : HalfEtaCharge) (p : HyperFock)
    (h : ¬ HalfPowerMatch t q) :
    nuExponentialHalfField t (piHalfFockState p q) = 0 := by
  rw [nuExponentialHalfField_piHalfFockState, nuHalfDress_of_not_match t q h,
    LinearMap.zero_apply, piNuCosetState, TensorProduct.zero_tmul]

/-- Lower truncation for a heterotypic formal distribution. -/
def IsHeterotypicField {A : Type u} {B : Type v}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (S : FormalDist (A →ₗ[ℂ] B)) : Prop :=
  ∀ x, ∃ N : ℤ, ∀ n : ℤ, n < N → S n x = 0

/-- The constructed half-power exponential is lower truncated. -/
theorem nuExponentialHalfField_isHeterotypicField :
    IsHeterotypicField nuExponentialHalfField := by
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
      | single q a =>
          obtain ⟨B, hB⟩ := nuDress_isField p
          refine ⟨2 * B + q.label, fun n hn => ?_⟩
          rw [← Finsupp.smul_single_one]
          erw [TensorProduct.tmul_smul, map_smul,
            show p ⊗ₜ[ℂ] halfEtaChargeBasis q = piHalfFockState p q from rfl]
          by_cases hm : HalfPowerMatch n q
          · obtain ⟨s, hs⟩ := hm
            rw [nuExponentialHalfField_piHalfFockState_of_eq n s q p hs]
            have hsB : s < B := by omega
            rw [hB s hsB, piNuCosetState, TensorProduct.zero_tmul, smul_zero]
          · rw [nuExponentialHalfField_piHalfFockState_of_not_match n q p hm, smul_zero]

/-! ## What a Pi-only residue can and cannot see -/

/-- The coefficient of the Pi half-power field at `z^(-1)`, whose numerator is `-2`.
This is not yet the Adamović--Milas screening: the latter is the residue only after tensoring
with the complementary Virasoro intertwining field. -/
def piNuHalfResidue : PiHalfFockCarrier →ₗ[ℂ] PiNuCosetCarrier :=
  nuExponentialHalfField (-2)

theorem piNuHalfResidue_piHalfFockState_of_eq (s : ℤ)
    (q : HalfEtaCharge) (p : HyperFock) (h : -2 = 2 * s + q.label) :
    piNuHalfResidue (piHalfFockState p q) =
      piNuCosetState (nuDress s p) (nuCosetCharge q) :=
  nuExponentialHalfField_piHalfFockState_of_eq (-2) s q p h

/-- On an odd half-lattice label, `exp(nu)` has only half-integral powers and therefore has no
Pi-only `z^(-1)` coefficient.  The full screening can nevertheless be nonzero there because the
Virasoro intertwiner supplies the complementary half-power. -/
theorem piNuHalfResidue_zero_of_odd_label (q : HalfEtaCharge) (p : HyperFock)
    (hq : ¬ Even q.label) : piNuHalfResidue (piHalfFockState p q) = 0 := by
  apply nuExponentialHalfField_piHalfFockState_of_not_match
  rintro ⟨s, hs⟩
  apply hq
  refine ⟨-s - 1, ?_⟩
  omega

end
end ScreeningCoset
end InverseDS
end VOA
