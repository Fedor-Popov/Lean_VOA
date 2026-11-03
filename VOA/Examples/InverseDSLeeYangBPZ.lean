/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangTargetNull

/-!
# An explicit BPZ coefficient identity for the inverse-DS Lee--Yang field

The Ward identity turns the image of the level-four vacuum singular vector into an explicit
three-step expression in target Virasoro modes and shifted coefficients of the Fock field.
This file performs that reduction before any target quotient is taken.  It isolates the exact
normal-form calculation still needed for descent to the level-two/level-three target null
submodule.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangBPZ

open Module (End)
open ScreeningLowering
open LeeYangFockExponential LeeYangFockVirasoro LeeYangFullFockWard
open LeeYangConcreteDescent LeeYangTargetNull

noncomputable section

/-- The scalar introduced by commuting a coefficient of the weight `-1/5` field past a source
`L_{-2}` mode. -/
def k85BPZStepTwo (t : ℤ) : ℂ := (t : ℂ) / 2 + 11 / 5

/-- The scalar introduced by commuting a coefficient of the weight `-1/5` field past a source
`L_{-4}` mode. -/
def k85BPZStepFour (t : ℤ) : ℂ := (t : ℂ) / 2 + 23 / 5

theorem k85BPZStepTwo_eq_ward (t : ℤ) :
    (((t - 2 * (-2) : ℤ) : ℂ) / 2 +
      (((-2 + 1 : ℤ) : ℂ) * k85ScreeningVirWeight)) = k85BPZStepTwo t := by
  simp only [k85BPZStepTwo, k85ScreeningVirWeight]
  push_cast
  ring

theorem k85BPZStepFour_eq_ward (t : ℤ) :
    (((t - 2 * (-4) : ℤ) : ℂ) / 2 +
      (((-4 + 1 : ℤ) : ℂ) * k85ScreeningVirWeight)) = k85BPZStepFour t := by
  simp only [k85BPZStepFour, k85ScreeningVirWeight]
  push_cast
  ring

/-- Exact coefficientwise BPZ expansion of the source level-four singular vector. -/
theorem k85FockField_sourceSingular_expansion (t : ℤ) :
    k85FockField t k85SourceSingular =
      (5 : ℂ) • k85TargetL (-2) (k85TargetL (-2)
        (k85FockField t (HeisenbergN.vacuumN 1))) +
      (-10 * k85BPZStepTwo t) • k85TargetL (-2)
        (k85FockField (t + 4) (HeisenbergN.vacuumN 1)) +
      (5 * k85BPZStepTwo t * k85BPZStepTwo (t + 4) +
        3 * k85BPZStepFour t) •
          k85FockField (t + 8) (HeisenbergN.vacuumN 1) +
      (-3 : ℂ) • k85TargetL (-4)
        (k85FockField t (HeisenbergN.vacuumN 1)) := by
  rw [k85SourceSingular, map_add, map_smul, map_smul]
  rw [LeeYangConcreteDescent.field_apply_sourceMode k85SourceL k85TargetL k85FockField
      k85FockVirasoroScreeningFieldData.ward (-2) t]
  rw [LeeYangConcreteDescent.field_apply_sourceMode k85SourceL k85TargetL k85FockField
      k85FockVirasoroScreeningFieldData.ward (-2) t]
  rw [LeeYangConcreteDescent.field_apply_sourceMode k85SourceL k85TargetL k85FockField
      k85FockVirasoroScreeningFieldData.ward (-2) (t - 2 * (-2))]
  rw [LeeYangConcreteDescent.field_apply_sourceMode k85SourceL k85TargetL k85FockField
      k85FockVirasoroScreeningFieldData.ward (-4) t]
  simp only [map_sub, map_smul, smul_sub, smul_smul]
  rw [k85BPZStepTwo_eq_ward t]
  rw [show t - 2 * (-2) = t + 4 by ring]
  rw [k85BPZStepTwo_eq_ward (t + 4)]
  rw [show t + 4 - 2 * (-2) = t + 8 by ring]
  rw [k85BPZStepFour_eq_ward t]
  rw [show t - 2 * (-4) = t + 8 by ring]
  module

/-- On even half-powers the BPZ expansion is a completely explicit Schur-polynomial normal
form.  Thus the remaining target-null calculation contains no hidden field coefficients. -/
theorem k85EEC_sourceSingular_normalForm (s : ℤ) :
    LatExp.EEC k85FockCharge s k85SourceSingular =
      (5 : ℂ) • k85TargetL (-2) (k85TargetL (-2)
        (if 0 ≤ s then LatExp.cSchurC k85FockCharge s.toNat else 0)) +
      (-10 * k85BPZStepTwo (2 * s)) • k85TargetL (-2)
        (if 0 ≤ s + 2 then LatExp.cSchurC k85FockCharge (s + 2).toNat else 0) +
      (5 * k85BPZStepTwo (2 * s) * k85BPZStepTwo (2 * s + 4) +
        3 * k85BPZStepFour (2 * s)) •
          (if 0 ≤ s + 4 then LatExp.cSchurC k85FockCharge (s + 4).toNat else 0) +
      (-3 : ℂ) • k85TargetL (-4)
        (if 0 ≤ s then LatExp.cSchurC k85FockCharge s.toNat else 0) := by
  have h := k85FockField_sourceSingular_expansion (2 * s)
  rw [k85FockField_of_eq (2 * s) s rfl] at h
  rw [k85FockField_of_eq (2 * s + 4) (s + 2) (by ring)] at h
  rw [k85FockField_of_eq (2 * s + 8) (s + 4) (by ring)] at h
  rw [LatExp.EEC_vacuum, LatExp.EEC_vacuum, LatExp.EEC_vacuum] at h
  exact h

/-- Coefficients below the level-four creation boundary vanish identically. -/
theorem k85EEC_sourceSingular_of_lt_negFour (s : ℤ) (hs : s < -4) :
    LatExp.EEC k85FockCharge s k85SourceSingular = 0 := by
  rw [k85EEC_sourceSingular_normalForm]
  simp only [if_neg (by omega : ¬ 0 ≤ s), if_neg (by omega : ¬ 0 ≤ s + 2),
    if_neg (by omega : ¬ 0 ≤ s + 4), map_zero, smul_zero, add_zero]

/-- Consequently the integer-indexed BPZ gate starts exactly at oscillator coefficient `-4`;
all lower coefficients belong to the target candidate automatically. -/
theorem k85BPZ_iff_from_negFour :
    (∀ s : ℤ, LatExp.EEC k85FockCharge s k85SourceSingular ∈
        k85TargetCandidateNull) ↔
      ∀ s : ℤ, -4 ≤ s →
        LatExp.EEC k85FockCharge s k85SourceSingular ∈ k85TargetCandidateNull := by
  constructor
  · intro h s _
    exact h s
  · intro h s
    by_cases hs : -4 ≤ s
    · exact h s hs
    · rw [k85EEC_sourceSingular_of_lt_negFour s (by omega)]
      exact Submodule.zero_mem _

/-! ## The first nonzero boundary coefficient -/

theorem k85SourceL_negOne_vacuum :
    k85SourceL (-1) (HeisenbergN.vacuumN 1) = 0 := by
  rw [k85SourceL, sectorVirasoro, LinearMap.sub_apply]
  simp only [zero_smul, sectorSugawara, LinearMap.add_apply, LinearMap.smul_apply]
  rw [HeisenbergN.LvirN_vacuum 1 2 (by norm_num : (-1 : ℤ) ≤ -1)]
  simp

/-- Translation covariance on the source vacuum gives the creation recurrence for the charged
Schur states in the target sector. -/
theorem k85TargetL_negOne_fockVacuum (t : ℤ) :
    k85TargetL (-1) (k85FockField t (HeisenbergN.vacuumN 1)) =
      (((t + 2 : ℤ) : ℂ) / 2) •
        k85FockField (t + 2) (HeisenbergN.vacuumN 1) := by
  have h := LeeYangConcreteDescent.field_apply_sourceMode
    k85SourceL k85TargetL k85FockField k85FockVirasoroScreeningFieldData.ward
      (-1) t (HeisenbergN.vacuumN 1)
  rw [k85SourceL_negOne_vacuum, map_zero] at h
  simp only [show t - 2 * (-1) = t + 2 by ring,
    show (-1 + 1 : ℤ) = 0 by norm_num, Int.cast_zero, zero_mul, add_zero] at h
  exact sub_eq_zero.mp h.symm

theorem k85TargetL_negOne_top :
    k85TargetL (-1) k85TargetTop = LatExp.cSchurC k85FockCharge 1 := by
  have h := k85TargetL_negOne_fockVacuum 0
  rw [k85FockField_of_eq 0 0 rfl] at h
  norm_num at h
  rw [k85FockField_of_eq 2 1 rfl, LatExp.EEC_vacuum, LatExp.EEC_vacuum] at h
  simpa [k85TargetTop, LatExp.cSchurC_zero] using h

theorem k85TargetL_negOne_sq_top :
    k85TargetL (-1) (k85TargetL (-1) k85TargetTop) =
      (2 : ℂ) • LatExp.cSchurC k85FockCharge 2 := by
  have h := k85TargetL_negOne_fockVacuum 2
  rw [k85FockField_of_eq 2 1 rfl] at h
  norm_num at h
  rw [k85FockField_of_eq 4 2 rfl, LatExp.EEC_vacuum, LatExp.EEC_vacuum] at h
  rw [k85TargetL_negOne_top]
  norm_num at h ⊢
  exact h

theorem k85TargetL_negOne_cube_top :
    k85TargetL (-1) (k85TargetL (-1) (k85TargetL (-1) k85TargetTop)) =
      (6 : ℂ) • LatExp.cSchurC k85FockCharge 3 := by
  have h := k85TargetL_negOne_fockVacuum 4
  rw [k85FockField_of_eq 4 2 rfl] at h
  norm_num at h
  rw [k85FockField_of_eq 6 3 rfl, LatExp.EEC_vacuum, LatExp.EEC_vacuum] at h
  norm_num at h
  change k85TargetL (-1) (LatExp.cSchurC k85FockCharge 2) =
    (3 : ℂ) • LatExp.cSchurC k85FockCharge 3 at h
  rw [k85TargetL_negOne_sq_top, map_smul, h, smul_smul]
  norm_num

/-- Uniform creation recurrence for the charged Schur basis. -/
theorem k85TargetL_negOne_cSchur (n : ℕ) :
    k85TargetL (-1) (LatExp.cSchurC k85FockCharge n) =
      ((n + 1 : ℕ) : ℂ) • LatExp.cSchurC k85FockCharge (n + 1) := by
  have h := k85TargetL_negOne_fockVacuum (2 * (n : ℤ))
  rw [k85FockField_of_eq (2 * (n : ℤ)) (n : ℤ) rfl] at h
  rw [k85FockField_of_eq (2 * (n : ℤ) + 2) (n + 1 : ℕ) (by push_cast; ring)] at h
  rw [LatExp.EEC_vacuum, LatExp.EEC_vacuum] at h
  rw [if_pos (by omega : 0 ≤ (n : ℤ)),
    if_pos (by omega : 0 ≤ ((n + 1 : ℕ) : ℤ))] at h
  simp only [Int.toNat_natCast] at h
  have hc : (((2 * (n : ℤ) + 2 : ℤ) : ℂ) / 2) = ((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hc] at h
  exact h

/-- Iterating `L_{-1}` gives the factorial-normalized Schur state. -/
def k85TargetNegOnePower : ℕ → LeeYangFock
  | 0 => k85TargetTop
  | n + 1 => k85TargetL (-1) (k85TargetNegOnePower n)

theorem k85TargetNegOnePower_eq (n : ℕ) :
    k85TargetNegOnePower n = (n.factorial : ℂ) •
      LatExp.cSchurC k85FockCharge n := by
  induction n with
  | zero =>
      rw [k85TargetNegOnePower, Nat.factorial_zero, Nat.cast_one, one_smul,
        LatExp.cSchurC_zero]
      rfl
  | succ n ih =>
      rw [k85TargetNegOnePower, ih, map_smul, k85TargetL_negOne_cSchur, smul_smul]
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      ring

theorem k85TargetL_negOne_negTwo_top :
    k85TargetL (-1) (k85TargetL (-2) k85TargetTop) =
      k85TargetL (-2) (k85TargetL (-1) k85TargetTop) +
        k85TargetL (-3) k85TargetTop := by
  rw [k85TargetL_comm_apply]
  norm_num

/-- The first potentially nonzero BPZ coefficient is exactly the level-two target singular
generator. -/
theorem k85EEC_sourceSingular_negTwo :
    LatExp.EEC k85FockCharge (-2) k85SourceSingular = k85TargetSingularTwo := by
  rw [k85EEC_sourceSingular_normalForm, k85TargetSingularTwo]
  norm_num [k85BPZStepTwo, k85BPZStepFour, LatExp.cSchurC_zero]
  rw [k85TargetL_negOne_sq_top]
  change
    -(2 • k85TargetL (-2) k85TargetTop) +
        10 • LatExp.cSchurC k85FockCharge 2 =
      5 • (2 • LatExp.cSchurC k85FockCharge 2) +
        -(2 • k85TargetL (-2) k85TargetTop)
  module

theorem k85EEC_sourceSingular_negTwo_mem :
    LatExp.EEC k85FockCharge (-2) k85SourceSingular ∈ k85TargetCandidateNull := by
  rw [k85EEC_sourceSingular_negTwo]
  apply seed_le_modeClosure k85TargetL k85TargetCandidateSeed
  apply Submodule.subset_span
  exact Set.mem_insert k85TargetSingularTwo {k85TargetSingularThree}

/-- The next boundary coefficient is the precise linear combination of the level-three target
singular vector and an `L_{-1}` descendant of the level-two singular vector predicted by BPZ
decoupling. -/
theorem k85EEC_sourceSingular_negOne :
    LatExp.EEC k85FockCharge (-1) k85SourceSingular =
      (1 / 3 : ℂ) • k85TargetSingularThree +
        (-2 / 3 : ℂ) • k85TargetL (-1) k85TargetSingularTwo := by
  rw [k85EEC_sourceSingular_normalForm]
  norm_num [k85BPZStepTwo, k85BPZStepFour]
  rw [← k85TargetL_negOne_top]
  rw [show Int.toNat 3 = 3 by rfl]
  rw [k85TargetSingularThree, k85TargetSingularTwo, map_add, map_smul, map_smul,
    k85TargetL_negOne_negTwo_top, k85TargetL_negOne_cube_top]
  simp only [smul_add, smul_smul]
  module

theorem k85EEC_sourceSingular_negOne_mem :
    LatExp.EEC k85FockCharge (-1) k85SourceSingular ∈ k85TargetCandidateNull := by
  rw [k85EEC_sourceSingular_negOne]
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    apply seed_le_modeClosure k85TargetL k85TargetCandidateSeed
    apply Submodule.subset_span
    exact Set.mem_insert_of_mem k85TargetSingularTwo (Set.mem_singleton _)
  · apply Submodule.smul_mem
    apply k85TargetCandidateNull_preserves
    apply seed_le_modeClosure k85TargetL k85TargetCandidateSeed
    apply Submodule.subset_span
    exact Set.mem_insert k85TargetSingularTwo {k85TargetSingularThree}

theorem k85EEC_sourceSingular_negFour :
    LatExp.EEC k85FockCharge (-4) k85SourceSingular = 0 := by
  rw [k85EEC_sourceSingular_normalForm]
  norm_num [k85BPZStepTwo, k85BPZStepFour, LatExp.cSchurC_zero]

theorem k85EEC_sourceSingular_negThree :
    LatExp.EEC k85FockCharge (-3) k85SourceSingular = 0 := by
  rw [k85EEC_sourceSingular_normalForm]
  norm_num [k85BPZStepTwo, k85BPZStepFour]

/-- The indicial coefficients at `-4` and `-3` cancel, while coefficient `-2` is the target
level-two singular vector.  Therefore the entire unresolved BPZ family begins at `s=-1`. -/
theorem k85BPZ_iff_from_negOne :
    (∀ s : ℤ, LatExp.EEC k85FockCharge s k85SourceSingular ∈
        k85TargetCandidateNull) ↔
      ∀ s : ℤ, -1 ≤ s →
        LatExp.EEC k85FockCharge s k85SourceSingular ∈ k85TargetCandidateNull := by
  constructor
  · intro h s _
    exact h s
  · intro h s
    by_cases hs : -1 ≤ s
    · exact h s hs
    · by_cases hs2 : s = -2
      · subst s
        exact k85EEC_sourceSingular_negTwo_mem
      by_cases hs3 : s = -3
      · subst s
        rw [k85EEC_sourceSingular_negThree]
        exact Submodule.zero_mem _
      by_cases hs4 : s = -4
      · subst s
        rw [k85EEC_sourceSingular_negFour]
        exact Submodule.zero_mem _
      · rw [k85EEC_sourceSingular_of_lt_negFour s (by omega)]
        exact Submodule.zero_mem _

/-! ## Uniform nonnegative normal form -/

/-- For every nonnegative coefficient, the BPZ image is a four-term expression whose last
scalar factors as `5 (n+3) (n+4)`.  This is the exact enveloping-algebra family that remains to
reduce by the level-two and level-three target singular relations. -/
theorem k85EEC_sourceSingular_natNormalForm (n : ℕ) :
    LatExp.EEC k85FockCharge (n : ℤ) k85SourceSingular =
      (5 : ℂ) • k85TargetL (-2) (k85TargetL (-2)
        (LatExp.cSchurC k85FockCharge n)) +
      (-2 * (5 * (n : ℂ) + 11)) • k85TargetL (-2)
        (LatExp.cSchurC k85FockCharge (n + 2)) +
      (5 * ((n : ℂ) + 3) * ((n : ℂ) + 4)) •
        LatExp.cSchurC k85FockCharge (n + 4) +
      (-3 : ℂ) • k85TargetL (-4) (LatExp.cSchurC k85FockCharge n) := by
  rw [k85EEC_sourceSingular_normalForm]
  rw [if_pos (by omega : 0 ≤ (n : ℤ)),
    if_pos (by omega : 0 ≤ (n : ℤ) + 2),
    if_pos (by omega : 0 ≤ (n : ℤ) + 4)]
  rw [Int.toNat_natCast, show ((n : ℤ) + 2).toNat = n + 2 by omega,
    show ((n : ℤ) + 4).toNat = n + 4 by omega]
  simp only [k85BPZStepTwo, k85BPZStepFour]
  push_cast
  module

/-- Clearing the Schur factorials turns the remaining BPZ calculation into a four-term word
identity in the negative Virasoro modes.  This is the most economical PBW form of the uniform
representation-theoretic obstruction. -/
theorem k85EEC_sourceSingular_PBWNumerator (n : ℕ) :
    ((n + 2).factorial : ℂ) •
        LatExp.EEC k85FockCharge (n : ℤ) k85SourceSingular =
      (5 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
          k85TargetL (-2) (k85TargetL (-2) (k85TargetNegOnePower n)) +
      (-2 * (5 * (n : ℂ) + 11)) • k85TargetL (-2)
        (k85TargetNegOnePower (n + 2)) +
      (5 : ℂ) • k85TargetNegOnePower (n + 4) +
      (-3 * ((n : ℂ) + 1) * ((n : ℂ) + 2)) •
        k85TargetL (-4) (k85TargetNegOnePower n) := by
  rw [k85EEC_sourceSingular_natNormalForm]
  rw [k85TargetNegOnePower_eq n, k85TargetNegOnePower_eq (n + 2),
    k85TargetNegOnePower_eq (n + 4)]
  simp only [smul_add, smul_smul, map_smul]
  have hf2 : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    ring
  have hf4 : (n + 4).factorial = (n + 4) * (n + 3) * (n + 2).factorial := by
    rw [show n + 4 = (n + 3) + 1 by omega, Nat.factorial_succ,
      show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ]
    ring
  rw [hf4, hf2]
  push_cast
  module

/-- After the four boundary coefficients have been discharged, full BPZ descent is equivalent
to the single explicit natural-number family above.  No field, parity, or negative-index
condition remains. -/
theorem k85BPZ_iff_natNormalForm :
    (∀ s : ℤ, LatExp.EEC k85FockCharge s k85SourceSingular ∈
        k85TargetCandidateNull) ↔
      ∀ n : ℕ,
        (5 : ℂ) • k85TargetL (-2) (k85TargetL (-2)
            (LatExp.cSchurC k85FockCharge n)) +
          (-2 * (5 * (n : ℂ) + 11)) • k85TargetL (-2)
            (LatExp.cSchurC k85FockCharge (n + 2)) +
          (5 * ((n : ℂ) + 3) * ((n : ℂ) + 4)) •
            LatExp.cSchurC k85FockCharge (n + 4) +
          (-3 : ℂ) • k85TargetL (-4) (LatExp.cSchurC k85FockCharge n) ∈
            k85TargetCandidateNull := by
  rw [k85BPZ_iff_from_negOne]
  constructor
  · intro h n
    rw [← k85EEC_sourceSingular_natNormalForm]
    exact h n (by omega)
  · intro h s hs
    by_cases hneg : s = -1
    · subst s
      exact k85EEC_sourceSingular_negOne_mem
    · have hs0 : 0 ≤ s := by omega
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = (n : ℤ) :=
        ⟨s.toNat, (Int.toNat_of_nonneg hs0).symm⟩
      rw [k85EEC_sourceSingular_natNormalForm]
      exact h n

end
end LeeYangBPZ
end InverseDS
end VOA
