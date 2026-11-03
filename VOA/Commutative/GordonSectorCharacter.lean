/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.GordonPartitionProfile
import VOA.Commutative.GordonPairTelescope

/-! # Literal profile-character bounds for actual auxiliary quotient sectors -/
namespace VOA.GordonSectorCharacter
open GordonPartitionProfile GordonCanonicalPartitions GordonPartitionBound GordonFullDivisor
open QSeries
noncomputable section
variable {ρ α β γ : Type} [Fintype ρ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The actual conductor times invariant Hilbert series is the literal
q-series source term after restoring its original particle weight. -/
theorem multiplicityResidualTerm_eq_shifted_canonical {m : ℕ}
    (lam : BoundedPartition (m + 1) (Fintype.card ρ)) :
    multiplicityResidualTerm (K := ℚ) (partitionProfile lam)
        (Fintype.card α) (Fintype.card β) (Fintype.card γ) =
      PowerSeries.X ^ (2 * Fintype.card ρ +
        (Fintype.card α + Fintype.card β + Fintype.card γ)) *
        (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) (m + 1)
          (canonicalMap (σ := ρ) lam.val) *
          invariantSeries (α := α) (β := β) (γ := γ) (canonicalMap (σ := ρ) lam.val)) := by
  rw [multiplicityResidualTerm, ← canonicalMap_fullDegree_sourceEnergy (α := α) (β := β) (γ := γ),
    invariantSeries, canonicalMap_factorial_product]
  simp only [pow_add]
  ring

/-- The homogeneous functional-model coefficient equals its conformal
profile-source coefficient, including every residual interaction. -/
theorem coeff_canonical_eq_sourceTerm {m : ℕ}
    (lam : BoundedPartition (m + 1) (Fintype.card ρ)) (D : ℕ) :
    PowerSeries.coeff D
      (PowerSeries.X ^ fullDegree (α := α) (β := β) (γ := γ) (m + 1)
        (canonicalMap (σ := ρ) lam.val) *
        invariantSeries (α := α) (β := β) (γ := γ) (canonicalMap (σ := ρ) lam.val)) =
      PowerSeries.coeff (D + 2 * Fintype.card ρ +
        (Fintype.card α + Fintype.card β + Fintype.card γ))
        (multiplicityResidualTerm (K := ℚ) (partitionProfile lam)
          (Fintype.card α) (Fintype.card β) (Fintype.card γ)) := by
  rw [multiplicityResidualTerm_eq_shifted_canonical (α := α) (β := β) (γ := γ),
    Nat.add_assoc, PowerSeries.coeff_X_pow_mul]


open GordonPairTelescope GordonPairIndexing GordonRestrictedDual

/-- The actual fixed-particle auxiliary quotient sector is bounded by the
literal multiplicity/residual source sum, with its conformal degree restored. -/
theorem sector_finrank_le_profile_sum {K : Type*} [Field K] [CharZero K]
    (m D a b c : ℕ) :
    (Module.finrank K (sector (K := K) (m + 1) D (originalColor a b c)) : ℚ) ≤
      ∑ R : PairCount a b, ∑ r : Profile (m + 1) R.val,
        PowerSeries.coeff (D + a + b + c)
          (multiplicityResidualTerm (K := ℚ) r.val (a - R.val) (b - R.val) c) := by
  apply (sector_finrank_le_pair_partition_sum (K := K) (m + 1) D a b c).trans_eq
  apply Finset.sum_congr rfl
  intro R _
  have hRa := pairCount_le_left a b R
  have hRb := pairCount_le_right a b R
  have hshift : D + 2 * R.val + (a - R.val + (b - R.val) + c) = D + a + b + c := by
    omega
  calc
    _ = ∑ r : Profile (m + 1) (Fintype.card (Fin R.val)),
        PowerSeries.coeff (D + 2 * Fintype.card (Fin R.val) +
          (Fintype.card (ResidualIndex a R.val) + Fintype.card (ResidualIndex b R.val) +
            Fintype.card (Fin c)))
          (multiplicityResidualTerm (K := ℚ) r.val
            (Fintype.card (ResidualIndex a R.val)) (Fintype.card (ResidualIndex b R.val))
              (Fintype.card (Fin c))) := by
      simp_rw [coeff_canonical_eq_sourceTerm]
      exact Fintype.sum_equiv (boundedPartitionProfileEquiv (m + 1)
        (Fintype.card (Fin R.val))) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Fintype.card_fin, card_residualIndex a R.val hRa,
        card_residualIndex b R.val hRb, hshift]
      let e : Profile (m + 1) (Fintype.card (Fin R.val)) ≃ Profile (m + 1) R.val :=
        Equiv.subtypeEquivRight (fun _ => by rw [Fintype.card_fin])
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end
end VOA.GordonSectorCharacter
