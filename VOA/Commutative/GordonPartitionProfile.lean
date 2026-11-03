/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.GordonCanonicalPartitions
import VOA.Commutative.QMultiplicityProfile
import VOA.Commutative.GordonDegree
import VOA.Commutative.GordonFullDivisor

/-! # Genuine partitions and finite multiplicity profiles -/
namespace VOA.GordonPartitionProfile
open MvPolynomial
noncomputable section

/-- A profile records how many parts of each size 1,...,m occur. -/
def profileParts {m : ℕ} (r : Fin m → ℕ) : Multiset ℕ :=
  ∑ i, Multiset.replicate (r i) (i.val + 1)

theorem count_profileParts {m : ℕ} (r : Fin m → ℕ) (a : ℕ) :
    (profileParts r).count a = ∑ i, if i.val + 1 = a then r i else 0 := by
  unfold profileParts
  simp only [Multiset.count_sum', Multiset.count_replicate]

theorem count_profileParts_index {m : ℕ} (r : Fin m → ℕ) (i : Fin m) :
    (profileParts r).count (i.val + 1) = r i := by
  rw [count_profileParts]
  simpa only [Nat.add_left_inj, ← Fin.ext_iff, Finset.mem_univ, if_true] using
    (Finset.sum_ite_eq' Finset.univ i r)

theorem mem_profileParts_iff {m : ℕ} (r : Fin m → ℕ) (a : ℕ) :
    a ∈ profileParts r ↔ ∃ i, a = i.val + 1 ∧ r i ≠ 0 := by
  simp [profileParts, Multiset.mem_sum, Multiset.mem_replicate, and_comm]

theorem sum_profileParts {m : ℕ} (r : Fin m → ℕ) :
    (profileParts r).sum = ∑ i, (i.val + 1) * r i := by
  simp [profileParts, Multiset.sum_sum, mul_comm]

theorem card_profileParts {m : ℕ} (r : Fin m → ℕ) :
    (profileParts r).card = ∑ i, r i := by
  simp [profileParts, Multiset.card_sum]

/-- Actual partitions whose parts are bounded by m. -/
def BoundedPartition (m R : ℕ) := {lam : Nat.Partition R // ∀ a ∈ lam.parts, a ≤ m}

/-- Multiplicity profiles at fixed total particle count. -/
def Profile (m R : ℕ) := {r : Fin m → ℕ // ∑ i, (i.val + 1) * r i = R}

def partitionProfile {m R : ℕ} (lam : BoundedPartition m R) : Fin m → ℕ :=
  fun i => lam.val.parts.count (i.val + 1)

theorem profileParts_partitionProfile {m R : ℕ} (lam : BoundedPartition m R) :
    profileParts (partitionProfile lam) = lam.val.parts := by
  apply Multiset.ext.mpr
  intro a
  by_cases ha : 0 < a ∧ a ≤ m
  · let i : Fin m := ⟨a - 1, by omega⟩
    have hi : i.val + 1 = a := by dsimp [i]; omega
    rw [← hi, count_profileParts_index]
    rfl
  · have hl : a ∉ lam.val.parts := fun h => ha ⟨lam.val.parts_pos h, lam.property a h⟩
    have hr : a ∉ profileParts (partitionProfile lam) := by
      rw [mem_profileParts_iff]
      rintro ⟨i, rfl, _⟩
      exact ha ⟨by omega, by omega⟩
    simp [Multiset.count_eq_zero_of_notMem hl, Multiset.count_eq_zero_of_notMem hr]

def boundedPartitionProfileEquiv (m R : ℕ) : BoundedPartition m R ≃ Profile m R where
  toFun lam := ⟨partitionProfile lam, by
    rw [← sum_profileParts, profileParts_partitionProfile]
    exact lam.val.parts_sum⟩
  invFun r := ⟨⟨profileParts r.val, by
    intro a ha
    obtain ⟨i, rfl, _⟩ := (mem_profileParts_iff r.val a).mp ha
    omega, (sum_profileParts r.val).trans r.property⟩, by
      intro a ha
      obtain ⟨i, rfl, _⟩ := (mem_profileParts_iff r.val a).mp ha
      omega⟩
  left_inv lam := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact profileParts_partitionProfile lam
  right_inv r := by
    apply Subtype.ext
    funext i
    exact count_profileParts_index r.val i


instance boundedPartitionFintype (m R : ℕ) : Fintype (BoundedPartition m R) := by
  classical
  exact inferInstanceAs (Fintype {lam : Nat.Partition R // ∀ a ∈ lam.parts, a ≤ m})

instance profileFintype (m R : ℕ) : Fintype (Profile m R) :=
  Fintype.ofEquiv (BoundedPartition m R) (boundedPartitionProfileEquiv m R)

/-- Reindex any actual finite bounded-partition sum by multiplicities. -/
theorem sum_boundedPartition_eq_profile {A : Type*} [AddCommMonoid A]
    (m R : ℕ) (F : (Fin m → ℕ) → A) :
    (∑ lam : BoundedPartition m R, F (partitionProfile lam)) =
      ∑ r : Profile m R, F r.val :=
  Fintype.sum_equiv (boundedPartitionProfileEquiv m R) _ _ (fun _ => rfl)

theorem sum_map_profileParts {m : ℕ} (r : Fin m → ℕ) (g : ℕ → ℕ) :
    ((profileParts r).map g).sum = ∑ i, r i * g (i.val + 1) := by
  change (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom g))
    (∑ i, Multiset.replicate (r i) (i.val + 1)) = _
  rw [map_sum]
  simp

open GordonCanonicalPartitions GordonFiltration GordonDegree
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- Every statistic of the actual canonical block sizes reindexes by its
part multiplicities, with no chosen or assumed block correspondence. -/
theorem sum_canonicalMap_profile {m : ℕ}
    (lam : BoundedPartition m (Fintype.card ρ)) (g : ℕ → ℕ) :
    (∑ j, g (blockSize (canonicalMap (σ := ρ) lam.val) j)) =
      ∑ i, partitionProfile lam i * g (i.val + 1) := by
  have he := congrArg (fun s : Multiset ℕ => (s.map g).sum)
    (canonicalMap_rawParts (σ := ρ) lam.val)
  have he' : (∑ j, g (blockSize (canonicalMap (σ := ρ) lam.val) j)) =
      (lam.val.parts.map g).sum := by
    simpa only [rawParts, Multiset.map_map, Function.comp_def] using he
  rw [he', ← profileParts_partitionProfile]
  exact sum_map_profileParts _ _

/-- The canonical evaluation conductor has the literal minimum-kernel
multiplicity quadratic form used by the Section 5 source sum. -/
theorem canonicalMap_clusterDegree_add_card {m : ℕ}
    (lam : BoundedPartition m (Fintype.card ρ)) :
    GordonDivisor.clusterDegree (canonicalMap (σ := ρ) lam.val) + Fintype.card ρ =
      QSeries.profileQuadratic (partitionProfile lam) := by
  rw [clusterDegree_add_card, sum_canonicalMap_profile lam
    (fun a => ∑ j, min a (blockSize (canonicalMap (σ := ρ) lam.val) j))]
  simp only [QSeries.profileQuadratic]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_canonicalMap_profile lam (fun b => min (i.val + 1) b), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The linear profile energy is exactly the original particle number. -/
theorem partitionProfile_linear {m R : ℕ} (lam : BoundedPartition m R) :
    QSeries.profileLinear (partitionProfile lam) = R :=
  (boundedPartitionProfileEquiv m R lam).property

/-- The exact shifted conductor equals the q-series profile exponent. -/
theorem canonicalMap_clusterDegree_add_two_card {m : ℕ}
    (lam : BoundedPartition m (Fintype.card ρ)) :
    GordonDivisor.clusterDegree (canonicalMap (σ := ρ) lam.val) + 2 * Fintype.card ρ =
      QSeries.profileEnergy (partitionProfile lam) := by
  rw [QSeries.profileEnergy, partitionProfile_linear,
    ← canonicalMap_clusterDegree_add_card]
  omega


/-- The actual canonical block-size fiber counts are the partition's multiplicities. -/
theorem card_canonicalMap_size (lam : Nat.Partition (Fintype.card ρ)) (a : ℕ) :
    Nat.card {j // blockSize (canonicalMap (σ := ρ) lam) j = a} = lam.parts.count a := by
  classical
  rw [← canonicalMap_rawParts (σ := ρ) lam, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [rawParts, Multiset.count_map]
  change (Finset.univ.filter (fun j => blockSize (canonicalMap (σ := ρ) lam) j = a)).card =
    (Finset.univ.filter (fun j => a = blockSize (canonicalMap (σ := ρ) lam) j)).card
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]

private theorem reciprocal_zero : (QSeries.reciprocalQFactorial 0 : PowerSeries ℚ) = 1 := by
  simpa using (QSeries.qFactorial_mul_reciprocal (R := ℚ) 0)

/-- A count-factorial product is independent of the cutoff once all actual
partition parts lie below it. Empty multiplicities contribute the unit. -/
theorem factorial_product_eq_support {R : ℕ} (lam : Nat.Partition R)
    (N : ℕ) (hN : ∀ a ∈ lam.parts, a ≤ N) :
    (∏ i : Fin (N + 1), (QSeries.reciprocalQFactorial (lam.parts.count i.val) : PowerSeries ℚ)) =
      ∏ a ∈ lam.parts.toFinset, (QSeries.reciprocalQFactorial (lam.parts.count a) : PowerSeries ℚ) := by
  classical
  rw [Fin.prod_univ_eq_prod_range (fun a =>
    (QSeries.reciprocalQFactorial (lam.parts.count a) : PowerSeries ℚ))]
  symm
  apply Finset.prod_subset
  · intro a ha
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hN a (Multiset.mem_toFinset.mp ha)))
  · intro a _ ha
    rw [Multiset.count_eq_zero_of_notMem (by simpa using ha)]
    exact reciprocal_zero

/-- The canonical invariant denominator reindexes to exactly one factorial
for each nonzero size color. -/
theorem canonicalMap_factorial_product {m : ℕ}
    (lam : BoundedPartition m (Fintype.card ρ)) :
    (∏ i : Fin (Fintype.card ρ + 1), (QSeries.reciprocalQFactorial
      (Nat.card {j // blockSize (canonicalMap (σ := ρ) lam.val) j = i.val}) : PowerSeries ℚ)) =
      ∏ i : Fin m, (QSeries.reciprocalQFactorial (partitionProfile lam i) : PowerSeries ℚ) := by
  simp_rw [card_canonicalMap_size]
  rw [factorial_product_eq_support lam.val _ (fun _ h => lam.val.le_of_mem_parts h),
    ← factorial_product_eq_support lam.val m lam.property, Fin.prod_univ_succ]
  have hzero : lam.val.parts.count 0 = 0 :=
    Multiset.count_eq_zero_of_notMem (fun h => by have := lam.val.parts_pos h; omega)
  simp only [Fin.val_zero, hzero, reciprocal_zero, one_mul, Fin.val_succ]
  rfl


/-- The actual full Gordon conductor, with all residual species and the
original particle shift, is precisely the exponent of the proved q-series source. -/
theorem canonicalMap_fullDegree_sourceEnergy {m : ℕ}
    (lam : BoundedPartition (m + 1) (Fintype.card ρ))
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [LinearOrder α] [LinearOrder β] [LinearOrder γ] :
    GordonFullDivisor.fullDegree (α := α) (β := β) (γ := γ) (m + 1)
        (canonicalMap (σ := ρ) lam.val) + 2 * Fintype.card ρ +
        (Fintype.card α + Fintype.card β + Fintype.card γ) =
      QSeries.profileEnergy (partitionProfile lam) +
        (partitionProfile lam (Fin.last m) + 1) *
          (Fintype.card α + Fintype.card β + Fintype.card γ) +
        Fintype.card α * Fintype.card β := by
  have hc := card_canonicalMap_size (ρ := ρ) lam.val (m + 1)
  rw [Nat.card_eq_fintype_card] at hc
  rw [GordonFullDivisor.fullDegree_eq, hc]
  have he := canonicalMap_clusterDegree_add_two_card (ρ := ρ) lam
  change _ = _ + (lam.val.parts.count (m + 1) + 1) * _ + _
  nlinarith

end
end VOA.GordonPartitionProfile
