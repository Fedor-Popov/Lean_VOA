/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaGramLeading
import Mathlib.Data.Multiset.Sort

/-!
# The partition count behind the Kac determinant degree

Marking an occurrence of a part in a partition can instead be recorded by
its part size r, its occurrence number s, and the partition left after removing
s copies of r. This gives the exact count of the expected Kac exponents.
It is an ordinary finite combinatorial identity: no singular-state existence,
Kac factorization or minimal-model rigidity is assumed or concluded.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule
open scoped Classical

/-- A multiset of creation indices has energy equal to the sum of their
positive mode sizes. Index a represents the part a+1, including translation. -/
def vermaMultisetEnergy (s : Multiset ℕ) : ℕ := (s.map (fun a => a+1)).sum

/-- Disjoint union adds the energies of creation multisets. -/
theorem vermaMultisetEnergy_add (s t : Multiset ℕ) :
    vermaMultisetEnergy (s+t)=vermaMultisetEnergy s+vermaMultisetEnergy t := by
  simp [vermaMultisetEnergy]

/-- k copies of the mode index a have total energy k(a+1). -/
theorem vermaMultisetEnergy_replicate (k a : ℕ) :
    vermaMultisetEnergy (Multiset.replicate k a)=k*(a+1) := by
  simp [vermaMultisetEnergy]

/-- Multiset energy agrees exactly with the existing energy of actual Verma
creation words, so the ensuing count uses the package's PBW index set. -/
theorem vermaMultisetEnergy_coe (w : List ℕ) :
    vermaMultisetEnergy (w:Multiset ℕ)=energyHW w := by
  simp [vermaMultisetEnergy,energyHW]

/-- The order-free version of the actual Verma level partition set. Sorting
below proves equivalence, rather than assuming an external partition count. -/
def VermaMultisetPartitions (n : ℕ) := {s : Multiset ℕ // vermaMultisetEnergy s=n}

/-- Forgetting order and sorting back gives an exact equivalence between
actual ordered PBW partitions and multisets of the same positive energy. -/
noncomputable def vermaPartitionMultisetEquiv (n : ℕ) :
    VermaPartitions n ≃ VermaMultisetPartitions n where
  toFun w := ⟨w.val,(vermaMultisetEnergy_coe w.val).trans w.property.2⟩
  invFun s := ⟨s.val.sort (· ≥ ·),Multiset.pairwise_sort _ _,by
    rw [← vermaMultisetEnergy_coe,Multiset.sort_eq]
    exact s.property⟩
  left_inv w := by
    apply Subtype.ext
    change (w.val:Multiset ℕ).sort (· ≥ ·)=w.val
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hba hab)
      (Multiset.pairwise_sort _ _) w.property.1
      (Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _))
  right_inv s := Subtype.ext (Multiset.sort_eq _ _)

/-- The multiset partition type is finite through its proved equivalence
with the actual finite Verma partition basis. -/
noncomputable instance vermaMultisetPartitionsFintype (n : ℕ) :
    Fintype (VermaMultisetPartitions n) := Fintype.ofEquiv (VermaPartitions n)
      (vermaPartitionMultisetEquiv n)

/-- The two partition descriptions have the same cardinality at every level. -/
theorem vermaMultisetPartitions_card (n : ℕ) :
    Fintype.card (VermaMultisetPartitions n)=Fintype.card (VermaPartitions n) :=
  (Fintype.card_congr (vermaPartitionMultisetEquiv n)).symm

/-- Removing k existing copies of a part subtracts exactly their positive
energy. The remaining multiset has nonnegative energy automatically. -/
theorem vermaMultisetEnergy_sub_replicate (s : Multiset ℕ) (k a : ℕ)
    (hk : k≤s.count a) :
    vermaMultisetEnergy (s-Multiset.replicate k a)+k*(a+1)=vermaMultisetEnergy s := by
  rw [← vermaMultisetEnergy_replicate,← vermaMultisetEnergy_add,
    Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp hk)]

/-- The energy spent on any k occurrences cannot exceed the partition's
level. This also excludes impossible occurrence thresholds. -/
theorem vermaPartMultiplicity_energy_le (n a k : ℕ) (s : VermaMultisetPartitions n)
    (hk : k≤s.val.count a) : k*(a+1)≤n := by
  have he := vermaMultisetEnergy_sub_replicate s.val k a hk
  rw [s.property] at he
  omega

/-- A partition of n has at most n parts, since every part has positive size. -/
theorem vermaMultisetPartitions_card_le (n : ℕ) (s : VermaMultisetPartitions n) :
    s.val.card≤n := by
  let w := (vermaPartitionMultisetEquiv n).symm s
  have he : (w.val:Multiset ℕ)=s.val :=
    congrArg Subtype.val ((vermaPartitionMultisetEquiv n).apply_symm_apply s)
  rw [← he]
  exact (verma_length_le_energy w.val).trans_eq w.property.2

/-- Every occurring creation index is strictly below the total level. -/
theorem vermaMultisetPartitions_mem_lt (n : ℕ) (s : VermaMultisetPartitions n)
    (a : ℕ) (ha : a∈s.val) : a<n := by
  have hh := vermaPartMultiplicity_energy_le n a 1 s
    (by simpa only [Nat.succ_le_iff] using (Multiset.count_pos.mpr ha))
  omega

/-- Removing k copies of a fixed part and adding them back is a bijection.
Thus partitions containing at least k such parts are counted by the full
partition number at the reduced energy n-k(a+1). -/
noncomputable def vermaRemovePartsEquiv (n a k : ℕ) (hk : k*(a+1)≤n) :
    {s : VermaMultisetPartitions n // k≤s.val.count a} ≃
      VermaMultisetPartitions (n-k*(a+1)) where
  toFun s := ⟨s.val.val-Multiset.replicate k a,by
    have he := vermaMultisetEnergy_sub_replicate s.val.val k a s.property
    rw [s.val.property] at he
    omega⟩
  invFun s := ⟨⟨s.val+Multiset.replicate k a,by
    rw [vermaMultisetEnergy_add,vermaMultisetEnergy_replicate,s.property]
    omega⟩,by simp⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp s.property)
  right_inv s := by
    apply Subtype.ext
    simp

/-- The number of partitions meeting a multiplicity threshold is the lower
partition number when the energy fits, and zero otherwise. The zero branch
is essential: natural subtraction alone would incorrectly count level zero. -/
theorem vermaPartThreshold_card (n a k : ℕ) :
    Fintype.card {s : VermaMultisetPartitions n // k≤s.val.count a}=
      if k*(a+1)≤n then Fintype.card (VermaPartitions (n-k*(a+1))) else 0 := by
  by_cases hk : k*(a+1)≤n
  · rw [if_pos hk,Fintype.card_congr (vermaRemovePartsEquiv n a k hk),vermaMultisetPartitions_card]
  · rw [if_neg hk]
    letI : IsEmpty {s : VermaMultisetPartitions n // k≤s.val.count a} :=
      ⟨fun s => hk (vermaPartMultiplicity_energy_le n a k s.val s.property)⟩
    exact Fintype.card_eq_zero

/-- A bounded natural count is the sum of its successive nonempty threshold
indicators. This is the finite layer-count identity used for multiplicities. -/
theorem vermaCount_eq_sum_thresholds (n m : ℕ) (hm : m≤n) :
    m=∑ k ∈ Finset.range n, if k+1≤m then 1 else 0 := by
  have he : (Finset.range n).filter (fun k => k+1≤m)=Finset.range m := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [← Finset.sum_filter,he]
  simp

/-- Summing one part's multiplicity over all level-n partitions counts all
possible occurrence numbers and their reduced-energy descendant partitions. -/
theorem verma_sum_partCount (n a : ℕ) :
    (∑ s : VermaMultisetPartitions n, s.val.count a)=
      ∑ k ∈ Finset.range n, if (k+1)*(a+1)≤n then
        Fintype.card (VermaPartitions (n-(k+1)*(a+1))) else 0 := by
  calc
    _ = ∑ s : VermaMultisetPartitions n,
        ∑ k ∈ Finset.range n, if k+1≤s.val.count a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact vermaCount_eq_sum_thresholds n _
        ((Multiset.count_le_card _ _).trans (vermaMultisetPartitions_card_le n s))
    _ = ∑ k ∈ Finset.range n,
        ∑ s : VermaMultisetPartitions n, if k+1≤s.val.count a then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← vermaPartThreshold_card]
      simp only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]

/-- The exact Kac degree-count identity on the package's actual partition
index set: every marked part is uniquely a positive size a+1, an occurrence
number k+1, and a partition of n-(a+1)(k+1). This is a finite combinatorial
count and supplies no singular-vector or determinant-factor assumption. -/
theorem verma_partition_lengths_eq_kac_count (n : ℕ) :
    (∑ w : VermaPartitions n, w.val.length)=
      ∑ a ∈ Finset.range n, ∑ k ∈ Finset.range n,
        if (a+1)*(k+1)≤n then
          Fintype.card (VermaPartitions (n-(a+1)*(k+1))) else 0 := by
  calc
    _ = ∑ s : VermaMultisetPartitions n, s.val.card :=
      Fintype.sum_equiv (vermaPartitionMultisetEquiv n) _ _ (fun _ => rfl)
    _ = ∑ s : VermaMultisetPartitions n, ∑ a ∈ Finset.range n, s.val.count a := by
      apply Finset.sum_congr rfl
      intro s hs
      exact (Multiset.sum_count_eq_card
        (fun a ha => Finset.mem_range.mpr (vermaMultisetPartitions_mem_lt n s a ha))).symm
    _ = ∑ a ∈ Finset.range n, ∑ s : VermaMultisetPartitions n, s.val.count a := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa only [Nat.mul_comm] using verma_sum_partCount n a

/-- The actual Verma determinant degree equals the sum of the expected full
Verma descendant multiplicities over all positive Kac label pairs rs≤n.
This identifies the degree budget; proving the corresponding general factors
is still a separate representation-theoretic task. -/
theorem vermaWeightDeterminant_degree_eq_kac_count (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det.natDegree=
      ∑ a ∈ Finset.range n, ∑ k ∈ Finset.range n,
        if (a+1)*(k+1)≤n then
          Fintype.card (VermaPartitions (n-(a+1)*(k+1))) else 0 := by
  rw [vermaWeightDeterminant_natDegree,verma_partition_lengths_eq_kac_count]

end VOA.InverseDS.VirasoroVerma
