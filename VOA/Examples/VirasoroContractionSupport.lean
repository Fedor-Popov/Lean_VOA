/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroCentralContractions

/-!
# Mode-content conservation in central contractions

Each contraction removes exactly its matching creation index. Tracking the
multiset of removed and remaining indices proves that complete contractions
vanish for different partition words. Combined with the weighted error estimate,
this makes every equal-length top Gram block diagonal. Its diagonal values and
nonvanishing remain separate from this support argument.
-/
namespace VOA.VirDeformModes.NormalOrdering

/-- Normal forms whose remaining creation indices, together with the already
removed indices, give the original multiset. Central powers do not affect content. -/
noncomputable def contentRelation (s t : Multiset ℕ) : Submodule ℂ NormalForm :=
  Submodule.span ℂ {f | ∃ b : Label, t+(b.2:Multiset ℕ)=s ∧ f=Finsupp.single b 1}

/-- A single term satisfies the content relation when its index multisets do. -/
theorem single_mem_contentRelation (s t : Multiset ℕ) (b : Label) (a : ℂ)
    (h : t+(b.2:Multiset ℕ)=s) : Finsupp.single b a ∈ contentRelation s t := by
  have hb : Finsupp.single b (1:ℂ) ∈ contentRelation s t := Submodule.subset_span ⟨b,h,rfl⟩
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using Submodule.smul_mem _ a hb

/-- Adding a creation index adds the same index to the original content. -/
theorem prepend_mem_contentRelation (i : ℕ) {s t : Multiset ℕ} {f : NormalForm}
    (h : f ∈ contentRelation s t) : prepend i f ∈ contentRelation (s+{i}) t := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,hb,rfl⟩ := hf
    simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply single_mem_contentRelation
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm ({i} : Multiset ℕ),
      ← add_assoc, hb]
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Central powers leave the multiset of creation indices unchanged. -/
theorem centralShift_mem_contentRelation (p : ℕ) {s t : Multiset ℕ} {f : NormalForm}
    (h : f ∈ contentRelation s t) : centralShift p f ∈ contentRelation s t := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,hb,rfl⟩ := hf
    simp only [centralShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact single_mem_contentRelation _ _ _ _ hb
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Remembering additional already-removed indices on both sides preserves
the content equation. This combines successive contraction steps. -/
theorem contentRelation_add_left (a : Multiset ℕ) {s t : Multiset ℕ} :
    contentRelation s t ≤ contentRelation (a+s) (a+t) := by
  apply Submodule.span_le.mpr
  rintro f ⟨b,hb,rfl⟩
  exact single_mem_contentRelation _ _ _ _ (by rw [add_assoc,hb])

/-- A central contraction with positive mode a+2 removes exactly the creation
index a. Terms with a different first index merely commute past it. -/
theorem contractionNormal_content (a : ℕ) (w : List ℕ) :
    contractionNormal ((a:ℤ)+2) w ∈ contentRelation (w:Multiset ℕ) {a} := by
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons i w ih =>
    apply Submodule.add_mem
    · simpa [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm] using prepend_mem_contentRelation i ih
    · split_ifs with h
      · have hi : a=i := by omega
        subst i
        apply single_mem_contentRelation
        simp
      · exact Submodule.zero_mem _

/-- Acting on arbitrary normal forms adds the contracted index to the
removed multiset, and does not change the original content. -/
theorem actContraction_content (a : ℕ) {s t : Multiset ℕ} {f : NormalForm}
    (h : f ∈ contentRelation s t) :
    actContraction ((a:ℤ)+2) f ∈ contentRelation s (t+{a}) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,hb,rfl⟩ := hf
    simp only [actContraction, Finsupp.linearCombination_single, one_smul]
    have hh := contentRelation_add_left t
      (centralShift_mem_contentRelation b.1 (contractionNormal_content a b.2))
    rwa [hb] at hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- A word of contractions records its entire multiset of annihilated
indices, independently of the order in which the contractions act. -/
theorem applyContractions_content (u : List ℕ) {s t : Multiset ℕ} {f : NormalForm}
    (h : f ∈ contentRelation s t) :
    applyContractions (u.map (fun (a : ℕ) => (a:ℤ)+2)) f ∈
      contentRelation s (t+(u:Multiset ℕ)) := by
  induction u with
  | nil => simpa [applyContractions] using h
  | cons a u ih =>
    simpa [applyContractions, ← Multiset.cons_coe, ← Multiset.singleton_add, add_assoc, add_comm, add_left_comm] using actContraction_content a ih

/-- Vacuum pairing vanishes unless all original indices have been removed.
Indeed a retained empty creation word would force the two multisets equal. -/
theorem centralPolynomial_eq_zero_of_content {s t : Multiset ℕ} (hst : t≠s)
    {f : NormalForm} (h : f ∈ contentRelation s t) : centralPolynomial f = 0 := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,hb,rfl⟩ := hf
    have hw : b.2 ≠ [] := by intro hw; simp [hw] at hb; exact hst hb
    simp [centralPolynomial, hw]
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add,hf,hg,add_zero]
  | smul a f _ hf => simp only [map_smul,hf,smul_zero]

/-- Reversing and negating a partition's negative modes gives positive modes
with the reversed natural index list. This is the exact word used by adjointness. -/
theorem adjoint_partitionWord (n : ℕ) (i : VirModule.SortedOfEnergy n) :
    (partitionWord n i).reverse.map Neg.neg =
      i.val.reverse.map (fun (a : ℕ) => (a:ℤ)+2) := by
  simp only [partitionWord, List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  dsimp
  omega

/-- Distinct sorted partition words have distinct multisets of indices.
Sorting removes exactly the ambiguity of permutation, not genuine partitions. -/
theorem partition_content_ne {n : ℕ} (i j : VirModule.SortedOfEnergy n) (h : i≠j) :
    (i.val:Multiset ℕ) ≠ (j.val:Multiset ℕ) := by
  intro he
  apply h
  apply Subtype.ext
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hba hab)
    i.property.1 j.property.1 (Multiset.coe_eq_coe.mp he)

/-- Every off-diagonal entry of an equal-length top Gram block vanishes.
The weighted filtration removes noncentral errors; conservation of indices
then kills all central contractions for different sorted partition words. -/
theorem partitionTopMatrix_eq_zero_of_ne_equal_length (n : ℕ)
    (i j : VirModule.SortedOfEnergy n) (hne : i≠j) (hlen : i.val.length=j.val.length) :
    partitionTopMatrix n i j = 0 := by
  rw [partitionTopMatrix_eq_contractions n i j hlen, adjoint_partitionWord]
  have hf : Finsupp.single (0,j.val) (1:ℂ) ∈ contentRelation (j.val:Multiset ℕ) 0 :=
    single_mem_contentRelation _ _ _ _ (by simp)
  have hh := applyContractions_content i.val.reverse hf
  simp only [zero_add, Multiset.coe_reverse] at hh
  rw [centralPolynomial_eq_zero_of_content (partition_content_ne i j hne) hh]
  simp

end VOA.VirDeformModes.NormalOrdering
