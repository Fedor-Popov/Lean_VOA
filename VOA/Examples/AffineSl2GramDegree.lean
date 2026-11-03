/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2JointChargeFlip
import VOA.Examples.VirasoroGramDegree

/-!
# Level-degree bounds for the actual joint affine Gram determinant

A central contraction replaces one creation mode by one level factor.
Keeping this count in the full coloured normal form gives uniform degree
bounds without discarding noncentral commutators. The resulting determinant
bound is ordinary polynomial algebra, not an assumption about roots.
-/
namespace VOA.AffineVOA.NormalOrdering
open Polynomial

/-- The span of normal-form terms whose central power plus remaining creation
length is at most d. Using a submodule makes the bound stable under cancellation. -/
noncomputable def lengthFiltration (d : ℕ) : Submodule ℂ NormalForm :=
  Submodule.span ℂ {f | ∃ t : Label, t.1+t.2.length ≤ d ∧ f=Finsupp.single t 1}

/-- Increasing the permitted length only enlarges the normal-form filtration. -/
theorem lengthFiltration_mono {d e : ℕ} (h : d ≤ e) :
    lengthFiltration d ≤ lengthFiltration e :=
  Submodule.span_mono (by rintro f ⟨t,ht,rfl⟩; exact ⟨t,ht.trans h,rfl⟩)

/-- A single term has filtration degree equal to its central power plus its
creation length. Arbitrary scalar coefficients do not change that bound. -/
theorem single_mem_lengthFiltration (t : Label) (a : ℂ) {d : ℕ}
    (h : t.1+t.2.length ≤ d) : Finsupp.single t a ∈ lengthFiltration d := by
  have ht : Finsupp.single t (1:ℂ) ∈ lengthFiltration d := Submodule.subset_span ⟨t,h,rfl⟩
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    Submodule.smul_mem (lengthFiltration d) a ht

/-- Prefixing a creation mode costs one unit of filtration degree. -/
theorem prepend_mem_lengthFiltration (i : Fin 3 × ℕ) {d : ℕ} {f : NormalForm}
    (h : f ∈ lengthFiltration d) : prepend i f ∈ lengthFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [prepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply single_mem_lengthFiltration
    simp only [List.length_cons]; omega
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Adding p central factors raises the filtration bound by p. -/
theorem centralShift_mem_lengthFiltration (p : ℕ) {d : ℕ} {f : NormalForm}
    (h : f ∈ lengthFiltration d) : centralShift p f ∈ lengthFiltration (p+d) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [centralShift, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    apply single_mem_lengthFiltration
    change p+t.1+t.2.length ≤ p+d
    omega
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Applying a creation mode raises the bound by one; every other mode
preserves it. The central term trades a creation mode for one central factor. -/
theorem modeNormal_mem_lengthFiltration (a : Fin 3) (m : ℤ) (w : List (Fin 3 × ℕ)) :
    modeNormal a m w ∈ lengthFiltration (w.length + if m < 0 then 1 else 0) := by
  induction w generalizing a m with
  | nil =>
    by_cases hm : m < 0
    · simp only [modeNormal, if_pos hm, List.length_nil]
      exact single_mem_lengthFiltration _ _ (by simp)
    · simp [modeNormal, hm]
  | cons i w ih =>
    by_cases hm : m < 0
    · simp only [modeNormal, if_pos hm, List.length_cons]
      exact single_mem_lengthFiltration _ _ (by simp)
    · simp only [modeNormal, if_neg hm, List.length_cons, Nat.add_zero]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · have hh := prepend_mem_lengthFiltration i (ih a m)
          simpa only [if_neg hm, Nat.add_zero] using hh
        · apply Submodule.sum_mem
          intro c hc
          apply Submodule.smul_mem
          apply lengthFiltration_mono (show w.length + (if m-(i.2:ℤ)-1 < 0 then 1 else 0) ≤
            w.length+1 by split_ifs <;> omega) (ih _ _)
      · split_ifs
        · exact single_mem_lengthFiltration _ _ (by simp; omega)
        · exact Submodule.zero_mem _

/-- A nonnegative mode preserves the filtration on arbitrary normal forms,
not only on a single creation word. -/
theorem actNormal_mem_lengthFiltration (a : Fin 3) (m : ℤ) (hm : 0 ≤ m)
    {d : ℕ} {f : NormalForm} (h : f ∈ lengthFiltration d) :
    actNormal a m f ∈ lengthFiltration d := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [actNormal, Finsupp.linearCombination_single, one_smul]
    apply lengthFiltration_mono ht
    have hh := centralShift_mem_lengthFiltration t.1 (modeNormal_mem_lengthFiltration a m t.2)
    simpa only [if_neg (by omega : ¬m < 0), Nat.add_zero] using hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- A word made entirely of creation modes is already a single normal-form
term, with central power zero and its original creation list. -/
theorem wordNormal_creation (w : List (Fin 3 × ℕ)) :
    wordNormal (w.map (fun i => (i.1,-(i.2:ℤ)-1))) = Finsupp.single (0,w) 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hm : -(i.2:ℤ)-1 < 0 := by omega
    have hi : (-(-(i.2:ℤ)-1)-1).toNat=i.2 := by omega
    rw [List.map_cons, wordNormal, ih]
    simp only [actNormal, Finsupp.linearCombination_single, one_smul]
    cases w <;> simp only [modeNormal, if_pos hm, hi, centralShift,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Nat.zero_add]

/-- Prefixing arbitrary vacuum-annihilating modes to a creation word preserves
its original length bound throughout the normal-ordering calculation. -/
theorem wordNormal_prefix_mem (u : List (Fin 3 × ℤ)) (v : List (Fin 3 × ℕ))
    (hu : ∀ m ∈ u, 0 ≤ m.2) :
    wordNormal (u ++ v.map (fun i => (i.1,-(i.2:ℤ)-1))) ∈ lengthFiltration v.length := by
  induction u with
  | nil =>
    rw [List.nil_append, wordNormal_creation]
    exact single_mem_lengthFiltration _ _ (by simp)
  | cons m u ih =>
    rw [List.cons_append, wordNormal]
    exact actNormal_mem_lengthFiltration m.1 m.2 (hu m (by simp))
      (ih (fun k hk => hu k (by simp [hk])))

/-- Keeping only the empty creation terms converts the filtration bound into
a bound on the degree in central charge of the vacuum-pairing polynomial. -/
theorem centralPolynomial_natDegree_le {d : ℕ} {f : NormalForm}
    (h : f ∈ lengthFiltration d) : (centralPolynomial f).natDegree ≤ d := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [centralPolynomial, Finsupp.linearCombination_single, one_smul]
    split_ifs
    · simpa only [natDegree_X_pow] using (Nat.le_add_right t.1 t.2.length).trans ht
    · simp
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add]
    exact natDegree_add_le_of_degree_le hf hg
  | smul a f _ hf =>
    rw [map_smul]
    exact (natDegree_smul_le _ _).trans hf


end VOA.AffineVOA.NormalOrdering
