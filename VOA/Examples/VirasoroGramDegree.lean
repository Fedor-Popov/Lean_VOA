/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroPartitionObstruction
import VOA.Examples.VirasoroFormSymmetry

/-!
# Degree bounds for the actual vacuum Gram polynomials

A central contraction consumes one creation mode. Normal forms therefore carry
a filtration by central power plus remaining creation-word length. Modes at
least -1 preserve it. This bounds the charge degree of each Gram entry by the
length of its column partition and the determinant degree by the sum of those
lengths. These bounds are inputs toward a determinant degree-comparison proof;
they do not assert the missing Kac factorization or its singular roots.
-/
namespace VOA.VirDeformModes.NormalOrdering
open Polynomial VirModule

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
theorem prepend_mem_lengthFiltration (i : ℕ) {d : ℕ} {f : NormalForm}
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
theorem modeNormal_mem_lengthFiltration (m : ℤ) (w : List ℕ) :
    modeNormal m w ∈ lengthFiltration (w.length + if m < -1 then 1 else 0) := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m < -1
    · simp only [modeNormal, if_pos hm, List.length_nil]
      exact single_mem_lengthFiltration _ _ (by simp)
    · simp [modeNormal, hm]
  | cons i w ih =>
    by_cases hm : m < -1
    · simp only [modeNormal, if_pos hm, List.length_cons]
      exact single_mem_lengthFiltration _ _ (by simp)
    · simp only [modeNormal, if_neg hm, List.length_cons, Nat.add_zero]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · have hh := prepend_mem_lengthFiltration i (ih m)
          simpa only [if_neg hm, Nat.add_zero] using hh
        · apply Submodule.smul_mem
          apply lengthFiltration_mono (show w.length + (if m-(i:ℤ)-2 < -1 then 1 else 0) ≤
            w.length+1 by split_ifs <;> omega) (ih _)
      · split_ifs
        · exact single_mem_lengthFiltration _ _ (by simp; omega)
        · exact Submodule.zero_mem _

/-- A mode at least -1 preserves the filtration on arbitrary normal forms,
not only on a single creation word. -/
theorem actNormal_mem_lengthFiltration (m : ℤ) (hm : -1 ≤ m)
    {d : ℕ} {f : NormalForm} (h : f ∈ lengthFiltration d) :
    actNormal m f ∈ lengthFiltration d := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t,ht,rfl⟩ := hf
    simp only [actNormal, Finsupp.linearCombination_single, one_smul]
    apply lengthFiltration_mono ht
    have hh := centralShift_mem_lengthFiltration t.1 (modeNormal_mem_lengthFiltration m t.2)
    simpa only [if_neg (by omega : ¬m < -1), Nat.add_zero] using hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- A word made entirely of creation modes is already a single normal-form
term, with central power zero and its original creation list. -/
theorem wordNormal_creation (w : List ℕ) :
    wordNormal (w.map (fun (i : ℕ) => -(i:ℤ)-2)) = Finsupp.single (0,w) 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hm : -(i:ℤ)-2 < -1 := by omega
    have hi : (-(-(i:ℤ)-2)-2).toNat=i := by omega
    rw [List.map_cons, wordNormal, ih]
    simp only [actNormal, Finsupp.linearCombination_single, one_smul]
    cases w <;> simp only [modeNormal, if_pos hm, hi, centralShift,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Nat.zero_add]

/-- Prefixing arbitrary vacuum-annihilating modes to a creation word preserves
its original length bound throughout the normal-ordering calculation. -/
theorem wordNormal_prefix_mem (u : List ℤ) (v : List ℕ)
    (hu : ∀ m ∈ u, -1 ≤ m) :
    wordNormal (u ++ v.map (fun (i : ℕ) => -(i:ℤ)-2)) ∈ lengthFiltration v.length := by
  induction u with
  | nil =>
    rw [List.nil_append, wordNormal_creation]
    exact single_mem_lengthFiltration _ _ (by simp)
  | cons m u ih =>
    rw [List.cons_append, wordNormal]
    exact actNormal_mem_lengthFiltration m (hu m (by simp))
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

/-- The charge degree of a partition Gram entry is at most the number of
creation modes in its column. Every central contraction consumes such a mode. -/
theorem partitionGramPolynomial_natDegree_le (n : ℕ) (i j : SortedOfEnergy n) :
    (partitionGramPolynomial n i j).natDegree ≤ j.val.length := by
  apply centralPolynomial_natDegree_le
  apply wordNormal_prefix_mem
  intro m hm
  simp only [partitionWord, List.mem_map, List.mem_reverse] at hm
  obtain ⟨a, ⟨k,hk,rfl⟩,rfl⟩ := hm
  omega

/-- The polynomial Gram matrix is symmetric before specializing the charge.
Equality at every complex charge follows from the proved symmetry of the
canonical form, and hence determines equality of the polynomials themselves. -/
theorem partitionGramPolynomial_symmetric (n : ℕ) (i j : SortedOfEnergy n) :
    partitionGramPolynomial n i j = partitionGramPolynomial n j i := by
  apply Polynomial.funext
  intro c
  simp only [partitionGramPolynomial, universal_gram_entry]
  exact VirFormSym.canB_isSymmetric c _ _

/-- Symmetry gives both the row and column bounds: a Gram entry's charge
degree cannot exceed the smaller of the two creation-word lengths. -/
theorem partitionGramPolynomial_natDegree_le_min (n : ℕ) (i j : SortedOfEnergy n) :
    (partitionGramPolynomial n i j).natDegree ≤ min i.val.length j.val.length := by
  apply le_min
  · rw [partitionGramPolynomial_symmetric n i j]
    exact partitionGramPolynomial_natDegree_le n j i
  · exact partitionGramPolynomial_natDegree_le n i j

/-- The determinant charge degree is bounded by the total number of parts
in all level-n partitions. Each permutation term uses every column once. -/
theorem partitionDeterminant_natDegree_le (n : ℕ) :
    (partitionGramPolynomial n).det.natDegree ≤ ∑ j : SortedOfEnergy n, j.val.length := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans
    (Finset.sum_le_sum (fun j _ => partitionGramPolynomial_natDegree_le n (σ j) j))

/-- With separate degree bounds for each factor, the coefficient at the sum
of the bounds is the product of the corresponding coefficients. No factor is
required to attain its bound, so vanishing leading entries are handled too. -/
theorem coeff_prod_sum_bounds {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial ℂ) (d : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (by simp))
        ((natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i hi => h i (by simp [hi])))),
      ih (fun i hi => h i (by simp [hi]))]

/-- For any polynomial matrix with a degree bound depending only on the
column, the determinant coefficient at the sum of the bounds is the determinant
of the matrix of column-top coefficients. This isolates the remaining leading
coefficient calculation from the permutation expansion. -/
theorem coeff_det_sum_column_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℂ)) (d : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = Matrix.det (fun i j => (M i j).coeff (d j)) := by
  rw [Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hc := coeff_prod_sum_bounds Finset.univ (fun j => M (σ j) j) d
    (fun j _ => h (σ j) j)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul] using hc
  · simpa only [hs, Units.neg_smul, one_smul, coeff_neg] using congrArg Neg.neg hc

/-- The matrix of coefficients at each column's maximal permitted charge
degree. Its determinant is the candidate top coefficient of the actual Gram
determinant; nonvanishing of this matrix determinant is not assumed. -/
noncomputable def partitionTopMatrix (n : ℕ) :
    Matrix (SortedOfEnergy n) (SortedOfEnergy n) ℂ :=
  fun i j => (partitionGramPolynomial n i j).coeff j.val.length

/-- The actual vacuum determinant's candidate top coefficient is exactly the
determinant of its column-top matrix. Proving that number nonzero would turn
the uniform upper degree bound into equality. -/
theorem partitionDeterminant_top_coeff (n : ℕ) :
    (partitionGramPolynomial n).det.coeff (∑ j : SortedOfEnergy n, j.val.length) =
      (partitionTopMatrix n).det :=
  coeff_det_sum_column_bounds _ _ (partitionGramPolynomial_natDegree_le n)

/-- A top-matrix entry vanishes whenever the row word is shorter than the
column word. Sorting partitions by length therefore exposes triangular blocks;
the equal-length blocks still require the central-contraction calculation. -/
theorem partitionTopMatrix_eq_zero_of_length_lt (n : ℕ) (i j : SortedOfEnergy n)
    (h : i.val.length < j.val.length) : partitionTopMatrix n i j = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt ((partitionGramPolynomial_natDegree_le_min n i j).trans
    (min_le_left _ _)) h

end VOA.VirDeformModes.NormalOrdering
