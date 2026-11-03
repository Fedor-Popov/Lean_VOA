/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaSingularEmbedding
import VOA.Examples.VirasoroGramDegree

/-!
# Highest-weight degree bounds for the actual Verma determinant

The charge is fixed while the highest weight is a polynomial variable.
A power of highest weight costs one unit, as does every remaining creation
operator. Positive modes preserve this filtration: producing a highest-weight
factor consumes a creation operator. The resulting bounds concern the actual
general Verma Gram matrix, including L₋₁, rather than the vacuum charge matrix.
They do not assert the existence or multiplicity of any Kac singular root.
-/
namespace VOA.InverseDS.VirasoroVerma
open Polynomial VirModule
open scoped Classical

/-- Polynomial word expressions of degree at most d, counting a highest-weight
power and a remaining creation operator each as one unit. The span formulation
keeps the estimate valid when different contributions cancel. -/
noncomputable def vermaWeightFiltration (d : ℕ) :
    Submodule ℂ (VermaPolynomialForm (Polynomial ℂ)) :=
  Submodule.span ℂ {f | ∃ k : ℕ, ∃ w : List ℕ,
    k+w.length≤d ∧ f=Finsupp.single w (X^k)}

/-- A larger filtration bound permits every expression allowed by the smaller one. -/
theorem vermaWeightFiltration_mono {d e : ℕ} (h : d≤e) :
    vermaWeightFiltration d≤vermaWeightFiltration e :=
  Submodule.span_mono (by rintro f ⟨k,w,hw,rfl⟩; exact ⟨k,w,hw.trans h,rfl⟩)

/-- A scalar multiple of a single highest-weight monomial has the expected
filtration bound. The scalar is complex and independent of highest weight. -/
theorem vermaWeightFiltration_single (k : ℕ) (w : List ℕ) (a : ℂ)
    {d : ℕ} (h : k+w.length≤d) :
    Finsupp.single w (a • (X^k : Polynomial ℂ))∈vermaWeightFiltration d := by
  have hm : Finsupp.single w (X^k : Polynomial ℂ)∈vermaWeightFiltration d :=
    Submodule.subset_span ⟨k,w,h,rfl⟩
  simpa only [Finsupp.smul_single] using (vermaWeightFiltration d).smul_mem a hm

/-- Prefixing one negative mode increases the permitted creation length by one. -/
theorem vermaWeightFiltration_prepend (i : ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaWeightFiltration d) :
    polynomialPrepend i f∈vermaWeightFiltration (d+1) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [polynomialPrepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    simpa only [one_smul] using vermaWeightFiltration_single k (i::w) 1 (by simp only [List.length_cons]; omega)
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Multiplication by p powers of highest weight increases the filtration
bound by p, for arbitrary finite polynomial word expressions. -/
theorem vermaWeightFiltration_shift (p : ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaWeightFiltration d) :
    (X^p : Polynomial ℂ) • f∈vermaWeightFiltration (p+d) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    rw [Finsupp.smul_single,smul_eq_mul,← pow_add]
    simpa only [one_smul] using vermaWeightFiltration_single (p+k) w 1 (by omega)
  | zero => simp
  | add f g _ _ hf hg => simpa only [smul_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [smul_comm (X^p : Polynomial ℂ) a] using Submodule.smul_mem _ a hf

/-- Positive modes preserve the word-length budget. Nonpositive modes may
increase it by one: a negative mode creates a letter and L₀ contributes the
highest weight. Central charge is constant in this calculation. -/
theorem vermaModePolynomial_weightFiltration (c : ℂ) (m : ℤ) (w : List ℕ) :
    vermaModePolynomial (Polynomial.C c) X m w∈
      vermaWeightFiltration (w.length + if m≤0 then 1 else 0) := by
  induction w generalizing m with
  | nil =>
    by_cases hm : m<0
    · simp only [vermaModePolynomial,if_pos hm,List.length_nil,if_pos (by omega : m≤0)]
      simpa only [pow_zero,one_smul] using
        vermaWeightFiltration_single 0 [(-m-1).toNat] 1 (by simp)
    · by_cases hz : m=0
      · subst m
        simp only [vermaModePolynomial,lt_self_iff_false,if_false,ite_true,List.length_nil,
          le_refl,Nat.zero_add]
        simpa only [pow_one,one_smul] using vermaWeightFiltration_single 1 [] 1 (by simp)
      · simp [vermaModePolynomial,hm,hz]
  | cons i w ih =>
    by_cases hm : m<0
    · simp only [vermaModePolynomial,if_pos hm,if_pos (by omega : m≤0)]
      simpa only [pow_zero,one_smul] using
        vermaWeightFiltration_single 0 ((-m-1).toNat::i::w) 1 (by simp)
    · rw [vermaModePolynomial,if_neg hm]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · have hh := vermaWeightFiltration_prepend i (ih m)
          simpa only [List.length_cons,Nat.add_right_comm] using hh
        · have hh := vermaWeightFiltration_mono
            (show w.length+(if m-(i:ℤ)-1≤0 then 1 else 0)≤
              (i::w).length+(if m≤0 then 1 else 0) by simp only [List.length_cons]; split_ifs <;> omega)
            (ih (m-(i:ℤ)-1))
          simpa only [algebraMap_smul] using
            (vermaWeightFiltration _).smul_mem ((m:ℂ)+(i:ℂ)+1) hh
      · by_cases hz : m-(i:ℤ)-1=0
        · rw [if_pos hz]
          have hh := vermaWeightFiltration_single 0 w ((((m:ℂ)^3-m)/12)*c)
            (d := (i::w).length+(if m≤0 then 1 else 0))
            (by simp only [List.length_cons]; omega)
          simpa [Algebra.smul_def,← map_mul] using hh
        · rw [if_neg hz]
          exact Submodule.zero_mem _

/-- A positive mode preserves the filtration on every expression, including
those with polynomial coefficients, by linearity over the polynomial ring. -/
theorem polynomialModeAction_weightFiltration (c : ℂ) (m : ℤ) (hm : 0<m)
    {d : ℕ} {f : VermaPolynomialForm (Polynomial ℂ)}
    (h : f∈vermaWeightFiltration d) :
    polynomialModeAction (Polynomial.C c) X m f∈vermaWeightFiltration d := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    rw [polynomialModeAction_single]
    apply vermaWeightFiltration_mono hw
    have hh := vermaWeightFiltration_shift k (vermaModePolynomial_weightFiltration c m w)
    simpa only [if_neg (by omega : ¬m≤0),Nat.add_zero] using hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [LinearMap.map_smul_of_tower] using Submodule.smul_mem _ a hf

/-- Extracting any PBW coordinate cannot increase highest-weight degree:
negative-word straightening has constant complex coefficients. -/
theorem polynomialFormCoordinate_natDegree_le {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaWeightFiltration d)
    (s : {w : List ℕ // SortedWord w}) :
    (polynomialFormCoordinate f s).natDegree≤d := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k,w,hw,rfl⟩ := hf
    simp only [polynomialFormCoordinate,Finsupp.sum_single_index,zero_mul]
    apply natDegree_mul_le.trans
    simpa using (show k≤d by omega)
  | zero => simp [polynomialFormCoordinate]
  | add f g _ _ hf hg =>
    rw [polynomialFormCoordinate_add]
    exact natDegree_add_le_of_degree_le hf hg
  | smul a f _ hf =>
    have he : polynomialFormCoordinate (a • f) s=a • polynomialFormCoordinate f s := by
      classical
      unfold polynomialFormCoordinate
      rw [Finsupp.sum_smul_index' (fun _ => zero_mul _)]
      simp only [Finsupp.sum,smul_mul_assoc,Finset.smul_sum]
    rw [he]
    exact (natDegree_smul_le _ _).trans hf

/-- Moving any left creation word across a pairing applies only positive
modes, so the final scalar's degree is bounded by the input filtration. -/
theorem vermaPairPolynomial_natDegree_le (c : ℂ) (u : List ℕ) {d : ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaWeightFiltration d) :
    (vermaPairPolynomial (Polynomial.C c) X u f).natDegree≤d := by
  induction u generalizing f with
  | nil => exact polynomialFormCoordinate_natDegree_le h _
  | cons i u ih => exact ih (polynomialModeAction_weightFiltration c ((i:ℤ)+1) (by omega) h)

/-- An actual general Verma Gram entry has highest-weight degree at most
the column partition length, uniformly at every fixed central charge. -/
theorem vermaWeightGramPolynomial_natDegree_le (c : ℂ) (n : ℕ) (i j : VermaPartitions n) :
    (vermaWeightGramPolynomial c n i j).natDegree≤j.val.length := by
  apply vermaPairPolynomial_natDegree_le
  simpa only [pow_zero,one_smul] using vermaWeightFiltration_single 0 j.val 1 (by simp)

/-- The actual highest-weight Gram polynomial is symmetric. Evaluation at
all complex weights reduces this to the proved contravariant symmetry. -/
theorem vermaWeightGramPolynomial_symmetric (c : ℂ) (n : ℕ) (i j : VermaPartitions n) :
    vermaWeightGramPolynomial c n i j=vermaWeightGramPolynomial c n j i := by
  apply Polynomial.funext
  intro h
  have he := vermaWeightGramPolynomial_eval c h n
  have hij := congrArg (fun M => M i j) he
  have hji := congrArg (fun M => M j i) he
  exact hij.trans ((vermaContravariant_symm c h _ _).trans hji.symm)

/-- Symmetry bounds each entry by the smaller of its two partition lengths. -/
theorem vermaWeightGramPolynomial_natDegree_le_min (c : ℂ) (n : ℕ)
    (i j : VermaPartitions n) :
    (vermaWeightGramPolynomial c n i j).natDegree≤min i.val.length j.val.length := by
  apply le_min
  · rw [vermaWeightGramPolynomial_symmetric c n i j]
    exact vermaWeightGramPolynomial_natDegree_le c n j i
  · exact vermaWeightGramPolynomial_natDegree_le c n i j

/-- The actual general Verma determinant's highest-weight degree is at most
the sum of the lengths of all level-n partitions, including parts one. This
upper bound does not assert that the determinant is nonzero or has Kac roots. -/
theorem vermaWeightDeterminant_natDegree_le (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det.natDegree≤
      ∑ j : VermaPartitions n, j.val.length := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans
    (Finset.sum_le_sum (fun j _ => vermaWeightGramPolynomial_natDegree_le c n (σ j) j))

/-- The candidate highest-weight leading matrix takes the coefficient at
each column's maximal permitted degree. Its invertibility is not assumed. -/
noncomputable def vermaWeightTopMatrix (c : ℂ) (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) ℂ :=
  fun i j => (vermaWeightGramPolynomial c n i j).coeff j.val.length

/-- The coefficient at the determinant degree bound is exactly the determinant
of the column-top matrix. Computing that matrix remains a separate step. -/
theorem vermaWeightDeterminant_top_coeff (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det.coeff (∑ j : VermaPartitions n, j.val.length)=
      (vermaWeightTopMatrix c n).det :=
  VirDeformModes.NormalOrdering.coeff_det_sum_column_bounds _ _
    (vermaWeightGramPolynomial_natDegree_le c n)

/-- A shorter row has zero coefficient at a longer column's degree bound.
Thus ordering partitions by length makes the top matrix block triangular. -/
theorem vermaWeightTopMatrix_zero_of_length_lt (c : ℂ) (n : ℕ)
    (i j : VermaPartitions n) (h : i.val.length<j.val.length) :
    vermaWeightTopMatrix c n i j=0 := by
  apply coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt ((vermaWeightGramPolynomial_natDegree_le_min c n i j).trans
    (min_le_left _ _)) h

end VOA.InverseDS.VirasoroVerma
