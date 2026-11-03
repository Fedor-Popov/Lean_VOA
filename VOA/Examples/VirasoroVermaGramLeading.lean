/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaWeightContractions

/-!
# Sharp highest-weight degree of the general Verma determinant

Leading contractions conserve the multiset of negative-mode indices.
Equal-length leading Gram blocks are therefore diagonal. Their diagonal
entries are products of positive multiplicities and 2m factors, including
m=1. This proves a nonzero leading coefficient at every charge and level.
Kac roots and their prescribed multiplicities remain separate mathematics.
-/
namespace VOA.InverseDS.VirasoroVerma
open Polynomial VirModule
open scoped Classical

/-- Polynomial expressions whose remaining indices, together with those
already removed, recover the original multiset. Polynomial coefficients do
not change the content equation. -/
noncomputable def vermaContentRelation (s t : Multiset ℕ) :
    Submodule (Polynomial ℂ) (VermaPolynomialForm (Polynomial ℂ)) :=
  Submodule.span (Polynomial ℂ) {f | ∃ w : List ℕ,
    t+(w:Multiset ℕ)=s ∧ f=Finsupp.single w 1}

/-- A single word with arbitrary polynomial coefficient obeys its multiset
content equation. -/
theorem vermaContentRelation_single (s t : Multiset ℕ) (w : List ℕ)
    (a : Polynomial ℂ) (h : t+(w:Multiset ℕ)=s) :
    Finsupp.single w a∈vermaContentRelation s t := by
  have hh : Finsupp.single w (1:Polynomial ℂ)∈vermaContentRelation s t :=
    Submodule.subset_span ⟨w,h,rfl⟩
  simpa using Submodule.smul_mem (vermaContentRelation s t) a hh

/-- Prefixing one remaining index adds it to the original content. -/
theorem vermaContentRelation_prepend (i : ℕ) {s t : Multiset ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContentRelation s t) :
    polynomialPrepend i f∈vermaContentRelation (s+{i}) t := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w,hw,rfl⟩ := hf
    simp only [polynomialPrepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    apply vermaContentRelation_single
    rw [← Multiset.cons_coe,← Multiset.singleton_add,add_comm ({i}:Multiset ℕ),← add_assoc,hw]
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- Recording additional removed indices on both sides preserves content. -/
theorem vermaContentRelation_add_left (a : Multiset ℕ) {s t : Multiset ℕ} :
    vermaContentRelation s t≤vermaContentRelation (a+s) (a+t) := by
  apply Submodule.span_le.mpr
  rintro f ⟨w,hw,rfl⟩
  exact vermaContentRelation_single _ _ _ _ (by rw [add_assoc,hw])

/-- A contraction at positive mode a+1 removes exactly creation index a. -/
theorem vermaContractionNormal_content (a : ℕ) (w : List ℕ) :
    vermaContractionNormal ((a:ℤ)+1) w∈vermaContentRelation (w:Multiset ℕ) {a} := by
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons i w ih =>
    apply Submodule.add_mem
    · simpa [← Multiset.cons_coe,← Multiset.singleton_add,add_comm] using
        vermaContentRelation_prepend i ih
    · split_ifs with h
      · have hi : a=i := by omega
        subst i
        exact vermaContentRelation_single _ _ _ _ (by simp)
      · exact Submodule.zero_mem _

/-- A contraction on arbitrary expressions adds its index to the removed
multiset while leaving original content fixed. -/
theorem vermaContractionAction_content (a : ℕ) {s t : Multiset ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContentRelation s t) :
    vermaContractionAction ((a:ℤ)+1) f∈vermaContentRelation s (t+{a}) := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w,hw,rfl⟩ := hf
    simp only [vermaContractionAction,Finsupp.linearCombination_single,one_smul]
    have hh := vermaContentRelation_add_left t (vermaContractionNormal_content a w)
    rwa [hw] at hh
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul a f _ hf => simpa only [map_smul] using Submodule.smul_mem _ a hf

/-- A whole contraction word records its complete multiset of removed indices. -/
theorem vermaContractionWord_content (u : List ℕ) {s t : Multiset ℕ}
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContentRelation s t) :
    vermaContractionWord u f∈vermaContentRelation s (t+(u:Multiset ℕ)) := by
  induction u generalizing t f with
  | nil => simpa [vermaContractionWord] using h
  | cons a u ih =>
    simpa [vermaContractionWord,← Multiset.cons_coe,← Multiset.singleton_add,
      add_assoc,add_comm,add_left_comm] using ih (vermaContractionAction_content a h)

/-- Extracting the highest coefficient of one nonempty word gives zero,
with any polynomial coefficient and without a sortedness assumption. -/
theorem vermaHighestPolynomial_single_cons (i : ℕ) (w : List ℕ) (a : Polynomial ℂ) :
    vermaHighestPolynomial (Finsupp.single (i::w) a)=0 := by
  simp only [vermaHighestPolynomial,Finsupp.linearCombination_single,smul_eq_mul]
  change a*Polynomial.C (vermaHighestCoordinate 0 0 (negWord 0 0 (i::w)))=0
  rw [vermaHighestCoordinate_cons,map_zero,mul_zero]

/-- A nonzero highest coordinate requires all original indices to have
been removed. Otherwise every surviving creation word is nonempty. -/
theorem vermaHighestPolynomial_zero_of_content {s t : Multiset ℕ} (hst : t≠s)
    {f : VermaPolynomialForm (Polynomial ℂ)} (h : f∈vermaContentRelation s t) :
    vermaHighestPolynomial f=0 := by
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w,hw,rfl⟩ := hf
    cases w with
    | nil => simp at hw; exact (hst hw).elim
    | cons i w => exact vermaHighestPolynomial_single_cons i w 1
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add,hf,hg,add_zero]
  | smul a f _ hf => simp only [map_smul,hf,smul_zero]

/-- Different ordered partitions have different multisets. Equal-length top
blocks therefore have no off-diagonal contributions from leading contractions. -/
theorem vermaWeightTopMatrix_zero_of_ne_equal_length (c : ℂ) (n : ℕ)
    (i j : VermaPartitions n) (hne : i≠j) (hlen : i.val.length=j.val.length) :
    vermaWeightTopMatrix c n i j=0 := by
  rw [vermaWeightTopMatrix_eq_contractions c n i j hlen]
  have hf := vermaContentRelation_single (j.val:Multiset ℕ) 0 j.val 1 (by simp)
  have hh := vermaContractionWord_content i.val hf
  simp only [zero_add] at hh
  have hne' : (i.val:Multiset ℕ)≠(j.val:Multiset ℕ) := by
    intro he
    apply hne
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hba hab)
      i.property.1 j.property.1 (Multiset.coe_eq_coe.mp he)
  rw [vermaHighestPolynomial_zero_of_content hne' hh]
  simp

/-- If a creation index never occurs, its leading contraction is zero. -/
theorem vermaContractionNormal_zero_of_not_mem (a : ℕ) (w : List ℕ) (ha : a∉w) :
    vermaContractionNormal ((a:ℤ)+1) w=0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hai : a≠i := by intro h; subst i; simp at ha
    have haw : a∉w := fun h => ha (List.mem_cons_of_mem i h)
    have hmode : ¬(a:ℤ)+1-(i:ℤ)-1=0 := by omega
    simp [vermaContractionNormal,ih haw,hmode]

/-- In natural creation indices, a matching contraction has polynomial
coefficient 2(a+1)X. In particular the translation index a=0 is nonzero. -/
theorem vermaContractionNormal_cons_index (a i : ℕ) (w : List ℕ) :
    vermaContractionNormal ((a:ℤ)+1) (i::w)=
      polynomialPrepend i (vermaContractionNormal ((a:ℤ)+1) w)+
      if a=i then Finsupp.single w ((2*((a:ℂ)+1)) • (X:Polynomial ℂ)) else 0 := by
  rw [vermaContractionNormal]
  have he : (a:ℤ)+1-(i:ℤ)-1=0 ↔ a=i := by omega
  by_cases h : a=i
  · subst i
    simp only [he,ite_true,Int.cast_add,Int.cast_natCast,Int.cast_one,Algebra.smul_def]
    rw [show (a:ℂ)+1+a+1=2*(a+1) by ring]
  · simp [he,h]

/-- On a sorted word all removals of its leading index leave the same
residual word. Their number is exactly the index's multiplicity. -/
theorem vermaContractionNormal_sorted_head (a : ℕ) (w : List ℕ)
    (hs : (a::w).Pairwise (· ≥ ·)) :
    vermaContractionNormal ((a:ℤ)+1) (a::w)=
      Finsupp.single w ((((w.count a+1:ℕ):ℂ)*(2*((a:ℂ)+1))) • (X:Polynomial ℂ)) := by
  induction w with
  | nil =>
    rw [vermaContractionNormal_cons_index]
    simp [vermaContractionNormal]
  | cons b v ih =>
    have hs' := List.pairwise_cons.mp hs
    have hv := List.pairwise_cons.mp hs'.2
    by_cases hab : a=b
    · subst b
      have he := ih hs'.2
      rw [vermaContractionNormal_cons_index,if_pos rfl,he]
      simp only [polynomialPrepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
        ← Finsupp.single_add,← add_smul]
      congr 2
      simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one]
      ring
    · have hnot : a∉b::v := by
        intro ha
        rcases List.mem_cons.mp ha with ha | ha
        · exact hab ha
        · have hba := hs'.1 b (by simp)
          have hab' := hv.1 a ha
          exact hab (by omega)
      have hz := vermaContractionNormal_zero_of_not_mem a (b::v) hnot
      have hc : (b::v).count a=0 := List.count_eq_zero.mpr hnot
      rw [vermaContractionNormal_cons_index,if_pos rfl,hz]
      simp [hc]

/-- The exact leading diagonal scalar. Repetitions contribute factorials,
and each mode L₋ₘ contributes the nonzero factor 2m. -/
noncomputable def vermaDiagonalContraction : List ℕ → ℂ
  | [] => 1
  | a::w => (((w.count a+1:ℕ):ℂ)*(2*((a:ℂ)+1)))*vermaDiagonalContraction w

/-- Every leading diagonal factor is nonzero, including those from L₋₁. -/
theorem vermaDiagonalContraction_ne_zero (w : List ℕ) : vermaDiagonalContraction w≠0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons a w ih =>
    apply mul_ne_zero _ ih
    apply mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero (w.count a))
    apply mul_ne_zero (by norm_num)
    exact_mod_cast (show a+1≠0 by omega)

/-- Contracting a sorted word against its actual adjoint leaves only the
highest vector, with one X factor per letter and the exact diagonal scalar. -/
theorem vermaContractionWord_diagonal (w : List ℕ) (hs : w.Pairwise (· ≥ ·)) :
    vermaContractionWord w (Finsupp.single w (1:Polynomial ℂ))=
      Finsupp.single [] (vermaDiagonalContraction w • (X^w.length : Polynomial ℂ)) := by
  induction w with
  | nil => simp [vermaContractionWord,vermaDiagonalContraction]
  | cons a w ih =>
    simp only [vermaContractionWord,LinearMap.comp_apply,vermaContractionAction,
      Finsupp.linearCombination_single,one_smul]
    rw [vermaContractionNormal_sorted_head a w hs]
    have he : Finsupp.single w ((((w.count a+1:ℕ):ℂ)*(2*((a:ℂ)+1))) • (X:Polynomial ℂ))=
        ((((w.count a+1:ℕ):ℂ)*(2*((a:ℂ)+1))) • (X:Polynomial ℂ)) • Finsupp.single w 1 := by simp
    rw [he,map_smul,ih (List.pairwise_cons.mp hs).2]
    simp only [Finsupp.smul_single,vermaDiagonalContraction,List.length_cons]
    congr 1
    simp only [Algebra.smul_def,Algebra.algebraMap_self_apply,map_mul,pow_succ]
    ring

/-- The highest-coordinate map takes the empty word to its polynomial
coefficient, by the normalized highest-vector form. -/
theorem vermaHighestPolynomial_single_nil (a : Polynomial ℂ) :
    vermaHighestPolynomial (Finsupp.single [] a)=a := by
  simp only [vermaHighestPolynomial,Finsupp.linearCombination_single,smul_eq_mul]
  change a*Polynomial.C (vermaHighestCoordinate 0 0 (highestVector 0 0))=a
  rw [vermaHighestCoordinate_highest,map_one,mul_one]

/-- Every actual leading diagonal Gram entry is the explicit nonzero product. -/
theorem vermaWeightTopMatrix_diagonal (c : ℂ) (n : ℕ) (i : VermaPartitions n) :
    vermaWeightTopMatrix c n i i=vermaDiagonalContraction i.val := by
  rw [vermaWeightTopMatrix_eq_contractions c n i i rfl,
    vermaContractionWord_diagonal i.val i.property.1,vermaHighestPolynomial_single_nil]
  simp

/-- A nonidentity permutation contributes zero to the top determinant. A
nonzero term must preserve every partition length, and then every partition. -/
theorem vermaWeightTopMatrix_perm_prod_zero (c : ℂ) (n : ℕ)
    (σ : Equiv.Perm (VermaPartitions n)) (hσ : σ≠1) :
    ∏ j : VermaPartitions n, vermaWeightTopMatrix c n (σ j) j=0 := by
  by_contra hp
  have hne : ∀ j, vermaWeightTopMatrix c n (σ j) j≠0 := by
    intro j hj
    exact hp (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hle : ∀ j : VermaPartitions n, j.val.length≤(σ j).val.length := by
    intro j
    by_contra hj
    exact hne j (vermaWeightTopMatrix_zero_of_length_lt c n (σ j) j (by omega))
  have hsum : (∑ j : VermaPartitions n, j.val.length)=∑ j : VermaPartitions n, (σ j).val.length :=
    (Equiv.sum_comp σ (fun j => j.val.length)).symm
  have heq : ∀ j : VermaPartitions n, j.val.length=(σ j).val.length :=
    fun j => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum j (Finset.mem_univ j)
  apply hσ
  apply Equiv.ext
  intro j
  change σ j=j
  by_contra hj
  exact hne j (vermaWeightTopMatrix_zero_of_ne_equal_length c n (σ j) j hj (heq j).symm)

/-- The leading matrix determinant is precisely the product of diagonal
contraction values, independently of central charge. -/
theorem vermaWeightTopMatrix_det (c : ℂ) (n : ℕ) :
    (vermaWeightTopMatrix c n).det=∏ j : VermaPartitions n, vermaDiagonalContraction j.val := by
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (VermaPartitions n))]
  · simp [vermaWeightTopMatrix_diagonal]
  · intro σ hσ hne
    rw [vermaWeightTopMatrix_perm_prod_zero c n σ hne,smul_zero]
  · simp

/-- The candidate leading coefficient is nonzero at every charge and level. -/
theorem vermaWeightTopMatrix_det_ne_zero (c : ℂ) (n : ℕ) :
    (vermaWeightTopMatrix c n).det≠0 := by
  rw [vermaWeightTopMatrix_det]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => vermaDiagonalContraction_ne_zero j.val)

/-- The actual general Verma highest-weight determinant is never identically
zero, even when its fixed central charge is a minimal-model charge. -/
theorem vermaWeightDeterminant_ne_zero (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det≠0 := by
  intro hz
  have hh := vermaWeightTopMatrix_det_ne_zero c n
  rw [← vermaWeightDeterminant_top_coeff,hz,Polynomial.coeff_zero] at hh
  exact hh rfl

/-- The highest-weight degree bound is attained exactly: it is the sum of
all partition lengths, including parts one. This proves sharp degree, not roots. -/
theorem vermaWeightDeterminant_natDegree (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det.natDegree=∑ j : VermaPartitions n, j.val.length := by
  apply le_antisymm (vermaWeightDeterminant_natDegree_le c n)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [vermaWeightDeterminant_top_coeff]
  exact vermaWeightTopMatrix_det_ne_zero c n

/-- The exact leading coefficient is the charge-independent product of
factorial multiplicities and 2m factors. No general Kac factorization is assumed. -/
theorem vermaWeightDeterminant_leadingCoeff (c : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).det.leadingCoeff=
      ∏ j : VermaPartitions n, vermaDiagonalContraction j.val := by
  rw [Polynomial.leadingCoeff,vermaWeightDeterminant_natDegree,
    vermaWeightDeterminant_top_coeff,vermaWeightTopMatrix_det]

/-- Evaluating the highest-weight determinant gives the determinant of the
actual normalized Gram matrix at that parameter. -/
theorem vermaWeightDeterminant_eval (c h : ℂ) (n : ℕ) :
    ((vermaWeightGramPolynomial c n).det).eval h=(vermaGramMatrix c h n).det := by
  have he := congrArg Matrix.det (vermaWeightGramPolynomial_eval c h n)
  change ((vermaWeightGramPolynomial c n).map (Polynomial.evalRingHom h)).det=_ at he
  exact ((Polynomial.evalRingHom h).map_det (vermaWeightGramPolynomial c n)).trans he

/-- At any fixed charge and level there are only finitely many highest
weights with a degenerate actual Gram form. This does not identify them
with the Kac labels; that representation-theoretic identification is open. -/
theorem vermaGram_degenerate_finite (c : ℂ) (n : ℕ) :
    Set.Finite {h : ℂ | (vermaGramMatrix c h n).det=0} := by
  simpa only [Polynomial.IsRoot.def,vermaWeightDeterminant_eval] using
    Polynomial.finite_setOf_isRoot (vermaWeightDeterminant_ne_zero c n)

/-- The sum of actual Gram nullities at distinct highest weights is bounded
by the exact partition-length degree. Thus the proved singular-descendant
lower bounds face a proved finite upper budget at every charge. -/
theorem sum_vermaNullities_le_lengths {τ : Type*} [Fintype τ]
    (c : ℂ) (n : ℕ) (h : τ → ℂ) (hh : Function.Injective h) :
    (∑ t, Module.finrank ℂ (LinearMap.ker (vermaGramMatrix c (h t) n).vecMulLinear))≤
      ∑ j : VermaPartitions n, j.val.length := by
  have hb := VirDeformModes.NormalOrdering.sum_nullities_le_det_degree
    (vermaWeightGramPolynomial c n) (vermaWeightDeterminant_ne_zero c n) h hh
  rw [vermaWeightDeterminant_natDegree] at hb
  have he : (∑ t, Module.finrank ℂ (LinearMap.ker (vermaGramMatrix c (h t) n).vecMulLinear))=
      ∑ t, Module.finrank ℂ (LinearMap.ker
        ((vermaWeightGramPolynomial c n).map (Polynomial.eval (h t))).vecMulLinear) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact congrArg (fun M : Matrix (VermaPartitions n) (VermaPartitions n) ℂ =>
      Module.finrank ℂ (LinearMap.ker M.vecMulLinear))
      (vermaWeightGramPolynomial_eval c (h t) n).symm
  exact he.trans_le hb

end VOA.InverseDS.VirasoroVerma
