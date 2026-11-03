/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.ClassicalFreeness

/-!
# Generator words in the Li associated graded

This file bridges the exact state identity
`(T^r a / r!)_{(-1)}b = a_{(-r-1)}b` to the external Li associated graded.  It is the
model-independent normal-form input needed by the finite-layer surjectivity criterion in
`Filtered.ClassicalFreeness`.
-/

namespace VOA

open scoped DirectSum

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

section HomogeneousOperations

/-- Translation of an inserted homogeneous representative is insertion of its translated
representative in bidegree `(p+1,N+1)`. -/
theorem liAssociatedGradedTranslation_liHomogeneousClass
    (W : VertexOperatorAlgebra V) (p N : ℕ) (a : liWeightPiece W p N) :
    liAssociatedGradedTranslation W (liHomogeneousClass W p N a) =
      liHomogeneousClass W (p + 1) (N + 1)
        ⟨W.L (-1) a.1, liWeightPiece_L_neg_one_mem W a.2⟩ := by
  rw [liHomogeneousClass, liHomogeneousClassLinear, LinearMap.comp_apply,
    DirectSum.lof_eq_of, liAssociatedGradedTranslation_of,
    liWeightLayerTranslation_mk]
  rfl

/-- Multiplication of inserted homogeneous representatives is insertion of their `(-1)`-product
in the summed bidegree. -/
theorem liHomogeneousClass_mul
    (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (a : liWeightPiece W p N) (b : liWeightPiece W q M) :
    liHomogeneousClass W p N a * liHomogeneousClass W q M b =
      liHomogeneousClass W (p + q) (N + M)
        ⟨W.smul a.1 (-1) b.1, liWeightPiece_smul_neg_one_mem W a.2 b.2⟩ := by
  simp only [liHomogeneousClass, liHomogeneousClassLinear, LinearMap.comp_apply,
    DirectSum.lof_eq_of]
  rw [liAssociatedGraded_of_mul_of, liWeightLayerMul_mk]

/-- Reindexing an inserted homogeneous representative along equal bidegrees does not change its
class. -/
theorem liHomogeneousClass_reindex (W : VertexOperatorAlgebra V)
    {p N p' N' : ℕ} {z : V} (hp : p = p') (hN : N = N')
    (hz : z ∈ liWeightPiece W p N) (hz' : z ∈ liWeightPiece W p' N') :
    liHomogeneousClass W p N ⟨z, hz⟩ =
      liHomogeneousClass W p' N' ⟨z, hz'⟩ := by
  subst p'
  subst N'
  rfl

/-- Iterated translation carries a homogeneous Li representative from bidegree `(p,N)` to
`(p+r,N+r)`. -/
theorem liWeightPiece_T_pow_mem (W : VertexOperatorAlgebra V)
    {p N : ℕ} {a : V} (ha : a ∈ liWeightPiece W p N) (r : ℕ) :
    (W.toPreVertexAlgebra.T ^ r) a ∈ liWeightPiece W (p + r) (N + r) := by
  induction r with
  | zero => simpa using ha
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := liWeightPiece_L_neg_one_mem W ih
      rw [← VertexOperatorAlgebra.T_eq_Lneg1] at h
      simpa only [Nat.add_assoc] using h

/-- The state-side divided translate has the expected homogeneous Li bidegree. -/
theorem dividedTranslateState_mem_liWeightPiece (W : VertexOperatorAlgebra V)
    {p N : ℕ} {a : V} (ha : a ∈ liWeightPiece W p N) (r : ℕ) :
    dividedTranslateState W r a ∈ liWeightPiece W (p + r) (N + r) := by
  rw [dividedTranslateState]
  exact (liWeightPiece W (p + r) (N + r)).smul_mem _
    (liWeightPiece_T_pow_mem W ha r)

/-- Iterating associated-graded translation on an inserted homogeneous class is represented by
the matching state-side iterate of `T`. -/
theorem liAssociatedGradedTranslation_pow_liHomogeneousClass
    (W : VertexOperatorAlgebra V) (p N : ℕ) (a : liWeightPiece W p N) :
    ∀ r : ℕ,
      (liAssociatedGradedTranslation W ^ r) (liHomogeneousClass W p N a) =
        liHomogeneousClass W (p + r) (N + r)
          ⟨(W.toPreVertexAlgebra.T ^ r) a.1, liWeightPiece_T_pow_mem W a.2 r⟩ := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        liAssociatedGradedTranslation_liHomogeneousClass]
      simp only [pow_succ', Module.End.mul_apply]
      congr 1
      apply Subtype.ext
      symm
      exact LinearMap.congr_fun (VertexOperatorAlgebra.T_eq_Lneg1 W)
        ((W.toPreVertexAlgebra.T ^ r) a.1)

/-- Divided iterates of associated-graded translation agree exactly with insertion of divided
state translates. -/
theorem dividedIterate_liHomogeneousClass
    (W : VertexOperatorAlgebra V) (p N r : ℕ) (a : liWeightPiece W p N) :
    FiniteJet.dividedIterate (liAssociatedGradedTranslation W) r
        (liHomogeneousClass W p N a) =
      liHomogeneousClass W (p + r) (N + r)
        ⟨dividedTranslateState W r a.1,
          dividedTranslateState_mem_liWeightPiece W a.2 r⟩ := by
  rw [FiniteJet.dividedIterate,
    liAssociatedGradedTranslation_pow_liHomogeneousClass]
  rw [← liHomogeneousClass_smul]
  rfl

/-- A degree-zero class is the generic homogeneous insertion from Li degree zero. -/
theorem liDegreeZeroClass_eq_liHomogeneousClass
    (W : VertexOperatorAlgebra V) (N : ℕ) (a : W.grading (N : ℤ)) :
    liDegreeZeroClass W N a =
      liHomogeneousClass W 0 N
        ⟨a.1, by
          rw [liWeightPiece, Submodule.mem_inf]
          exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top, a.2⟩⟩ := by
  rfl

/-- The jet-theoretic divided iterate of a degree-zero homogeneous class is represented by the
state-side divided translate in bidegree `(r,N+r)`. -/
theorem dividedIterate_liDegreeZeroClass
    (W : VertexOperatorAlgebra V) (N r : ℕ) (a : W.grading (N : ℤ)) :
    FiniteJet.dividedIterate (liAssociatedGradedTranslation W) r
        (liDegreeZeroClass W N a) =
      liHomogeneousClass W r (N + r)
        ⟨dividedTranslateState W r a.1, by
          have ha0 : a.1 ∈ liWeightPiece W 0 N := by
            rw [liWeightPiece, Submodule.mem_inf]
            exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top, a.2⟩
          simpa using dividedTranslateState_mem_liWeightPiece W ha0 r⟩ := by
  rw [liDegreeZeroClass_eq_liHomogeneousClass,
    dividedIterate_liHomogeneousClass]
  exact liHomogeneousClass_reindex W (Nat.zero_add r) rfl _ _

/-- The vacuum, inserted as a bidegree `(0,0)` representative, is the unit of the external Li
associated graded. -/
theorem liHomogeneousClass_vacuum (W : VertexOperatorAlgebra V) :
    liHomogeneousClass W 0 0
        ⟨W.vacuum, by
          rw [liWeightPiece, Submodule.mem_inf]
          exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top,
            W.vacuum_mem_grading_zero⟩⟩ = 1 := by
  rw [liAssociatedGraded_one]
  rfl

/-- The iterated `(-1)`-product of divided translates has exactly the Li degree and conformal
weight read off from its generator word. -/
theorem dividedTranslatedWord_mem_liWeightPiece (W : VertexOperatorAlgebra V)
    {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) :
    ∀ l : List (Fin g × ℕ),
      dividedTranslatedWord W gen l ∈
        liWeightPiece W (pairsLevel l) (wordDeg (genWord gen wt l)) := by
  intro l
  induction l with
  | nil =>
      rw [dividedTranslatedWord, pairsLevel_nil, genWord_nil, wordDeg_nil,
        liWeightPiece, Submodule.mem_inf]
      exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top,
        W.vacuum_mem_grading_zero⟩
  | cons q t ih =>
      have hq0 : gen q.1 ∈ liWeightPiece W 0 (wt q.1) := by
        rw [liWeightPiece, Submodule.mem_inf]
        exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top, hgen q.1⟩
      have hq := dividedTranslateState_mem_liWeightPiece W hq0 q.2
      simp only [Nat.zero_add] at hq
      simpa only [dividedTranslatedWord, pairsLevel_cons, genWord_cons, wordDeg_cons] using
        liWeightPiece_smul_neg_one_mem W hq ih

/-- **Exact associated-graded generator-word bridge.**  The product of the divided translation
iterates of the degree-zero generator classes is the homogeneous Li class of the corresponding
iterated state product.  Combining this with `dividedTranslatedWord_eq_wordAct` identifies it
with the usual negative-mode generator word. -/
theorem prod_dividedIterate_degreeZeroClass_eq_dividedTranslatedWord
    (W : VertexOperatorAlgebra V)
    {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) :
    ∀ l : List (Fin g × ℕ),
      (l.map fun q =>
        FiniteJet.dividedIterate (liAssociatedGradedTranslation W) q.2
          (liDegreeZeroClass W (wt q.1) ⟨gen q.1, hgen q.1⟩)).prod =
        liHomogeneousClass W (pairsLevel l) (wordDeg (genWord gen wt l))
          ⟨dividedTranslatedWord W gen l,
            dividedTranslatedWord_mem_liWeightPiece W gen wt hgen l⟩ := by
  intro l
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, pairsLevel_nil, genWord_nil, wordDeg_nil,
        dividedTranslatedWord]
      exact (liHomogeneousClass_vacuum W).symm
  | cons q t ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [dividedIterate_liDegreeZeroClass, ih, liHomogeneousClass_mul]
      rfl

/-- The usual negative-mode generator word has the same exact Li bidegree as its divided-
translation factorization. -/
theorem generatorWord_mem_liWeightPiece (W : VertexOperatorAlgebra V)
    {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (l : List (Fin g × ℕ)) :
    wordAct (adjointWeakModule W) (genWord gen wt l) W.vacuum ∈
      liWeightPiece W (pairsLevel l) (wordDeg (genWord gen wt l)) := by
  rw [← dividedTranslatedWord_eq_wordAct W gen wt l]
  exact dividedTranslatedWord_mem_liWeightPiece W gen wt hgen l

/-- Product form of the exact associated-graded generator-word bridge. -/
theorem prod_dividedIterate_degreeZeroClass_eq_generatorWord
    (W : VertexOperatorAlgebra V)
    {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (l : List (Fin g × ℕ)) :
    (l.map fun q =>
      FiniteJet.dividedIterate (liAssociatedGradedTranslation W) q.2
        (liDegreeZeroClass W (wt q.1) ⟨gen q.1, hgen q.1⟩)).prod =
      liHomogeneousClass W (pairsLevel l) (wordDeg (genWord gen wt l))
        ⟨wordAct (adjointWeakModule W) (genWord gen wt l) W.vacuum,
          generatorWord_mem_liWeightPiece W gen wt hgen l⟩ := by
  rw [prod_dividedIterate_degreeZeroClass_eq_dividedTranslatedWord]
  apply congrArg (liHomogeneousClass W (pairsLevel l) (wordDeg (genWord gen wt l)))
  apply Subtype.ext
  exact dividedTranslatedWord_eq_wordAct W gen wt l

end HomogeneousOperations

section JetGeneratorWords

variable {g : ℕ}

/-- The finite-jet monomial attached to a negative-mode generator word.  An order above the
truncation bound is represented by zero, following `FiniteJet.jetVariable`. -/
noncomputable def generatorJetWord (m : ℕ) : List (Fin g × ℕ) →
    FiniteJet.JetPoly ℂ (Fin g) m
  | [] => 1
  | q :: t => FiniteJet.jetVariable (R := ℂ) m q.1 q.2 * generatorJetWord m t

/-- Each individual mode depth in a word is bounded by its total Li level. -/
theorem snd_le_pairsLevel_of_mem {l : List (Fin g × ℕ)} {q : Fin g × ℕ}
    (hq : q ∈ l) : q.2 ≤ pairsLevel l := by
  induction l with
  | nil => simp at hq
  | cons a t ih =>
      rw [List.mem_cons] at hq
      rw [pairsLevel_cons]
      rcases hq with rfl | hq
      · exact Nat.le_add_right _ _
      · exact (ih hq).trans (Nat.le_add_left _ _)

/-- Evaluating the finite-jet monomial of a word produces the product of divided translation
iterates, provided the truncation retains every mode depth occurring in the word. -/
theorem liFiniteJetPolynomialMap_generatorJetWord
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (x : Fin g → liAssociatedGraded W) (l : List (Fin g × ℕ))
    (horders : ∀ q ∈ l, q.2 ≤ m) :
    liFiniteJetPolynomialMap W m x (generatorJetWord m l) =
      (l.map fun q =>
        FiniteJet.dividedIterate (liAssociatedGradedTranslation W) q.2 (x q.1)).prod := by
  change FiniteJet.derivationJetEval (liAssociatedGradedTranslation W) m x
      (generatorJetWord m l) = _
  induction l with
  | nil => simp [generatorJetWord]
  | cons q t ih =>
      have hq : q.2 ≤ m := horders q (List.mem_cons_self)
      have ht : ∀ a ∈ t, a.2 ≤ m := fun a ha => horders a (List.mem_cons_of_mem q ha)
      simp only [generatorJetWord, List.map_cons, List.prod_cons, map_mul]
      rw [FiniteJet.derivationJetEval_jetVariable
        (liAssociatedGradedTranslation W) m x q.1 q.2 hq]
      rw [ih ht]

/-- Every retained generator word has an explicit preimage under the presented finite-jet map:
the class of its jet monomial. -/
theorem liPresentedJetMap_hits_generatorWord
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    {gen : Fin g → V} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (l : List (Fin g × ℕ)) (hlevel : pairsLevel l ≤ m) :
    ∃ y : FiniteJet.PresentedJet (R := ℂ) m I,
      liPresentedJetMap W m
          (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI y =
        liHomogeneousClass W (pairsLevel l) (wordDeg (genWord gen wt l))
          ⟨wordAct (adjointWeakModule W) (genWord gen wt l) W.vacuum,
            generatorWord_mem_liWeightPiece W gen wt hgen l⟩ := by
  refine ⟨FiniteJet.presentedJetMk (R := ℂ) m I (generatorJetWord m l), ?_⟩
  rw [liPresentedJetMap_mk]
  rw [liFiniteJetPolynomialMap_generatorJetWord]
  · exact prod_dividedIterate_degreeZeroClass_eq_generatorWord W gen wt hgen l
  · intro q hq
    exact (snd_le_pairsLevel_of_mem hq).trans hlevel

-- The final ordered-span application expands nested finite sums; keep the larger budget local.
set_option maxHeartbeats 800000 in
/-- **Finite-layer homogeneous generation from degree-zero classes.**  If homogeneous states
span `V` modulo the vacuum and `C₂(V)`, then every exact Li layer of degree `p ≤ m` is hit by
the order-`m` presented jet map on their degree-zero classes.  No basis of `C₂(V)`, presentation
of its relations, or classical-freeness hypothesis is used.

⚠ **Scope of `hdec`.**  Since `gen` is a finite family, `hdec` forces `C2Cofinite W`
(certificate `L11cert_hdec_C2Cofinite`, `Notes/Textbook/certificates/L11_Checks.lean`), so this
theorem applies only to `C₂`-cofinite VOAs; it is narrower than Li's theorem, and for instance it
has no instance at `L_{-4/3}(sl₂)` (`QuasiLisseSl2.not_C2Cofinite_simpleSl2QL`). -/
theorem liPresentedJetMap_hits_homogeneous_class_of_generators
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (p N : ℕ) (hp : p ≤ m) :
    ∀ z : liWeightLayer W p N,
      ∃ y : FiniteJet.PresentedJet (R := ℂ) m I,
        liPresentedJetMap W m
            (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z := by
  apply liPresentedJetMap_hits_homogeneous_class_of_ordered_words
    W m (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI
      gen wt hgen hdec p N
  intro l _ hlevel hdegree
  obtain ⟨y, hy⟩ := liPresentedJetMap_hits_generatorWord W m I hgen hI l
    (hlevel.le.trans hp)
  refine ⟨y, hy.trans ?_⟩
  exact liHomogeneousClass_reindex W hlevel hdegree _ _

end JetGeneratorWords

end VOA
