/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.InfiniteClassicalFreeness
import VOA.Filtered.InfiniteLiJetBidegree
import VOA.Filtered.LiGeneratorWords

/-!
# Surjectivity of the canonical jet map from generator-word spanning of Li's filtration

Let `W` be a VOA and `gen : Fin g → V` homogeneous generators of weights `wt`.  Write
`C_p = span { a^{i_1}_{(-n_1-1)} ... a^{i_s}_{(-n_s-1)} vacuum : n_1 + ... + n_s >= p }`.
The inclusion `C_p ≤ F^p` is automatic (`genWord_mem_Gfil`).  This file proves, for an arbitrary
VOA, that the reverse inclusion

  `GeneratorWordsSpanLiFiltration W gen wt : ∀ p, F^p W ≤ C_p`

implies that every exact Li layer `gr^{p}_N` is spanned by the classes of exact-level,
exact-weight generator words; consequently the canonical presented-jet map is surjective, at
finite order `p` on every `(p,N)` layer and on the infinite jet algebra.

This replaces the global criterion `span (gen ∪ {vacuum}) ⊔ O₂ = ⊤`, which holds only when the
`C₂` algebra is linearly spanned by the generators (e.g. it fails for `M(2,2n+1)`, `n >= 3`,
and for every non-lisse affine VOA).  The proof is the generic form of the affine argument in
`AffineInfiniteClassicalFreeness`.
-/

namespace VOA

open scoped DirectSum

universe u

noncomputable section

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (W : VertexOperatorAlgebra V) {g : ℕ} (gen : Fin g → V) (wt : Fin g → ℕ)

/-- The state of a generator word. -/
abbrev genWordState (l : List (Fin g × ℕ)) : V :=
  wordAct (adjointWeakModule W) (genWord gen wt l) W.vacuum

/-- Span of generator words of level at least `p`. -/
def genWordPiece (p : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ l : List (Fin g × ℕ), p ≤ pairsLevel l ∧ genWordState W gen wt l = u}

/-- Generator words span Li's filtration with the correct level. -/
def GeneratorWordsSpanLiFiltration : Prop :=
  ∀ p : ℕ, liFiltration W p ≤ genWordPiece W gen wt p

theorem genWordPiece_le_liFiltration (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (p : ℕ) :
    genWordPiece W gen wt p ≤ liFiltration W p := by
  rw [genWordPiece, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact genWord_mem_Gfil (adjointWeakModule W) ({W.vacuum} : Set V) hgen l
    (Set.mem_singleton _) (by exact_mod_cast hl)

theorem liFiltration_eq_genWordPiece (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hspan : GeneratorWordsSpanLiFiltration W gen wt) (p : ℕ) :
    liFiltration W p = genWordPiece W gen wt p :=
  le_antisymm (hspan p) (genWordPiece_le_liFiltration W gen wt hgen p)

theorem linearMap_mem_span_of_mem_span'
    {E A : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    (s : Set E) (t : Set A) (q : Submodule.span ℂ s →ₗ[ℂ] A)
    (hgen : ∀ (a : E) (ha : a ∈ s), q ⟨a, Submodule.subset_span ha⟩ ∈ Submodule.span ℂ t)
    (a : E) (ha : a ∈ Submodule.span ℂ s) :
    q ⟨a, ha⟩ ∈ Submodule.span ℂ t := by
  refine Submodule.span_induction
    (p := fun a ha => q ⟨a, ha⟩ ∈ Submodule.span ℂ t) hgen ?_ ?_ ?_ ha
  · change q (0 : Submodule.span ℂ s) ∈ Submodule.span ℂ t
    rw [map_zero]
    exact (Submodule.span ℂ t).zero_mem
  · intro x y _ _ hx hy
    change q ((⟨x, ‹x ∈ Submodule.span ℂ s›⟩ : Submodule.span ℂ s) +
      ⟨y, ‹y ∈ Submodule.span ℂ s›⟩) ∈ Submodule.span ℂ t
    rw [map_add]
    exact (Submodule.span ℂ t).add_mem hx hy
  · intro c x _ hx
    change q (c • (⟨x, ‹x ∈ Submodule.span ℂ s›⟩ : Submodule.span ℂ s)) ∈
      Submodule.span ℂ t
    rw [map_smul]
    exact (Submodule.span ℂ t).smul_mem c hx

variable (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))

/-- Exact homogeneous classes represented by generator words. -/
def genWordClassSet (p N : ℕ) : Set (liAssociatedGraded W) :=
  {x | ∃ l : List (Fin g × ℕ),
      pairsLevel l = p ∧ wordDeg (genWord gen wt l) = N ∧
      x = liHomogeneousClass W (pairsLevel l) (wordDeg (genWord gen wt l))
        ⟨genWordState W gen wt l, generatorWord_mem_liWeightPiece W gen wt hgen l⟩}

/-- Exact Li layers are spanned by exact-level, exact-weight generator-word classes. -/
theorem genWordClassSet_spans_layer (hspan : GeneratorWordsSpanLiFiltration W gen wt)
    (p N : ℕ) (z : liWeightLayer W p N) :
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
      Submodule.span ℂ (genWordClassSet W gen wt hgen p N) := by
  refine Submodule.Quotient.induction_on _ z fun zrep => ?_
  let P : Module.End ℂ V := wProj (adjointModule W) (N : ℂ)
  have hvacWeight : W.vacuum ∈ (adjointModule W).weight 0 := by
    change W.vacuum ∈ adjWeight W 0
    have hzero : (0 : ℂ) = ((0 : ℤ) : ℂ) := by norm_num
    rw [hzero, adjWeight_cast W 0]
    exact W.vacuum_mem_grading_zero
  have hbottom : ∀ w ∈ ({W.vacuum} : Set V),
      ∃ d₀ : ℕ, w ∈ (adjointModule W).weight ((0 : ℂ) + d₀) := by
    intro w hw
    have hw' : w = W.vacuum := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨0, by simpa using hvacWeight⟩
  have hprojGrade (a : V) : P a ∈ W.grading (N : ℤ) := by
    have ha := wProj_apply_mem (adjointModule W) (N : ℂ) a
    change P a ∈ adjWeight W (N : ℂ) at ha
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast W N] at ha
    exact ha
  let G : Set V := {u | ∃ l : List (Fin g × ℕ), p ≤ pairsLevel l ∧ genWordState W gen wt l = u}
  have hprojFiltration (a : V) (ha : a ∈ Submodule.span ℂ G) :
      P a ∈ liFiltration W p := by
    have haLi : a ∈ liFiltration W p :=
      genWordPiece_le_liFiltration W gen wt hgen p ha
    exact wProj_mem_Gfil (adjointModule W) ({W.vacuum} : Set V) 0 hbottom (N : ℂ) haLi
  let toPiece : Submodule.span ℂ G →ₗ[ℂ] liWeightPiece W p N :=
    { toFun := fun a => ⟨P a.1, hprojFiltration a.1 a.2, hprojGrade a.1⟩
      map_add' := fun a b => by
        apply Subtype.ext
        exact map_add P a.1 b.1
      map_smul' := fun c a => by
        apply Subtype.ext
        exact map_smul P c a.1 }
  let Q : Submodule.span ℂ G →ₗ[ℂ] liAssociatedGraded W :=
    (liHomogeneousClassLinear W p N).comp toPiece
  have hgenQ : ∀ (u : V) (hu : u ∈ G),
      Q ⟨u, Submodule.subset_span hu⟩ ∈ Submodule.span ℂ (genWordClassSet W gen wt hgen p N) := by
    rintro u ⟨l, hp, rfl⟩
    have huPiece := generatorWord_mem_liWeightPiece W gen wt hgen l
    have huGrade : genWordState W gen wt l ∈ W.grading (wordDeg (genWord gen wt l) : ℤ) :=
      huPiece.2
    by_cases hlevel : pairsLevel l = p
    · by_cases hdegree : wordDeg (genWord gen wt l) = N
      · have hproj : P (genWordState W gen wt l) = genWordState W gen wt l := by
          apply wProj_of_mem (adjointModule W)
          change genWordState W gen wt l ∈ adjWeight W (N : ℂ)
          have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
          rw [hcast, adjWeight_cast W N]
          simpa [hdegree] using huGrade
        apply Submodule.subset_span
        refine ⟨l, hlevel, hdegree, ?_⟩
        change liHomogeneousClass W p N (toPiece ⟨genWordState W gen wt l, _⟩) = _
        have huPieceExact : genWordState W gen wt l ∈ liWeightPiece W p N := by
          simpa [hlevel, hdegree] using huPiece
        calc
          liHomogeneousClass W p N (toPiece ⟨genWordState W gen wt l, _⟩) =
              liHomogeneousClass W p N ⟨genWordState W gen wt l, huPieceExact⟩ := by
                apply congrArg (liHomogeneousClass W p N)
                exact Subtype.ext hproj
          _ = _ := liHomogeneousClass_reindex W hlevel.symm hdegree.symm _ _
      · have hproj : P (genWordState W gen wt l) = 0 := by
          apply wProj_of_mem_ne (adjointModule W)
          · change genWordState W gen wt l ∈ adjWeight W (wordDeg (genWord gen wt l) : ℂ)
            have hcast : (wordDeg (genWord gen wt l) : ℂ) =
                ((wordDeg (genWord gen wt l) : ℤ) : ℂ) := by norm_num
            rw [hcast, adjWeight_cast W]
            exact huGrade
          · intro heq
            have hnat : N = wordDeg (genWord gen wt l) := by exact_mod_cast heq
            exact hdegree hnat.symm
        change liHomogeneousClass W p N (toPiece ⟨genWordState W gen wt l, _⟩) ∈
          Submodule.span ℂ (genWordClassSet W gen wt hgen p N)
        have htoPiece : toPiece ⟨genWordState W gen wt l,
            Submodule.subset_span ⟨l, hp, rfl⟩⟩ = 0 := by
          apply Subtype.ext
          exact hproj
        rw [htoPiece, liHomogeneousClass_zero]
        exact (Submodule.span ℂ (genWordClassSet W gen wt hgen p N)).zero_mem
    · have hstrict : p < pairsLevel l := lt_of_le_of_ne hp (Ne.symm hlevel)
      have huNext : genWordState W gen wt l ∈ liFiltration W (p + 1) :=
        genWordPiece_le_liFiltration W gen wt hgen (p + 1)
          (Submodule.subset_span ⟨l, hstrict, rfl⟩)
      have hprojNext : P (genWordState W gen wt l) ∈ liFiltration W (p + 1) :=
        wProj_mem_Gfil (adjointModule W) ({W.vacuum} : Set V) 0 hbottom (N : ℂ) huNext
      have hq :
          ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ
              (toPiece ⟨genWordState W gen wt l, Submodule.subset_span ⟨l, hp, rfl⟩⟩) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨hprojNext, hprojGrade _⟩
      change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) _ ∈
        Submodule.span ℂ (genWordClassSet W gen wt hgen p N)
      rw [hq, map_zero]
      exact (Submodule.span ℂ (genWordClassSet W gen wt hgen p N)).zero_mem
  have hzSpan : (zrep : V) ∈ Submodule.span ℂ G := hspan p zrep.property.1
  have hQ := linearMap_mem_span_of_mem_span' G (genWordClassSet W gen wt hgen p N) Q hgenQ
    (zrep : V) hzSpan
  have hzWeight : (zrep : V) ∈ (adjointModule W).weight (N : ℂ) := by
    change (zrep : V) ∈ adjWeight W (N : ℂ)
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast W N]
    exact zrep.property.2
  have hproj : P (zrep : V) = zrep := wProj_of_mem (adjointModule W) hzWeight
  convert hQ using 1
  change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) _ = _
  apply congrArg (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
  apply congrArg (fun a : liWeightPiece W p N =>
    ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ a)
  exact Subtype.ext hproj.symm

/-- **Finite-order homogeneous surjectivity from generator-word spanning.**  Every exact Li class
of bidegree `(p,N)` is hit by the order-`p` presented jet map, for any relation ideal vanishing
on the degree-zero generator classes. -/
theorem liPresentedJetMap_hits_homogeneous_class_of_genWordSpan
    (hspan : GeneratorWordsSpanLiFiltration W gen wt)
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom) :
    ∀ p N (z : liWeightLayer W p N),
      ∃ y : FiniteJet.PresentedJet (R := ℂ) p I,
        liPresentedJetMap W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z := by
  intro p N z
  let f : FiniteJet.PresentedJet (R := ℂ) p I →ₗ[ℂ] liAssociatedGraded W :=
    (liPresentedJetMap W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI).toLinearMap
  have hgenf : ∀ x ∈ genWordClassSet W gen wt hgen p N, x ∈ LinearMap.range f := by
    rintro x ⟨l, hl, -, rfl⟩
    obtain ⟨y, hy⟩ := liPresentedJetMap_hits_generatorWord W p I hgen hI l hl.le
    exact ⟨y, hy⟩
  have hzspan := genWordClassSet_spans_layer W gen wt hgen hspan p N z
  have hzrange : DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
      LinearMap.range f := by
    refine Submodule.span_induction (p := fun x _ => x ∈ LinearMap.range f) hgenf ?_ ?_ ?_ hzspan
    · exact (LinearMap.range f).zero_mem
    · intro x y _ _ hx hy
      exact (LinearMap.range f).add_mem hx hy
    · intro c x _ hx
      exact (LinearMap.range f).smul_mem c hx
  obtain ⟨y, hy⟩ := hzrange
  exact ⟨y, hy⟩

/-- Bidegree surjectivity at stable order `p`, from generator-word spanning. -/
theorem liPresentedJetBidegreeMap_surjective_of_genWordSpan
    (hspan : GeneratorWordsSpanLiFiltration W gen wt)
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (p N : ℕ) :
    Function.Surjective
      (liPresentedJetBidegreeMap W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N) :=
  liPresentedJetBidegreeMap_surjective_of_homogeneous_hits W p gen wt hgen I hI p N
    (liPresentedJetMap_hits_homogeneous_class_of_genWordSpan W gen wt hgen hspan I hI p N)

/-- **Surjectivity of the canonical infinite jet map from generator-word spanning.** -/
theorem liInfinitePresentedJetMap_surjective_of_genWordSpan
    (hspan : GeneratorWordsSpanLiFiltration W gen wt)
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom) :
    Function.Surjective
      (liInfinitePresentedJetMap W (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI) := by
  apply liInfinitePresentedJetMap_surjective_of_finite_homogeneous_preimages
  intro p N z
  obtain ⟨y, hy⟩ := liPresentedJetMap_hits_homogeneous_class_of_genWordSpan
    W gen wt hgen hspan I hI p N z
  exact ⟨p, y, by rw [liInfinitePresentedJetMap_ofFinite]; exact hy⟩

end

end VOA
