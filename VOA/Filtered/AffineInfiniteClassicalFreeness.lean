/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli.
-/
import VOA.Filtered.AffineCurrentLi
import VOA.Filtered.InfiniteClassicalFreeness
import VOA.Filtered.InfiniteLiJetBidegree

set_option maxHeartbeats 800000

/-!
# Infinite jets and current words for the universal affine `sl₂` VOA

The universal affine VOA is not `C₂`-cofinite, so the finite-generation criterion based on a
global `span generators ⊔ O₂ = ⊤` must not be applied to it.  This file records the safe
replacement: the already proved equality between Li filtration and current-word filtration is
projected to each conformal weight.  Words above the requested Li level vanish in the exact
quotient, and words of the wrong conformal weight vanish under projection.  Thus exact-level
current words span every homogeneous Li layer.  Each is hit by the finite presented jet algebra
of matching order, which proves unconditional surjectivity of the infinite presentation-level
map.  No finite-dimensional `C₂` quotient, PBW independence, or quotient strictness assumption
occurs here.  The same argument is then carried out intrinsically for every graded affine
quotient, using the proved equality between its Li filtration and the image current-word
filtration; the maximal graded quotient is recorded as a named specialization.
-/

namespace VOA

namespace AffineVOA
namespace CurrentLi

open VOA.AffineVOA.Inst
open scoped DirectSum

noncomputable section

variable (k : ℂ) (hk : k + 2 ≠ 0)

local notation "W" => affineSl2VOA_closed k hk

/-! ### The projected-span linear algebra

The affine weight projection and the exact-layer quotient are model-specific, but the final
passage from projected current-word generators to a whole layer is just span induction.  We state
that step separately so an affine projection calculation can be supplied without invoking the
global `span generators ⊔ O₂ = ⊤` criterion.
-/

theorem linearMap_mem_span_of_mem_span
    {E A : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup A] [Module ℂ A]
    (s : Set E) (t : Set A)
    (q : Submodule.span ℂ s →ₗ[ℂ] A)
    (hgen : ∀ (a : E) (ha : a ∈ s),
      q ⟨a, Submodule.subset_span ha⟩ ∈ Submodule.span ℂ t)
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

/-- The degree-zero Li classes of the three affine currents. -/
noncomputable def affineCurrentLiClass (a : Fin 3) : liAssociatedGraded W :=
  liDegreeZeroClass W 1
    ⟨currentState k a, currentState_mem_grading k hk a⟩

/-- Exact homogeneous classes represented by current creation words.  The set lives in the full
associated graded algebra, so no choice of a quotient representative is exposed. -/
noncomputable def affineCurrentWordClassSet (p N : ℕ) :
    Set (liAssociatedGraded W) :=
  {x | ∃ l : List (Fin 3 × ℕ),
      pairsLevel l = p ∧ wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) = N ∧
      x = liHomogeneousClass W (pairsLevel l)
        (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l))
        ⟨wordStateA k l, by
          rw [wordStateA_eq_generatorWord k hk l]
          exact generatorWord_mem_liWeightPiece W (currentState k)
            (fun _ : Fin 3 => 1) (fun a => currentState_mem_grading k hk a) l⟩}

theorem affineCurrentWordClassSet_mem (p N : ℕ)
    {l : List (Fin 3 × ℕ)} (hl : pairsLevel l = p)
    (hN : wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) = N) :
    liHomogeneousClass W (pairsLevel l)
      (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l))
        ⟨wordStateA k l, by
          rw [wordStateA_eq_generatorWord k hk l]
          exact generatorWord_mem_liWeightPiece W (currentState k)
            (fun _ : Fin 3 => 1) (fun a => currentState_mem_grading k hk a) l⟩ ∈
      affineCurrentWordClassSet k hk p N := by
  exact ⟨l, hl, hN, rfl⟩

theorem affineCurrentWordClassSet_generator_hit
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => affineCurrentLiClass k hk a)).toRingHom)
    (p : ℕ) {l : List (Fin 3 × ℕ)}
    (hl : pairsLevel l = p) :
    ∃ y : FiniteJet.PresentedJet (R := ℂ) p I,
      liPresentedJetMap W p (fun a => affineCurrentLiClass k hk a) I hI y =
        liHomogeneousClass W (pairsLevel l)
          (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l))
          ⟨wordStateA k l, by
            rw [wordStateA_eq_generatorWord k hk l]
            exact generatorWord_mem_liWeightPiece W (currentState k)
              (fun _ : Fin 3 => 1) (fun a => currentState_mem_grading k hk a) l⟩ := by
  obtain ⟨y, hy⟩ := liPresentedJetMap_hits_generatorWord W p I
    (fun a => currentState_mem_grading k hk a) hI l hl.le
  refine ⟨y, ?_⟩
  calc
    liPresentedJetMap W p (fun a => affineCurrentLiClass k hk a) I hI y =
        liHomogeneousClass W (pairsLevel l)
          (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l))
          ⟨wordAct (adjointWeakModule W)
            (genWord (currentState k) (fun _ : Fin 3 => 1) l)
            (affineSl2VOA_closed k hk).vacuum, _⟩ := hy
    _ = liHomogeneousClass W (pairsLevel l)
          (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l))
          ⟨wordStateA k l, _⟩ := by
      congr 1
      apply Subtype.ext
      exact (wordStateA_eq_generatorWord k hk l).symm

/-- Exact affine Li layers are spanned by current-word classes of the exact Li level and
conformal weight.  The proof projects the strict current-word spanning theorem to weight `N`.
A word of level greater than `p` dies in the exact layer, while a word of the wrong weight dies
under the homogeneous projection.  No independence of current words is used. -/
theorem affineCurrentWordClassSet_spans_layer (p N : ℕ) (z : liWeightLayer W p N) :
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
      Submodule.span ℂ (affineCurrentWordClassSet k hk p N) := by
  refine Submodule.Quotient.induction_on _ z fun zrep => ?_
  let P : Module.End ℂ (WakModule k) := wProj (adjointModule W) (N : ℂ)
  have hvacWeight : (affineSl2VOA_closed k hk).vacuum ∈
      (adjointModule W).weight 0 := by
    change (affineSl2VOA_closed k hk).vacuum ∈ adjWeight W 0
    have hzero : (0 : ℂ) = ((0 : ℤ) : ℂ) := by norm_num
    rw [hzero, adjWeight_cast W 0]
    exact (affineSl2VOA_closed k hk).vacuum_mem_grading_zero
  have hbottom : ∀ w ∈ ({(affineSl2VOA_closed k hk).vacuum} : Set (WakModule k)),
      ∃ d₀ : ℕ, w ∈ (adjointModule W).weight ((0 : ℂ) + d₀) := by
    intro w hw
    have hw' : w = (affineSl2VOA_closed k hk).vacuum := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨0, by simpa using hvacWeight⟩
  have hprojGrade (a : WakModule k) : P a ∈
      (affineSl2VOA_closed k hk).grading (N : ℤ) := by
    have ha := wProj_apply_mem (adjointModule W) (N : ℂ) a
    change P a ∈ adjWeight W (N : ℂ) at ha
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast W N] at ha
    exact ha
  let G : Set (WakModule k) :=
    {u | ∃ l : List (Fin 3 × ℕ), p ≤ pairsLevel l ∧ wordStateA k l = u}
  have hprojFiltration (a : WakModule k) (ha : a ∈ Submodule.span ℂ G) :
      P a ∈ liFiltration W p := by
    have haLi : a ∈ liFiltration W p := by
      rw [liFiltration_eq_currentWordPiece k hk p, currentWordPiece]
      exact ha
    exact wProj_mem_Gfil (adjointModule W)
      ({(affineSl2VOA_closed k hk).vacuum} : Set (WakModule k)) 0 hbottom
      (N : ℂ) haLi
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
  have hgen : ∀ (u : WakModule k) (hu : u ∈ G),
      Q ⟨u, Submodule.subset_span hu⟩ ∈
        Submodule.span ℂ (affineCurrentWordClassSet k hk p N) := by
    rintro u ⟨l, hp, rfl⟩
    have huPiece := generatorWord_mem_liWeightPiece W (currentState k)
      (fun _ : Fin 3 => 1) (fun a => currentState_mem_grading k hk a) l
    have huGrade : wordStateA k l ∈
        (affineSl2VOA_closed k hk).grading
          (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) : ℤ) := by
      rw [wordStateA_eq_generatorWord k hk l]
      exact huPiece.2
    by_cases hlevel : pairsLevel l = p
    · by_cases hdegree :
          wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) = N
      · have hproj : P (wordStateA k l) = wordStateA k l := by
          apply wProj_of_mem (adjointModule W)
          change wordStateA k l ∈ adjWeight W (N : ℂ)
          have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
          rw [hcast, adjWeight_cast W N]
          simpa [hdegree] using huGrade
        apply Submodule.subset_span
        refine ⟨l, hlevel, hdegree, ?_⟩
        change liHomogeneousClass W p N (toPiece ⟨wordStateA k l, _⟩) = _
        have huPieceWord : wordStateA k l ∈
            liWeightPiece W (pairsLevel l)
              (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l)) := by
          rw [wordStateA_eq_generatorWord k hk l]
          exact huPiece
        have huPieceExact : wordStateA k l ∈ liWeightPiece W p N := by
          simpa [hlevel, hdegree] using huPieceWord
        calc
          liHomogeneousClass W p N (toPiece ⟨wordStateA k l, _⟩) =
              liHomogeneousClass W p N ⟨wordStateA k l, huPieceExact⟩ := by
                apply congrArg (liHomogeneousClass W p N)
                exact Subtype.ext hproj
          _ = _ := liHomogeneousClass_reindex W hlevel.symm hdegree.symm _ _
      · have hproj : P (wordStateA k l) = 0 := by
          apply wProj_of_mem_ne (adjointModule W)
          · change wordStateA k l ∈ adjWeight W
              (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) : ℂ)
            have hcast :
                (wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) : ℂ) =
                  ((wordDeg (genWord (currentState k) (fun _ : Fin 3 => 1) l) : ℤ) : ℂ) := by
              norm_num
            rw [hcast, adjWeight_cast W]
            exact huGrade
          · intro heq
            have hnat : N = wordDeg
                (genWord (currentState k) (fun _ : Fin 3 => 1) l) := by
              exact_mod_cast heq
            exact hdegree hnat.symm
        change liHomogeneousClass W p N (toPiece ⟨wordStateA k l, _⟩) ∈
          Submodule.span ℂ (affineCurrentWordClassSet k hk p N)
        have htoPiece : toPiece ⟨wordStateA k l,
            Submodule.subset_span ⟨l, hp, rfl⟩⟩ = 0 := by
          apply Subtype.ext
          exact hproj
        rw [htoPiece, liHomogeneousClass_zero]
        exact (Submodule.span ℂ (affineCurrentWordClassSet k hk p N)).zero_mem
    · have hstrict : p < pairsLevel l := lt_of_le_of_ne hp (Ne.symm hlevel)
      have huNext : wordStateA k l ∈ liFiltration W (p + 1) := by
        rw [liFiltration_eq_currentWordPiece k hk (p + 1)]
        exact wordStateA_mem_currentWordPiece k (p + 1) l hstrict
      have hprojNext : P (wordStateA k l) ∈ liFiltration W (p + 1) := by
        exact wProj_mem_Gfil (adjointModule W)
          ({(affineSl2VOA_closed k hk).vacuum} : Set (WakModule k)) 0 hbottom
          (N : ℂ) huNext
      have hq :
          ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ
              (toPiece ⟨wordStateA k l, Submodule.subset_span ⟨l, hp, rfl⟩⟩) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨hprojNext, hprojGrade _⟩
      change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) _ ∈
        Submodule.span ℂ (affineCurrentWordClassSet k hk p N)
      rw [hq, map_zero]
      exact (Submodule.span ℂ (affineCurrentWordClassSet k hk p N)).zero_mem
  have hzSpan : (zrep : WakModule k) ∈ Submodule.span ℂ G := by
    rw [← currentWordPiece, ← liFiltration_eq_currentWordPiece k hk p]
    exact zrep.property.1
  have hQ := linearMap_mem_span_of_mem_span G
    (affineCurrentWordClassSet k hk p N) Q hgen (zrep : WakModule k) hzSpan
  have hzWeight : (zrep : WakModule k) ∈ (adjointModule W).weight (N : ℂ) := by
    change (zrep : WakModule k) ∈ adjWeight W (N : ℂ)
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast W N]
    exact zrep.property.2
  have hproj : P (zrep : WakModule k) = zrep :=
    wProj_of_mem (adjointModule W) hzWeight
  convert hQ using 1
  change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) _ = _
  apply congrArg (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
  apply congrArg (fun a : liWeightPiece W p N =>
    ((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ a)
  exact Subtype.ext hproj.symm

/-- If every homogeneous current-word class spans its Li layer, then the finite order-`p`
presented jet map hits the whole `(p,N)` layer.  This is the affine replacement for the generic
`span generators ⊔ O₂ = ⊤` criterion. -/
theorem affine_liPresentedJetMap_hits_homogeneous_class_of_currentWords
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => affineCurrentLiClass k hk a)).toRingHom)
    (hspan : ∀ p N (z : liWeightLayer W p N),
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
        Submodule.span ℂ (affineCurrentWordClassSet k hk p N)) :
    ∀ p N (z : liWeightLayer W p N),
      ∃ y : FiniteJet.PresentedJet (R := ℂ) p I,
        liPresentedJetMap W p (fun a => affineCurrentLiClass k hk a) I hI y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z := by
  intro p N z
  let f : FiniteJet.PresentedJet (R := ℂ) p I →ₗ[ℂ] liAssociatedGraded W :=
    (liPresentedJetMap W p (fun a => affineCurrentLiClass k hk a) I hI).toLinearMap
  have hgen : ∀ x ∈ affineCurrentWordClassSet k hk p N,
      x ∈ LinearMap.range f := by
    intro x hx
    obtain ⟨l, hl, hN, rfl⟩ := hx
    obtain ⟨y, hy⟩ := affineCurrentWordClassSet_generator_hit k hk I hI p hl
    exact ⟨y, hy⟩
  have hzspan : DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
      Submodule.span ℂ (affineCurrentWordClassSet k hk p N) := hspan p N z
  have hzrange : DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z ∈
      LinearMap.range f := by
    refine Submodule.span_induction (p := fun x _ => x ∈ LinearMap.range f) hgen ?_ ?_ ?_ hzspan
    · exact (LinearMap.range f).zero_mem
    · intro x y _ _ hx hy
      exact (LinearMap.range f).add_mem hx hy
    · intro c x _ hx
      exact (LinearMap.range f).smul_mem c hx
  obtain ⟨y, hy⟩ := hzrange
  exact ⟨y, hy⟩

/-- Every exact affine Li class has a preimage already in the finite presented jet algebra whose
order is its Li degree.  The relation ideal remains arbitrary, subject only to vanishing under
the chosen degree-zero current classes. -/
theorem affine_liPresentedJetMap_hits_homogeneous_class
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => affineCurrentLiClass k hk a)).toRingHom) :
    ∀ p N (z : liWeightLayer W p N),
      ∃ y : FiniteJet.PresentedJet (R := ℂ) p I,
        liPresentedJetMap W p (fun a => affineCurrentLiClass k hk a) I hI y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z := by
  exact affine_liPresentedJetMap_hits_homogeneous_class_of_currentWords k hk I hI
    (affineCurrentWordClassSet_spans_layer k hk)

/-- The current-word homogeneous spanning condition therefore implies surjectivity of the
infinite presentation-level jet map.  The order of a preimage may depend on the homogeneous
layer, as it should for the non-C₂-cofinite universal affine VOA. -/
theorem affine_liInfinitePresentedJetMap_surjective_of_homogeneous_preimages
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => affineCurrentLiClass k hk a)).toRingHom)
    (hhom : ∀ p N (z : liWeightLayer W p N),
      ∃ (m : ℕ) (y : FiniteJet.PresentedJet (R := ℂ) m I),
        liInfinitePresentedJetMap W (fun a => affineCurrentLiClass k hk a) I hI
            (InfiniteJet.presentedJetOfFinite (R := ℂ) m I y) =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z) :
    Function.Surjective
      (liInfinitePresentedJetMap W (fun a => affineCurrentLiClass k hk a) I hI) := by
  exact liInfinitePresentedJetMap_surjective_of_finite_homogeneous_preimages
    W (fun a => affineCurrentLiClass k hk a) I hI hhom

/-- **Unconditional affine presentation-level surjectivity.**  For the universal noncritical
affine `sl₂` VOA, the infinite presented jet map is surjective for every relation ideal that
vanishes on the three degree-zero current classes.  This is a generation statement only: it does
not identify the relation ideal with the `C₂` kernel and does not assert injectivity. -/
theorem affine_liInfinitePresentedJetMap_surjective
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun a => affineCurrentLiClass k hk a)).toRingHom) :
    Function.Surjective
      (liInfinitePresentedJetMap W (fun a => affineCurrentLiClass k hk a) I hI) := by
  apply affine_liInfinitePresentedJetMap_surjective_of_homogeneous_preimages k hk I hI
  intro p N z
  obtain ⟨y, hy⟩ := affine_liPresentedJetMap_hits_homogeneous_class k hk I hI p N z
  refine ⟨p, y, ?_⟩
  rw [liInfinitePresentedJetMap_ofFinite]
  exact hy

/-! ### Graded affine quotients -/

section Quotient

variable (J : Submodule ℂ (WakModule k))
variable (hJ : (affineSl2VOA_closed k hk).IsIdeal J)
variable (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) J)

local notation "QW" =>
  QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr

/-- The degree-zero Li classes of the three current images in a graded affine quotient. -/
noncomputable def quotientAffineCurrentLiClass (a : Fin 3) : liAssociatedGraded QW :=
  liDegreeZeroClass QW 1
    ⟨J.mkQ (currentState k a),
      QuotVOA.quotientVOA_mkQ_grading hJ hgr (currentState_mem_grading k hk a)⟩

/-- Exact homogeneous quotient classes represented by images of universal current words. -/
noncomputable def quotientAffineCurrentWordClassSet (p N : ℕ) :
    Set (liAssociatedGraded QW) :=
  {x | ∃ l : List (Fin 3 × ℕ),
      pairsLevel l = p ∧ wordDeg
        (genWord (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1) l) = N ∧
      x = liHomogeneousClass QW (pairsLevel l)
        (wordDeg (genWord (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1) l))
        ⟨J.mkQ (wordStateA k l), by
          rw [mkQ_wordStateA_eq_generatorWord k hk J hJ hgr l]
          exact generatorWord_mem_liWeightPiece QW
            (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1)
            (fun a => QuotVOA.quotientVOA_mkQ_grading hJ hgr
              (currentState_mem_grading k hk a)) l⟩}

/-- Every exact quotient current word is hit at finite jet order equal to its Li level. -/
theorem quotientAffineCurrentWordClassSet_generator_hit
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)).toRingHom)
    (p : ℕ) {l : List (Fin 3 × ℕ)} (hl : pairsLevel l = p) :
    ∃ y : FiniteJet.PresentedJet (R := ℂ) p B,
      liPresentedJetMap QW p
          (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB y =
        liHomogeneousClass QW (pairsLevel l)
          (wordDeg (genWord (fun a => J.mkQ (currentState k a))
            (fun _ : Fin 3 => 1) l))
          ⟨J.mkQ (wordStateA k l), by
            rw [mkQ_wordStateA_eq_generatorWord k hk J hJ hgr l]
            exact generatorWord_mem_liWeightPiece QW
              (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1)
              (fun a => QuotVOA.quotientVOA_mkQ_grading hJ hgr
                (currentState_mem_grading k hk a)) l⟩ := by
  obtain ⟨y, hy⟩ := liPresentedJetMap_hits_generatorWord QW p B
    (fun a => QuotVOA.quotientVOA_mkQ_grading hJ hgr
      (currentState_mem_grading k hk a)) hB l hl.le
  refine ⟨y, ?_⟩
  calc
    liPresentedJetMap QW p
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB y =
      liHomogeneousClass QW (pairsLevel l)
        (wordDeg (genWord (fun a => J.mkQ (currentState k a))
          (fun _ : Fin 3 => 1) l))
        ⟨wordAct (adjointWeakModule QW)
          (genWord (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1) l)
          (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr).vacuum, _⟩ := hy
    _ = liHomogeneousClass QW (pairsLevel l)
        (wordDeg (genWord (fun a => J.mkQ (currentState k a))
          (fun _ : Fin 3 => 1) l))
        ⟨J.mkQ (wordStateA k l), _⟩ := by
      congr 1
      apply Subtype.ext
      exact (mkQ_wordStateA_eq_generatorWord k hk J hJ hgr l).symm

/-- The span of quotient current words of level at least `p` is exactly the induced quotient
current-word piece. -/
theorem quotientCurrentWordPiece_eq_span_words (p : ℕ) :
    quotientCurrentWordPiece k J p =
      Submodule.span ℂ
        {u | ∃ l : List (Fin 3 × ℕ),
          p ≤ pairsLevel l ∧ J.mkQ (wordStateA k l) = u} := by
  apply le_antisymm
  · rintro y hy
    rw [quotientCurrentWordPiece] at hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    clear hy
    rw [currentWordPiece] at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨l, hl, rfl⟩ := hz
        exact Submodule.subset_span ⟨l, hl, rfl⟩
    | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
    | add x y _ _ ihx ihy =>
        rw [map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x _ ihx =>
        rw [map_smul]
        exact Submodule.smul_mem _ c ihx
  · rw [Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact Submodule.mem_map_of_mem (wordStateA_mem_currentWordPiece k p l hl)

/-- Every exact Li layer of a graded affine quotient is spanned by exact-level, exact-weight
images of universal current words. -/
theorem quotientAffineCurrentWordClassSet_spans_layer
    (p N : ℕ) (z : liWeightLayer QW p N) :
    DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) z ∈
      Submodule.span ℂ (quotientAffineCurrentWordClassSet k hk J hJ hgr p N) := by
  refine Submodule.Quotient.induction_on _ z fun zrep => ?_
  let P : Module.End ℂ (WakModule k ⧸ J) := wProj (adjointModule QW) (N : ℂ)
  have hvacWeight :
      (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr).vacuum ∈
        (adjointModule QW).weight 0 := by
    change (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr).vacuum ∈
      adjWeight QW 0
    have hzero : (0 : ℂ) = ((0 : ℤ) : ℂ) := by norm_num
    rw [hzero, adjWeight_cast QW 0]
    exact (QuotVOA.quotientVOA
      (affineSl2VOA_closed k hk) J hJ hgr).vacuum_mem_grading_zero
  have hbottom : ∀ w ∈
      ({(QuotVOA.quotientVOA
        (affineSl2VOA_closed k hk) J hJ hgr).vacuum} : Set (WakModule k ⧸ J)),
      ∃ d₀ : ℕ, w ∈ (adjointModule QW).weight ((0 : ℂ) + d₀) := by
    intro w hw
    have hw' : w =
        (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) J hJ hgr).vacuum :=
      Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨0, by simpa using hvacWeight⟩
  have hprojGrade (a : WakModule k ⧸ J) : P a ∈
      (QuotVOA.quotientVOA
        (affineSl2VOA_closed k hk) J hJ hgr).grading (N : ℤ) := by
    have ha := wProj_apply_mem (adjointModule QW) (N : ℂ) a
    change P a ∈ adjWeight QW (N : ℂ) at ha
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast QW N] at ha
    exact ha
  let G : Set (WakModule k ⧸ J) :=
    {u | ∃ l : List (Fin 3 × ℕ),
      p ≤ pairsLevel l ∧ J.mkQ (wordStateA k l) = u}
  have hprojFiltration (a : WakModule k ⧸ J) (ha : a ∈ Submodule.span ℂ G) :
      P a ∈ liFiltration QW p := by
    have haLi : a ∈ liFiltration QW p := by
      rw [quotientLiFiltration_eq_currentWordPiece k hk J hJ hgr p,
        quotientCurrentWordPiece_eq_span_words k J p]
      exact ha
    exact wProj_mem_Gfil (adjointModule QW)
      ({(QuotVOA.quotientVOA
        (affineSl2VOA_closed k hk) J hJ hgr).vacuum} : Set (WakModule k ⧸ J))
      0 hbottom (N : ℂ) haLi
  let toPiece : Submodule.span ℂ G →ₗ[ℂ] liWeightPiece QW p N :=
    { toFun := fun a => ⟨P a.1, hprojFiltration a.1 a.2, hprojGrade a.1⟩
      map_add' := fun a b => by
        apply Subtype.ext
        exact map_add P a.1 b.1
      map_smul' := fun c a => by
        apply Subtype.ext
        exact map_smul P c a.1 }
  let Q : Submodule.span ℂ G →ₗ[ℂ] liAssociatedGraded QW :=
    (liHomogeneousClassLinear QW p N).comp toPiece
  have hgen : ∀ (u : WakModule k ⧸ J) (hu : u ∈ G),
      Q ⟨u, Submodule.subset_span hu⟩ ∈
        Submodule.span ℂ
          (quotientAffineCurrentWordClassSet k hk J hJ hgr p N) := by
    rintro u ⟨l, hp, rfl⟩
    have huPiece := generatorWord_mem_liWeightPiece QW
      (fun a => J.mkQ (currentState k a)) (fun _ : Fin 3 => 1)
      (fun a => QuotVOA.quotientVOA_mkQ_grading hJ hgr
        (currentState_mem_grading k hk a)) l
    have huGrade : J.mkQ (wordStateA k l) ∈
        (QuotVOA.quotientVOA
          (affineSl2VOA_closed k hk) J hJ hgr).grading
            (wordDeg (genWord (fun a => J.mkQ (currentState k a))
              (fun _ : Fin 3 => 1) l) : ℤ) := by
      rw [mkQ_wordStateA_eq_generatorWord k hk J hJ hgr l]
      exact huPiece.2
    by_cases hlevel : pairsLevel l = p
    · by_cases hdegree : wordDeg
          (genWord (fun a => J.mkQ (currentState k a))
            (fun _ : Fin 3 => 1) l) = N
      · have hproj : P (J.mkQ (wordStateA k l)) = J.mkQ (wordStateA k l) := by
          apply wProj_of_mem (adjointModule QW)
          change J.mkQ (wordStateA k l) ∈ adjWeight QW (N : ℂ)
          have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
          rw [hcast, adjWeight_cast QW N]
          rw [hdegree] at huGrade
          exact huGrade
        apply Submodule.subset_span
        refine ⟨l, hlevel, hdegree, ?_⟩
        change liHomogeneousClass QW p N
          (toPiece ⟨J.mkQ (wordStateA k l), _⟩) = _
        have huPieceWord : J.mkQ (wordStateA k l) ∈
            liWeightPiece QW (pairsLevel l)
              (wordDeg (genWord (fun a => J.mkQ (currentState k a))
                (fun _ : Fin 3 => 1) l)) := by
          rw [mkQ_wordStateA_eq_generatorWord k hk J hJ hgr l]
          exact huPiece
        have huPieceExact : J.mkQ (wordStateA k l) ∈ liWeightPiece QW p N := by
          rw [hlevel, hdegree] at huPieceWord
          exact huPieceWord
        calc
          liHomogeneousClass QW p N
              (toPiece ⟨J.mkQ (wordStateA k l), _⟩) =
            liHomogeneousClass QW p N
              ⟨J.mkQ (wordStateA k l), huPieceExact⟩ := by
                apply congrArg (liHomogeneousClass QW p N)
                exact Subtype.ext hproj
          _ = _ := liHomogeneousClass_reindex QW hlevel.symm hdegree.symm _ _
      · have hproj : P (J.mkQ (wordStateA k l)) = 0 := by
          apply wProj_of_mem_ne (adjointModule QW)
          · change J.mkQ (wordStateA k l) ∈ adjWeight QW
              (wordDeg (genWord (fun a => J.mkQ (currentState k a))
                (fun _ : Fin 3 => 1) l) : ℂ)
            have hcast :
                (wordDeg (genWord (fun a => J.mkQ (currentState k a))
                  (fun _ : Fin 3 => 1) l) : ℂ) =
                ((wordDeg (genWord (fun a => J.mkQ (currentState k a))
                  (fun _ : Fin 3 => 1) l) : ℤ) : ℂ) := by
              norm_num
            rw [hcast, adjWeight_cast QW]
            exact huGrade
          · intro heq
            have hnat : N = wordDeg
                (genWord (fun a => J.mkQ (currentState k a))
                  (fun _ : Fin 3 => 1) l) := by
              exact_mod_cast heq
            exact hdegree hnat.symm
        change liHomogeneousClass QW p N
            (toPiece ⟨J.mkQ (wordStateA k l), _⟩) ∈
          Submodule.span ℂ
            (quotientAffineCurrentWordClassSet k hk J hJ hgr p N)
        have htoPiece : toPiece
            ⟨J.mkQ (wordStateA k l), Submodule.subset_span ⟨l, hp, rfl⟩⟩ = 0 := by
          apply Subtype.ext
          exact hproj
        rw [htoPiece, liHomogeneousClass_zero]
        exact (Submodule.span ℂ
          (quotientAffineCurrentWordClassSet k hk J hJ hgr p N)).zero_mem
    · have hstrict : p < pairsLevel l := lt_of_le_of_ne hp (Ne.symm hlevel)
      have huNext : J.mkQ (wordStateA k l) ∈ liFiltration QW (p + 1) := by
        rw [quotientLiFiltration_eq_currentWordPiece k hk J hJ hgr (p + 1)]
        exact Submodule.mem_map_of_mem
          (wordStateA_mem_currentWordPiece k (p + 1) l hstrict)
      have hprojNext : P (J.mkQ (wordStateA k l)) ∈
          liFiltration QW (p + 1) := by
        exact wProj_mem_Gfil (adjointModule QW)
          ({(QuotVOA.quotientVOA
            (affineSl2VOA_closed k hk) J hJ hgr).vacuum} : Set (WakModule k ⧸ J))
          0 hbottom (N : ℂ) huNext
      have hq :
          ((liWeightPiece QW (p + 1) N).comap
            (liWeightPiece QW p N).subtype).mkQ
              (toPiece ⟨J.mkQ (wordStateA k l),
                Submodule.subset_span ⟨l, hp, rfl⟩⟩) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨hprojNext, hprojGrade _⟩
      change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) _ ∈
        Submodule.span ℂ
          (quotientAffineCurrentWordClassSet k hk J hJ hgr p N)
      rw [hq, map_zero]
      exact (Submodule.span ℂ
        (quotientAffineCurrentWordClassSet k hk J hJ hgr p N)).zero_mem
  have hzSpan : (zrep : WakModule k ⧸ J) ∈ Submodule.span ℂ G := by
    rw [← quotientCurrentWordPiece_eq_span_words k J p,
      ← quotientLiFiltration_eq_currentWordPiece k hk J hJ hgr p]
    exact zrep.property.1
  have hQ := linearMap_mem_span_of_mem_span G
    (quotientAffineCurrentWordClassSet k hk J hJ hgr p N) Q hgen
    (zrep : WakModule k ⧸ J) hzSpan
  have hzWeight : (zrep : WakModule k ⧸ J) ∈
      (adjointModule QW).weight (N : ℂ) := by
    change (zrep : WakModule k ⧸ J) ∈ adjWeight QW (N : ℂ)
    have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
    rw [hcast, adjWeight_cast QW N]
    exact zrep.property.2
  have hproj : P (zrep : WakModule k ⧸ J) = zrep :=
    wProj_of_mem (adjointModule QW) hzWeight
  convert hQ using 1
  change DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) _ = _
  apply congrArg
    (DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N))
  apply congrArg (fun a : liWeightPiece QW p N =>
    ((liWeightPiece QW (p + 1) N).comap (liWeightPiece QW p N).subtype).mkQ a)
  exact Subtype.ext hproj.symm

/-- Every exact Li class of a graded affine quotient is hit at finite jet order equal to its Li
degree.  The presentation ideal is arbitrary, subject only to vanishing on the quotient current
classes. -/
theorem quotientAffine_liPresentedJetMap_hits_homogeneous_class
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)).toRingHom) :
    ∀ p N (z : liWeightLayer QW p N),
      ∃ y : FiniteJet.PresentedJet (R := ℂ) p B,
        liPresentedJetMap QW p
            (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) z := by
  intro p N z
  let f : FiniteJet.PresentedJet (R := ℂ) p B →ₗ[ℂ] liAssociatedGraded QW :=
    (liPresentedJetMap QW p
      (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB).toLinearMap
  have hgen : ∀ x ∈ quotientAffineCurrentWordClassSet k hk J hJ hgr p N,
      x ∈ LinearMap.range f := by
    intro x hx
    obtain ⟨l, hl, hN, rfl⟩ := hx
    obtain ⟨y, hy⟩ := quotientAffineCurrentWordClassSet_generator_hit
      k hk J hJ hgr B hB p hl
    exact ⟨y, hy⟩
  have hzspan :
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) z ∈
        Submodule.span ℂ
          (quotientAffineCurrentWordClassSet k hk J hJ hgr p N) :=
    quotientAffineCurrentWordClassSet_spans_layer k hk J hJ hgr p N z
  have hzrange :
      DirectSum.of (fun d : ℕ × ℕ => liWeightLayer QW d.1 d.2) (p, N) z ∈
        LinearMap.range f := by
    refine Submodule.span_induction
      (p := fun x _ => x ∈ LinearMap.range f) hgen ?_ ?_ ?_ hzspan
    · exact (LinearMap.range f).zero_mem
    · intro x y _ _ hx hy
      exact (LinearMap.range f).add_mem hx hy
    · intro c x _ hx
      exact (LinearMap.range f).smul_mem c hx
  obtain ⟨y, hy⟩ := hzrange
  exact ⟨y, hy⟩

/-- The affine current-word theorem gives surjectivity on every exact Li/conformal bidegree at
the stable order equal to the Li degree.  This is deliberately derived from homogeneous
current-word preimages, not from the global finite-`C₂` generator condition: that condition
fails for the non-`C₂`-cofinite boundary affine quotients considered here. -/
theorem quotientAffine_liPresentedJetBidegreeMap_surjective
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)).toRingHom)
    (p N : ℕ) :
    Function.Surjective
      (liPresentedJetBidegreeMap QW p
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)
        B hB (fun _ : Fin 3 => 1) p N) := by
  let gen : Fin 3 → WakModule k ⧸ J := fun a => J.mkQ (currentState k a)
  have hgen : ∀ a, gen a ∈
      (QuotVOA.quotientVOA
        (affineSl2VOA_closed k hk) J hJ hgr).grading ((1 : ℕ) : ℤ) := fun a =>
    QuotVOA.quotientVOA_mkQ_grading hJ hgr (currentState_mem_grading k hk a)
  apply liPresentedJetBidegreeMap_surjective_of_homogeneous_hits
    QW p gen (fun _ : Fin 3 => 1) hgen B
      (by simpa only [gen, quotientAffineCurrentLiClass] using hB) p N
  intro z
  simpa only [gen, quotientAffineCurrentLiClass] using
    (quotientAffine_liPresentedJetMap_hits_homogeneous_class
      k hk J hJ hgr B hB p N z)

/-- **Presentation-level surjectivity for every graded affine quotient.**  The infinite jet map
generated by the three quotient currents is surjective for any base relation ideal known to
vanish on them.  This theorem makes no claim that the chosen ideal is the full `C₂` kernel and
no injectivity claim. -/
theorem quotientAffine_liInfinitePresentedJetMap_surjective
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)).toRingHom) :
    Function.Surjective
      (liInfinitePresentedJetMap QW
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB) := by
  apply liInfinitePresentedJetMap_surjective_of_finite_homogeneous_preimages QW
    (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB
  intro p N z
  obtain ⟨y, hy⟩ := quotientAffine_liPresentedJetMap_hits_homogeneous_class
    k hk J hJ hgr B hB p N z
  refine ⟨p, y, ?_⟩
  rw [liInfinitePresentedJetMap_ofFinite]
  exact hy

/-- For a graded affine quotient, the stable exact-bidegree Hilbert inequality is the only
remaining input to presentation-level classical freeness.  Homogeneous finite-order
surjectivity and infinite surjectivity are supplied unconditionally by current-word spanning;
no finite-`C₂` generation statement is assumed. -/
theorem quotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a)).toRingHom)
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage
          (fun _ : Fin 3 => 1) p p N B) ≤
      Module.finrank ℂ (liWeightLayer QW p N)) :
    LiPresentationClassicallyFree QW
      (fun a => quotientAffineCurrentLiClass k hk J hJ hgr a) B hB := by
  let gen : Fin 3 → WakModule k ⧸ J := fun a => J.mkQ (currentState k a)
  have hgen : ∀ a, gen a ∈
      (QuotVOA.quotientVOA
        (affineSl2VOA_closed k hk) J hJ hgr).grading ((1 : ℕ) : ℤ) := fun a =>
    QuotVOA.quotientVOA_mkQ_grading hJ hgr (currentState_mem_grading k hk a)
  simpa only [gen, quotientAffineCurrentLiClass] using
    (liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze_of_surjective
      QW gen (fun _ : Fin 3 => 1) hgen B
      (by simpa only [gen, quotientAffineCurrentLiClass] using hB)
      (fun _ => by simp)
      (fun p N => by
        simpa only [gen, quotientAffineCurrentLiClass] using
          (quotientAffine_liPresentedJetBidegreeMap_surjective
            k hk J hJ hgr B hB p N))
      (by simpa only [gen, quotientAffineCurrentLiClass] using
        (quotientAffine_liInfinitePresentedJetMap_surjective
          k hk J hJ hgr B hB))
      hle)

end Quotient

/-! ### The maximal graded quotient -/

local notation "MW" =>
  QuotVOA.maxQuotientVOA (affineSl2VOA_closed k hk)

/-- Current Li classes in the maximal graded affine quotient.  At boundary admissible levels this
is the presentation used for the simple affine VOA. -/
noncomputable def maxQuotientAffineCurrentLiClass (a : Fin 3) :
    liAssociatedGraded MW :=
  quotientAffineCurrentLiClass k hk
    (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (affineSl2VOA_closed k hk)) a

/-- Surjectivity of the presentation-level infinite jet map for the maximal graded affine
quotient, hence in particular for the boundary simple quotient once that identification is
chosen.  The relation ideal is still only assumed to vanish on the three current classes. -/
theorem maxQuotientAffine_liInfinitePresentedJetMap_surjective
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => maxQuotientAffineCurrentLiClass k hk a)).toRingHom) :
    Function.Surjective
      (liInfinitePresentedJetMap MW
        (fun a => maxQuotientAffineCurrentLiClass k hk a) B hB) := by
  unfold maxQuotientAffineCurrentLiClass
  exact quotientAffine_liInfinitePresentedJetMap_surjective k hk
    (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (affineSl2VOA_closed k hk)) B hB

/-- Maximal-quotient affine classical freeness from the exact stable bidegree Hilbert bound.
This is the capstone used by the boundary `sl₂` specializations. -/
theorem maxQuotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
    (B : Ideal (MvPolynomial (Fin 3) ℂ))
    (hB : B ≤ RingHom.ker
      (MvPolynomial.aeval
        (fun a => maxQuotientAffineCurrentLiClass k hk a)).toRingHom)
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage
          (fun _ : Fin 3 => 1) p p N B) ≤
      Module.finrank ℂ (liWeightLayer MW p N)) :
    LiPresentationClassicallyFree MW
      (fun a => maxQuotientAffineCurrentLiClass k hk a) B hB := by
  unfold maxQuotientAffineCurrentLiClass
  exact quotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
    k hk
    (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isIdeal (affineSl2VOA_closed k hk))
    (QuotVOA.maxGradedIdeal_isGradedIdeal (affineSl2VOA_closed k hk)) B hB hle

end
end CurrentLi
end AffineVOA
end VOA

section AxiomAudit
#print axioms VOA.AffineVOA.CurrentLi.quotientAffine_liPresentedJetBidegreeMap_surjective
#print axioms VOA.AffineVOA.CurrentLi.quotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
#print axioms VOA.AffineVOA.CurrentLi.maxQuotientAffine_liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
end AxiomAudit
