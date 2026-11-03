/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.LiGeneratorWords

/-!
# Bidegree preservation for the finite jet-to-Li map

The canonical finite jet map sends the variable attached to a weight-`N` generator and jet
order `r` to exact Li/conformal bidegree `(r,N+r)`.  This file promotes that generator statement
to arbitrary weighted-homogeneous polynomials and proves that taking a weighted-homogeneous
component preserves the evaluation kernel.
-/

namespace VOA

open scoped DirectSum

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- An element of the external Li associated graded is supported in one exact bidegree. -/
def IsLiBihomogeneous (W : VertexOperatorAlgebra V) (d : ℕ × ℕ)
    (a : liAssociatedGraded W) : Prop :=
  ∃ z : liWeightLayer W d.1 d.2,
    a = DirectSum.of (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d z

theorem isLiBihomogeneous_zero (W : VertexOperatorAlgebra V) (d : ℕ × ℕ) :
    IsLiBihomogeneous W d 0 := by
  refine ⟨0, ?_⟩
  rw [map_zero]

theorem IsLiBihomogeneous.add (W : VertexOperatorAlgebra V) {d : ℕ × ℕ}
    {a b : liAssociatedGraded W}
    (ha : IsLiBihomogeneous W d a) (hb : IsLiBihomogeneous W d b) :
    IsLiBihomogeneous W d (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨x + y, ?_⟩
  rw [map_add]

theorem IsLiBihomogeneous.smul (W : VertexOperatorAlgebra V) {d : ℕ × ℕ}
    {a : liAssociatedGraded W} (ha : IsLiBihomogeneous W d a) (c : ℂ) :
    IsLiBihomogeneous W d (c • a) := by
  obtain ⟨x, rfl⟩ := ha
  refine ⟨c • x, ?_⟩
  rw [DirectSum.of_smul]

theorem IsLiBihomogeneous.reindex (W : VertexOperatorAlgebra V)
    {d e : ℕ × ℕ} {a : liAssociatedGraded W}
    (ha : IsLiBihomogeneous W d a) (hde : d = e) :
    IsLiBihomogeneous W e a := by
  subst e
  exact ha

theorem IsLiBihomogeneous.mul (W : VertexOperatorAlgebra V)
    {d e : ℕ × ℕ} {a b : liAssociatedGraded W}
    (ha : IsLiBihomogeneous W d a) (hb : IsLiBihomogeneous W e b) :
    IsLiBihomogeneous W (d + e) (a * b) := by
  rcases d with ⟨p, N⟩
  rcases e with ⟨q, M⟩
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  refine ⟨liWeightLayerMul W p q N M x y, ?_⟩
  exact liAssociatedGraded_of_mul_of W p q N M x y

theorem IsLiBihomogeneous.pow (W : VertexOperatorAlgebra V)
    {d : ℕ × ℕ} {a : liAssociatedGraded W}
    (ha : IsLiBihomogeneous W d a) (n : ℕ) :
    IsLiBihomogeneous W (n • d) (a ^ n) := by
  induction n with
  | zero =>
      simpa only [zero_nsmul, pow_zero] using
        ⟨liWeightLayerVacuum W, (liAssociatedGraded_one W).symm⟩
  | succ n ih =>
      rw [pow_succ, succ_nsmul]
      exact ih.mul W ha

theorem isLiBihomogeneous_algebraMap (W : VertexOperatorAlgebra V) (c : ℂ) :
    IsLiBihomogeneous W (0, 0)
      ((@algebraMap ℂ
        (⨁ d : ℕ × ℕ, liWeightLayer W d.1 d.2) _
        (DirectSum.semiring (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2))
        (DirectSum.instAlgebra ℂ
          (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2))) c) := by
  exact ⟨c • liWeightLayerVacuum W, liAssociatedGraded_algebraMap W c⟩

section FiniteJetBidegree

variable {g : ℕ}

/-- Every jet variable on a homogeneous degree-zero generator evaluates in its prescribed exact
Li/conformal bidegree. -/
theorem liFiniteJetPolynomialMap_X_isLiBihomogeneous
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (v : FiniteJet.JetVar (Fin g) m) :
    IsLiBihomogeneous W (FiniteJet.jetLiBidegree wt m v)
      (liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        (MvPolynomial.X v)) := by
  refine ⟨((liWeightPiece W (v.order + 1) (wt v.generator + v.order)).comap
      (liWeightPiece W v.order (wt v.generator + v.order)).subtype).mkQ
        ⟨dividedTranslateState W v.order (gen v.generator),
          by
            have h := dividedTranslateState_mem_liWeightPiece W
              (p := 0) (N := wt v.generator)
              (a := gen v.generator)
              (by
                rw [liWeightPiece, Submodule.mem_inf]
                exact ⟨by rw [liFiltration_zero_eq_top]; exact Submodule.mem_top,
                  hgen v.generator⟩) v.order
            simpa using h⟩, ?_⟩
  change FiniteJet.derivationJetEval (liAssociatedGradedTranslation W) m
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) (MvPolynomial.X v) = _
  simp only [FiniteJet.derivationJetEval, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_X]
  rw [dividedIterate_liDegreeZeroClass]
  rfl

/-- Evaluation of a monomial has the bidegree obtained by weighting its exponent vector. -/
theorem liFiniteJetPolynomialMap_monomial_isLiBihomogeneous
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) :
    ∀ (d : FiniteJet.JetVar (Fin g) m →₀ ℕ) (c : ℂ),
      IsLiBihomogeneous W
        (Finsupp.weight (FiniteJet.jetLiBidegree wt m) d)
        (liFiniteJetPolynomialMap W m
          (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
          (MvPolynomial.monomial d c)) := by
  intro d
  induction d using Finsupp.induction with
  | zero =>
      intro c
      simpa using isLiBihomogeneous_algebraMap W c
  | single_add v n d hv hn ih =>
      intro c
      rw [add_comm (Finsupp.single v n) d, map_add,
        Finsupp.weight_single, MvPolynomial.monomial_add_single, map_mul, map_pow]
      exact (ih c).mul W
        ((liFiniteJetPolynomialMap_X_isLiBihomogeneous W m gen wt hgen v).pow W n)

/-- Weighted-homogeneous jet polynomials evaluate in the matching exact Li/conformal
bidegree. -/
theorem liFiniteJetPolynomialMap_isLiBihomogeneous
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    {f : FiniteJet.JetPoly ℂ (Fin g) m} {d : ℕ × ℕ}
    (hf : f.IsWeightedHomogeneous (FiniteJet.jetLiBidegree wt m) d) :
    IsLiBihomogeneous W d
      (liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) f) := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact isLiBihomogeneous_zero W d
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using ihp.add W ihq
  | monomial e c he =>
      exact (liFiniteJetPolynomialMap_monomial_isLiBihomogeneous
        W m gen wt hgen e c).reindex W he

/-- A homogeneous element is zero if its component in its own bidegree is zero. -/
theorem IsLiBihomogeneous.eq_zero_of_component_eq_zero
    (W : VertexOperatorAlgebra V) {d : ℕ × ℕ} {a : liAssociatedGraded W}
    (ha : IsLiBihomogeneous W d a)
    (hcomponent : DirectSum.component ℂ (ℕ × ℕ)
      (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d a = 0) :
    a = 0 := by
  obtain ⟨z, rfl⟩ := ha
  change (DirectSum.component ℂ (ℕ × ℕ)
    (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d)
      ((DirectSum.lof ℂ (ℕ × ℕ)
        (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d) z) = 0 at hcomponent
  rw [DirectSum.component.lof_self] at hcomponent
  change (DirectSum.lof ℂ (ℕ × ℕ)
    (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d) z = 0
  rw [hcomponent, map_zero]

/-- Projecting the evaluation of a polynomial to bidegree `d` depends only on the weighted-
homogeneous component of degree `d`. -/
theorem liFiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (f : FiniteJet.JetPoly ℂ (Fin g) m) (d : ℕ × ℕ) :
    DirectSum.component ℂ (ℕ × ℕ)
        (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d
        (liFiniteJetPolynomialMap W m
          (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) f) =
      DirectSum.component ℂ (ℕ × ℕ)
        (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d
        (liFiniteJetPolynomialMap W m
          (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
          (MvPolynomial.weightedHomogeneousComponent
            (FiniteJet.jetLiBidegree wt m) d f)) := by
  classical
  let E := liFiniteJetPolynomialMap W m
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
  let P : FiniteJet.JetPoly ℂ (Fin g) m →ₗ[ℂ] liWeightLayer W d.1 d.2 :=
    (DirectSum.component ℂ (ℕ × ℕ)
      (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d).comp E.toLinearMap
  change P f = P (MvPolynomial.weightedHomogeneousComponent
    (FiniteJet.jetLiBidegree wt m) d f)
  calc
    P f = P (∑ᶠ e : ℕ × ℕ,
        MvPolynomial.weightedHomogeneousComponent
          (FiniteJet.jetLiBidegree wt m) e f) := by
      rw [MvPolynomial.sum_weightedHomogeneousComponent]
    _ = ∑ᶠ e : ℕ × ℕ, P
        (MvPolynomial.weightedHomogeneousComponent
          (FiniteJet.jetLiBidegree wt m) e f) := by
      exact P.toAddMonoidHom.map_finsum
        (MvPolynomial.weightedHomogeneousComponent_finsupp f)
    _ = P (MvPolynomial.weightedHomogeneousComponent
        (FiniteJet.jetLiBidegree wt m) d f) := by
      apply finsum_eq_single
      intro e hed
      have he := liFiniteJetPolynomialMap_isLiBihomogeneous
        W m gen wt hgen
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
          (w := FiniteJet.jetLiBidegree wt m) (n := e) (φ := f))
      obtain ⟨z, hz⟩ := he
      change DirectSum.component ℂ (ℕ × ℕ)
        (fun q : ℕ × ℕ => liWeightLayer W q.1 q.2) d (E _) = 0
      rw [hz]
      change (DirectSum.component ℂ (ℕ × ℕ)
        (fun q : ℕ × ℕ => liWeightLayer W q.1 q.2) d)
          ((DirectSum.lof ℂ (ℕ × ℕ)
            (fun q : ℕ × ℕ => liWeightLayer W q.1 q.2) e) z) = 0
      rw [DirectSum.component.of]
      simp [hed]

/-- Consequently, taking a weighted-homogeneous component preserves the kernel of the
canonical finite jet-to-Li evaluation on homogeneous degree-zero generators. -/
theorem liFiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (f : FiniteJet.JetPoly ℂ (Fin g) m)
    (hzero : liFiniteJetPolynomialMap W m
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) f = 0)
    (d : ℕ × ℕ) :
    liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        (MvPolynomial.weightedHomogeneousComponent
          (FiniteJet.jetLiBidegree wt m) d f) = 0 := by
  let q := MvPolynomial.weightedHomogeneousComponent
    (FiniteJet.jetLiBidegree wt m) d f
  have hqhom : IsLiBihomogeneous W d
      (liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) q) :=
    liFiniteJetPolynomialMap_isLiBihomogeneous W m gen wt hgen
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := FiniteJet.jetLiBidegree wt m) (n := d) (φ := f))
  apply hqhom.eq_zero_of_component_eq_zero W
  rw [← liFiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    W m gen wt hgen f d, hzero, map_zero]

/-- Degree-zero generation modulo `C₂`, together with the ordered-word theorem, makes the
restricted jet-to-Li map surjective in every Li degree `p ≤ m`.  Starting from an arbitrary
finite-jet preimage, weighted-homogeneous projection produces a preimage in the exact presented
bidegree image.

⚠ **Scope of `hdec`.**  Since `gen` is a finite family, `hdec` forces `C2Cofinite W`
(certificate `L11cert_hdec_C2Cofinite`, `Notes/Textbook/certificates/L11_Checks.lean`), so this
theorem applies only to `C₂`-cofinite VOAs; it is narrower than Li's theorem, and for instance it
has no instance at `L_{-4/3}(sl₂)` (`QuasiLisseSl2.not_C2Cofinite_simpleSl2QL`). -/
theorem liPresentedJetBidegreeMap_surjective_of_generators
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (p N : ℕ) (hp : p ≤ m) :
    Function.Surjective
      (liPresentedJetBidegreeMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N) := by
  intro z
  obtain ⟨y, hy⟩ := liPresentedJetMap_hits_homogeneous_class_of_generators
    W m I gen wt hgen hI hdec p N hp z
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective y
  change FiniteJet.presentedJetMk (R := ℂ) m I f = y at hf
  let q := MvPolynomial.weightedHomogeneousComponent
    (FiniteJet.jetLiBidegree wt m) (p, N) f
  let z' : FiniteJet.PresentedJetLiBidegreeImage wt m p N I :=
    ⟨FiniteJet.presentedJetMk (R := ℂ) m I q,
      ⟨⟨q, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := FiniteJet.jetLiBidegree wt m) (n := (p, N)) (φ := f)⟩, rfl⟩⟩
  refine ⟨z', ?_⟩
  change DirectSum.component ℂ (ℕ × ℕ)
      (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N)
      (liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) q) = z
  rw [← liFiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    W m gen wt hgen f (p, N)]
  rw [← liPresentedJetMap_mk W m
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI]
  rw [hf, hy]
  change (DirectSum.component ℂ (ℕ × ℕ)
    (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
      ((DirectSum.lof ℂ (ℕ × ℕ)
        (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N)) z) = z
  rw [DirectSum.component.lof_self]

/-- Any model-specific theorem producing a finite presented-jet preimage of every homogeneous
Li class already implies surjectivity of the exact-bidegree restriction.  This is the appropriate
adapter for affine current-word spanning, where the global finite-`C₂` generator hypothesis need
not hold. -/
theorem liPresentedJetBidegreeMap_surjective_of_homogeneous_hits
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (p N : ℕ)
    (hhit : ∀ z : liWeightLayer W p N,
      ∃ y : FiniteJet.PresentedJet (R := ℂ) m I,
        liPresentedJetMap W m
            (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
            I hI y =
          DirectSum.of (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N) z) :
    Function.Surjective
      (liPresentedJetBidegreeMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N) := by
  intro z
  obtain ⟨y, hy⟩ := hhit z
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective y
  change FiniteJet.presentedJetMk (R := ℂ) m I f = y at hf
  let q := MvPolynomial.weightedHomogeneousComponent
    (FiniteJet.jetLiBidegree wt m) (p, N) f
  let z' : FiniteJet.PresentedJetLiBidegreeImage wt m p N I :=
    ⟨FiniteJet.presentedJetMk (R := ℂ) m I q,
      ⟨⟨q, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := FiniteJet.jetLiBidegree wt m) (n := (p, N)) (φ := f)⟩, rfl⟩⟩
  refine ⟨z', ?_⟩
  change DirectSum.component ℂ (ℕ × ℕ)
      (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N)
      (liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) q) = z
  rw [← liFiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    W m gen wt hgen f (p, N)]
  rw [← liPresentedJetMap_mk W m
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI]
  rw [hf, hy]
  change (DirectSum.component ℂ (ℕ × ℕ)
    (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
      ((DirectSum.lof ℂ (ℕ × ℕ)
        (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N)) z) = z
  rw [DirectSum.component.lof_self]

/-- In the stable Li range `p ≤ m`, the generator-word surjection and a carrier finrank bound
give injectivity of the exact-bidegree map with no further homogeneity hypothesis.

⚠ **Scope of `hdec`.**  Since `gen` is a finite family, `hdec` forces `C2Cofinite W`
(certificate `L11cert_hdec_C2Cofinite`, `Notes/Textbook/certificates/L11_Checks.lean`), so this
theorem applies only to `C₂`-cofinite VOAs; it is narrower than Li's theorem, and for instance it
has no instance at `L_{-4/3}(sl₂)` (`QuasiLisseSl2.not_C2Cofinite_simpleSl2QL`). -/
theorem liPresentedJetBidegreeMap_injective_of_generators_of_finrank_le
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (hpositive : ∀ i, 0 < wt i)
    (p N : ℕ) (hp : p ≤ m)
    (hle : Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt m p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    Function.Injective
      (liPresentedJetBidegreeMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N) :=
  liPresentedJetBidegreeMap_injective_of_surjective_of_finrank_le
    W m (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
      I hI wt hpositive p N
      (liPresentedJetBidegreeMap_surjective_of_generators
        W m gen wt hgen I hI hdec p N hp) hle

/-- For homogeneous degree-zero generators, the component-kernel hypothesis in the abstract
Hilbert-squeeze theorem is automatic.  Thus exactness of the finite Li kernel reduces precisely
to bidegreewise surjectivity and the carrier/Hilbert dimension inequality. -/
theorem liFiniteJetPolynomialMap_kernel_eq_of_bidegree_hilbert_squeeze_generators
    (W : VertexOperatorAlgebra V) (m : ℕ)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hpositive : ∀ i, 0 < wt i)
    (hsurj : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N))
    (hle : ∀ p N,
      Module.finrank ℂ
          (FiniteJet.PresentedJetLiBidegreeImage wt m p N I) ≤
        Module.finrank ℂ (liWeightLayer W p N)) :
    RingHom.ker
        (liFiniteJetPolynomialMap W m
          (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)).toRingHom =
      FiniteJet.jetIdeal (R := ℂ) m I := by
  apply liFiniteJetPolynomialMap_kernel_eq_of_bidegree_hilbert_squeeze
    W m (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
      I hI wt hpositive
  · intro f hf d
    apply RingHom.mem_ker.mpr
    exact liFiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
      W m gen wt hgen f (RingHom.mem_ker.mp hf) d
  · exact hsurj
  · exact hle

end FiniteJetBidegree

end VOA

section AxiomAudit
#print axioms VOA.liFiniteJetPolynomialMap_isLiBihomogeneous
#print axioms VOA.liFiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
#print axioms VOA.liPresentedJetBidegreeMap_surjective_of_generators
#print axioms VOA.liPresentedJetBidegreeMap_surjective_of_homogeneous_hits
#print axioms VOA.liPresentedJetBidegreeMap_injective_of_generators_of_finrank_le
#print axioms VOA.liFiniteJetPolynomialMap_kernel_eq_of_bidegree_hilbert_squeeze_generators
end AxiomAudit
