/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.InfiniteClassicalFreeness
import VOA.Filtered.LiJetBidegree

/-!
# Stable-bidegree passage from finite jets to the infinite Li map

A finite jet map of order `m` need not be surjective onto Li layers of degree larger than `m`.
For the infinite map this causes no problem: a polynomial of exact Li degree `p` only uses jet
variables of individual order at most `p`, so it comes from the order-`p` finite jet algebra.
This file formalizes that stable-bidegree reduction.
-/

namespace VOA

open scoped DirectSum

universe u

namespace InfiniteJet

variable {σ : Type u}

/-- Natural Li/conformal bidegree on an unbounded jet variable. -/
def jetLiBidegree (baseWeight : σ → ℕ) : σ × ℕ → ℕ × ℕ :=
  fun v => (v.2, baseWeight v.1 + v.2)

/-- Exact Li/conformal bidegree in the unbounded jet polynomial ring. -/
abbrev JetLiBidegreePiece (K : Type*) [CommSemiring K]
    (baseWeight : σ → ℕ) (p N : ℕ) :=
  MvPolynomial.weightedHomogeneousSubmodule K (jetLiBidegree baseWeight) (p, N)

@[simp] theorem jetLiBidegree_finiteJetVar (baseWeight : σ → ℕ) (p : ℕ)
    (v : FiniteJet.JetVar σ p) :
    jetLiBidegree baseWeight (finiteJetVar p v) =
      FiniteJet.jetLiBidegree baseWeight p v := rfl

theorem weight_mapDomain_finiteJetVar (baseWeight : σ → ℕ) (p : ℕ)
    (d : FiniteJet.JetVar σ p →₀ ℕ) :
    Finsupp.weight (jetLiBidegree baseWeight)
        (d.mapDomain (finiteJetVar p)) =
      Finsupp.weight (FiniteJet.jetLiBidegree baseWeight p) d := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · simp [Finsupp.weight_apply]
  · simp
  · intro b n₁ n₂
    exact add_nsmul (jetLiBidegree baseWeight b) n₁ n₂

/-- Finite-to-infinite inclusion preserves the natural Li bidegree. -/
theorem ofFinite_isWeightedHomogeneous_jetLiBidegree
    {K : Type*} [CommSemiring K]
    (baseWeight : σ → ℕ) (p : ℕ)
    {f : FiniteJet.JetPoly K σ p} {d : ℕ × ℕ}
    (hf : f.IsWeightedHomogeneous (FiniteJet.jetLiBidegree baseWeight p) d) :
    (ofFinite (R := K) p f).IsWeightedHomogeneous (jetLiBidegree baseWeight) d := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isWeightedHomogeneous_zero K _ _
  | add f g hf hg ihf ihg => simpa only [map_add] using ihf.add ihg
  | monomial e c he =>
      rw [ofFinite, MvPolynomial.rename_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [weight_mapDomain_finiteJetVar baseWeight p e, he]

/-- Restricting an infinite homogeneous polynomial to variables of order at most `p` preserves
its natural Li bidegree. -/
theorem killCompl_isWeightedHomogeneous_jetLiBidegree
    {K : Type*} [CommSemiring K]
    (baseWeight : σ → ℕ) (p : ℕ)
    {f : JetPoly K σ} {d : ℕ × ℕ}
    (hf : f.IsWeightedHomogeneous (jetLiBidegree baseWeight) d) :
    (MvPolynomial.killCompl (finiteJetVar_injective p) f).IsWeightedHomogeneous
      (FiniteJet.jetLiBidegree baseWeight p) d := by
  intro e he
  rw [MvPolynomial.coeff_killCompl] at he
  have hweight := hf he
  rw [weight_mapDomain_finiteJetVar baseWeight p e] at hweight
  exact hweight

/-- In exact Li degree `p`, every variable occurring in a monomial has jet order at most `p`. -/
theorem monomialSupport_subset_range_finiteJetVar_of_liDegree
    (baseWeight : σ → ℕ) (p N : ℕ) (d : (σ × ℕ) →₀ ℕ)
    (hd : Finsupp.weight (jetLiBidegree baseWeight) d = (p, N)) :
    (↑d.support : Set (σ × ℕ)) ⊆ Set.range (finiteJetVar p) := by
  intro v hv
  have hne : d v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have horder : v.2 ≤ p := by
    have hpos : 0 < d v := Nat.pos_of_ne_zero hne
    have hsum : (∑ i ∈ d.support, d i * i.2) = p := by
      have hfirst := congrArg Prod.fst hd
      simpa [Finsupp.weight_apply, Finsupp.sum, jetLiBidegree,
        Prod.fst_sum, nsmul_eq_mul] using hfirst
    have hterm : d v * v.2 ≤ ∑ i ∈ d.support, d i * i.2 := by
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (d i * i.2)) hv
    rw [hsum] at hterm
    have hvleprod : v.2 ≤ d v * v.2 := Nat.le_mul_of_pos_left v.2 hpos
    omega
  exact ⟨⟨v.1, ⟨v.2, Nat.lt_succ_iff.mpr horder⟩⟩, rfl⟩

theorem ofFinite_killCompl_eq_of_support_subset
    {K : Type*} [CommSemiring K]
    (p : ℕ) (f : JetPoly K σ)
    (hsupport : ∀ d ∈ f.support,
      (↑d.support : Set (σ × ℕ)) ⊆ Set.range (finiteJetVar p)) :
    ofFinite (R := K) p (MvPolynomial.killCompl (finiteJetVar_injective p) f) = f := by
  rw [MvPolynomial.as_sum f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset
    (finiteJetVar_injective p) _ (hsupport d hd)]
  rw [ofFinite, MvPolynomial.rename_monomial,
    d.mapDomain_comapDomain _ (finiteJetVar_injective p) (hsupport d hd)]

/-- Every infinite polynomial of exact Li degree `p` has a bidegree-preserving preimage already
at finite jet order `p`. -/
theorem liBidegreePiece_ofFinite_surjective
    {K : Type*} [CommSemiring K]
    (baseWeight : σ → ℕ) (p N : ℕ) :
    Function.Surjective fun
      f : FiniteJet.JetLiBidegreePiece K baseWeight p p N =>
        (⟨ofFinite (R := K) p f.1,
          ofFinite_isWeightedHomogeneous_jetLiBidegree
            baseWeight p f.2⟩ : JetLiBidegreePiece K baseWeight p N) := by
  intro f
  let g : FiniteJet.JetLiBidegreePiece K baseWeight p p N :=
    ⟨MvPolynomial.killCompl (finiteJetVar_injective p) f.1,
      killCompl_isWeightedHomogeneous_jetLiBidegree baseWeight p f.2⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply ofFinite_killCompl_eq_of_support_subset p f.1
  intro d hd
  exact monomialSupport_subset_range_finiteJetVar_of_liDegree
    baseWeight p N d (f.2 (MvPolynomial.mem_support_iff.mp hd))

end InfiniteJet

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

section InfiniteLiEvaluation

variable {g : ℕ}

/-- The polynomial-level infinite Li evaluation on homogeneous degree-zero generators. -/
noncomputable def liInfiniteJetPolynomialMap
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) :
    InfiniteJet.JetPoly ℂ (Fin g) →ₐ[ℂ] liAssociatedGraded W :=
  InfiniteJet.derivationJetEval (liAssociatedGradedTranslation W)
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)

/-- Evaluation of a polynomial representative by the presented infinite Li map. -/
@[simp] theorem liInfinitePresentedJetMap_mk_liGenerators
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (f : InfiniteJet.JetPoly ℂ (Fin g)) :
    liInfinitePresentedJetMap W
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI
        (InfiniteJet.presentedJetMk (R := ℂ) I f) =
      liInfiniteJetPolynomialMap W gen wt hgen f :=
  rfl

/-- Infinite Li evaluation, as an algebra map, restricts to the finite Li evaluation. -/
theorem liInfiniteJetPolynomialMap_comp_ofFinite
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (m : ℕ) :
    (liInfiniteJetPolynomialMap W gen wt hgen).comp
        (InfiniteJet.ofFinite (R := ℂ) m) =
      liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) := by
  simpa only [liInfiniteJetPolynomialMap, liFiniteJetPolynomialMap] using
    (InfiniteJet.derivationJetEval_comp_ofFinite
      (liAssociatedGradedTranslation W) m
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩))

/-- Infinite evaluation agrees with finite evaluation under the canonical inclusion. -/
theorem liInfiniteJetPolynomialMap_ofFinite
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (m : ℕ) (f : FiniteJet.JetPoly ℂ (Fin g) m) :
    liInfiniteJetPolynomialMap W gen wt hgen (InfiniteJet.ofFinite m f) =
      liFiniteJetPolynomialMap W m
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) f :=
  DFunLike.congr_fun
    (liInfiniteJetPolynomialMap_comp_ofFinite W gen wt hgen m) f

/-- An infinite weighted-homogeneous jet polynomial evaluates in the matching Li bidegree. -/
theorem liInfiniteJetPolynomialMap_isLiBihomogeneous
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    {f : InfiniteJet.JetPoly ℂ (Fin g)} {p N : ℕ}
    (hf : f.IsWeightedHomogeneous (InfiniteJet.jetLiBidegree wt) (p, N)) :
    IsLiBihomogeneous W (p, N) (liInfiniteJetPolynomialMap W gen wt hgen f) := by
  let z : InfiniteJet.JetLiBidegreePiece ℂ wt p N := ⟨f, hf⟩
  obtain ⟨q, hq⟩ := InfiniteJet.liBidegreePiece_ofFinite_surjective wt p N z
  have hfinite := liFiniteJetPolynomialMap_isLiBihomogeneous
    W p gen wt hgen q.2
  have hqval : InfiniteJet.ofFinite (R := ℂ) p q.1 = f :=
    congrArg Subtype.val hq
  rw [← hqval, liInfiniteJetPolynomialMap_ofFinite]
  exact hfinite

/-- Projecting infinite Li evaluation to bidegree `d` depends only on the weighted-homogeneous
component of degree `d`. -/
theorem liInfiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (f : InfiniteJet.JetPoly ℂ (Fin g)) (d : ℕ × ℕ) :
    DirectSum.component ℂ (ℕ × ℕ)
        (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d
        (liInfiniteJetPolynomialMap W gen wt hgen f) =
      DirectSum.component ℂ (ℕ × ℕ)
        (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d
        (liInfiniteJetPolynomialMap W gen wt hgen
          (MvPolynomial.weightedHomogeneousComponent
            (InfiniteJet.jetLiBidegree wt) d f)) := by
  classical
  let E := liInfiniteJetPolynomialMap W gen wt hgen
  let P : InfiniteJet.JetPoly ℂ (Fin g) →ₗ[ℂ] liWeightLayer W d.1 d.2 :=
    (DirectSum.component ℂ (ℕ × ℕ)
      (fun e : ℕ × ℕ => liWeightLayer W e.1 e.2) d).comp E.toLinearMap
  change P f = P (MvPolynomial.weightedHomogeneousComponent
    (InfiniteJet.jetLiBidegree wt) d f)
  calc
    P f = P (∑ᶠ e : ℕ × ℕ,
        MvPolynomial.weightedHomogeneousComponent
          (InfiniteJet.jetLiBidegree wt) e f) := by
      rw [MvPolynomial.sum_weightedHomogeneousComponent]
    _ = ∑ᶠ e : ℕ × ℕ, P
        (MvPolynomial.weightedHomogeneousComponent
          (InfiniteJet.jetLiBidegree wt) e f) := by
      exact P.toAddMonoidHom.map_finsum
        (MvPolynomial.weightedHomogeneousComponent_finsupp f)
    _ = P (MvPolynomial.weightedHomogeneousComponent
        (InfiniteJet.jetLiBidegree wt) d f) := by
      apply finsum_eq_single
      intro e hed
      have he := liInfiniteJetPolynomialMap_isLiBihomogeneous
        W gen wt hgen
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
          (w := InfiniteJet.jetLiBidegree wt) (n := e) (φ := f))
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

/-- Taking a weighted-homogeneous component preserves the kernel of infinite Li evaluation. -/
theorem liInfiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (f : InfiniteJet.JetPoly ℂ (Fin g))
    (hzero : liInfiniteJetPolynomialMap W gen wt hgen f = 0)
    (d : ℕ × ℕ) :
    liInfiniteJetPolynomialMap W gen wt hgen
        (MvPolynomial.weightedHomogeneousComponent
          (InfiniteJet.jetLiBidegree wt) d f) = 0 := by
  let q := MvPolynomial.weightedHomogeneousComponent
    (InfiniteJet.jetLiBidegree wt) d f
  have hqhom : IsLiBihomogeneous W d
      (liInfiniteJetPolynomialMap W gen wt hgen q) :=
    liInfiniteJetPolynomialMap_isLiBihomogeneous W gen wt hgen
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := InfiniteJet.jetLiBidegree wt) (n := d) (φ := f))
  apply hqhom.eq_zero_of_component_eq_zero W
  rw [← liInfiniteJetPolynomialMap_component_eq_component_weightedHomogeneousComponent
    W gen wt hgen f d, hzero, map_zero]

/-- **Stable-bidegree exact-kernel theorem from direct homogeneous surjectivity.**  It is enough
to compare the exact `(p,N)` piece at finite jet order `p`, provided the restricted maps are
surjective there.  This formulation is needed for affine current-word arguments: their `C₂`
algebras need not be finite-dimensional, so a global `span generators ⊔ O₂ = ⊤` hypothesis can be
false even though every homogeneous Li layer has the required current-word preimages. -/
theorem liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze_of_surjective
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hpositive : ∀ i, 0 < wt i)
    (hsurj : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W p
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N))
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    RingHom.ker (liInfiniteJetPolynomialMap W gen wt hgen).toRingHom =
      InfiniteJet.jetIdeal (R := ℂ) I := by
  apply le_antisymm
  · intro f hf
    rw [← MvPolynomial.sum_weightedHomogeneousComponent
      (InfiniteJet.jetLiBidegree wt) f]
    rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp f)]
    apply (InfiniteJet.jetIdeal (R := ℂ) I).sum_mem
    intro d _hd
    rcases d with ⟨p, N⟩
    let q := MvPolynomial.weightedHomogeneousComponent
      (InfiniteJet.jetLiBidegree wt) (p, N) f
    have hqhom : q.IsWeightedHomogeneous
        (InfiniteJet.jetLiBidegree wt) (p, N) :=
      MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := InfiniteJet.jetLiBidegree wt) (n := (p, N)) (φ := f)
    let z : InfiniteJet.JetLiBidegreePiece ℂ wt p N := ⟨q, hqhom⟩
    obtain ⟨a, ha⟩ := InfiniteJet.liBidegreePiece_ofFinite_surjective wt p N z
    have haVal : InfiniteJet.ofFinite (R := ℂ) p a.1 = q :=
      congrArg Subtype.val ha
    have hqzero : liInfiniteJetPolynomialMap W gen wt hgen q = 0 :=
      liInfiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
        W gen wt hgen f (RingHom.mem_ker.mp hf) (p, N)
    have hazero : liFiniteJetPolynomialMap W p
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) a.1 = 0 := by
      rw [← liInfiniteJetPolynomialMap_ofFinite W gen wt hgen p a.1, haVal]
      exact hqzero
    have hinj := liPresentedJetBidegreeMap_injective_of_surjective_of_finrank_le
      W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt hpositive p N (hsurj p N) (hle p N)
    have haIdeal : a.1 ∈ FiniteJet.jetIdeal (R := ℂ) p I :=
      mem_jetIdeal_of_bidegree_of_liPresentedJetBidegreeMap_injective
        W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
          I hI wt p N hinj a.2 hazero
    change q ∈ InfiniteJet.jetIdeal (R := ℂ) I
    rw [← haVal]
    exact InfiniteJet.ofFinite_mem_jetIdeal p I a.1 haIdeal
  · intro f hf
    apply RingHom.mem_ker.mpr
    change liInfiniteJetPolynomialMap W gen wt hgen f = 0
    rw [← liInfinitePresentedJetMap_mk_liGenerators
      W gen wt hgen I hI f]
    have hmk : InfiniteJet.presentedJetMk (R := ℂ) I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf
    rw [hmk, map_zero]

/-- The direct homogeneous-surjectivity stable squeeze makes the infinite presented Li map
injective, without any global finite-`C₂` generation assumption. -/
theorem liInfinitePresentedJetMap_injective_of_stable_bidegree_hilbert_squeeze_of_surjective
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hpositive : ∀ i, 0 < wt i)
    (hsurj : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W p
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N))
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    Function.Injective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI) := by
  apply (injective_iff_map_eq_zero (liInfinitePresentedJetMap W
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI)).mpr
  intro y
  refine Submodule.Quotient.induction_on _ y fun f hf ↦ ?_
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [←
    liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze_of_surjective
      W gen wt hgen I hI hpositive hsurj hle]
  apply RingHom.mem_ker.mpr
  exact hf

/-- Direct homogeneous surjectivity, stable exact-bidegree Hilbert bounds, and infinite
surjectivity prove presentation-level classical freeness. -/
theorem liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze_of_surjective
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hpositive : ∀ i, 0 < wt i)
    (hsurjBidegree : ∀ p N, Function.Surjective
      (liPresentedJetBidegreeMap W p
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
        I hI wt p N))
    (hsurjInfinite : Function.Surjective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI))
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    LiPresentationClassicallyFree W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI :=
  ⟨liInfinitePresentedJetMap_injective_of_stable_bidegree_hilbert_squeeze_of_surjective
      W gen wt hgen I hI hpositive hsurjBidegree hle,
    hsurjInfinite⟩

/-- **Stable-bidegree exact-kernel theorem.**  It is enough to compare the exact `(p,N)`
piece at finite jet order `p`.  This avoids the unnecessarily strong requirement that every
finite truncation be injective in Li degrees beyond its jet order. -/
theorem liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (hpositive : ∀ i, 0 < wt i)
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    RingHom.ker (liInfiniteJetPolynomialMap W gen wt hgen).toRingHom =
      InfiniteJet.jetIdeal (R := ℂ) I := by
  apply le_antisymm
  · intro f hf
    rw [← MvPolynomial.sum_weightedHomogeneousComponent
      (InfiniteJet.jetLiBidegree wt) f]
    rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp f)]
    apply (InfiniteJet.jetIdeal (R := ℂ) I).sum_mem
    intro d _hd
    rcases d with ⟨p, N⟩
    let q := MvPolynomial.weightedHomogeneousComponent
      (InfiniteJet.jetLiBidegree wt) (p, N) f
    have hqhom : q.IsWeightedHomogeneous
        (InfiniteJet.jetLiBidegree wt) (p, N) :=
      MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
        (w := InfiniteJet.jetLiBidegree wt) (n := (p, N)) (φ := f)
    let z : InfiniteJet.JetLiBidegreePiece ℂ wt p N := ⟨q, hqhom⟩
    obtain ⟨a, ha⟩ := InfiniteJet.liBidegreePiece_ofFinite_surjective wt p N z
    have haVal : InfiniteJet.ofFinite (R := ℂ) p a.1 = q :=
      congrArg Subtype.val ha
    have hqzero : liInfiniteJetPolynomialMap W gen wt hgen q = 0 :=
      liInfiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
        W gen wt hgen f (RingHom.mem_ker.mp hf) (p, N)
    have hazero : liFiniteJetPolynomialMap W p
        (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) a.1 = 0 := by
      rw [← liInfiniteJetPolynomialMap_ofFinite W gen wt hgen p a.1, haVal]
      exact hqzero
    have hinj := liPresentedJetBidegreeMap_injective_of_generators_of_finrank_le
      W p gen wt hgen I hI hdec hpositive p N (le_refl p) (hle p N)
    have haIdeal : a.1 ∈ FiniteJet.jetIdeal (R := ℂ) p I :=
      mem_jetIdeal_of_bidegree_of_liPresentedJetBidegreeMap_injective
        W p (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩)
          I hI wt p N hinj a.2 hazero
    change q ∈ InfiniteJet.jetIdeal (R := ℂ) I
    rw [← haVal]
    exact InfiniteJet.ofFinite_mem_jetIdeal p I a.1 haIdeal
  · intro f hf
    apply RingHom.mem_ker.mpr
    change liInfiniteJetPolynomialMap W gen wt hgen f = 0
    rw [← liInfinitePresentedJetMap_mk_liGenerators
      W gen wt hgen I hI f]
    have hmk : InfiniteJet.presentedJetMk (R := ℂ) I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf
    rw [hmk, map_zero]

/-- The stable bidegree Hilbert squeeze implies injectivity of the presented infinite Li map. -/
theorem liInfinitePresentedJetMap_injective_of_stable_bidegree_hilbert_squeeze
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (hpositive : ∀ i, 0 < wt i)
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    Function.Injective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI) := by
  apply (injective_iff_map_eq_zero (liInfinitePresentedJetMap W
    (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI)).mpr
  intro y
  refine Submodule.Quotient.induction_on _ y fun f hf ↦ ?_
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze
    W gen wt hgen I hI hdec hpositive hle]
  apply RingHom.mem_ker.mpr
  exact hf

/-- Stable exact-bidegree Hilbert bounds plus homogeneous surjectivity prove presentation-level
classical freeness of the infinite Li map. -/
theorem liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
    (W : VertexOperatorAlgebra V)
    (gen : Fin g → V) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (I : Ideal (MvPolynomial (Fin g) ℂ))
    (hI : I ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩).toRingHom)
    (hdec : (⊤ : Submodule ℂ V) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (hpositive : ∀ i, 0 < wt i)
    (hsurj : Function.Surjective (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI))
    (hle : ∀ p N, Module.finrank ℂ
        (FiniteJet.PresentedJetLiBidegreeImage wt p p N I) ≤
      Module.finrank ℂ (liWeightLayer W p N)) :
    LiPresentationClassicallyFree W
      (fun i => liDegreeZeroClass W (wt i) ⟨gen i, hgen i⟩) I hI :=
  ⟨liInfinitePresentedJetMap_injective_of_stable_bidegree_hilbert_squeeze
      W gen wt hgen I hI hdec hpositive hle,
    hsurj⟩

end InfiniteLiEvaluation

end VOA

section AxiomAudit
#print axioms VOA.InfiniteJet.liBidegreePiece_ofFinite_surjective
#print axioms VOA.liInfiniteJetPolynomialMap_isLiBihomogeneous
#print axioms VOA.liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze
#print axioms VOA.liInfiniteJetPolynomialMap_kernel_eq_of_stable_bidegree_hilbert_squeeze_of_surjective
#print axioms VOA.liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze
#print axioms VOA.liPresentationClassicallyFree_of_stable_bidegree_hilbert_squeeze_of_surjective
end AxiomAudit
