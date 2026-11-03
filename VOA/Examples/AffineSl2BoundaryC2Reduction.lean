/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.Presentation
import VOA.Examples.AffineSl2BoundaryC2
import VOA.Examples.AffineSl2Presentation

/-!
# Reducing the boundary affine `C₂` presentation to the singular-submodule image

This file isolates the exact formal-algebra step behind the boundary affine `sl₂` `C₂`
presentation.  For a quotient vertex operator algebra `W / I`, it proves that

```text
ker (A₂(W) → A₂(W / I)) = image (I → A₂(W)).
```

Thus the only representation-theoretic input needed to identify the kernel of the boundary
symbol map is the `C₂` image of the maximal (equivalently, singular-generated) affine submodule.
That input is exposed below as an ordinary theorem hypothesis, not installed as an axiom.

The result is deliberately independent of the boundary character/classical-freeness argument:
using the desired `C₂` presentation to prove the singular-submodule image hypothesis would be
circular.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace QuotVOA

variable {W : VertexOperatorAlgebra 𝒱} {I : Submodule ℂ 𝒱}

/-! ## The exact `C₂` sequence of a VOA quotient -/

/-- The `C₂` subspace of a quotient VOA is exactly the image of the source `C₂` subspace.

The forward inclusion lifts both entries of each quotient `(-2)`-product; the reverse inclusion
is functoriality of the quotient products. -/
theorem O₂_quotient_eq_map (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    O₂ (quotientVOA W I hI hgr) = (O₂ W).map I.mkQ := by
  apply le_antisymm
  · rw [O₂, Submodule.span_le]
    rintro x ⟨u, v, rfl⟩
    obtain ⟨u', rfl⟩ := I.mkQ_surjective u
    obtain ⟨v', rfl⟩ := I.mkQ_surjective v
    rw [quotientVOA_mkQ_smul]
    exact Submodule.mem_map.mpr ⟨W.smul u' (-2) v',
      Submodule.subset_span ⟨u', v', rfl⟩, rfl⟩
  · rw [O₂, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [← quotientVOA_mkQ_smul hI hgr a (-2) b]
    exact Submodule.subset_span ⟨I.mkQ a, I.mkQ b, rfl⟩

/-- Exactness of `C₂` under a VOA quotient: the kernel is the image of the quotient ideal.

This is the precise linear-algebra identity
`ker(A₂(W) → A₂(W/I)) = (I + O₂(W))/O₂(W)`. -/
theorem ker_A₂quotₗ_eq_map (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    LinearMap.ker (A₂quotₗ hI hgr) = I.map (mk₂ W) := by
  ext p
  obtain ⟨u, rfl⟩ := mk₂_surjective W p
  constructor
  · intro hu
    rw [LinearMap.mem_ker, A₂quotₗ_mk₂] at hu
    have hqu : I.mkQ u ∈ O₂ (quotientVOA W I hI hgr) :=
      (mk₂_eq_zero_iff _).mp hu
    rw [O₂_quotient_eq_map hI hgr] at hqu
    obtain ⟨o, hoO₂, hou⟩ := Submodule.mem_map.mp hqu
    refine Submodule.mem_map.mpr ⟨u - o, ?_, ?_⟩
    · have heq : I.mkQ u = I.mkQ o := hou.symm
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at heq
      exact heq
    · rw [map_sub, (mk₂_eq_zero_iff W).mpr hoO₂, sub_zero]
  · rintro ⟨i, hiI, hiu⟩
    rw [LinearMap.mem_ker, ← hiu, A₂quotₗ_mk₂]
    rw [show I.mkQ i = 0 from (Submodule.Quotient.mk_eq_zero I).mpr hiI, map_zero]

/-- The image of a VOA ideal in `A₂(W)`, bundled as an ideal of the commutative ring `A₂(W)`.

Closure under multiplication is exactly VOA-ideal absorption at mode `-1`. -/
def A₂IdealImage (hI : W.IsIdeal I) : Ideal (A₂ W) where
  carrier := I.map (mk₂ W)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := by
    intro p x hx
    obtain ⟨i, hiI, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨u, rfl⟩ := mk₂_surjective W p
    refine Submodule.mem_map.mpr ⟨poissonMul W u i, ?_, ?_⟩
    · exact hI u i (-1) hiI
    · rw [smul_eq_mul, A₂_mul_mk]

@[simp] theorem mem_A₂IdealImage_iff (hI : W.IsIdeal I) (p : A₂ W) :
    p ∈ A₂IdealImage hI ↔ p ∈ I.map (mk₂ W) := Iff.rfl

/-- The algebra-map membership version of `ker_A₂quotₗ_eq_map`.

The two sides have different bundled scalar structures (`Ideal` versus `ℂ`-submodule), so the
canonical statement is a membership equivalence. -/
theorem mem_ker_A₂quot_iff (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (p : A₂ W) :
    p ∈ RingHom.ker (A₂quot hI hgr) ↔ p ∈ I.map (mk₂ W) := by
  change p ∈ LinearMap.ker (A₂quotₗ hI hgr) ↔ _
  rw [ker_A₂quotₗ_eq_map hI hgr]

/-- Exactness of `C₂` under quotient, as an equality of ring ideals. -/
theorem ker_A₂quot_eq_idealImage (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    RingHom.ker (A₂quot hI hgr) = A₂IdealImage hI := by
  ext p
  exact mem_ker_A₂quot_iff hI hgr p

end QuotVOA

namespace AffineSl2BoundaryC2

open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.QuasiLisseSl2
open VOA.SingVec
open VOA.Sl2Pres

noncomputable section

/-! ## The exact non-circular representation-theoretic interface -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The quotient symbol map associated to a VOA ideal in the universal affine `sl₂` VOA. -/
def quotientSymbol (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I) :
    SymSl2 →ₐ[ℂ] A₂ (QuotVOA.quotientVOA (affineSl2VOA_closed k hk) I hI hgr) :=
  (QuotVOA.A₂quot hI hgr).comp (symbolAlg k hk)

/-- The quotient symbol map is surjective, without any PBW-independence assumption. -/
theorem quotientSymbol_surjective
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I) :
    Function.Surjective (quotientSymbol k hk I hI hgr) :=
  (QuotVOA.A₂quot_surjective hI hgr).comp (symbolAlg_surjective k hk)

/-- The PBW/representation-theory statement needed for the boundary presentation: the `C₂`
image of the affine quotient ideal is exactly the image of the displayed classical ideal.

For the simple boundary quotient one takes `I` to be the maximal graded ideal.  If a published
singular-generator theorem identifies that ideal with `idealGen W s`, this predicate becomes
literally the paper proposition that the `C₂` image of the singular submodule generated by `s`
is `(Cas^n e, Cas^n h, Cas^n f)`. -/
def BoundaryC2Image (n : ℕ) (I : Submodule ℂ (WakModule k)) : Prop :=
  ∀ x : A₂ (affineSl2VOA_closed k hk),
    x ∈ I.map (mk₂ (affineSl2VOA_closed k hk)) ↔
      x ∈ Ideal.map (symbolAlg k hk) (boundaryIdeal n)

/-- `BoundaryC2Image` is literally equality between the `C₂` image ideal and the proposed
classical relation ideal. -/
theorem boundaryC2Image_iff_ideal_eq
    (n : ℕ) (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I) :
    BoundaryC2Image k hk n I ↔
      QuotVOA.A₂IdealImage hI = Ideal.map (symbolAlg k hk) (boundaryIdeal n) := by
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    change x ∈ QuotVOA.A₂IdealImage hI ↔ _
    rw [h]

/-- The paper's singular-submodule proposition, stated independently of maximality: the image
of the vertex-algebra ideal generated by `s` in the universal `C₂` algebra is exactly the ideal
generated by `(Cas^n e, Cas^n h, Cas^n f)`. -/
def SingularC2Image (n : ℕ) (s : WakModule k) : Prop :=
  ∀ x : A₂ (affineSl2VOA_closed k hk),
    x ∈ (idealGen (affineSl2VOA_closed k hk) s).map
        (mk₂ (affineSl2VOA_closed k hk)) ↔
      x ∈ Ideal.map (symbolAlg k hk) (boundaryIdeal n)

/-- Ideal-equality form of the singular-submodule `C₂` image proposition. -/
theorem singularC2Image_iff_ideal_eq (n : ℕ) (s : WakModule k) :
    SingularC2Image k hk n s ↔
      QuotVOA.A₂IdealImage (idealGen_isIdeal (affineSl2VOA_closed k hk) s) =
        Ideal.map (symbolAlg k hk) (boundaryIdeal n) :=
  boundaryC2Image_iff_ideal_eq k hk n _ (idealGen_isIdeal _ _)

/-- Injectivity of the universal affine symbol map converts equality of `C₂` images into the
exact kernel of the quotient symbol map. -/
theorem exact_quotientSymbol_of_boundaryC2Image
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I)
    (huniv : Function.Injective (symbolAlg k hk))
    (himage : BoundaryC2Image k hk n I) :
    Presentation.IsExactPresentation (boundaryIdeal n) (quotientSymbol k hk I hI hgr) := by
  rw [Presentation.IsExactPresentation]
  ext p
  constructor
  · intro hp
    have hker : symbolAlg k hk p ∈ RingHom.ker (QuotVOA.A₂quot hI hgr) := hp
    rw [QuotVOA.mem_ker_A₂quot_iff hI hgr, himage,
      Ideal.mem_map_iff_of_surjective _ (symbolAlg_surjective k hk)] at hker
    obtain ⟨q, hq, hpq⟩ := hker
    have : p = q := huniv hpq.symm
    simpa [this] using hq
  · intro hp
    change QuotVOA.A₂quot hI hgr (symbolAlg k hk p) = 0
    rw [← RingHom.mem_ker, QuotVOA.mem_ker_A₂quot_iff hI hgr, himage]
    exact Ideal.mem_map_of_mem _ hp

/-- With universal affine PBW injectivity, exactness of the boundary presentation is equivalent
to the `C₂` image identity for the quotient ideal.  This is the sharp reduction: neither side is
smuggled into the other as an assumption. -/
theorem exact_quotientSymbol_iff_boundaryC2Image
    (I : Submodule ℂ (WakModule k))
    (hI : (affineSl2VOA_closed k hk).IsIdeal I)
    (hgr : QuotVOA.IsGradedIdeal (affineSl2VOA_closed k hk) I)
    (huniv : Function.Injective (symbolAlg k hk)) :
    Presentation.IsExactPresentation (boundaryIdeal n) (quotientSymbol k hk I hI hgr) ↔
      BoundaryC2Image k hk n I := by
  constructor
  · intro hex x
    obtain ⟨p, rfl⟩ := symbolAlg_surjective k hk x
    constructor
    · intro himage
      have hzero : quotientSymbol k hk I hI hgr p = 0 :=
        (QuotVOA.mem_ker_A₂quot_iff hI hgr (symbolAlg k hk p)).mpr himage
      have hp : p ∈ boundaryIdeal n := by
        have hpker : p ∈ RingHom.ker (quotientSymbol k hk I hI hgr) := hzero
        rwa [hex] at hpker
      exact Ideal.mem_map_of_mem _ hp
    · intro hrel
      rw [Ideal.mem_map_iff_of_surjective _ (symbolAlg_surjective k hk)] at hrel
      obtain ⟨q, hq, hqp⟩ := hrel
      have hqp' : q = p := huniv hqp
      subst q
      apply (QuotVOA.mem_ker_A₂quot_iff hI hgr (symbolAlg k hk p)).mp
      have hpker : p ∈ RingHom.ker (quotientSymbol k hk I hI hgr) := by
        rw [hex]
        exact hq
      exact hpker
  · exact exact_quotientSymbol_of_boundaryC2Image k hk I hI hgr huniv

/-- A singular-generator presentation of the affine maximal ideal rewrites the remaining
`BoundaryC2Image` input as the `C₂` image of the singular submodule itself. -/
theorem boundaryC2Image_maximal_of_singular
    (s : WakModule k)
    (hmax : QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk) =
      idealGen (affineSl2VOA_closed k hk) s)
    (hsing : SingularC2Image k hk n s) :
    BoundaryC2Image k hk n (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk)) := by
  unfold BoundaryC2Image
  intro x
  rw [hmax]
  exact hsing x

/-- The boundary simple-quotient `C₂` presentation follows from exactly three external inputs:

1. PBW injectivity for `R_{V^k(sl₂)} = Sym(sl₂)`;
2. generation of the maximal affine ideal by the named singular vector;
3. the singular submodule's `C₂` image identity.

No associated-variety or classical-freeness conclusion is used in this reduction. -/
theorem exact_boundary_simple_of_singularC2Image
    (s : WakModule k)
    (huniv : Function.Injective (symbolAlg k hk))
    (hmax : QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk) =
      idealGen (affineSl2VOA_closed k hk) s)
    (hsing : SingularC2Image k hk n s) :
    Presentation.IsExactPresentation (boundaryIdeal n)
      (quotientSymbol k hk (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk))
        (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)) := by
  apply exact_quotientSymbol_of_boundaryC2Image k hk
  · exact huniv
  · exact boundaryC2Image_maximal_of_singular k hk s hmax hsing

/-- Algebra equivalence form of the exact boundary simple-quotient presentation. -/
noncomputable def boundarySimpleQuotientEquiv_of_singularC2Image
    (s : WakModule k)
    (huniv : Function.Injective (symbolAlg k hk))
    (hmax : QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk) =
      idealGen (affineSl2VOA_closed k hk) s)
    (hsing : SingularC2Image k hk n s) :
    (SymSl2 ⧸ boundaryIdeal n) ≃ₐ[ℂ]
      A₂ (QuotVOA.maxQuotientVOA (affineSl2VOA_closed k hk)) :=
  Presentation.quotientEquiv (boundaryIdeal n)
    (quotientSymbol k hk (QuotVOA.maxGradedIdeal (affineSl2VOA_closed k hk))
      (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _))
    (quotientSymbol_surjective k hk _ _ _)
    (exact_boundary_simple_of_singularC2Image k hk s huniv hmax hsing)

end
end AffineSl2BoundaryC2
end VOA

section AxiomAudit
#print axioms VOA.QuotVOA.O₂_quotient_eq_map
#print axioms VOA.QuotVOA.ker_A₂quotₗ_eq_map
#print axioms VOA.QuotVOA.A₂IdealImage
#print axioms VOA.QuotVOA.mem_ker_A₂quot_iff
#print axioms VOA.QuotVOA.ker_A₂quot_eq_idealImage
#print axioms VOA.AffineSl2BoundaryC2.exact_boundary_simple_of_singularC2Image
#print axioms VOA.AffineSl2BoundaryC2.boundarySimpleQuotientEquiv_of_singularC2Image
end AxiomAudit
