import VOA.Classification.COne.PlusSplitResidual
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A dimension-and-characters route to plus Zhu semisimplicity

The remaining VOA inputs are an upper bound and distinct algebra characters,
not an assumed complete-reducibility theorem. Their source is Dong--Nagatomo,
https://arxiv.org/pdf/math/9807168, Section 5 (Propositions 5.9--5.11 and
Theorem 5.13). For squared lattice length `2*m`, `m >= 2`, the count is `m+7`.
Neither of these two inputs is proved in this file.
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting

section Characters
variable {K R ι : Type*} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [Fintype ι]

/-- Evaluate an algebra element in a finite family of characters. -/
def characterEvaluation (χ : ι → R →ₐ[K] K) : R →ₐ[K] (ι → K) where
  toFun x i := χ i x
  map_one' := by ext i; exact map_one (χ i)
  map_zero' := by ext i; exact map_zero (χ i)
  map_add' x y := by ext i; exact map_add (χ i) x y
  map_mul' x y := by ext i; exact map_mul (χ i) x y
  commutes' x := by ext i; exact (χ i).commutes x

/-- Distinct characters saturating a dimension bound exhaust the algebra.
No commutativity of the source algebra is assumed. -/
theorem characterEvaluation_bijective (χ : ι → R →ₐ[K] K)
    (hχ : Function.Injective χ) (hdim : Module.finrank K R ≤ Fintype.card ι) :
    Function.Bijective (characterEvaluation χ) := by
  have hli := (linearIndependent_algHom_toLinearMap K R K).comp χ hχ
  have hcard : Fintype.card ι = Module.finrank K (Module.Dual K R) := by
    apply le_antisymm hli.fintype_card_le_finrank
    simpa using hdim
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  simp only [Function.comp_def] at hspan
  have hinj : Function.Injective (characterEvaluation χ) := by
    apply (LinearMap.ker_eq_bot (f := (characterEvaluation χ).toLinearMap)).mp
    apply bot_unique
    intro x hx
    change x = 0
    apply (Module.forall_dual_apply_eq_zero_iff K x).mp
    intro f
    have hf : f ∈ Submodule.span K (Set.range (fun i => (χ i).toLinearMap)) := by
      rw [hspan]; trivial
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact congrFun hx i
    | zero => rfl
    | add f g _ _ hf hg => simp [hf, hg]
    | smul c f _ hf => simp [hf]
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (characterEvaluation χ).toLinearMap) ?_).mp hinj
  simpa using hcard.symm

/-- A finite algebra with enough distinct characters is a product of fields. -/
noncomputable def characterAlgEquiv (χ : ι → R →ₐ[K] K)
    (hχ : Function.Injective χ) (hdim : Module.finrank K R ≤ Fintype.card ι) :
    R ≃ₐ[K] (ι → K) :=
  AlgEquiv.ofBijective (characterEvaluation χ) (characterEvaluation_bijective χ hχ hdim)

theorem isSemisimpleRing_of_characters (χ : ι → R →ₐ[K] K)
    (hχ : Function.Injective χ) (hdim : Module.finrank K R ≤ Fintype.card ι) :
    IsSemisimpleRing R :=
  (characterAlgEquiv χ hχ hdim).symm.toRingEquiv.isSemisimpleRing

end Characters
end VOA.Classification.COne.PlusSplitting

namespace VOA.Classification.COne
open PlusSplitting

/-- OPEN: the spanning-set bound of Dong--Nagatomo Section 5, on the actual
Zhu quotient. C2 cofiniteness already supplies finite dimensionality. -/
def V2mPlusZhuDimensionBound : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤ m + 7

/-- OPEN: the `m+7` distinct one-dimensional top representations from
Dong--Nagatomo Sections 2 and 5. This asks only for their characters, not
completeness of the module list. Numerical lowest weights alone do not suffice. -/
def V2mPlusZhuDistinctCharacters : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : Fin (m + 7) → VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, Function.Injective χ

/-- Dong--Nagatomo's two explicit algebra inputs imply the exact
semisimplicity target `ZhuV2mPlusSemisimple`. Neither input is silently discharged. -/
theorem zhuV2mPlusSemisimple_of_dimension_characters
    (hdim : V2mPlusZhuDimensionBound) (hchar : V2mPlusZhuDistinctCharacters) :
    ZhuV2mPlusSemisimple := by
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  letI := finiteDimensional_A_of_C2Cofinite _ (V2mPlus_c2Cofinite m hm)
  obtain ⟨χ, hχ⟩ := hchar m hm hm2
  exact isSemisimpleRing_of_characters χ hχ (by simpa using hdim m hm hm2)

theorem generalizedGeneratorSplitting_of_dimension_characters_lifting_resonant
    (hdim : V2mPlusZhuDimensionBound) (hchar : V2mPlusZhuDistinctCharacters)
    (hlift : V2mPlusEqualBottomZhuLifting) (hres : V2mPlusResonantBottomSplitting) :
    V2mPlusGeneralizedGeneratorSplittingFactGe2 :=
  generalizedGeneratorSplitting_of_zhu_lifting_resonant
    (zhuV2mPlusSemisimple_of_dimension_characters hdim hchar) hlift hres

end VOA.Classification.COne
