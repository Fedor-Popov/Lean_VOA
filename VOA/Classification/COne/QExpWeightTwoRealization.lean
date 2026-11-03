import VOA.Classification.COne.QExpWeightTwoAnalytic

/-!
# The remaining transformation and spanning inputs

The analytic functions are already defined and proved holomorphic and bounded
at infinity in `QExpWeightTwoAnalytic`. This file constructs genuine modular
forms conditional on only their slash laws, and proves their exact coefficients.

The slash laws below are consequences of the classical weight-one Eisenstein
transformation formula, with the nonzero rescalings fixed above. References:
Khuri-Makdisi, Section 2 and Corollary 3.13,
https://arxiv.org/html/0903.1439v6; Mascot, Theorem 4.2.2,
https://doi.org/10.1007/s40993-022-00329-6.
The scalar-orbit clause deliberately retains only what is needed at cusps,
rather than specifying the exact permutation of indices.

The independent product-spanning input is the restriction of Khuri-Makdisi,
Theorems 3.5 and 5.1, to Gamma1 weight-two forms. The published hypothesis
is N >= 3, satisfied by every positive multiple of 24. No input is an axiom
or is asserted to have been proved in Lean.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Invariance and scalar orbits of the explicitly defined functions.
These are actual transformation identities, with no modular-form existence
assumption. For primitive roots and N >= 3 they are classical true statements. -/
def WeightOneSlashLaws (N : ℕ) (ζ : ℂ) : Prop :=
  (∀ a b : Fin N, ∀ γ ∈ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)),
    weightOneQSeries N ζ a b ∣[(1 : ℤ)] γ = weightOneQSeries N ζ a b) ∧
  (∀ (a b : Fin N) (γ : SL(2, ℤ)), ∃ (a' b' : Fin N) (c : ℂ),
    weightOneQSeries N ζ a b ∣[(1 : ℤ)] γ = c • weightOneQSeries N ζ a' b')

/-- Missing classical transformation theorem, restricted to the levels needed. -/
def FullLevelWeightOneSlash24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → ∀ ζ : ℂ, IsPrimitiveRoot ζ N → WeightOneSlashLaws N ζ

/-- Missing classical spanning theorem for the concrete convergent functions.
No implication from a possibly empty type of realizations is used here. -/
def FullLevelWeightOneQSeriesSpan24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → ∀ ζ : ℂ, IsPrimitiveRoot ζ N →
    ∀ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2,
      ∃ (d : ℕ) (a b a' b' : Fin d → Fin N) (c : Fin d → ℂ),
        ∀ τ : ℍ, F τ = ∑ i, c i *
          (weightOneQSeries N ζ (a i) (b i) τ * weightOneQSeries N ζ (a' i) (b' i) τ)

/-- The scalar-orbit law transports the proved infinity bound to every cusp. -/
theorem boundedAtCusps_weightOneQSeries {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hslash : WeightOneSlashLaws N ζ) (a b : Fin N)
    {c : OnePoint ℝ} (hc : IsCusp c
      (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt (weightOneQSeries N ζ a b) 1 := by
  letI : NeZero N := ⟨hN.ne'⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  obtain ⟨a', b', c', heq⟩ := hslash.2 a b γ
  rw [heq]
  exact (bounded_weightOneQSeries hN hζ a' b').smul c'

/-- A genuine Mathlib modular form, conditional solely on the slash laws.
Its underlying function is the explicit convergent sum, not a choice of form. -/
def weightOneModularForm {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hslash : WeightOneSlashLaws N ζ) (a b : Fin N) :
    ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1 where
  toFun := weightOneQSeries N ζ a b
  slash_action_eq' := hslash.1 a b
  holo' := mdifferentiable_weightOneQSeries hN hζ a b
  bdd_at_cusps' hc := boundedAtCusps_weightOneQSeries hN hζ hslash a b hc

/-- All Fourier coefficients of the conditional construction are proved. -/
theorem weightOneModularForm_coeff {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hslash : WeightOneSlashLaws N ζ) (a b : Fin N) (n : ℕ) :
    (qExpansion (N : ℝ) (weightOneModularForm hN hζ hslash a b)).coeff n =
      weightOneIntegralCoeff N ζ a b n := by
  exact (ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast hN)
    (nat_mem_strictPeriods_Gamma N) (hasSum_weightOneQSeries hN hζ a b) n).symm

/-- The coefficients uniquely determine any genuine full-level realization. -/
theorem eq_weightOneQSeries_of_coeff {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N)
    (E : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 1)
    (hE : ∀ n, (qExpansion (N : ℝ) E).coeff n = weightOneIntegralCoeff N ζ a b n) :
    (E : ℍ → ℂ) = weightOneQSeries N ζ a b := by
  letI : NeZero N := ⟨hN.ne'⟩
  funext τ
  have hs := hasSum_qExpansion (by exact_mod_cast hN)
    (SlashInvariantFormClass.periodic_comp_ofComplex E (nat_mem_strictPeriods_Gamma N))
    (ModularFormClass.holo E) (ModularFormClass.bdd_at_infty E) τ
  simp_rw [hE] at hs
  exact hs.unique (hasSum_weightOneQSeries hN hζ a b τ)

theorem fullLevelEisensteinRealization24_of_slash_and_span
    (hslash : FullLevelWeightOneSlash24) (hspan : FullLevelWeightOneQSeriesSpan24) :
    FullLevelEisensteinRealization24 := by
  intro N hN h24
  let ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  let E := weightOneModularForm hN hζ (hslash N hN h24 ζ hζ)
  refine ⟨ζ, hζ, E, fun a b n => weightOneModularForm_coeff hN hζ _ a b n, ?_⟩
  exact hspan N hN h24 ζ hζ

theorem qExpPrinciple24_two_of_slash_and_span
    (hslash : FullLevelWeightOneSlash24) (hspan : FullLevelWeightOneQSeriesSpan24) :
    QExpPrinciple24 2 :=
  qExpPrinciple24_two_of_eisensteinRealization
    (fullLevelEisensteinRealization24_of_slash_and_span hslash hspan)

theorem qExpPrinciple24Away_two_of_slash_and_span
    (hslash : FullLevelWeightOneSlash24) (hspan : FullLevelWeightOneQSeriesSpan24) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_eisensteinRealization
    (fullLevelEisensteinRealization24_of_slash_and_span hslash hspan)

end VOA.Classification.COne.SSHecke
