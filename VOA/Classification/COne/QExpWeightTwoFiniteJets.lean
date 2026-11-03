import VOA.Classification.COne.QExpWeightTwoRealization

/-!
# An exact finite-jet alternative to the product-spanning input

The cutoff must separate FULL-LEVEL weight-two forms: the proposed product
need not be Gamma1 invariant until its equality with the target is proved.
The matching condition is containment of the target's coefficient vectors
in the product-column space, not surjectivity onto all coefficient vectors.

`FullLevelWeightTwoFiniteJetInput24` is true by a full-level Sturm bound and
the classical spanning theorem (Khuri-Makdisi, Theorems 3.5 and 5.1,
https://arxiv.org/html/0903.1439v6). Neither its cutoff nor its uniform
rank assertion is proved here. The implication from such a certificate is
proved, with the coefficient matrix given by explicit finite convolutions.
-/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem Gamma_le_Gamma1_GL (N : ℕ) :
    (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) ≤
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) := by
  apply Subgroup.map_mono
  intro γ hγ
  simp only [CongruenceSubgroup.Gamma_mem] at hγ
  simp only [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

/-- Restriction preserves the underlying function and therefore every expansion width. -/
def restrictGamma1ToGamma {N : ℕ} (hN : 0 < N) {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k := by
  letI : NeZero N := ⟨hN.ne'⟩
  exact {
    toFun := F
    slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (Gamma_le_Gamma1_GL N hγ)
    holo' := ModularFormClass.holo F
    bdd_at_cusps' := fun hc => by
      apply ModularFormClass.bdd_at_cusps F
      rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢ }

/-- A candidate full-level Sturm cutoff, expressed without a dimension formula. -/
def FullLevelWeightTwoJetSeparation (N B : ℕ) : Prop :=
  ∀ F G : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2,
    (∀ n < B, (qExpansion (N : ℝ) F).coeff n = (qExpansion (N : ℝ) G).coeff n) → F = G

/-- Explicit entries of the product coefficient matrix. -/
def weightTwoProductCoeff (N : ℕ) (ζ : ℂ) (a b a' b' : Fin N) (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal n,
    weightOneIntegralCoeff N ζ a b p.1 * weightOneIntegralCoeff N ζ a' b' p.2

theorem weightOneModularForm_mul_coeff {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hslash : WeightOneSlashLaws N ζ)
    (a b a' b' : Fin N) (n : ℕ) :
    (qExpansion (N : ℝ) ((weightOneModularForm hN hζ hslash a b).mul
      (weightOneModularForm hN hζ hslash a' b'))).coeff n =
      weightTwoProductCoeff N ζ a b a' b' n := by
  rw [ModularForm.qExpansion_mul (by exact_mod_cast hN) (nat_mem_strictPeriods_Gamma N),
    PowerSeries.coeff_mul]
  simp only [weightOneModularForm_coeff, weightTwoProductCoeff]

/-- Finite linear systems for all Gamma1 target jets. No assertion that the
product columns span the entire ambient space of B-tuples is made. -/
def WeightTwoProductJetMatching (N : ℕ) (ζ : ℂ) (B : ℕ) : Prop :=
  ∀ F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2,
    ∃ (d : ℕ) (a b a' b' : Fin d → Fin N) (c : Fin d → ℂ),
      ∀ n < B, (qExpansion (N : ℝ) F).coeff n =
        ∑ i, c i * weightTwoProductCoeff N ζ (a i) (b i) (a' i) (b' i) n

/-- Missing full-level separation plus uniform coefficient-rank input.
The existence of B is part of the assertion, so a vacuous cutoff implication
cannot discharge it. This is an alternative to the analytic spanning input. -/
def FullLevelWeightTwoFiniteJetInput24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → ∀ ζ : ℂ, IsPrimitiveRoot ζ N →
    ∃ B : ℕ, FullLevelWeightTwoJetSeparation N B ∧ WeightTwoProductJetMatching N ζ B

/-- Finite coefficient matching becomes a genuine product identity once the
factors are modular and the cutoff separates full-level weight-two forms. -/
theorem weightTwoProductIdentity_of_finiteJet {N B : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hslash : WeightOneSlashLaws N ζ)
    (hsep : FullLevelWeightTwoJetSeparation N B)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {d : ℕ} (a b a' b' : Fin d → Fin N) (c : Fin d → ℂ)
    (hjet : ∀ n < B, (qExpansion (N : ℝ) F).coeff n =
      ∑ i, c i * weightTwoProductCoeff N ζ (a i) (b i) (a' i) (b' i) n) :
    ∀ τ : ℍ, F τ = ∑ i, c i *
      (weightOneQSeries N ζ (a i) (b i) τ * weightOneQSeries N ζ (a' i) (b' i) τ) := by
  let E := weightOneModularForm hN hζ hslash
  let H : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2 :=
    ∑ i, c i • (E (a i) (b i)).mul (E (a' i) (b' i))
  have heq : restrictGamma1ToGamma hN F = H := by
    apply hsep
    intro n hn
    change (qExpansion (N : ℝ) F).coeff n = (qExpansion (N : ℝ) H).coeff n
    rw [hjet n hn]
    have hs : qExpansion (N : ℝ) H = ∑ i, c i •
        qExpansion (N : ℝ) ((E (a i) (b i)).mul (E (a' i) (b' i))) :=
      qExpansion_sum_Gamma hN c
        (fun i => (E (a i) (b i)).mul (E (a' i) (b' i)))
    have hc := congrArg (fun p : PowerSeries ℂ => p.coeff n) hs
    simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, E,
      weightOneModularForm_mul_coeff] using hc.symm
  intro τ
  have h := congrArg (fun G : ModularForm
    (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) 2 => G τ) heq
  change F τ = (ModularForm.coeHom H) τ at h
  simpa [H, E, map_sum, ModularForm.coeHom, ModularForm.coe_smul, ModularForm.coe_mul,
    Finset.sum_apply, smul_eq_mul, weightOneModularForm] using h

theorem fullLevelWeightOneQSeriesSpan24_of_finiteJets
    (hslash : FullLevelWeightOneSlash24) (hjet : FullLevelWeightTwoFiniteJetInput24) :
    FullLevelWeightOneQSeriesSpan24 := by
  intro N hN h24 ζ hζ F
  obtain ⟨B, hsep, hmatch⟩ := hjet N hN h24 ζ hζ
  obtain ⟨d, a, b, a', b', c, hc⟩ := hmatch F
  exact ⟨d, a, b, a', b', c,
    weightTwoProductIdentity_of_finiteJet hN hζ (hslash N hN h24 ζ hζ) hsep F a b a' b' c hc⟩

theorem fullLevelEisensteinRealization24_of_slash_and_finiteJets
    (hslash : FullLevelWeightOneSlash24) (hjet : FullLevelWeightTwoFiniteJetInput24) :
    FullLevelEisensteinRealization24 :=
  fullLevelEisensteinRealization24_of_slash_and_span hslash
    (fullLevelWeightOneQSeriesSpan24_of_finiteJets hslash hjet)

theorem qExpPrinciple24Away_two_of_slash_and_finiteJets
    (hslash : FullLevelWeightOneSlash24) (hjet : FullLevelWeightTwoFiniteJetInput24) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_eisensteinRealization
    (fullLevelEisensteinRealization24_of_slash_and_finiteJets hslash hjet)

end VOA.Classification.COne.SSHecke
