import VOA.Classification.COne.QExpWeightTwoFiniteJets
import VOA.Classification.COne.CyclotomicSpanningSturm

/-!
# Full-level jet separation

The norm to level one proves an explicit (nonoptimal) width-N cutoff.
This discharges separation, independently of the weight-one slash laws.
The remaining finite-jet input is exactly product-column containment.
-/

open Complex Filter Topology
open UpperHalfPlane (qExpansion hasSum_qExpansion)
open scoped MatrixGroups ModularForm Manifold UpperHalfPlane

set_option maxSynthPendingDepth 3

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- A convergent exponential expansion with B zero initial coefficients decays
at the corresponding rate. This lemma does not assume modularity. -/
theorem norm_le_of_exponential_coeff_lt {p : ℝ} (hp : 0 < p)
    (f : ℍ → ℂ) (c : ℕ → ℂ)
    (hasSum_exp : ∀ τ : ℍ,
      HasSum (fun n : ℕ => c n * cexp (2 * p * I * n * τ)) (f τ))
    (B : ℕ) (hc : ∀ n < B, c n = 0) :
    ∃ K : ℝ, ∀ τ : ℍ, 1 ≤ τ.im →
      ‖f τ‖ ≤ K * Real.exp (-(2 * p * B * τ.im)) := by
  -- `|a_n| e^{-π n} ≤ K₀` from convergence at `τ₀ = i/2`
  have h0 : 0 < (I / 2 : ℂ).im := by simp
  have hs := (hasSum_exp ⟨I / 2, h0⟩).summable
  have hterm : ∀ n : ℕ, ‖c n * cexp (2 * p * I * n * (I / 2))‖ =
      ‖c n‖ * Real.exp (-(p * n)) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have : (2 * (p : ℂ) * I * n * (I / 2)) = ((-(p * n) : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [this, Complex.ofReal_re]
  obtain ⟨K₀, hK₀⟩ := (hs.tendsto_atTop_zero.norm).bddAbove_range
  have hK₀' : ∀ n, ‖c n‖ * Real.exp (-(p * n)) ≤ K₀ := fun n => by
    rw [← hterm]; exact hK₀ ⟨n, rfl⟩
  have hK₀0 : 0 ≤ K₀ := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (hK₀' 0)
  have hr0 : 0 ≤ Real.exp (-p) := (Real.exp_pos _).le
  have hr1 : Real.exp (-p) < 1 := Real.exp_lt_one_iff.2 (by linarith [hp])
  refine ⟨K₀ * Real.exp (2 * p * B) * (1 - Real.exp (-p))⁻¹, fun τ hτ => ?_⟩
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (K₀ * Real.exp (2 * p * B) * Real.exp (-(2 * p * B * τ.im)))
  have hfin : K₀ * Real.exp (2 * p * B) * Real.exp (-(2 * p * B * τ.im)) *
      (1 - Real.exp (-p))⁻¹ = K₀ * Real.exp (2 * p * B) *
      (1 - Real.exp (-p))⁻¹ * Real.exp (-(2 * p * B * τ.im)) := by ring
  rw [← hfin]
  refine (hasSum_exp τ).norm_le_of_bounded hg fun n => ?_
  by_cases hn : n < B
  · rw [hc n hn, zero_mul, norm_zero]
    positivity
  · push Not at hn
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * (p : ℂ) * I * n * τ).re = -(2 * p * n * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp : Real.exp (p * n) * Real.exp (-(2 * p * n * τ.im)) ≤
        Real.exp (2 * p * B) * Real.exp (-(2 * p * B * τ.im)) *
          Real.exp (-p) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hnB : (B : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.2 hnB))
        (sub_nonneg.2 hτ)]
    have h1 : Real.exp (-(p * n)) * Real.exp (p * n) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc ‖c n‖ * Real.exp (-(2 * p * n * τ.im))
        = (‖c n‖ * Real.exp (-(p * n))) *
          (Real.exp (p * n) * Real.exp (-(2 * p * n * τ.im))) := by
          linear_combination (-(‖c n‖ *
            Real.exp (-(2 * p * n * τ.im)))) * h1
      _ ≤ K₀ * (Real.exp (2 * p * B) * Real.exp (-(2 * p * B * τ.im)) *
          Real.exp (-p) ^ n) :=
          mul_le_mul (hK₀' n) hexp (by positivity) hK₀0
      _ = K₀ * Real.exp (2 * p * B) * Real.exp (-(2 * p * B * τ.im)) *
          Real.exp (-p) ^ n := by ring

/-- The full-level index used by Mathlib's norm construction. -/
def fullLevelIndex (N : ℕ) : ℕ :=
  Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)

/-- Width-N cutoff. The factor N compensates for the width at infinity. -/
def fullLevelSturmBound (N : ℕ) (k : ℤ) : ℕ :=
  N * ((k * (fullLevelIndex N : ℤ)).toNat / 12 + 1)

theorem qParam_nat_pow_exp (N : ℕ) (τ : ℍ) (n : ℕ) :
    Function.Periodic.qParam (N : ℝ) τ ^ n =
      cexp (2 * (Real.pi / (N : ℝ)) * I * n * τ) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Vanishing width-N coefficients give a level-one exponential decay rate. -/
theorem norm_le_of_coeff_lt_Gamma {N : ℕ} (hN : 0 < N) {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k)
    (B : ℕ) (hc : ∀ n < N * B, (qExpansion (N : ℝ) F).coeff n = 0) :
    ∃ K : ℝ, ∀ τ : ℍ, 1 ≤ τ.im →
      ‖F τ‖ ≤ K * Real.exp (-(2 * Real.pi * B * τ.im)) := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs (τ : ℍ) : HasSum
      (fun n : ℕ => (qExpansion (N : ℝ) F).coeff n *
        cexp (2 * (Real.pi / (N : ℝ)) * I * n * τ)) (F τ) := by
    simpa only [smul_eq_mul, qParam_nat_pow_exp N] using
      hasSum_qExpansion hNR
        (SlashInvariantFormClass.periodic_comp_ofComplex F (nat_mem_strictPeriods_Gamma N))
        (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
  obtain ⟨K, hK⟩ := norm_le_of_exponential_coeff_lt
    (p := Real.pi / (N : ℝ)) (div_pos Real.pi_pos hNR)
    (fun τ : ℍ => F τ) (fun n : ℕ => (qExpansion (N : ℝ) F).coeff n)
    (by simpa only [Complex.ofReal_div] using hs) (N * B) hc
  refine ⟨K, fun τ hτ => ?_⟩
  have he : 2 * (Real.pi / (N : ℝ)) * (N * B : ℕ) * τ.im =
      2 * Real.pi * B * τ.im := by
    push_cast
    field_simp
  simpa only [he] using hK τ hτ

/-- A full-level modular form with zero coefficients below the cutoff is zero. -/
theorem eq_zero_of_coeff_lt_Gamma {N : ℕ} [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k)
    (hc : ∀ n < fullLevelSturmBound N k, (qExpansion (N : ℝ) F).coeff n = 0) : F = 0 := by
  classical
  set B := (k * (fullLevelIndex N : ℤ)).toNat / 12 + 1
  set G := ModularForm.norm 𝒮ℒ F
  choose M A hMA using quotientFunc_bounded F
  obtain ⟨K, hK⟩ := norm_le_of_coeff_lt_Gamma (Nat.pos_of_ne_zero (NeZero.ne N)) F B hc
  set q₀ : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ :=
    ⟦(1 : 𝒮ℒ)⟧
  letI := Fintype.ofFinite
    (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  set P := ∏ q ∈ Finset.univ.erase q₀, M q
  set T := max 1 (∑ q, |A q|)
  have hG : ∀ τ : ℍ, T ≤ τ.im →
      ‖G τ‖ ≤ (K * P) * Real.exp (-(2 * Real.pi * B * τ.im)) := by
    intro τ hτ
    have hτ1 : 1 ≤ τ.im := (le_max_left _ _).trans hτ
    have hAq : ∀ q, A q ≤ τ.im := fun q =>
      (le_abs_self _).trans ((Finset.single_le_sum (fun q _ => abs_nonneg (A q))
        (Finset.mem_univ q)).trans ((le_max_right _ _).trans hτ))
    rw [ModularForm.coe_norm, Finset.prod_apply, norm_prod,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀)]
    have hq₀ : SlashInvariantForm.quotientFunc F q₀ τ = F τ := by simp [q₀]
    rw [hq₀]
    have hP : ∏ q ∈ Finset.univ.erase q₀, ‖SlashInvariantForm.quotientFunc F q τ‖ ≤ P :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun q _ => hMA q τ (hAq q))
    calc
      _ ≤ (K * Real.exp (-(2 * Real.pi * B * τ.im))) * P :=
        mul_le_mul (hK τ hτ1) hP
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) ((norm_nonneg _).trans (hK τ hτ1))
      _ = _ := by ring
  have hcoeff : ∀ n < B, (qExpansion 1 G).coeff n = 0 :=
    fun n hn => coeff_eq_zero_of_decay G B hG n hn
  have hord : (B : ℕ∞) ≤ (qExpansion 1 G).order := PowerSeries.nat_le_order _ _ hcoeff
  have hG0 : G = 0 := by
    refine ModularForm.sturm_bound_levelOne (lt_of_lt_of_le ?_ hord)
    change (((k * (fullLevelIndex N : ℤ)).toNat / 12 : ℕ) : ℕ∞) < (B : ℕ∞)
    exact_mod_cast Nat.lt_succ_self ((k * (fullLevelIndex N : ℤ)).toNat / 12)
  exact DFunLike.coe_injective ((ModularForm.norm_eq_zero_iff 𝒮ℒ F).mp hG0)

/-- The first B coefficients as a complex linear map. -/
def fullLevelCoeffMap (N : ℕ) (hN : 0 < N) (k : ℤ) (B : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      (Fin B → ℂ) where
  toFun F n := (qExpansion (N : ℝ) F).coeff n
  map_add' F G := by
    funext n
    change (qExpansion (N : ℝ) (F + G)).coeff n = _
    rw [ModularForm.qExpansion_add (by exact_mod_cast hN) (nat_mem_strictPeriods_Gamma N) F G,
      map_add]
    rfl
  map_smul' c F := by
    funext n
    change (qExpansion (N : ℝ) (c • F)).coeff n = _
    rw [ModularForm.qExpansion_smul (by exact_mod_cast hN) (nat_mem_strictPeriods_Gamma N) c F,
      PowerSeries.coeff_smul]
    rfl

/-- Truncation at the norm bound is injective. -/
theorem fullLevelCoeffMap_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (fullLevelCoeffMap N (Nat.pos_of_ne_zero (NeZero.ne N)) k
      (fullLevelSturmBound N k)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  exact eq_zero_of_coeff_lt_Gamma F (fun n hn => congrFun hF ⟨n, hn⟩)

/-- Finite dimensionality at every positive full level and every integral weight. -/
theorem finiteDimensional_Gamma (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ
      (ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k) :=
  Module.Finite.of_injective _ (fullLevelCoeffMap_injective N k)

/-- The norm bound also bounds the dimension, but need not equal it. -/
theorem finrank_Gamma_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ
      (ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k) ≤
        fullLevelSturmBound N k := by
  simpa using LinearMap.finrank_le_finrank_of_injective (fullLevelCoeffMap_injective N k)

/-- The concrete cutoff separates all full-level weight-two forms. -/
theorem fullLevelWeightTwoJetSeparation_sturm {N : ℕ} (hN : 0 < N) :
    FullLevelWeightTwoJetSeparation N (fullLevelSturmBound N 2) := by
  letI : NeZero N := ⟨hN.ne'⟩
  intro F G h
  apply sub_eq_zero.mp
  apply eq_zero_of_coeff_lt_Gamma (F - G)
  intro n hn
  change (qExpansion (N : ℝ) (⇑F - ⇑G)).coeff n = 0
  rw [ModularForm.qExpansion_sub (by exact_mod_cast hN)
    (nat_mem_strictPeriods_Gamma N) F G, map_sub, h n hn, sub_self]

/-- The rank assertion at the proved cutoff; this remains an unproved
classical input. No unknown separation certificate is included. -/
def FullLevelWeightTwoSturmMatching24 : Prop :=
  ∀ N : ℕ, 0 < N → 24 ∣ N → ∀ ζ : ℂ, IsPrimitiveRoot ζ N →
    WeightTwoProductJetMatching N ζ (fullLevelSturmBound N 2)

theorem fullLevelWeightTwoFiniteJetInput24_of_sturmMatching
    (h : FullLevelWeightTwoSturmMatching24) : FullLevelWeightTwoFiniteJetInput24 := by
  intro N hN h24 ζ hζ
  exact ⟨fullLevelSturmBound N 2, fullLevelWeightTwoJetSeparation_sturm hN,
    h N hN h24 ζ hζ⟩

/-- Conversely, a product identity gives matching at every finite cutoff. -/
theorem fullLevelWeightTwoSturmMatching24_of_slash_and_span
    (hslash : FullLevelWeightOneSlash24) (hspan : FullLevelWeightOneQSeriesSpan24) :
    FullLevelWeightTwoSturmMatching24 := by
  intro N hN h24 ζ hζ F
  obtain ⟨d, a, b, a', b', c, hc⟩ := hspan N hN h24 ζ hζ F
  let E := weightOneModularForm hN hζ (hslash N hN h24 ζ hζ)
  have he := qExpansion_eq_sum_products hN F
    (fun i => E (a i) (b i)) (fun i => E (a' i) (b' i)) c hc
  refine ⟨d, a, b, a', b', c, fun n _ => ?_⟩
  have hec := congrArg (fun p : PowerSeries ℂ => p.coeff n) he
  simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_mul,
    E, weightOneModularForm_coeff, weightTwoProductCoeff] using hec

/-- Under slash laws, the remaining finite rank assertion is exactly the
original analytic product span, rather than a weaker conclusion. -/
theorem fullLevelWeightTwoSturmMatching24_iff_span
    (hslash : FullLevelWeightOneSlash24) :
    FullLevelWeightTwoSturmMatching24 ↔ FullLevelWeightOneQSeriesSpan24 := by
  exact ⟨fun h => fullLevelWeightOneQSeriesSpan24_of_finiteJets hslash
      (fullLevelWeightTwoFiniteJetInput24_of_sturmMatching h),
    fullLevelWeightTwoSturmMatching24_of_slash_and_span hslash⟩

theorem qExpPrinciple24Away_two_of_slash_and_sturmMatching
    (hslash : FullLevelWeightOneSlash24) (hmatch : FullLevelWeightTwoSturmMatching24) :
    QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_slash_and_finiteJets hslash
    (fullLevelWeightTwoFiniteJetInput24_of_sturmMatching hmatch)

end VOA.Classification.COne.SSHecke
