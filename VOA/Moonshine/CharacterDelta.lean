/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.CharacterSeries
import VOA.Moonshine.CharacterBridge
import VOA.LatticesAndCodes.Leech.RepCount
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Jacobi's product for `Δ` and `Θ_Λ = E₄³ - 720Δ`  (Moonshine step M7d, part 2)

Two of the three identities of `CharacterSeries.lean`, proved:

* `deltaProductIdentity : DeltaProductIdentity` — the formal discriminant
  `deltaSeries = (E₄³ - E₆²)/1728` of `Modularity/JFunction.lean` satisfies
  `deltaSeries = q ∏(1-qⁿ)^{24}`, i.e. `(Δ/q) · ∏(1-qⁿ)^{-24} = 1`.
  Route: `qExpansion 1 Δ = deltaSeries` (Mathlib's `discriminant_eq_E₄_cube_sub_E₆_sq` and the
  `q`-expansions of `E₄`, `E₆`), and `Δ(z) = q ∏'(1-q^{n+1})^{24}` (Mathlib's
  `discriminant_eq_q_prod`) evaluated against the formal product by the dominated-convergence
  bridge `QBridge.tendsto_ev_one_sub_pow`; uniqueness of `q`-expansions
  (`ModularFormClass.qExpansion_coeff_unique`) identifies the coefficients.
* `leechThetaIdentity : LeechThetaIdentity` — `Θ_Λ = E₄³ - 720Δ` as formal `q`-series.
  Route: `θ_Λ` is a level-one weight-12 modular form (vendored `thetaModularForm`), every such
  form has `q`-expansion `c₀ E₄³ + ((c₁ - 720 c₀)/1728)(E₄³ - E₆²)`
  (`qExpansion_weight_twelve`, from `M₁₂ = ⟨E₄³, E₆²⟩`), and for `Λ`, `c₀ = 1`, `c₁ = r_Λ(2) = 0`.

Consequences: `jShift_eq : q·j = E₄³ ∏(1-qⁿ)^{-24}` and
`leechTheta_mul_fock : Θ_Λ ∏(1-qⁿ)^{-24} = q·j - 720 q` (the character of `V_Λ` is `j - 720`,
read as `q⁻¹A = j - 720`), and `sectorSeries_eq_JShift_of_levelTwo : LevelTwoIdentity →
sectorSeries = JShift`.

## Status
All declarations proved, no `sorry`, no new axioms.
-/

set_option linter.style.longLine false

open scoped MatrixGroups

namespace VOA

namespace Moonshine

open PowerSeries UpperHalfPlane ModularForm EisensteinSeries Filter Topology QBridge

/-! ## §1  `q`-expansions of `E₄`, `E₆`, `Δ` -/

theorem qExpansion_E₄ : qExpansion 1 (E₄ : ℍ → ℂ) = E4Series := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, E4Series, coeff_mk]
  split_ifs with h
  · rfl
  · rw [lambertCoeff_eq_sigma]
    norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

theorem qExpansion_E₆ : qExpansion 1 (E₆ : ℍ → ℂ) = E6Series := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, E6Series, coeff_mk]
  split_ifs with h
  · rfl
  · rw [lambertCoeff_eq_sigma]
    norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

/-- `E₄³ - E₆²` (`= 1728 Δ`) as a level-one modular form of weight 12. -/
noncomputable def e46Form : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

theorem e46Form_apply (z : ℍ) : e46Form z = E₄ z ^ 3 - E₆ z ^ 2 := by
  simp only [e46Form, ModularForm.coe_sub, ModularForm.coe_mcast, Pi.sub_apply]
  rw [ModularForm.coe_pow, ModularForm.coe_pow]; rfl

theorem qExpansion_e46Form : qExpansion 1 e46Form = E4Series ^ 3 - E6Series ^ 2 := by
  rw [e46Form, ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
  simp only [ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄, qExpansion_E₆]

theorem coe_discriminant_eq :
    (ModularForm.discriminant : ℍ → ℂ) = (1728 : ℂ)⁻¹ • (e46Form : ℍ → ℂ) := by
  funext z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, Pi.smul_apply, e46Form_apply, smul_eq_mul]
  ring

/-- **`qExpansion Δ = deltaSeries`**: Mathlib's analytic discriminant has the formal
`q`-expansion `(E₄³ - E₆²)/1728` of `Modularity/JFunction.lean`. -/
theorem qExpansion_discriminant :
    qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = deltaSeries := by
  rw [coe_discriminant_eq, UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero e46Form one_pos one_mem_strictPeriods_SL),
    qExpansion_e46Form, deltaSeries]

/-! ## §2  The formal product `∏(1-qⁿ)^{24}` and Jacobi's formula -/

open scoped PowerSeries.WithPiTopology

/-- The formal product `D = ∏_{n≥1} (1-qⁿ)^{24}`. -/
noncomputable def deltaProd : PowerSeries ℂ := (∏' i : ℕ, ((1 : PowerSeries ℂ) - X ^ (i + 1))) ^ 24

theorem hasProd_deltaProd :
    HasProd (fun i : ℕ => ((1 : PowerSeries ℂ) - X ^ (i + 1)) ^ 24) deltaProd :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow (R := ℂ)).hasProd.pow 24

theorem coeff_deltaProd (n : ℕ) :
    coeff n deltaProd = coeff n (∏ i ∈ Finset.range n, ((1 : PowerSeries ℂ) - X ^ (i + 1)) ^ 24) :=
  coeff_of_hasProd hasProd_deltaProd
    (fun _ => dvd_sub_one_pow (dvd_one_sub_X_pow_sub_one ℂ le_rfl) 24) n

/-- The analytic evaluation: for `‖q‖ < 1`, `Σ [qⁿ]D · qⁿ = ∏' (1 - q^{n+1})^{24}`. -/
theorem hasSum_deltaProd {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => coeff n deltaProd * q ^ n) (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) := by
  obtain ⟨hs, ht⟩ := tendsto_ev_one_sub_pow (e := fun i => i + 1) (fun i => le_rfl) 24
    coeff_deltaProd hq
  have hP := ((ModularForm.multipliable_one_sub_pow hq).hasProd.pow 24)
  have hP' : HasProd (fun n : ℕ => (1 - q ^ (n + 1)) ^ 24) (∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) := by
    convert hP using 1
    exact hP.tprod_eq
  have heq : ev deltaProd q = ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 :=
    tendsto_nhds_unique ht hP'.tendsto_prod_nat
  rw [← heq]
  exact hs.of_norm.hasSum

/-- `q ∏'(1-q^{n+1})^{24} = Σ [qⁿ](X·D) qⁿ`. -/
theorem hasSum_X_mul_deltaProd {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => coeff n (X * deltaProd) * q ^ n) (q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, coeff_zero_X_mul, zero_mul, sub_zero,
    coeff_succ_X_mul]
  have := (hasSum_deltaProd hq).mul_left q
  convert this using 2 with n
  ring

/-- **Jacobi's product formula, formally**: `Δ = q ∏(1-qⁿ)^{24}` for the formal discriminant
`(E₄³ - E₆²)/1728`. -/
theorem deltaSeries_eq_X_mul_deltaProd : deltaSeries = X * deltaProd := by
  ext m
  rw [← qExpansion_discriminant, ← CuspForm.coe_discriminant]
  refine (ModularFormClass.qExpansion_coeff_unique (h := 1) (Γ := 𝒮ℒ) one_pos
    one_mem_strictPeriods_SL (f := CuspForm.discriminant)
    (c := fun m => coeff m (X * deltaProd)) (fun τ => ?_) m).symm
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have h := hasSum_X_mul_deltaProd hq
  rw [CuspForm.coe_discriminant, discriminant_eq_q_prod]
  simpa only [smul_eq_mul] using h

theorem deltaOverQ_eq_deltaProd : deltaOverQ = deltaProd := by
  ext n
  have h := congrArg (coeff (n + 1)) (deltaSeries_eq.symm.trans deltaSeries_eq_X_mul_deltaProd)
  rwa [coeff_succ_X_mul, coeff_succ_X_mul] at h

/-- **`DeltaProductIdentity`**: `(Δ/q) · ∏(1-qⁿ)^{-24} = 1`. -/
theorem deltaProductIdentity : DeltaProductIdentity := by
  unfold DeltaProductIdentity
  rw [deltaOverQ_eq_deltaProd]
  have h := hasProd_deltaProd.mul (LatGen.hasProd_fockGenFun 24)
  have h1 : (fun i : ℕ => ((1 : PowerSeries ℂ) - X ^ (i + 1)) ^ 24
      * ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ 24) = fun _ => 1 := by
    funext i
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ (by simp), one_pow]
  rw [h1] at h
  exact (tendsto_nhds_unique h.tendsto_prod_nat (hasProd_one.tendsto_prod_nat)).symm ▸ rfl

/-! ## §3  Level-one weight-12 forms and `Θ_Λ` -/

/-- Every level-one modular form of weight `12` has `q`-expansion
`c₀ E₄³ + ((c₁ - 720 c₀)/1728)(E₄³ - E₆²)`. -/
theorem qExpansion_weight_twelve (f : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) :
    qExpansion 1 (f : ℍ → ℂ)
      = (qExpansion 1 (f : ℍ → ℂ)).coeff 0 • E4Series ^ 3
        + (((qExpansion 1 (f : ℍ → ℂ)).coeff 1 - 720 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0) / 1728)
          • (E4Series ^ 3 - E6Series ^ 2) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (eisBasisFun 12)) := by
    rw [span_eisBasisFun]
    trivial
  have c4 : E4Series.coeff 0 = 1 ∧ E4Series.coeff 1 = 240 := by
    rw [← qExpansion_E₄]; exact ⟨E₄_coeff_zero, E₄_coeff_one⟩
  have c6 : E6Series.coeff 0 = 1 ∧ E6Series.coeff 1 = -504 := by
    rw [← qExpansion_E₆]; exact ⟨E₆_coeff_zero, E₆_coeff_one⟩
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, rfl⟩ := hg
    have hq : qExpansion 1 (eisBasisFun 12 p : ℍ → ℂ)
        = E4Series ^ (p : ℕ × ℕ).1 * E6Series ^ (p : ℕ × ℕ).2 := by
      rw [eisBasisFun, ModularForm.qExpansion_mcast, qExpansion_eisMonomial, qExpansion_E₄,
        qExpansion_E₆]
    rw [hq]
    rcases wtIdx_twelve p.2 with hp | hp
    · rw [hp]
      simp only [pow_zero, mul_one]
      rw [show E4Series ^ 3 = E4Series * E4Series * E4Series by ring]
      rw [coeff_zero_mul, coeff_zero_mul, coeff_one_mul, coeff_one_mul, coeff_zero_mul,
        c4.1, c4.2]
      ext n
      simp only [map_add, map_smul, smul_eq_mul, map_sub]
      ring
    · rw [hp]
      simp only [pow_zero, one_mul]
      rw [show E6Series ^ 2 = E6Series * E6Series by ring, coeff_zero_mul, coeff_one_mul,
        c6.1, c6.2]
      ext n
      simp only [map_add, map_smul, smul_eq_mul, map_sub]
      ring
  | zero =>
    have h0 : qExpansion 1 ((0 : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ) = 0 := by
      have h := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (0 : ℂ)
        (0 : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ))
      simpa using h
    rw [h0]
    simp
  | add x y _ _ hx hy =>
    have hadd : qExpansion 1 ((x + y : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ)
        = qExpansion 1 (x : ℍ → ℂ) + qExpansion 1 (y : ℍ → ℂ) :=
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL x y
    rw [hadd]
    conv_lhs => rw [hx, hy]
    ext n
    simp only [map_add, coeff_smul, smul_eq_mul, map_sub]
    ring
  | smul a x _ hx =>
    have hsmul : qExpansion 1 ((a • x : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ)
        = a • qExpansion 1 (x : ℍ → ℂ) :=
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL a x
    rw [hsmul]
    conv_lhs => rw [hx]
    ext n
    simp only [map_add, smul_eq_mul, map_sub, map_smul]
    ring

theorem leechThetaSeries_coeff (n : ℕ) :
    coeff n leechThetaSeries = (Leech.lattice.repCount (2 * (n : ℤ)) : ℂ) := by
  rw [leechThetaSeries, coeff_mk, LatGen.normEq,
    ← Set.ncard_eq_toFinset_card _ (LatGen.normEq_finite leech leech_posDef _)]
  rfl

/-- **`LeechThetaIdentity`: `Θ_Λ = E₄³ - 720Δ`** as formal `q`-series. -/
theorem leechThetaIdentity : LeechThetaIdentity := by
  have hw : ((Leech.lattice.rank / 2 : ℕ) : ℤ) = ((12 : ℕ) : ℤ) := by rw [Leech.lattice_rank]
  set f := Leech.lattice.thetaModularForm Leech.lattice_isPosDef Leech.lattice_isEven
    Leech.lattice_isUnimodular with hf
  set g : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ) := ModularForm.mcast hw f with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
    rw [hg, ModularForm.qExpansion_mcast]
  have hcoeff : ∀ n, (qExpansion 1 (f : ℍ → ℂ)).coeff n = coeff n leechThetaSeries := by
    intro n
    rw [leechThetaSeries_coeff, hf, IntegralLattice.coeff_qExpansion_thetaModularForm]
  have hser : qExpansion 1 (f : ℍ → ℂ) = leechThetaSeries := by ext n; exact hcoeff n
  have h := qExpansion_weight_twelve g
  rw [hqg, hser] at h
  have c0 : coeff 0 leechThetaSeries = 1 := by
    rw [leechThetaSeries_coeff]
    have := IntegralLattice.repCount_zero (Γ := Leech.lattice) Leech.lattice_isPosDef
    simp [this]
  have c1 : coeff 1 leechThetaSeries = 0 := by
    rw [leechThetaSeries_coeff]
    have := Leech.lattice_repCount_two
    simp [this]
  rw [c0, c1] at h
  unfold LeechThetaIdentity
  rw [h, deltaSeries]
  ext n
  simp only [map_add, coeff_smul, smul_eq_mul, map_sub]
  ring

/-! ## §4  Consequences -/

/-- **`q·j = E₄³ · ∏(1-qⁿ)^{-24}`**. -/
theorem jShift_eq : jShift = E4Series ^ 3 * LatGen.fockGenFun 24 :=
  jShift_eq_of_deltaProduct deltaProductIdentity

/-- **The character of `V_Λ` is `j - 720`**: `Θ_Λ · ∏(1-qⁿ)^{-24} = q·j - 720 q`. -/
theorem leechTheta_mul_fock :
    leechThetaSeries * LatGen.fockGenFun 24 = jShift - (720 : ℂ) • X :=
  leechTheta_mul_fock_of deltaProductIdentity leechThetaIdentity

/-- The remaining reduction: the level-two identity alone implies `sectorSeries = q·J`. -/
theorem sectorSeries_eq_JShift_of_levelTwo (hL : LevelTwoIdentity) : sectorSeries = JShift :=
  sectorSeries_eq_JShift_of deltaProductIdentity leechThetaIdentity hL

end Moonshine

end VOA
