/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LogRemovalAdmissible

/-!
# A uniform bound on the log-degree of products at the iterate point

For fixed irreducible modules and intertwiners `𝒴₁, 𝒴₂` of a strongly rational `V`, the expansions
at the iterate point `u = z₁ − z₂ = 0` of **all** products `⟨f, 𝒴₁(w₁, 1+u)𝒴₂(w₂, 1)w₃⟩`
(homogeneous `wᵢ`, `f` supported at one weight) have log-degree `≤ K` for one `K`
(`logDeg_bounded_holds`, `coeffLogBounded_holds : StronglyRational W →
CoeffLogBounded W`).  Contrast `prod_frobenius_expansion_holds`, which bounds the log-degree of
each product separately.

**Proof.**  Huang's Prop. 1.1/2.1 at the iterate point (`HuangODEIterPoint.pt_mem`, already in
the library) says: for any `ℂ[x]`-module `NN` of power series containing the renormalized series
`(1 − x)^s QT` of the finitely many tuples of bounded levels, it contains those of all tuples.  We
take for `NN` the series `Z` whose analytic value `(1 + e^t)^{−c₀−1} Z((1 + e^t)⁻¹)` has
log-degree `≤ K` (`logModule K`); it is a `ℂ[x]`-module because a polynomial in
`x = (1 + e^t)⁻¹` is a convergent power series in `u = e^t` (`exists_subexp_of_mem_ratRing_zero`),
and multiplying by such does not raise the log-degree.  The base tuples span a finite-dimensional
space (`exists_finite_span_supported`), so one `K` works for all of them, and the renormalization
`(1 − x)^{−s} x^{−K'}` is `e^{−st}` times an integer power of `1 + e^t` — again log-free.

## Main results
* `LogDegLE` and its closure properties.
* `weightCompl`, `isCompl_weightCompl`, `weightProj`, `supportedAt_comp_weightProj`.
* `exists_finite_span_supported` (the base tuples, with supported functionals).
* `logModule` (a `ℂ[x]`-module), `logDeg_bounded_holds`, `coeffLogBounded_holds`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.LogRemovalBound

open VOA PowerSeries VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.LogRemovalSemisimple VOA.Huang.LogRemovalAdmissible
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEIterPoint VOA.Huang.HuangODEAlgebra
open VOA.Huang.FrobeniusLog (psEval)
open scoped BigOperators

universe u

/-! ## Functions of bounded log-degree -/

section LogDeg

/-- `F` has a log-expansion on the overlap domain, of log-degree `≤ K`. -/
def LogDegLE (K : ℕ) (F : ℂ → ℂ) : Prop :=
  HasLogExp overlapDomain F ∧ ∀ μ k, K < k → logCoeff overlapDomain F μ k = 0

theorem LogDegLE.mono {K K' : ℕ} {F : ℂ → ℂ} (h : LogDegLE K F) (hK : K ≤ K') :
    LogDegLE K' F :=
  ⟨h.1, fun μ k hk => h.2 μ k (by omega)⟩

theorem LogDegLE.congr {K : ℕ} {F G : ℂ → ℂ} (h : LogDegLE K F)
    (hFG : ∀ t ∈ overlapDomain, F t = G t) : LogDegLE K G :=
  ⟨hasLogExp_congr hFG h.1, fun μ k hk => by
    rw [← logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hFG h.1]
    exact h.2 μ k hk⟩

theorem logDegLE_zero (K : ℕ) : LogDegLE K (fun _ => 0) :=
  ⟨hasLogExp_zero, fun μ k _ =>
    logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty μ k⟩

theorem LogDegLE.add {K : ℕ} {F G : ℂ → ℂ} (hF : LogDegLE K F) (hG : LogDegLE K G) :
    LogDegLE K (F + G) :=
  ⟨hasLogExp_add hF.1 hG.1, fun μ k hk => by
    rw [logCoeff_add isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF.1 hG.1,
      hF.2 μ k hk, hG.2 μ k hk, add_zero]⟩

theorem LogDegLE.const_mul {K : ℕ} {F : ℂ → ℂ} (hF : LogDegLE K F) (a : ℂ) :
    LogDegLE K (fun t => a * F t) :=
  ⟨hasLogExp_smul a hF.1, fun μ k hk => by
    rw [logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty a hF.1,
      hF.2 μ k hk, mul_zero]⟩

theorem LogDegLE.psEval_mul {K : ℕ} {F : ℂ → ℂ} (hF : LogDegLE K F) {c : PowerSeries ℂ}
    (hc : c ∈ SubexpPS) : LogDegLE K (fun t => psEval c (Complex.exp t) * F t) :=
  ⟨hasLogExp_psEval_mul overlapDomain_subset hF.1 hc, fun μ k hk => by
    rw [logCoeff_psEval_mul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      hF.1 hc]
    simp [hF.2 _ k hk]⟩

theorem LogDegLE.exp_mul {K : ℕ} {F : ℂ → ℂ} (hF : LogDegLE K F) (ν : ℂ) :
    LogDegLE K (fun t => Complex.exp (ν * t) * F t) :=
  ⟨hasLogExp_exp_mul hF.1 ν, fun μ k hk => by
    have := logCoeff_exp_mul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      hF.1 ν (μ - ν) k
    rw [sub_add_cancel] at this
    rw [this, hF.2 _ k hk]⟩

/-- Every function with a log-expansion has bounded log-degree. -/
theorem exists_logDegLE {F : ℂ → ℂ} (hF : HasLogExp overlapDomain F) : ∃ K, LogDegLE K F := by
  obtain ⟨K, hK⟩ := logCoeff_eventually_zero isOpen_overlapDomain overlapDomain_subset
    overlapDomain_nonempty hF
  exact ⟨K, hF, fun μ k hk => hK μ k hk⟩

end LogDeg

/-! ## The canonical projection onto a weight space -/

section Proj

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The sum of all weight spaces other than `h`. -/
noncomputable def weightCompl (A : OrdVModule W M) (h : ℂ) : Submodule ℂ M :=
  ⨆ (α : ℂ) (_ : α ≠ h), A.weight α

theorem isCompl_weightCompl (A : OrdVModule W M) (h : ℂ) :
    IsCompl (A.weight h) (weightCompl A h) := by
  refine ⟨A.isInternal.submodule_iSupIndep h, ?_⟩
  rw [codisjoint_iff, weightCompl, ← iSup_split_single, A.isInternal.submodule_iSup_eq_top]

/-- The projection onto the weight space `h` along the other weight spaces. -/
noncomputable def weightProj (A : OrdVModule W M) (h : ℂ) : M →ₗ[ℂ] A.weight h :=
  Submodule.projectionOnto _ _ (isCompl_weightCompl A h)

theorem weightProj_apply_self (A : OrdVModule W M) (h : ℂ) (x : A.weight h) :
    weightProj A h x = x :=
  Submodule.projectionOnto_apply_left _ x

theorem supportedAt_comp_weightProj (A : OrdVModule W M) (h : ℂ)
    (g : Module.Dual ℂ (A.weight h)) : SupportedAt A (g ∘ₗ weightProj A h) h := by
  intro α hα x hx
  have hx' : x ∈ weightCompl A h := (le_iSup₂_of_le α hα le_rfl : A.weight α ≤ _) hx
  have := Submodule.projectionOnto_apply_right (isCompl_weightCompl A h) ⟨x, hx'⟩
  simp only [LinearMap.comp_apply, weightProj]
  rw [show (x : M) = ((⟨x, hx'⟩ : weightCompl A h) : M) from rfl, this, map_zero]

theorem domRestrict_comp_weightProj (A : OrdVModule W M) (h : ℂ) (f : M →ₗ[ℂ] ℂ) :
    f.domRestrict (A.weight h)
      = ((f.domRestrict (A.weight h)) ∘ₗ weightProj A h).domRestrict (A.weight h) := by
  ext x
  simp [weightProj_apply_self]

/-- A functional supported at a weight with zero weight space vanishes. -/
theorem eq_zero_of_supportedAt_bot {A : OrdVModule W M} {f : M →ₗ[ℂ] ℂ} {h : ℂ}
    (hf : SupportedAt A f h) (hbot : A.weight h = ⊥) : f = 0 := by
  ext x
  have hx : x ∈ ⨆ α, A.weight α := by rw [A.isInternal.submodule_iSup_eq_top]; trivial
  simp only [LinearMap.zero_apply]
  induction hx using Submodule.iSup_induction' with
  | mem α y hy =>
    by_cases hα : α = h
    · subst hα; rw [hbot] at hy; rw [(Submodule.mem_bot ℂ).mp hy, map_zero]
    · exact hf α hα y hy
  | zero => exact map_zero f
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]

end Proj

/-! ## The base tuples span a finite-dimensional space -/

section Base

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

/-- `exists_finite_span` with the spanning tuples made explicit: homogeneous vectors and a
functional **supported** at the weight `h₄ + N₄`. -/
theorem exists_finite_span_supported {h₁ h₂ h₃ h₄ ν : ℂ}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂)
    (N₁ N₂ N₃ N₄ : ℕ) :
    ∃ T : Set (PowerSeries ℂ), T.Finite ∧
      (∀ g ∈ T, ∃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃),
        w₁ ∈ A₁.weight (h₁ + N₁) ∧ w₂ ∈ A₂.weight (h₂ + N₂) ∧ w₃ ∈ A₃.weight (h₃ + N₃) ∧
        SupportedAt A₄ f (h₄ + N₄) ∧
        g = QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)) ∧
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        QT Y₁ Y₂ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ Submodule.span ℂ T := by
  classical
  haveI := A₁.finrank (h₁ + N₁)
  haveI := A₂.finrank (h₂ + N₂)
  haveI := A₃.finrank (h₃ + N₃)
  haveI := A₄.finrank (h₄ + N₄)
  set E₄ := A₄.weight (h₄ + N₄)
  set π := weightProj A₄ (h₄ + N₄)
  set b₁ := Module.finBasis ℂ (A₁.weight (h₁ + N₁))
  set b₂ := Module.finBasis ℂ (A₂.weight (h₂ + N₂))
  set b₃ := Module.finBasis ℂ (A₃.weight (h₃ + N₃))
  set b₄ := Module.finBasis ℂ (Module.Dual ℂ E₄)
  set c := h₁ + h₂ + h₃ - h₄ - 2
  set s := N₁ + N₂ + N₃ + N₄
  refine ⟨Set.range fun q : _ × _ × _ × _ =>
    QT Y₁ Y₂ c ν ((b₄ q.1).comp π) (b₁ q.2.1 : M₁) (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2 : M₃) N₄ s,
    Set.finite_range _, ?_, ?_⟩
  · rintro g ⟨q, rfl⟩
    exact ⟨(b₄ q.1).comp π, b₁ q.2.1, b₂ q.2.2.1, b₃ q.2.2.2, (b₁ q.2.1).2, (b₂ q.2.2.1).2,
      (b₃ q.2.2.2).2, supportedAt_comp_weightProj A₄ _ _, rfl⟩
  intro f w₁ w₂ w₃ hw₁ hw₂ hw₃
  rw [QT_congr_f hY₁ hY₂ hw₁ hw₂ hw₃ (domRestrict_comp_weightProj A₄ (h₄ + N₄) f)]
  have hψ := b₄.sum_repr (f.domRestrict E₄)
  have hcomp : (f.domRestrict E₄).comp π
      = ∑ a, b₄.repr (f.domRestrict E₄) a • (b₄ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change QTf (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s w₁ w₂ w₃ ((f.domRestrict E₄).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change QT₁ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) w₂ w₃ w₁ ∈ _
  refine map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change QT₂ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) w₃ w₂ ∈ _
  refine map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change QT₃ (Y₁ := Y₁) (Y₂ := Y₂) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) (b₂ j : M₂) w₃ ∈ _
  refine map_mem_span_basis _ _ hw₃ _ fun k => ?_
  exact Submodule.subset_span ⟨(a, i, j, k), rfl⟩

end Base

/-! ## The `ℂ[x]`-module of series of bounded log-degree -/

section Module

/-- The analytic value of a series `Z` in `x = (1 + e^t)⁻¹`, with the prefactor
`(1 + e^t)^{−c₀−1}`. -/
noncomputable def Phi (c₀ : ℂ) (Z : PowerSeries ℂ) (t : ℂ) : ℂ :=
  (1 + Complex.exp t) ^ (-c₀ - 1) * psEval Z (xt t)

theorem psEval_zero' (y : ℂ) : psEval (0 : PowerSeries ℂ) y = 0 := by
  simp [psEval]

/-- **Series of bounded log-degree form a `ℂ[x]`-module.** -/
noncomputable def logModule (c₀ : ℂ) (K : ℕ) : Submodule (ratRing 0) (PowerSeries ℂ) where
  carrier := {Z | Z ∈ SubexpPS ∧ LogDegLE K (Phi c₀ Z)}
  zero_mem' := ⟨SubexpPS.zero_mem, (logDegLE_zero K).congr fun t _ => by
    simp [Phi, psEval_zero']⟩
  add_mem' := by
    rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
    refine ⟨SubexpPS.add_mem hA hB, (hA'.add hB').congr fun t ht => ?_⟩
    simp only [Phi, Pi.add_apply]
    rw [psEval_add hA hB (norm_xt_lt_one ht)]
    ring
  smul_mem' := by
    rintro ⟨r, hr⟩ Z ⟨hZ, hZ'⟩
    have hrs := subexp_of_mem_ratRing_zero hr
    obtain ⟨c, hc, hcr⟩ := exists_subexp_of_mem_ratRing_zero hr
    refine ⟨?_, (hZ'.psEval_mul hc).congr fun t ht => ?_⟩
    · rw [Subalgebra.smul_def]
      exact SubexpPS.mul_mem hrs hZ
    · simp only [Phi]
      rw [show (⟨r, hr⟩ : ratRing 0) • Z = r * Z from rfl,
        psEval_mul hrs hZ (norm_xt_lt_one ht), hcr _ (norm_exp_lt_one ht)]
      simp only [xt]
      ring

end Module

/-! ## The renormalization identity -/

section Identity

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- **The renormalized series and the product.**  With `σ − ν₀ = c₀ + N₁ − N₄`, at
`z₂ = 1`, `z₁ = 1 + e^t`:
`Φ((1 − x)^s x^K G)(t) = e^{st} (1 + e^t)^{−(N₄ − N₁ + s + K)} F(t)`. -/
theorem Phi_eq (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ c₀ : ℂ) (N₁ N₄ s K : ℕ)
    (hσ : σ - ν₀ = c₀ + N₁ - N₄)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) {t : ℂ} (ht : t ∈ overlapDomain) :
    Phi c₀ ((1 - X) ^ s * (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)) t
      = Complex.exp ((s : ℂ) * t) * (psEval (binPS (-((N₄ : ℤ) - N₁ + s + K)))
          (Complex.exp t) * prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ t) := by
  have hz := one_add_exp_ne_zero ht
  have hy := norm_xt_lt_one ht
  rw [Phi, prodFun_eq Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ht,
    psEval_mul (SubexpPS.pow_mem one_sub_X_mem_subexp s)
      (SubexpPS.mul_mem (SubexpPS.pow_mem X_mem_subexp K) hG) hy,
    psEval_mul (SubexpPS.pow_mem X_mem_subexp K) hG hy,
    psEval_pow one_sub_X_mem_subexp hy, psEval_pow X_mem_subexp hy,
    psEval_sub SubexpPS.one_mem X_mem_subexp hy, psEval_one, psEval_X,
    psEval_binPS _ (norm_exp_lt_one ht)]
  set e := Complex.exp t with he
  set z := 1 + e with hzdef
  have hxt : xt t = z⁻¹ := rfl
  have h1x : 1 - xt t = e * z⁻¹ := by
    rw [hxt]; field_simp; rw [hzdef]; ring
  have hexp : Complex.exp ((s : ℂ) * t) = e ^ s := by
    rw [he, ← Complex.exp_nat_mul]
  have hcp : z ^ (-(σ - ν₀) - 1) = z ^ (-c₀ - 1) * z ^ (((N₄ : ℤ) - N₁ : ℤ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hz, hσ]
    congr 1
    push_cast; ring
  rw [h1x, hexp, hcp, Complex.cpow_intCast, hxt]
  rw [show (-((N₄ : ℤ) - N₁ + s + K)) = -(((N₄ : ℤ) - N₁) + (s + K : ℕ)) by push_cast; ring,
    zpow_neg, zpow_add₀ hz, zpow_natCast]
  rw [mul_pow, inv_pow, inv_pow, pow_add]
  field_simp

/-- The converse form of `Phi_eq`. -/
theorem prodFun_eq_Phi (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ c₀ : ℂ) (N₁ N₄ s K : ℕ)
    (hσ : σ - ν₀ = c₀ + N₁ - N₄)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) {t : ℂ} (ht : t ∈ overlapDomain) :
    prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ t
      = Complex.exp ((-(s : ℂ)) * t) * (psEval (binPS ((N₄ : ℤ) - N₁ + s + K)) (Complex.exp t)
          * Phi c₀ ((1 - X) ^ s * (X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)) t) := by
  rw [Phi_eq Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ c₀ N₁ N₄ s K hσ hG ht,
    psEval_binPS _ (norm_exp_lt_one ht), psEval_binPS _ (norm_exp_lt_one ht)]
  have hz := one_add_exp_ne_zero ht
  rw [zpow_neg]
  field_simp
  rw [mul_assoc, ← Complex.exp_add]
  simp

end Identity

/-! ## The uniform log-degree bound -/

section Main

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem prodFun_eq_zero_of_w₁ {M₁ M₂ M₃ M₄ M₅ : Type u}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
    [AddCommGroup M₅] [Module ℂ M₅] (Y₁ : IntertwiningModes M₁ M₅ M₄)
    (Y₂ : IntertwiningModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (σ ν₀ : ℂ) (h : w₁ = 0 ∨ w₂ = 0 ∨ w₃ = 0 ∨ f = 0) :
    prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ = fun _ => 0 := by
  funext t
  rcases h with h | h | h | h <;> subst h <;> simp [prodFun, prodValue, prodCoeff]

/-- **A uniform bound on the log-degree** of all products of `𝒴₁, 𝒴₂` at the iterate
point (strongly rational `V`, irreducible modules). -/
theorem logDeg_bounded_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂) :
    ∃ K : ℕ, ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ), w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ →
      w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
      LogDegLE K (prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)) := by
  classical
  have h2 := VOA.Huang.BuhlSpanning.moduleC2Input_holds.{u}
  have hC : ModuleC1Data W := VOA.Huang.HuangODEC1.moduleC1Data_of_C2
    (fun P hP => h2 𝒱 W hV P hP)
    (VOA.Huang.HuangODEDual.moduleDualC1Data_of_contragredientC2
      (VOA.Huang.HuangODEContra.contragredientC2Data_of_moduleC2Input h2 hV))
  obtain ⟨B₁, c₁⟩ := (hC P₁ i₁).1
  obtain ⟨B₂, c₂⟩ := (hC P₂ i₂).1
  obtain ⟨B₃, c₃⟩ := (hC P₃ i₃).1
  obtain ⟨B₄, d₄⟩ := (hC P₄ i₄).2
  set c₀ : ℂ := P₁.h - P₄.h - 1 + Q.h with hc₀
  set ν₀ : ℂ := P₂.h + P₃.h - 1 - Q.h with hν₀
  obtain ⟨K₀, hUB⟩ := exists_unifBase (A₅ := Q.isMod) hY₂ P₂.h P₃.h ν₀ 0
  set ν : ℂ := ν₀ - ((0 : ℕ) : ℂ) + K₀ with hν
  set cc : ℂ := P₁.h + P₂.h + P₃.h - P₄.h - 2 with hcc
  -- the renormalized series of a homogeneous supported tuple
  have hZ : ∀ (N₁ N₂ N₃ N₄ : ℕ) (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
      (w₃ : P₃.carrier), w₁ ∈ P₁.isMod.weight (P₁.h + N₁) →
      w₂ ∈ P₂.isMod.weight (P₂.h + N₂) → w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
      SupportedAt P₄.isMod f (P₄.h + N₄) →
      (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        = (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * (X ^ (K₀ + N₁ + N₄) * prodSeries Y₁ Y₂ f w₁ w₂ w₃
            ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
            ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h)) := by
    intro N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ _
    have hb := isBase_canonical Q hY₂ hw₂ hw₃
    have e : ν = ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h) - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ)
        + ((K₀ + N₁ + N₄ : ℕ) : ℂ) := by
      rw [hν, hν₀]; push_cast; ring
    rw [e, QT_eq_X_pow_mul_prodSeries hb]
  -- transfer of log-degree bounds between `Φ(Z_D)` and the product
  have hσeq : ∀ N₁ N₂ N₃ N₄ : ℕ,
      ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
        - ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h) = c₀ + N₁ - N₄ := by
    intros; rw [hc₀]; ring
  have hgood : ∀ (N₁ N₂ N₃ N₄ : ℕ) (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier)
      (w₂ : P₂.carrier) (w₃ : P₃.carrier), w₁ ∈ P₁.isMod.weight (P₁.h + N₁) →
      w₂ ∈ P₂.isMod.weight (P₂.h + N₂) → w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
      SupportedAt P₄.isMod f (P₄.h + N₄) →
      (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ SubexpPS ∧
      (∀ K, LogDegLE K (prodFun Y₁ Y₂ f w₁ w₂ w₃
          ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
          ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h)) →
        LogDegLE K (Phi c₀ ((1 - X) ^ (N₁ + N₂ + N₃ + N₄)
          * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)))) ∧
      (∀ K, LogDegLE K (Phi c₀ ((1 - X) ^ (N₁ + N₂ + N₃ + N₄)
          * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄))) →
        LogDegLE K (prodFun Y₁ Y₂ f w₁ w₂ w₃
          ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
          ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h))) := by
    intro N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf
    have hG := prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ hY₁ hY₂ hw₁ hw₂ hw₃ hf
    rw [hZ N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf]
    refine ⟨SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp _)
      (SubexpPS.mul_mem (SubexpPS.pow_mem X_mem_subexp _) hG), fun K hK => ?_, fun K hK => ?_⟩
    · exact ((hK.psEval_mul (binPS_mem _)).exp_mul _).congr fun t ht =>
        (Phi_eq Y₁ Y₂ f w₁ w₂ w₃ _ _ c₀ N₁ N₄ (N₁ + N₂ + N₃ + N₄) (K₀ + N₁ + N₄)
          (hσeq N₁ N₂ N₃ N₄) hG ht).symm
    · exact ((hK.psEval_mul (binPS_mem _)).exp_mul _).congr fun t ht =>
        (prodFun_eq_Phi Y₁ Y₂ f w₁ w₂ w₃ _ _ c₀ N₁ N₄ (N₁ + N₂ + N₃ + N₄) (K₀ + N₁ + N₄)
          (hσeq N₁ N₂ N₃ N₄) hG ht).symm
  -- the finitely many base generators
  choose T hTfin hTform hTspan using fun q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1)
      × Fin (B₄ + 1) =>
    exists_finite_span_supported (h₁ := P₁.h) (h₂ := P₂.h) (h₃ := P₃.h) (h₄ := P₄.h)
      (ν := ν) hY₁ hY₂ q.1 q.2.1 q.2.2.1 q.2.2.2
  set lev : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) → ℕ :=
    fun q => (q.1 : ℕ) + (q.2.1 : ℕ) + (q.2.2.1 : ℕ) + (q.2.2.2 : ℕ) with hlev
  set S : Set (PowerSeries ℂ) := ⋃ q, (fun g => (1 - X) ^ lev q * g) '' T q with hS
  have hSfin : S.Finite := Set.finite_iUnion fun q => (hTfin q).image _
  have hSgood : ∀ Z ∈ S, ∃ K, Z ∈ logModule c₀ K := by
    intro Z hZS
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hZS
    obtain ⟨g, hg, rfl⟩ := hq
    obtain ⟨f, w₁, w₂, w₃, hw₁, hw₂, hw₃, hf, rfl⟩ := hTform q g hg
    obtain ⟨K, hK⟩ := exists_logDegLE (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hw₁ hw₂ hw₃ hf)
    have hg' := hgood q.1 q.2.1 q.2.2.1 q.2.2.2 f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf
    exact ⟨K, hg'.1, hg'.2.1 K hK⟩
  choose! KZ hKZ using hSgood
  set K : ℕ := hSfin.toFinset.sup KZ with hK
  have hSK : ∀ Z ∈ S, Z ∈ logModule c₀ K := by
    intro Z hZS
    obtain ⟨h1, h2⟩ := hKZ Z hZS
    exact ⟨h1, h2.mono (Finset.le_sup (f := KZ) (hSfin.mem_toFinset.mpr hZS))⟩
  -- the base hypothesis of `pt_mem`
  have hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier),
        w₁ ∈ P₁.isMod.weight (P₁.h + N₁) → w₂ ∈ P₂.isMod.weight (P₂.h + N₂) →
        w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
        (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
          QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ logModule c₀ K := by
    intro N₁ N₂ N₃ N₄ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃
    set q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
      (⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩) with hq
    have hmem := hTspan q f w₁ w₂ w₃ hw₁ hw₂ hw₃
    have hmem' : (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
        QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ Submodule.span ℂ ((fun g => (1 - X) ^ lev q * g) '' T q) := by
      have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℂ ((1 - X) ^ lev q)) hmem
      rw [Submodule.map_span] at this
      exact this
    have hle : Submodule.span ℂ ((fun g => (1 - X) ^ lev q * g) '' T q)
        ≤ (logModule c₀ K).restrictScalars ℂ := by
      rw [Submodule.span_le]
      intro Z hZ'
      exact hSK Z (Set.mem_iUnion.mpr ⟨q, hZ'⟩)
    exact hle hmem'
  have hall := pt_mem hY₁ hY₂ P₁.isLow P₂.isLow P₃.isLow P₄.isLow hUB c₁ c₂ c₃ d₄
    (logModule c₀ K) hbase
  refine ⟨K, fun α₁ α₂ α₃ h₄ w₁ w₂ w₃ f hw₁ hw₂ hw₃ hf => ?_⟩
  -- degenerate cases
  by_cases z₁ : P₁.isMod.weight α₁ = ⊥
  · have h0 : w₁ = 0 := by rw [z₁] at hw₁; exact (Submodule.mem_bot ℂ).mp hw₁
    rw [prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inl h0)]
    exact logDegLE_zero K
  by_cases z₂ : P₂.isMod.weight α₂ = ⊥
  · have h0 : w₂ = 0 := by rw [z₂] at hw₂; exact (Submodule.mem_bot ℂ).mp hw₂
    rw [prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inr (Or.inl h0))]
    exact logDegLE_zero K
  by_cases z₃ : P₃.isMod.weight α₃ = ⊥
  · have h0 : w₃ = 0 := by rw [z₃] at hw₃; exact (Submodule.mem_bot ℂ).mp hw₃
    rw [prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inl h0)))]
    exact logDegLE_zero K
  by_cases z₄ : P₄.isMod.weight h₄ = ⊥
  · rw [prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _
      (Or.inr (Or.inr (Or.inr (eq_zero_of_supportedAt_bot hf z₄))))]
    exact logDegLE_zero K
  obtain ⟨N₁, rfl⟩ := P₁.isLow α₁ z₁
  obtain ⟨N₂, rfl⟩ := P₂.isLow α₂ z₂
  obtain ⟨N₃, rfl⟩ := P₃.isLow α₃ z₃
  obtain ⟨N₄, rfl⟩ := P₄.isLow h₄ z₄
  have hm := hall _ N₁ N₂ N₃ N₄ rfl f w₁ w₂ w₃ hw₁ hw₂ hw₃
  exact (hgood N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf).2.2 K hm.2

/-- **`CoeffLogBounded` holds** for strongly rational `V` (one log bound for all
products of given intertwiners, in particular for each outside datum). -/
theorem coeffLogBounded_holds (hV : StronglyRational W) : CoeffLogBounded W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  obtain ⟨K, hK⟩ := logDeg_bounded_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
  refine ⟨K, fun k hk => ?_⟩
  funext x
  simp only [coefFun, Pi.zero_apply, prodExpCoeff]
  exact (hK _ _ _ _ _ _ _ _ x.h₁ x.h₂ h₃ hf).2 _ k hk

end Main


end VOA.Huang.LogRemovalBound

