/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorY3
import VOA.Huang.LogRemovalWeak
import VOA.Huang.PzTensorCompatProof

/-!
# The log-free iterate identity from a decomposition of `Λ` (assembly)

Let `Λ = coefSpan 𝒴₁ 𝒴₂` be the span of the coefficient functions of a product of intertwining
operators among irreducible modules.  Suppose (`CoefSpanDecomp`) that `Λ`, under the
Huang–Lepowsky action `τ`, splits as a finite sum of irreducible lowest-weight modules: there are
irreducible `R_j`, `τ`-equivariant `ψ_j : R_j → Λ` and `χ_j : Λ → R_j` with `Σ ψ_j χ_j = id`.
Then, with `Qs j = R_j'`, `𝒴₄ j = Y4` (built from `ψ_j`, `PzTensorY4`) and `𝒴₃ j = Y3` (built
from `χ_j`, `PzTensorY3`), every log-free coefficient of the product is the corresponding
coefficient of `Σ_j 𝒴₃ j (𝒴₄ j (·, ·), ·)`:

`assocCoeffIdentityZero_of_decomp : StronglyRational W → ABDWeakIsAdmissible W →
CoefSpanDecomp W → AssocCoeffIdentityZero W`, and hence
`associativityInput_of_decomp : … → AssociativityInput W`.

The log-freeness used by `𝒴₃` (`PzTensorY3.LogFree`) is discharged from ABD through log removal
(`LogRemovalWeak.coeffL0Semisimple_of_weakInput` with the proved `CoeffWeakInput`).

`CoefSpanDecomp` is a named Prop (TRUE for strongly rational `W`: `Λ` is a weak module
(`coeffWeakInput_holds`), admissible by ABD, hence a direct sum of irreducible ordinary modules
by rationality; the sum is finite since each summand `R_j` yields, through `Y4`, a nonzero
intertwining operator of type `(R_j' / P₁ P₂)` and the fusion rules are finite — Huang 2005 §3,
HL IV, DLM 1997).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorHL6

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction VOA.Huang.AssocCoeffRules
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorHatBridge
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorY4 VOA.Huang.PzTensorY3
open VOA.Huang.PzTensorCompat VOA.Huang.HuangODEContra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Weight membership from the `L₀`-eigenvalue -/

/-- An `L₀`-eigenvector of eigenvalue `γ` lies in the weight space of weight `γ`. -/
theorem mem_weight_of_L0 {P : LWModule W} {γ : ℂ} {v : P.carrier}
    (hv : mode (P.isMod.YM W.conformalVector) 1 v = γ • v) : v ∈ P.isMod.weight γ := by
  have hp := internalProjTo_coe_mem P.isMod
    (Submodule.coe_mem (internalProjTo P.isMod.isInternal γ v))
  have key : v - ((internalProjTo P.isMod.isInternal γ v : P.isMod.weight γ) : P.carrier) = 0 := by
    refine eq_zero_of_supported fun hh f hf => ?_
    rw [map_sub, sub_eq_zero]
    by_cases hγ : hh = γ
    · subst hγ
      conv_lhs => rw [← extF_restrict hf]
      simp only [extF, LinearMap.comp_apply, Submodule.subtype_apply]
    · have h1 : γ * f v = hh * f v := by
        have := congrArg (fun F : P.carrier →ₗ[ℂ] ℂ => F v) (comp_L0 hf)
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, hv, map_smul] at this
        exact this
      have h2 : f v = 0 := by
        have : (γ - hh) * f v = 0 := by rw [sub_mul, h1, sub_self]
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (sub_eq_zero.mp h).symm hγ
        · exact h
      rw [h2, hf γ (Ne.symm hγ) _ (Submodule.coe_mem _)]
  rw [sub_eq_zero.mp key]
  exact Submodule.coe_mem _

/-! ## The named decomposition of `Λ` -/

/-- **`CoefSpanDecomp`** (named; TRUE for strongly rational `W` — Huang 2005 §3, HL IV, ABD,
DLM 1997 complete reducibility, finite fusion rules): for every product of intertwining operators
among irreducible modules, the span `Λ` of its coefficient functions is, under the
Huang–Lepowsky action `τ`, a finite sum of irreducible lowest-weight modules `R_j`, realized by
`τ`-equivariant maps `ψ_j : R_j → Λ` and `χ_j : Λ → R_j` with `Σ_j ψ_j ∘ χ_j = id_Λ`. -/
def CoefSpanDecomp (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (R : Fin r → LWModule W) (_ : ∀ j, (R j).IsIrreducibleLW)
    (ψ : ∀ j, (R j).carrier →ₗ[ℂ] coefSpan Y₁ Y₂) (χ : ∀ j, coefSpan Y₁ Y₂ →ₗ[ℂ] (R j).carrier),
    (∀ j (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (k : ℤ) (v : (R j).carrier),
      ((ψ j (mode ((R j).isMod.YM u) k v) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
        = tauHom hu k ((ψ j v : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)) ∧
    (∀ j, TauProj (Y₁ := Y₁) (Y₂ := Y₂) (χ j)) ∧
    ∀ G : coefSpan Y₁ Y₂, ∑ j, ψ j (χ j G) = G

section Assembly

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

/-- A `τ`-equivariant map into `Λ` is a `τ`-embedding (`PzTensorY4.TauEmb`): bilinearity, lower
truncation and compatibility hold on all of `Λ`. -/
theorem tauEmb_of_coefSpan {R : LWModule W} (ψ : R.carrier →ₗ[ℂ] coefSpan Y₁ Y₂)
    (hψ : ∀ (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (k : ℤ) (v : R.carrier),
      ((ψ (mode (R.isMod.YM u) k v) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
        = tauHom hu k ((ψ v : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)) :
    TauEmb R ((coefSpan Y₁ Y₂).subtype ∘ₗ ψ) where
  bil v := coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ v).2
  act β u hu k v := hψ β u hu k v
  trunc v _ _ ha := copT_truncation_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ v).2 ha
  compat v := compatFn_coefSpan iQ (PzTensorCompatProof.coeffCompat_holds hV) hY₁ hY₂ i₁ i₂ i₃ i₄
    (ψ v).2

/-- Log-freeness of the coefficient functions from ABD (log removal). -/
theorem logFree_of_ABD (hABD : ABDWeakIsAdmissible W) : LogFree (Y₁ := Y₁) (Y₂ := Y₂) := by
  intro f w₃ α₃ hh γ h₃ hf
  have hS := LogRemovalWeak.coeffL0Semisimple_of_weakInput hV hABD (coeffWeakInput_holds hV)
  funext x
  exact prodExpCoeff_log_eq_zero hV hS i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf _ le_rfl

/-- `χ(B_γ)` has weight `γ`: `τ(ω, 1) = L'(0)` acts on the log-free `B_γ` by `γ`. -/
theorem chi_B_mem (hlog : LogFree (Y₁ := Y₁) (Y₂ := Y₂)) {R : LWModule W}
    {χ : coefSpan Y₁ Y₂ →ₗ[ℂ] R.carrier} (hP : TauProj χ) {f : P₄.carrier →ₗ[ℂ] ℂ}
    {w₃ : P₃.carrier} {α₃ hh : ℂ} (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f hh)
    (γ : ℂ) :
    χ ⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩
      ∈ R.isMod.weight γ := by
  apply mem_weight_of_L0
  have hω := W.conformalVector_mem_grading_two
  have hm := tauHom_mem_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
    (coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0) hω 1
  have h1 := hlog f w₃ α₃ hh γ h₃ hf
  have hfun : tauHom hω 1 (coefFun Y₁ Y₂ f w₃ α₃ hh γ 0) = γ • coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 := by
    rw [tauHom_conformal_one (coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0),
      L0T_coefFun hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0, zero_add, h1, smul_zero, add_zero]
  have e : (⟨tauHom hω 1 (coefFun Y₁ Y₂ f w₃ α₃ hh γ 0), hm⟩ : coefSpan Y₁ Y₂)
      = γ • (⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩ :
        coefSpan Y₁ Y₂) := Subtype.ext hfun
  have h2 := hP ⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩ 2
    W.conformalVector hω 1 hm
  rw [e, map_smul] at h2
  exact h2.symm

/-- **One summand of the iterate side**: the log-free coefficient of the iterate built from
`(ψ, χ)` is `ψ(χ(B_n))(w₁, w₂)` at intermediate weight `n = μ + α₁ + α₂`. -/
theorem iterExpCoeff_Y3_Y4 (hlog : LogFree (Y₁ := Y₁) (Y₂ := Y₂)) {R : LWModule W}
    (ψ : R.carrier →ₗ[ℂ] coefSpan Y₁ Y₂)
    (hψ : ∀ (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (k : ℤ) (v : R.carrier),
      ((ψ (mode (R.isMod.YM u) k v) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
        = tauHom hu k ((ψ v : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ))
    {χ : coefSpan Y₁ Y₂ →ₗ[ℂ] R.carrier} (hP : TauProj χ)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ} (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (μ : ℂ) :
    iterExpCoeff (Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ)
        (Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ ψ hψ)) f w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - (contraLW R).h) μ 0
      = ((ψ (χ ⟨coefFun Y₁ Y₂ f w₃ α₃ h₄ (μ + α₁ + α₂) 0,
          coefFun_mem_coefSpan Y₁ Y₂ h₃ hf (μ + α₁ + α₂) 0⟩) : coefSpan Y₁ Y₂) :
          HomPair P₁ P₂ → ℂ) ⟨w₁, α₁, w₂, α₂, h₁, h₂⟩ := by
  set hE := tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ ψ hψ
  set ν : ℂ := α₁ + α₂ - 1 - (contraLW R).h with hν
  set F : ℂ → ℂ := fun n => ((ψ (χ ⟨coefFun Y₁ Y₂ f w₃ α₃ h₄ n 0,
    coefFun_mem_coefSpan Y₁ Y₂ h₃ hf n 0⟩) : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
      ⟨w₁, α₁, w₂, α₂, h₁, h₂⟩ with hF
  have hFc : ∀ n n' : ℂ, n = n' → F n = F n' := by rintro _ _ rfl; rfl
  change _ = F (μ + α₁ + α₂)
  by_cases hm : ∃ m : ℕ, -ν - 1 + m = μ
  · obtain ⟨m, rfl⟩ := hm
    rw [iterExpCoeff_eq, if_pos rfl]
    unfold MatrixCoeff.iterCoeff
    have hξ : Y4 hE (ν - m) w₁ w₂ ∈ (contraLW R).isMod.weight (α₁ + α₂ - (ν - m) - 1) := by
      rw [Y4_homog hE (ν - m) h₁ h₂]
      exact LinearMap.mem_range_self _ _
    refine (pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ _ hξ h₃ hf).trans ?_
    rw [if_pos (by ring), Bχ,
      pair_Y4 hE (ν - m) (chi_B_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hlog hP h₃ hf _) h₁ h₂, if_pos rfl]
    exact hFc _ _ (by ring)
  · push Not at hm
    rw [iterExpCoeff_eq_zero _ _ _ _ _ _ _ _ _ hm]
    have hmem := chi_B_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hlog hP h₃ hf (μ + α₁ + α₂)
    have hbot : R.isMod.weight (μ + α₁ + α₂) = ⊥ := by
      by_contra hne
      obtain ⟨m, hm'⟩ := R.isLow _ hne
      exact hm m (by rw [hν]; change -(α₁ + α₂ - 1 - R.h) - 1 + m = μ; linear_combination -hm')
    rw [hbot] at hmem
    simp only [hF, (Submodule.mem_bot ℂ).mp hmem, map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]

end Assembly

/-- **The log-free iterate identity** (`AssocCoeffIdentityZero`) from ABD and the
named decomposition `CoefSpanDecomp` of the span of coefficient functions. -/
theorem assocCoeffIdentityZero_of_decomp (hV : StronglyRational W)
    (hABD : ABDWeakIsAdmissible W) (hD : CoefSpanDecomp W) : AssocCoeffIdentityZero W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, R, iR, ψ, χ, hψ, hP, hsum⟩ := hD P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  have hlog := logFree_of_ABD hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hABD
  refine ⟨r, fun j => contraLW (R j), fun j => contraLW_isIrreducibleLW (iR j),
    fun j => Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (χ j),
    fun j => Y4 (tauEmb_of_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (ψ j) (hψ j)),
    fun j => isIntertwining_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (χ j) (hP j) hlog,
    fun j => isIntertwining_Y4 _, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf μ
  rw [Finset.sum_congr rfl fun j _ =>
    iterExpCoeff_Y3_Y4 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hlog (ψ j) (hψ j) (hP j) h₁ h₂ h₃ hf μ]
  have hs := congrArg (fun G : coefSpan Y₁ Y₂ => (G : HomPair P₁ P₂ → ℂ) ⟨w₁, α₁, w₂, α₂, h₁, h₂⟩)
    (hsum ⟨coefFun Y₁ Y₂ f w₃ α₃ h₄ (μ + α₁ + α₂) 0,
      coefFun_mem_coefSpan Y₁ Y₂ h₃ hf (μ + α₁ + α₂) 0⟩)
  simp only [Submodule.coe_sum, Finset.sum_apply] at hs
  rw [hs]
  change _ = prodExpCoeff Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)
    (μ + α₁ + α₂ - α₁ - α₂) 0
  rw [show μ + α₁ + α₂ - α₁ - α₂ = μ by ring]

/-- **`AssociativityInput` from ABD and `CoefSpanDecomp`** (strongly rational `V`). -/
theorem associativityInput_of_decomp (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hD : CoefSpanDecomp W) : AssociativityInput W :=
  associativityInput_of_ABD hV hABD (assocCoeffIdentityZero_of_decomp hV hABD hD)

end VOA.Huang.PzTensorHL6
