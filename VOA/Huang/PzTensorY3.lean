/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorOutside

/-!
# The second iterate intertwiner `𝒴₃` (part 2)

Let `R` be a lowest-weight module and `χ : Λ → R` a linear map from the span `Λ` of the
coefficient functions of a product `𝒴₁ 𝒴₂` which intertwines the Huang–Lepowsky action `τ` with
the module action of `R` (`TauProj`).  Then

`⟨f, 𝒴₃(ξ, x) w₃⟩ = ⟨χ B_{wt ξ}(f, w₃), ξ⟩ x^{…}`  (`ξ ∈ R'`, `w₃ ∈ P₃`, `f ∈ P₄*`)

defines an intertwining operator `𝒴₃` of type `(P₄ / R' P₃)` (`isIntertwining_Y3`), provided
the coefficient functions are log-free (`B_{γ,1} = 0`, a consequence of log removal).  Its Jacobi
identity is the outside Borcherds identity `PzTensorOutside.outE_eq_zero` transported by `χ`
and the double twist; its `L₋₁`-property is the `ω`-case of the same identity plus
`L'(0) B_γ = γ B_γ`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorY3

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction VOA.Huang.AssocCoeffRules
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorHatBridge
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorY4 VOA.Huang.PzTensorOutside
open VOA.Huang.HuangODEContra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Functionals supported at one weight -/

section Supp

variable {P : LWModule W}

/-- The functional `g ∘ proj_h` on `P`, for `g ∈ P(h)*`. -/
noncomputable def extF (h : ℂ) (g : Module.Dual ℂ (P.isMod.weight h)) : P.carrier →ₗ[ℂ] ℂ :=
  g ∘ₗ internalProjTo P.isMod.isInternal h

theorem extF_supported (h : ℂ) (g : Module.Dual ℂ (P.isMod.weight h)) :
    SupportedAt P.isMod (extF h g) h := by
  intro α hα x hx
  simp only [extF, LinearMap.comp_apply]
  rw [internalProjTo_eq_zero_of_ne P.isMod hx (Ne.symm hα), map_zero]

theorem extF_apply_mem (h : ℂ) (g : Module.Dual ℂ (P.isMod.weight h)) {x : P.carrier}
    (hx : x ∈ P.isMod.weight h) : extF h g x = g ⟨x, hx⟩ := by
  simp only [extF, LinearMap.comp_apply]
  congr 1
  exact Subtype.ext (internalProjTo_coe_mem P.isMod hx)

/-- A functional supported at `h` is `extF` of its restriction. -/
theorem extF_restrict {h : ℂ} {f : P.carrier →ₗ[ℂ] ℂ} (hf : SupportedAt P.isMod f h) :
    extF h (f ∘ₗ (P.isMod.weight h).subtype) = f := by
  ext x
  have hx : x ∈ ⨆ α, P.isMod.weight α := mem_iSup_weight P x
  refine Submodule.iSup_induction P.isMod.weight
    (motive := fun x => extF h (f ∘ₗ (P.isMod.weight h).subtype) x = f x) hx ?_ (by simp) ?_
  · intro α y hy
    by_cases hα : α = h
    · subst hα
      rw [extF_apply_mem _ _ hy]; rfl
    · rw [hf α hα y hy]
      simp only [extF, LinearMap.comp_apply]
      rw [internalProjTo_eq_zero_of_ne P.isMod hy (Ne.symm hα)]
      simp
  · intro y z hy hz; rw [map_add, map_add, hy, hz]

/-- A vector is zero once all functionals supported at single weights vanish on it. -/
theorem eq_zero_of_supported {v : P.carrier}
    (h : ∀ (hh : ℂ) (f : P.carrier →ₗ[ℂ] ℂ), SupportedAt P.isMod f hh → f v = 0) : v = 0 := by
  classical
  haveI : ∀ α, FiniteDimensional ℂ (P.isMod.weight α) := P.isMod.finrank
  have hc : ∀ α, internalProjTo P.isMod.isInternal α v = 0 := by
    intro α
    by_contra hne
    obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (P.isMod.weight α),
        g (internalProjTo P.isMod.isInternal α v) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, ne_eq, not_not] at hcon
      exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp hcon)
    exact hg (h α (extF α g) (extF_supported α g))
  letI := DirectSum.IsInternal.chooseDecomposition P.isMod.weight P.isMod.isInternal
  have hd : DirectSum.decompose P.isMod.weight v = 0 := by
    ext α
    have := hc α
    simp only [internalProjTo, LinearMap.comp_apply] at this
    exact congrArg Subtype.val this
  have := congrArg (DirectSum.decompose P.isMod.weight).symm hd
  simpa using this

end Supp

/-! ## Linearity of the coefficient functions in the outside data -/

section Lin

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

theorem coefFun_add_f {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f f' : P₄.carrier →ₗ[ℂ] ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    (hf' : SupportedAt P₄.isMod f' h₄) (n : ℂ) (k : ℕ) (x : HomPair P₁ P₂) :
    coefFun Y₁ Y₂ (f + f') w₃ α₃ h₄ n k x
      = coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x + coefFun Y₁ Y₂ f' w₃ α₃ h₄ n k x := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  have hsum : SupportedAt P₄.isMod (f + f') h₄ := fun α hα y hy => by
    rw [LinearMap.add_apply, hf α hα y hy, hf' α hα y hy, add_zero]
  simp only [coefFun, prodExpCoeff]
  have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
  have e' := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf'
  rw [logCoeff_congr hU hs hne (G := fun t =>
      prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t
        + prodFun Y₁ Y₂ f' x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t)
    (fun t ht => by
      have s := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ x.h₁ x.h₂ h₃ hf one_ne_zero
        (one_norm_lt ht)
      have s' := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ x.h₁ x.h₂ h₃ hf' one_ne_zero
        (one_norm_lt ht)
      unfold prodFun prodValue
      beta_reduce
      rw [← Summable.tsum_add s s']
      refine tsum_congr fun k => ?_
      simp only [prodCoeff, LinearMap.add_apply]
      ring)
    (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hsum)]
  exact logCoeff_add hU hs hne e e' _ _

omit hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem coefFun_smul_f {α₃ h₄ : ℂ} {w₃ : P₃.carrier} (c : ℂ) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (n : ℂ) (k : ℕ)
    (x : HomPair P₁ P₂) :
    coefFun Y₁ Y₂ (c • f) w₃ α₃ h₄ n k x = c * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  simp only [coefFun, prodExpCoeff]
  have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
  have hcf : SupportedAt P₄.isMod (c • f) h₄ := fun α hα y hy => by
    rw [LinearMap.smul_apply, hf α hα y hy, smul_zero]
  rw [logCoeff_congr hU hs hne (G := fun t => c *
      prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t)
    (fun t _ => by
      unfold prodFun prodValue
      beta_reduce
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [prodCoeff, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hcf)]
  exact logCoeff_smul hU hs hne c e _ _

theorem coefFun_add_w₃ {α₃ h₄ : ℂ} {w₃ w₃' : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (h₃' : w₃' ∈ P₃.isMod.weight α₃)
    (hf : SupportedAt P₄.isMod f h₄) (n : ℂ) (k : ℕ) (x : HomPair P₁ P₂) :
    coefFun Y₁ Y₂ f (w₃ + w₃') α₃ h₄ n k x
      = coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x + coefFun Y₁ Y₂ f w₃' α₃ h₄ n k x := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  simp only [coefFun, prodExpCoeff]
  have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
  have e' := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃' hf
  rw [logCoeff_congr hU hs hne (G := fun t =>
      prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t
        + prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃' (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t)
    (fun t ht => by
      have s := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ x.h₁ x.h₂ h₃ hf one_ne_zero
        (one_norm_lt ht)
      have s' := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ x.h₁ x.h₂ h₃' hf one_ne_zero
        (one_norm_lt ht)
      unfold prodFun prodValue
      beta_reduce
      rw [← Summable.tsum_add s s']
      refine tsum_congr fun k => ?_
      simp only [prodCoeff, map_add]
      ring)
    (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ (add_mem h₃ h₃') hf)]
  exact logCoeff_add hU hs hne e e' _ _

omit hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem coefFun_smul_w₃ {α₃ h₄ : ℂ} (c : ℂ) (w₃ : P₃.carrier) {f : P₄.carrier →ₗ[ℂ] ℂ}
    (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (n : ℂ) (k : ℕ)
    (x : HomPair P₁ P₂) :
    coefFun Y₁ Y₂ f (c • w₃) α₃ h₄ n k x = c * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  simp only [coefFun, prodExpCoeff]
  have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
  rw [logCoeff_congr hU hs hne (G := fun t => c *
      prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) t)
    (fun t _ => by
      unfold prodFun prodValue
      beta_reduce
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [prodCoeff, map_smul, smul_eq_mul]
      ring)
    (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ (Submodule.smul_mem _ c h₃) hf)]
  exact logCoeff_smul hU hs hne c e _ _

end Lin

/-! ## Auxiliary identities -/

section Aux

variable {P₁ P₂ : LWModule W}

/-- `Δᵀ(ω_1) = L'(0)` on bilinear functions. -/
theorem copT_conformal_one {G : HomPair P₁ P₂ → ℂ} (hB : IsBilin G) (x : HomPair P₁ P₂) :
    copT W.conformalVector_mem_grading_two 1 G x = L0T P₁ P₂ G x := by
  rw [L0T_apply]
  simp only [copT]
  rw [hB.smulR (pairRight x _ _) x x.α₂ rfl rfl (by simp only [pairRight]; push_cast; ring)
    (by simp only [pairRight]; exact P₂.isMod.L0_weight x.α₂ x.w₂ x.h₂)]
  set L := PzTensorAction.lowBound P₁.h x.α₁ 2 with hLdef
  have hzero : ∀ r : ℕ, L ≤ r →
      G (pairLeft x W.conformalVector_mem_grading_two (r : ℤ)) = 0 := fun r hr =>
    hB.zero_left _ (mode_eq_zero_of_lowBound P₁.isLow x.h₁ W.conformalVector_mem_grading_two hr)
  have hc2 : ∀ r : ℕ, 2 ≤ r → cbz 1 (r : ℤ) = 0 := by
    intro r hr
    rw [cbz_apply_nonneg _ (Int.natCast_nonneg r), Int.toNat_natCast,
      show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num]
    exact VOA.VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega)
  have hsum : ∑ r ∈ Finset.range L, cbz 1 (r : ℤ)
      * G (pairLeft x W.conformalVector_mem_grading_two (r : ℤ))
      = ∑ r ∈ Finset.range 2, cbz 1 (r : ℤ)
        * G (pairLeft x W.conformalVector_mem_grading_two (r : ℤ)) := by
    rw [Finset.sum_subset (Finset.range_subset_range.2 (le_max_left L 2)) (fun r _ hr => by
        rw [Finset.mem_range, not_lt] at hr; rw [hzero r hr, mul_zero]),
      Finset.sum_subset (Finset.range_subset_range.2 (le_max_right L 2)) (fun r _ hr => by
        rw [Finset.mem_range, not_lt] at hr; rw [hc2 r hr, zero_mul])]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_one]
  have c0 : cbz 1 ((0 : ℕ) : ℤ) = 1 := by rw [cbz_apply_nonneg _ (by norm_num)]; simp
  have c1 : cbz 1 ((1 : ℕ) : ℤ) = 1 := by rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
  rw [c0, c1, one_mul, one_mul]
  have e0 : G (pairLeft x W.conformalVector_mem_grading_two ((0 : ℕ) : ℤ)) = G x.lm1 :=
    G_congr G (by simp only [pairLeft, HomPair.lm1]; rfl)
      (by simp only [pairLeft, HomPair.lm1]; push_cast; ring) rfl rfl
  have e1 : G (pairLeft x W.conformalVector_mem_grading_two ((1 : ℕ) : ℤ)) = x.α₁ * G x :=
    hB.smulL _ x x.α₁ (by simp only [pairLeft]; push_cast; ring) rfl rfl
      (by simp only [pairLeft]; push_cast; exact P₁.isMod.L0_weight x.α₁ x.w₁ x.h₁)
  rw [e0, e1]
  ring

/-- `f ∘ L₀ = h f` for a functional supported at `h`. -/
theorem comp_L0 {P : LWModule W} {f : P.carrier →ₗ[ℂ] ℂ} {h : ℂ} (hf : SupportedAt P.isMod f h) :
    f ∘ₗ mode (P.isMod.YM W.conformalVector) 1 = h • f := by
  ext y
  have hy : y ∈ ⨆ α, P.isMod.weight α := mem_iSup_weight P y
  refine Submodule.iSup_induction P.isMod.weight
    (motive := fun y => (f ∘ₗ mode (P.isMod.YM W.conformalVector) 1) y = (h • f) y) hy ?_
    (by simp) ?_
  · intro α z hz
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [P.isMod.L0_weight α z hz, map_smul, smul_eq_mul]
    by_cases hα : α = h
    · rw [hα]
    · rw [hf α hα z hz]; ring
  · intro y z hy hz; rw [map_add, map_add, hy, hz]

theorem finsum_cbz_zero (F : ℤ → ℂ) : ∑ᶠ i : ℤ, cbz 0 i * F i = F 0 := by
  rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_mul])]
  simp

theorem finsum_sgn_cbz_zero (F : ℤ → ℂ) : ∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) * F i = F 0 := by
  rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi]; ring)]
  simp [negOnePow]

theorem finsum_sgn_cbz_one (F : ℤ → ℂ) :
    ∑ᶠ i : ℤ, (negOnePow i * cbz 1 i) * F i = F 0 - F 1 := by
  rw [finsum_eq_Icc' _ 0 1 (fun i hi => by
    rcases hi with hi | hi
    · rw [cbz_neg hi]; ring
    · rw [cbz_nat_lt (by norm_num) hi]; ring)]
  rw [show Finset.Icc (0 : ℤ) 1 = {0, 1} by ext i; simp only [Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]; omega, Finset.sum_pair (by norm_num)]
  have c1 : cbz 1 1 = 1 := by rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
  rw [cbz_zero, c1]
  simp [negOnePow]
  ring

end Aux

/-! ## The construction of `𝒴₃` -/

section Y3

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {R : LWModule W} (χ : coefSpan Y₁ Y₂ →ₗ[ℂ] R.carrier)

/-- `χ(B_γ(f, w₃))`. -/
noncomputable def Bχ (f : P₄.carrier →ₗ[ℂ] ℂ) (w₃ : P₃.carrier) (α₃ h γ : ℂ)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h) : R.carrier :=
  χ ⟨coefFun Y₁ Y₂ f w₃ α₃ h γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩

theorem Bχ_congr {f f' : P₄.carrier →ₗ[ℂ] ℂ} (e : f = f') {w₃ : P₃.carrier} {α₃ h γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h)
    (hf' : SupportedAt P₄.isMod f' h) : Bχ χ f w₃ α₃ h γ h₃ hf = Bχ χ f' w₃ α₃ h γ h₃ hf' := by
  subst e; rfl

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Bχ_add_f {f f' : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier} {α₃ h γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h)
    (hf' : SupportedAt P₄.isMod f' h) (hff : SupportedAt P₄.isMod (f + f') h) :
    Bχ χ (f + f') w₃ α₃ h γ h₃ hff = Bχ χ f w₃ α₃ h γ h₃ hf + Bχ χ f' w₃ α₃ h γ h₃ hf' := by
  unfold Bχ
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext x
  exact coefFun_add_f hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hf' γ 0 x

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Bχ_smul_f (c : ℂ) {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier} {α₃ h γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h)
    (hcf : SupportedAt P₄.isMod (c • f) h) :
    Bχ χ (c • f) w₃ α₃ h γ h₃ hcf = c • Bχ χ f w₃ α₃ h γ h₃ hf := by
  unfold Bχ
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext x
  exact coefFun_smul_f c f hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0 x

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Bχ_add_w {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ w₃' : P₃.carrier} {α₃ h γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (h₃' : w₃' ∈ P₃.isMod.weight α₃)
    (hf : SupportedAt P₄.isMod f h) :
    Bχ χ f (w₃ + w₃') α₃ h γ (add_mem h₃ h₃') hf
      = Bχ χ f w₃ α₃ h γ h₃ hf + Bχ χ f w₃' α₃ h γ h₃' hf := by
  unfold Bχ
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext x
  exact coefFun_add_w₃ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ h₃' hf γ 0 x

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Bχ_smul_w (c : ℂ) {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier} {α₃ h γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h) :
    Bχ χ f (c • w₃) α₃ h γ (Submodule.smul_mem _ c h₃) hf = c • Bχ χ f w₃ α₃ h γ h₃ hf := by
  unfold Bχ
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext x
  exact coefFun_smul_w₃ c w₃ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0 x

theorem supp_add {f f' : P₄.carrier →ₗ[ℂ] ℂ} {h : ℂ} (hf : SupportedAt P₄.isMod f h)
    (hf' : SupportedAt P₄.isMod f' h) : SupportedAt P₄.isMod (f + f') h := fun α hα y hy => by
  rw [LinearMap.add_apply, hf α hα y hy, hf' α hα y hy, add_zero]

theorem supp_smul (c : ℂ) {f : P₄.carrier →ₗ[ℂ] ℂ} {h : ℂ} (hf : SupportedAt P₄.isMod f h) :
    SupportedAt P₄.isMod (c • f) h := fun α hα y hy => by
  rw [LinearMap.smul_apply, hf α hα y hy, smul_zero]

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- The functional `g ↦ ⟨χ B_γ(g ∘ proj_h, w), ξ⟩` on `P₄(h)*`. -/
noncomputable def Phi (h γ α₃ : ℂ) (ξ : RestrictedDual R.isMod) (w : P₃.isMod.weight α₃) :
    Module.Dual ℂ (Module.Dual ℂ (P₄.isMod.weight h)) where
  toFun g := dualPairing R.isMod (Bχ χ (extF h g) w.1 α₃ h γ w.2 (extF_supported h g)) ξ
  map_add' g g' := by
    have e : extF h (g + g') = extF h g + extF h g' := LinearMap.add_comp _ _ _
    rw [Bχ_congr χ e w.2 (extF_supported h (g + g'))
      (supp_add (extF_supported h g) (extF_supported h g')),
      Bχ_add_f hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ w.2 (extF_supported h g) (extF_supported h g'),
      dualPairing_add_x]
  map_smul' c g := by
    have e : extF h (c • g) = c • extF h g := LinearMap.smul_comp _ _ _
    rw [Bχ_congr χ e w.2 (extF_supported h (c • g)) (supp_smul c (extF_supported h g)),
      Bχ_smul_f hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ c w.2 (extF_supported h g),
      dualPairing_smul_x, RingHom.id_apply, smul_eq_mul]

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- The block of `𝒴₃(·)_n ·` on `R'_γ × P₃(α₃)`, valued in `P₄(γ + α₃ − n − 1)`. -/
noncomputable def block3 (n γ α₃ : ℂ) :
    (contraLW R).isMod.weight γ →ₗ[ℂ] P₃.isMod.weight α₃ →ₗ[ℂ] P₄.carrier :=
  letI : FiniteDimensional ℂ (P₄.isMod.weight (γ + α₃ - n - 1)) := P₄.isMod.finrank _
  LinearMap.mk₂ ℂ
    (fun ξ w => ((Module.evalEquiv ℂ (P₄.isMod.weight (γ + α₃ - n - 1))).symm
      (Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w) : P₄.carrier))
    (fun ξ ξ' w => by
      have : Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ (ξ + ξ').1 w
          = Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w
            + Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ'.1 w := by
        ext g; simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          Submodule.coe_add]
        exact map_add _ _ _
      dsimp only
      rw [this, map_add, Submodule.coe_add])
    (fun c ξ w => by
      have : Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ (c • ξ).1 w
          = c • Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w := by
        ext g; simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          Submodule.coe_smul, smul_eq_mul]
        exact (map_smul _ _ _).trans (smul_eq_mul _ _)
      dsimp only
      rw [this, map_smul, Submodule.coe_smul])
    (fun ξ w w' => by
      have : Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 (w + w')
          = Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w
            + Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w' := by
        ext g
        simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
        rw [show Bχ χ (extF (γ + α₃ - n - 1) g) (w + w').1 α₃ (γ + α₃ - n - 1) γ (w + w').2
            (extF_supported _ g) = Bχ χ (extF (γ + α₃ - n - 1) g) (w.1 + w'.1) α₃
            (γ + α₃ - n - 1) γ (add_mem w.2 w'.2) (extF_supported _ g) from rfl,
          Bχ_add_w hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ w.2 w'.2 (extF_supported _ g), dualPairing_add_x]
      dsimp only
      rw [this, map_add, Submodule.coe_add])
    (fun c ξ w => by
      have : Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 (c • w)
          = c • Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ.1 w := by
        ext g
        simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]
        rw [show Bχ χ (extF (γ + α₃ - n - 1) g) (c • w).1 α₃ (γ + α₃ - n - 1) γ (c • w).2
            (extF_supported _ g) = Bχ χ (extF (γ + α₃ - n - 1) g) (c • w.1) α₃
            (γ + α₃ - n - 1) γ (Submodule.smul_mem _ c w.2) (extF_supported _ g) from rfl,
          Bχ_smul_w hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ c w.2 (extF_supported _ g), dualPairing_smul_x]
      dsimp only
      rw [this, map_smul, Submodule.coe_smul])

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- **The second iterate intertwiner** `𝒴₃ : R' ⊗ P₃ → P₄{x}`. -/
noncomputable def Y3 : IntertwiningModes (contraLW R).carrier P₃.carrier P₄.carrier :=
  fun n => biHat (block3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ n)

/-- **The pairing of `𝒴₃` with `P₄*`.** -/
theorem pair_Y3 (n : ℂ) {γ α₃ h' : ℂ} {ξ : (contraLW R).carrier}
    (hξ : ξ ∈ (contraLW R).isMod.weight γ) {w₃ : P₃.carrier} (h₃ : w₃ ∈ P₃.isMod.weight α₃)
    {f : P₄.carrier →ₗ[ℂ] ℂ} (hf : SupportedAt P₄.isMod f h') :
    f (Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ n ξ w₃)
      = if h' = γ + α₃ - n - 1 then dualPairing R.isMod (Bχ χ f w₃ α₃ h' γ h₃ hf) ξ else 0 := by
  letI : FiniteDimensional ℂ (P₄.isMod.weight (γ + α₃ - n - 1)) := P₄.isMod.finrank _
  rw [Y3, biHat_homog _ hξ h₃]
  simp only [block3, LinearMap.mk₂_apply]
  set v := (Module.evalEquiv ℂ (P₄.isMod.weight (γ + α₃ - n - 1))).symm
    (Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ ⟨w₃, h₃⟩) with hv
  split_ifs with h
  · subst h
    have e := Module.apply_evalEquiv_symm_apply ℂ (P₄.isMod.weight (γ + α₃ - n - 1))
      (f ∘ₗ (P₄.isMod.weight (γ + α₃ - n - 1)).subtype)
      (Phi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (γ + α₃ - n - 1) γ α₃ ξ ⟨w₃, h₃⟩)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
    rw [← hv] at e
    rw [e]
    simp only [Phi, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Bχ_congr χ (extF_restrict hf) h₃ _ hf]
  · exact hf _ (Ne.symm h) _ v.2

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- **The `L₋₁`-identity of the coefficient functions**: on log-free coefficient functions,
`Δᵀ(ω₀) B_{γ+1}(f, w₃) = (h − α₃ − γ) B_γ(f, w₃)`. -/
theorem copT_Lm1_B {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier} {α₃ hh γ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f hh)
    (hlog : coefFun Y₁ Y₂ f w₃ α₃ hh γ 1 = 0) (x : HomPair P₁ P₂) :
    copT W.conformalVector_mem_grading_two 0 (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + 1) 0) x
      = (hh - α₃ - γ) * coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 x := by
  have hω := W.conformalVector_mem_grading_two
  have E0 := outE_eq_zero hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hω γ 0 x 0 0
  have E1 := outE_eq_zero hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hω γ 0 x 1 0
  unfold OE at E0 E1
  simp only [finsum_cbz_zero, finsum_sgn_cbz_zero, finsum_sgn_cbz_one] at E0 E1
  -- `X(1) = h B`, `Y(1) = α₃ B`, `Z(1) = γ B`
  have eX1 : coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM W.conformalVector) (1 + 0 - 0)) w₃ α₃
      (hh - ((2 : ℤ) : ℂ) + ((1 + 0 - 0 : ℤ) : ℂ) + 1) γ 0 x
      = hh * coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 x := by
    rw [show (1 + 0 - 0 : ℤ) = 1 by ring, comp_L0 hf,
      show hh - ((2 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) + 1 = hh by push_cast; ring]
    exact coefFun_smul_f hh f hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0 x
  have eY1 : coefFun Y₁ Y₂ f (mode (P₃.isMod.YM W.conformalVector) (0 + 1) w₃)
      (α₃ + ((2 : ℤ) : ℂ) - ((0 + 1 : ℤ) : ℂ) - 1) hh γ 0 x
      = α₃ * coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 x := by
    rw [show (0 + 1 : ℤ) = 1 by ring, P₃.isMod.L0_weight α₃ w₃ h₃,
      show α₃ + ((2 : ℤ) : ℂ) - ((1 : ℤ) : ℂ) - 1 = α₃ by push_cast; ring]
    exact coefFun_smul_w₃ α₃ w₃ hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0 x
  have eZ1 : copT hω (1 + 0) (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + ((2 : ℤ) : ℂ)
      - ((1 + 0 : ℤ) : ℂ) - 1) 0) x = γ * coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 x := by
    rw [show (1 + 0 : ℤ) = 1 by ring, show γ + ((2 : ℤ) : ℂ) - ((1 : ℤ) : ℂ) - 1 = γ by
      push_cast; ring, copT_conformal_one (coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0)]
    have hL := congrFun (L0T_coefFun hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0) x
    rw [hL, hlog]
    simp
  have eZ0 : copT hω (0 + 0) (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + ((2 : ℤ) : ℂ)
      - ((0 + 0 : ℤ) : ℂ) - 1) 0) x
      = copT W.conformalVector_mem_grading_two 0 (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + 1) 0) x := by
    rw [show (0 + 0 : ℤ) = 0 by ring, show γ + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = γ + 1 by
      push_cast; ring]
  rw [eX1, eY1, eZ1] at E1
  rw [eZ0] at E0
  have hs1 : negOnePow 1 = -1 := by simp [negOnePow]
  have hs0 : negOnePow 0 = 1 := by simp [negOnePow]
  rw [hs1] at E1
  rw [hs0] at E0
  simp only [show (1 + 0 - 1 : ℤ) = 0 by ring, show (0 + 0 : ℤ) = 0 by ring, sub_zero]
    at E0 E1
  linear_combination -E0 - E1

/-- `χ` intertwines the Huang–Lepowsky action with the module action of `R`. -/
def TauProj : Prop :=
  ∀ (G : coefSpan Y₁ Y₂) (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (k : ℤ)
    (hm : tauHom hu k (G : HomPair P₁ P₂ → ℂ) ∈ coefSpan Y₁ Y₂),
    χ ⟨tauHom hu k (G : HomPair P₁ P₂ → ℂ), hm⟩ = mode (R.isMod.YM u) k (χ G)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- **The contragredient action through `χ`** (double twist):
`⟨χ B, u'_k ξ⟩ = ⟨χ Δᵀ(u_k) B, ξ⟩`. -/
theorem pair_mode_chi (hP : TauProj χ) {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier}
    {α₃ hh γ : ℂ} (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f hh)
    {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (k : ℤ) (ξ : RestrictedDual R.isMod) :
    dualPairing R.isMod (χ ⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩)
        (mode ((contragredientModule R.isMod).YM u) k ξ)
      = dualPairing R.isMod (χ ⟨copT hu k (coefFun Y₁ Y₂ f w₃ α₃ hh γ 0),
          copT_coefFun_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0 hu k⟩) ξ := by
  rw [pair_mode hu k]
  set B : coefSpan Y₁ Y₂ := ⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0, coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩
  set Λ : coefSpan Y₁ Y₂ →ₗ[ℂ] ℂ := (dualPairingFlip R.isMod ξ) ∘ₗ χ with hΛ
  have hmem : ∀ j : ℕ, tauHom (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)
      (2 * wt - k - 2 - (j : ℤ)) (B : HomPair P₁ P₂ → ℂ) ∈ coefSpan Y₁ Y₂ := fun j =>
    tauHom_mem_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ B.2 _ _
  have e1 : ∀ j : ℕ, dualPairing R.isMod (mode (R.isMod.YM ((W.L 1 ^ j) u))
      (2 * wt - k - 2 - (j : ℤ)) (χ B)) ξ
      = Λ ⟨_, hmem j⟩ := by
    intro j
    rw [← hP B _ _ (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) _ (hmem j)]
    rfl
  simp only [e1]
  have e2 : (-1 : ℂ) ^ wt * ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) *
      Λ ⟨_, hmem j⟩ = Λ ((-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
        ((j.factorial : ℂ)⁻¹) • (⟨_, hmem j⟩ : coefSpan Y₁ Y₂)) := by
    rw [map_smul, map_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [e2]
  change Λ _ = Λ _
  congr 1
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  exact twist_twist_fn (coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf γ 0) hu k x

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Y3_mem (n : ℂ) {γ α₃ : ℂ} {ξ : (contraLW R).carrier}
    (hξ : ξ ∈ (contraLW R).isMod.weight γ) {w₃ : P₃.carrier} (h₃ : w₃ ∈ P₃.isMod.weight α₃) :
    Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ n ξ w₃ ∈ P₄.isMod.weight (γ + α₃ - n - 1) := by
  rw [Y3, biHat_homog _ hξ h₃]
  simp only [block3, LinearMap.mk₂_apply]
  exact Submodule.coe_mem _

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Y3_trunc (ξ : (contraLW R).carrier) (w₃ : P₃.carrier) (n : ℂ) :
    ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n + k) ξ w₃ = 0 := by
  obtain ⟨B, hB⟩ := P₄.isMod.boundedBelow
  refine Submodule.iSup_induction (contraLW R).isMod.weight
    (motive := fun ξ => ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n + k) ξ w₃ = 0)
    (mem_iSup_weight (contraLW R) ξ) ?_ ⟨0, fun k _ => by simp⟩ ?_
  · intro γ y hy
    refine Submodule.iSup_induction P₃.isMod.weight
      (motive := fun w => ∃ N : ℤ, ∀ k : ℤ, N ≤ k →
        Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n + k) y w = 0)
      (mem_iSup_weight P₃ w₃) ?_ ⟨0, fun k _ => by simp⟩ ?_
    · intro α₃ z hz
      set c : ℤ := ⌈(γ + α₃ - n - 1).re - B⌉ with hc
      have hc' : (γ + α₃ - n - 1).re - B ≤ (c : ℝ) := Int.le_ceil _
      refine ⟨c + 1, fun k hk => ?_⟩
      have hmem := Y3_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n + k) hy hz
      have hbot : P₄.isMod.weight (γ + α₃ - (n + k) - 1) = ⊥ := by
        by_contra hne
        have h1 := hB _ hne
        have h3 : ((c + 1 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at h1 hc'
        push_cast at h3
        linarith
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    · rintro z z' ⟨N, hN⟩ ⟨N', hN'⟩
      exact ⟨max N N', fun k hk => by
        rw [map_add, hN k (le_trans (le_max_left _ _) hk), hN' k (le_trans (le_max_right _ _) hk),
          add_zero]⟩
  · rintro y y' ⟨N, hN⟩ ⟨N', hN'⟩
    exact ⟨max N N', fun k hk => by
      rw [map_add, LinearMap.add_apply, hN k (le_trans (le_max_left _ _) hk),
        hN' k (le_trans (le_max_right _ _) hk), add_zero]⟩

/-- Log-freeness of the coefficient functions (`B_{γ,1} = 0`; a consequence of log removal). -/
def LogFree : Prop :=
  ∀ (f : P₄.carrier →ₗ[ℂ] ℂ) (w₃ : P₃.carrier) (α₃ hh γ : ℂ), w₃ ∈ P₃.isMod.weight α₃ →
    SupportedAt P₄.isMod f hh → coefFun Y₁ Y₂ f w₃ α₃ hh γ 1 = 0

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
theorem Y3_L_homog (hP : TauProj χ) (hlog : LogFree (Y₁ := Y₁) (Y₂ := Y₂)) {γ α₃ : ℂ}
    {ξ : (contraLW R).carrier} {w₃ : P₃.carrier} (hξ : ξ ∈ (contraLW R).isMod.weight γ)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (n : ℂ) :
    Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ n ((contraLW R).isMod.Lm1 ξ) w₃
      = (-n) • Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n - 1) ξ w₃ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_supported fun hh f hf => ?_
  rw [map_sub, map_smul, smul_eq_mul, pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ n
      (Lm1_mem_weight' (contraLW R).isMod hξ) h₃ hf,
    pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n - 1) hξ h₃ hf]
  have hc : (hh = γ + 1 + α₃ - n - 1) ↔ (hh = γ + α₃ - (n - 1) - 1) := by
    constructor <;> intro h <;> rw [h] <;> ring
  by_cases h : hh = γ + α₃ - (n - 1) - 1
  · rw [if_pos (hc.mpr h), if_pos h]
    have hL : (contraLW R).isMod.Lm1 ξ
        = mode ((contragredientModule R.isMod).YM W.conformalVector) 0 ξ := rfl
    rw [hL, Bχ, pair_mode_chi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ hP h₃ hf
      W.conformalVector_mem_grading_two 0 ξ]
    have hfun : copT W.conformalVector_mem_grading_two 0 (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + 1) 0)
        = (hh - α₃ - γ) • coefFun Y₁ Y₂ f w₃ α₃ hh γ 0 := by
      funext x
      rw [copT_Lm1_B hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf (hlog f w₃ α₃ hh γ h₃ hf) x]
      rfl
    have hel : (⟨copT W.conformalVector_mem_grading_two 0 (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + 1) 0),
        copT_coefFun_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf (γ + 1) 0
          W.conformalVector_mem_grading_two 0⟩ : coefSpan Y₁ Y₂)
        = (hh - α₃ - γ) • (⟨coefFun Y₁ Y₂ f w₃ α₃ hh γ 0,
          coefFun_mem_coefSpan Y₁ Y₂ h₃ hf γ 0⟩ : coefSpan Y₁ Y₂) :=
      Subtype.ext hfun
    rw [hel, map_smul, dualPairing_smul_x, Bχ]
    have hn : hh - α₃ - γ = -n := by rw [h]; ring
    rw [hn]
    ring
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
    ring

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- **The Jacobi identity of `𝒴₃`** on homogeneous data: it is the outside Borcherds identity
of the coefficient functions transported by `χ`. -/
theorem Y3_jac_homog (hP : TauProj χ) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) {γ α₃ : ℂ}
    {ξ : (contraLW R).carrier} {w₃ : P₃.carrier} (hξ : ξ ∈ (contraLW R).isMod.weight γ)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (ℓ m : ℤ) (n : ℂ) :
    JacAt (P₁ := contraLW R) (P₂ := P₃) P₄.isMod (Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ) u ξ w₃ ℓ m n := by
  unfold JacAt
  rw [← sub_eq_zero]
  refine eq_zero_of_supported fun hh f hf => ?_
  set Y := Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ with hYdef
  have htr := Y3_trunc hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ
  have hfinL := IsIntertwiningOperator.jacL_support_finite (A₂ := P₃.isMod) (A₃ := P₄.isMod)
    htr u ξ w₃ ℓ m n
  have hfinR := IsIntertwiningOperator.jacR_support_finite (A₁ := (contraLW R).isMod) Y u ξ w₃ ℓ m n
  change f (∑ᶠ i, IsIntertwiningOperator.jacL P₃.isMod P₄.isMod Y u ξ w₃ ℓ m n i
    - ∑ᶠ i, IsIntertwiningOperator.jacR (contraLW R).isMod Y u ξ w₃ ℓ m n i) = 0
  rw [map_sub, map_finsum f hfinL, map_finsum f hfinR]
  set Λ : coefSpan Y₁ Y₂ →ₗ[ℂ] ℂ := (dualPairingFlip R.isMod ξ) ∘ₗ χ with hΛ
  set h₀ : ℂ := γ + α₃ + wt - ℓ - m - n - 2 with hh₀
  -- the three families of coefficient functions
  let Xe : ℤ → coefSpan Y₁ Y₂ := fun i =>
    ⟨coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ + m - i)) w₃ α₃
      (hh - wt + ((ℓ + m - i : ℤ) : ℂ) + 1) γ 0,
      coefFun_mem_coefSpan Y₁ Y₂ h₃ (supportedAt_comp_mode hf hu (ℓ + m - i)) γ 0⟩
  let Ye : ℤ → coefSpan Y₁ Y₂ := fun i =>
    ⟨coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) (m + i) w₃) (α₃ + wt - ((m + i : ℤ) : ℂ) - 1) hh γ 0,
      coefFun_mem_coefSpan Y₁ Y₂ (VOA.mode_mem_weight P₃.isMod hu h₃ (m + i)) hf γ 0⟩
  let Ze : ℤ → coefSpan Y₁ Y₂ := fun i =>
    ⟨copT hu (ℓ + i) (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + wt - ((ℓ + i : ℤ) : ℂ) - 1) 0),
      copT_coefFun_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf _ 0 hu (ℓ + i)⟩
  -- the pairings
  have hT : ∀ i : ℤ, f (IsIntertwiningOperator.jacL P₃.isMod P₄.isMod Y u ξ w₃ ℓ m n i)
      = if hh = h₀ then (negOnePow i * cbz ℓ i) * (Λ (Xe i) - negOnePow ℓ * Λ (Ye i)) else 0 := by
    intro i
    simp only [IsIntertwiningOperator.jacL, map_smul, map_sub, smul_eq_mul]
    rw [show f (mode (P₄.isMod.YM u) (ℓ + m - i) (Y (n + i) ξ w₃))
        = (f ∘ₗ mode (P₄.isMod.YM u) (ℓ + m - i)) (Y (n + i) ξ w₃) from rfl,
      hYdef, pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (n + i) hξ h₃
        (supportedAt_comp_mode hf hu (ℓ + m - i)),
      pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (ℓ + n - i) hξ
        (VOA.mode_mem_weight P₃.isMod hu h₃ (m + i)) hf]
    have c1 : (hh - wt + ((ℓ + m - i : ℤ) : ℂ) + 1 = γ + α₃ - (n + i) - 1) ↔ hh = h₀ := by
      rw [hh₀]; push_cast; constructor <;> intro h <;> linear_combination h
    have c2 : (hh = γ + (α₃ + wt - ((m + i : ℤ) : ℂ) - 1) - (ℓ + n - i) - 1) ↔ hh = h₀ := by
      rw [hh₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : hh = h₀
    · rw [if_pos (c1.mpr h), if_pos (c2.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (c1.mp h')), if_neg (fun h' => h (c2.mp h')), if_neg h]; ring
  have hR : ∀ i : ℤ, f (IsIntertwiningOperator.jacR (contraLW R).isMod Y u ξ w₃ ℓ m n i)
      = if hh = h₀ then cbz m i * Λ (Ze i) else 0 := by
    intro i
    simp only [IsIntertwiningOperator.jacR, map_smul, smul_eq_mul]
    have hξ' := VOA.mode_mem_weight (contraLW R).isMod hu hξ (ℓ + i)
    rw [hYdef, pair_Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ (m + n - i) hξ' h₃ hf]
    have c3 : (hh = γ + wt - ((ℓ + i : ℤ) : ℂ) - 1 + α₃ - (m + n - i) - 1) ↔ hh = h₀ := by
      rw [hh₀]; push_cast; constructor <;> intro h <;> linear_combination h
    by_cases h : hh = h₀
    · rw [if_pos (c3.mpr h), if_pos h, Bχ]
      change cbz m i * dualPairing R.isMod _ (mode ((contragredientModule R.isMod).YM u) _ ξ) = _
      rw [pair_mode_chi hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ hP h₃ hf hu (ℓ + i) ξ]
      rfl
    · rw [if_neg (fun h' => h (c3.mp h')), if_neg h, mul_zero]
  rw [finsum_congr hT, finsum_congr hR]
  by_cases h : hh = h₀
  swap
  · simp only [if_neg h, finsum_zero, sub_self]
  simp only [if_pos h]
  -- vanishing bounds
  obtain ⟨NA, hNA⟩ := exists_comp_mode_vanish P₄.isLow hf hu (ℓ + m)
  obtain ⟨N₃, hN₃⟩ := P₃.isMod.truncation u w₃
  obtain ⟨M, hM⟩ := VOA.Huang.LogRemovalWeightBound.coefFun_eq_zero_of_re_lt hV i₁ i₂ i₃ i₄ iQ
    hY₁ hY₂
  obtain ⟨IL, hIL⟩ := exists_int_gt (γ.re + wt - 1 - (M - α₃.re - hh.re))
  set K : ℤ := max (max (NA : ℤ) (N₃ - m)) (max (IL - ℓ) 0) with hK
  have hX0 : ∀ i : ℤ, K < i → Xe i = 0 := by
    intro i hi
    have h0 : f ∘ₗ mode (P₄.isMod.YM u) (ℓ + m - i) = 0 := by
      have := hNA i.toNat (by omega)
      rwa [Int.toNat_of_nonneg (by omega)] at this
    apply Subtype.ext
    funext x
    exact coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inr h0)))
  have hY0 : ∀ i : ℤ, K < i → Ye i = 0 := by
    intro i hi
    apply Subtype.ext
    funext x
    exact coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inl (hN₃ _ (by omega)))))
  have hZ0 : ∀ i : ℤ, K < i → Ze i = 0 := by
    intro i hi
    apply Subtype.ext
    have hz : coefFun Y₁ Y₂ f w₃ α₃ hh (γ + wt - ((ℓ + i : ℤ) : ℂ) - 1) 0 = 0 := by
      refine hM α₃ hh w₃ f h₃ hf _ 0 ?_
      have : (IL : ℝ) ≤ ((ℓ + i : ℤ) : ℝ) := by exact_mod_cast (show IL ≤ ℓ + i by omega)
      simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
      push_cast at this ⊢
      linarith
    change copT hu (ℓ + i) (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + wt - ((ℓ + i : ℤ) : ℂ) - 1) 0) = 0
    rw [hz]
    funext x
    simp [copT]
  rw [finsum_eq_Icc' _ 0 K (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hX0 i hi, hY0 i hi, map_zero]; ring),
    finsum_eq_Icc' _ 0 K (fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hZ0 i hi, map_zero]; ring),
    ← Finset.sum_sub_distrib]
  have hlin : ∀ i : ℤ, (negOnePow i * cbz ℓ i) * (Λ (Xe i) - negOnePow ℓ * Λ (Ye i))
      - cbz m i * Λ (Ze i)
      = Λ ((negOnePow i * cbz ℓ i) • (Xe i - negOnePow ℓ • Ye i) - cbz m i • Ze i) := by
    intro i
    simp only [map_sub, map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hlin i, ← map_sum]
  have hE : ∑ i ∈ Finset.Icc 0 K,
      ((negOnePow i * cbz ℓ i) • (Xe i - negOnePow ℓ • Ye i) - cbz m i • Ze i) = 0 := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Submodule.coe_sub, Submodule.coe_smul, Finset.sum_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
    have hO := outE_eq_zero hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hu γ 0 x ℓ m
    unfold OE at hO
    rw [finsum_eq_Icc' _ 0 K (fun i hi => by
        dsimp only
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have h0 : coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ + m - i)) w₃ α₃
              (hh - wt + ((ℓ + m - i : ℤ) : ℂ) + 1) γ 0 = 0 := congrArg Subtype.val (hX0 i hi)
          rw [h0]; simp),
      finsum_eq_Icc' _ 0 K (fun i hi => by
        dsimp only
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have h0 : coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) (m + i) w₃)
              (α₃ + wt - ((m + i : ℤ) : ℂ) - 1) hh γ 0 = 0 := congrArg Subtype.val (hY0 i hi)
          rw [h0]; simp),
      finsum_eq_Icc' _ 0 K (fun i hi => by
        dsimp only
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have h0 : copT hu (ℓ + i) (coefFun Y₁ Y₂ f w₃ α₃ hh (γ + wt - ((ℓ + i : ℤ) : ℂ) - 1) 0)
              = 0 := congrArg Subtype.val (hZ0 i hi)
          rw [h0]; simp)] at hO
    rw [← hO, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hE, map_zero]

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ in
/-- **`𝒴₃` is an intertwining operator** of type `(P₄ / R' P₃)`, given that `χ` intertwines
`τ` with the action on `R` and the coefficient functions are log-free. -/
theorem isIntertwining_Y3 (hP : TauProj χ) (hlog : LogFree (Y₁ := Y₁) (Y₂ := Y₂)) :
    IsIntertwiningOperator (contraLW R).isMod P₃.isMod P₄.isMod
      (Y3 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ) :=
  isIntertwining_of_homog (P₁ := contraLW R) (P₂ := P₃)
    (Y3_trunc hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ)
    (fun _ _ _ _ hy hz n => Y3_L_homog hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ hP hlog hy hz n)
    (fun _ _ hu _ _ _ _ hy hz ℓ m n => Y3_jac_homog hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ χ hP hu hy hz ℓ m n)

end Y3

end VOA.Huang.PzTensorY3
