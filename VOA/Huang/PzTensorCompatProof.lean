/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorCompat

/-!
# The left associator on expansion coefficients, and `CoeffCompat`

The left associator identity `AssocAssociator.prodValueZ_assoc_left` (the residue theorem for
`(ζ − z₁)^ℓ`, values at `z₂ = 1`, `z₁ = 1 + u`) is transferred to the expansion coefficients at
the iterate point (`coefFun_assoc_left_holds`; the factors `z₁^N = (1+u)^N` become the binomial
Cauchy products `binPS N`, the factors `(z₁ − 1)^{ℓ−j} = u^{ℓ−j}` index shifts).  Combined with
the right associator (`AssocTauStable.coefFun_coproduct_holds`), the trinomial identities and the
weight bound (`LogRemovalWeightBound.coefFun_eq_zero_of_re_lt`), this gives the
`P(1)`-compatibility of every coefficient function: `coeffCompat_holds : StronglyRational W →
CoeffCompat W`.

## Main results
* `coeff_binPS` — the coefficients of `(1 + X)^N`, `N ∈ ℤ`, are the generalized binomials.
* `prodFunZ_assoc_left_holds`, `logCoeff_assoc_left_holds`, `coefFun_assoc_left_holds`.
* `coeffCompat_holds`; `coeffWeakInput_of_HLZ544`, `associativityInput_of_HLZ544`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorCompatProof

open VOA PowerSeries VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.AssocCommutator VOA.Huang.AssocAssociator
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorCompat
open VOA.Huang.HuangODEAlgebra
open VOA.Huang.FrobeniusLog (psEval)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## The coefficients of `(1 + X)^N` -/

theorem one_add_X_mul_geom : (1 + X : PowerSeries ℂ) * geom (-1) = 1 := by
  have := one_sub_mul_geom (-1)
  simpa [sub_eq_add_neg] using this

theorem one_add_X_mul_binPS (N : ℤ) : (1 + X : PowerSeries ℂ) * binPS N = binPS (N + 1) := by
  unfold binPS
  by_cases hN : 0 ≤ N
  · rw [if_pos hN, if_pos (by omega), ← pow_succ',
      show (N + 1).toNat = N.toNat + 1 by omega]
  · rw [if_neg hN]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (-N).toNat = m + 1 := ⟨(-N).toNat - 1, by omega⟩
    rw [hm, pow_succ', ← mul_assoc, one_add_X_mul_geom, one_mul]
    by_cases hN1 : 0 ≤ N + 1
    · rw [if_pos hN1, show (N + 1).toNat = 0 by omega, show m = 0 by omega, pow_zero, pow_zero]
    · rw [if_neg hN1, show (-(N + 1)).toNat = m by omega]

theorem coeff_one_add_X_mul (P : PowerSeries ℂ) (s : ℕ) :
    coeff (s + 1) ((1 + X) * P) = coeff (s + 1) P + coeff s P := by
  rw [add_mul, one_mul, map_add, coeff_succ_X_mul]

theorem coeff_zero_one_add_X_mul (P : PowerSeries ℂ) :
    coeff 0 ((1 + X) * P) = coeff 0 P := by
  rw [add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero]

/-- The coefficients of `(1 + X)^N`, `N ∈ ℤ`, are the generalized binomial coefficients. -/
theorem coeff_binPS (N : ℤ) (s : ℕ) : coeff s (binPS N) = cbz N s := by
  induction N using Int.induction_on generalizing s with
  | zero =>
    rw [show binPS 0 = 1 by simp [binPS], coeff_one, cbz_zero_left]
    by_cases hs : s = 0
    · subst hs; simp
    · rw [if_neg hs, if_neg (by exact_mod_cast hs)]
  | succ N ih =>
    rw [← one_add_X_mul_binPS]
    cases s with
    | zero =>
      rw [coeff_zero_one_add_X_mul, ih, cbz_pascal_up,
        cbz_apply_neg (N : ℤ) (show ((0 : ℕ) : ℤ) - 1 < 0 by norm_num), add_zero]
    | succ s =>
      rw [coeff_one_add_X_mul, ih, ih, cbz_pascal_up]
      push_cast
      ring_nf
  | pred N ih =>
    induction s with
    | zero =>
      have h := coeff_zero_one_add_X_mul (binPS (-(N : ℤ) - 1))
      rw [one_add_X_mul_binPS, show -(N : ℤ) - 1 + 1 = -N by ring, ih] at h
      rw [← h]
      have hp := cbz_pascal_up (-(N : ℤ) - 1) 0
      rw [show -(N : ℤ) - 1 + 1 = -N by ring,
        cbz_apply_neg (-(N : ℤ) - 1) (show (0 : ℤ) - 1 < 0 by norm_num), add_zero] at hp
      exact_mod_cast hp
    | succ s ihs =>
      have h := coeff_one_add_X_mul (binPS (-(N : ℤ) - 1)) s
      rw [one_add_X_mul_binPS, show -(N : ℤ) - 1 + 1 = -N by ring, ih, ihs] at h
      have := cbz_pascal_up (-(N : ℤ) - 1) ((s + 1 : ℕ) : ℤ)
      rw [show -(N : ℤ) - 1 + 1 = -N by ring,
        show ((s + 1 : ℕ) : ℤ) - 1 = (s : ℤ) by push_cast; ring]
        at this
      linear_combination this - h

/-! ## The left associator on functions and on coefficients -/

section Holds

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
  {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
  {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
include hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hu

/-- **The left associator identity at `z₂ = 1`, `z₁ = 1 + e^t`** (functions on the overlap
domain), all summability discharged. -/
theorem prodFunZ_assoc_left_holds (ℓ : ℤ) {NA N₂ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i) = 0)
    (hN₂ : ∀ j : ℕ, N₂ ≤ j → mode (P₂.isMod.YM u) j w₂ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) :
    ∀ t ∈ overlapDomain,
    prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) ℓ w₁) w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1) (α₂ + α₃ - 1 - Q.h) t
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * (psEval (binPS (i : ℤ)) (Complex.exp t)
            * prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) w₁ w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((i : ℤ) : ℂ)) (α₂ + α₃ - 1 - Q.h) t)
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * (psEval (binPS (ℓ - i)) (Complex.exp t)
            * prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - i : ℤ) : ℂ)) (α₂ + α₃ - 1 - Q.h) t)
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j
          * (Complex.exp (((ℓ - j : ℤ) : ℂ) * t)
            * prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) j w₂) w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - j : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h - j) t) := by
  intro t ht
  have hz : 1 < ‖1 + Complex.exp t‖ := one_lt_norm ht
  have hz₂ : (1 : ℂ) ≠ 0 := one_ne_zero
  have hz' : ‖(1 : ℂ)‖ < ‖1 + Complex.exp t‖ := by rw [norm_one]; exact hz
  unfold prodFunZ
  rw [prodValueZ_assoc_left hY₁ hY₂ u ℓ f w₁ w₂ w₃ hNA hN₂ hN₃ _ _ _ hz
    (fun i => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃
      (supportedAt_comp_mode hf hu (ℓ - i)) (by push_cast; ring) 0 (by push_cast; ring) hz₂ hz')
    (fun i => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hu h₃ i) hf (by push_cast; ring) (i + 1 - β)
      (by push_cast; ring) hz₂ hz')
    (fun j => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hu h₂ j) h₃ hf (by push_cast; ring) (1 - β)
      (by push_cast; ring) hz₂ hz')]
  have ep : ∀ N : ℤ, (1 + Complex.exp t) ^ N = psEval (binPS N) (Complex.exp t) := fun N =>
    (psEval_binPS N (norm_exp_lt_one ht)).symm
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ep]; ring
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ep]; ring
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_sub_cancel_left, ← Complex.exp_int_mul]
    ring

end Holds

section HoldsCoeff

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
  {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
  {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf hu

/-- **The left associator identity on expansion coefficients.** -/
theorem logCoeff_assoc_left_holds (ℓ : ℤ) {NA N₂ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i) = 0)
    (hN₂ : ∀ j : ℕ, N₂ ≤ j → mode (P₂.isMod.YM u) j w₂ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) (μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) ℓ w₁) w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1) (α₂ + α₃ - 1 - Q.h)) μ k
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * ∑ᶠ s : ℕ, coeff s (binPS (i : ℤ))
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) w₁ w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((i : ℤ) : ℂ)) (α₂ + α₃ - 1 - Q.h)) (μ - s) k
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * ∑ᶠ s : ℕ, coeff s (binPS (ℓ - i))
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - i : ℤ) : ℂ)) (α₂ + α₃ - 1 - Q.h))
              (μ - s) k
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j
          * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) j w₂) w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - j : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h - j)) (μ - ((ℓ - j : ℤ) : ℂ)) k := by
  have hN := prodFunZ_assoc_left_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hu ℓ hNA hN₂ hN₃
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  set S := α₁ + α₂ + α₃ - h₄ - 2 + β - ℓ - 1 with hSdef
  set ν := α₂ + α₃ - 1 - Q.h with hνdef
  set FA : ℕ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) w₁ w₂ w₃
    (S + ((i : ℤ) : ℂ)) ν with hFA
  set FB : ℕ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
    (S + ((ℓ - i : ℤ) : ℂ)) ν with hFB
  set FC : ℕ → ℂ → ℂ := fun j => prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) j w₂) w₃
    (S + ((ℓ - j : ℤ) : ℂ)) (ν - j) with hFC
  have eA : ∀ i, HasLogExp overlapDomain (FA i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃
      (supportedAt_comp_mode hf hu (ℓ - i)) (by rw [hSdef]; push_cast; ring) 0
      (by rw [hνdef]; push_cast; ring)
  have eB : ∀ i, HasLogExp overlapDomain (FB i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hu h₃ i) hf (by rw [hSdef]; push_cast; ring) (i + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have eC : ∀ j, HasLogExp overlapDomain (FC j) := fun j =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hu h₂ j) h₃ hf (by rw [hSdef]; push_cast; ring) (1 - β)
      (by rw [hνdef]; push_cast; ring)
  have eA' : ∀ i : ℕ, HasLogExp overlapDomain (fun t => negOnePow i * cbz ℓ i
      * (psEval (binPS (i : ℤ)) (Complex.exp t) * FA i t)) :=
    fun i => hasLogExp_smul _ (hasLogExp_psEval_mul hs (eA i) (binPS_mem _))
  have eB' : ∀ i : ℕ, HasLogExp overlapDomain (fun t => negOnePow i * cbz ℓ i
      * (psEval (binPS (ℓ - i)) (Complex.exp t) * FB i t)) :=
    fun i => hasLogExp_smul _ (hasLogExp_psEval_mul hs (eB i) (binPS_mem _))
  have eC' : ∀ j : ℕ, HasLogExp overlapDomain (fun t => negOnePow j * cbz ℓ j
      * (Complex.exp (((ℓ - j : ℤ) : ℂ) * t) * FC j t)) :=
    fun j => hasLogExp_smul _ (hasLogExp_exp_mul (eC j) _)
  have eSA := hasLogExp_sum (Finset.range NA) (fun i _ => eA' i)
  have eSB := hasLogExp_smul (negOnePow ℓ) (hasLogExp_sum (Finset.range N₃) (fun i _ => eB' i))
  have eSC := hasLogExp_smul (negOnePow ℓ) (hasLogExp_sum (Finset.range N₂) (fun j _ => eC' j))
  have eSB' := hasLogExp_smul (-1) eSB
  have eSC' := hasLogExp_smul (-1) eSC
  simp only [neg_one_mul] at eSB' eSC'
  have eAB := hasLogExp_add eSA eSB'
  have hsum : ∀ t ∈ overlapDomain,
      prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) ℓ w₁) w₂ w₃ S ν t
        = (((fun t => ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
              * (psEval (binPS (i : ℤ)) (Complex.exp t) * FA i t))
            + fun t => -(negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
              * (psEval (binPS (ℓ - i)) (Complex.exp t) * FB i t)))
          + fun t => -(negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j
              * (Complex.exp (((ℓ - j : ℤ) : ℂ) * t) * FC j t))) t := by
    intro t ht
    rw [hN t ht]
    simp only [Pi.add_apply, hFA, hFB, hFC]
    rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [logCoeff_congr hU hs hne hsum (hasLogExp_congr (fun t ht => (hsum t ht).symm)
      (hasLogExp_add eAB eSC')),
    logCoeff_add hU hs hne eAB eSC', logCoeff_add hU hs hne eSA eSB']
  have nB : logCoeff overlapDomain (fun t => -(negOnePow ℓ * ∑ i ∈ Finset.range N₃,
      negOnePow i * cbz ℓ i * (psEval (binPS (ℓ - i)) (Complex.exp t) * FB i t))) μ k
      = -(negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * ∑ᶠ s : ℕ, coeff s (binPS (ℓ - i)) * logCoeff overlapDomain (FB i) (μ - s) k) := by
    have := logCoeff_smul hU hs hne (-1) eSB μ k
    simp only [neg_one_mul] at this
    rw [this, logCoeff_smul hU hs hne _ (hasLogExp_sum (Finset.range N₃) (fun i _ => eB' i)),
      logCoeff_sum hU hs hne _ (fun i _ => eB' i)]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_psEval_mul hs (eB i) (binPS_mem _)),
      logCoeff_psEval_mul hU hs hne (eB i) (binPS_mem _)]
  have nC : logCoeff overlapDomain (fun t => -(negOnePow ℓ * ∑ j ∈ Finset.range N₂,
      negOnePow j * cbz ℓ j * (Complex.exp (((ℓ - j : ℤ) : ℂ) * t) * FC j t))) μ k
      = -(negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j
          * logCoeff overlapDomain (FC j) (μ - ((ℓ - j : ℤ) : ℂ)) k) := by
    have := logCoeff_smul hU hs hne (-1) eSC μ k
    simp only [neg_one_mul] at this
    rw [this, logCoeff_smul hU hs hne _ (hasLogExp_sum (Finset.range N₂) (fun j _ => eC' j)),
      logCoeff_sum hU hs hne _ (fun j _ => eC' j)]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_exp_mul (eC j) _)]
    congr 1
    have := logCoeff_exp_mul hU hs hne (eC j) (((ℓ - j : ℤ) : ℂ)) (μ - ((ℓ - j : ℤ) : ℂ)) k
    rw [sub_add_cancel] at this
    exact this
  rw [nB, nC, logCoeff_sum hU hs hne _ (fun i _ => eA' i)]
  simp only [sub_eq_add_neg]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logCoeff_smul hU hs hne _ (hasLogExp_psEval_mul hs (eA i) (binPS_mem _)),
    logCoeff_psEval_mul hU hs hne (eA i) (binPS_mem _)]
  simp only [hFA, sub_eq_add_neg]

end HoldsCoeff

/-! ## The left associator on the coefficient functions -/

/-- **The left associator on the coefficient functions** (fixed intermediate weight `n`):
`B_n(u_ℓ w₁, w₂) = Σᵢ (−1)ⁱC(ℓ,i) Σ_s C(i,s) B_{n−β+ℓ+1−s}(f∘u_{ℓ−i}, w₃)(w₁, w₂)
  − (−1)^ℓ Σᵢ (−1)ⁱC(ℓ,i) Σ_s C(ℓ−i,s) B_{n−β+ℓ+1−s}(f, uᵢw₃)(w₁, w₂)
  − (−1)^ℓ Σⱼ (−1)ʲC(ℓ,j) B_n(w₁, uⱼw₂)`. -/
theorem coefFun_assoc_left_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (ℓ : ℤ) (x : HomPair P₁ P₂) {NA N₂ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i) = 0)
    (hN₂ : ∀ j : ℕ, N₂ ≤ j → mode (P₂.isMod.YM u) j x.w₂ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) (n : ℂ) (k : ℕ) :
    coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairLeft x hu ℓ)
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz ℓ i
          * ∑ᶠ s : ℕ, coeff s (binPS (i : ℤ))
            * coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) w₃ α₃
                (h₄ - β + (ℓ - i : ℤ) + 1) (n - β + ℓ + 1 - s) k x
        - negOnePow ℓ * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ℓ i
          * ∑ᶠ s : ℕ, coeff s (binPS (ℓ - i))
            * coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) i w₃) (α₃ + β - i - 1) h₄
                (n - β + ℓ + 1 - s) k x
        - negOnePow ℓ * ∑ j ∈ Finset.range N₂, negOnePow j * cbz ℓ j
          * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairRight x hu j) := by
  have key := logCoeff_assoc_left_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf hu ℓ hNA hN₂
    hN₃ (n - x.α₁ - x.α₂ - β + ℓ + 1) k
  -- rewrite every `prodFunZ` as the canonical `prodFun`
  rw [prodFunZ_canonical hY₂ f _ x.h₂ h₃ _ 0 _ (by push_cast; ring)] at key
  have eA : ∀ i : ℕ, prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) x.w₁ x.w₂ w₃
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((i : ℤ) : ℂ)) (x.α₂ + α₃ - 1 - Q.h)
      = prodFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) x.w₁ x.w₂ w₃
          (x.α₁ + x.α₂ + α₃ - (h₄ - β + (ℓ - i : ℤ) + 1) - 2) (x.α₂ + α₃ - 1 - Q.h) := by
    intro i
    rw [prodFunZ_canonical hY₂ _ x.w₁ x.h₂ h₃ _ 0 _ (by push_cast; ring)]
    congr 1
    push_cast; ring
  have eB : ∀ i : ℕ, prodFunZ Y₁ Y₂ f x.w₁ x.w₂ (mode (P₃.isMod.YM u) i w₃)
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - i : ℤ) : ℂ)) (x.α₂ + α₃ - 1 - Q.h)
      = prodFun Y₁ Y₂ f x.w₁ x.w₂ (mode (P₃.isMod.YM u) i w₃)
          (x.α₁ + x.α₂ + (α₃ + β - i - 1) - h₄ - 2) (x.α₂ + (α₃ + β - i - 1) - 1 - Q.h) := by
    intro i
    have hw := VOA.mode_mem_weight P₃.isMod hu h₃ i
    rw [prodFunZ_canonical hY₂ f x.w₁ x.h₂ hw _ (i + 1 - β) _ (by push_cast; ring)]
    congr 1
    push_cast; ring
  have eC : ∀ j : ℕ, prodFunZ Y₁ Y₂ f x.w₁ (mode (P₂.isMod.YM u) j x.w₂) w₃
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - ℓ - 1 + ((ℓ - j : ℤ) : ℂ)) (x.α₂ + α₃ - 1 - Q.h - j)
      = prodFun Y₁ Y₂ f x.w₁ (mode (P₂.isMod.YM u) j x.w₂) w₃
          (x.α₁ + (x.α₂ + β - j - 1) + α₃ - h₄ - 2) ((x.α₂ + β - j - 1) + α₃ - 1 - Q.h) := by
    intro j
    have hw := VOA.mode_mem_weight P₂.isMod hu x.h₂ j
    rw [prodFunZ_canonical hY₂ f x.w₁ hw h₃ _ (1 - β) _ (by push_cast; ring)]
    congr 1
    push_cast; ring
  simp only [eA, eB, eC] at key
  simp only [coefFun, pairRight, pairLeft, prodExpCoeff]
  have l1 : x.α₁ + (β : ℂ) - ((ℓ : ℤ) : ℂ) - 1 + x.α₂ + α₃ - h₄ - 2
      = x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - ℓ - 1 := by ring
  have l2 : n - (x.α₁ + (β : ℂ) - ((ℓ : ℤ) : ℂ) - 1) - x.α₂
      = n - x.α₁ - x.α₂ - β + ℓ + 1 := by ring
  rw [l1, l2, key]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine finsum_congr fun s => ?_
      congr 2
      ring
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine finsum_congr fun s => ?_
      congr 2
      ring
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    push_cast; ring

/-! ## Sign and summation helpers -/

theorem negOnePow_add (a b : ℤ) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  rw [negOnePow, negOnePow, negOnePow]
  by_cases ha : Even a <;> by_cases hb : Even b
  · rw [if_pos ha, if_pos hb, if_pos (ha.add hb)]; ring
  · rw [if_pos ha, if_neg hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_pos hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_neg hb, if_pos (by simp [Int.even_add, ha, hb])]; ring

theorem negOnePow_sub (a b : ℤ) : negOnePow (a - b) = negOnePow a * negOnePow b := by
  rw [sub_eq_add_neg, negOnePow_add]
  congr 1
  rw [negOnePow, negOnePow]; simp only [even_neg]

/-- The reindexing `(k, i') ↦ (k, k + i')` of a triangular double sum. -/
theorem sum_shift_triangle (F : ℕ → ℕ → ℂ) {Nf K : ℕ}
    (h1 : ∀ s i, i < s → F s i = 0) (h2 : ∀ s i, Nf ≤ i → F s i = 0) :
    ∑ k ∈ Finset.range K, ∑ i' ∈ Finset.range Nf, F k (k + i')
      = ∑ i ∈ Finset.range Nf, ∑ s ∈ Finset.range K, F s i := by
  have e1 : ∀ k : ℕ, ∑ i' ∈ Finset.range Nf, F k (k + i') = ∑ i ∈ Finset.range Nf, F k i := by
    intro k
    have h3 : ∑ i' ∈ Finset.range Nf, F k (k + i') = ∑ i ∈ Finset.Ico k (k + Nf), F k i := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    rw [h3, Finset.sum_Ico_eq_sub _ (Nat.le_add_right k Nf),
      Finset.sum_eq_zero (s := Finset.range k) fun i hi => h1 k i (Finset.mem_range.1 hi),
      sub_zero]
    exact (Finset.sum_subset (Finset.range_subset_range.2 (Nat.le_add_left Nf k)) fun i _ hi => by
      rw [Finset.mem_range, not_lt] at hi; exact h2 k i hi).symm
  simp only [e1]
  exact Finset.sum_comm

/-! ## The two binomial reorganizations -/

theorem cbz_nat_eq_zero {i s : ℕ} (h : i < s) : cbz (i : ℤ) (s : ℤ) = 0 := by
  rw [cbz_apply_nonneg _ (Int.natCast_nonneg s), Int.toNat_natCast]
  exact VOA.VertexOperatorAlgebra.gBinom_natCast_eq_zero h

/-- The `f`-side reorganization (trinomial reindexing). -/
theorem Xpart (X : ℕ → ℤ → ℂ) (ell : ℤ) {Nf K : ℕ} (hNK : Nf ≤ K)
    (hXz : ∀ s i : ℕ, Nf ≤ i → X s (ell - i) = 0) :
    ∑ i ∈ Finset.range Nf, negOnePow i * cbz ell i
        * ∑ᶠ s : ℕ, coeff s (binPS (i : ℤ)) * X s (ell - i)
      = ∑ k' ∈ Finset.range K, cbz ell k' * negOnePow k'
          * ∑ i ∈ Finset.range Nf, negOnePow i * cbz (ell - k') i * X k' (ell - k' - i) := by
  set F : ℕ → ℕ → ℂ := fun s i => negOnePow i * cbz ell i * (cbz (i : ℤ) s * X s (ell - i))
    with hF
  have hL : ∀ i ∈ Finset.range Nf, negOnePow i * cbz ell i
      * ∑ᶠ s : ℕ, coeff s (binPS (i : ℤ)) * X s (ell - i)
      = ∑ s ∈ Finset.range K, F s i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (by
      intro s hs
      rw [Function.mem_support] at hs
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hs
      rw [coeff_binPS, cbz_nat_eq_zero (by omega), zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [coeff_binPS]
  rw [Finset.sum_congr rfl hL, ← sum_shift_triangle F (K := K)
    (fun s i h => by simp only [hF]; rw [cbz_nat_eq_zero h]; ring)
    (fun s i h => by simp only [hF]; rw [hXz s i h]; ring)]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hF]
  have htri := VOA.Huang.AssocAssociator.cbz_trinomial ell (i := ((k' + i : ℕ) : ℤ))
    (j := (k' : ℤ)) (by positivity) (by positivity)
  rw [show ((k' + i : ℕ) : ℤ) - (k' : ℤ) = (i : ℤ) by push_cast; ring] at htri
  rw [show ell - ((k' + i : ℕ) : ℤ) = ell - k' - i by push_cast; ring,
    show negOnePow ((k' + i : ℕ) : ℤ) = negOnePow k' * negOnePow i by
      rw [show ((k' + i : ℕ) : ℤ) = (k' : ℤ) + (i : ℤ) by push_cast; ring, negOnePow_add]]
  linear_combination (negOnePow (k' : ℤ) * negOnePow (i : ℤ) * X k' (ell - k' - i)) * htri

/-- The `w₃`-side reorganization (`C(ℓ,i)C(ℓ−i,s) = C(ℓ,s)C(ℓ−s,i)`). -/
theorem Ypart (Y : ℕ → ℕ → ℂ) (ell : ℤ) {N₃ K : ℕ}
    (hYz : ∀ s : ℕ, K ≤ s → ∀ i : ℕ, Y s i = 0) :
    negOnePow ell * ∑ i ∈ Finset.range N₃, negOnePow i * cbz ell i
        * ∑ᶠ s : ℕ, coeff s (binPS (ell - i)) * Y s i
      = ∑ k' ∈ Finset.range K, cbz ell k' * negOnePow k'
          * (negOnePow (ell - k') * ∑ i ∈ Finset.range N₃, negOnePow i * cbz (ell - k') i
            * Y k' i) := by
  have hL : ∀ i : ℕ, ∑ᶠ s : ℕ, coeff s (binPS (ell - i)) * Y s i
      = ∑ s ∈ Finset.range K, cbz (ell - i) s * Y s i := by
    intro i
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (by
      intro s hs
      rw [Function.mem_support] at hs
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hs
      rw [hYz s (by omega) i, mul_zero])]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [coeff_binPS]
  simp only [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsw := VOA.Huang.AssocAssociator.cbz_swap ell i k'
  have hs : negOnePow (k' : ℤ) * negOnePow (ell - k') = negOnePow ell := by
    rw [negOnePow_sub, ← mul_assoc, mul_comm (negOnePow (k' : ℤ)), mul_assoc,
      negOnePow_mul_self, mul_one]
  linear_combination (negOnePow ell * negOnePow (i : ℤ) * Y k' i) * hsw
    + (cbz ell k' * negOnePow (i : ℤ) * cbz (ell - k') i * Y k' i) * hs.symm

/-! ## The compatibility condition for the coefficient functions -/

/-- **Every coefficient function satisfies the `P(1)`-compatibility condition**
(strongly rational `V`). -/
theorem coeffCompat_holds (hV : StronglyRational W) : CoeffCompat W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n k γ a ha ell
  have hB : coefFun Y₁ Y₂ f w₃ α₃ h₄ n k ∈ bilin P₁ P₂ :=
    coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k
  have hBi : IsBilin (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k) := hB
  -- (i) truncation of the coproduct
  obtain ⟨Pt, hPt⟩ := coproduct_lower_truncation hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf ha n k
  -- (ii) `f ∘ a_q = 0` for small `q`
  obtain ⟨QA, hQA⟩ : ∃ QA : ℤ, ∀ q : ℤ, q ≤ QA → f ∘ₗ mode (P₄.isMod.YM a) q = 0 := by
    obtain ⟨Q0, hQ0⟩ := exists_int_lt ((P₄.h - h₄ + γ - 1).re)
    refine ⟨Q0, fun q hq => comp_mode_eq_zero_of_lt P₄.isLow hf ha ?_⟩
    have : (q : ℝ) ≤ Q0 := by exact_mod_cast hq
    simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re] at hQ0 ⊢
    linarith
  obtain ⟨N₃, hN₃⟩ := exists_nat_truncation P₃.isMod a w₃
  obtain ⟨M, hM⟩ := VOA.Huang.LogRemovalWeightBound.coefFun_eq_zero_of_re_lt hV i₁ i₂ i₃ i₄ iQ
    hY₁ hY₂
  set Nf : ℕ := (ell - QA).toNat with hNfdef
  have hNf : ∀ (p : ℤ), p ≤ ell → ∀ i : ℕ, Nf ≤ i → f ∘ₗ mode (P₄.isMod.YM a) (p - i) = 0 :=
    fun p hp i hi => hQA _ (by omega)
  have hw : ∀ i : ℕ, mode (P₃.isMod.YM a) i w₃ ∈ P₃.isMod.weight (α₃ + γ - i - 1) := by
    intro i
    have := VOA.mode_mem_weight P₃.isMod ha h₃ i
    simpa using this
  -- (iii) the weight bound
  obtain ⟨Sw, hSw⟩ : ∃ Sw : ℕ, ∀ s : ℕ, Sw ≤ s → ∀ i : ℕ,
      coefFun Y₁ Y₂ f (mode (P₃.isMod.YM a) i w₃) (α₃ + γ - i - 1) h₄
        (n - γ + ell + 1 - s) k = 0 := by
    obtain ⟨S0, hS0⟩ := exists_nat_gt (n.re + ell - M + α₃.re + h₄.re)
    refine ⟨S0, fun s hs i => hM _ _ _ _ (hw i) hf _ k ?_⟩
    have h1 : (S0 : ℝ) ≤ s := by exact_mod_cast hs
    have h2 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re,
      Complex.natCast_re]
    linarith
  set K : ℕ := max (max Nf Sw) (ell - Pt).toNat with hKdef
  refine ⟨K, fun k' hk' => ?_, fun x => ?_⟩
  · funext x
    obtain ⟨N₁, hN₁, hz⟩ := hPt (ell - k') (by omega) x
    rw [copT_eq_sum hB ha _ x hN₁, hz, Pi.zero_apply]
  -- the identity at `x`
  have hL := coefFun_assoc_left_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf ha ell x
    (NA := Nf) (N₂ := PzTensorAction.lowBound P₂.h x.α₂ γ) (N₃ := N₃) (hNf ell le_rfl)
    (fun j hj => mode_eq_zero_of_lowBound P₂.isLow x.h₂ ha hj) hN₃ n k
  have hR : ∀ k' : ℕ, copT ha (ell - k') (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k) x
      = ∑ i ∈ Finset.range Nf, negOnePow i * cbz (ell - k') i
          * coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM a) (ell - k' - i)) w₃ α₃
              (h₄ - γ + (ell - k' - i : ℤ) + 1) (n - γ + ell + 1 - k') k x
        - negOnePow (ell - k') * ∑ i ∈ Finset.range N₃, negOnePow i * cbz (ell - k') i
          * coefFun Y₁ Y₂ f (mode (P₃.isMod.YM a) i w₃) (α₃ + γ - i - 1) h₄
              (n - γ + ell + 1 - k') k x := by
    intro k'
    have := coefFun_coproduct_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf ha (ell - k') x
      (NA := Nf) (N₁ := PzTensorAction.lowBound P₁.h x.α₁ γ) (N₃ := N₃) (hNf _ (by omega))
      (fun r hr => mode_eq_zero_of_lowBound P₁.isLow x.h₁ ha hr) hN₃ n k
    unfold copT
    rw [this, show n - (γ : ℂ) + ((ell - k' : ℤ) : ℂ) + 1 = n - γ + ell + 1 - k' by
      push_cast; ring]
  -- the `w₂`-side terms cancel
  have cR : locR ha ell (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k) x
      = negOnePow ell * ∑ j ∈ Finset.range (PzTensorAction.lowBound P₂.h x.α₂ γ),
          negOnePow j * cbz ell j * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairRight x ha j) := by
    rw [locR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [negOnePow_sub]
    ring
  -- the `f`-side and `w₃`-side reorganizations
  have cX := Xpart (fun s q => coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM a) q) w₃ α₃
      (h₄ - γ + q + 1) (n - γ + ell + 1 - s) k x) ell (Nf := Nf) (K := K)
    (le_trans (le_max_left _ _) (le_max_left _ _))
    (fun s i hi => by
      simp only
      rw [hNf ell le_rfl i hi]
      exact coefFun_eq_zero_of Y₁ Y₂ 0 w₃ α₃ _ _ k x (Or.inr (Or.inr (Or.inr rfl))))
  have cY := Ypart (fun s i => coefFun Y₁ Y₂ f (mode (P₃.isMod.YM a) i w₃) (α₃ + γ - i - 1)
      h₄ (n - γ + ell + 1 - s) k x) ell (N₃ := N₃) (K := K)
    (fun s hs i => by
      simp only
      rw [hSw s (by omega) i, Pi.zero_apply])
  simp only at cX cY
  rw [hL, cR]
  simp only [hR, mul_sub, Finset.sum_sub_distrib]
  rw [← cX, ← cY]
  ring

/-! ## Consequences -/

/-- **`TauAssociator` from the pure-algebra input `HLZ544` alone.** -/
theorem tauAssociator_of_HLZ544 (hV : StronglyRational W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂) :
    TauAssociator W :=
  tauAssociator_of_compat hV (coeffCompat_holds hV) hH

/-- **`CoeffWeakInput` from the pure-algebra input `HLZ544` alone.** -/
theorem coeffWeakInput_of_HLZ544 (hV : StronglyRational W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂) :
    VOA.Huang.LogRemovalWeak.CoeffWeakInput W :=
  coeffWeakInput_of_compat hV (coeffCompat_holds hV) hH

/-- **`AssociativityInput` from the remaining named inputs**: ABD (citation), HLZ Thm. 5.44
(pure algebra) and the log-free iterate identity (HL6). -/
theorem associativityInput_of_HLZ544 (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂)
    (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  associativityInput_of_compat hV hABD (coeffCompat_holds hV) hH hZ

end VOA.Huang.PzTensorCompatProof
