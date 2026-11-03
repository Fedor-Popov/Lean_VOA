/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Foundations.FormalDist4
import VOA.Foundations.IotaZExpansion

/-!
# Two-delta substitution in four variables

This file is the delta-calculus layer needed in the proof of Li's local-system theorem
(Proposition 3.2.9).  It remains independent of fields and vertex algebras.

There are two formal expansions of `outer⁻¹ δ((source-base)/outer)` (`singleDelta`).  This
file records those expansions themselves and their common-base convolution `doubleDelta`,
uniformly for all four `PP/PN/NP/NN` orientation choices.  In the Lean coordinates of
`FormalDist₄` the four variables `z₁, z₂, z₃, z₄` are `(source₁, source₂, outer₁, outer₂)`, and
the shared base variable is the inner `FormalDist`.  The central identity is the coefficientwise
form of

`(z₃-z₄)^N K = (z₁-z₂)^N K`

(`mulBySub₃₄_doubleDelta`, `mulBySub₃₄Pow_doubleDelta`).

The semantic contraction of these kernels against a payload, including its exact support
hypotheses, is deliberately separated into `Foundations.FormalDist4DeltaContract`.  In
particular, no independent binomial formula is postulated here for the negative expansion:
its contraction coefficient must be derived from `singleDelta` itself.
-/

namespace VOA

open scoped BigOperators

universe u

namespace FormalDist₄Delta

/-! ## The two delta orientations -/

/-- The two formal expansions of the additive delta substitution. -/
inductive Orientation
  | pos
  | neg
  deriving DecidableEq

/-! ## The composed double-delta kernels -/

/-- The three-variable coefficient kernel
`z_outer⁻¹ δ((z_source-z_base)/z_outer)` in the selected orientation. -/
noncomputable def singleDelta (o : Orientation) : FormalDist₃ ℂ
  | source, base, outer => match o with
    | .pos => expandPos (-outer - 1) source base
    | .neg => expandNeg (-outer - 1) source base

@[simp] theorem singleDelta_pos_apply (source base outer : ℤ) :
    singleDelta .pos source base outer = expandPos (-outer - 1) source base := rfl

@[simp] theorem singleDelta_neg_apply (source base outer : ℤ) :
    singleDelta .neg source base outer = expandNeg (-outer - 1) source base := rfl

theorem singleDelta_eq_zero_off_diag (o : Orientation) (source base outer : ℤ)
    (h : source + base ≠ -outer - 1) : singleDelta o source base outer = 0 := by
  cases o
  · exact expandPos_eq_zero_off_diag _ _ _ h
  · exact expandNeg_eq_zero_off_diag _ _ _ h

/-- Each coefficient in the common-base convolution has finite support. -/
theorem singleDelta_convolution_finite (o₁ o₂ : Orientation)
    (source₁ source₂ outer₁ outer₂ base : ℤ) :
    (Function.support fun split : ℤ =>
      singleDelta o₁ source₁ split outer₁ *
        singleDelta o₂ source₂ (base - split) outer₂).Finite := by
  apply Set.Finite.subset (Set.finite_singleton (-outer₁ - 1 - source₁))
  intro split hs
  rw [Set.mem_singleton_iff]
  by_contra hne
  apply hs
  change singleDelta o₁ source₁ split outer₁ *
      singleDelta o₂ source₂ (base - split) outer₂ = 0
  rw [singleDelta_eq_zero_off_diag o₁ source₁ split outer₁ (by omega), zero_mul]

/-- Composition of two delta substitutions sharing the base variable.  The four explicit
coordinates are `(source₁, source₂, outer₁, outer₂)`; the value is the Laurent series in
the common base variable. -/
noncomputable def doubleDelta (o₁ o₂ : Orientation) : FormalDist₄ (FormalDist ℂ) :=
  fun source₁ source₂ outer₁ outer₂ base => ∑ᶠ split : ℤ,
    singleDelta o₁ source₁ split outer₁ *
      singleDelta o₂ source₂ (base - split) outer₂

@[simp] theorem doubleDelta_apply (o₁ o₂ : Orientation)
    (source₁ source₂ outer₁ outer₂ base : ℤ) :
    doubleDelta o₁ o₂ source₁ source₂ outer₁ outer₂ base = ∑ᶠ split : ℤ,
      singleDelta o₁ source₁ split outer₁ *
        singleDelta o₂ source₂ (base - split) outer₂ := rfl

/-- The single delta identifies `source-base` with `outer`. -/
theorem singleDelta_relation (o : Orientation) (source base outer : ℤ) :
    singleDelta o (source - 1) base outer - singleDelta o source (base - 1) outer =
      singleDelta o source base (outer - 1) := by
  cases o
  · change expandPos (-outer - 1) (source - 1) base -
        expandPos (-outer - 1) source (base - 1) =
      expandPos (-(outer - 1) - 1) source base
    have h := congrFun (congrFun (mulBySub_expandPos (-outer - 1)) source) base
    rw [mulBySub_apply] at h
    convert h using 1
    ring_nf
  · change expandNeg (-outer - 1) (source - 1) base -
        expandNeg (-outer - 1) source (base - 1) =
      expandNeg (-(outer - 1) - 1) source base
    have h := congrFun (congrFun (mulBySub_expandNeg (-outer - 1)) source) base
    rw [mulBySub_apply] at h
    convert h using 1
    ring_nf

/-- The two disjoint difference operators commute. -/
theorem mulBySub₁₂_comm_mulBySub₃₄ :
    Commute
      (FormalDist₄.mulBySub₁₂ : FormalDist₄ (FormalDist ℂ) →ₗ[ℂ] _)
      (FormalDist₄.mulBySub₃₄ : FormalDist₄ (FormalDist ℂ) →ₗ[ℂ] _) := by
  show FormalDist₄.mulBySub₁₂ * FormalDist₄.mulBySub₃₄ =
    FormalDist₄.mulBySub₃₄ * FormalDist₄.mulBySub₁₂
  ext f i j k l base
  change
    (f (i - 1) j (k - 1) l base - f (i - 1) j k (l - 1) base) -
      (f i (j - 1) (k - 1) l base - f i (j - 1) k (l - 1) base) =
    (f (i - 1) j (k - 1) l base - f i (j - 1) (k - 1) l base) -
      (f (i - 1) j k (l - 1) base - f i (j - 1) k (l - 1) base)
  abel

/-- Li's outer-to-inner transport for one difference factor, uniformly in all four choices
`PP/PN/NP/NN`. -/
theorem mulBySub₃₄_doubleDelta (o₁ o₂ : Orientation) :
    FormalDist₄.mulBySub₃₄ (doubleDelta o₁ o₂) =
      FormalDist₄.mulBySub₁₂ (doubleDelta o₁ o₂) := by
  ext source₁ source₂ outer₁ outer₂ base
  change
    (∑ᶠ split : ℤ, singleDelta o₁ source₁ split (outer₁ - 1) *
        singleDelta o₂ source₂ (base - split) outer₂) -
      (∑ᶠ split : ℤ, singleDelta o₁ source₁ split outer₁ *
        singleDelta o₂ source₂ (base - split) (outer₂ - 1)) =
    (∑ᶠ split : ℤ, singleDelta o₁ (source₁ - 1) split outer₁ *
        singleDelta o₂ source₂ (base - split) outer₂) -
      (∑ᶠ split : ℤ, singleDelta o₁ source₁ split outer₁ *
        singleDelta o₂ (source₂ - 1) (base - split) outer₂)
  have h₁ := singleDelta_convolution_finite o₁ o₂
    source₁ source₂ (outer₁ - 1) outer₂ base
  have h₂ := singleDelta_convolution_finite o₁ o₂
    source₁ source₂ outer₁ (outer₂ - 1) base
  have h₃ := singleDelta_convolution_finite o₁ o₂
    (source₁ - 1) source₂ outer₁ outer₂ base
  have h₄ := singleDelta_convolution_finite o₁ o₂
    source₁ (source₂ - 1) outer₁ outer₂ base
  rw [← finsum_sub_distrib h₁ h₂, ← finsum_sub_distrib h₃ h₄]
  let R : ℤ → ℂ := fun split =>
    singleDelta o₁ (source₁ - 1) split outer₁ *
        singleDelta o₂ source₂ (base - split) outer₂ -
      singleDelta o₁ source₁ split outer₁ *
        singleDelta o₂ (source₂ - 1) (base - split) outer₂
  let C₁ : ℤ → ℂ := fun split =>
    singleDelta o₁ source₁ split outer₁ *
      singleDelta o₂ source₂ (base - split - 1) outer₂
  let C₂ : ℤ → ℂ := fun split =>
    singleDelta o₁ source₁ (split - 1) outer₁ *
      singleDelta o₂ source₂ (base - split) outer₂
  have hR : (Function.support R).Finite := by
    apply (h₃.union h₄).subset
    intro split hs
    simp only [Function.mem_support, Set.mem_union] at hs ⊢
    by_contra hnot
    simp only [not_or, not_ne_iff] at hnot
    exact hs (by simp only [R, hnot.1, hnot.2, sub_zero])
  have hC₁ : (Function.support C₁).Finite := by
    have h := singleDelta_convolution_finite o₁ o₂
      source₁ source₂ outer₁ outer₂ (base - 1)
    have heq : C₁ = fun split =>
        singleDelta o₁ source₁ split outer₁ *
          singleDelta o₂ source₂ (base - 1 - split) outer₂ := by
      funext split
      simp only [C₁]
      congr 2
      ring_nf
    rw [heq]
    exact h
  have hC₂ : (Function.support C₂).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (-outer₁ - source₁))
    intro split hs
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hs
    simp only [C₂]
    have hoff : source₁ + (split - 1) ≠ -outer₁ - 1 := by omega
    rw [singleDelta_eq_zero_off_diag o₁ source₁ (split - 1) outer₁ hoff,
      zero_mul]
  have hCsub : (Function.support fun split => C₁ split - C₂ split).Finite := by
    apply (hC₁.union hC₂).subset
    intro split hs
    simp only [Function.mem_support, Set.mem_union] at hs ⊢
    by_contra hnot
    simp only [not_or, not_ne_iff] at hnot
    exact hs (by rw [hnot.1, hnot.2, sub_zero])
  have hpoint : ∀ split : ℤ,
      singleDelta o₁ source₁ split (outer₁ - 1) *
          singleDelta o₂ source₂ (base - split) outer₂ -
        singleDelta o₁ source₁ split outer₁ *
          singleDelta o₂ source₂ (base - split) (outer₂ - 1) =
      R split + (C₁ split - C₂ split) := by
    intro split
    have ha := singleDelta_relation o₁ source₁ split outer₁
    have hb := singleDelta_relation o₂ source₂ (base - split) outer₂
    simp only [R, C₁, C₂]
    rw [← ha, ← hb]
    ring
  have hsum : (∑ᶠ split : ℤ,
      (singleDelta o₁ source₁ split (outer₁ - 1) *
          singleDelta o₂ source₂ (base - split) outer₂ -
        singleDelta o₁ source₁ split outer₁ *
          singleDelta o₂ source₂ (base - split) (outer₂ - 1))) =
      (∑ᶠ split : ℤ, (R split + (C₁ split - C₂ split))) :=
    finsum_congr hpoint
  rw [hsum]
  rw [finsum_add_distrib hR hCsub, finsum_sub_distrib hC₁ hC₂]
  have hcancel : (∑ᶠ split : ℤ, C₁ split) = ∑ᶠ split : ℤ, C₂ split := by
    have hshift := finsum_int_succ_shift C₂
    rw [show (fun split : ℤ => C₂ (split + 1)) = C₁ by
      funext split
      simp only [C₁, C₂]
      congr 2 <;> ring] at hshift
    exact hshift
  rw [hcancel, sub_self, add_zero]

/-- Li's outer-to-inner transport for an arbitrary natural power. -/
theorem mulBySub₃₄Pow_doubleDelta (o₁ o₂ : Orientation) (N : ℕ) :
    FormalDist₄.mulBySub₃₄Pow N (doubleDelta o₁ o₂) =
      FormalDist₄.mulBySub₁₂Pow N (doubleDelta o₁ o₂) := by
  induction N with
  | zero => rfl
  | succ n ih =>
      change (FormalDist₄.mulBySub₃₄ ^ (n + 1)) (doubleDelta o₁ o₂) =
        (FormalDist₄.mulBySub₁₂ ^ (n + 1)) (doubleDelta o₁ o₂)
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change FormalDist₄.mulBySub₃₄
          ((FormalDist₄.mulBySub₃₄ ^ n) (doubleDelta o₁ o₂)) =
        FormalDist₄.mulBySub₁₂
          ((FormalDist₄.mulBySub₁₂ ^ n) (doubleDelta o₁ o₂))
      rw [show (FormalDist₄.mulBySub₃₄ ^ n) (doubleDelta o₁ o₂) =
          (FormalDist₄.mulBySub₁₂ ^ n) (doubleDelta o₁ o₂) from ih]
      have hcomm := (mulBySub₁₂_comm_mulBySub₃₄).pow_left n
      rw [show FormalDist₄.mulBySub₃₄
          ((FormalDist₄.mulBySub₁₂ ^ n) (doubleDelta o₁ o₂)) =
          (FormalDist₄.mulBySub₁₂ ^ n)
            (FormalDist₄.mulBySub₃₄ (doubleDelta o₁ o₂)) by
        exact DFunLike.congr_fun hcomm.eq.symm (doubleDelta o₁ o₂)]
      rw [mulBySub₃₄_doubleDelta]
      exact DFunLike.congr_fun
        ((Commute.refl FormalDist₄.mulBySub₁₂).pow_left n).eq
        (doubleDelta o₁ o₂)

end FormalDist₄Delta

end VOA

section AxiomAudit
#print axioms VOA.FormalDist₄Delta.mulBySub₃₄_doubleDelta
#print axioms VOA.FormalDist₄Delta.mulBySub₃₄Pow_doubleDelta
end AxiomAudit
