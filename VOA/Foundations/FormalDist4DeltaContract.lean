/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Foundations.FormalDist4Delta

/-!
# Semantic contraction of the four-variable delta kernels

`Foundations.FormalDist4Delta` constructs the two expansions of
`z₀⁻¹ δ((z₁-z₂)/z₀)` and proves the kernel identity

`(z₃-z₀)^N K = (z₁-z₄)^N K`.

This file supplies the deliberately separate semantic interface: the coefficient with which
the delta kernel sends an input coefficient `(source, baseIn)` to `(outer, baseOut)` is

`singleDelta o (-source-1) (baseOut-baseIn) outer`.

Defining the contraction coefficient from `singleDelta` is essential.  The negative expansion
is supported where the *source delta exponent* is nonnegative; it is not obtained by reusing
the positive-expansion binomial with its lower index changed.  The definitions below therefore
derive both orientations from the already audited expansion kernels.

Double contractions are recorded in both iterated orders.  Their Fubini theorem assumes exactly
finite joint support, so no exchange of an infinite `finsum` is implicit.  The final transport
theorem applies the kernel identity before contraction and is consequently valid for every
payload, independently of later field-truncation arguments.
-/

namespace VOA

open scoped BigOperators

universe u

namespace FormalDist₄Delta

/-! ## The semantic single-delta coefficient -/

/-- The coefficient on the residue graph `source = outer + k`, derived from the delta kernel
itself.  Here `k = baseOut - baseIn`. -/
noncomputable def contractionCoeff (o : Orientation) (outer k : ℤ) : ℂ :=
  singleDelta o (-outer - k - 1) k outer

/-- The full matrix coefficient from `(source, baseIn)` to `(outer, baseOut)`. -/
noncomputable def contractionKernel (o : Orientation) : FormalDist₄ ℂ :=
  fun outer baseOut source baseIn =>
    singleDelta o (-source - 1) (baseOut - baseIn) outer

@[simp] theorem contractionKernel_apply (o : Orientation)
    (outer baseOut source baseIn : ℤ) :
    contractionKernel o outer baseOut source baseIn =
      singleDelta o (-source - 1) (baseOut - baseIn) outer := rfl

@[simp] theorem contractionKernel_param (o : Orientation) (outer baseOut k : ℤ) :
    contractionKernel o outer baseOut (outer + k) (baseOut - k) =
      contractionCoeff o outer k := by
  simp only [contractionKernel, contractionCoeff]
  congr 2 <;> ring

/-- The kernel is supported on the residue graph `source = outer + baseOut - baseIn`. -/
theorem contractionKernel_eq_zero_off_graph (o : Orientation)
    (outer baseOut source baseIn : ℤ)
    (h : source ≠ outer + (baseOut - baseIn)) :
    contractionKernel o outer baseOut source baseIn = 0 := by
  rw [contractionKernel_apply]
  apply singleDelta_eq_zero_off_diag
  omega

/-- The positive orientation has no coefficients with `k < 0`. -/
theorem contractionCoeff_pos_eq_zero_of_neg (outer : ℤ) {k : ℤ} (hk : k < 0) :
    contractionCoeff .pos outer k = 0 := by
  rw [contractionCoeff, singleDelta_pos_apply]
  exact expandPos_eq_zero_of_neg _ _ hk

/-- The negative orientation has no coefficients above `k = -outer-1`.  Equivalently,
its source exponent `outer+k` is at most `-1`, exactly as residue contraction requires. -/
theorem contractionCoeff_neg_eq_zero_of_gt (outer : ℤ) {k : ℤ}
    (hk : -outer - 1 < k) : contractionCoeff .neg outer k = 0 := by
  rw [contractionCoeff, singleDelta_neg_apply]
  exact expandNeg_eq_zero_of_neg _ _ (by omega)

/-- Regression check at the coefficient that distinguishes the two delta orientations. -/
theorem contractionCoeff_neg_zero_neg_one : contractionCoeff .neg 0 (-1) = -1 := by
  norm_num [contractionCoeff, singleDelta, expandNeg, negOnePow, gBinom]

/-- Regression check at the negative outer exponent where the discarded binomial interface
incorrectly returned zero. -/
theorem contractionCoeff_neg_neg_one_zero : contractionCoeff .neg (-1) 0 = 1 := by
  norm_num [contractionCoeff, singleDelta, expandNeg, negOnePow, gBinom]

/-! ## Single contraction and its residue formula -/

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-- One summand in the semantic contraction of a single delta kernel. -/
noncomputable def singleContractSummand (o : Orientation) (f : FormalDist₂ W)
    (outer baseOut k : ℤ) : W :=
  contractionKernel o outer baseOut (outer + k) (baseOut - k) •
    f (outer + k) (baseOut - k)

/-- Contraction of a two-variable payload with one delta kernel, reparametrized by its
one-dimensional residue graph. -/
noncomputable def singleDeltaContract (o : Orientation) (f : FormalDist₂ W) :
    FormalDist₂ W :=
  fun outer baseOut => ∑ᶠ k : ℤ, singleContractSummand o f outer baseOut k

/-- The coefficientwise residue-substitution formula, with its coefficient derived from
`singleDelta`. -/
noncomputable def residueSubst (o : Orientation) (f : FormalDist₂ W) : FormalDist₂ W :=
  fun outer baseOut => ∑ᶠ k : ℤ,
    contractionCoeff o outer k • f (outer + k) (baseOut - k)

@[simp] theorem singleDeltaContract_apply (o : Orientation) (f : FormalDist₂ W)
    (outer baseOut : ℤ) :
    singleDeltaContract o f outer baseOut =
      ∑ᶠ k : ℤ, singleContractSummand o f outer baseOut k := rfl

@[simp] theorem residueSubst_apply (o : Orientation) (f : FormalDist₂ W)
    (outer baseOut : ℤ) :
    residueSubst o f outer baseOut = ∑ᶠ k : ℤ,
      contractionCoeff o outer k • f (outer + k) (baseOut - k) := rfl

/-- Semantic contraction by `singleDelta` is exactly the residue-substitution formula. -/
theorem singleDeltaContract_eq_residueSubst (o : Orientation) (f : FormalDist₂ W) :
    singleDeltaContract o f = residueSubst o f := by
  ext outer baseOut
  exact finsum_congr fun k => by
    rw [singleContractSummand, contractionKernel_param]

/-! ## The actual double-delta coefficient on the residue graph -/

/-- On the two-dimensional residue graph, the common-base convolution of the two deltas is
the product of their two semantic contraction coefficients. -/
theorem doubleDelta_on_residue_graph (o₁ o₂ : Orientation)
    (outer₁ outer₂ k₁ k₂ : ℤ) :
    doubleDelta o₁ o₂
        (-outer₁ - k₁ - 1) (-outer₂ - k₂ - 1) outer₁ outer₂ (k₁ + k₂) =
      contractionCoeff o₁ outer₁ k₁ * contractionCoeff o₂ outer₂ k₂ := by
  rw [doubleDelta_apply, finsum_eq_single _ k₁]
  · simp only [contractionCoeff]
    congr 2
    all_goals ring
  · intro split hsplit
    rw [singleDelta_eq_zero_off_diag o₁ (-outer₁ - k₁ - 1) split outer₁ (by omega),
      zero_mul]

/-! ## Raw semantic kernel contraction -/

/-- The common-base double delta is supported on the total antidiagonal forced by its two
single-delta factors. -/
theorem doubleDelta_eq_zero_off_total_diag (o₁ o₂ : Orientation)
    (source₁ source₂ outer₁ outer₂ base : ℤ)
    (h : source₁ + source₂ + base ≠ -outer₁ - outer₂ - 2) :
    doubleDelta o₁ o₂ source₁ source₂ outer₁ outer₂ base = 0 := by
  rw [doubleDelta_apply, finsum_eq_zero_of_forall_eq_zero]
  intro split
  by_cases h₁ : source₁ + split = -outer₁ - 1
  · have h₂ : source₂ + (base - split) ≠ -outer₂ - 1 := by omega
    rw [singleDelta_eq_zero_off_diag o₂ source₂ (base - split) outer₂ h₂, mul_zero]
  · rw [singleDelta_eq_zero_off_diag o₁ source₁ split outer₁ h₁, zero_mul]

/-- One summand in the genuine convolution of a scalar kernel against a payload.  Unlike the
residue-graph formula below, this definition is valid for an arbitrary kernel, including a
kernel after a coordinate shift: the common-base exponent is summed independently. -/
noncomputable def kernelContractSummand (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (outer₁ baseOut outer₂ source₁ source₂ baseIn : ℤ) : W :=
  K (-source₁ - 1) (-source₂ - 1) outer₁ outer₂ (baseOut - baseIn) •
    f source₁ baseIn source₂

/-- Raw kernel contraction in source order `1,2`. -/
noncomputable def kernelContract₁₂ (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) : FormalDist₃ W :=
  fun outer₁ baseOut outer₂ => ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
    kernelContractSummand K f outer₁ baseOut outer₂ source₁ source₂ baseIn

/-- Raw kernel contraction in source order `2,1`. -/
noncomputable def kernelContract₂₁ (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) : FormalDist₃ W :=
  fun outer₁ baseOut outer₂ => ∑ᶠ source₂ : ℤ, ∑ᶠ source₁ : ℤ, ∑ᶠ baseIn : ℤ,
    kernelContractSummand K f outer₁ baseOut outer₂ source₁ source₂ baseIn

@[simp] theorem kernelContract₁₂_apply (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (outer₁ baseOut outer₂ : ℤ) :
    kernelContract₁₂ K f outer₁ baseOut outer₂ =
      ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        kernelContractSummand K f outer₁ baseOut outer₂ source₁ source₂ baseIn := rfl

@[simp] theorem kernelContract₂₁_apply (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (outer₁ baseOut outer₂ : ℤ) :
    kernelContract₂₁ K f outer₁ baseOut outer₂ =
      ∑ᶠ source₂ : ℤ, ∑ᶠ source₁ : ℤ, ∑ᶠ baseIn : ℤ,
        kernelContractSummand K f outer₁ baseOut outer₂ source₁ source₂ baseIn := rfl

/-! ## Double residue formulas and their semantic identification -/

/-- The algebraic double-residue summand using the two contraction coefficients. -/
noncomputable def doubleResidueSummand (o₁ o₂ : Orientation) (f : FormalDist₃ W)
    (outer₁ baseOut outer₂ k₁ k₂ : ℤ) : W :=
  (contractionCoeff o₁ outer₁ k₁ * contractionCoeff o₂ outer₂ k₂) •
    f (outer₁ + k₁) (baseOut - k₁ - k₂) (outer₂ + k₂)

/-- Exact coefficientwise finite-support condition for the double residue. -/
def DoubleResidueFinite (o₁ o₂ : Orientation) (f : FormalDist₃ W) : Prop :=
  ∀ outer₁ baseOut outer₂,
    (Function.support fun k : ℤ × ℤ =>
      doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k.1 k.2).Finite

/-- Double residue in `1,2` order. -/
noncomputable def doubleResidue₁₂ (o₁ o₂ : Orientation) (f : FormalDist₃ W) :
    FormalDist₃ W :=
  fun outer₁ baseOut outer₂ => ∑ᶠ k₁ : ℤ, ∑ᶠ k₂ : ℤ,
    doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k₁ k₂

/-- Double residue in `2,1` order. -/
noncomputable def doubleResidue₂₁ (o₁ o₂ : Orientation) (f : FormalDist₃ W) :
    FormalDist₃ W :=
  fun outer₁ baseOut outer₂ => ∑ᶠ k₂ : ℤ, ∑ᶠ k₁ : ℤ,
    doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k₁ k₂

@[simp] theorem doubleResidue₁₂_apply (o₁ o₂ : Orientation) (f : FormalDist₃ W)
    (outer₁ baseOut outer₂ : ℤ) :
    doubleResidue₁₂ o₁ o₂ f outer₁ baseOut outer₂ = ∑ᶠ k₁ : ℤ, ∑ᶠ k₂ : ℤ,
      doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k₁ k₂ := rfl

@[simp] theorem doubleResidue₂₁_apply (o₁ o₂ : Orientation) (f : FormalDist₃ W)
    (outer₁ baseOut outer₂ : ℤ) :
    doubleResidue₂₁ o₁ o₂ f outer₁ baseOut outer₂ = ∑ᶠ k₂ : ℤ, ∑ᶠ k₁ : ℤ,
      doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k₁ k₂ := rfl

/-- Contracting the actual two-delta kernel is the `1,2` double residue. -/
theorem kernelContract₁₂_doubleDelta (o₁ o₂ : Orientation) (f : FormalDist₃ W) :
    kernelContract₁₂ (doubleDelta o₁ o₂) f = doubleResidue₁₂ o₁ o₂ f := by
  ext outer₁ baseOut outer₂
  rw [kernelContract₁₂_apply, doubleResidue₁₂_apply]
  have hcollapse : ∀ source₁ source₂ : ℤ,
      (∑ᶠ baseIn : ℤ,
        kernelContractSummand (doubleDelta o₁ o₂) f
          outer₁ baseOut outer₂ source₁ source₂ baseIn) =
        doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
          (source₁ - outer₁) (source₂ - outer₂) := by
    intro source₁ source₂
    let base₀ := baseOut - (source₁ - outer₁) - (source₂ - outer₂)
    rw [finsum_eq_single _ base₀]
    · simp only [kernelContractSummand, doubleResidueSummand, base₀]
      rw [show -source₁ - 1 = -outer₁ - (source₁ - outer₁) - 1 by ring,
        show -source₂ - 1 = -outer₂ - (source₂ - outer₂) - 1 by ring,
        show baseOut - (baseOut - (source₁ - outer₁) - (source₂ - outer₂)) =
            (source₁ - outer₁) + (source₂ - outer₂) by ring,
        doubleDelta_on_residue_graph]
      congr 2
      all_goals ring_nf
    · intro baseIn hbase
      rw [kernelContractSummand,
        doubleDelta_eq_zero_off_total_diag o₁ o₂ (-source₁ - 1) (-source₂ - 1)
          outer₁ outer₂ (baseOut - baseIn) (by dsimp only [base₀] at hbase; omega),
        zero_smul]
  rw [show (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
      kernelContractSummand (doubleDelta o₁ o₂) f
        outer₁ baseOut outer₂ source₁ source₂ baseIn) =
      ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ,
        doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
          (source₁ - outer₁) (source₂ - outer₂) from
    finsum_congr fun source₁ => finsum_congr fun source₂ => hcollapse source₁ source₂]
  rw [← FormalDist₄.finsum_finsum_reindex (Equiv.addLeft outer₁) (Equiv.addLeft outer₂)
    (fun source₁ source₂ => doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
      (source₁ - outer₁) (source₂ - outer₂))]
  exact finsum_congr fun k₁ => finsum_congr fun k₂ => by simp

/-- Contracting the actual two-delta kernel is the `2,1` double residue. -/
theorem kernelContract₂₁_doubleDelta (o₁ o₂ : Orientation) (f : FormalDist₃ W) :
    kernelContract₂₁ (doubleDelta o₁ o₂) f = doubleResidue₂₁ o₁ o₂ f := by
  ext outer₁ baseOut outer₂
  rw [kernelContract₂₁_apply, doubleResidue₂₁_apply]
  have hcollapse : ∀ source₁ source₂ : ℤ,
      (∑ᶠ baseIn : ℤ,
        kernelContractSummand (doubleDelta o₁ o₂) f
          outer₁ baseOut outer₂ source₁ source₂ baseIn) =
        doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
          (source₁ - outer₁) (source₂ - outer₂) := by
    intro source₁ source₂
    let base₀ := baseOut - (source₁ - outer₁) - (source₂ - outer₂)
    rw [finsum_eq_single _ base₀]
    · simp only [kernelContractSummand, doubleResidueSummand, base₀]
      rw [show -source₁ - 1 = -outer₁ - (source₁ - outer₁) - 1 by ring,
        show -source₂ - 1 = -outer₂ - (source₂ - outer₂) - 1 by ring,
        show baseOut - (baseOut - (source₁ - outer₁) - (source₂ - outer₂)) =
            (source₁ - outer₁) + (source₂ - outer₂) by ring,
        doubleDelta_on_residue_graph]
      congr 2
      all_goals ring_nf
    · intro baseIn hbase
      rw [kernelContractSummand,
        doubleDelta_eq_zero_off_total_diag o₁ o₂ (-source₁ - 1) (-source₂ - 1)
          outer₁ outer₂ (baseOut - baseIn) (by dsimp only [base₀] at hbase; omega),
        zero_smul]
  rw [show (∑ᶠ source₂ : ℤ, ∑ᶠ source₁ : ℤ, ∑ᶠ baseIn : ℤ,
      kernelContractSummand (doubleDelta o₁ o₂) f
        outer₁ baseOut outer₂ source₁ source₂ baseIn) =
      ∑ᶠ source₂ : ℤ, ∑ᶠ source₁ : ℤ,
        doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
          (source₁ - outer₁) (source₂ - outer₂) from
    finsum_congr fun source₂ => finsum_congr fun source₁ => hcollapse source₁ source₂]
  rw [← FormalDist₄.finsum_finsum_reindex (Equiv.addLeft outer₂) (Equiv.addLeft outer₁)
    (fun source₂ source₁ => doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂
      (source₁ - outer₁) (source₂ - outer₂))]
  exact finsum_congr fun k₂ => finsum_congr fun k₁ => by simp

/-- Double-residue Fubini, connected to the actual two-delta kernel. -/
theorem doubleResidue_comm (o₁ o₂ : Orientation) (f : FormalDist₃ W)
    (hfin : DoubleResidueFinite o₁ o₂ f) :
    doubleResidue₁₂ o₁ o₂ f = doubleResidue₂₁ o₁ o₂ f := by
  ext outer₁ baseOut outer₂
  exact (FormalDist₄.finsum_finsum_comm_of_joint_finite
    (fun k₁ k₂ : ℤ => doubleResidueSummand o₁ o₂ f outer₁ baseOut outer₂ k₁ k₂)
    (hfin outer₁ baseOut outer₂)).symm

/-- The two raw contraction orders of the actual double-delta kernel agree under the exact
joint support hypothesis on their common residue formula. -/
theorem kernelContract_doubleDelta_comm (o₁ o₂ : Orientation) (f : FormalDist₃ W)
    (hfin : DoubleResidueFinite o₁ o₂ f) :
    kernelContract₁₂ (doubleDelta o₁ o₂) f =
      kernelContract₂₁ (doubleDelta o₁ o₂) f := by
  rw [kernelContract₁₂_doubleDelta, kernelContract₂₁_doubleDelta,
    doubleResidue_comm o₁ o₂ f hfin]

/-! ## Transport before semantic contraction -/

/-- Equal scalar kernels give equal contractions in the first residue order. -/
theorem kernelContract₁₂_congr {K K' : FormalDist₄ (FormalDist ℂ)} (h : K = K')
    (f : FormalDist₃ W) : kernelContract₁₂ K f = kernelContract₁₂ K' f := by
  rw [h]

/-- Equal scalar kernels give equal contractions in the second residue order. -/
theorem kernelContract₂₁_congr {K K' : FormalDist₄ (FormalDist ℂ)} (h : K = K')
    (f : FormalDist₃ W) : kernelContract₂₁ K f = kernelContract₂₁ K' f := by
  rw [h]

/-- Li's outer-to-inner difference-power transport remains valid after contraction against
an arbitrary payload.  Finiteness enters only if the two residue orders are exchanged. -/
theorem kernelContract₁₂_doubleDelta_transport (o₁ o₂ : Orientation) (N : ℕ)
    (f : FormalDist₃ W) :
    kernelContract₁₂ (FormalDist₄.mulBySub₃₄Pow N (doubleDelta o₁ o₂)) f =
      kernelContract₁₂ (FormalDist₄.mulBySub₁₂Pow N (doubleDelta o₁ o₂)) f :=
  kernelContract₁₂_congr (mulBySub₃₄Pow_doubleDelta o₁ o₂ N) f

/-- The same contracted transport in the opposite residue order. -/
theorem kernelContract₂₁_doubleDelta_transport (o₁ o₂ : Orientation) (N : ℕ)
    (f : FormalDist₃ W) :
    kernelContract₂₁ (FormalDist₄.mulBySub₃₄Pow N (doubleDelta o₁ o₂)) f =
      kernelContract₂₁ (FormalDist₄.mulBySub₁₂Pow N (doubleDelta o₁ o₂)) f :=
  kernelContract₂₁_congr (mulBySub₃₄Pow_doubleDelta o₁ o₂ N) f

end FormalDist₄Delta

end VOA

section AxiomAudit
#print axioms VOA.FormalDist₄Delta.singleDeltaContract_eq_residueSubst
#print axioms VOA.FormalDist₄Delta.doubleDelta_on_residue_graph
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_doubleDelta
#print axioms VOA.FormalDist₄Delta.doubleResidue_comm
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_doubleDelta_transport
end AxiomAudit
