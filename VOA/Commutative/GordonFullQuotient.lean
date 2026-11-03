/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFullSymmetry
import VOA.Commutative.GordonGradedQuotient

/-! # The full source-connected Gordon quotient and graded invariant injection -/

namespace VOA.GordonFullQuotient

open MvPolynomial VOA.GordonFiltration VOA.GordonRestrictedDual VOA.GordonPairedEvaluation
open VOA.GordonPairedRelations VOA.GordonResidualFiltration VOA.GordonFullDivisor
open VOA.GordonFullSymmetry VOA.GordonGradedQuotient

noncomputable section

variable {K ρ τ α β γ : Type*} [Field K] [CharZero K]
variable [Fintype ρ] [Fintype τ] [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq ρ] [LinearOrder τ] [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- The actual auxiliary functional model, intersected with next-pair kernels and
lexicographically larger block-evaluation kernels. -/
def sourceStep (m D : ℕ) (f : ρ → τ) : Submodule K (MvPolynomial (Source ρ α β γ) K) :=
  functionalModel m D sourceColor ⊓
    ((⨅ x : α, ⨅ y : β, (nextPairEval (K := K) (ρ := ρ) (γ := γ) x y).toLinearMap.ker) ⊓
      (residualFiltration (τ := τ) ⊤ (shape f)).comap pairEval.toLinearMap)

@[simp] theorem mem_sourceStep (m D : ℕ) (f : ρ → τ)
    (F : MvPolynomial (Source ρ α β γ) K) :
    F ∈ sourceStep m D f ↔ F ∈ functionalModel m D sourceColor ∧
      (∀ x : α, ∀ y : β, nextPairEval x y F = 0) ∧
      pairEval F ∈ residualFiltration (τ := τ) ⊤ (shape f) := by
  simp [sourceStep, LinearMap.mem_ker]

/-- The genuine block evaluation on this filtration step. -/
def stepEval (m D : ℕ) (f : ρ → τ) :
    sourceStep (K := K) (α := α) (β := β) (γ := γ) m D f →ₗ[K]
      MvPolynomial (Target τ α β γ) K :=
  (clusterEval f).toLinearMap.domRestrict (sourceStep m D f)

/-- The separately symmetric divided target, including all residual species. -/
def fullInvariantSubmodule (f : ρ → τ) : Submodule K (MvPolynomial (Target τ α β γ) K) where
  carrier := {q | ∀ e : Equiv.Perm τ, (∀ j, blockSize f (e j) = blockSize f j) →
    ∀ a : Equiv.Perm α, ∀ b : Equiv.Perm β, ∀ c : Equiv.Perm γ,
      rename (fullPerm e a b c) q = q}
  zero_mem' := by intros; simp
  add_mem' := by intro p q hp hq e he a b c; simp [hp e he a b c, hq e he a b c]
  smul_mem' := by intro k p hp e he a b c; simp [hp e he a b c]

/-- The full evaluation image admits a separately symmetric quotient by the full divisor. -/
theorem image_exists_quotient (m D : ℕ) (f : ρ → τ)
    (x : (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range) :
    ∃ q : fullInvariantSubmodule (K := K) (α := α) (β := β) (γ := γ) f,
      x.val = fullDivisor m f * q.val := by
  obtain ⟨F, hx⟩ := x.property
  have hF := (mem_sourceStep m D f F.val).mp F.property
  obtain ⟨q, hq⟩ := fullDivisor_dvd m D f F.val hF.1 hF.2.1 ⊤ hF.2.2
  refine ⟨⟨q, quotient_separate_symmetry m D f F.val hF.1 q hq⟩, ?_⟩
  rw [← hx]
  exact hq

/-- Divide the actual evaluated image by the full divisor. -/
def dividedImage (m D : ℕ) (f : ρ → τ) :
    (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range →ₗ[K]
      fullInvariantSubmodule (K := K) (α := α) (β := β) (γ := γ) f where
  toFun x := (image_exists_quotient m D f x).choose
  map_add' x y := by
    apply Subtype.ext
    apply mul_left_cancel₀ (fullDivisor_ne_zero (K := K) (α := α) (β := β) (γ := γ) m f)
    simp only [Submodule.coe_add]
    rw [mul_add, ← (image_exists_quotient m D f (x + y)).choose_spec,
      ← (image_exists_quotient m D f x).choose_spec, ← (image_exists_quotient m D f y).choose_spec]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    apply mul_left_cancel₀ (fullDivisor_ne_zero (K := K) (α := α) (β := β) (γ := γ) m f)
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [mul_smul_comm, ← (image_exists_quotient m D f (c • x)).choose_spec,
      ← (image_exists_quotient m D f x).choose_spec]
    rfl

theorem dividedImage_spec (m D : ℕ) (f : ρ → τ)
    (x : (stepEval (K := K) (α := α) (β := β) (γ := γ) m D f).range) :
    x.val = fullDivisor m f * (dividedImage m D f x).val :=
  (image_exists_quotient m D f x).choose_spec

theorem dividedImage_injective (m D : ℕ) (f : ρ → τ) :
    Function.Injective (dividedImage (K := K) (α := α) (β := β) (γ := γ) m D f) := by
  intro x y h
  apply Subtype.ext
  rw [dividedImage_spec m D f x, dividedImage_spec m D f y, h]

def fullInvariantPiece (f : ρ → τ) (r : ℕ) : Submodule K (MvPolynomial (Target τ α β γ) K) :=
  fullInvariantSubmodule f ⊓ homogeneousSubmodule (Target τ α β γ) K r

instance fullInvariantPiece_finite (f : ρ → τ) (r : ℕ) :
    FiniteDimensional K (fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f r) := by
  letI := VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_homogeneousSubmodule
    (K := K) (I := Target τ α β γ) r
  exact FiniteDimensional.of_injective (Submodule.inclusion (show
    fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f r ≤
      homogeneousSubmodule (Target τ α β γ) K r from inf_le_right))
    (Submodule.inclusion_injective _)

/-- Division lowers degree by the full, exactly computed conductor degree. -/
theorem dividedImage_homogeneous (m r : ℕ) (f : ρ → τ)
    (x : (stepEval (K := K) (α := α) (β := β) (γ := γ) m
      (fullDegree (α := α) (β := β) (γ := γ) m f + r) f).range) :
    (dividedImage m _ f x).val.IsHomogeneous r := by
  apply quotient_weightedHomogeneous_of_factorization 1 (fullDivisor m f) x.val
    (dividedImage m _ f x).val (fullDegree (α := α) (β := β) (γ := γ) m f) r
    (fullDivisor_ne_zero m f) (fullDivisor_isHomogeneous m f)
  · obtain ⟨F, hx⟩ := x.property
    rw [← hx]
    have hF := (mem_sourceStep m _ f F.val).mp F.property
    obtain ⟨L, hL⟩ := hF.1
    change (clusterEval f F.val).IsWeightedHomogeneous 1 _
    rw [← hL]
    exact (particleMap_homogeneous _ _ _ L).rename_isHomogeneous
  · exact dividedImage_spec m _ f x

/-- The degree-shifted divided image, in the correct homogeneous symmetric target. -/
def gradedImageMap (m r : ℕ) (f : ρ → τ) :
    (stepEval (K := K) (α := α) (β := β) (γ := γ) m
      (fullDegree (α := α) (β := β) (γ := γ) m f + r) f).range →ₗ[K]
      fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f r :=
  ((fullInvariantSubmodule (K := K) (α := α) (β := β) (γ := γ) f).subtype.comp
    (dividedImage m _ f)).codRestrict (fullInvariantPiece f r)
      (fun x ↦ ⟨(dividedImage m _ f x).property, dividedImage_homogeneous m r f x⟩)

theorem gradedImageMap_injective (m r : ℕ) (f : ρ → τ) :
    Function.Injective (gradedImageMap (K := K) (α := α) (β := β) (γ := γ) m r f) := by
  intro x y h
  apply dividedImage_injective m _ f
  apply Subtype.ext
  exact congrArg (fun q : fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f r ↦
    (q : MvPolynomial (Target τ α β γ) K)) h

/-- Proposition 4.6's actual degreewise source-quotient bound, before identifying
the invariant target dimension with its reciprocal q-factorials. -/
theorem finrank_quotient_le (m r : ℕ) (f : ρ → τ) :
    Module.finrank K
      ((sourceStep (K := K) (α := α) (β := β) (γ := γ) m
        (fullDegree (α := α) (β := β) (γ := γ) m f + r) f) ⧸
        (stepEval (K := K) (α := α) (β := β) (γ := γ) m (fullDegree (α := α) (β := β) (γ := γ) m f + r) f).ker) ≤
      Module.finrank K (fullInvariantPiece (K := K) (α := α) (β := β) (γ := γ) f r) := by
  rw [(stepEval (K := K) (α := α) (β := β) (γ := γ) m
    (fullDegree (α := α) (β := β) (γ := γ) m f + r) f).quotKerEquivRange.finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective
    (gradedImageMap_injective (K := K) (α := α) (β := β) (γ := γ) m r f)

end
end VOA.GordonFullQuotient
