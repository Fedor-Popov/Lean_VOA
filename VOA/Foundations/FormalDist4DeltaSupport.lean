/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Foundations.FormalDist4DeltaContract

/-!
# Moving finite difference powers through semantic delta contraction

The semantic contraction in `FormalDist4DeltaContract` is a nested algebraic `finsum`.
Linearity of an individual summand is automatic, but distributing subtraction through a
`finsum` is valid only under finite support.  This file records exactly that missing support
interface and proves the two adjointness identities needed in Li's local-system argument:

* an outer difference on a scalar kernel becomes the corresponding difference on the
  contracted output;
* a source difference on a scalar kernel can be moved to the payload.

The support hypothesis is deliberately stable under arbitrary finite coordinate shifts.  It
says that every translated contraction summand has finite joint support in the two source
indices and the payload's base index.  This is stronger than any single displayed identity,
but exactly stable under the finite shift/add/sub operations used to form difference powers.
No field or vertex-algebra hypothesis occurs here; a later layer may derive this predicate from
field truncation for its concrete payloads.
-/

namespace VOA

open scoped BigOperators

universe u

namespace FormalDist₄Delta

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

/-! ## Joint support for triple contractions -/

/-- Joint finite support of a three-index family, associated as `source₁ × (source₂ × base)`. -/
def TripleFinite (F : ℤ → ℤ → ℤ → W) : Prop :=
  (Function.support fun t : ℤ × (ℤ × ℤ) => F t.1 t.2.1 t.2.2).Finite

omit [Module ℂ W] in
/-- Joint finite support is preserved by pointwise subtraction. -/
theorem TripleFinite.sub {F G : ℤ → ℤ → ℤ → W}
    (hF : TripleFinite F) (hG : TripleFinite G) :
    TripleFinite (fun i j k => F i j k - G i j k) := by
  apply (hF.union hG).subset
  intro t ht
  simp only [Function.mem_support, Set.mem_union] at ht ⊢
  by_contra hnot
  simp only [not_or, not_ne_iff] at hnot
  exact ht (by rw [hnot.1, hnot.2, sub_zero])

omit [Module ℂ W] in
private theorem triple_slice_finite {F : ℤ → ℤ → ℤ → W}
    (hF : TripleFinite F) (source₁ : ℤ) :
    (Function.support fun q : ℤ × ℤ => F source₁ q.1 q.2).Finite := by
  have hpre : (Function.support fun q : ℤ × ℤ => F source₁ q.1 q.2) =
      (fun q : ℤ × ℤ => (source₁, q)) ⁻¹'
        (Function.support fun t : ℤ × (ℤ × ℤ) => F t.1 t.2.1 t.2.2) := rfl
  rw [hpre]
  exact Set.Finite.preimage
    (Function.Injective.injOn (fun _ _ h => congrArg Prod.snd h)) hF

omit [Module ℂ W] in
/-- A jointly finite triple `finsum` can be curried in the contraction order. -/
theorem tripleFinsum_eq_prod {F : ℤ → ℤ → ℤ → W} (hF : TripleFinite F) :
    (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
      F source₁ source₂ baseIn) =
      ∑ᶠ t : ℤ × (ℤ × ℤ), F t.1 t.2.1 t.2.2 := by
  rw [finsum_curry (fun t : ℤ × (ℤ × ℤ) => F t.1 t.2.1 t.2.2) hF]
  exact finsum_congr fun source₁ =>
    (finsum_curry (fun q : ℤ × ℤ => F source₁ q.1 q.2)
      (triple_slice_finite hF source₁)).symm

omit [Module ℂ W] in
/-- Subtraction distributes through a triple contraction under the two exact joint-support
hypotheses. -/
theorem tripleFinsum_sub_distrib {F G : ℤ → ℤ → ℤ → W}
    (hF : TripleFinite F) (hG : TripleFinite G) :
    (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
      (F source₁ source₂ baseIn - G source₁ source₂ baseIn)) =
      (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        F source₁ source₂ baseIn) -
      ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        G source₁ source₂ baseIn := by
  have hsub := hF.sub hG
  rw [tripleFinsum_eq_prod hsub, tripleFinsum_eq_prod hF, tripleFinsum_eq_prod hG,
    finsum_sub_distrib hF hG]

/-! ## A shift-stable support predicate -/

/-- A translated contraction summand.  The six offsets shift the two kernel-source
coordinates, the two kernel-output coordinates, and the two payload-source coordinates.
The common-base coordinate is not shifted by either difference operator used below. -/
noncomputable def shiftedContractSummand (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (d₁ d₂ d₃ d₄ e₁ e₃ : ℤ)
    (outer₁ baseOut outer₂ source₁ source₂ baseIn : ℤ) : W :=
  K (-source₁ - 1 - d₁) (-source₂ - 1 - d₂)
      (outer₁ - d₃) (outer₂ - d₄) (baseOut - baseIn) •
    f (source₁ - e₁) baseIn (source₂ - e₃)

/-- Joint support remains finite after every finite coordinate translation relevant to
source/outer difference powers. -/
def ShiftContractFinite (K : FormalDist₄ (FormalDist ℂ)) (f : FormalDist₃ W) : Prop :=
  ∀ d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂,
    TripleFinite (shiftedContractSummand K f d₁ d₂ d₃ d₄ e₁ e₃
      outer₁ baseOut outer₂)

/-- The unshifted raw contraction summand is one instance of `shiftedContractSummand`. -/
theorem kernelContractSummand_eq_shifted (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (outer₁ baseOut outer₂ source₁ source₂ baseIn : ℤ) :
    kernelContractSummand K f outer₁ baseOut outer₂ source₁ source₂ baseIn =
      shiftedContractSummand K f 0 0 0 0 0 0
        outer₁ baseOut outer₂ source₁ source₂ baseIn := by
  simp [kernelContractSummand, shiftedContractSummand]

/-! ## Stability of the support interface -/

/-- The shift-stable support hypothesis survives one outer difference on the kernel. -/
theorem ShiftContractFinite.mulBySub₃₄ {K : FormalDist₄ (FormalDist ℂ)}
    {f : FormalDist₃ W} (hfin : ShiftContractFinite K f) :
    ShiftContractFinite (FormalDist₄.mulBySub₃₄ K) f := by
  intro d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂
  let F : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f d₁ d₂ (d₃ + 1) d₄ e₁ e₃
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let G : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f d₁ d₂ d₃ (d₄ + 1) e₁ e₃
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  have hF : TripleFinite F := hfin d₁ d₂ (d₃ + 1) d₄ e₁ e₃
    outer₁ baseOut outer₂
  have hG : TripleFinite G := hfin d₁ d₂ d₃ (d₄ + 1) e₁ e₃
    outer₁ baseOut outer₂
  rw [show shiftedContractSummand (FormalDist₄.mulBySub₃₄ K) f
        d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂ =
      (fun source₁ source₂ baseIn => F source₁ source₂ baseIn -
        G source₁ source₂ baseIn) by
    funext source₁ source₂ baseIn
    simp only [shiftedContractSummand, FormalDist₄.mulBySub₃₄_apply, F, G]
    change
      (K (-source₁ - 1 - d₁) (-source₂ - 1 - d₂)
          (outer₁ - d₃ - 1) (outer₂ - d₄) (baseOut - baseIn) -
        K (-source₁ - 1 - d₁) (-source₂ - 1 - d₂)
          (outer₁ - d₃) (outer₂ - d₄ - 1) (baseOut - baseIn)) •
        f (source₁ - e₁) baseIn (source₂ - e₃) = _
    rw [sub_smul]
    congr 2 <;> ring_nf]
  exact hF.sub hG

/-- The shift-stable support hypothesis survives one source difference on the kernel. -/
theorem ShiftContractFinite.mulBySub₁₂ {K : FormalDist₄ (FormalDist ℂ)}
    {f : FormalDist₃ W} (hfin : ShiftContractFinite K f) :
    ShiftContractFinite (FormalDist₄.mulBySub₁₂ K) f := by
  intro d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂
  let F : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f (d₁ + 1) d₂ d₃ d₄ e₁ e₃
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let G : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f d₁ (d₂ + 1) d₃ d₄ e₁ e₃
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  have hF : TripleFinite F := hfin (d₁ + 1) d₂ d₃ d₄ e₁ e₃
    outer₁ baseOut outer₂
  have hG : TripleFinite G := hfin d₁ (d₂ + 1) d₃ d₄ e₁ e₃
    outer₁ baseOut outer₂
  rw [show shiftedContractSummand (FormalDist₄.mulBySub₁₂ K) f
        d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂ =
      (fun source₁ source₂ baseIn => F source₁ source₂ baseIn -
        G source₁ source₂ baseIn) by
    funext source₁ source₂ baseIn
    simp only [shiftedContractSummand, FormalDist₄.mulBySub₁₂_apply, F, G]
    change
      (K (-source₁ - 1 - d₁ - 1) (-source₂ - 1 - d₂)
          (outer₁ - d₃) (outer₂ - d₄) (baseOut - baseIn) -
        K (-source₁ - 1 - d₁) (-source₂ - 1 - d₂ - 1)
          (outer₁ - d₃) (outer₂ - d₄) (baseOut - baseIn)) •
        f (source₁ - e₁) baseIn (source₂ - e₃) = _
    rw [sub_smul]
    congr 2 <;> ring_nf]
  exact hF.sub hG

/-- The shift-stable support hypothesis survives one source difference on the payload. -/
theorem ShiftContractFinite.payload_mulBySub₁₃ {K : FormalDist₄ (FormalDist ℂ)}
    {f : FormalDist₃ W} (hfin : ShiftContractFinite K f) :
    ShiftContractFinite K (mulBySub₁₃ f) := by
  intro d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂
  let F : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f d₁ d₂ d₃ d₄ (e₁ + 1) e₃
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let G : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f d₁ d₂ d₃ d₄ e₁ (e₃ + 1)
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  have hF : TripleFinite F := hfin d₁ d₂ d₃ d₄ (e₁ + 1) e₃
    outer₁ baseOut outer₂
  have hG : TripleFinite G := hfin d₁ d₂ d₃ d₄ e₁ (e₃ + 1)
    outer₁ baseOut outer₂
  rw [show shiftedContractSummand K (mulBySub₁₃ f)
        d₁ d₂ d₃ d₄ e₁ e₃ outer₁ baseOut outer₂ =
      (fun source₁ source₂ baseIn => F source₁ source₂ baseIn -
        G source₁ source₂ baseIn) by
    funext source₁ source₂ baseIn
    simp only [shiftedContractSummand, mulBySub₁₃_apply, F, G, smul_sub]
    congr 2 <;> ring_nf]
  exact hF.sub hG

/-- The support interface survives every outer difference power on the kernel. -/
theorem ShiftContractFinite.mulBySub₃₄Pow {K : FormalDist₄ (FormalDist ℂ)}
    {f : FormalDist₃ W} (hfin : ShiftContractFinite K f) (N : ℕ) :
    ShiftContractFinite (FormalDist₄.mulBySub₃₄Pow N K) f := by
  induction N with
  | zero => simpa only [FormalDist₄.mulBySub₃₄Pow_zero, LinearMap.id_apply]
  | succ N ih =>
      rw [FormalDist₄.mulBySub₃₄Pow_succ]
      exact ih.mulBySub₃₄

/-- The support interface survives every source difference power on the kernel. -/
theorem ShiftContractFinite.mulBySub₁₂Pow {K : FormalDist₄ (FormalDist ℂ)}
    {f : FormalDist₃ W} (hfin : ShiftContractFinite K f) (N : ℕ) :
    ShiftContractFinite (FormalDist₄.mulBySub₁₂Pow N K) f := by
  induction N with
  | zero => simpa only [FormalDist₄.mulBySub₁₂Pow_zero, LinearMap.id_apply]
  | succ N ih =>
      rw [FormalDist₄.mulBySub₁₂Pow_succ]
      exact ih.mulBySub₁₂

/-- The support interface survives every source difference power on the payload. -/
theorem ShiftContractFinite.payload_mulBySub₁₃Pow
    {K : FormalDist₄ (FormalDist ℂ)} {f : FormalDist₃ W}
    (hfin : ShiftContractFinite K f) (N : ℕ) :
    ShiftContractFinite K (mulBySub₁₃Pow N f) := by
  induction N with
  | zero => simpa only [mulBySub₁₃Pow_zero, LinearMap.id_apply]
  | succ N ih =>
      rw [mulBySub₁₃Pow_succ]
      exact ih.payload_mulBySub₁₃

/-! ## One outer difference -/

/-- Moving one `(outer₁-outer₂)` factor through contraction. -/
theorem kernelContract₁₂_mulBySub₃₄ (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (hfin : ShiftContractFinite K f) :
    kernelContract₁₂ (FormalDist₄.mulBySub₃₄ K) f =
      mulBySub₁₃ (kernelContract₁₂ K f) := by
  ext outer₁ baseOut outer₂
  rw [kernelContract₁₂_apply, mulBySub₁₃_apply,
    kernelContract₁₂_apply, kernelContract₁₂_apply]
  let F : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 0 0 1 0 0 0
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let G : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 0 0 0 1 0 0
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  have hF : TripleFinite F := hfin 0 0 1 0 0 0 outer₁ baseOut outer₂
  have hG : TripleFinite G := hfin 0 0 0 1 0 0 outer₁ baseOut outer₂
  rw [show (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
      kernelContractSummand (FormalDist₄.mulBySub₃₄ K) f
        outer₁ baseOut outer₂ source₁ source₂ baseIn) =
      ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        (F source₁ source₂ baseIn - G source₁ source₂ baseIn) from
    finsum_congr fun source₁ => finsum_congr fun source₂ => finsum_congr fun baseIn => by
      simp only [kernelContractSummand, FormalDist₄.mulBySub₃₄_apply,
        F, G, shiftedContractSummand]
      simp only [sub_zero]
      change
        (K (-source₁ - 1) (-source₂ - 1) (outer₁ - 1) outer₂
              (baseOut - baseIn) -
            K (-source₁ - 1) (-source₂ - 1) outer₁ (outer₂ - 1)
              (baseOut - baseIn)) • f source₁ baseIn source₂ = _
      exact sub_smul _ _ _]
  rw [tripleFinsum_sub_distrib hF hG]
  congr 1
  · exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
      finsum_congr fun baseIn => by simp [F, shiftedContractSummand, kernelContractSummand]
  · exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
      finsum_congr fun baseIn => by simp [G, shiftedContractSummand, kernelContractSummand]

/-! ## One source difference -/

/-- Moving one `(source₁-source₂)` factor from the scalar kernel onto the two source
coordinates of the payload.  The shift of the summation variables is a bijective `finsum`
reindexing; finite support is used only to distribute the two subtractions. -/
theorem kernelContract₁₂_mulBySub₁₂ (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (hfin : ShiftContractFinite K f) :
    kernelContract₁₂ (FormalDist₄.mulBySub₁₂ K) f =
      kernelContract₁₂ K (mulBySub₁₃ f) := by
  ext outer₁ baseOut outer₂
  rw [kernelContract₁₂_apply, kernelContract₁₂_apply]
  let F : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 1 0 0 0 0 0
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let G : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 0 1 0 0 0 0
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let P : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 0 0 0 0 1 0
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  let Q : ℤ → ℤ → ℤ → W := fun source₁ source₂ baseIn =>
    shiftedContractSummand K f 0 0 0 0 0 1
      outer₁ baseOut outer₂ source₁ source₂ baseIn
  have hF : TripleFinite F := hfin 1 0 0 0 0 0 outer₁ baseOut outer₂
  have hG : TripleFinite G := hfin 0 1 0 0 0 0 outer₁ baseOut outer₂
  have hP : TripleFinite P := hfin 0 0 0 0 1 0 outer₁ baseOut outer₂
  have hQ : TripleFinite Q := hfin 0 0 0 0 0 1 outer₁ baseOut outer₂
  have hleft :
      (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        kernelContractSummand (FormalDist₄.mulBySub₁₂ K) f
          outer₁ baseOut outer₂ source₁ source₂ baseIn) =
        (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          F source₁ source₂ baseIn) -
        ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          G source₁ source₂ baseIn := by
    rw [← tripleFinsum_sub_distrib hF hG]
    exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
      finsum_congr fun baseIn => by
        simp only [kernelContractSummand, FormalDist₄.mulBySub₁₂_apply,
          F, G, shiftedContractSummand]
        simp only [sub_zero]
        change
          (K (-source₁ - 1 - 1) (-source₂ - 1) outer₁ outer₂
                (baseOut - baseIn) -
              K (-source₁ - 1) (-source₂ - 1 - 1) outer₁ outer₂
                (baseOut - baseIn)) • f source₁ baseIn source₂ = _
        exact sub_smul _ _ _
  have hright :
      (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
        kernelContractSummand K (mulBySub₁₃ f)
          outer₁ baseOut outer₂ source₁ source₂ baseIn) =
        (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          P source₁ source₂ baseIn) -
        ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          Q source₁ source₂ baseIn := by
    rw [← tripleFinsum_sub_distrib hP hQ]
    exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
      finsum_congr fun baseIn => by
        simp only [kernelContractSummand, mulBySub₁₃_apply,
          P, Q, shiftedContractSummand, smul_sub, sub_zero]
  rw [hleft, hright]
  congr 1
  · calc
      (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          F source₁ source₂ baseIn) =
          ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
            P (source₁ + 1) source₂ baseIn := by
              exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
                finsum_congr fun baseIn => by
                  simp only [F, P, shiftedContractSummand]
                  congr 2 <;> ring_nf
      _ = ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
            P source₁ source₂ baseIn :=
          finsum_comp_equiv (Equiv.addRight (1 : ℤ))
            (f := fun source₁ => ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
              P source₁ source₂ baseIn)
  · calc
      (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
          G source₁ source₂ baseIn) =
          ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
            Q source₁ (source₂ + 1) baseIn := by
              exact finsum_congr fun source₁ => finsum_congr fun source₂ =>
                finsum_congr fun baseIn => by
                  simp only [G, Q, shiftedContractSummand]
                  congr 2 <;> ring_nf
      _ = ∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
            Q source₁ source₂ baseIn := by
          exact finsum_congr fun source₁ =>
            finsum_comp_equiv (Equiv.addRight (1 : ℤ))
              (f := fun source₂ => ∑ᶠ baseIn : ℤ, Q source₁ source₂ baseIn)

/-! ## Difference powers and locality transport -/

/-- Moving an arbitrary outer difference power through contraction. -/
theorem kernelContract₁₂_mulBySub₃₄Pow (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (hfin : ShiftContractFinite K f) (N : ℕ) :
    kernelContract₁₂ (FormalDist₄.mulBySub₃₄Pow N K) f =
      mulBySub₁₃Pow N (kernelContract₁₂ K f) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [FormalDist₄.mulBySub₃₄Pow_succ, mulBySub₁₃Pow_succ]
      change kernelContract₁₂
          (FormalDist₄.mulBySub₃₄ (FormalDist₄.mulBySub₃₄Pow N K)) f =
        mulBySub₁₃ (mulBySub₁₃Pow N (kernelContract₁₂ K f))
      rw [kernelContract₁₂_mulBySub₃₄
        (FormalDist₄.mulBySub₃₄Pow N K) f (hfin.mulBySub₃₄Pow N), ih]

/-- Iterating `mulBySub₁₃` before or after its own power gives the same payload. -/
private theorem mulBySub₁₃Pow_self_comm (N : ℕ) (f : FormalDist₃ W) :
    mulBySub₁₃Pow N (mulBySub₁₃ f) =
      mulBySub₁₃ (mulBySub₁₃Pow N f) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [mulBySub₁₃Pow_succ]
      change mulBySub₁₃ (mulBySub₁₃Pow N (mulBySub₁₃ f)) =
        mulBySub₁₃ (mulBySub₁₃ (mulBySub₁₃Pow N f))
      rw [ih]

/-- Moving an arbitrary source difference power from the scalar kernel onto the payload. -/
theorem kernelContract₁₂_mulBySub₁₂Pow (K : FormalDist₄ (FormalDist ℂ))
    (f : FormalDist₃ W) (hfin : ShiftContractFinite K f) (N : ℕ) :
    kernelContract₁₂ (FormalDist₄.mulBySub₁₂Pow N K) f =
      kernelContract₁₂ K (mulBySub₁₃Pow N f) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
      rw [FormalDist₄.mulBySub₁₂Pow_succ, mulBySub₁₃Pow_succ]
      change kernelContract₁₂
          (FormalDist₄.mulBySub₁₂ (FormalDist₄.mulBySub₁₂Pow N K)) f =
        kernelContract₁₂ K (mulBySub₁₃ (mulBySub₁₃Pow N f))
      rw [kernelContract₁₂_mulBySub₁₂
        (FormalDist₄.mulBySub₁₂Pow N K) f (hfin.mulBySub₁₂Pow N),
        ih (mulBySub₁₃ f) hfin.payload_mulBySub₁₃,
        mulBySub₁₃Pow_self_comm]

/-- Li's double-delta kernel transports a source locality power to the same locality power
on the contracted output.  This is the support-aware semantic bridge missing from the raw
kernel equality. -/
theorem kernelContract₁₂_doubleDelta_locality_transport (o₁ o₂ : Orientation)
    (N : ℕ) (f : FormalDist₃ W)
    (hfin : ShiftContractFinite (doubleDelta o₁ o₂) f) :
    mulBySub₁₃Pow N (kernelContract₁₂ (doubleDelta o₁ o₂) f) =
      kernelContract₁₂ (doubleDelta o₁ o₂) (mulBySub₁₃Pow N f) := by
  calc
    mulBySub₁₃Pow N (kernelContract₁₂ (doubleDelta o₁ o₂) f) =
        kernelContract₁₂
          (FormalDist₄.mulBySub₃₄Pow N (doubleDelta o₁ o₂)) f :=
      (kernelContract₁₂_mulBySub₃₄Pow (doubleDelta o₁ o₂) f hfin N).symm
    _ = kernelContract₁₂
          (FormalDist₄.mulBySub₁₂Pow N (doubleDelta o₁ o₂)) f :=
      kernelContract₁₂_doubleDelta_transport o₁ o₂ N f
    _ = kernelContract₁₂ (doubleDelta o₁ o₂) (mulBySub₁₃Pow N f) :=
      kernelContract₁₂_mulBySub₁₂Pow (doubleDelta o₁ o₂) f hfin N

/-- In particular, source locality implies locality of the double-delta contraction. -/
theorem kernelContract₁₂_doubleDelta_eq_zero_of_local (o₁ o₂ : Orientation)
    (N : ℕ) (f : FormalDist₃ W)
    (hfin : ShiftContractFinite (doubleDelta o₁ o₂) f)
    (hlocal : mulBySub₁₃Pow N f = 0) :
    mulBySub₁₃Pow N (kernelContract₁₂ (doubleDelta o₁ o₂) f) = 0 := by
  rw [kernelContract₁₂_doubleDelta_locality_transport o₁ o₂ N f hfin, hlocal]
  ext outer₁ baseOut outer₂
  rw [kernelContract₁₂_apply]
  change (∑ᶠ source₁ : ℤ, ∑ᶠ source₂ : ℤ, ∑ᶠ baseIn : ℤ,
    doubleDelta o₁ o₂ (-source₁ - 1) (-source₂ - 1) outer₁ outer₂
      (baseOut - baseIn) • (0 : W)) = 0
  simp only [smul_zero, finsum_zero]

end FormalDist₄Delta

end VOA

section AxiomAudit
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_mulBySub₃₄Pow
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_mulBySub₁₂Pow
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_doubleDelta_locality_transport
#print axioms VOA.FormalDist₄Delta.kernelContract₁₂_doubleDelta_eq_zero_of_local
end AxiomAudit
