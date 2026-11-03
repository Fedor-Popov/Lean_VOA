/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.VertexOperatorAlgebra
import VOA.Foundations.Substitution
import VOA.Foundations.Expansion

/-!
# First-order deformations of a vertex operator algebra

This file defines, elementarily, what it means to deform the state–field correspondence `Y` of a
vertex operator algebra `W` to first order in a square-zero parameter `t`, together with the
notions of *trivial* deformation, *rigidity*, *regularity* (the hypothesis of the target paper's
Theorem 3.1) and the *pole coefficient* that Theorem 3.1 is about.

**No cohomology theory is built here, and none is needed.** The reading "equivalence classes of
first-order deformations `=` `H²` of the deformation complex" is an *interpretation*: the cocycle
condition is `FirstOrderDeformation.jacobi` below, the coboundaries are `Deform.coboundaries`, and
`IsRigid` says every cocycle is a coboundary. All three are elementary statements about modes.

## The shape of the deformed datum (a design choice, recorded)

The repository's state–field correspondence is
`PreVertexAlgebra.Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧`, a **linear map into formal distributions with
`End ℂ 𝒱` coefficients**. We give `Y₁` **exactly that shape**:

`Y1 : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧`.

The alternative shapes we did *not* take, and why:

* `𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] FormalDist 𝒱` (a bilinear map landing in `𝒱`-valued distributions). Equivalent,
  but it does not compose with the repository's `mode`/`smul` API without a translation layer.
* a family of bilinear products `(u, n, v) ↦ u¹₍ₙ₎v` indexed by `n : ℤ`. Also equivalent
  (`smul₁` below *is* that family), but then linearity in `u` has to be re-imposed by hand as
  three extra axioms instead of coming for free from `→ₗ`.

## Coefficient conventions (checked against `Foundations.FormalSeries`/`FormalCalculus`)

* `FormalDist 𝒲 = ℤ → 𝒲` is indexed by the **`z`-exponent**: `f k` is the coefficient of `zᵏ`
  (`Foundations.FormalSeries`, docstring of `FormalDist`).
* `mode f n = f (-n - 1)` (`Foundations.FormalCalculus.mode`), so `u₍ₙ₎ = ` coefficient of
  `z^{-n-1}`, matching `Y(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`.
* Consequently, for a distribution `f`:
  - "`f` contains **no negative powers** of `z`" `⟺ ∀ k < 0, f k = 0 ⟺ ∀ n ≥ 0, mode f n = 0`;
  - "the coefficient of `z^{-2}` in `f`" `= f (-2) = mode f 1`.

  Both readings are recorded as lemmas (`regular_iff`, `poleVec_eq_coeff`) so no downstream file
  has to re-derive the index arithmetic.

## The derivation of the axioms (expand to order `t`, discard `t²`)

Let `R = ℂ[t]/(t²)`, let `𝒱_R = R ⊗_ℂ 𝒱`, keep the vacuum `𝟙` and set

`Yᵗ(u,x)v := Y(u,x)v + t · Y₁(u,x)v`,

extended `R`-bilinearly. In modes: `uᵗ₍ₙ₎v = u₍ₙ₎v + t·u¹₍ₙ₎v`, where `u¹₍ₙ₎v := mode (Y₁ u) n v`.
Now impose the vertex-algebra axioms on `(𝒱_R, Yᵗ, 𝟙)` over `R` and split each by powers of `t`.
The `t⁰` part is always the corresponding axiom of `W` and carries no information; the `t¹` part is
the axiom recorded below. (`t²` and higher are discarded: that is exactly what "first order" means.)

* **VA5, truncation.** `uᵗ₍ₙ₎v = 0` for `n ≫ 0`. Order `t¹`: `u¹₍ₙ₎v = 0` for `n ≫ 0`.
  ⟶ field `truncation`.
* **VA2, vacuum field.** `Yᵗ(𝟙,x) = id`. The right-hand side has no `t`, so order `t¹` gives
  `Y₁(𝟙,x) = 0`. ⟶ field `vacuum_Y1`.
* **VA3, creation.** `uᵗ₍ₙ₎𝟙 = 0` for `n ≥ 0` and `uᵗ₍₋₁₎𝟙 = u`. The state `u` on the right carries
  no `t` (we deform `Y`, not the underlying space), so order `t¹` gives `u¹₍ₙ₎𝟙 = 0` for `n ≥ 0`
  **and** `u¹₍₋₁₎𝟙 = 0`, i.e. `u¹₍ₙ₎𝟙 = 0` for every `n ≥ -1`. ⟶ field `creation`.
* **VA4, locality.** *Not imposed separately.* Over any commutative base, locality together with
  the remaining axioms is equivalent to the Jacobi/Borcherds identity, and we impose the latter
  (in this repository that equivalence is the content of `Core.Reconstruction`/`Core.Borcherds`).
* **Jacobi/Borcherds (Gannon 5.1.7b).** The identity proved for `W` in `Core.Borcherds.jacobi` is
  `∑ᶠ i, (-1)ⁱ C(ℓ,i)·(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − (-1)^ℓ·v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x))`
  `  = ∑ᶠ i, C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`.
  Every term is **quadratic** in `Y`, so substituting `u₍ₖ₎ ↦ u₍ₖ₎ + t·u¹₍ₖ₎` and dropping `t²`
  leaves, at order `t`, the sum over the two ways of placing a single `Y₁` — the Leibniz
  ("derivative") of the identity. On the left the two placements are the inner and the outer mode;
  on the right they are the inner product `u¹₍ℓ₊ᵢ₎v` and the outer mode `(·)¹₍ₘ₊ₙ₋ᵢ₎`:

  `∑ᶠ i, (-1)ⁱ C(ℓ,i)·( u¹₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) + u₍ℓ₊ₘ₋ᵢ₎(v¹₍ₙ₊ᵢ₎x)`
  `                     − (-1)^ℓ·[ v¹₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎x) + v₍ℓ₊ₙ₋ᵢ₎(u¹₍ₘ₊ᵢ₎x) ] )`
  `  = ∑ᶠ i, C(m,i)·( (u¹₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x + (u₍ℓ₊ᵢ₎v)¹₍ₘ₊ₙ₋ᵢ₎x )`.

  ⟶ field `jacobi`. This is the "`Y₁` is a 2-cocycle" condition; it is *linear* in `Y₁`, which is
  what makes `coboundaries` a subspace and the whole picture cohomological.

  Both `∑ᶠ` are genuinely finite sums: `jacobiLHS_support_finite` and `jacobiRHS_support_finite`
  prove it from `truncation` together with `W`'s VA5. (Without that check the axiom could have
  been vacuous, since `finsum` of a non-finitely-supported family is `0` by fiat.)

## Two further conventions, stated rather than silently chosen

1. **The vacuum is not deformed.** We keep `𝟙ᵗ = 𝟙`. The alternative is to allow
   `𝟙ᵗ = 𝟙 + t·𝟙′`; it gives nothing new, because `𝟙′` can be gauged away by the coboundary of
   `φ := −(the operator v ↦ 𝟙′₍₋₁₎v)`, at the cost of a longer definition. We take the rigid
   vacuum; the deformed vacuum is a strictly redundant generalisation.
2. **The grading axiom VA1 is *not* a field.** Its first-order part,
   `u¹₍ₙ₎ : 𝒱ₖ ⊗ 𝒱ₗ → 𝒱_{k+ℓ-n-1}`, is offered as the separate predicate `IsGraded`. Reason: the
   task's axiom list is truncation + vacuum + Jacobi, and an ungraded first-order deformation is a
   perfectly good object; but the notion of *trivial* deformation (a grading-preserving `φ`) and
   the hypotheses of Theorem 3.1 both live in the graded category, so the predicate is needed and
   is used exactly where it is needed (`poleVec_mem_grading_zero`, `exists_hasPoleCoeff`). The
   alternative — making it a field — would silently strengthen `FirstOrderDeformation`.

## Cohomological reading (interpretation only; nothing below depends on it)

`FirstOrderDeformation W` is the space of 2-cocycles of the deformation ("`½`") complex of `W`;
`Deform.coboundaries W` is the space of 2-coboundaries `δφ` with
`(δφ)(u,x)v = Y(φu,x)v − φ(Y(u,x)v) + Y(u,x)φv`; the quotient is `H²_{1/2}(V,V)`, and
`IsRigid W` says that quotient vanishes. We construct **no** complex, no differential and no
quotient: every statement below is elementary.

## Main declarations

* `Deform.FirstOrderDeformation W` — the data `Y₁` plus the three first-order axioms.
* `Deform.FirstOrderDeformation.smul₁` — the deformed products `u¹₍ₙ₎v`, with linearity API.
* `Deform.GradePreserving`, `Deform.FirstOrderDeformation.IsGraded`.
* `Deform.IsCoboundary`, `Deform.FirstOrderDeformation.IsTrivial`, `Deform.coboundaries`,
  `Deform.IsRigid`.
* `Deform.zeroDeformation`, `Deform.isTrivial_zeroDeformation`.
* `Deform.FirstOrderDeformation.Regular`, `poleVec`, `poleCoeff`, `HasPoleCoeff`.

## Dependencies
* `VOA.Core.VertexOperatorAlgebra` (the VOA structure and the `smul` mode API),
* `VOA.Foundations.Substitution` (`cbz`, the `ℤ`-indexed binomial),
* `VOA.Foundations.Expansion` (`negOnePow`).

## References
* Gannon §5.1.3 (the axioms being deformed), eq. 5.1.7b (the identity being differentiated).
* `Core.Borcherds.jacobi` — the undeformed identity whose first-order variation is `jacobi`.
-/

namespace VOA

namespace Deform

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Every coefficient of the zero formal distribution is zero. Needed explicitly because
`FormalDist` is an opaque type synonym for `ℤ → 𝒲` (deliberately, to keep the pointwise ring of
`ℤ → 𝒲` out — see `Foundations.FormalSeries`), so `Pi.zero_apply` does not fire on it, while the
`@[simp]` lemma `mode_apply` does rewrite `mode f m` to `f (-m-1)`. -/
@[simp] theorem zero_dist_apply {𝒲 : Type*} [AddCommGroup 𝒲] (k : ℤ) :
    (0 : FormalDist 𝒲) k = 0 := rfl

/-! ## The structure -/

/-- A **first-order deformation** of the vertex operator algebra `W`: a bilinear `Y₁`, of the same
shape as `W.Y`, such that `Yᵗ := Y + t·Y₁` is a vertex algebra structure on `ℂ[t]/(t²) ⊗ 𝒱` with
the same vacuum. The fields are precisely the order-`t` parts of VA5, VA2, VA3 and the
Jacobi/Borcherds identity; see the file docstring for the term-by-term expansion. -/
structure FirstOrderDeformation (W : VertexOperatorAlgebra 𝒱) where
  /-- The first-order piece of the deformed state–field correspondence,
  `Yᵗ(u,x) = Y(u,x) + t·Y₁(u,x)`. Same shape as `W.Y`. -/
  Y1 : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  /-- **Order-`t` VA5 (truncation).** For each `u, v` the deformed products `u¹₍ₙ₎v` vanish for
  `n` large. -/
  truncation : ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y1 u) n v = 0
  /-- **Order-`t` VA2 (vacuum field).** `Yᵗ(𝟙,x) = id` has no `t`-part, so `Y₁(𝟙,x) = 0`. -/
  vacuum_Y1 : Y1 W.vacuum = 0
  /-- **Order-`t` VA3 (creation).** `uᵗ₍ₙ₎𝟙 = 0` for `n ≥ 0` and `uᵗ₍₋₁₎𝟙 = u` together give
  `u¹₍ₙ₎𝟙 = 0` for all `n ≥ -1`. -/
  creation : ∀ (u : 𝒱) (n : ℤ), -1 ≤ n → mode (Y1 u) n W.vacuum = 0
  /-- **Order-`t` Jacobi/Borcherds identity** (the Leibniz variation of Gannon 5.1.7b in the
  direction `Y₁`): on each side, sum over the two ways of inserting a single `Y₁`. -/
  jacobi : ∀ (u v x : 𝒱) (ℓ m n : ℤ),
      (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (Y1 u) (ℓ + m - i) (W.smul v (n + i) x)
            + W.smul u (ℓ + m - i) (mode (Y1 v) (n + i) x)
            - negOnePow ℓ •
              (mode (Y1 v) (ℓ + n - i) (W.smul u (m + i) x)
                + W.smul v (ℓ + n - i) (mode (Y1 u) (m + i) x))))
        = ∑ᶠ i : ℤ, cbz m i •
            (W.smul (mode (Y1 u) (ℓ + i) v) (m + n - i) x
              + mode (Y1 (W.smul u (ℓ + i) v)) (m + n - i) x)

namespace FirstOrderDeformation

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The deformed products `u¹₍ₙ₎v` -/

/-- The **first-order product** `u¹₍ₙ₎v := mode (Y₁ u) n v`: the coefficient of `x^{-n-1}` in
`Y₁(u,x)v`. Mirrors `PreVertexAlgebra.smul`. -/
def smul₁ (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (D.Y1 u) n v

/-- The correction to the nth product is obtained by selecting the nth mode of the correction field.
This is the link between the field-valued data and the two-state product notation used in
proofs. -/
theorem smul₁_def (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    D.smul₁ u n v = mode (D.Y1 u) n v := rfl

/-- `u¹₍ₙ₎v` is the `x^{-n-1}` coefficient of `Y₁(u,x)v`. -/
theorem smul₁_eq_coeff (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    D.smul₁ u n v = D.Y1 u (-n - 1) v := rfl

/-- The first-order correction is additive in the state whose field acts. A field attached to a sum
of states is the sum of their fields. -/
@[simp] theorem smul₁_add_left (D : FirstOrderDeformation W) (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    D.smul₁ (u₁ + u₂) n v = D.smul₁ u₁ n v + D.smul₁ u₂ n v := by
  simp only [smul₁_def, map_add, mode_add, LinearMap.add_apply]

/-- Rescaling the state whose field acts rescales the correction by the same complex number.
Together with additivity this gives linearity in the first state. -/
@[simp] theorem smul₁_smul_left (D : FirstOrderDeformation W) (c : ℂ) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    D.smul₁ (c • u) n v = c • D.smul₁ u n v := by
  simp only [smul₁_def, map_smul, mode_smul, LinearMap.smul_apply]

/-- The zero state contributes no correction field, so all of its corrected products vanish. -/
@[simp] theorem smul₁_zero_left (D : FirstOrderDeformation W) (n : ℤ) (v : 𝒱) :
    D.smul₁ 0 n v = 0 := by
  simp only [smul₁_def, map_zero, mode_zero, LinearMap.zero_apply]

/-- The correction field acts linearly on its target: applying it to a sum adds the two corrected
products. -/
@[simp] theorem smul₁_add_right (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    D.smul₁ u n (v₁ + v₂) = D.smul₁ u n v₁ + D.smul₁ u n v₂ :=
  map_add (mode (D.Y1 u) n) v₁ v₂

/-- A scalar multiplying the target state passes through the correction field. The first-order
products are therefore complex bilinear in their two states. -/
@[simp] theorem smul₁_smul_right (D : FirstOrderDeformation W) (u : 𝒱) (c : ℂ) (n : ℤ) (v : 𝒱) :
    D.smul₁ u n (c • v) = c • D.smul₁ u n v :=
  map_smul (mode (D.Y1 u) n) c v

/-- Every correction mode is a linear operator, so it sends the zero target state to zero. -/
@[simp] theorem smul₁_zero_right (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) :
    D.smul₁ u n 0 = 0 :=
  map_zero (mode (D.Y1 u) n)

/-! ## The axioms, restated in the `smul₁` API -/

/-- **Order-`t` VA5** in the `smul₁` API. -/
theorem smul₁_eventually_zero (D : FirstOrderDeformation W) (u v : 𝒱) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → D.smul₁ u n v = 0 := D.truncation u v

/-- **Order-`t` VA2** in the `smul₁` API: `𝟙¹₍ₙ₎v = 0`. -/
@[simp] theorem smul₁_vacuum_left (D : FirstOrderDeformation W) (n : ℤ) (v : 𝒱) :
    D.smul₁ W.vacuum n v = 0 := by
  simp only [smul₁_def, D.vacuum_Y1, mode_zero, LinearMap.zero_apply]

/-- **Order-`t` VA3** in the `smul₁` API: `u¹₍ₙ₎𝟙 = 0` for `n ≥ -1`. -/
theorem smul₁_vacuum_right (D : FirstOrderDeformation W) (u : 𝒱) (n : ℤ) (hn : -1 ≤ n) :
    D.smul₁ u n W.vacuum = 0 := D.creation u n hn

/-- **Order-`t` VA3**, in coefficient form: `Y₁(u,x)𝟙` has no coefficient in degree `≤ 0`, i.e.
`Y₁(u,x)𝟙 ∈ x·𝒱[[x]]`. -/
theorem Y1_vacuum_coeff (D : FirstOrderDeformation W) (u : 𝒱) (k : ℤ) (hk : k ≤ 0) :
    D.Y1 u k W.vacuum = 0 := by
  have h := D.creation u (-k - 1) (by omega)
  rwa [mode_apply, show -(-k - 1) - 1 = k from by ring] at h

/-- **Order-`t` Jacobi/Borcherds**, in the `smul₁` API. -/
theorem borcherds₁ (D : FirstOrderDeformation W) (u v x : 𝒱) (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (D.smul₁ u (ℓ + m - i) (W.smul v (n + i) x)
          + W.smul u (ℓ + m - i) (D.smul₁ v (n + i) x)
          - negOnePow ℓ •
            (D.smul₁ v (ℓ + n - i) (W.smul u (m + i) x)
              + W.smul v (ℓ + n - i) (D.smul₁ u (m + i) x))))
      = ∑ᶠ i : ℤ, cbz m i •
          (W.smul (D.smul₁ u (ℓ + i) v) (m + n - i) x
            + D.smul₁ (W.smul u (ℓ + i) v) (m + n - i) x) :=
  D.jacobi u v x ℓ m n

/-! ## The two `finsum`s really are finite sums

Without these, `jacobi` could be a statement about `finsum`s of families with infinite support,
which `Mathlib` defines to be `0` — the axiom would then say `0 = 0`. Both bounds come from
`truncation` together with `W`'s VA5, exactly as `Core.Borcherds.BR_fin`/`Puv_fin` do upstream. -/

/-- Only finitely many indices contribute to the commutator side of linearized Jacobi. Negative
indices have zero binomial coefficient; sufficiently large indices kill the target by
truncation. This justifies treating the formal finite sum as a genuine sum rather than the
default value assigned to infinite support. -/
theorem jacobiLHS_support_finite (D : FirstOrderDeformation W) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (D.smul₁ u (ℓ + m - i) (W.smul v (n + i) x)
          + W.smul u (ℓ + m - i) (D.smul₁ v (n + i) x)
          - negOnePow ℓ •
            (D.smul₁ v (ℓ + n - i) (W.smul u (m + i) x)
              + W.smul v (ℓ + n - i) (D.smul₁ u (m + i) x)))).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  obtain ⟨Mv, hMv⟩ := D.smul₁_eventually_zero v x
  obtain ⟨Mu, hMu⟩ := D.smul₁_eventually_zero u x
  refine Set.Finite.subset
    (Set.finite_Icc 0 (max (max (Nv - n) (Mv - n)) (max (Nu - m) (Mu - m)))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [max_lt_iff, max_lt_iff, max_lt_iff] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
    rw [hNv (n + i) (by omega), hMv (n + i) (by omega), hNu (m + i) (by omega),
      hMu (m + i) (by omega)]
    simp

/-- The iterate side of linearized Jacobi also has finite support. Above a common bound, both the
ordinary and corrected inner products vanish; negative indices have zero binomial coefficient.
The Jacobi axiom thus imposes an actual finite identity. -/
theorem jacobiRHS_support_finite (D : FirstOrderDeformation W) (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support fun i : ℤ => cbz m i •
        (W.smul (D.smul₁ u (ℓ + i) v) (m + n - i) x
          + D.smul₁ (W.smul u (ℓ + i) v) (m + n - i) x)).Finite := by
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  obtain ⟨M, hM⟩ := D.smul₁_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Icc 0 (max (N - ℓ) (M - ℓ))) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [hN (ℓ + i) (by omega), hM (ℓ + i) (by omega)]
    simp

/-! ## Grading compatibility (VA1 at order `t`) — a predicate, not a field -/

/-- **Order-`t` VA1.** The deformation is *graded* when `u¹₍ₙ₎` shifts the degree the same way
`u₍ₙ₎` does: `𝒱ₖ ⊗ 𝒱ₗ → 𝒱_{k+ℓ-n-1}`. Kept as a predicate rather than a structure field; see the
file docstring, convention 2. -/
def IsGraded (D : FirstOrderDeformation W) : Prop :=
  ∀ (k ℓ : ℤ) (u : 𝒱), u ∈ W.grading k → ∀ (v : 𝒱), v ∈ W.grading ℓ → ∀ (n : ℤ),
    D.smul₁ u n v ∈ W.grading (k + ℓ - n - 1)

end FirstOrderDeformation

/-! ## Trivial deformations and the space of coboundaries -/

/-- A linear map `φ : 𝒱 →ₗ[ℂ] 𝒱` **preserves the grading** of `W` when it maps each `𝒱ₙ` into
itself. -/
def GradePreserving (W : VertexOperatorAlgebra 𝒱) (φ : 𝒱 →ₗ[ℂ] 𝒱) : Prop :=
  ∀ (k : ℤ) (u : 𝒱), u ∈ W.grading k → φ u ∈ W.grading k

/-- `f` is a **coboundary** when it is `δφ` for a grading-preserving `φ` killing the vacuum:
`f(u,x)v = Y(φu,x)v − φ(Y(u,x)v) + Y(u,x)φv`, i.e. in modes
`f-product(u,n,v) = (φu)₍ₙ₎v − φ(u₍ₙ₎v) + u₍ₙ₎(φv)`.

The sign convention is the one in which `δφ` measures the failure of `φ` to be a derivation of
every `n`-th product; the opposite overall sign gives the same subspace, so nothing downstream can
depend on the choice. -/
def IsCoboundary (W : VertexOperatorAlgebra 𝒱) (f : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧) : Prop :=
  ∃ φ : 𝒱 →ₗ[ℂ] 𝒱, φ W.vacuum = 0 ∧ GradePreserving W φ ∧
    ∀ (u : 𝒱) (n : ℤ) (v : 𝒱),
      mode (f u) n v = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v)

namespace FirstOrderDeformation

variable {W : VertexOperatorAlgebra 𝒱}

/-- A first-order deformation is **trivial** when its `Y₁` is a coboundary: there is a
grading-preserving `φ` with `φ𝟙 = 0` and
`u¹₍ₙ₎v = (φu)₍ₙ₎v − φ(u₍ₙ₎v) + u₍ₙ₎(φv)`.  Equivalently, `Yᵗ` is obtained from `Y` by the
`R`-linear change of variables `1 + tφ` of `𝒱_R`. -/
def IsTrivial (D : FirstOrderDeformation W) : Prop := IsCoboundary W D.Y1

/-- Unpack triviality into a concrete linear change of coordinates. The map must kill the vacuum,
preserve every grade, and produce the correction through its action on both inputs minus its
action on the output. Triviality allows a nonzero correction; it means the algebra has only been
rewritten in new coordinates. -/
theorem isTrivial_iff (D : FirstOrderDeformation W) :
    D.IsTrivial ↔ ∃ φ : 𝒱 →ₗ[ℂ] 𝒱, φ W.vacuum = 0 ∧ GradePreserving W φ ∧
      ∀ (u : 𝒱) (n : ℤ) (v : 𝒱),
        D.smul₁ u n v = W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v) := Iff.rfl

end FirstOrderDeformation

/-- **`W` is rigid to first order** when every first-order deformation is trivial.

⚠ **Not a useful rigidity notion.**  `FirstOrderDeformation` does not require the deformation to
respect the grading, while `IsTrivial` asks for a *grade-preserving* coboundary.  Hence the
ungraded coboundary deformation `δL₁` (`l1Deformation`) is never trivial, and `IsRigid` fails for
every `V(c,0)` for this definitional reason (`not_isRigid_virasoroVOA`,
`Examples/NonzeroDeformation.lean`).  Use `IsRigidGraded` (`Core.DeformationGraded`) instead. -/
def IsRigid (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : FirstOrderDeformation W, D.IsTrivial

/-- The **coboundaries** form a subspace of the ambient space of bilinear maps: this is the
"`δ` is linear" half of the cohomological picture, proved directly. -/
def coboundaries (W : VertexOperatorAlgebra 𝒱) :
    Submodule ℂ (𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧) where
  carrier := {f | IsCoboundary W f}
  add_mem' {f g} hf hg := by
    obtain ⟨φ, hφ0, hφg, hφ⟩ := hf
    obtain ⟨ψ, hψ0, hψg, hψ⟩ := hg
    change IsCoboundary W (f + g)
    refine ⟨φ + ψ, by simp [hφ0, hψ0], fun k u hu =>
      Submodule.add_mem _ (hφg k u hu) (hψg k u hu), fun u n v => ?_⟩
    have hfg : mode ((f + g) u) n v = mode (f u) n v + mode (g u) n v := by
      simp only [LinearMap.add_apply, mode_add, LinearMap.add_apply]
    rw [hfg, hφ u n v, hψ u n v]
    simp only [LinearMap.add_apply, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right]
    abel
  zero_mem' := by
    change IsCoboundary W 0
    refine ⟨0, rfl, fun k u _ => Submodule.zero_mem _, fun u n v => ?_⟩
    simp
  smul_mem' c f hf := by
    obtain ⟨φ, hφ0, hφg, hφ⟩ := hf
    change IsCoboundary W (c • f)
    refine ⟨c • φ, by simp [hφ0], fun k u hu => Submodule.smul_mem _ c (hφg k u hu),
      fun u n v => ?_⟩
    have hcf : mode ((c • f) u) n v = c • mode (f u) n v := by
      simp only [LinearMap.smul_apply, mode_smul, LinearMap.smul_apply]
    rw [hcf, hφ u n v]
    simp only [LinearMap.smul_apply, PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
      smul_sub, smul_add]

/-- Membership in the coboundary subspace is exactly the existence of the allowed infinitesimal
coordinate change. This translates a geometric interpretation into the subspace language needed
for cohomology. -/
@[simp] theorem mem_coboundaries {W : VertexOperatorAlgebra 𝒱}
    {f : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧} : f ∈ coboundaries W ↔ IsCoboundary W f := Iff.rfl

/-- A deformation is trivial exactly when its `Y₁` lies in the subspace of coboundaries. -/
theorem isTrivial_iff_mem_coboundaries {W : VertexOperatorAlgebra 𝒱}
    (D : FirstOrderDeformation W) : D.IsTrivial ↔ D.Y1 ∈ coboundaries W := Iff.rfl

/-! ### Closure properties (target (d)) -/

/-- The zero map is a coboundary (take `φ = 0`). -/
theorem isCoboundary_zero (W : VertexOperatorAlgebra 𝒱) :
    IsCoboundary W (0 : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧) := (coboundaries W).zero_mem

/-- Coboundaries are closed under addition. -/
theorem IsCoboundary.add {W : VertexOperatorAlgebra 𝒱} {f g : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧}
    (hf : IsCoboundary W f) (hg : IsCoboundary W g) : IsCoboundary W (f + g) :=
  (coboundaries W).add_mem hf hg

/-- Coboundaries are closed under scalar multiplication. -/
theorem IsCoboundary.smul {W : VertexOperatorAlgebra 𝒱} {f : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧} (c : ℂ)
    (hf : IsCoboundary W f) : IsCoboundary W (c • f) :=
  (coboundaries W).smul_mem c hf

/-- Two trivial deformations have trivial sum: the triviality of a deformation depends only on
`Y₁`, and the coboundaries are a subspace. -/
theorem isCoboundary_add_Y1 {W : VertexOperatorAlgebra 𝒱} {D E : FirstOrderDeformation W}
    (hD : D.IsTrivial) (hE : E.IsTrivial) : IsCoboundary W (D.Y1 + E.Y1) :=
  IsCoboundary.add hD hE

/-- A scalar multiple of a trivial deformation is trivial. -/
theorem isCoboundary_smul_Y1 {W : VertexOperatorAlgebra 𝒱} {D : FirstOrderDeformation W} (c : ℂ)
    (hD : D.IsTrivial) : IsCoboundary W (c • D.Y1) :=
  IsCoboundary.smul c hD

/-! ### The zero deformation -/

/-- The **zero deformation** `Y₁ = 0`: every axiom is immediate. -/
def zeroDeformation (W : VertexOperatorAlgebra 𝒱) : FirstOrderDeformation W where
  Y1 := 0
  truncation := fun _ _ => ⟨0, fun _ _ => by simp⟩
  vacuum_Y1 := rfl
  creation := fun _ _ _ => by simp
  jacobi := fun _ _ _ _ _ _ => by simp

/-- The distinguished zero deformation has no correction field at all: the original state-field
correspondence is unchanged. -/
@[simp] theorem zeroDeformation_Y1 (W : VertexOperatorAlgebra 𝒱) :
    (zeroDeformation W).Y1 = 0 := rfl

/-- **The zero deformation is trivial** (target (d), first half). -/
theorem isTrivial_zeroDeformation (W : VertexOperatorAlgebra 𝒱) :
    (zeroDeformation W).IsTrivial := isCoboundary_zero W

namespace FirstOrderDeformation

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## Regularity and the pole coefficient (the paper's Theorem 3.1) -/

/-- Recorded for readability: by VA3, `a₍₋₁₎𝟙 = a`, so the paper's `Y₁(a₍₋₁₎𝟙, x)(b₍₋₁₎𝟙)` is
literally `Y₁(a,x)b`. -/
theorem smul_neg_one_vacuum (a : 𝒱) : W.smul a (-1) W.vacuum = a :=
  W.toPreVertexAlgebra.smul_vacuum_neg_one a

/-- **Regularity** — the hypothesis of the target paper's Theorem 3.1. For weight-one `a, b`, the
series `Y₁(a₍₋₁₎𝟙, x)(b₍₋₁₎𝟙) = Y₁(a,x)b` contains **no negative powers of `x`**.

Stated in the repository's index convention: `FormalDist` is indexed by the `z`-exponent and
`mode f n = f (-n-1)`, so "no negative powers" is "`mode` vanishes for every `n ≥ 0`", i.e.
`a¹₍ₙ₎b = 0` for `n ≥ 0`. The literal coefficient form is `regular_iff`. -/
def Regular (D : FirstOrderDeformation W) : Prop :=
  ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1, ∀ n : ℤ, 0 ≤ n → D.smul₁ a n b = 0

/-- `Regular` in literal coefficient form: every coefficient of `xᵏ` with `k < 0` vanishes. -/
theorem regular_iff (D : FirstOrderDeformation W) :
    D.Regular ↔ ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1, ∀ k : ℤ, k < 0 → D.Y1 a k b = 0 := by
  constructor
  · intro h a ha b hb k hk
    have hk' := h a ha b hb (-k - 1) (by omega)
    rwa [smul₁_def, mode_apply, show -(-k - 1) - 1 = k from by ring] at hk'
  · intro h a ha b hb n hn
    rw [smul₁_def, mode_apply]
    exact h a ha b hb (-n - 1) (by omega)

/-- The **pole vector**: the coefficient of `x^{-2}` in `Y₁(a,x)b`, as a vector of `𝒱`. For
weight-one `a, b` and a graded deformation it lies in `𝒱₀ = ℂ𝟙` (`poleVec_mem_grading_zero`), and
the whole of Theorem 3.1 is the statement that it vanishes. -/
def poleVec (D : FirstOrderDeformation W) (a b : 𝒱) : 𝒱 := D.smul₁ a 1 b

/-- `poleVec` is literally the `x^{-2}` coefficient (`mode _ 1 = _ (-2)`). -/
theorem poleVec_eq_coeff (D : FirstOrderDeformation W) (a b : 𝒱) :
    D.poleVec a b = D.Y1 a (-2) b := by
  rw [poleVec, smul₁_def, mode_apply, show -(1 : ℤ) - 1 = -2 from by norm_num]

/-- A regular deformation has vanishing pole vector on the weight-one space. -/
theorem poleVec_eq_zero_of_regular (D : FirstOrderDeformation W) (h : D.Regular) {a b : 𝒱}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) : D.poleVec a b = 0 :=
  h a ha b hb 1 (by norm_num)

/-- For a graded deformation the pole vector of two weight-one vectors sits in `𝒱₀`:
`1 + 1 - 1 - 1 = 0`. -/
theorem poleVec_mem_grading_zero (D : FirstOrderDeformation W) (hD : D.IsGraded) {a b : 𝒱}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) : D.poleVec a b ∈ W.grading 0 := by
  have h := hD 1 1 a ha b hb 1
  rwa [show (1 : ℤ) + 1 - 1 - 1 = 0 from by ring] at h

/-- `c` **is the pole coefficient** of `(a,b)`: the relational form, which needs no choice
principle and is the one to use in hypotheses. -/
def HasPoleCoeff (D : FirstOrderDeformation W) (a b : 𝒱) (c : ℂ) : Prop :=
  c • W.vacuum = D.poleVec a b

/-- For a graded deformation and weight-one `a, b` a pole coefficient exists, because
`𝒱₀ = ℂ𝟙` (VOA4). -/
theorem exists_hasPoleCoeff (D : FirstOrderDeformation W) (hD : D.IsGraded) {a b : 𝒱}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) : ∃ c : ℂ, D.HasPoleCoeff a b c := by
  have h := D.poleVec_mem_grading_zero hD ha hb
  rw [W.vacuum_grade] at h
  exact Submodule.mem_span_singleton.mp h

/-- The **pole coefficient** as a function: the scalar `c` with `c·𝟙` equal to the `x^{-2}`
coefficient of `Y₁(a,x)b`. It is `Classical.epsilon`-chosen, hence junk when no such `c` exists
(e.g. for an ungraded deformation); `poleCoeff_spec` is the only way to use it, and
`exists_hasPoleCoeff` supplies its hypothesis in the graded weight-one case. -/
noncomputable def poleCoeff (D : FirstOrderDeformation W) (a b : 𝒱) : ℂ :=
  Classical.epsilon fun c : ℂ => D.HasPoleCoeff a b c

/-- Defining property of `poleCoeff`, given that a pole coefficient exists at all. -/
theorem poleCoeff_spec (D : FirstOrderDeformation W) {a b : 𝒱}
    (h : ∃ c : ℂ, D.HasPoleCoeff a b c) : D.poleCoeff a b • W.vacuum = D.poleVec a b :=
  Classical.epsilon_spec h

end FirstOrderDeformation

/-! ### Scalars are pinned down by `𝟙` (needed to read `poleCoeff` off `poleVec`) -/

/-- In a nontrivial VOA, `c·𝟙 = 0` forces `c = 0`. Proved by hand (multiply by `c⁻¹`) rather than
through a `NoZeroSMulDivisors` instance. -/
theorem eq_zero_of_smul_vacuum_eq_zero {W : VertexOperatorAlgebra 𝒱} (hvac : W.vacuum ≠ 0)
    {c : ℂ} (h : c • W.vacuum = 0) : c = 0 := by
  by_contra hc
  refine hvac ?_
  calc W.vacuum = (1 : ℂ) • W.vacuum := (one_smul ℂ W.vacuum).symm
    _ = (c⁻¹ * c) • W.vacuum := by rw [inv_mul_cancel₀ hc]
    _ = c⁻¹ • (c • W.vacuum) := mul_smul _ _ _
    _ = c⁻¹ • (0 : 𝒱) := by rw [h]
    _ = 0 := smul_zero _

/-- In a nontrivial VOA the map `c ↦ c·𝟙` is injective, so a pole coefficient is unique. -/
theorem eq_of_smul_vacuum_eq {W : VertexOperatorAlgebra 𝒱} (hvac : W.vacuum ≠ 0) {c d : ℂ}
    (h : c • W.vacuum = d • W.vacuum) : c = d := by
  have h0 : (c - d) • W.vacuum = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_smul_vacuum_eq_zero hvac h0)

namespace FirstOrderDeformation

variable {W : VertexOperatorAlgebra 𝒱}

/-- Uniqueness: in a nontrivial VOA, `poleCoeff` really is *the* pole coefficient. -/
theorem poleCoeff_eq (D : FirstOrderDeformation W) (hvac : W.vacuum ≠ 0) {a b : 𝒱} {c : ℂ}
    (hc : D.HasPoleCoeff a b c) : D.poleCoeff a b = c :=
  eq_of_smul_vacuum_eq hvac ((D.poleCoeff_spec ⟨c, hc⟩).trans hc.symm)

/-- The reduction the target paper performs: **regular ⟹ the pole coefficient vanishes.** -/
theorem poleCoeff_eq_zero_of_regular (D : FirstOrderDeformation W) (hvac : W.vacuum ≠ 0)
    (h : D.Regular) {a b : 𝒱} (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1) :
    D.poleCoeff a b = 0 := by
  refine D.poleCoeff_eq hvac ?_
  change (0 : ℂ) • W.vacuum = D.poleVec a b
  rw [zero_smul, D.poleVec_eq_zero_of_regular h ha hb]

end FirstOrderDeformation

end Deform

end VOA
