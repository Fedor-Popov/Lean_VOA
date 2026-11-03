/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalSeries
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The formal delta, residues, and modes  (Gannon §5.1.2, pp. 314–317)

The formal calculus that makes the vertex-algebra axioms computable.

* **Formal delta** (5.1.2): `δ(z) := ∑_{n ∈ ℤ} zⁿ`. In multiplicative notation it is
  the Dirac delta centred at `z = 1`. The two-variable delta is
  `δ(z₁/z₂) = ∑_{k} z₁ᵏ z₂⁻ᵏ`.
* **Residue** (5.1.3a): `Res_z (∑ bₙ zⁿ) := b₋₁`. Integration by parts (5.1.3b):
  `Res_z (g · ∂_z f) = - Res_z (f · ∂_z g)`.
* **Modes** (5.1.3c): writing `f(z) = ∑ aₙ zⁿ =: ∑ a₍ₘ₎ z^{-m-1}`, the mode is
  `a₍ₘ₎ = Res_z (zᵐ f(z)) = a₋ₘ₋₁`. (This is the indexing used for vertex operators.)
* **Binomial convention** (5.1.4): `(z₁ + z₂)ⁿ := ∑_{k ∈ ℕ} C(n,k) z₁^{n-k} z₂^k`,
  *always expanded in nonnegative powers of the second variable* — a genuine
  convention, not an identity (Paradox 5.2, eq. 5.1.5).

## Dependencies
* `VOA.Foundations.FormalSeries`.

## Status
Complete & `sorry`-free. `formalDelta`, `res`, and `mode` are essentially
one-liners; integration by parts (5.1.3b) is derived from `res_deriv` and the Leibniz
rule `deriv_lpSMul` for the (well-defined) Laurent-polynomial action `lpSMul`.

## References
* Gannon §5.1.2; Lepowsky–Li Ch. 2; FLM §8.1.
-/

namespace VOA

universe u

variable {𝒲 : Type u}

/-! ## The formal delta -/

/-- The formal delta `δ(z) = ∑_{n ∈ ℤ} zⁿ` — all coefficients equal `1` (Gannon 5.1.2). -/
def formalDelta : FormalDist ℂ := fun _ => 1

@[simp] theorem formalDelta_apply (n : ℤ) : formalDelta n = 1 := rfl

/-- The two-variable delta `δ(z₁/z₂) = ∑_{k ∈ ℤ} z₁ᵏ z₂⁻ᵏ`: the coefficient of
`z₁ᵐ z₂ⁿ` is `1` exactly when `m + n = 0` (Gannon 5.1.2). -/
def delta₂ : FormalDist₂ ℂ := fun m n => if m + n = 0 then 1 else 0

@[simp] theorem delta₂_apply (m n : ℤ) : delta₂ m n = if m + n = 0 then 1 else 0 := rfl

/-! ## Residue, derivative and modes -/

/-- The `m`-th mode `a₍ₘ₎ = a₋ₘ₋₁` of a distribution (Gannon 5.1.3c). This is the
coefficient indexing used for vertex operators: `Y(u,z) = ∑ u₍ₙ₎ z^{-n-1}`. -/
def mode (f : FormalDist 𝒲) (m : ℤ) : 𝒲 := f (-m - 1)

@[simp] theorem mode_apply (f : FormalDist 𝒲) (m : ℤ) : mode f m = f (-m - 1) := rfl

/-! ## Reindexing helpers for doubly-infinite sums -/

/-- The successor shift `k ↦ k + 1` as an equivalence `ℤ ≃ ℤ`. -/
def intSucc : ℤ ≃ ℤ where
  toFun k := k + 1
  invFun k := k - 1
  left_inv k := by dsimp only; omega
  right_inv k := by dsimp only; omega

/-- Reindexing a doubly-infinite (`finsum`) sum over `ℤ` by `k ↦ k + 1` leaves it
unchanged: the algebraic analogue of shifting the summation index. -/
theorem finsum_int_succ_shift {M : Type*} [AddCommMonoid M] (F : ℤ → M) :
    ∑ᶠ k : ℤ, F (k + 1) = ∑ᶠ k : ℤ, F k :=
  finsum_comp_equiv intSucc

/-- Scaling a family pointwise by integers can only shrink its support. -/
theorem support_zsmul_left_subset {M : Type*} [AddCommGroup M] (a : ℤ → ℤ) (w : ℤ → M) :
    Function.support (fun k => a k • w k) ⊆ Function.support w := by
  intro k hk
  rw [Function.mem_support] at hk ⊢
  intro h
  exact hk (by rw [h, smul_zero])

section ComplexModule

variable [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- The formal residue `Res_z (∑ bₙ zⁿ) = b₋₁`, a `ℂ`-linear functional (Gannon 5.1.3a). -/
def res : FormalDist 𝒲 →ₗ[ℂ] 𝒲 where
  toFun f := f (-1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem res_apply (f : FormalDist 𝒲) : res f = f (-1) := rfl

/-- The term-wise formal derivative `∂_z`: since `∂_z zⁿ = n z^{n-1}`, the coefficient of
`zⁿ` in `∂_z f` is `(n+1)·(coefficient of z^{n+1})`. A `ℂ`-linear endomorphism. -/
def deriv : FormalDist 𝒲 →ₗ[ℂ] FormalDist 𝒲 where
  toFun f := fun n => (n + 1 : ℤ) • f (n + 1)
  map_add' f g := by funext n; exact smul_add (n + 1 : ℤ) (f (n + 1)) (g (n + 1))
  map_smul' c f := by funext n; exact smul_comm (n + 1 : ℤ) c (f (n + 1))

@[simp] theorem deriv_apply (f : FormalDist 𝒲) (n : ℤ) :
    deriv f n = (n + 1 : ℤ) • f (n + 1) := rfl

/-- The mode is the residue of the shifted distribution: `a₍ₘ₎ = Res_z (zᵐ f(z))`
(Gannon 5.1.3c). -/
theorem mode_eq_res (f : FormalDist 𝒲) (m : ℤ) : mode f m = res (mulByMonomial m f) := by
  change f (-m - 1) = f (-1 - m)
  congr 1
  ring

/-- The coefficient of `z⁻¹` in a derivative vanishes: `Res_z (∂_z f) = 0`
(part of Gannon 5.1.3). -/
@[simp] theorem res_deriv (f : FormalDist 𝒲) : res (deriv f) = 0 := by
  change deriv f (-1) = 0
  rw [deriv_apply, show (-1 : ℤ) + 1 = 0 from by ring, zero_smul]

/-! ## The Laurent-polynomial action and integration by parts (Gannon 5.1.3b) -/

/-- The action of a Laurent polynomial `g(z) = ∑ gₖ zᵏ` on a formal distribution
`f(z)`: the algebraically-defined product `(g · f)(z)`, with coefficient
`(g · f)ₙ = ∑ₖ gₖ · f_{n-k}`. For `g` a genuine Laurent polynomial (finite support)
every coefficient is a finite sum, so this product is well-defined (Gannon p. 315). -/
noncomputable def lpSMul (g : FormalDist ℂ) (f : FormalDist 𝒲) : FormalDist 𝒲 :=
  fun n => ∑ᶠ k, g k • f (n - k)

@[simp] theorem lpSMul_apply (g : FormalDist ℂ) (f : FormalDist 𝒲) (n : ℤ) :
    lpSMul g f n = ∑ᶠ k, g k • f (n - k) := rfl

/-- For a Laurent polynomial `g`, every convolution summand `k ↦ gₖ · F k` has finite
support, so the products defining `lpSMul g f` are algebraically defined (Gannon p. 315). -/
theorem support_smul_left_finite (g : FormalDist ℂ) (hg : (Function.support g).Finite)
    (F : ℤ → 𝒲) : (Function.support (fun k => g k • F k)).Finite := by
  refine hg.subset ?_
  intro k hk
  rw [Function.mem_support] at hk ⊢
  intro h
  exact hk (by rw [h, zero_smul])

/-- **Leibniz rule** for the formal derivative on the Laurent-polynomial action:
`∂_z (g · f) = (∂_z g) · f + g · (∂_z f)` — the product rule for formal distributions,
valid for `g` a Laurent polynomial (Gannon §5.1.2). -/
theorem deriv_lpSMul (g : FormalDist ℂ) (hg : (Function.support g).Finite) (f : FormalDist 𝒲) :
    deriv (lpSMul g f) = lpSMul (deriv g) f + lpSMul g (deriv f) := by
  funext n
  change deriv (lpSMul g f) n = lpSMul (deriv g) f n + lpSMul g (deriv f) n
  have hfin1 : (Function.support (fun k : ℤ => g k • f (n + 1 - k))).Finite :=
    support_smul_left_finite g hg _
  have hfinc : (Function.support (fun k : ℤ => g k • f (n - k + 1))).Finite :=
    support_smul_left_finite g hg _
  have hL : deriv (lpSMul g f) n = ∑ᶠ k : ℤ, (n + 1 : ℤ) • (g k • f (n - k + 1)) := by
    rw [deriv_apply, lpSMul_apply, smul_finsum' (n + 1 : ℤ) hfin1]
    refine finsum_congr fun k => ?_
    rw [show n + 1 - k = n - k + 1 from by ring]
  have hT2 : lpSMul g (deriv f) n = ∑ᶠ k : ℤ, (n - k + 1 : ℤ) • (g k • f (n - k + 1)) := by
    rw [lpSMul_apply]
    refine finsum_congr fun k => ?_
    rw [deriv_apply, smul_comm]
  have hT1 : lpSMul (deriv g) f n = ∑ᶠ k : ℤ, (k : ℤ) • (g k • f (n - k + 1)) := by
    rw [lpSMul_apply]
    simp only [deriv_apply]
    rw [show (∑ᶠ k : ℤ, ((k + 1 : ℤ) • g (k + 1)) • f (n - k))
          = ∑ᶠ k : ℤ, (k + 1 : ℤ) • (g (k + 1) • f (n - (k + 1) + 1)) from
        finsum_congr fun k => by rw [smul_assoc, show n - k = n - (k + 1) + 1 from by ring]]
    exact finsum_int_succ_shift fun k : ℤ => (k : ℤ) • (g k • f (n - k + 1))
  rw [hL, hT1, hT2]
  have e1 : (Function.support (fun k : ℤ => (k : ℤ) • (g k • f (n - k + 1)))).Finite :=
    hfinc.subset (support_zsmul_left_subset _ _)
  have e2 : (Function.support (fun k : ℤ => (n - k + 1 : ℤ) • (g k • f (n - k + 1)))).Finite :=
    hfinc.subset (support_zsmul_left_subset _ _)
  rw [← finsum_add_distrib e1 e2]
  refine finsum_congr fun k => ?_
  rw [← add_smul, show (k : ℤ) + (n - k + 1) = n + 1 from by ring]

/-- **Integration by parts** (Gannon 5.1.3b): for `g` a Laurent polynomial,
`Res_z (g · ∂_z f) = - Res_z ((∂_z g) · f)`. Derived from `res_deriv` (the residue of a
derivative vanishes) together with the Leibniz rule `deriv_lpSMul`. -/
theorem res_lpSMul_deriv (g : FormalDist ℂ) (hg : (Function.support g).Finite)
    (f : FormalDist 𝒲) : res (lpSMul g (deriv f)) = - res (lpSMul (deriv g) f) := by
  have h := res_deriv (lpSMul g f)
  rw [deriv_lpSMul g hg f, map_add] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h

end ComplexModule

/-! ## The generalized binomial convention (Gannon 5.1.4) -/

/-- The generalized binomial coefficient `C(n,k) = n(n-1)⋯(n-k+1)/k!` for `n ∈ ℤ`,
`k ∈ ℕ` (Gannon 5.1.4a). -/
noncomputable def gBinom (n : ℤ) (k : ℕ) : ℂ :=
  (∏ i ∈ Finset.range k, ((n : ℂ) - (i : ℂ))) / (k.factorial : ℂ)

@[simp] theorem gBinom_zero (n : ℤ) : gBinom n 0 = 1 := by
  simp [gBinom]

/-- The binomial expansion `(z₁ + z₂)ⁿ`, *expanded in nonnegative powers of `z₂`*
(Gannon 5.1.4a): the coefficient of `z₁ᵃ z₂ᵇ` is `C(n,b)` when `b ≥ 0` and `a = n - b`,
and `0` otherwise. This is a genuine convention (Paradox 5.2), asymmetric in `z₁, z₂`. -/
noncomputable def binomialExpand (n : ℤ) : FormalDist₂ ℂ :=
  fun a b => if 0 ≤ b ∧ a = n - b then gBinom n b.toNat else 0

/-! ## Smoke tests -/

/-- `Res_z δ(z) = 1`: the residue of the formal delta is `1`. -/
example : res formalDelta = 1 := rfl

/-- The mode is the `(-m-1)`-coefficient (Gannon 5.1.3c). -/
example (f : FormalDist ℂ) (m : ℤ) : mode f m = f (-m - 1) := rfl

/-- The residue of a derivative vanishes. -/
example (f : FormalDist ℂ) : res (deriv f) = 0 := res_deriv f

/-- `(z₁ - z₂) · δ(z₁/z₂) = 0`: a sanity check of the two-variable algebra. -/
example : mulBySubPow 1 (delta₂ : FormalDist₂ ℂ) = 0 := by
  rw [mulBySubPow_one]
  ext m n
  change delta₂ (m - 1) n - delta₂ m (n - 1) = 0
  simp only [delta₂]
  rw [show m - 1 + n = m + (n - 1) from by ring]
  exact sub_self _

/-- `Res_z (g · ∂f) = - Res_z ((∂g) · f)` instantiated, confirming the by-parts API. -/
example (g f : FormalDist ℂ) (hg : (Function.support g).Finite) :
    res (lpSMul g (deriv f)) = - res (lpSMul (deriv g) f) := res_lpSMul_deriv g hg f

end VOA
