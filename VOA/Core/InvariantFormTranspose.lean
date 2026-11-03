/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormFHL

/-!
# The transpose obstruction for FHL full invariance

An axiom-free structural result used in the conditional delimitation of the
Frenkel–Huang–Lepowsky full-invariance theorem. The `InvariantForm` structure carries the
Virasoro-adjointness `virasoro_adj` (`(Lₙa|b) = (a|L₋ₙb)`). This file proves:

* **`InvariantForm.transpose`** — the transpose `Bᵀ(a,b) := B(b,a)` is *again* an `InvariantForm`
  (its `virasoro_adj` follows from `B`'s at `-n`). So is **`InvariantForm.antisymmetrize`** `B − Bᵀ`.
* **`InvariantForm.form_smul_skew_transpose`** — the skew-route adjoint identity `form_smul_skew`
  holds verbatim for `Bᵀ`; the entire `skew` + `virasoro_adj` toolkit is *blind to slot order*.
* **`InvariantForm.no_structural_symmetry_of_antisymmetrize_ne`** — hence a single invariant form
  with nonzero antisymmetric part refutes any structural derivation `∀ B, B.IsSymmetric`.

The last theorem is conditional on a supplied `B` with nonzero antisymmetric part.  This file does
not construct such a form, so it does not by itself prove unconditional failure of the universal
full-invariance statement.  `Core.InvariantFormDelimitation` combines this perspective with the
proved `𝒱₁`-symmetry consequence of full invariance under `hqp`, again conditional on an explicit
nonsymmetric witness.  The genuine canonical-form FHL theorem is completed separately.

## Status
Axiom-clean. The transpose constructions are unconditional; the non-universality conclusion is
an explicit implication from a form with nonzero antisymmetric part, not a constructed
counterexample.

## References
* Gannon §5.1.3, eq. (5.1.11a); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA.VertexOperatorAlgebra

open scoped BigOperators
open Classical

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **The transpose invariant form** `Bᵀ.form a b = B.form b a` — again an `InvariantForm`
(`virasoro_adj` is slot-symmetric: `(Lₙa|b)_{Bᵀ} = (b|Lₙa)_B = (L₋ₙb|a)_B = (a|L₋ₙb)_{Bᵀ}`). -/
def InvariantForm.transpose (B : InvariantForm W) : InvariantForm W where
  form := B.form.flip
  virasoro_adj := by
    intro n a b
    show B.form b (W.L n a) = B.form (W.L (-n) b) a
    rw [B.virasoro_adj (-n) b a, show (-(-n) : ℤ) = n by ring]

@[simp] theorem InvariantForm.transpose_form (B : InvariantForm W) (a b : 𝒱) :
    (InvariantForm.transpose B).form a b = B.form b a := rfl

/-- The transpose is an involution. -/
theorem InvariantForm.transpose_transpose (B : InvariantForm W) :
    (InvariantForm.transpose (InvariantForm.transpose B)).form = B.form := by
  ext a b; rfl

/-- The **antisymmetrization** `B − Bᵀ`, again an invariant form (difference of invariant forms). -/
def InvariantForm.antisymmetrize (B : InvariantForm W) : InvariantForm W :=
  InvariantForm.sub B (InvariantForm.transpose B)

@[simp] theorem InvariantForm.antisymmetrize_form (B : InvariantForm W) (a b : 𝒱) :
    (InvariantForm.antisymmetrize B).form a b = B.form a b - B.form b a := by
  show (B.form - (InvariantForm.transpose B).form) a b = _
  rw [LinearMap.sub_apply, LinearMap.sub_apply, InvariantForm.transpose_form]

/-- **Symmetry ⇔ vanishing antisymmetric part.** -/
theorem InvariantForm.isSymmetric_iff_antisymmetrize_zero (B : InvariantForm W) :
    B.IsSymmetric ↔ (InvariantForm.antisymmetrize B).form = 0 := by
  constructor
  · intro hsym
    ext a b
    rw [InvariantForm.antisymmetrize_form, hsym a b, sub_self]; rfl
  · intro hzero a b
    have := DFunLike.congr_fun (DFunLike.congr_fun hzero a) b
    rw [InvariantForm.antisymmetrize_form, LinearMap.zero_apply, LinearMap.zero_apply,
      sub_eq_zero] at this
    exact this

/-- **The skew-route identity is transpose-invariant.** `form_smul_skew` holds for `Bᵀ`:
`B.form b (u₍ₙ₎a) = ∑ⱼ (1/j!) sgn(−n−1−j) B.form (L₁ʲb) (a₍n+j₎u)`. So the whole `skew`+`virasoro_adj`
toolkit cannot pin `B.form a b` vs `B.form b a`. -/
theorem InvariantForm.form_smul_skew_transpose (B : InvariantForm W) (u a b : 𝒱) (n : ℤ) :
    B.form b (W.smul u n a)
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
          B.form ((W.L 1 ^ j) b) (W.smul a (n + j) u) := by
  have h := form_smul_skew (InvariantForm.transpose B) u a b n
  simpa only [InvariantForm.transpose_form] using h

/-- With symmetry, the FHL target only relabels slots — no new adjoint relation (it feeds the same
already-circular covariance recursion). -/
theorem InvariantForm.diagonal_symmetric_relabel (B : InvariantForm W) (hsym : B.IsSymmetric)
    (u a b : 𝒱) (n : ℤ) :
    B.form (W.smul u n a) b = B.form b (W.smul u n a) := hsym _ _

/-- **The seal.** A single invariant form with nonzero antisymmetric part refutes any structural
symmetry derivation `∀ B, B.IsSymmetric`; equivalently, `virasoro_adj` does not force symmetry, so
it cannot force `IsFullyInvariant` (which does). -/
theorem InvariantForm.no_structural_symmetry_of_antisymmetrize_ne
    (B : InvariantForm W) (hne : (InvariantForm.antisymmetrize B).form ≠ 0) :
    ¬ (∀ B' : InvariantForm W, B'.IsSymmetric) := by
  intro hderiv
  have hsym : (InvariantForm.antisymmetrize B).IsSymmetric := hderiv _
  apply hne
  ext a b
  have h1 : (InvariantForm.antisymmetrize B).form a b
      = (InvariantForm.antisymmetrize B).form b a := hsym a b
  rw [InvariantForm.antisymmetrize_form, InvariantForm.antisymmetrize_form] at h1
  have hab : B.form a b - B.form b a = 0 := by linear_combination h1 / 2
  show (InvariantForm.antisymmetrize B).form a b = (0 : LinearMap.BilinForm ℂ 𝒱) a b
  rw [InvariantForm.antisymmetrize_form, LinearMap.zero_apply, LinearMap.zero_apply, hab]

end VOA.VertexOperatorAlgebra
