/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroGram4
import VOA.Core.InvariantFormTranspose

/-!
# The canonical form on `V(c,0)` is **symmetric** — and is pinned by `Normalized` alone

This file supplies the prerequisite without which none of `Core.GradedUnitarity`'s reduction can
even be *stated* at Virasoro: reflexivity of the level-`n` Gram form.  Mathlib's orthogonality
API (`LinearMap.BilinForm.orthogonal`, `isCompl_orthogonal_of_restrict_nondegenerate`) is gated on
`IsRefl`, and a *general* `InvariantForm` is not reflexive — `Core.InvariantFormTranspose`
proves outright that `∀ B, B.IsSymmetric` is **false**
(`InvariantForm.no_structural_symmetry_of_antisymmetrize_ne`).

## The route, and why it is cheap

Not via FHL.  The abstract argument (`IsFullyInvariant` of the transpose, then
`invariantForm_unique`) is *unavailable*: `IsFullyInvariant` is not slot-symmetric, and proving it
for `Bᵀ` is essentially the FHL symmetry theorem.  `Core.InvariantFormSymmetry` says as much in its
own "honest gap" section, and only gets weight `1`.

Instead, a Virasoro-specific **determinacy** statement, which needs neither full invariance nor
simplicity:

> `invariantForm_ext` — on `V(c,0)`, an `InvariantForm` is determined by `Normalized` alone.

The proof is three lines of structure and no analysis.  Adjointness `B(L₋ᵢ₋₂ a, b) = B(a, L₊ᵢ₊₂ b)`
peels creation modes off the *left* slot, shortening the word; the base case `B(𝟙, ·)` is `0` on
every nonempty creation word (the mode moves right onto `L₊|0⟩ = 0`) and `1` on the empty one
(`Normalized`); and creation words span (`VirModule.negSpanVir_eq_top`, `pbw`-free).

Symmetry is then immediate, because `InvariantForm.transpose` is again an `InvariantForm` and has
the same vacuum normalisation.

## Contents

* `adjLop` — adjointness for an arbitrary `InvariantForm` on `V(c,0)`, in `Lop` form.
* `vac_negWord_cons` — `B(𝟙, L₋ᵢ₋₂ v) = 0`, the base case.
* `invariantForm_ext` — **determinacy**: two normalised invariant forms on `V(c,0)` agree.
* `canB_isSymmetric` — the canonical form is symmetric.
* `canB_isRefl`, `gradedForm_canB_isRefl` — the reflexivity that `Core.GradedUnitarity`
  consumes.

## Status
`sorry`-free, no new axioms.  This is a **theorem**, not a statement or a reduction: it is
proved outright here.  It says nothing about graded unitarity.
-/

namespace VOA

namespace VirFormSym

open VOA.VirModule VOA.VirGram4 VOA.VertexOperatorAlgebra

variable {c : ℂ}

/-! ## §1  Adjointness and the vacuum row -/

/-- **Virasoro adjointness in `Lop` form**, for an *arbitrary* invariant form on `V(c,0)`:
`B(Lₙ a, b) = B(a, L₋ₙ b)`.  A structure field, transported along `virasoroVOA_L_eq_Lop`. -/
theorem adjLop (B : InvariantForm (virasoroVOA c)) (n : ℤ) (a b : VirUniv c) :
    B.form (Lop c n a) b = B.form a (Lop c (-n) b) := by
  rw [← virasoroVOA_L_eq_Lop, ← virasoroVOA_L_eq_Lop]
  exact B.virasoro_adj n a b

/-- **The vacuum row vanishes on every nonempty creation word.**  Move the creation mode across:
`B(𝟙, L₋ᵢ₋₂ v) = B(L₊ᵢ₊₂ 𝟙, v) = B(0, v) = 0`, using `Lop_vacuum` (`Lₙ|0⟩ = 0` for `n ≥ -1`).

Note that this uses *only* the `virasoro_adj` field — no normalisation, no invariance. -/
theorem vac_negWord_cons (B : InvariantForm (virasoroVOA c)) (i : ℕ) (rest : List ℕ) :
    B.form (vacVec c) (negWordVir c (i :: rest)) = 0 := by
  have h := adjLop B ((i : ℤ) + 2) (vacVec c) (negWordVir c rest)
  rw [Lop_vacuum c (by omega)] at h
  rw [show (-((i : ℤ) + 2)) = -(i : ℤ) - 2 by ring] at h
  rw [negWordVir_cons, ← h]
  simp

/-- **The vacuum row is determined by the normalisation.**  On the empty word it is `+1`
(`Normalized`), on every other creation word it is `0` (`vac_negWord_cons`), and creation words
span (`negSpanVir_eq_top`). -/
theorem vac_row_ext {B₁ B₂ : InvariantForm (virasoroVOA c)}
    (h₁ : B₁.Normalized) (h₂ : B₂.Normalized) (y : VirUniv c) :
    B₁.form (vacVec c) y = B₂.form (vacVec c) y := by
  have htop : Submodule.span ℂ (Set.range (negWordVir c)) = ⊤ := negSpanVir_eq_top c
  have hy : y ∈ Submodule.span ℂ (Set.range (negWordVir c)) := htop ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      cases w with
      | nil => exact h₁.trans h₂.symm
      | cons i rest => rw [vac_negWord_cons B₁ i rest, vac_negWord_cons B₂ i rest]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul r a _ ha => rw [map_smul, map_smul, ha]

/-! ## §2  Determinacy: `Normalized` pins an invariant form on `V(c,0)` -/

/-- The one peeling step: a creation mode moves off the left slot, shortening the word. -/
theorem negWord_cons_left (B : InvariantForm (virasoroVOA c)) (i : ℕ) (rest : List ℕ)
    (y : VirUniv c) :
    B.form (negWordVir c (i :: rest)) y
      = B.form (negWordVir c rest) (Lop c ((i : ℤ) + 2) y) := by
  rw [negWordVir_cons]
  have h := adjLop B (-(i : ℤ) - 2) (negWordVir c rest) y
  rw [show (-(-(i : ℤ) - 2)) = (i : ℤ) + 2 by ring] at h
  exact h

/-- Determinacy along a creation word: the left slot is peeled by induction on the word, the base
case being `vac_row_ext`. -/
theorem negWord_row_ext {B₁ B₂ : InvariantForm (virasoroVOA c)}
    (h₁ : B₁.Normalized) (h₂ : B₂.Normalized) :
    ∀ (w : List ℕ) (y : VirUniv c),
      B₁.form (negWordVir c w) y = B₂.form (negWordVir c w) y := by
  intro w
  induction w with
  | nil => intro y; exact vac_row_ext h₁ h₂ y
  | cons i rest ih =>
      intro y
      rw [negWord_cons_left B₁ i rest y, negWord_cons_left B₂ i rest y, ih]

/-- **DETERMINACY.**  On `V(c,0)` an invariant bilinear form is completely determined by its
vacuum normalisation: any two normalised `InvariantForm`s are *equal*.

This is strictly stronger than what `Core.InvariantFormFHL2.invariantForm_unique_FHL` gives,
because it does **not** assume `IsFullyInvariant` on either side.  The reason it can be stronger
is that `V(c,0)` is generated from the vacuum by the Virasoro modes alone, which is exactly the
content that `virasoro_adj` controls. -/
theorem invariantForm_ext {B₁ B₂ : InvariantForm (virasoroVOA c)}
    (h₁ : B₁.Normalized) (h₂ : B₂.Normalized) : B₁.form = B₂.form := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have htop : Submodule.span ℂ (Set.range (negWordVir c)) = ⊤ := negSpanVir_eq_top c
  have hx : x ∈ Submodule.span ℂ (Set.range (negWordVir c)) := htop ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact negWord_row_ext h₁ h₂ w y
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, LinearMap.add_apply]; rw [ha, hb]
  | smul r a _ ha => simp only [map_smul, LinearMap.smul_apply]; rw [ha]

/-! ## §3  Symmetry, and the reflexivity the reduction consumes -/

/-- The transpose of a normalised form is normalised (the vacuum entry is on the diagonal). -/
theorem transpose_normalized {B : InvariantForm (virasoroVOA c)} (h : B.Normalized) :
    (InvariantForm.transpose B).Normalized := h

/-- **The canonical form on `V(c,0)` is symmetric.**

`Bᵀ` is again an `InvariantForm` (`InvariantForm.transpose`) with the same vacuum normalisation,
so `invariantForm_ext` forces `B = Bᵀ`.

⚠ This is *not* the general FHL symmetry theorem, which remains unproved in this repository
(`Core.InvariantFormTranspose.not_forall_isSymmetric` shows the unqualified statement is false for
a general `InvariantForm`).  It is symmetry of the **canonical** form on the **Virasoro** vacuum
module, obtained from determinacy. -/
theorem canB_isSymmetric (c : ℂ) : (canB c).IsSymmetric := by
  have h : (canB c).form = (InvariantForm.transpose (canB c)).form :=
    invariantForm_ext (canB_normalized c) (transpose_normalized (canB_normalized c))
  intro a b
  calc (canB c).form a b = (InvariantForm.transpose (canB c)).form a b := by rw [h]
    _ = (canB c).form b a := InvariantForm.transpose_form _ a b

/-- **Reflexivity of the canonical form** — the hypothesis that unlocks Mathlib's
`LinearMap.BilinForm.orthogonal` API. -/
theorem canB_isRefl (c : ℂ) : ((canB c).form).IsRefl :=
  fun a b h => (canB_isSymmetric c b a).trans h

/-- **Reflexivity of the level-`n` Gram form** of the canonical form on `V(c,0)`.  This is the
`href` argument of `Core.GradedUnitarity.layerDecomposition`. -/
theorem gradedForm_canB_isRefl (c : ℂ) (n : ℤ) :
    ((LiRadical.gradedForm (canB c) n)).IsRefl :=
  fun a b h => (canB_isSymmetric c (b : VirUniv c) (a : VirUniv c)).trans h

end VirFormSym

end VOA
