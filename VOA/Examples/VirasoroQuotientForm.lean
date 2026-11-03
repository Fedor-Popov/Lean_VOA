/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroFormSymmetry
import VOA.Examples.VirasoroSelfDual

/-!
# One matrix for two algebras: the form on `L(c,0)` is `canGram` of `V(c,0)`

`L(c,0) = V(c,0)/J` carries its own canonical normalised invariant form `Bsimp`
(`Core.InvariantFormFHL2.canonicalInvariantForm`, whose two hypotheses are free here:
`VirSimple.virasoroSimple_vacuum_ne_zero` and `VirSimple.virasoroSimple_qp`).  This file proves
that it is the *same numbers* as the form on the universal module:

  `canB_quot_mkQ` :  `Bsimp c ([x], [y]) = canB c (x, y)`.

That is the reason the reduction of `Core.GradedUnitarity` is computable at all.  The Gram matrix
of the simple quotient's form, in the images of the partition monomials, **is**
`GramMat.canGram` of `V(c,0)` in `VirModule.gradedBasis` — a matrix the repository already knows
how to write down (`Examples.VirasoroGram4`, `Examples.VirasoroGram56`).  No separate
computation on the quotient is ever needed.

## Why the proof is short

Not by pulling back full invariance.  `VirFormSym.invariantForm_ext` says an invariant form on
`V(c,0)` is pinned by `Normalized` **alone**, so it is enough to check that the pullback
`Bpull := Bsimp ∘ (mkQ × mkQ)` is an `InvariantForm` and is normalised.  Both are immediate:
`mkQ` intertwines the Virasoro modes (`mkQ_L`, from `VirSimple.virasoroSimple_mkQ_smul` and
`ω ↦ [ω]`), and `mkQ 𝟙 = 𝟙`.

## Contents

* `Bsimp` — the canonical normalised invariant form on `L(c,0)`.
* `mkQ_L` — the quotient map intertwines `Lₙ`.
* `Bpull` — the pullback of `Bsimp` to `V(c,0)`, as an `InvariantForm`.
* `canB_quot_mkQ` — **the bridge**.
* `gram_simple_negWord` — the bridge on creation monomials: the entries of the quotient Gram
  matrix are the entries of `canGram`.
* `Bsimp_isSymmetric`, `Bsimp_isRefl`, `gradedForm_Bsimp_isRefl` — symmetry transported to the
  quotient; the last is the `href` hypothesis of `Core.GradedUnitarity.layerDecomposition`.
* `Bsimp_leftRadical` — nondegeneracy of `Bsimp` (from simplicity of `L(c,0)`).

## Status
`sorry`-free, no new axioms.  Everything here is a **theorem**, proved outright.  Nothing here
concerns graded unitarity, positivity, or signatures.
-/

namespace VOA

namespace VirQuotForm

open VOA.VirModule VOA.VirSimple VOA.VirGram4
open VOA.VertexOperatorAlgebra

variable (c : ℂ)

/-! ## §1  The canonical form on the simple quotient -/

/-- The **canonical normalised invariant form on `L(c,0)`**.  Both hypotheses of
`canonicalInvariantForm` are discharged unconditionally: the vacuum survives the quotient, and
`L(c,0)₁ = 0` makes `L₁𝒱₁ = 0` vacuous. -/
noncomputable def Bsimp : InvariantForm (virasoroSimple c) :=
  canonicalInvariantForm (virasoroSimple_vacuum_ne_zero c) (virasoroSimple_qp c)

/-- The vacuum pairs with itself to give +1. This fixes the scale of the
canonical form and lets scalar vacuum identities detect central-charge motion. -/
theorem Bsimp_normalized : (Bsimp c).Normalized :=
  canonicalInvariantForm_normalized _ _

/-- The canonical form intertwines all vertex operators through the
contragredient transformation, not only the Virasoro modes stored in its basic
structure. This is the full state-field invariance needed for radical arguments. -/
theorem Bsimp_isFullyInvariant : (Bsimp c).IsFullyInvariant :=
  canonicalInvariantForm_isFullyInvariant _ _

/-- **Nondegeneracy of `Bsimp`.**  `L(c,0)` is simple (`virasoroSimple_isSimple`), so Gannon
5.1.11b applies: the left radical of the canonical form is `⊥`. -/
theorem Bsimp_leftRadical : InvariantForm.leftRadical (Bsimp c) = ⊥ :=
  invariantForm_nondegenerate_FHL _ _ (virasoroSimple_isSimple c)

/-! ## §2  The quotient map intertwines the Virasoro modes -/

/-- `[Lₙ x] = Lₙ [x]`.  Both sides unfold to a mode of `Y(ω, z)`, and `[ω]` is the conformal
vector of the quotient (`virasoroSimple_conformalVector`), so this is
`virasoroSimple_mkQ_smul` at `u = ω`. -/
theorem mkQ_L (n : ℤ) (x : VirUniv c) :
    (maxIdealVir c).mkQ ((virasoroVOA c).L n x)
      = (virasoroSimple c).L n ((maxIdealVir c).mkQ x) := by
  have h1 : (virasoroSimple c).L n ((maxIdealVir c).mkQ x)
      = (virasoroSimple c).smul (virasoroSimple c).conformalVector (n + 1)
          ((maxIdealVir c).mkQ x) := rfl
  have h2 : (virasoroVOA c).L n x
      = (virasoroVOA c).smul (virasoroVOA c).conformalVector (n + 1) x := rfl
  rw [h1, h2, virasoroSimple_conformalVector]
  exact (virasoroSimple_mkQ_smul c (omegaVir c) x (n + 1)).symm

/-! ## §3  The bridge -/

/-- The **pullback** of `Bsimp` along the quotient map, as an `InvariantForm` on `V(c,0)`.
Adjointness pulls back because `mkQ` intertwines `Lₙ` (`mkQ_L`). -/
noncomputable def Bpull : InvariantForm (virasoroVOA c) where
  form := (Bsimp c).form.compl₁₂ (maxIdealVir c).mkQ (maxIdealVir c).mkQ
  virasoro_adj := by
    intro n a b
    show (Bsimp c).form ((maxIdealVir c).mkQ ((virasoroVOA c).L n a)) ((maxIdealVir c).mkQ b)
        = (Bsimp c).form ((maxIdealVir c).mkQ a)
            ((maxIdealVir c).mkQ ((virasoroVOA c).L (-n) b))
    rw [mkQ_L, mkQ_L]
    exact (Bsimp c).virasoro_adj n _ _

/-- To pair universal states with the pulled-back form, first project both
states to the simple quotient. In particular, a state killed by the quotient
pairs to zero with every other universal state. -/
theorem Bpull_apply (x y : VirUniv c) :
    (Bpull c).form x y = (Bsimp c).form ((maxIdealVir c).mkQ x) ((maxIdealVir c).mkQ y) := rfl

/-- The pullback is normalised, because `mkQ 𝟙 = 𝟙`. -/
theorem Bpull_normalized : (Bpull c).Normalized := Bsimp_normalized c

/-- **THE BRIDGE.**  The canonical form of the *simple quotient*, evaluated on classes, is the
canonical form of the *universal* module evaluated on representatives.

Consequence, and the whole point: the Gram matrix of `L(c,0)ₙ` in the images of the partition
monomials **is** `GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) n (gradedBasis c n)`.
One matrix serves both algebras, so every determinant already computed for `V(c,0)`
(`Examples.VirasoroGram4`, `Examples.VirasoroGram56`) is directly a statement about `L(c,0)`.

The proof is `VirFormSym.invariantForm_ext`: on `V(c,0)` an invariant form is pinned by its
vacuum normalisation, and both forms here are normalised. -/
theorem canB_quot_mkQ (x y : VirUniv c) :
    (Bsimp c).form ((maxIdealVir c).mkQ x) ((maxIdealVir c).mkQ y) = (canB c).form x y := by
  have h : (Bpull c).form = (canB c).form :=
    VirFormSym.invariantForm_ext (Bpull_normalized c) (canB_normalized c)
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- The bridge on creation monomials: every entry of the quotient's Gram matrix in the partition
basis is the corresponding entry of `canGram`. -/
theorem gram_simple_negWord (w w' : List ℕ) :
    (Bsimp c).form ((maxIdealVir c).mkQ (negWordVir c w))
        ((maxIdealVir c).mkQ (negWordVir c w'))
      = (canB c).form (negWordVir c w) (negWordVir c w') :=
  canB_quot_mkQ c _ _

/-! ## §4  Symmetry and reflexivity on the quotient -/

/-- **The canonical form on `L(c,0)` is symmetric**, transported through the bridge from
`VirFormSym.canB_isSymmetric` by surjectivity of `mkQ`. -/
theorem Bsimp_isSymmetric : (Bsimp c).IsSymmetric := by
  intro a b
  obtain ⟨x, rfl⟩ := virasoroSimple_mkQ_surjective (c := c) a
  obtain ⟨y, rfl⟩ := virasoroSimple_mkQ_surjective (c := c) b
  rw [canB_quot_mkQ, canB_quot_mkQ, VirFormSym.canB_isSymmetric]

/-- Orthogonality is symmetric: if a pairs to zero with b, then b pairs
to zero with a. This is the bilinear-form meaning of reflexivity here; it does
not assert positivity or a Hermitian inner product. -/
theorem Bsimp_isRefl : ((Bsimp c).form).IsRefl :=
  fun a b h => (Bsimp_isSymmetric c b a).trans h

/-- **Reflexivity of the level-`n` Gram form on `L(c,0)`** — precisely the `href` hypothesis of
`Core.GradedUnitarity.layerDecomposition` and `finrank_pieceLT_add_layer`. -/
theorem gradedForm_Bsimp_isRefl (n : ℤ) :
    ((LiRadical.gradedForm (Bsimp c) n)).IsRefl :=
  fun a b h => (Bsimp_isSymmetric c (b : VirUniv c ⧸ maxIdealVir c)
    (a : VirUniv c ⧸ maxIdealVir c)).trans h

end VirQuotForm

end VOA
