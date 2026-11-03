/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.BilinearForm

/-!
# Graded flags and good filtrations (clause (iv) of the graded-unitarity datum)

⚠ **This file is a DEFINITION, not a theorem.**  Nothing here proves that any VOA carries a good
filtration, and nothing here proves graded unitarity of anything.

The object is the `R`-filtration of Arabi Ardehali–Beem–Lemos–Rastelli,
*Graded Unitarity in the SCFT/VOA Correspondence*, arXiv:2507.23781v2 = JHEP 06 (2026) 075,
clause (iv) of Definition 2.2: a half-integral increasing filtration of each conformal weight
space, on which the sesquilinear form of clause (iii) is required to be nondegenerate.  At the
boundary Virasoro minimal models the filtration in question is ABLR eq. (3.11),

  `G_p V = span{ L₋₂₋ₙ₁ ⋯ L₋₂₋ₙ_k Ω : k ≤ p }`,

which is literally Kaufmann's `Ṽ_{n,k}` (hep-th/9405041, §4.2): the filtration degree is the
**length** of the partition.

## The split, and why it is the honest one

Two *different* things get called "the filtration":

* `GradedFlag` — the order-theoretic data alone: an increasing, exhaustive family of subspaces of
  each `𝒱ₙ`, starting at `ℂ𝟙` in weight `0` and at `0` in positive weight.  Everything the
  reduction of `Core.GradedUnitarity` consumes lives here, and every field of it is checkable.
* `GradedFlag.ModeCompatible` — the extra requirement that makes the flag a *vertex-algebra*
  object rather than an arbitrary flag: `u ∈ G_p 𝒱ₘ`, `v ∈ G_q 𝒱ₙ` ⟹ `u₍ₖ₎v ∈ G_{p+q} 𝒱_{m+n-k-1}`.

⚠ **`ModeCompatible` is a reconstruction, not a transcription.**  The ABLR text was not
available when this file was written, so the axioms that the paper attaches to the word "good"
could not be read off the source.  The condition
above is what makes the associated graded a Poisson-type object and is what the length filtration
on creation words visibly satisfies, but *whether it is ABLR's condition verbatim has not been
checked*.  It is therefore carried as a **separate predicate** and as the single field of
`GoodFiltration`, so that:

* a `GradedFlag` can be constructed unconditionally (as it is for Virasoro in
  `Examples.VirasoroGoodFiltration`) even while `ModeCompatible` is unproved for it, and
* every downstream statement makes visible whether it depends on the reconstructed clause.  None
  of them does: `Core.GradedUnitarity` uses only `mono`, `le_grading`, `bot` and `exhaustive`.

## Status
Definitions and their immediate order-theoretic consequences, `sorry`-free, no new axioms.
The universal affine `sl2` filtration and all of its induced graded VOA quotient
filtrations are constructed as `GoodFiltration`s in `Examples.AffineSl2GoodFiltration`.
**Not proved here:** mode compatibility of the boundary Virasoro length flag; the
graded-unitarity development uses only its underlying `GradedFlag`.

## References
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2, Definition 2.2(iv) and eq. (3.11).
* R. M. Kaufmann, hep-th/9405041, §4.2.
-/

namespace VOA

open VOA.VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **graded flag** on a VOA: an increasing, exhaustive ℕ-filtration of every conformal weight
space, normalised so that degree `0` is `ℂ𝟙` in weight `0` and `0` in positive weight.

This is the order-theoretic half of clause (iv) of ABLR Definition 2.2.  The vertex-algebraic half
is `GradedFlag.ModeCompatible`, kept separate on purpose — see the file docstring. -/
structure GradedFlag (W : VertexOperatorAlgebra 𝒱) where
  /-- `piece p n = G_p 𝒱ₙ`. -/
  piece : ℕ → ℤ → Submodule ℂ 𝒱
  /-- Each piece sits inside its weight space. -/
  le_grading : ∀ (p : ℕ) (n : ℤ), piece p n ≤ W.grading n
  /-- The filtration is increasing in the filtration degree. -/
  mono : ∀ {p q : ℕ} (n : ℤ), p ≤ q → piece p n ≤ piece q n
  /-- Degree `0` is trivial in positive weight (the vacuum is the only length-`0` state). -/
  bot : ∀ n : ℤ, 0 < n → piece 0 n = ⊥
  /-- Degree `0` in weight `0` is the vacuum line. -/
  vacuum_zero : piece 0 0 = ℂ ∙ W.vacuum
  /-- The filtration exhausts each weight space. -/
  exhaustive : ∀ n : ℤ, (⨆ p : ℕ, piece p n) = W.grading n

namespace GradedFlag

variable {W : VertexOperatorAlgebra 𝒱} (F : GradedFlag W)

theorem monotone (n : ℤ) : Monotone fun p : ℕ => F.piece p n := fun _ _ h => F.mono n h

theorem directed (n : ℤ) : Directed (· ≤ ·) fun p : ℕ => F.piece p n :=
  (F.monotone n).directed_le

/-- ⚠ **RECONSTRUCTED, NOT TRANSCRIBED.**  The vertex-algebraic compatibility that would make a
graded flag "good" in the sense of ABLR Definition 2.2(iv): the mode products add filtration
degrees, `u₍ₖ₎v ∈ G_{p+q}`.

The source paper is not in this repository (see the file docstring), so this condition is the
present author's reconstruction of the word "good" and **must not be cited as ABLR's axiom** until
the paper has been read against it.  Nothing in `Core.GradedUnitarity` depends on it. -/
def ModeCompatible : Prop :=
  ∀ {p q : ℕ} {m n k : ℤ} {u v : 𝒱}, u ∈ F.piece p m → v ∈ F.piece q n →
    W.smul u k v ∈ F.piece (p + q) (m + n - k - 1)

/-- The piece, transported into the weight space `𝒱ₙ` as a subspace *of that finite-dimensional
space*.  This is the form the orthogonality API of `Mathlib.LinearAlgebra.BilinearForm.Orthogonal`
needs: it requires the ambient space to be finite-dimensional, which `𝒱` is not and `𝒱ₙ` is. -/
def pieceIn (p : ℕ) (n : ℤ) : Submodule ℂ (W.grading n) :=
  (F.piece p n).comap (W.grading n).subtype

@[simp] theorem mem_pieceIn {p : ℕ} {n : ℤ} (x : W.grading n) :
    x ∈ F.pieceIn p n ↔ (x : 𝒱) ∈ F.piece p n := Iff.rfl

theorem pieceIn_mono {p q : ℕ} (n : ℤ) (h : p ≤ q) : F.pieceIn p n ≤ F.pieceIn q n :=
  fun _ hx => F.mono n h hx

/-- The **strictly smaller** piece: `G_{p-1}`, with `G_{-1} = 0`.  Written by recursion rather
than by ℕ-subtraction, which would wrongly return `G₀` at `p = 0`. -/
def pieceLT : ℕ → ∀ n : ℤ, Submodule ℂ (W.grading n)
  | 0, _ => ⊥
  | (q + 1), n => F.pieceIn q n

@[simp] theorem pieceLT_zero (n : ℤ) : F.pieceLT 0 n = ⊥ := rfl

@[simp] theorem pieceLT_succ (q : ℕ) (n : ℤ) : F.pieceLT (q + 1) n = F.pieceIn q n := rfl

theorem pieceLT_le_pieceIn (p : ℕ) (n : ℤ) : F.pieceLT p n ≤ F.pieceIn p n := by
  cases p with
  | zero => exact bot_le
  | succ q => exact F.pieceIn_mono n (Nat.le_succ q)

/-- The flag exhausts each weight space, in the `pieceIn` formulation. -/
theorem iSup_pieceIn (n : ℤ) : (⨆ p : ℕ, F.pieceIn p n) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : (x : 𝒱) ∈ ⨆ p : ℕ, F.piece p n := by rw [F.exhaustive n]; exact x.2
  obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ (F.directed n)).mp hx
  exact Submodule.mem_iSup_of_mem p hp

end GradedFlag

/-- A **good filtration** in the sense of ABLR Definition 2.2(iv): a graded flag whose mode
products add filtration degrees.

⚠ The field `mode_mem` is a **reconstruction** of the word "good"; see
`GradedFlag.ModeCompatible` and the file docstring.  Concrete constructions live downstream; in
particular, `Examples.AffineSl2GoodFiltration` proves mode compatibility for the corrected affine
flag and for its induced graded quotients. -/
structure GoodFiltration (W : VertexOperatorAlgebra 𝒱) extends GradedFlag W where
  /-- ⚠ Reconstructed, not transcribed: `u₍ₖ₎v ∈ G_{p+q}`. -/
  mode_mem : toGradedFlag.ModeCompatible

end VOA
