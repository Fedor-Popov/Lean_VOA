/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BlockwiseSymmetricInvariantInduction

/-!
# The Fundamental Theorem for an arbitrary finite list of blocks

This file iterates the one-block extension theorem over a list of block sizes.  Variables are
presented recursively as a disjoint union, so the induction is definitional and independent of
the later reindexing by a numerical profile `rho : Fin n → ℕ`.
-/

namespace VOA.IteratedBlockSymmetricInvariant

open VOA.BlockwiseSymmetricInvariantInduction
open VOA.TwoBlockSymmetricInvariant

noncomputable section

universe u

variable {K : Type u} [CommRing K]

/-- Root variables grouped recursively by a list of block sizes. -/
def BlockSlots : List ℕ → Type
  | [] => Fin 0
  | a :: rest => Fin a ⊕ BlockSlots rest

noncomputable instance blockSlotsFintype : (blocks : List ℕ) → Fintype (BlockSlots blocks)
  | [] => by
      change Fintype (Fin 0)
      infer_instance
  | _ :: rest => by
      letI := blockSlotsFintype rest
      change Fintype (Fin _ ⊕ BlockSlots rest)
      infer_instance

/-- Independent relabelings inside every recursively presented block. -/
def BlockRelabeling : List ℕ → Type
  | [] => PUnit
  | a :: rest => Equiv.Perm (Fin a) × BlockRelabeling rest

/-- The identity relabeling of every block. -/
def identityRelabeling : (blocks : List ℕ) → BlockRelabeling blocks
  | [] => PUnit.unit
  | _ :: rest => (Equiv.refl _, identityRelabeling rest)

/-- The permutation of all recursively presented slots induced by a block relabeling. -/
def blockAction : (blocks : List ℕ) → BlockRelabeling blocks → Equiv.Perm (BlockSlots blocks)
  | [], _ => Equiv.refl _
  | _ :: rest, h => blockPermutation h.1 (blockAction rest h.2)

@[simp] theorem blockAction_identity (blocks : List ℕ) :
    blockAction blocks (identityRelabeling blocks) = Equiv.refl (BlockSlots blocks) := by
  induction blocks with
  | nil => rfl
  | cons a rest ih =>
      ext i
      rcases i with i | i
      · rfl
      · change Sum.inr (blockAction rest (identityRelabeling rest) i) = Sum.inr i
        rw [ih]
        rfl

/-- Polynomials fixed by every independent block relabeling. -/
def blockFixedSubalgebra (blocks : List ℕ) :
    Subalgebra K (MvPolynomial (BlockSlots blocks) K) where
  carrier := {p | ∀ h : BlockRelabeling blocks,
    MvPolynomial.rename (blockAction blocks h) p = p}
  algebraMap_mem' r h := MvPolynomial.rename_C _ _
  add_mem' {p q} hp hq h := by rw [map_add, hp h, hq h]
  mul_mem' {p q} hp hq h := by rw [map_mul, hp h, hq h]

/-- For a nonempty recursive list, the old fixed subalgebra is definitionally the right fixed
subalgebra used by the one-block extension theorem. -/
def tailFixedAlgEquiv (rest : List ℕ) :
    blockFixedSubalgebra (K := K) rest ≃ₐ[K]
      rightFixedSubalgebra (K := K) (blockAction rest) :=
  AlgEquiv.refl

/-- Repackage an extended fixed polynomial as a fixed polynomial for a nonempty recursive list. -/
def extendedToConsFixed (a : ℕ) (rest : List ℕ) :
    extendedFixedSubalgebra (K := K) (sigma := Fin a) (blockAction rest) →ₐ[K]
      blockFixedSubalgebra (K := K) (a :: rest) where
  toFun p := ⟨p.1, fun h ↦ p.2 h.1 h.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Repackage a fixed polynomial for a nonempty recursive list in extended form. -/
def consFixedToExtended (a : ℕ) (rest : List ℕ) :
    blockFixedSubalgebra (K := K) (a :: rest) →ₐ[K]
      extendedFixedSubalgebra (K := K) (sigma := Fin a) (blockAction rest) where
  toFun p := ⟨p.1, fun e h ↦ p.2 (e, h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The nonempty-list fixed subalgebra is the extended fixed subalgebra used by the one-block
extension theorem. -/
def consFixedAlgEquiv (a : ℕ) (rest : List ℕ) :
    extendedFixedSubalgebra (K := K) (sigma := Fin a) (blockAction rest) ≃ₐ[K]
      blockFixedSubalgebra (K := K) (a :: rest) :=
  AlgEquiv.ofAlgHom (extendedToConsFixed (K := K) a rest)
    (consFixedToExtended (K := K) a rest)
    (AlgHom.ext fun _ ↦ Subtype.ext rfl)
    (AlgHom.ext fun _ ↦ Subtype.ext rfl)

/-- In zero blocks every polynomial is fixed. -/
def emptyToFixed : MvPolynomial (BlockSlots []) K →ₐ[K]
    blockFixedSubalgebra (K := K) [] :=
  (AlgHom.id K (MvPolynomial (BlockSlots []) K)).codRestrict
    (blockFixedSubalgebra (K := K) []) fun p ↦ by
      intro h
      exact MvPolynomial.rename_id_apply p

/-- The zero-block fixed presentation is an equivalence. -/
def emptyFixedAlgEquiv : MvPolynomial (BlockSlots []) K ≃ₐ[K]
    blockFixedSubalgebra (K := K) [] := by
  apply AlgEquiv.ofBijective (emptyToFixed (K := K))
  constructor
  · intro p q hpq
    exact congrArg Subtype.val hpq
  · intro p
    exact ⟨p.1, Subtype.ext rfl⟩

/-- Arbitrary finite-list Fundamental Theorem of blockwise symmetric polynomials. -/
def blockEsymmAlgEquiv : (blocks : List ℕ) →
    MvPolynomial (BlockSlots blocks) K ≃ₐ[K]
      blockFixedSubalgebra (K := K) blocks
  | [] => emptyFixedAlgEquiv (K := K)
  | a :: rest =>
      (MvPolynomial.sumAlgEquiv K (Fin a) (BlockSlots rest)).trans
        ((extendFixedPresentation (K := K) (sigma := Fin a)
          (act := blockAction rest) (identityRelabeling rest)
          (blockAction_identity rest) a (Fintype.card_fin a)
          ((blockEsymmAlgEquiv rest).trans (tailFixedAlgEquiv (K := K) rest))).trans
            (consFixedAlgEquiv (K := K) a rest))

/-- The arbitrary-list block elementary map is bijective onto the simultaneous fixed
subalgebra. -/
theorem blockEsymmAlgEquiv_bijective (blocks : List ℕ) :
    Function.Bijective (blockEsymmAlgEquiv (K := K) blocks) :=
  (blockEsymmAlgEquiv (K := K) blocks).bijective

end

end VOA.IteratedBlockSymmetricInvariant

