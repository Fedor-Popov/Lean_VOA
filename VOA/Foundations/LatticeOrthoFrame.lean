/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.LatticeFinite
import Mathlib.Analysis.Matrix.Order

/-!
# The orthonormal frame of an even positive-definite lattice  (`orthCoord`)

For the general lattice VOA the boson oscillators must realise the Heisenberg algebra
`𝔥 = L ⊗ ℝ` with the lattice form: `[α(m), β(n)] = ⟨α,β⟩ · m · δ_{m+n,0}`.  The ambient rank-`r`
Fock oscillators `HeisenbergN.oscN` are **orthonormal** (`[aᵃₘ, aᵇₙ] = m δ^{ab} δ_{m+n,0}`), so the
integer charge `α = ∑ᵢ αᵢ Bᵢ` must be re-expressed in a real **orthonormal frame** of `(𝔥, ⟨,⟩)`.

That frame is a real Gram square root `C` with `Cᵀ C = G` (`G = gramR L`), which exists because
`L.PosDef` makes `G` positive-definite (`gramR_posDef`, bridging the already-proven `Qr_pos`).  We
take `C = √G = CFC.sqrt (gramR L)` (the Hermitian PSD square root; `frame_transpose_mul_self`
gives `Cᵀ C = G`).  The real orthonormal coordinates `orthCoord α = C ·(coord α)` then satisfy

  `∑ₐ orthCoordα ₐ · orthCoordβ ₐ = ⟨α,β⟩`   (`orthCoord_inner`)

— the metric-carrying identity that will drive every locality sign of the charge-`α` vertex
operators (Goal 3), via `latticeCocycle_comm` for the odd-pairing signs.

## References
* FLM Ch. 8; Gannon §5.2.2.
-/

set_option linter.style.longLine false

namespace VOA.IntegralLattice

open scoped BigOperators Matrix MatrixOrder
open Module

variable (L : IntegralLattice)

/-! ## `gramR L` as a `Matrix.PosDef` (bridging `Qr_pos`) -/

/-- Over `ℝ`, the conjugate-transpose is the transpose (trivial star). -/
theorem real_conjTranspose_eq_transpose {ι : Type*} (M : Matrix ι ι ℝ) : Mᴴ = Mᵀ := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]

/-- `gramR L` is Hermitian (from the symmetry `gramR_symm`). -/
theorem gramR_isHermitian : (gramR L).IsHermitian := by
  change (gramR L)ᴴ = gramR L
  rw [real_conjTranspose_eq_transpose]
  exact gramR_symm L

/-- **`gramR L` is a positive-definite matrix** — the `Matrix.PosDef` packaging of `Qr_pos`. -/
theorem gramR_posDef (hPos : L.PosDef) : (gramR L).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramR_isHermitian L) (fun x hx => ?_)
  have hstar : star x = x := by funext i; exact star_trivial _
  rw [hstar]
  exact Qr_pos L hPos hx

/-! ## The Gram square root (the real orthonormal frame) -/

/-- The **orthonormal frame** `C = √G` — the Hermitian positive-semidefinite square root of the
Gram matrix `G = gramR L`.  (Total in `L`; the sqrt property needs `L.PosDef`.) -/
noncomputable def frame : Matrix (Fin (latRank L)) (Fin (latRank L)) ℝ := CFC.sqrt (gramR L)

theorem frame_posSemidef : (frame L).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (gramR L))

/-- `C` is symmetric (`Cᵀ = C`) — a real Hermitian matrix. -/
theorem frame_transpose : (frame L)ᵀ = frame L := by
  rw [← real_conjTranspose_eq_transpose]
  exact (frame_posSemidef L).isHermitian

/-- `C · C = G` — the defining square-root property. -/
theorem frame_mul_self (hPos : L.PosDef) : frame L * frame L = gramR L := by
  have hnn : (0 : Matrix (Fin (latRank L)) (Fin (latRank L)) ℝ) ≤ gramR L :=
    Matrix.nonneg_iff_posSemidef.mpr (gramR_posDef L hPos).posSemidef
  exact CFC.sqrt_mul_sqrt_self (gramR L) hnn

/-- **`Cᵀ C = G`** — the Gram factorization through the frame. -/
theorem frame_transpose_mul_self (hPos : L.PosDef) : (frame L)ᵀ * frame L = gramR L := by
  rw [frame_transpose L]
  exact frame_mul_self L hPos

/-! ## Real orthonormal coordinates and the metric identity -/

/-- The real-cast integer coordinates `coordR α = (coord α : ℝ)`. -/
noncomputable def coordR (α : L.carrier) : Fin (latRank L) → ℝ := fun i => ((coord L α i : ℤ) : ℝ)

/-- The bilinear Gram identity over `ℤ`: `⟨α,β⟩ = coord α ⬝ᵥ G *ᵥ coord β`. -/
theorem form_eq_gram_bilin (α β : L.carrier) :
    L.form α β = coord L α ⬝ᵥ (gram L *ᵥ coord L β) := by
  rw [form_eq_sum_repr L (latticeBasis L) α β]
  simp only [dotProduct, Matrix.mulVec, gram, coord, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The bilinear Gram identity over `ℝ`: `coordR α ⬝ᵥ Gℝ *ᵥ coordR β = ⟨α,β⟩`. -/
theorem coordR_gram_bilin (α β : L.carrier) :
    coordR L α ⬝ᵥ (gramR L *ᵥ coordR L β) = ((L.form α β : ℤ) : ℝ) := by
  rw [form_eq_gram_bilin L α β]
  simp only [coordR, gramR, dotProduct, Matrix.mulVec, Matrix.map_apply, Int.cast_sum,
    Int.cast_mul, Finset.mul_sum]

/-- The **real orthonormal coordinates** `orthCoord α = C ·(coord α)` (`C` the frame). -/
noncomputable def orthCoord (α : L.carrier) : Fin (latRank L) → ℝ := frame L *ᵥ coordR L α

/-- **The frame realises the lattice form** — `∑ₐ orthCoordα ₐ · orthCoordβ ₐ = ⟨α,β⟩`.  This is
the whole point of the frame: the euclidean inner product of the orthonormal coordinates is the
lattice pairing, so `α(m) = ∑ₐ orthCoordα ₐ · aₐ(m)` will satisfy `[α(m),β(n)] = ⟨α,β⟩ m δ`. -/
theorem orthCoord_inner (hPos : L.PosDef) (α β : L.carrier) :
    ∑ a, orthCoord L α a * orthCoord L β a = ((L.form α β : ℤ) : ℝ) := by
  have hdot : (∑ a, orthCoord L α a * orthCoord L β a) = orthCoord L α ⬝ᵥ orthCoord L β := rfl
  rw [hdot, orthCoord, orthCoord, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, frame_transpose_mul_self L hPos, dotProduct_comm,
    coordR_gram_bilin L β α, form_symm L β α]

end VOA.IntegralLattice
