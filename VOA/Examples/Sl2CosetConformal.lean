/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetSubspace

/-!
# The explicit conformal-vector membership input

An abstract super vertex algebra and affine action do not specify an ambient
conformal vector or a diagonal Sugawara vector. Their difference is a coset
state exactly when their nonnegative current products agree. This file records
that membership as data, as distinct from the proved closure of the coset.

OPEN: construct the actual Sugawara vectors in the desired simple tensor
factors and prove the required equality of their singular current products.
The data below do not assert Virasoro relations or a conformal VOA structure.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- Membership of the proposed Sugawara difference is explicit data. -/
structure CosetConformalData (A : AffineSl2Action V k)
    (ambientConformal diagonalSugawara : M) : Prop where
  mem_coset : ambientConformal - diagonalSugawara ∈ cosetSubspace A

/-- The precise current-product obligation for a conformal difference. -/
theorem conformalDifference_mem_iff (A : AffineSl2Action V k)
    (ambientConformal diagonalSugawara : M) :
    ambientConformal - diagonalSugawara ∈ cosetSubspace A ↔
      ∀ a n, 0 ≤ n → mode (V.Y (A.current a)) n ambientConformal =
        mode (V.Y (A.current a)) n diagonalSugawara := by
  simp only [mem_cosetSubspace, map_sub, sub_eq_zero]

/-- Matching singular current products supplies the membership datum. -/
def CosetConformalData.of_current_modes (A : AffineSl2Action V k)
    (ambientConformal diagonalSugawara : M)
    (h : ∀ a n, 0 ≤ n → mode (V.Y (A.current a)) n ambientConformal =
      mode (V.Y (A.current a)) n diagonalSugawara) :
    CosetConformalData A ambientConformal diagonalSugawara :=
  ⟨(conformalDifference_mem_iff A ambientConformal diagonalSugawara).mpr h⟩

/-- The proposed conformal difference, as a state of the actual commutant. -/
def cosetConformalState (A : AffineSl2Action V k)
    (ambientConformal diagonalSugawara : M)
    (h : CosetConformalData A ambientConformal diagonalSugawara) : cosetSubspace A :=
  ⟨ambientConformal - diagonalSugawara, h.mem_coset⟩

end VOA.Sl2Coset
