/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryAuxiliarySectors
import VOA.Commutative.GordonPairTelescope

/-! # Transport between the conformal sector decomposition and the Gordon source -/

namespace VOA.GordonSectorTransport
open VOA.GordonRestrictedDual VOA.GordonFunctionalRelabel VOA.GordonPairIndexing
open VOA.BoundaryAuxiliarySectors
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Actual quotient-sector dimensions are independent of color-preserving particle labels. -/
theorem sector_finrank_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (m D : ℕ) (color : ι → Fin 3) (other : κ → Fin 3)
    (e : ι ≃ κ) (he : ∀ i, other (e i) = color i) :
    Module.finrank K (sector (K := K) m D color) =
      Module.finrank K (sector (K := K) m D other) := by
  rw [← finrank_functionalModel, ← finrank_functionalModel]
  exact (functionalModelEquiv (K := K) m D color other e he).finrank_eq

/-- The canonical conformal-sector labels and the fixed Gordon source have identical dimensions. -/
theorem piece_finrank_eq_original (m a b c D : ℕ) :
    Module.finrank K (piece (K := K) m a b c D) =
      Module.finrank K (sector (K := K) m D (originalColor a b c)) := by
  exact sector_finrank_relabel m D (color a b c) (originalColor a b c)
    (Equiv.sumAssoc (Fin a) (Fin b) (Fin c)) (by rintro ((i | i) | i) <;> rfl)

/-- The actual global conformal piece is bounded by the same fixed particle sectors
used in the complete Gordon pair and partition argument. -/
theorem auxiliaryPiece_finrank_le_sum_original_sectors (m N : ℕ) :
    Module.finrank K (VOA.BoundaryAuxiliary.auxiliaryPiece (K := K) m N) ≤
      ∑ t : Index N, Module.finrank K
        (sector (K := K) m (N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val))
          (originalColor t.val.1.val t.val.2.1.val t.val.2.2.val)) := by
  have h := auxiliaryPiece_finrank_le_sum_sectors (K := K) m N
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro t _
  exact piece_finrank_eq_original m _ _ _ _

end
end VOA.GordonSectorTransport
