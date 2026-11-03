/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.LocalSystemJacobi

/-!
# The regular fields of a local field system

This file develops the next layer of Li's local-system construction.  The first prerequisite is
the all-integer form of Dong closure for `Fld.prod`: a product of two fields is local with a
third field whenever the three inputs are pairwise local.  The nonnegative branch is
`dong_nonneg`; the negative branch combines `dong_neg`, derivative locality, and scalar
locality.

The intended endpoints are mutual locality of the regular fields `LocalFieldSystem.stateFld`
and compatibility of their field products with `LocalFieldSystem.modeAction`.  They must be
derived from the original locality data; neither property is included as an assumption.
-/

namespace VOA

open Module (End)

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

namespace Fld

/-- **Dong closure for the total integer field product.**  Pairwise locality of `a`, `b`, and
`c` implies locality of `a₍n₎b` with `c` for every integer `n`. -/
theorem prod_local_right_of_pairwise {a b c : Fld M}
    (hab : Local a.1 b.1) (hac : Local a.1 c.1) (hbc : Local b.1 c.1) (n : ℤ) :
    Local (prod n a b).1 c.1 := by
  rcases lt_or_ge n 0 with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) - 1 :=
      ⟨(-n - 1).toNat, by omega⟩
    rw [prod_of_neg (by omega), show (-(-(k : ℤ) - 1) - 1).toNat = k by omega]
    rw [negProd]
    exact VertexOperatorAlgebra.Local.smul' ((k.factorial : ℂ)⁻¹)
      (dong_neg (a.2.deriv_iterate k) b.2
        (hab.deriv_iterate_left k) (hac.deriv_iterate_left k) hbc)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) :=
      ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    rw [prod_of_nonneg (Int.natCast_nonneg k), Int.toNat_natCast]
    exact dong_nonneg hab hac hbc k

end Fld

namespace LocalFieldSystem

/-- Products inside a local field system remain local with every member. -/
theorem prod_local (L : LocalFieldSystem M) (n : ℤ) (a b c : L.carrier) :
    Local (Fld.prod n a.1 b.1).1 c.1.1 :=
  Fld.prod_local_right_of_pairwise
    (L.locality a.1 a.2 b.1 b.2)
    (L.locality a.1 a.2 c.1 c.2)
    (L.locality b.1 b.2 c.1 c.2) n

end LocalFieldSystem

end VOA
