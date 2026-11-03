/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.AffineSl2
import VOA.Examples.Sl2SemiInfiniteGhosts

/-!
# The adjoint coefficients of the three-pair `sl₂` ghost current

The colours are the repository's Chevalley basis `e,f,h`.  In dual ghost coordinates the
intended current is `Jᵃ_gh = ∑_{b,c} f^{ab}_c :b_c c_b:`.  Thus `b` transforms in the adjoint
representation and `c` in its dual.  The finite contraction `tr(ad a · ad b)` is `4 κ(a,b)`,
with a positive sign, for the normalised form `κ(e,f)=1`, `κ(h,h)=2`.

The contraction identity below is an exact calculation of the numerical coefficient.  By
itself it does not assert an operator-product expansion for the ghost fields.
-/

namespace VOA.Sl2SemiInfinite

open scoped BigOperators
open AffineVOA

/-- The coefficient of `b_c c_b` in the ghost current for colour `a`. -/
def ghostCurrentCoefficient (a b c : Fin 3) : ℂ := fabc a b c

/-- The adjoint representation is traceless in the chosen Chevalley basis. -/
theorem ghostCurrentCoefficient_trace (a : Fin 3) :
    (∑ b : Fin 3, ghostCurrentCoefficient a b b) = 0 := by
  fin_cases a <;> norm_num [ghostCurrentCoefficient, fabc, Fin.sum_univ_three]

set_option maxHeartbeats 800000 in
-- Expanding all four Chevalley indices gives eighty-one finite coefficient identities.
/-- The single-contraction coefficient is the adjoint Lie bracket.  This fixes the ordering
of the two indices in `:b_c c_b:` before any mode calculation is undertaken. -/
theorem ghostCurrentCoefficient_commutator (a b c d : Fin 3) :
    (∑ i : Fin 3,
      (ghostCurrentCoefficient a i c * ghostCurrentCoefficient b d i
        - ghostCurrentCoefficient b i c * ghostCurrentCoefficient a d i)) =
      ∑ e : Fin 3, fabc a b e * ghostCurrentCoefficient e d c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [ghostCurrentCoefficient, fabc, Fin.sum_univ_three]

/-- The double-contraction coefficient of the adjoint ghost currents.  The normalised
Killing form of `sl₂` has adjoint index `2h∨ = 4`; the sign here is positive. -/
theorem ghostCurrentCoefficient_doubleContraction (a b : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ghostCurrentCoefficient a i j * ghostCurrentCoefficient b j i) =
      4 * kappa a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [ghostCurrentCoefficient, fabc, kappa, Fin.sum_univ_three]

/-- The total numerical central coefficient cancels exactly at matter level `-4`.  This is
level arithmetic, not yet the current OPE or BRST nilpotency theorem. -/
theorem matter_add_ghost_doubleContraction (k : ℂ) (a b : Fin 3) :
    k * kappa a b +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ghostCurrentCoefficient a i j * ghostCurrentCoefficient b j i) =
      (k + 4) * kappa a b := by
  rw [ghostCurrentCoefficient_doubleContraction]
  ring

/-- At level `-4`, the matter and ghost double-contraction coefficients sum to zero. -/
theorem minus_four_add_ghost_doubleContraction (a b : Fin 3) :
    (-4 : ℂ) * kappa a b +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ghostCurrentCoefficient a i j * ghostCurrentCoefficient b j i) = 0 := by
  rw [matter_add_ghost_doubleContraction]
  norm_num

/-- The quadratic ghost state `:b_c c_b:`, defined by the genuine `(-1)`-product
in the three-pair ghost vertex superalgebra. -/
noncomputable def ghostBilinear (c b : Fin 3) : Sl2GhostSpace :=
  mode (sl2GhostSVA.Y (bGhost c)) (-1) (cGhost b)

/-- Every quadratic `bc` current state has weight one. -/
theorem ghostBilinear_weight (c b : Fin 3) :
    ghostBilinear c b ∈ sl2GhostSVA.grading 1 := by
  have h := sl2GhostSVA.grading_mode (bGhost c) (bGhost_weight c)
    (cGhost b) (cGhost_weight b) (-1)
  norm_num at h
  exact h

/-- A quadratic `bc` current is even. -/
theorem ghostBilinear_even (c b : Fin 3) :
    ghostBilinear c b ∈ sl2GhostSVA.parity 0 := by
  have h := sl2GhostSVA.parity_mode (bGhost c) (bGhost_odd c)
    (cGhost b) (cGhost_odd b) (-1)
  norm_num at h
  exact h

/-- The adjoint `sl₂` ghost-current state.  The first ghost index is the output
of the adjoint matrix, so that antighosts transform in the adjoint representation. -/
noncomputable def ghostCurrent (a : Fin 3) : Sl2GhostSpace :=
  ∑ b : Fin 3, ∑ c : Fin 3, ghostCurrentCoefficient a b c • ghostBilinear c b

/-- The corresponding field, using the actual three-pair state-field correspondence. -/
noncomputable def ghostCurrentField (a : Fin 3) :
    FormalDist (Module.End ℂ Sl2GhostSpace) := sl2GhostSVA.Y (ghostCurrent a)

/-- The three ghost currents have conformal weight one. -/
theorem ghostCurrent_weight (a : Fin 3) : ghostCurrent a ∈ sl2GhostSVA.grading 1 := by
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro c _
  exact Submodule.smul_mem _ _ (ghostBilinear_weight c b)

/-- The three ghost currents are even states of the ghost superalgebra. -/
theorem ghostCurrent_even (a : Fin 3) : ghostCurrent a ∈ sl2GhostSVA.parity 0 := by
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro c _
  exact Submodule.smul_mem _ _ (ghostBilinear_even c b)

/-- The ghost-current state products have no poles of order greater than two.
This follows from weight one and the nonnegative ghost weight grading. -/
theorem ghostCurrent_mode_eq_zero_of_two_le (a b : Fin 3) (n : ℤ) (hn : 2 ≤ n) :
    mode (ghostCurrentField a) n (ghostCurrent b) = 0 := by
  have h := sl2GhostSVA.grading_mode (ghostCurrent a) (ghostCurrent_weight a)
    (ghostCurrent b) (ghostCurrent_weight b) n
  have hbot : sl2GhostSVA.grading (1 + 1 - (n : ℂ) - 1) = ⊥ := by
    apply natSupported_sl2GhostSVA
    rintro ⟨m, hm⟩
    have hm' : ((m : ℤ) : ℂ) = ((1 - n : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    have : (m : ℤ) = 1 - n := by exact_mod_cast hm'
    omega
  rw [hbot] at h
  exact h

/-- The `e` ghost current in the Chevalley basis. -/
theorem ghostCurrent_e :
    ghostCurrent colE = ghostBilinear colH colF - (2 : ℂ) • ghostBilinear colE colH := by
  simp [ghostCurrent, ghostCurrentCoefficient, fabc, Fin.sum_univ_three]
  module

/-- The `f` ghost current in the Chevalley basis. -/
theorem ghostCurrent_f :
    ghostCurrent colF = (2 : ℂ) • ghostBilinear colF colH - ghostBilinear colH colE := by
  simp [ghostCurrent, ghostCurrentCoefficient, fabc, Fin.sum_univ_three]
  module

/-- The `h` ghost current in the Chevalley basis. -/
theorem ghostCurrent_h :
    ghostCurrent colH = (2 : ℂ) • ghostBilinear colE colE -
      (2 : ℂ) • ghostBilinear colF colF := by
  simp [ghostCurrent, ghostCurrentCoefficient, fabc, Fin.sum_univ_three]
  module

/-!
The complete singular products are proved downstream as
`ghostCurrent_simplePole` and `ghostCurrent_doublePole` in
`Sl2SemiInfiniteGhostAffine`. That module constructs
`ghostAffineAction : AffineSl2Action sl2GhostSVA 4` and proves the full
integer-mode commutator. The bridge uses the actual ghost translation data from
`Sl2SemiInfiniteTranslation`, rather than assuming an additional ghost axiom.
-/

end VOA.Sl2SemiInfinite
