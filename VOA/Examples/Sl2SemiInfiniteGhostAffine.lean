/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteTranslation
import VOA.Examples.Sl2SemiInfiniteAction
import VOA.Examples.Sl2SemiInfiniteCurrents
import VOA.Examples.Sl2SemiInfiniteBilinearProducts

/-!
# Recovering complete affine current commutators from singular state products

Translation covariance, super locality and the complete singular state-product table
imply all affine mode commutators. The actual bilinear contraction table is assembled
into `ghostAffineAction : AffineSl2Action sl2GhostSVA 4`, with no additional inputs.
`affineActionOfProducts` also exposes the general reconstruction bridge.
-/

namespace VOA.Sl2SemiInfinite
open Module (End)
open AffineVOA
open scoped BigOperators
universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Recover an actual affine current action from weight-one even states and their
singular state products. The mode identity is proved for every pair of integer modes
from translation covariance and locality. -/
noncomputable def affineActionOfProducts {V : SuperVertexAlgebra M} {k : ℂ}
    (H : TranslationCovariant V) (current : Fin 3 → M)
    (hweight : ∀ a, current a ∈ V.grading 1)
    (heven : ∀ a, current a ∈ V.parity 0)
    (hzero : ∀ a b, mode (V.Y (current a)) 0 (current b) =
      ∑ c, fabc a b c • current c)
    (hone : ∀ a b, mode (V.Y (current a)) 1 (current b) =
      (k * kappa a b) • V.vacuum)
    (hhigh : ∀ a b (j : ℤ), 2 ≤ j → mode (V.Y (current a)) j (current b) = 0) :
    AffineSl2Action V k where
  current := current
  current_weight := hweight
  current_even := heven
  current_comm a b m n := by
    have hc := H.mode_commutator_two (heven a) (heven b) (hhigh a b) m n
    rw [koszul_zero_left, one_smul, hzero, hone] at hc
    rw [hc]
    congr 1
    · simp only [Fin.sum_univ_three, map_add, map_smul, mode_add, mode_smul]
    · rw [map_smul, mode_smul, smul_smul, V.vacuum_Y, mode_apply]
      rw [FormalDist.one_apply]
      by_cases hmn : m + n = 0
      · rw [if_pos hmn, if_pos (by omega)]
        simp only [Module.End.one_eq_id]
        congr 1
        ring
      · rw [if_neg hmn, if_neg (by omega), smul_zero]

/-- The complete simple-pole table of the adjoint three-pair ghost currents. -/
theorem ghostCurrent_simplePole (a b : Fin 3) :
    mode (ghostCurrentField a) 0 (ghostCurrent b) =
      ∑ c, fabc a b c • ghostCurrent c := by
  fin_cases a <;> fin_cases b <;>
    simp only [ghostCurrentField, ghostCurrent, Fin.sum_univ_three] <;>
    norm_num only [ghostCurrentCoefficient, fabc] <;>
    simp only [map_add, map_sub, map_smul, map_neg, map_zero,
      mode_add, mode_sub, mode_smul, mode_neg, mode_zero,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, LinearMap.zero_apply, zero_smul, one_smul, smul_zero,
      add_zero, zero_add,
      ghostBilinear_simplePole] <;>
    norm_num only [fabc] <;>
    try simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      and_false, false_and, and_true, true_and, ite_false, ite_true,
      zero_add, add_zero, sub_zero, zero_sub, sub_self, smul_zero] <;> module

/-- The complete double-pole table is level `+4` in the normalized sl2 form. -/
theorem ghostCurrent_doublePole (a b : Fin 3) :
    mode (ghostCurrentField a) 1 (ghostCurrent b) =
      (4 * kappa a b) • sl2GhostSVA.vacuum := by
  fin_cases a <;> fin_cases b <;>
    simp only [ghostCurrentField, ghostCurrent, Fin.sum_univ_three] <;>
    norm_num only [ghostCurrentCoefficient, fabc] <;>
    simp only [map_add, map_sub, map_smul, map_neg, map_zero,
      mode_add, mode_sub, mode_smul, mode_neg, mode_zero,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, LinearMap.zero_apply, zero_smul, one_smul, smul_zero,
      add_zero, zero_add,
      ghostBilinear_doublePole] <;>
    norm_num only [kappa] <;>
    try simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      and_false, false_and, and_true, true_and, ite_false, ite_true,
      zero_add, add_zero, sub_zero, zero_sub, sub_self, smul_zero] <;> module

/-- The actual three-pair ghost currents form an affine sl2 action at level `+4`.
All integer-mode commutators are consequences of the explicit singular products and
translation covariance of the reconstructed tensor algebra. -/
noncomputable def ghostAffineAction : AffineSl2Action sl2GhostSVA 4 :=
  affineActionOfProducts translationCovariant_sl2GhostSVA ghostCurrent
    ghostCurrent_weight ghostCurrent_even ghostCurrent_simplePole ghostCurrent_doublePole
    ghostCurrent_mode_eq_zero_of_two_le

/-- Explicit full affine-mode commutator for the actual ghost currents. -/
theorem ghostCurrent_mode_commutator (a b : Fin 3) (m n : ℤ) :
    mode (ghostCurrentField a) m * mode (ghostCurrentField b) n
      - mode (ghostCurrentField b) n * mode (ghostCurrentField a) m =
      (∑ c, fabc a b c • mode (ghostCurrentField c) (m + n))
        + if m + n = 0 then ((m : ℂ) * 4 * kappa a b) • LinearMap.id else 0 :=
  ghostAffineAction.current_comm a b m n

end VOA.Sl2SemiInfinite
