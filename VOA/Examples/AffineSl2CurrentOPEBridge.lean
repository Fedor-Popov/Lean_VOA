/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2CurrentRealization
import VOA.Core.OPE

/-!
# From the affine current OPE to universal vacuum evaluation

The inverse-DS calculation is naturally stated as the singular OPE of a linear family of
`sl₂`-valued currents.  `AffineCurrentFieldData` records exactly that OPE, lower truncation,
the grading operator, and the vacuum conditions.  This file converts it to `AffineCurrentData`,
and hence to the universal evaluation map from the affine vacuum module.

Thus a concrete free-field triple does not have to construct a representation of the full affine
Lie algebra by hand: the three current OPEs are the only nonformal commutator input.
-/

namespace VOA.AffineVOA

open Module (End)
open VOA.AffineLie

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The identity-valued coefficient field used by a second-order current pole. -/
noncomputable def affineIdentityOPECoeff : FormalDist (End ℂ E) :=
  fun n => if n = 0 then (1 : End ℂ E) else 0

@[simp] theorem affineIdentityOPECoeff_zero :
    affineIdentityOPECoeff (E := E) 0 = 1 := by
  rw [affineIdentityOPECoeff, if_pos rfl]

theorem affineIdentityOPECoeff_ne_zero {n : ℤ} (hn : n ≠ 0) :
    affineIdentityOPECoeff (E := E) n = 0 := by
  rw [affineIdentityOPECoeff, if_neg hn]

/-- The coefficient-extraction part of `mode_bracket_ope`, without a vertex-algebra shell. -/
theorem mode_bracket_ope_fields {a b : FormalDist (End ℂ E)} {N : ℕ}
    {c : Fin N → FormalDist (End ℂ E)}
    (h : bracketDist a b = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (m n : ℤ) :
    ⁅mode a m, mode b n⁆ = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))) •
        mode (c j) (m + n - ((j : ℕ) : ℤ)) := by
  have hcomm : ⁅mode a m, mode b n⁆ = bracketDist a b (-m - 1) (-n - 1) := by
    simp only [bracketDist_apply, LieRing.of_associative_ring_bracket, mode_apply]
  rw [hcomm, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-m - 1) - 1 - (i : ℤ))) =
        ∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ)) from
      Finset.prod_congr rfl fun i _ => by ring]
  congr 1
  rw [mode_apply]
  congr 1
  ring

/-- Current fields whose singular OPE is the affine `sl₂` OPE at level `k`. -/
structure AffineCurrentFieldData (k : ℂ) (E : Type u) [AddCommGroup E] [Module ℂ E] where
  /-- A linear current field `x ↦ Jˣ(z)`. -/
  field : Sl2 →ₗ[ℂ] FormalDist (End ℂ E)
  /-- Every current is lower truncated. -/
  isField : ∀ x : Sl2, IsField (field x)
  /-- The complete singular affine current OPE. -/
  bracket : ∀ x y : Sl2,
    bracketDist (field x) (field y) =
      deltaDeriv 0 (field ⁅x, y⁆) +
        deltaDeriv 1
          ((k * kappaForm x y) • affineIdentityOPECoeff (E := E))
  /-- The affine grading derivation on the target carrier. -/
  degree : End ℂ E
  /-- The proposed target vacuum. -/
  vacuum : E
  /-- Degree covariance of the current modes. -/
  degree_comm_mode : ∀ (x : Sl2) (n : ℤ),
    ⁅degree, mode (field x) n⁆ = (n : ℂ) • mode (field x) n
  /-- Nonnegative current modes annihilate the vacuum. -/
  pos_annihilate : ∀ (x : Sl2) (n : ℤ), 0 ≤ n → mode (field x) n vacuum = 0
  /-- The affine grading derivation annihilates the vacuum. -/
  degree_vacuum : degree vacuum = 0

namespace AffineCurrentFieldData

variable {k : ℂ} (D : AffineCurrentFieldData k E)

/-- The mode of the linear current family, as a linear map in `sl₂`. -/
noncomputable def loopMode (n : ℤ) : Sl2 →ₗ[ℂ] End ℂ E where
  toFun x := mode (D.field x) n
  map_add' x y := by
    rw [map_add]
    rfl
  map_smul' c x := by
    rw [map_smul]
    rfl

@[simp] theorem loopMode_apply (n : ℤ) (x : Sl2) :
    D.loopMode n x = mode (D.field x) n := rfl

/-- The current OPE gives the affine mode commutator, including its exact central term. -/
theorem loopMode_comm (x y : Sl2) (m n : ℤ) :
    ⁅D.loopMode m x, D.loopMode n y⁆
      = D.loopMode (m + n) ⁅x, y⁆
        + (if m + n = 0 then ((m : ℂ) * kappaForm x y) •
            (k • (1 : End ℂ E)) else 0) := by
  change ⁅mode (D.field x) m, mode (D.field y) n⁆ = _
  calc
    ⁅mode (D.field x) m, mode (D.field y) n⁆
        = bracketDist (D.field x) (D.field y) (-m - 1) (-n - 1) := by
          simp only [bracketDist_apply, LieRing.of_associative_ring_bracket, mode_apply]
    _ = (deltaDeriv 0 (D.field ⁅x, y⁆) +
          deltaDeriv 1
            ((k * kappaForm x y) • affineIdentityOPECoeff (E := E)))
          (-m - 1) (-n - 1) := by rw [D.bracket]
    _ = D.loopMode (m + n) ⁅x, y⁆
          + (if m + n = 0 then ((m : ℂ) * kappaForm x y) •
              (k • (1 : End ℂ E)) else 0) := by
      change deltaDeriv 0 (D.field ⁅x, y⁆) (-m - 1) (-n - 1) +
          deltaDeriv 1
            ((k * kappaForm x y) • affineIdentityOPECoeff (E := E))
            (-m - 1) (-n - 1) = _
      rw [deltaDeriv_apply, deltaDeriv_apply]
      simp only [Finset.range_zero, Finset.prod_empty, one_smul,
        Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero]
      norm_num only [Nat.cast_one]
      rw [show -m - 1 + (-n - 1) + 1 + 0 = -m - n - 1 by ring,
        show -m - 1 + (-n - 1) + 1 + (1 : ℤ) = -m - n by ring,
        show -(-m - 1) - 1 = m by ring]
      change D.field ⁅x, y⁆ (-m - n - 1) +
          m • ((k * kappaForm x y) •
            affineIdentityOPECoeff (E := E) (-m - n)) = _
      rw [show D.field ⁅x, y⁆ (-m - n - 1) =
          D.loopMode (m + n) ⁅x, y⁆ by
        rw [loopMode_apply, mode_apply]
        congr 1
        ring]
      by_cases hmn : m + n = 0
      · rw [if_pos hmn, show -m - n = 0 by omega, affineIdentityOPECoeff_zero,
          ← Int.cast_smul_eq_zsmul ℂ]
        module
      · rw [if_neg hmn, affineIdentityOPECoeff_ne_zero (by omega)]
        simp

/-- The affine OPE is local with the uniform bound two. -/
theorem field_local (x y : Sl2) : Local (D.field x) (D.field y) := by
  refine ⟨2, ?_⟩
  rw [D.bracket, map_add]
  change mulBySubPow 2 (deltaDeriv 0 (D.field ⁅x, y⁆)) +
      mulBySubPow 2
        (deltaDeriv 1 ((k * kappaForm x y) • affineIdentityOPECoeff)) = 0
  rw [mulBySubPow_deltaDeriv_eq_zero (by norm_num),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num), add_zero]

/-- Forget the field presentation and retain the affine current representation data. -/
noncomputable def toAffineCurrentData : AffineCurrentData k E where
  loopMode := D.loopMode
  degree := D.degree
  vacuum := D.vacuum
  loop_comm := D.loopMode_comm
  degree_comm := D.degree_comm_mode
  pos_annihilate := D.pos_annihilate
  degree_vacuum := D.degree_vacuum

/-- The resulting evaluation from the universal affine vacuum module. -/
noncomputable def eval : WakModule k →ₗ[ℂ] E :=
  D.toAffineCurrentData.toVacuumCurrentRealization.eval

@[simp] theorem eval_vacuum :
    D.eval (vacuumVector kappaForm kappaForm_isInvariant k) = D.vacuum :=
  D.toAffineCurrentData.toVacuumCurrentRealization.eval_vacuum

theorem eval_vacuumRho (x : Sl2) (n : ℤ) (v : WakModule k) :
    D.eval (vacuumRho kappaForm kappaForm_isInvariant k
      (ofLoop kappaForm kappaForm_isInvariant x n) v) =
      mode (D.field x) n (D.eval v) := by
  rw [eval, VacuumCurrentRealization.eval_vacuumRho,
    AffineCurrentData.toVacuumCurrentRealization_current]
  rfl

end AffineCurrentFieldData

end
end VOA.AffineVOA
