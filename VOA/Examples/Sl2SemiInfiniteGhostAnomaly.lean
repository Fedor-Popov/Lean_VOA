/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteChargeProducts
import VOA.Examples.Sl2SemiInfiniteBilinearProducts

/-! # Explicit tensor coordinates of the derivative-ghost anomaly -/

namespace VOA.Sl2SemiInfinite

open Ghost SympFerm AffineVOA
open scoped BigOperators TensorProduct

/-- The three dual ghosts in ordered exterior tensor coordinates. -/
theorem cGhost_tensor (a : Fin 3) : cGhost a =
    match a.val with
    | 0 => ghostTripleWord [1] [] []
    | 1 => ghostTripleWord [] [1] []
    | _ => ghostTripleWord [] [] [1] := by
  fin_cases a <;> rfl

/-- The three antighosts in ordered exterior tensor coordinates. -/
theorem bGhost_tensor (a : Fin 3) : bGhost a =
    match a.val with
    | 0 => ghostTripleWord [0] [] []
    | 1 => ghostTripleWord [] [0] []
    | _ => ghostTripleWord [] [] [0] := by
  fin_cases a <;> rfl

/-- The `e,f` derivative-ghost product. -/
theorem cGhost_e_derivative_f :
    mode (sl2GhostSVA.Y (cGhost colE)) (-2) (cGhost colF) =
      (ghField 1 1 (ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ]
        ghostZeroWord [] := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) 1
    ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord []) = _
  rw [tenY_left_ghostVac, ghostPair_single_left]

/-- The `f,e` derivative-ghost product has the tensor Koszul sign. -/
theorem cGhost_f_derivative_e :
    mode (sl2GhostSVA.Y (cGhost colF)) (-2) (cGhost colE) =
      -((ghostZeroWord [1] ⊗ₜ[ℂ] ghField 1 1 (ghostZeroWord [])) ⊗ₜ[ℂ]
        ghostZeroWord []) := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ] ghostZeroWord []) 1
    ((ghostZeroWord [1] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord []) = _
  rw [tenY_left_ghostVac, ghostPair_single_right]
  norm_num [TensorProduct.neg_tmul]

/-- The Cartan derivative-ghost product lies wholly in the last factor. -/
theorem cGhost_h_derivative_h :
    mode (sl2GhostSVA.Y (cGhost colH)) (-2) (cGhost colH) =
      (ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ]
        ghField 1 1 (ghostZeroWord [1]) := by
  change TensorVA.tenY ghostPairSVA bcGhostSVA
    ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) 1
    ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) = _
  rw [tenY_last_unit_word]
  norm_num

/-- The actual level anomaly in ordered tensor coordinates. The two mixed
terms and the Cartan term carry the normalised Killing-form coefficients. -/
theorem ghostAnomalyState_tensor :
    ghostAnomalyState =
      (ghField 1 1 (ghostZeroWord []) ⊗ₜ[ℂ] ghostZeroWord [1]) ⊗ₜ[ℂ]
          ghostZeroWord [] -
        (ghostZeroWord [1] ⊗ₜ[ℂ] ghField 1 1 (ghostZeroWord [])) ⊗ₜ[ℂ]
          ghostZeroWord [] +
        (2 : ℂ) • ((ghostZeroWord [] ⊗ₜ[ℂ] ghostZeroWord []) ⊗ₜ[ℂ]
          ghField 1 1 (ghostZeroWord [1])) := by
  have he := cGhost_e_derivative_f
  have hf := cGhost_f_derivative_e
  have hh := cGhost_h_derivative_h
  norm_num [colE, colF, colH, mode] at he hf hh
  simp only [ghostAnomalyState, Fin.sum_univ_three]
  norm_num [kappa]
  rw [he, hf, hh]
  module

/-- The derivative-ghost anomaly is a nonzero state. Two contractions in the
Cartan pair isolate twice the nonzero vacuum. -/
theorem ghostAnomalyState_ne_zero : ghostAnomalyState ≠ 0 := by
  let D : Module.End ℂ FockSF := annBase (0, 1) * annBase (1, 1)
  have hDv : D (ghostZeroWord []) = 0 := by
    change annBase (0, 1) (annBase (1, 1) (stWordSF [])) = 0
    rw [annBase_stWordSF_nil, map_zero]
  have hDc : D (ghField 1 1 (ghostZeroWord [1])) = ghostZeroWord [] := by
    change annBase (0, 1)
      (annBase (1, 1) (stWordSF [((1, 1) : ℕ × Fin 2), (0, 1)])) = stWordSF []
    simp [annBase_stWordSF_cons, annBase_stWordSF_nil, ← stWordSF_nil]
  have hmap : TensorProduct.map (LinearMap.id : Module.End ℂ GhostPairSpace) D
      ghostAnomalyState = (2 : ℂ) • sl2GhostSVA.vacuum := by
    rw [ghostAnomalyState_tensor]
    simp only [map_add, map_sub, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
      hDv, hDc, TensorProduct.tmul_zero, zero_sub, zero_add]
    rfl
  intro hz
  rw [hz, map_zero] at hmap
  have hv : sl2GhostSVA.vacuum = 0 :=
    (smul_eq_zero.mp hmap.symm).resolve_left (by norm_num)
  exact sl2GhostSVA_vacuum_ne_zero hv

end VOA.Sl2SemiInfinite
