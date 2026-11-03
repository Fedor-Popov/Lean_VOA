/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGhosts

/-!
# The three ghost-pair embeddings

The unit embeddings preserve vacua, addition, scalars and all vertex products.
Fields from distinct pairs have no singular products.  The latter is recorded
here for an even first state, which is the case used by the quadratic currents.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct

@[simp] theorem ghostEmbed_zero (a : Fin 3) : ghostEmbed a 0 = 0 := by
  unfold ghostEmbed
  split_ifs <;> simp

@[simp] theorem ghostEmbed_add (a : Fin 3) (x y : SympFerm.FockSF) :
    ghostEmbed a (x + y) = ghostEmbed a x + ghostEmbed a y := by
  unfold ghostEmbed
  split_ifs <;> simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]

@[simp] theorem ghostEmbed_smul (a : Fin 3) (c : ℂ) (x : SympFerm.FockSF) :
    ghostEmbed a (c • x) = c • ghostEmbed a x := by
  unfold ghostEmbed
  split_ifs <;> simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]

@[simp] theorem ghostEmbed_vacuum (a : Fin 3) :
    ghostEmbed a SympFerm.vacSF = sl2GhostSVA.vacuum := by
  unfold ghostEmbed
  split_ifs <;> rfl

section UnitField

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

/-- An even right-factor field acts only in that factor. -/
theorem tenY_right_unit_even (V : SuperVertexAlgebra A) (W : SuperVertexAlgebra B)
    {b : B} (hb : b ∈ W.parity 0) (x : A) (y : B) (s : ℤ) :
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] b) s (x ⊗ₜ[ℂ] y) =
      x ⊗ₜ[ℂ] W.Y b s y := by
  rw [TensorVA.tenY_tmul_parity V W V.vacuum hb,
    TensorVA.kappaTen_zero, LinearMap.id_apply, TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]

end UnitField

/-- Distinct ghost pairs have no singular products with an even first state. -/
theorem ghostEmbed_Y_of_ne {a b : Fin 3} (hab : a ≠ b)
    {x : SympFerm.FockSF} (hx : x ∈ Ghost.bcGhostSVA.parity 0)
    (y : SympFerm.FockSF) {s : ℤ} (hs : s < 0) :
    sl2GhostSVA.Y (ghostEmbed a x) s (ghostEmbed b y) = 0 := by
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((SympFerm.vacSF ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SympFerm.vacSF) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (x ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] SympFerm.vacSF = 0
    rw [tenY_left_unit Ghost.bcGhostSVA Ghost.bcGhostSVA,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((x ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] y) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA,
      TensorVA.Ycoeff_vacuum_neg ghostPairSVA _ hs, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      ((y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] SympFerm.vacSF) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA]
    change TensorVA.tenY Ghost.bcGhostSVA Ghost.bcGhostSVA
      (Ghost.bcGhostSVA.vacuum ⊗ₜ[ℂ] x) s
      (y ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) ⊗ₜ[ℂ] SympFerm.vacSF = 0
    rw [tenY_right_unit_even Ghost.bcGhostSVA Ghost.bcGhostSVA hx,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs,
      TensorProduct.tmul_zero, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      ((SympFerm.vacSF ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) s
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] y) = 0
    rw [tenY_left_unit ghostPairSVA Ghost.bcGhostSVA,
      TensorVA.Ycoeff_vacuum_neg ghostPairSVA _ hs, TensorProduct.zero_tmul]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] x) s
      ((y ⊗ₜ[ℂ] SympFerm.vacSF) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) = 0
    rw [tenY_right_unit_even ghostPairSVA Ghost.bcGhostSVA hx,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs, TensorProduct.tmul_zero]
  · change TensorVA.tenY ghostPairSVA Ghost.bcGhostSVA
      (ghostPairSVA.vacuum ⊗ₜ[ℂ] x) s
      ((SympFerm.vacSF ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] Ghost.bcGhostSVA.vacuum) = 0
    rw [tenY_right_unit_even ghostPairSVA Ghost.bcGhostSVA hx,
      TensorVA.Ycoeff_vacuum_neg Ghost.bcGhostSVA x hs, TensorProduct.tmul_zero]

/-- The mode-index form of the absence of cross-pair singular products. -/
theorem ghostEmbed_mode_of_ne {a b : Fin 3} (hab : a ≠ b)
    {x : SympFerm.FockSF} (hx : x ∈ Ghost.bcGhostSVA.parity 0)
    (y : SympFerm.FockSF) {n : ℤ} (hn : 0 ≤ n) :
    mode (sl2GhostSVA.Y (ghostEmbed a x)) n (ghostEmbed b y) = 0 := by
  exact ghostEmbed_Y_of_ne hab hx y (by omega : -n - 1 < 0)

end VOA.Sl2SemiInfinite
