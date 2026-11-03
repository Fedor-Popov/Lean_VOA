/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGhosts

/-!
# Tensor field lifts for ghost mode calculations

The unit embeddings identify complete fields with their tensor lifts.
The anticommutator lemmas propagate Clifford relations through these lifts,
including the Koszul sign between distinct tensor legs.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped TensorProduct

section Lifts

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- A unit embedding identifies the entire left field with its tensor lift. -/
theorem tenY_left_unit_field (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y)
    (a : X) :
    TensorVA.tenY V W (a ⊗ₜ[ℂ] W.vacuum) = TensorVA.lftF V W a := by
  funext s
  apply TensorProduct.ext'
  intro x y
  exact tenY_left_unit V W a x y s

/-- An odd right-factor field carries the left parity involution. -/
theorem tenY_right_unit_field (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y)
    {q : ZMod 2} {b : Y} (hb : b ∈ W.parity q) :
    TensorVA.tenY V W (V.vacuum ⊗ₜ[ℂ] b) = TensorVA.rgtF V W q b := by
  funext s
  apply TensorProduct.ext'
  intro x y
  rw [TensorVA.tenY_tmul_parity V W V.vacuum hb,
    TensorVA.kappaTen_tmul, TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl]
  rfl

/-- The left tensor lift preserves anticommutators that vanish. -/
theorem lftF_anticomm (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y)
    (a b : X) (m n : ℤ)
    (h : V.Y a m * V.Y b n + V.Y b n * V.Y a m = 0) :
    TensorVA.lftF V W a m * TensorVA.lftF V W b n +
      TensorVA.lftF V W b n * TensorVA.lftF V W a m = 0 := by
  have hh := congrArg (TensorVA.mapLeftHom V W) h
  simpa only [map_add, TensorVA.mapLeftHom_mul, map_zero] using hh

/-- The right tensor lift preserves anticommutators that vanish. -/
theorem rgtF_anticomm (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y)
    (a b : Y) (q : ZMod 2) (m n : ℤ)
    (h : W.Y a m * W.Y b n + W.Y b n * W.Y a m = 0) :
    TensorVA.rgtF V W q a m * TensorVA.rgtF V W q b n +
      TensorVA.rgtF V W q b n * TensorVA.rgtF V W q a m = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.add_apply, Module.End.mul_apply, TensorVA.rgtF_tmul,
    LinearMap.zero_apply]
  rw [← TensorProduct.tmul_add]
  have hh := congrArg (fun f : End ℂ Y => f y) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at hh
  rw [hh, TensorProduct.tmul_zero]

/-- Odd fields in distinct tensor legs anticommute in every pair of modes. -/
theorem lftF_rgtF_anticomm (V : SuperVertexAlgebra X) (W : SuperVertexAlgebra Y)
    {a : X} (ha : a ∈ V.parity 1) (b : Y) (m n : ℤ) :
    TensorVA.lftF V W a m * TensorVA.rgtF V W 1 b n +
      TensorVA.rgtF V W 1 b n * TensorVA.lftF V W a m = 0 := by
  rw [TensorVA.lftF_mul_rgtF_comm V W ha 1 b m n]
  simp

end Lifts

end VOA.Sl2SemiInfinite
