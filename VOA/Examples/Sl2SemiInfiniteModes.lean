/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteCharge

/-!
# The actual semi-infinite charge in mode coordinates

This file identifies the residue already defined in `Sl2SemiInfiniteCharge`
with its locally finite current-mode sum and the cubic ghost residue.  The
matter parity involution supplies the Koszul sign, including when matter has
odd states.  No reconstruction or additional matter axiom is used.

The `c` field has weight zero.  Accordingly its physical coefficient `c_n`
is vertex mode `n - 1`; the current-mode summand is `J_n ⊗ c_{-n}`.

OPEN: complete the locally finite sum rearrangement for the pure mode-algebra
proof without translation hypotheses. The independent finite-state calculation
and translation commutator in `Sl2SemiInfiniteNilpotency` already prove operator
nilpotency for translated matter. The decomposition below by itself is not a
nilpotency certificate.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped BigOperators TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The sign-free current-times-ghost part of the charge. -/
noncomputable def matterModeCharge (A : AffineSl2Action V k) :
    End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  ∑ a : Fin 3, TensorVA.rawCoeff V sl2GhostSVA (A.current a) (cGhost a) (-1)

/-- The sign-free cubic-ghost correction acting in the ghost factor. -/
noncomputable def cubicModeCharge (V : SuperVertexAlgebra M) :
    End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  TensorProduct.map LinearMap.id (mode (sl2GhostSVA.Y ghostBRSTState) 0)

/-- A right-factor odd field is its raw coefficient followed by the matter parity sign. -/
theorem tenY_tmul_odd_eq (V : SuperVertexAlgebra M) (a : M)
    {b : Sl2GhostSpace} (hb : b ∈ sl2GhostSVA.parity 1) (s : ℤ) :
    TensorVA.tenY V sl2GhostSVA (a ⊗ₜ[ℂ] b) s =
      TensorVA.rawCoeff V sl2GhostSVA a b s * TensorVA.kappaTen V sl2GhostSVA 1 := by
  apply LinearMap.ext
  intro z
  exact TensorVA.tenY_tmul_parity V sl2GhostSVA a hb s z

/-- For a vacuum in the matter leg, the raw coefficient acts only in the ghost leg. -/
theorem rawCoeff_vacuum_left (V : SuperVertexAlgebra M) (b : Sl2GhostSpace) (s : ℤ) :
    TensorVA.rawCoeff V sl2GhostSVA V.vacuum b s =
      TensorProduct.map LinearMap.id (sl2GhostSVA.Y b s) := by
  apply TensorProduct.ext'
  intro x y
  rw [TensorVA.rawCoeff_tmul]
  rw [finsum_eq_single _ 0 (fun m hm => by
    rw [DSMor.Y_vacuum_applySVA, if_neg hm, TensorProduct.zero_tmul])]
  rw [sub_zero, DSMor.Y_vacuum_applySVA, if_pos rfl, TensorProduct.map_tmul]
  rfl

/-- The exact operator decomposition of the already defined BRST residue. -/
theorem semiInfiniteQ_eq_modeCharges (A : AffineSl2Action V k) :
    semiInfiniteQ A = (matterModeCharge A + cubicModeCharge V) *
      TensorVA.kappaTen V sl2GhostSVA 1 := by
  change TensorVA.tenY V sl2GhostSVA (brstState A) (-1) = _
  rw [brstState, map_add, map_sum]
  change (∑ a : Fin 3, TensorVA.tenY V sl2GhostSVA
    (A.current a ⊗ₜ[ℂ] cGhost a) (-1)) +
    TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostBRSTState) (-1) = _
  simp only [tenY_tmul_odd_eq V _ (cGhost_odd _),
    tenY_tmul_odd_eq V _ ghostBRSTState_odd, rawCoeff_vacuum_left]
  rw [add_mul]
  unfold matterModeCharge
  rw [Finset.sum_mul]
  rfl

/-- The local finiteness required by the current-mode formula. -/
theorem currentMode_support (A : AffineSl2Action V k) (a : Fin 3) (x : M)
    (y : Sl2GhostSpace) :
    (Function.support (fun n : ℤ =>
      mode (V.Y (A.current a)) n x ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y)).Finite := by
  have h := TensorVA.raw_support V sl2GhostSVA (A.current a) (cGhost a) (-1) x y
  let e : ℤ ≃ ℤ :=
    { toFun := fun n => -n - 1
      invFun := fun n => -n - 1
      left_inv := by intro n; dsimp; omega
      right_inv := by intro n; dsimp; omega }
  have he := h.preimage e.injective.injOn
  change (Function.support ((fun n : ℤ => V.Y (A.current a) n x ⊗ₜ[ℂ]
    sl2GhostSVA.Y (cGhost a) (-1 - n) y) ∘ e)).Finite at he
  simpa only [Function.comp_def, mode_apply, e, Equiv.coe_fn_mk,
    show ∀ n : ℤ, -1 - (-n - 1) = -(-n - 1) - 1 from by intro n; ring] using he

/-- Each current-times-ghost residue is the locally finite sum `∑ n, J_n ⊗ c_{-n}`. -/
theorem rawCurrentCharge_tmul (A : AffineSl2Action V k) (a : Fin 3) (x : M)
    (y : Sl2GhostSpace) :
    TensorVA.rawCoeff V sl2GhostSVA (A.current a) (cGhost a) (-1) (x ⊗ₜ[ℂ] y) =
      ∑ᶠ n : ℤ, mode (V.Y (A.current a)) n x ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y := by
  rw [TensorVA.rawCoeff_tmul]
  let e : ℤ ≃ ℤ :=
    { toFun := fun n => -n - 1
      invFun := fun n => -n - 1
      left_inv := by intro n; dsimp; omega
      right_inv := by intro n; dsimp; omega }
  have he := finsum_comp_equiv (f := fun n : ℤ =>
    V.Y (A.current a) n x ⊗ₜ[ℂ] sl2GhostSVA.Y (cGhost a) (-1 - n) y) e
  simpa only [mode_apply, e, Equiv.coe_fn_mk,
    show ∀ n : ℤ, -1 - (-n - 1) = -(-n - 1) - 1 from by intro n; ring] using he.symm

/-- The complete charge on a pure tensor, with the matter parity operator explicit. -/
theorem semiInfiniteQ_tmul (A : AffineSl2Action V k) (x : M) (y : Sl2GhostSpace) :
    semiInfiniteQ A (x ⊗ₜ[ℂ] y) =
      (∑ a : Fin 3, ∑ᶠ n : ℤ,
        mode (V.Y (A.current a)) n ((TensorVA.parGr V).parityInvol x) ⊗ₜ[ℂ]
          mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y) +
      (TensorVA.parGr V).parityInvol x ⊗ₜ[ℂ]
        mode (sl2GhostSVA.Y ghostBRSTState) 0 y := by
  rw [semiInfiniteQ_eq_modeCharges, Module.End.mul_apply, TensorVA.kappaTen_tmul,
    TensorVA.koszulOp_one, LinearMap.add_apply]
  simp only [matterModeCharge, LinearMap.sum_apply, rawCurrentCharge_tmul,
    cubicModeCharge, TensorProduct.map_tmul, LinearMap.id_apply]

end VOA.Sl2SemiInfinite
