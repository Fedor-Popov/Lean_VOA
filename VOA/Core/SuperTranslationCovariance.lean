/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperNearVOA
import VOA.Core.SuperGoddard
import VOA.Core.SuperCovariant
import VOA.Core.Borcherds

/-!
# Translation covariance for a super near-VOA  (Layer 2 of the super Borcherds chain)

The super analogue of the first half of `Core.Reconstruction`: everything the super
Borcherds/Jacobi derivation needs about `L₋₁ = ω₍₀₎`, before any `ε`-sign bookkeeping starts.

## Why this layer carries no Koszul sign

`ω` is **even** (`SuperNearVOA.conformal_parity`), so every Koszul sign in which it
participates is `1`: `koszul 0 q = 1`, and `bracketDistε 1 = bracketDist`.  The whole layer is
therefore literally the bosonic argument, with `SuperVertexAlgebra.goddard_uniquenessε` in
place of `goddard_uniqueness` and `SuperVertexAlgebra.dong_fields` (at `p = 0`) supplying the
locality of the candidate field.

## What is here

* `Y_Trε`, `mode_Y_Trε` — VOA3 in field and mode form (restated for `SuperNearVOA`; the
  `SuperVertexOperatorAlgebra` versions in `Core.SuperSkew` are not usable here because the
  Zhu layer downstream runs on `SuperNearVOA`).
* `creation_powε` — `a₍₋k₋₁₎𝟙 = L₋₁ᵏ a / k!` (proof copied from `Core.SuperSkew`).
* `translation_covariance_homε` — Goddard's identification of `Res_{z₁}[Y(ω,z₁),Y(u,z₂)]`
  with `Y(L₋₁u,z₂)`, for parity-homogeneous `u`.
* `L_comm_Ycoeffε` — `[L₋₁, (Yu)ₛ] = (s+1)(Yu)_{s+1}`, for **arbitrary** `u`: both sides
  are linear in `u`, so the parity hypothesis is discharged by the even/odd splitting.  This
  is the form the whole rest of the chain consumes.
* `Y_Tpowε`, `smul_Tpowε`, `smul_Tpow_neg_oneε`, `isField_Yε`.
-/

namespace VOA

open Module (End)

universe u

namespace SuperNearVOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  VOA3 and the vacuum tower -/

/-- **VOA3, as stated**: `Y(L₋₁u, z) = ∂_z Y(u,z)`. -/
theorem Y_Trε (V : SuperNearVOA 𝒱) (u : 𝒱) : V.Y (V.L (-1) u) = deriv (V.Y u) := by
  rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]
  exact V.translation u

/-- The mode form of the derivative property: `(L₋₁u)₍ₙ₎ = -n·u₍ₙ₋₁₎`. -/
theorem mode_Y_Trε (V : SuperNearVOA 𝒱) (u : 𝒱) (n : ℤ) :
    mode (V.Y (V.L (-1) u)) n = (-n) • mode (V.Y u) (n - 1) := by
  rw [Y_Trε, mode_deriv]

/-- `L₋₁` annihilates the vacuum. -/
theorem L_neg_one_vacuumε (V : SuperNearVOA 𝒱) : V.L (-1) V.vacuum = 0 := by
  have h : V.L (-1) V.vacuum = V.smul V.conformalVector 0 V.vacuum := by
    rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]; rfl
  rw [h]
  exact V.smul_vacuum_eq_zero V.conformalVector le_rfl

/-- **The creation theorem**: `a₍₋k₋₁₎𝟙 = L₋₁ᵏa / k!`.  Induction on `k` from VOA3 and VA3
(proof copied verbatim from `SuperVertexOperatorAlgebra.creation_powε`). -/
theorem creation_powε (V : SuperNearVOA 𝒱) (a : 𝒱) (k : ℕ) :
    V.smul a (-(k : ℤ) - 1) V.vacuum = ((k.factorial : ℂ)⁻¹) • ((V.L (-1) ^ k) a) := by
  induction k generalizing a with
  | zero =>
      rw [show (-(↑(0 : ℕ) : ℤ) - 1) = -1 by norm_num,
        SuperVertexAlgebra.smul_neg_one_vacuum]
      simp
  | succ k ih =>
      have key : V.smul (V.L (-1) a) (-(k : ℤ) - 1) V.vacuum
          = ((k : ℤ) + 1) • V.smul a (-(k : ℤ) - 2) V.vacuum := by
        rw [SuperVertexAlgebra.smul_def, SuperVertexAlgebra.smul_def, mode_Y_Trε,
          show (-(-(k : ℤ) - 1)) = (k : ℤ) + 1 by ring,
          show ((-(k : ℤ) - 1) - 1) = -(k : ℤ) - 2 by ring, LinearMap.smul_apply]
      have hih := ih (V.L (-1) a)
      have hTk : (V.L (-1) ^ k) (V.L (-1) a) = (V.L (-1) ^ (k + 1)) a := by
        rw [pow_succ]; rfl
      rw [key, hTk] at hih
      rw [show (-(↑(k + 1) : ℤ) - 1) = -(k : ℤ) - 2 by push_cast; ring]
      have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      rw [← Int.cast_smul_eq_zsmul ℂ ((k : ℤ) + 1)] at hih
      push_cast at hih
      have hX : V.smul a (-(k : ℤ) - 2) V.vacuum
          = ((k : ℂ) + 1)⁻¹ • ((k.factorial : ℂ)⁻¹ • (V.L (-1) ^ (k + 1)) a) := by
        rw [← hih, inv_smul_smul₀ hk1]
      rw [hX, smul_smul]
      congr 1
      rw [← mul_inv, Nat.factorial_succ]
      push_cast
      ring

/-- `L₋₁` is a derivation on the vacuum descendants: `L₋₁(u₍ₛ₎𝟙) = (L₋₁u)₍ₛ₎𝟙`. -/
theorem L_neg_one_smul_vacuumε (V : SuperNearVOA 𝒱) (u : 𝒱) (s : ℤ) :
    V.L (-1) (V.smul u s V.vacuum) = V.smul (V.L (-1) u) s V.vacuum := by
  rcases lt_or_ge s 0 with hs | hs
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = -(j : ℤ) - 1 := ⟨(-s - 1).toNat, by omega⟩
    rw [creation_powε, creation_powε, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ', ← pow_succ]
  · rw [V.smul_vacuum_eq_zero u hs, V.smul_vacuum_eq_zero _ hs, map_zero]

/-- **The vertex operators are fields** (VA5 restated as lower truncation). -/
theorem isField_Yε (V : SuperNearVOA 𝒱) (u : 𝒱) : IsField (V.Y u) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity u x
  refine ⟨-N, fun n hn => ?_⟩
  have h := hN (-n - 1) (by omega)
  rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h

/-! ## §2  Translation covariance -/

/-- `(Y ω)₍₋₁₎ = L₋₁`. -/
theorem Y_omega_neg_one (V : SuperNearVOA 𝒱) : (V.Y V.conformalVector) (-1) = V.L (-1) := by
  rw [L_def, show (-1 : ℤ) + 1 = 0 by ring, mode_apply]
  norm_num

/-- The field `Res_{z₁}[Y(ω,z₁), Y(u,z₂)] = [L₋₁, Y(u,z₂)]`, as `cCoeff 0` of the `ω,u`
commutator.  No sign: `ω` is even. -/
theorem cCoeff_zero_omegaε (V : SuperNearVOA 𝒱) (u : 𝒱) (m : ℤ) :
    cCoeff 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) m
      = V.L (-1) * (V.Y u) m - (V.Y u) m * V.L (-1) := by
  show mulBySubPow 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) (-1) m = _
  rw [mulBySubPow_zero]
  show bracketDist (V.Y V.conformalVector) (V.Y u) (-1) m = _
  rw [bracketDist_apply, Y_omega_neg_one]

/-- **Translation covariance** for a parity-homogeneous state:
`Res_{z₁}[Y(ω,z₁),Y(u,z)] = Y(L₋₁u,z)`.  Goddard uniqueness (`goddard_uniquenessε`), with the
candidate's locality supplied by `dong_fields` at `p = 0` — where every Koszul sign is `1`. -/
theorem translation_covariance_homε (V : SuperNearVOA 𝒱) {p : ZMod 2} {u : 𝒱}
    (hu : u ∈ V.parity p) :
    cCoeff 0 (bracketDist (V.Y V.conformalVector) (V.Y u)) = V.Y (V.L (-1) u) := by
  have hLu : V.L (-1) u ∈ V.parity p := by
    have h := V.smul_mem_parity V.conformal_parity hu 0
    rw [zero_add] at h
    have hLe : V.L (-1) u = V.smul V.conformalVector 0 u := by
      rw [L_def, show (-1 : ℤ) + 1 = 0 by ring]; rfl
    rw [hLe]; exact h
  refine V.toSuperVertexAlgebra.goddard_uniquenessε _ (V.L (-1) u) hLu (fun q b hb => ?_)
    (fun m => ?_)
  · have h := V.toSuperVertexAlgebra.dong_fields V.conformal_parity hu hb (k := 0)
    rwa [koszul_zero_left, bracketDistε_one, zero_add] at h
  · rw [cCoeff_zero_omegaε]
    show V.L (-1) ((V.Y u) m V.vacuum) - (V.Y u) m (V.L (-1) V.vacuum)
      = (V.Y (V.L (-1) u)) m V.vacuum
    have e1 : (V.Y u) m V.vacuum = V.smul u (-m - 1) V.vacuum := by
      rw [SuperVertexAlgebra.smul_def, mode_apply]; norm_num
    have e2 : (V.Y (V.L (-1) u)) m V.vacuum = V.smul (V.L (-1) u) (-m - 1) V.vacuum := by
      rw [SuperVertexAlgebra.smul_def, mode_apply]; norm_num
    rw [L_neg_one_vacuumε, map_zero, sub_zero, e1, e2, L_neg_one_smul_vacuumε]

/-- Operator translation covariance, coefficient form, for a parity-homogeneous state. -/
theorem L_comm_Ycoeff_homε (V : SuperNearVOA 𝒱) {p : ZMod 2} {u : 𝒱} (hu : u ∈ V.parity p)
    (s : ℤ) : ⁅V.L (-1), (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1) := by
  have h := congrFun (translation_covariance_homε V hu) s
  rw [cCoeff_zero_omegaε, Y_Trε, deriv_apply] at h
  rw [LieRing.of_associative_ring_bracket]
  exact h

/-- **Operator translation covariance, coefficient form, for an arbitrary state**:
`[L₋₁, (Yu)ₛ] = (s+1)·(Yu)_{s+1}`.  Both sides are linear in `u`, so the parity hypothesis of
`L_comm_Ycoeff_homε` is discharged by splitting `u` into its even and odd parts. -/
theorem L_comm_Ycoeffε (V : SuperNearVOA 𝒱) (u : 𝒱) (s : ℤ) :
    ⁅V.L (-1), (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1) := by
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ :=
    V.toSuperVertexAlgebra.toParityGrading.exists_parity_decomp u
  have hsplit : ∀ t : ℤ, (V.Y (u₀ + u₁)) t = (V.Y u₀) t + (V.Y u₁) t := by
    intro t
    rw [map_add]; rfl
  rw [hsplit, hsplit, lie_add, L_comm_Ycoeff_homε V hu₀, L_comm_Ycoeff_homε V hu₁, smul_add]

/-- Operator translation covariance, mode form: `[L₋₁, u₍ₙ₎] = -n·u₍ₙ₋₁₎`. -/
theorem L_comm_modeε (V : SuperNearVOA 𝒱) (u : 𝒱) (n : ℤ) :
    ⁅V.L (-1), mode (V.Y u) n⁆ = (-n) • mode (V.Y u) (n - 1) := by
  have h := L_comm_Ycoeffε V u (-n - 1)
  rw [show (-n - 1 : ℤ) + 1 = -n from by ring] at h
  rw [mode_apply, h, mode_apply, show (-(n - 1) - 1 : ℤ) = -n from by ring]

/-- **Translation covariance, mode form**: `[L₋₁, u₍ₙ₎] = (L₋₁u)₍ₙ₎`, i.e. `L₋₁` is a
derivation of every product. -/
theorem L_neg_one_derivε (V : SuperNearVOA 𝒱) (u w : 𝒱) (n : ℤ) :
    V.L (-1) (V.smul u n w) - V.smul u n (V.L (-1) w) = V.smul (V.L (-1) u) n w := by
  have h := DFunLike.congr_fun (L_comm_modeε V u n) w
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h
  simp only [SuperVertexAlgebra.smul_def]
  rw [mode_Y_Trε, LinearMap.smul_apply]
  exact h

/-! ## §3  The translation iterate -/

/-- `Y(L₋₁ʲu, z) = ∂_z^j Y(u,z)`. -/
theorem Y_Tpowε (V : SuperNearVOA 𝒱) (u : 𝒱) (j : ℕ) :
    V.Y ((V.L (-1) ^ j) u) = (deriv^[j]) (V.Y u) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, Y_Trε, ih, Function.iterate_succ',
        Function.comp_apply]

/-- The mode form of the translation property on a product: `(L₋₁w)₍ₙ₎v = -n·w₍ₙ₋₁₎v`. -/
theorem smul_T_applyε (V : SuperNearVOA 𝒱) (w v : 𝒱) (n : ℤ) :
    V.smul (V.L (-1) w) n v = (-n) • V.smul w (n - 1) v := by
  rw [SuperVertexAlgebra.smul_def, mode_Y_Trε, LinearMap.smul_apply]
  rfl

/-- Iterated: `(L₋₁ᵏw)₍ₙ₎v = (∏_{i<k} -(n-i))·w₍ₙ₋ₖ₎v`. -/
theorem smul_Tpowε (V : SuperNearVOA 𝒱) (u v : 𝒱) (k : ℕ) (n : ℤ) :
    V.smul ((V.L (-1) ^ k) u) n v
      = (∏ i ∈ Finset.range k, (-(n - (i : ℤ)))) • V.smul u (n - (k : ℤ)) v := by
  induction k generalizing n with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, smul_T_applyε, ih, smul_smul,
        Finset.prod_range_succ' (fun i => -(n - (i : ℤ))) j]
      have hidx : n - 1 - (j : ℤ) = n - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hidx]
      congr 1
      rw [show (-(n - ((0 : ℕ) : ℤ))) = -n by push_cast; ring, mul_comm]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)

/-- The creation identity for translates: `(L₋₁ᵏu)₍₋₁₎v = k!·u₍₋ₖ₋₁₎v`. -/
theorem smul_Tpow_neg_oneε (V : SuperNearVOA 𝒱) (u v : 𝒱) (k : ℕ) :
    V.smul ((V.L (-1) ^ k) u) (-1) v = (k.factorial : ℤ) • V.smul u (-(k : ℤ) - 1) v := by
  rw [smul_Tpowε]
  congr 1
  · rw [← VertexOperatorAlgebra.prod_one_add_factorial]; exact Finset.prod_congr rfl (fun i _ => by ring)
  · congr 1; ring

end SuperNearVOA

end VOA
