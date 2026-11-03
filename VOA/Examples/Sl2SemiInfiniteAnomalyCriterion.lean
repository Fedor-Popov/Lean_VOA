/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteNilpotency
import VOA.Examples.Sl2SemiInfiniteAnomalyMode

/-!
# Exact level criterion for the semi-infinite BRST charge

The ghost anomaly has a nonzero zero mode. On matter with nonzero vacuum,
the tensor anomaly also has a nonzero zero mode, as witnessed by the vacuum
tensored with the Cartan antighost. Thus the proven square formula vanishes
exactly at level minus four. Matter translation covariance and tensor grading
hypotheses are stated explicitly in the operator criterion.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- A nonzero matter vacuum tensored with a nonzero ghost state remains nonzero. -/
theorem vacuum_tmul_ghost_ne_zero (hvac : V.vacuum ≠ 0)
    {x : Sl2GhostSpace} (hx : x ≠ 0) : V.vacuum ⊗ₜ[ℂ] x ≠ 0 := by
  intro hz
  have hs := congrArg (TensorProduct.comm ℂ M Sl2GhostSpace) hz
  simp only [TensorProduct.comm_tmul, map_zero] at hs
  apply hx
  apply DSMor.unitEmbed_injective V hvac
  rw [map_zero]
  exact hs

/-- The tensor anomaly zero mode is nonzero whenever the matter vacuum is nonzero. -/
theorem tensorGhostAnomaly_zero_mode_ne_zero (hvac : V.vacuum ≠ 0) :
    mode (TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostAnomalyState)) 0 ≠ 0 := by
  have hact : mode (TensorVA.tenY V sl2GhostSVA
      (V.vacuum ⊗ₜ[ℂ] ghostAnomalyState)) 0
      (V.vacuum ⊗ₜ[ℂ] bGhost AffineVOA.colH) =
      (4 : ℂ) • (V.vacuum ⊗ₜ[ℂ]
        ghostEmbed AffineVOA.colH (Ghost.ghField 1 1 (ghostZeroWord []))) := by
    change TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostAnomalyState) (-1)
      (V.vacuum ⊗ₜ[ℂ] bGhost AffineVOA.colH) = _
    rw [tenY_right_unit]
    change (V.vacuum ⊗ₜ[ℂ]
      mode (sl2GhostSVA.Y ghostAnomalyState) 0 (bGhost AffineVOA.colH)) = _
    rw [ghostAnomaly_zero_bGhost_h, TensorProduct.tmul_smul]
  intro hz
  have h := LinearMap.congr_fun hz (V.vacuum ⊗ₜ[ℂ] bGhost AffineVOA.colH)
  rw [hact, LinearMap.zero_apply] at h
  exact vacuum_tmul_ghost_ne_zero hvac ghostEmbed_derivative_c_ne_zero
    ((smul_eq_zero.mp h).resolve_left (by norm_num))

/-- The actual BRST state is closed exactly at level minus four, provided
that the matter vacuum is nonzero. This state calculation uses only the affine action. -/
theorem semiInfiniteQ_brstState_zero_iff (A : AffineSl2Action V k)
    (hvac : V.vacuum ≠ 0) : semiInfiniteQ A (brstState A) = 0 ↔ k = -4 := by
  rw [semiInfiniteQ_brstState_anomaly]
  constructor
  · intro h
    have hk : k + 4 = 0 := (smul_eq_zero.mp h).resolve_right
      (vacuum_tmul_ghost_ne_zero hvac ghostAnomalyState_ne_zero)
    linear_combination hk
  · intro hk
    rw [hk]
    norm_num

/-- The actual semi-infinite BRST charge squares to zero exactly at level minus four.
The matter vacuum is nonzero; translation covariance and tensor grading provide the
commutator transfer used in the already-proved square formula. -/
theorem semiInfiniteQ_sq_zero_iff (A : AffineSl2Action V k)
    (H : TranslationCovariant V) (hV : TensorVA.ParityCompatible V)
    (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) (hvac : V.vacuum ≠ 0) :
    semiInfiniteQ A * semiInfiniteQ A = 0 ↔ k = -4 := by
  rw [semiInfiniteQ_square_anomaly A H hV hg]
  constructor
  · intro h
    have hc : (1 / 2 : ℂ) * (k + 4) = 0 := (smul_eq_zero.mp h).resolve_right
      (tensorGhostAnomaly_zero_mode_ne_zero hvac)
    have hk : k + 4 = 0 := (mul_eq_zero.mp hc).resolve_left (by norm_num)
    linear_combination hk
  · intro hk
    rw [hk]
    norm_num

end VOA.Sl2SemiInfinite
