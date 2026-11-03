/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHL0

/-!
# The `hL0` grading scalar for an ARBITRARY `A(𝒱)`-module with an `[ω]`-scalar

`Modules.ZhuVermaAnArchHL0.pHL0` proves Dong–Jiang's `L₀`-grading law for `U = Ω(P)`, the bottom of
an *already existing* irreducible lowest-weight module `P`.  For residual **(b)** that is circular:
the realization has to start from an abstract simple `A(𝒱)`-module.

Reading `pHL0`'s proof declaration by declaration, the only place `P` enters is the single line
`[ω]·w = P.h·w`, i.e. `lowestAMod_omegaScalar`.  Everything else — the representative-level collapse
`[ω ∗̄ⁿ₀ v] = [v ∗ⁿ₀ ω] + n·[v]` off `dj23Comm_holds` and `anmLgen_mem_Onm`, and the balancing
relation — is `U`-independent. So the theorem holds verbatim for any `U : AMod W` carrying
`AMod.OmegaScalar U h`; the independent `BottomProjection` hypothesis `Pr` is not needed either.

## Main result

* `genHL0` — `hL0` from `AMod.OmegaScalar` alone.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **The `L₀`-grading scalar, scoped only by `AMod.OmegaScalar`.**  Dong–Jiang's `ω₍₁₎ = L₀`
acts on the level-`n` piece of `M(U)` by `h + n`, for any `U` on which the Zhu class `[ω]` acts by
the single scalar `h`. -/
theorem genHL0 (U : AMod W) (hval : ℂ) (homegaU : U.OmegaScalar hval) :
    ∀ (n : ℕ) (x : DJCarrier W (U.toAmModZero)), x ∈ DJCarrier.deg W (U.toAmModZero) n →
      djModeZero W (U.toAmModZero) 1 W.conformalVector x = (hval + n) • x := by
  intro n x hx
  -- The representative-level collapse `[ω ∗̄^n_0 v] = [v ∗^n_0 ω] + n·[v]` in `A_{n,0}(𝒱)`.
  have hkeyGen : ∀ v : 𝒱,
      mkAnmFull W n 0 (anmGen W n 0 n W.conformalVector v)
        = mkAnmFull W n 0 (anmRight W n 0 v W.conformalVector) + (n : ℂ) • mkAnmFull W n 0 v := by
    intro v
    -- `resFull W 0 Q ω v = ω₍₋Q₎ v` (a single-mode delta).
    have resFull_zero_delta : ∀ Q : ℤ,
        resFull W 0 Q W.conformalVector v = W.smul W.conformalVector (-Q) v := by
      intro Q
      rw [resFull]
      have hsingle : ∀ l : ℤ, l ≠ -Q →
          cbz 0 (l + Q) • W.smul W.conformalVector l v = 0 := by
        intro l hl
        rw [cbz_zero_left, if_neg (show l + Q ≠ 0 by omega), zero_smul]
      rw [finsum_eq_single
        (fun l : ℤ => cbz (0 : ℤ) (l + Q) • W.smul W.conformalVector l v) (-Q) hsingle]
      show cbz 0 (-Q + Q) • W.smul W.conformalVector (-Q) v = W.smul W.conformalVector (-Q) v
      rw [show (-Q + Q : ℤ) = 0 by ring, cbz_zero, one_smul]
    -- `Res_z (1+z) Y(ω,z) v = ω₍₀₎ v + ω₍₁₎ v`.
    have hres : resExp W 1 W.conformalVector v
        = W.smul W.conformalVector 0 v + W.smul W.conformalVector 1 v := by
      rw [resExp_eq_resFull, resFull_pascal W 1 0 W.conformalVector v,
        show (1 : ℤ) - 1 = 0 by ring, resFull_zero_delta 0, resFull_zero_delta (0 - 1),
        neg_zero, show (-(0 - 1) : ℤ) = 1 by ring]
    -- `ω₍₀₎ = L₋₁`, `ω₍₁₎ = L₀`.
    have hL1 : W.smul W.conformalVector (0 : ℤ) v = W.L (-1) v := by
      rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = (0 : ℤ) by ring]
    have hL0 : W.smul W.conformalVector (1 : ℤ) v = W.L 0 v := by
      rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = (1 : ℤ) by ring]
    -- `Res_z (1+z) Y(ω,z) v − n·v = anmLgen W n 0 v`.
    have hresL : resExp W 1 W.conformalVector v - (n : ℂ) • v = anmLgen W n 0 v := by
      rw [hres, hL1, hL0, anmLgen]
      push_cast
      module
    -- The skew relation (DJ 2.3) plus the grading generator: the difference lies in `O'_{n,0}`.
    have hmemOnm : anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
        - (n : ℂ) • v ∈ Onm W n 0 := by
      have h23 := dj23Comm_holds W 2 W.conformalVector W.conformalVector_mem_grading_two
        v 0 n 0 n (by push_cast; ring)
      rw [show ((2 : ℤ) - 1 + ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = (1 : ℤ) by norm_num,
        anmGen_eq_anmRight W n 0 v W.conformalVector] at h23
      have hcombine : anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
            - (n : ℂ) • v
          = (anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
              - resExp W 1 W.conformalVector v)
            + (resExp W 1 W.conformalVector v - (n : ℂ) • v) := by abel
      rw [hcombine, hresL]
      exact Submodule.add_mem _ h23 (anmLgen_mem_Onm W n 0 v)
    -- Push into the quotient `A_{n,0}(𝒱) = 𝒱 / O_{n,0}(𝒱)`.
    have hquot : mkAnmFull W n 0 (anmGen W n 0 n W.conformalVector v
        - anmRight W n 0 v W.conformalVector - (n : ℂ) • v) = 0 := by
      rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Onm_le_OnmFull W n 0 hmemOnm
    rw [map_sub, map_sub, map_smul] at hquot
    rw [← sub_eq_zero, ← hquot]
    abel
  -- Reduce to the two linear maps `ω₍₁₎ ∘ incl` and `(hval+n) • incl` agreeing on generators.
  have hx' : x ∈ LinearMap.range (DJCarrier.incl W (U.toAmModZero) n) := hx
  rw [LinearMap.mem_range] at hx'
  obtain ⟨y, rfl⟩ := hx'
  suffices hFG : (djModeZero W (U.toAmModZero) 1 W.conformalVector).comp
        (DJCarrier.incl W (U.toAmModZero) n)
      = (hval + (n : ℂ)) • DJCarrier.incl W (U.toAmModZero) n by
    have hcf := LinearMap.congr_fun hFG y
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using hcf
  refine djPiece_ext (fun v w => ?_)
  -- `[ω]` acts by `hval` on the bottom `Ω(P)`.
  have homega : (U.toAmModZero).ρ (mkAnFull W 0 W.conformalVector) w = hval • w := by
    rw [AMod.toAmModZero_ρ]
    exact AMod.omegaScalar_apply homegaU w
  have hN : muTargetLevel (2 : ℤ) 1 n = ((n : ℕ) : ℤ) := by
    unfold muTargetLevel; ring
  rw [LinearMap.comp_apply, LinearMap.smul_apply, djModeZero,
    djMode_apply_tmul (U.toAmModZero) (djActionDescent_zero W) 1
      W.conformalVector_mem_grading_two hN v w,
    ← LinearMap.map_smul (DJCarrier.incl W (U.toAmModZero) n) (hval + (n : ℂ))
      (mkDJPiece W (U.toAmModZero) n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w))]
  refine congrArg (DJCarrier.incl W (U.toAmModZero) n) ?_
  rw [hkeyGen v, TensorProduct.add_tmul, map_add, ← TensorProduct.smul_tmul', map_smul,
    mkDJPiece_balance (U.toAmModZero) n v W.conformalVector w, homega,
    TensorProduct.tmul_smul, map_smul, ← add_smul]

end VOA
