/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.VirasoroModule
import VOA.Core.Dong

/-!
# The Virasoro field on the abstract vacuum module

The Virasoro modes `Lₙ` acting on the universal vacuum module `VirUniv c` (= `V(c,0)`, not the simple quotient) (by the module action
`virVacRho`), their **abstract** Virasoro relation `[Lₘ,Lₙ] = (m−n)L_{m+n} + δ·(m³−m)/12·c`
(transported through the Lie hom `virVacRho` from `virasoro_bracket`), the conformal state
`ω = L₋₂|0⟩`, and the conformal field `Y(ω,z) = ∑ₙ Lₙ z^{−n−2}` as a `FormalDist`.

The self-locality of `Y(ω,z)` (the `T(z)T(w)` OPE) comes from this abstract relation — no
free-boson realization needed there.  `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)

variable (c : ℂ)

/-! ## §A  The Virasoro modes and their abstract relation. -/

/-- The Virasoro mode `Lₙ` as an operator on the universal vacuum module `VirUniv c` (the module action). -/
noncomputable def Lop (n : ℤ) : End ℂ (VirUniv c) := virVacRho c (L n)

/-- **The abstract Virasoro relation on `VirUniv c`**: `[Lₘ, Lₙ] = (m−n)L_{m+n} + δ_{m+n,0}(m³−m)/12·c`,
transported through the Lie-algebra homomorphism `virVacRho` from `virasoro_bracket`. -/
theorem Lop_bracket (m n : ℤ) :
    Lop c m * Lop c n - Lop c n * Lop c m
      = ((m : ℂ) - n) • Lop c (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) • (1 : End ℂ (VirUniv c)) := by
  simp only [Lop]
  rw [← LieRing.of_associative_ring_bracket, ← (virVacRho c).map_lie (L m) (L n),
    virasoro_bracket, map_add, map_smul]
  congr 1
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, map_smul, vac_acts_central, smul_smul]
    rfl
  · rw [if_neg hmn, if_neg hmn, map_zero, zero_smul]

/-- The Virasoro modes annihilate the vacuum for `n ≥ -1` (`L₋₁|0⟩ = 0` = translation of the
vacuum; highest weight `0`). -/
theorem Lop_vacuum {n : ℤ} (hn : -1 ≤ n) : Lop c n (vacVec c) = 0 :=
  vac_pos_annihilate c n hn

/-! ## §B  The conformal vector `ω` and the conformal field `Y(ω,z)`. -/

/-- The **conformal vector** `ω = L₋₂|0⟩` of the Virasoro VOA. -/
noncomputable def omegaVir : VirUniv c := Lop c (-2) (vacVec c)

/-- The **conformal field** `Y(ω,z) = ∑ₙ Lₙ z^{−n−2}`: the `zᵗ`-coefficient is `L_{−t−2}`. -/
noncomputable def YomegaVir : FormalDist (End ℂ (VirUniv c)) := fun t => Lop c (-t - 2)

/-- The coefficient of z to the integer power t in the conformal field is
L indexed by minus t minus two. This exposes the power-index convention
needed when converting between formal distributions and VOA mode indices. -/
@[simp] theorem YomegaVir_apply (t : ℤ) : YomegaVir c t = Lop c (-t - 2) := rfl

/-- `mode (Y(ω,z)) m = L_{m-1} = ω₍ₘ₎` (the VOA mode of `ω`); in particular `mode (Yω)(n+1) = Lₙ`. -/
theorem mode_YomegaVir (m : ℤ) : mode (YomegaVir c) m = Lop c (m - 1) := by
  rw [mode_apply, YomegaVir_apply, show (-(-m - 1) - 2) = m - 1 from by ring]

/-- The creation property `ω₍₋₁₎|0⟩ = ω`: `mode (Yω)(-1)|0⟩ = L₋₂|0⟩ = ω`. -/
theorem YomegaVir_creation : mode (YomegaVir c) (-1) (vacVec c) = omegaVir c := by
  rw [mode_YomegaVir, show (-1 - 1 : ℤ) = -2 from by ring, omegaVir]

/-- The nonnegative modes `ω₍ₙ₎|0⟩ = 0` for `n ≥ 0` (`Lₙ₋₁|0⟩ = 0`, `n ≥ 0` ⟹ `n-1 ≥ -1`). -/
theorem YomegaVir_creation_nonneg {n : ℤ} (hn : 0 ≤ n) :
    mode (YomegaVir c) n (vacVec c) = 0 := by
  rw [mode_YomegaVir]; exact Lop_vacuum c (by omega)

/-! ## §C  The `T(z)T(w)` OPE mode identity (the input to self-locality). -/

/-- **The `T(z)T(w)` OPE at the mode level** — the `(s,t)`-coefficient of `[Y(ω,z),Y(ω,w)]`:
`bracketDist Yω Yω s t = (t−s)·L_{−s−t−4} + δ_{s+t+4,0}·((−s−2)³−(−s−2))/12·c·1`, directly from
`Lop_bracket`.  This is the mode form of the OPE `T(z)T(w) ∼ (c/2)/(z−w)⁴ + 2T/(z−w)² + ∂T/(z−w)`;
decomposing it into `∑ⱼ deltaDeriv j (·)` and applying `mulBySubPow_deltaDeriv_eq_zero` yields the
self-locality `Local Yω Yω` (bound `N = 4`). -/
theorem bracketDist_YomegaVir (s t : ℤ) :
    bracketDist (YomegaVir c) (YomegaVir c) s t
      = ((t : ℂ) - s) • Lop c (-s - t - 4)
        + (if -s - t - 4 = 0 then (((-s - 2 : ℂ)) ^ 3 - (-s - 2)) / 12 * c else 0)
            • (1 : End ℂ (VirUniv c)) := by
  rw [bracketDist_apply, YomegaVir_apply, YomegaVir_apply, Lop_bracket,
    show ((-s - 2 : ℤ) + (-t - 2)) = -s - t - 4 from by ring]
  congr 2
  · push_cast; ring
  · push_cast; ring

/-! ## §D  Self-locality of `Y(ω,z)` (the `deltaDeriv` decomposition, bound `N = 4`). -/

/-- The `∂T` OPE coefficient field `(deriv Y(ω,z))(u) = (u+1)·L_{−u−3}` (the `(z−w)⁻¹` residue). -/
noncomputable def YomegaVir_deriv : FormalDist (End ℂ (VirUniv c)) :=
  fun u => ((u : ℂ) + 1) • Lop c (-u - 3)

/-- The central OPE coefficient field `(c/12)·𝟙` supported at `u = 0` (the `(z−w)⁻⁴` residue). -/
noncomputable def YomegaVir_unit : FormalDist (End ℂ (VirUniv c)) :=
  fun u => if u = 0 then (c / 12) • (1 : End ℂ (VirUniv c)) else 0

/-- **The `T(z)T(w)` OPE as a sum of `deltaDeriv`s**:
`[Y(ω,z),Y(ω,w)] = δ(z−w)·∂T + ∂_wδ(z−w)·2T + (1/3!)∂_w³δ(z−w)·(c/2)𝟙`. -/
theorem bracketDist_YomegaVir_deltaDeriv :
    bracketDist (YomegaVir c) (YomegaVir c)
      = deltaDeriv 0 (YomegaVir_deriv c) + deltaDeriv 1 ((2 : ℂ) • YomegaVir c)
        + deltaDeriv 3 (YomegaVir_unit c) := by
  refine FormalDist₂.ext (fun s t => ?_)
  have e0 : deltaDeriv 0 (YomegaVir_deriv c) s t = ((s : ℂ) + t + 2) • Lop c (-s - t - 4) := by
    rw [deltaDeriv_apply, Finset.range_zero, Finset.prod_empty, one_smul, YomegaVir_deriv,
      show (s + t + 1 + ((0 : ℕ) : ℤ)) = s + t + 1 from by push_cast; ring,
      show (-(s + t + 1) - 3) = -s - t - 4 from by ring]
    congr 1; push_cast; ring
  have e1 : deltaDeriv 1 ((2 : ℂ) • YomegaVir c) s t = (2 * (-(s : ℂ) - 1)) • Lop c (-s - t - 4) := by
    rw [deltaDeriv_apply, Finset.prod_range_one,
      show (s + t + 1 + ((1 : ℕ) : ℤ)) = s + t + 2 from by push_cast; ring]
    change (-s - 1 - ((0 : ℕ) : ℤ)) • ((2 : ℂ) • YomegaVir c (s + t + 2)) = _
    rw [YomegaVir_apply, show (-(s + t + 2) - 2) = -s - t - 4 from by ring,
      ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1; push_cast; ring
  have e3 : deltaDeriv 3 (YomegaVir_unit c) s t
      = (if s + t + 4 = 0
          then (((-(s : ℂ) - 1) * (-(s : ℂ) - 2) * (-(s : ℂ) - 3)) * (c / 12))
              • (1 : End ℂ (VirUniv c))
          else 0) := by
    rw [deltaDeriv_apply, YomegaVir_unit,
      show (s + t + 1 + ((3 : ℕ) : ℤ)) = s + t + 4 from by push_cast; ring,
      ← Int.cast_smul_eq_zsmul ℂ]
    by_cases h : s + t + 4 = 0
    · rw [if_pos h, if_pos h, smul_smul]
      congr 1
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]; push_cast; ring
    · rw [if_neg h, if_neg h, smul_zero]
  show bracketDist (YomegaVir c) (YomegaVir c) s t = _
  rw [bracketDist_YomegaVir]
  change _ = deltaDeriv 0 (YomegaVir_deriv c) s t + deltaDeriv 1 ((2 : ℂ) • YomegaVir c) s t
      + deltaDeriv 3 (YomegaVir_unit c) s t
  rw [e0, e1, e3]
  by_cases h : s + t + 4 = 0
  · rw [if_pos (by omega : -s - t - 4 = 0), if_pos h]
    have hLop : Lop c (-s - t - 4) = Lop c 0 := by congr 1; omega
    rw [hLop]; module
  · rw [if_neg (by omega : ¬ -s - t - 4 = 0), if_neg h, add_zero]
    module

/-- **`Y(ω,z)` is self-local** with bound `N = 4` (the `T(z)T(w)` OPE), from the `deltaDeriv`
decomposition + `mulBySubPow_deltaDeriv_eq_zero` — the abstract self-locality, no Fock needed. -/
theorem YomegaVir_self_local : Local (YomegaVir c) (YomegaVir c) := by
  refine ⟨4, ?_⟩
  rw [bracketDist_YomegaVir_deltaDeriv, map_add, map_add,
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 0 + 1 ≤ 4) (YomegaVir_deriv c),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 1 + 1 ≤ 4) ((2 : ℂ) • YomegaVir c),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 3 + 1 ≤ 4) (YomegaVir_unit c), add_zero, add_zero]

end VOA.VirModule
