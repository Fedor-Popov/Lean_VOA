/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SquareBracketGrading
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Schwarzian derivative and the cylinder→torus coordinate  (Gannon 5.3.15e–f, 5.3.16)

GOAL C.  The change of coordinate underlying Zhu's square bracket is `w = f(z) = e^z − 1` (the
cylinder→torus map).  Under a change of coordinate a Virasoro field transforms with an extra
**Schwarzian** term `(c/12)·{f;z}` (Gannon 5.3.15e–f), and the whole point of this particular `f` is:

  **`{e^z − 1; z} = −1/2`** — a *constant* (`schwarzian_expMinusOne`).

That constant is exactly what produced the `δ_{m+n,−2}` coboundary in the Gel'fand–Fuks cocycle
`centralMomentClosed_holds`: a constant Schwarzian contributes a `δ_{m+n,−2}` term with coefficient
`−(m−n)/2`, and the `ω̃` vacuum term of `Lsq` absorbs it, leaving the clean Virasoro relation
`Lsq_virasoro` with the *same* central charge.  So this file is the conceptual companion of
`GelfandFuks.lean`: same `−1/2`, arrived at from the coordinate side.

Everything is a formal `PowerSeries ℂ` computation — `ℂ⟦X⟧` has `Inv` (ℂ is a field), and
`PowerSeries.exp` with `derivative_exp : d(exp) = exp` does all the work.

## Status
(C1) is proved (`schwarzian_expMinusOne`), axiom-clean and `pbw`-free, engine-confirmed
(`certificates/mathematica/schwarzian_check.wl`: `{e^z−1;z} = −1/2` exactly, plus the sanity checks
`{z;z} = 0` and `{e^{2πiz}−1;z} = 2π²`).  (C2), the operator `T_f`, is built in
`Modularity.ChangeCoord` (`changeCoord`, an equivalence).  (C3), the general transformation law,
is not proved (see the note at the end).

## References
* Gannon §5.3.4–5, eqs. (5.3.15e–f), (5.3.16); Zhu, J. AMS 9 (1996) §4.
-/

namespace VOA

open PowerSeries

/-! ## The Schwarzian derivative of a formal power series -/

/-- **The Schwarzian derivative** `{f; z} = f‴/f′ − (3/2)·(f″/f′)²`, as a formal power-series
operation (`ℂ⟦X⟧` has `Inv` since `ℂ` is a field; the formula is meaningful exactly when `f′` is a
unit, i.e. `f` has nonzero linear coefficient). -/
noncomputable def schwarzian (f : PowerSeries ℂ) : PowerSeries ℂ :=
  derivativeFun (derivativeFun (derivativeFun f)) * (derivativeFun f)⁻¹
    - (3 / 2 : ℂ) • ((derivativeFun (derivativeFun f) * (derivativeFun f)⁻¹) ^ 2)

theorem derivativeFun_sub (f g : PowerSeries ℂ) :
    derivativeFun (f - g) = derivativeFun f - derivativeFun g := by
  show (PowerSeries.derivative ℂ) (f - g)
    = (PowerSeries.derivative ℂ) f - (PowerSeries.derivative ℂ) g
  exact map_sub _ f g

/-- **The cylinder→torus coordinate** `f(z) = e^z − 1` (Gannon 5.3.16a: `w = e^z − 1`; the torus
normalization `e^{2πiz} − 1` differs by the `2πi` rescaling). -/
noncomputable def expMinusOne : PowerSeries ℂ := PowerSeries.exp ℂ - 1

/-- `f′ = e^z` for `f = e^z − 1`. -/
theorem derivativeFun_expMinusOne : derivativeFun expMinusOne = PowerSeries.exp ℂ := by
  rw [expMinusOne, derivativeFun_sub, PowerSeries.derivativeFun_one, sub_zero]
  exact PowerSeries.derivative_exp ℂ

/-- **`{e^z − 1; z} = −1/2`** — the Schwarzian of the cylinder→torus map is the **constant**
`−1/2`.  This is the coordinate-side origin of the `δ_{m+n,−2}` Schwarzian anomaly that
`centralMomentClosed_holds` computes on the cocycle side, and which the `ω̃` vacuum term of `Lsq`
cancels (`Lsq_virasoro`).  Engine-confirmed. -/
theorem schwarzian_expMinusOne :
    schwarzian expMinusOne = (-(1 / 2) : ℂ) • (1 : PowerSeries ℂ) := by
  have hd1 : derivativeFun expMinusOne = PowerSeries.exp ℂ := derivativeFun_expMinusOne
  have hd2 : derivativeFun (derivativeFun expMinusOne) = PowerSeries.exp ℂ := by
    rw [hd1]; exact PowerSeries.derivative_exp ℂ
  have hd3 : derivativeFun (derivativeFun (derivativeFun expMinusOne)) = PowerSeries.exp ℂ := by
    rw [hd2]; exact PowerSeries.derivative_exp ℂ
  have hcc : PowerSeries.constantCoeff (R := ℂ) (PowerSeries.exp ℂ) ≠ 0 := by
    rw [PowerSeries.constantCoeff_exp]; norm_num
  have hinv : PowerSeries.exp ℂ * (PowerSeries.exp ℂ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hcc
  rw [schwarzian, hd3, hd2, hd1, hinv, one_pow]
  calc (1 : PowerSeries ℂ) - (3 / 2 : ℂ) • (1 : PowerSeries ℂ)
      = ((1 : ℂ) - (3 / 2 : ℂ)) • (1 : PowerSeries ℂ) := by rw [sub_smul, one_smul]
    _ = (-(1 / 2) : ℂ) • (1 : PowerSeries ℂ) := by norm_num

/-- Sanity check: the Schwarzian of the identity coordinate `z` vanishes. -/
theorem schwarzian_X : schwarzian (PowerSeries.X : PowerSeries ℂ) = 0 := by
  have h1 : derivativeFun (PowerSeries.X : PowerSeries ℂ) = 1 := derivativeFun_X
  have h2 : derivativeFun (derivativeFun (PowerSeries.X : PowerSeries ℂ)) = 0 := by
    rw [h1, PowerSeries.derivativeFun_one]
  have h3 : derivativeFun (derivativeFun (derivativeFun (PowerSeries.X : PowerSeries ℂ))) = 0 := by
    rw [h2]
    show (PowerSeries.derivative ℂ) 0 = 0
    exact map_zero _
  rw [schwarzian, h3, h2, h1]
  simp

/-! ## (C2) `changeCoord T_f` (built) and (C3) the general transformation law (open)

* **(C2)** — **built** in `Modularity.ChangeCoord` (`changeCoord W a : 𝒱 ≃ₗ[ℂ] 𝒱`, for an arbitrary
  coefficient family, via the locally nilpotent exponential `expEquiv`).  The original plan read:
  `changeCoord T_f` for `f(z) = e^z − 1`: the operator `T_f = exp(Σ_{k ≥ 1} a_k L_k)` with
  `f(z) = exp(Σ a_k z^{k+1} ∂_z) z`.  It must be built as a **locally finite** operator on `𝒱`, the
  same way `vSqZ`/`gradedExpL0` are (a `finsum` whose finiteness comes from VA5 `W.regularity` plus
  the fact that each `L_k`, `k ≥ 1`, strictly lowers the `L₀`-grade — cf.
  `SquareBracketGrading.sqBracketCoeff_zero_of_neg`).  A *general* formal exponential of an operator
  series is **not** needed and should not be attempted.
* **(C3)** the transformation law `T_f Y(v,z) T_f⁻¹ = Y(v,z)·f′(z)^k` on primaries (5.3.15d) and, on
  the stress tensor, the same with the Schwarzian term `(c/12)·{f;z}` (5.3.15e–f) — which by
  `schwarzian_expMinusOne` is the constant `−c/24`, i.e. precisely the `ω̃ = ω − (c/24)𝟙` shift
  already built into `Lsq`.

The consequences of (C3) that the Zhu-modularity route consumes are proved independently, without
the conjugation law: the square-bracket Virasoro relation (`Lsq_virasoro`) and the arbitrary-state
commutator `[L[0], a[j]] = (L[0]a)[j] − (j+1)a[j]` (`Lsq_zero_sqMode_comm`,
`Modularity.SqModeWeight`).  So (C3) is needed only for the general coordinate-change API, not as a
prerequisite for Zhu's theorem.
-/

end VOA
