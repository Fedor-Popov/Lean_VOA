/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedPlus
import VOA.Moonshine.SkewIntertwiner

/-!
# M8b: the skew intertwiner `W` of the Leech twisted sector

For `t ∈ TP = (V_Λ^T)^+` (the carrier of `Moonshine.plusModule : OrdVModule leechVOAPlus TP`)
and `φ ∈ VP = V_Λ^+` (the carrier of `leechVOAPlus`), the untwisted-to-twisted block of the
moonshine vertex operator (DGM CMP 1996, eq. (3.8); FHL §5.4) is

  `W(t,z)φ = e^{zL₋₁} Y_TP(φ,−z) t`,  i.e.
  `W(t)₍ₙ₎φ = ∑_{i≥0} (−1)^{n+i+1}/i! · L₋₁ⁱ(φ₍ₙ₊ᵢ₎ t)`.

Everything here is the instantiation of the general, module-agnostic theory of
`Moonshine.SkewIntertwiner` at `A := plusModule`. Since `plusModule` is an *ordinary* module
(integral modes `u₍ₙ₎ = Y^T(u)₍2n/2₎`, `mode_plusModule`; integral weights,
`plusModule_weight_ne_bot`), `W` has only integral modes and no fractional bookkeeping arises.

## Main results

* `leechLTP` — `L₋₁` on `TP`; `leechLTP_coe`: it is the twisted `ω`-mode `Y^T(ω)` at twisted
  index `0` (i.e. `ω₍₀₎`), restricted to `TP`.
* `leechWsk t : FormalDist (SkewVP →ₗ[ℂ] TP)` — the skew field; `mode_leechWsk`.
* `leechWsk_vacuum` — `W(t,z)𝟙 = e^{zL₋₁}t`.
* `leechWsk_deriv` — `W(L₋₁t, z) = ∂_z W(t, z)`.
* `leechWsk_comm` — the intertwining commutator formula, all `m ∈ ℤ`.
* `leechWsk_local` — `(z₁−z₂)ᴺ [Y_TP(u,z₁) W(t,z₂) − W(t,z₂) Y_VP(u,z₁)] = 0`.
* `leechSkewIntertwiner : Intertwiner plusModule (adjointModule leechVOAPlus) plusModule` —
  `W` is an intertwining operator of type `(TP; TP, VP)` in the sense of `Modules.Fusion`.

## Status

`sorry`-free; `#print axioms` of every declaration here is
`[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`). These are *unconditional* statements
about `plusModule`: no hypotheses beyond the already-built `leechVOAPlus` and `plusModule`.

Not done here (M8c/M8d): the adjoint `W̄` (needs the invariant forms of M8c), and the
conversion of `leechWsk_local` into the `End ℂ Vnat`-valued `Local` of the block field `Ynat`
(M8d: `W` is the `TP ← VP` block of `Ynat t`; its locality with the diagonal block
`diag(Y_VP(u), Y_TP(u))` is exactly `leechWsk_local`).
-/

namespace VOA.Moonshine

open SkewIntertwiner TwistedPlus LatticeTwisted

/-- The carrier `VP` of `V_Λ^+ = leechVOAPlus`. -/
abbrev SkewVP : Type := ↥(orbifold (Subgroup.zpowers leechTheta)).carrier

/-- `L₋₁ = ω₍₀₎` on `TP = (V_Λ^T)^+`. -/
noncomputable abbrev leechLTP : Module.End ℂ TP := Lm1 plusModule.toWeakModule

/-- `L₋₁` on `TP` is the twisted `ω`-mode at twisted index `0` (`= ω₍₀₎`), restricted. -/
theorem leechLTP_coe (x : TP) :
    ((leechLTP x : TP) : Tw) = leechTwistedModule.YM leechVOAPlus.conformalVector.1 0 x := by
  have h := mode_plusModule leechVOAPlus.conformalVector 0 x
  rw [mul_zero] at h
  exact h

/-- **The skew field** `W(t,z) ∈ Hom(VP, TP)⟦z^±⟧`, `W(t,z)φ = e^{zL₋₁} Y_TP(φ,−z) t`. -/
noncomputable def leechWsk (t : TP) : FormalDist (SkewVP →ₗ[ℂ] TP) :=
  Wsk plusModule.toWeakModule t

/-- The modes: `W(t)₍ₙ₎φ = ∑_{i≥0} (−1)^{n+i+1}/i! · L₋₁ⁱ(φ₍ₙ₊ᵢ₎ t)`. -/
theorem mode_leechWsk (t : TP) (n : ℤ) (φ : SkewVP) :
    mode (leechWsk t) n φ
      = ∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (n + i + 1)) •
          ((leechLTP ^ i) (mode (plusModule.YM φ) (n + i) t)) := by
  rw [leechWsk, mode_Wsk, wModeLin_apply]; rfl

/-- **`leechWsk_vacuum`**: `W(t,z)𝟙 = e^{zL₋₁} t`. -/
theorem leechWsk_vacuum (t : TP) (k : ℤ) :
    leechWsk t k leechVOAPlus.vacuum
      = if 0 ≤ k then ((k.toNat.factorial : ℂ)⁻¹) • (leechLTP ^ k.toNat) t else 0 :=
  Wsk_vacuum plusModule.toWeakModule t k

/-- **`leechWsk_deriv`**: `W(L₋₁t, z) = ∂_z W(t, z)`. -/
theorem leechWsk_deriv (t : TP) : leechWsk (leechLTP t) = deriv (leechWsk t) :=
  Wsk_deriv plusModule.toWeakModule t

/-- **The intertwining commutator formula** for `W` (all `m ∈ ℤ`):
`u₍ₘ₎ W(t)₍ₙ₎φ − W(t)₍ₙ₎(u₍ₘ₎φ) = ∑_{r<J} C(m,r) W(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎φ`. -/
theorem leechWsk_comm (u : SkewVP) (m : ℤ) (t : TP) (n : ℤ) (φ : SkewVP) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → mode (plusModule.YM u) j t = 0) :
    mode (plusModule.YM u) m (mode (leechWsk t) n φ)
        - mode (leechWsk t) n (leechVOAPlus.smul u m φ)
      = ∑ r ∈ Finset.range J,
          gBinom m r • mode (leechWsk (mode (plusModule.YM u) r t)) (m + n - r) φ := by
  simp only [leechWsk, mode_Wsk, wModeLin_apply]
  exact wMode_comm plusModule.toWeakModule u m t n φ J hJ

/-- **`leechWsk_local`**: `Y_TP(u, z₁)` and `W(t, z₂)` are mutually local,
`(z₁ − z₂)ᴺ [Y_TP(u,z₁) W(t,z₂) − W(t,z₂) Y_VP(u,z₁)] = 0` as a `Hom(VP, TP)`-valued
two-variable distribution. -/
theorem leechWsk_local (u : SkewVP) (t : TP) :
    ∃ N : ℕ, mulBySubPow N
      (fun a b => (plusModule.YM u a).comp (leechWsk t b)
        - (leechWsk t b).comp (leechVOAPlus.Y u a) : FormalDist₂ (SkewVP →ₗ[ℂ] TP)) = 0 :=
  Wsk_local plusModule.toWeakModule u t

/-- **`W` is an intertwining operator of type `(TP; TP, VP)`** (Gannon Def. 6.1.9, in the
`Modules.Fusion` sense): lower-truncated mode data satisfying the intertwining commutator. -/
noncomputable def leechSkewIntertwiner :
    Intertwiner plusModule (adjointModule leechVOAPlus) plusModule :=
  skewIntertwiner plusModule

theorem leechSkewIntertwiner_modes (n : ℤ) (t : TP) (φ : SkewVP) :
    leechSkewIntertwiner.modes (n : ℂ) t φ = mode (leechWsk t) n φ := by
  rw [leechSkewIntertwiner, skewIntertwiner_modes, leechWsk, mode_Wsk, wModeLin_apply]

end VOA.Moonshine
