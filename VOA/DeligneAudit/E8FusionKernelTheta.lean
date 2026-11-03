/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8FusionKernel
import VOA.DeligneAudit.D4FusionKernelTheta

/-!
# `ThetaNilG` for `E₈`: `f_θ^{2k+1} w = 0` by a Heisenberg chain

the `D₄` argument, carried to `E₈` exactly as for `E₇` (`E7FusionKernelTheta`). In the table basis, `x₁₂₈` is
the simple lowering vector with `θ(h₇) = 1`, and `x₁₂₉ … x₁₃₅` are the seven simple roots orthogonal to `θ`.

The chain (found by `Notes/deligne/campaign/generators/e8_kernel_scan.py`) is `128 → 136 → 143 → 150 → 157 → 164 → 171 → 178 → 184 → 190 → 196 → 202 → 207 → 212 → 216 → 220 → 224 → 228 → 231 → 234 → 236 → 238 → 241 → 242 → 243 → 244 → 245 → 246`, 27 steps,
reaching `f_{θ-α} = x₂₄₆`. Each step is followed by `sl₂` sharpening (`root_sharpen8`; the `h₇`-coefficient of
`[e_γ, f_γ]` is `-1`). The last step is `[f₂₄₆, f₁₂₈] = -f_θ`.

* `e8_thetaNil : ThetaNilG E8sector`, unconditional.
* `e8_ravinderKernelRel'`.
* `e8_fusionModuleBound_of_totalBound`: U5 for `E₈` from `FusionTotalBoundG E8sector`, the Demazure
  realizations, and the named count `E8FusionCount`.

The declarations are in the namespace `UnivG.E8K`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.E8K

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E8 (E8sector thetaH lowExpE8)

noncomputable section

/-! ## Table facts for the chain -/

/-- The `∀ e` form of one chain step, from support checks on the three entries. -/
theorem chainZ_of {a b z : Fin 248} {c : ℤ}
    (h : suppIn (brK a b) (· == z.val) = true ∧ sget (brK a b) z = c ∧
      suppIn (brK a z) (fun _ => false) = true ∧ suppIn (brK b z) (fun _ => false) = true) :
    (∀ e : Fin 248, fZ brK a b e = if e = z then c else 0) ∧
      (∀ e : Fin 248, fZ brK a z e = 0) ∧ (∀ e : Fin 248, fZ brK b z e = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e => ?_, fun e => sget_eq_zero_of_suppIn h3 rfl, fun e => sget_eq_zero_of_suppIn h4 rfl⟩
  split_ifs with he
  · subst he; exact h2
  · exact sget_eq_zero_of_suppIn h1 (ne_val he)

theorem e8_chainL_0 : suppIn (brK 128 129) (· == 136) = true ∧ sget (brK 128 129) 136 = 1 ∧
    suppIn (brK 128 136) (fun _ => false) = true ∧ suppIn (brK 129 136) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_0 :
    (∀ e : Fin 248, fZ brK 128 129 e = if e = 136 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 128 136 e = 0) ∧ (∀ e : Fin 248, fZ brK 129 136 e = 0) :=
  chainZ_of (a := 128) (b := 129) (z := 136) e8_chainL_0

theorem e8_chainL_1 : suppIn (brK 136 130) (· == 143) = true ∧ sget (brK 136 130) 143 = -1 ∧
    suppIn (brK 136 143) (fun _ => false) = true ∧ suppIn (brK 130 143) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_1 :
    (∀ e : Fin 248, fZ brK 136 130 e = if e = 143 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 136 143 e = 0) ∧ (∀ e : Fin 248, fZ brK 130 143 e = 0) :=
  chainZ_of (a := 136) (b := 130) (z := 143) e8_chainL_1

theorem e8_chainL_2 : suppIn (brK 143 131) (· == 150) = true ∧ sget (brK 143 131) 150 = -1 ∧
    suppIn (brK 143 150) (fun _ => false) = true ∧ suppIn (brK 131 150) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_2 :
    (∀ e : Fin 248, fZ brK 143 131 e = if e = 150 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 143 150 e = 0) ∧ (∀ e : Fin 248, fZ brK 131 150 e = 0) :=
  chainZ_of (a := 143) (b := 131) (z := 150) e8_chainL_2

theorem e8_chainL_3 : suppIn (brK 150 132) (· == 157) = true ∧ sget (brK 150 132) 157 = -1 ∧
    suppIn (brK 150 157) (fun _ => false) = true ∧ suppIn (brK 132 157) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_3 :
    (∀ e : Fin 248, fZ brK 150 132 e = if e = 157 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 150 157 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 157 e = 0) :=
  chainZ_of (a := 150) (b := 132) (z := 157) e8_chainL_3

theorem e8_chainL_4 : suppIn (brK 157 133) (· == 164) = true ∧ sget (brK 157 133) 164 = -1 ∧
    suppIn (brK 157 164) (fun _ => false) = true ∧ suppIn (brK 133 164) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_4 :
    (∀ e : Fin 248, fZ brK 157 133 e = if e = 164 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 157 164 e = 0) ∧ (∀ e : Fin 248, fZ brK 133 164 e = 0) :=
  chainZ_of (a := 157) (b := 133) (z := 164) e8_chainL_4

theorem e8_chainL_5 : suppIn (brK 164 134) (· == 171) = true ∧ sget (brK 164 134) 171 = -1 ∧
    suppIn (brK 164 171) (fun _ => false) = true ∧ suppIn (brK 134 171) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_5 :
    (∀ e : Fin 248, fZ brK 164 134 e = if e = 171 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 164 171 e = 0) ∧ (∀ e : Fin 248, fZ brK 134 171 e = 0) :=
  chainZ_of (a := 164) (b := 134) (z := 171) e8_chainL_5

theorem e8_chainL_6 : suppIn (brK 171 132) (· == 178) = true ∧ sget (brK 171 132) 178 = 1 ∧
    suppIn (brK 171 178) (fun _ => false) = true ∧ suppIn (brK 132 178) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_6 :
    (∀ e : Fin 248, fZ brK 171 132 e = if e = 178 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 171 178 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 178 e = 0) :=
  chainZ_of (a := 171) (b := 132) (z := 178) e8_chainL_6

theorem e8_chainL_7 : suppIn (brK 178 131) (· == 184) = true ∧ sget (brK 178 131) 184 = 1 ∧
    suppIn (brK 178 184) (fun _ => false) = true ∧ suppIn (brK 131 184) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_7 :
    (∀ e : Fin 248, fZ brK 178 131 e = if e = 184 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 178 184 e = 0) ∧ (∀ e : Fin 248, fZ brK 131 184 e = 0) :=
  chainZ_of (a := 178) (b := 131) (z := 184) e8_chainL_7

theorem e8_chainL_8 : suppIn (brK 184 130) (· == 190) = true ∧ sget (brK 184 130) 190 = 1 ∧
    suppIn (brK 184 190) (fun _ => false) = true ∧ suppIn (brK 130 190) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_8 :
    (∀ e : Fin 248, fZ brK 184 130 e = if e = 190 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 184 190 e = 0) ∧ (∀ e : Fin 248, fZ brK 130 190 e = 0) :=
  chainZ_of (a := 184) (b := 130) (z := 190) e8_chainL_8

theorem e8_chainL_9 : suppIn (brK 190 129) (· == 196) = true ∧ sget (brK 190 129) 196 = 1 ∧
    suppIn (brK 190 196) (fun _ => false) = true ∧ suppIn (brK 129 196) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_9 :
    (∀ e : Fin 248, fZ brK 190 129 e = if e = 196 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 190 196 e = 0) ∧ (∀ e : Fin 248, fZ brK 129 196 e = 0) :=
  chainZ_of (a := 190) (b := 129) (z := 196) e8_chainL_9

theorem e8_chainL_10 : suppIn (brK 196 135) (· == 202) = true ∧ sget (brK 196 135) 202 = -1 ∧
    suppIn (brK 196 202) (fun _ => false) = true ∧ suppIn (brK 135 202) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_10 :
    (∀ e : Fin 248, fZ brK 196 135 e = if e = 202 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 196 202 e = 0) ∧ (∀ e : Fin 248, fZ brK 135 202 e = 0) :=
  chainZ_of (a := 196) (b := 135) (z := 202) e8_chainL_10

theorem e8_chainL_11 : suppIn (brK 202 133) (· == 207) = true ∧ sget (brK 202 133) 207 = -1 ∧
    suppIn (brK 202 207) (fun _ => false) = true ∧ suppIn (brK 133 207) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_11 :
    (∀ e : Fin 248, fZ brK 202 133 e = if e = 207 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 202 207 e = 0) ∧ (∀ e : Fin 248, fZ brK 133 207 e = 0) :=
  chainZ_of (a := 202) (b := 133) (z := 207) e8_chainL_11

theorem e8_chainL_12 : suppIn (brK 207 132) (· == 212) = true ∧ sget (brK 207 132) 212 = 1 ∧
    suppIn (brK 207 212) (fun _ => false) = true ∧ suppIn (brK 132 212) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_12 :
    (∀ e : Fin 248, fZ brK 207 132 e = if e = 212 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 207 212 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 212 e = 0) :=
  chainZ_of (a := 207) (b := 132) (z := 212) e8_chainL_12

theorem e8_chainL_13 : suppIn (brK 212 131) (· == 216) = true ∧ sget (brK 212 131) 216 = 1 ∧
    suppIn (brK 212 216) (fun _ => false) = true ∧ suppIn (brK 131 216) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_13 :
    (∀ e : Fin 248, fZ brK 212 131 e = if e = 216 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 212 216 e = 0) ∧ (∀ e : Fin 248, fZ brK 131 216 e = 0) :=
  chainZ_of (a := 212) (b := 131) (z := 216) e8_chainL_13

theorem e8_chainL_14 : suppIn (brK 216 130) (· == 220) = true ∧ sget (brK 216 130) 220 = 1 ∧
    suppIn (brK 216 220) (fun _ => false) = true ∧ suppIn (brK 130 220) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_14 :
    (∀ e : Fin 248, fZ brK 216 130 e = if e = 220 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 216 220 e = 0) ∧ (∀ e : Fin 248, fZ brK 130 220 e = 0) :=
  chainZ_of (a := 216) (b := 130) (z := 220) e8_chainL_14

theorem e8_chainL_15 : suppIn (brK 220 134) (· == 224) = true ∧ sget (brK 220 134) 224 = 1 ∧
    suppIn (brK 220 224) (fun _ => false) = true ∧ suppIn (brK 134 224) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_15 :
    (∀ e : Fin 248, fZ brK 220 134 e = if e = 224 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 220 224 e = 0) ∧ (∀ e : Fin 248, fZ brK 134 224 e = 0) :=
  chainZ_of (a := 220) (b := 134) (z := 224) e8_chainL_15

theorem e8_chainL_16 : suppIn (brK 224 132) (· == 228) = true ∧ sget (brK 224 132) 228 = 1 ∧
    suppIn (brK 224 228) (fun _ => false) = true ∧ suppIn (brK 132 228) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_16 :
    (∀ e : Fin 248, fZ brK 224 132 e = if e = 228 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 224 228 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 228 e = 0) :=
  chainZ_of (a := 224) (b := 132) (z := 228) e8_chainL_16

theorem e8_chainL_17 : suppIn (brK 228 131) (· == 231) = true ∧ sget (brK 228 131) 231 = 1 ∧
    suppIn (brK 228 231) (fun _ => false) = true ∧ suppIn (brK 131 231) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_17 :
    (∀ e : Fin 248, fZ brK 228 131 e = if e = 231 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 228 231 e = 0) ∧ (∀ e : Fin 248, fZ brK 131 231 e = 0) :=
  chainZ_of (a := 228) (b := 131) (z := 231) e8_chainL_17

theorem e8_chainL_18 : suppIn (brK 231 133) (· == 234) = true ∧ sget (brK 231 133) 234 = 1 ∧
    suppIn (brK 231 234) (fun _ => false) = true ∧ suppIn (brK 133 234) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_18 :
    (∀ e : Fin 248, fZ brK 231 133 e = if e = 234 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 231 234 e = 0) ∧ (∀ e : Fin 248, fZ brK 133 234 e = 0) :=
  chainZ_of (a := 231) (b := 133) (z := 234) e8_chainL_18

theorem e8_chainL_19 : suppIn (brK 234 132) (· == 236) = true ∧ sget (brK 234 132) 236 = 1 ∧
    suppIn (brK 234 236) (fun _ => false) = true ∧ suppIn (brK 132 236) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_19 :
    (∀ e : Fin 248, fZ brK 234 132 e = if e = 236 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 234 236 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 236 e = 0) :=
  chainZ_of (a := 234) (b := 132) (z := 236) e8_chainL_19

theorem e8_chainL_20 : suppIn (brK 236 134) (· == 238) = true ∧ sget (brK 236 134) 238 = -1 ∧
    suppIn (brK 236 238) (fun _ => false) = true ∧ suppIn (brK 134 238) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_20 :
    (∀ e : Fin 248, fZ brK 236 134 e = if e = 238 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 236 238 e = 0) ∧ (∀ e : Fin 248, fZ brK 134 238 e = 0) :=
  chainZ_of (a := 236) (b := 134) (z := 238) e8_chainL_20

theorem e8_chainL_21 : suppIn (brK 238 135) (· == 241) = true ∧ sget (brK 238 135) 241 = 1 ∧
    suppIn (brK 238 241) (fun _ => false) = true ∧ suppIn (brK 135 241) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_21 :
    (∀ e : Fin 248, fZ brK 238 135 e = if e = 241 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 238 241 e = 0) ∧ (∀ e : Fin 248, fZ brK 135 241 e = 0) :=
  chainZ_of (a := 238) (b := 135) (z := 241) e8_chainL_21

theorem e8_chainL_22 : suppIn (brK 241 133) (· == 242) = true ∧ sget (brK 241 133) 242 = 1 ∧
    suppIn (brK 241 242) (fun _ => false) = true ∧ suppIn (brK 133 242) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_22 :
    (∀ e : Fin 248, fZ brK 241 133 e = if e = 242 then 1 else 0) ∧
    (∀ e : Fin 248, fZ brK 241 242 e = 0) ∧ (∀ e : Fin 248, fZ brK 133 242 e = 0) :=
  chainZ_of (a := 241) (b := 133) (z := 242) e8_chainL_22

theorem e8_chainL_23 : suppIn (brK 242 132) (· == 243) = true ∧ sget (brK 242 132) 243 = -1 ∧
    suppIn (brK 242 243) (fun _ => false) = true ∧ suppIn (brK 132 243) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_23 :
    (∀ e : Fin 248, fZ brK 242 132 e = if e = 243 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 242 243 e = 0) ∧ (∀ e : Fin 248, fZ brK 132 243 e = 0) :=
  chainZ_of (a := 242) (b := 132) (z := 243) e8_chainL_23

theorem e8_chainL_24 : suppIn (brK 243 131) (· == 244) = true ∧ sget (brK 243 131) 244 = -1 ∧
    suppIn (brK 243 244) (fun _ => false) = true ∧ suppIn (brK 131 244) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_24 :
    (∀ e : Fin 248, fZ brK 243 131 e = if e = 244 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 243 244 e = 0) ∧ (∀ e : Fin 248, fZ brK 131 244 e = 0) :=
  chainZ_of (a := 243) (b := 131) (z := 244) e8_chainL_24

theorem e8_chainL_25 : suppIn (brK 244 130) (· == 245) = true ∧ sget (brK 244 130) 245 = -1 ∧
    suppIn (brK 244 245) (fun _ => false) = true ∧ suppIn (brK 130 245) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_25 :
    (∀ e : Fin 248, fZ brK 244 130 e = if e = 245 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 244 245 e = 0) ∧ (∀ e : Fin 248, fZ brK 130 245 e = 0) :=
  chainZ_of (a := 244) (b := 130) (z := 245) e8_chainL_25

theorem e8_chainL_26 : suppIn (brK 245 129) (· == 246) = true ∧ sget (brK 245 129) 246 = -1 ∧
    suppIn (brK 245 246) (fun _ => false) = true ∧ suppIn (brK 129 246) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_26 :
    (∀ e : Fin 248, fZ brK 245 129 e = if e = 246 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 245 246 e = 0) ∧ (∀ e : Fin 248, fZ brK 129 246 e = 0) :=
  chainZ_of (a := 245) (b := 129) (z := 246) e8_chainL_26

theorem e8_chainL_27 : suppIn (brK 246 128) (· == 247) = true ∧ sget (brK 246 128) 247 = -1 ∧
    suppIn (brK 246 247) (fun _ => false) = true ∧ suppIn (brK 128 247) (fun _ => false) = true := by
  decide +kernel

theorem e8_chainZ_27 :
    (∀ e : Fin 248, fZ brK 246 128 e = if e = 247 then -1 else 0) ∧
    (∀ e : Fin 248, fZ brK 246 247 e = 0) ∧ (∀ e : Fin 248, fZ brK 128 247 e = 0) :=
  chainZ_of (a := 246) (b := 128) (z := 247) e8_chainL_27

/-- `sl₂` data of the root `γ` with raising partner `e`, where `[e, f_γ] = -h_γ` and `θ(h_γ) = 1`. The `sl₂`
relation is summed over the Cartan part only. -/
def RootSl2E8 (e γ : Fin 248) : Prop :=
  (8 ≤ e.val ∧ e.val < 128) ∧ (∀ c : Fin 248, fZ brK e γ c ≠ 0 → c.val < 8) ∧ fZ brK e γ 7 = -1 ∧
    ∀ d : Fin 248, ∑ c : Fin 248, (if c.val < 8 then fZ brK e γ c * fZ brK c γ d else 0) =
      if d = γ then 2 else 0

/-- `RootSl2E8` from support checks: `[e, f_γ]` lies in the Cartan part with `h₇`-coefficient `-1`, each
`[h_c, f_γ]` (`c < 8`) is a multiple of `f_γ`, and the `sl₂` pairing is `2`. -/
theorem rootSl2_of {e γ : Fin 248} (hE : 8 ≤ e.val ∧ e.val < 128)
    (h : suppIn (brK e γ) (fun c => decide (c < 8)) = true ∧ sget (brK e γ) 7 = -1 ∧
      (∀ c, c < 8 → suppIn (brK c γ) (· == γ.val) = true) ∧
      ∑ c ∈ Finset.range 8, sget (brK e γ) c * sget (brK c γ) γ = 2) : RootSl2E8 e γ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hE, fun c hc => ?_, h2, fun d => ?_⟩
  · simpa using mem_of_suppIn h1 hc
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 8 then fZ brK e γ i * fZ brK i γ d else 0) 248,
    show Finset.range 248 = Finset.range (8 + 240) from rfl, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range 240) (fun i _ => by simp)]
  rw [add_zero, Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
  split_ifs with hd
  · subst hd; exact h4
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [show fZ brK i γ d = 0 from sget_eq_zero_of_suppIn (h3 i (Finset.mem_range.mp hi)) (ne_val hd),
      mul_zero]

theorem e8_rootSl2L_136 : suppIn (brK 16 136) (fun c => decide (c < 8)) = true ∧ sget (brK 16 136) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 136) (· == 136) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 16 136) c * sget (brK c 136) 136 = 2 := by
  decide +kernel

theorem e8_rootSl2_136 : RootSl2E8 16 136 :=
  rootSl2_of (show 8 ≤ (16 : Fin 248).val ∧ (16 : Fin 248).val < 128 by decide) e8_rootSl2L_136

theorem e8_rootSl2L_143 : suppIn (brK 23 143) (fun c => decide (c < 8)) = true ∧ sget (brK 23 143) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 143) (· == 143) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 23 143) c * sget (brK c 143) 143 = 2 := by
  decide +kernel

theorem e8_rootSl2_143 : RootSl2E8 23 143 :=
  rootSl2_of (show 8 ≤ (23 : Fin 248).val ∧ (23 : Fin 248).val < 128 by decide) e8_rootSl2L_143

theorem e8_rootSl2L_150 : suppIn (brK 30 150) (fun c => decide (c < 8)) = true ∧ sget (brK 30 150) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 150) (· == 150) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 30 150) c * sget (brK c 150) 150 = 2 := by
  decide +kernel

theorem e8_rootSl2_150 : RootSl2E8 30 150 :=
  rootSl2_of (show 8 ≤ (30 : Fin 248).val ∧ (30 : Fin 248).val < 128 by decide) e8_rootSl2L_150

theorem e8_rootSl2L_157 : suppIn (brK 37 157) (fun c => decide (c < 8)) = true ∧ sget (brK 37 157) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 157) (· == 157) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 37 157) c * sget (brK c 157) 157 = 2 := by
  decide +kernel

theorem e8_rootSl2_157 : RootSl2E8 37 157 :=
  rootSl2_of (show 8 ≤ (37 : Fin 248).val ∧ (37 : Fin 248).val < 128 by decide) e8_rootSl2L_157

theorem e8_rootSl2L_164 : suppIn (brK 44 164) (fun c => decide (c < 8)) = true ∧ sget (brK 44 164) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 164) (· == 164) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 44 164) c * sget (brK c 164) 164 = 2 := by
  decide +kernel

theorem e8_rootSl2_164 : RootSl2E8 44 164 :=
  rootSl2_of (show 8 ≤ (44 : Fin 248).val ∧ (44 : Fin 248).val < 128 by decide) e8_rootSl2L_164

theorem e8_rootSl2L_171 : suppIn (brK 51 171) (fun c => decide (c < 8)) = true ∧ sget (brK 51 171) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 171) (· == 171) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 51 171) c * sget (brK c 171) 171 = 2 := by
  decide +kernel

theorem e8_rootSl2_171 : RootSl2E8 51 171 :=
  rootSl2_of (show 8 ≤ (51 : Fin 248).val ∧ (51 : Fin 248).val < 128 by decide) e8_rootSl2L_171

theorem e8_rootSl2L_178 : suppIn (brK 58 178) (fun c => decide (c < 8)) = true ∧ sget (brK 58 178) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 178) (· == 178) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 58 178) c * sget (brK c 178) 178 = 2 := by
  decide +kernel

theorem e8_rootSl2_178 : RootSl2E8 58 178 :=
  rootSl2_of (show 8 ≤ (58 : Fin 248).val ∧ (58 : Fin 248).val < 128 by decide) e8_rootSl2L_178

theorem e8_rootSl2L_184 : suppIn (brK 64 184) (fun c => decide (c < 8)) = true ∧ sget (brK 64 184) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 184) (· == 184) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 64 184) c * sget (brK c 184) 184 = 2 := by
  decide +kernel

theorem e8_rootSl2_184 : RootSl2E8 64 184 :=
  rootSl2_of (show 8 ≤ (64 : Fin 248).val ∧ (64 : Fin 248).val < 128 by decide) e8_rootSl2L_184

theorem e8_rootSl2L_190 : suppIn (brK 70 190) (fun c => decide (c < 8)) = true ∧ sget (brK 70 190) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 190) (· == 190) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 70 190) c * sget (brK c 190) 190 = 2 := by
  decide +kernel

theorem e8_rootSl2_190 : RootSl2E8 70 190 :=
  rootSl2_of (show 8 ≤ (70 : Fin 248).val ∧ (70 : Fin 248).val < 128 by decide) e8_rootSl2L_190

theorem e8_rootSl2L_196 : suppIn (brK 76 196) (fun c => decide (c < 8)) = true ∧ sget (brK 76 196) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 196) (· == 196) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 76 196) c * sget (brK c 196) 196 = 2 := by
  decide +kernel

theorem e8_rootSl2_196 : RootSl2E8 76 196 :=
  rootSl2_of (show 8 ≤ (76 : Fin 248).val ∧ (76 : Fin 248).val < 128 by decide) e8_rootSl2L_196

theorem e8_rootSl2L_202 : suppIn (brK 82 202) (fun c => decide (c < 8)) = true ∧ sget (brK 82 202) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 202) (· == 202) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 82 202) c * sget (brK c 202) 202 = 2 := by
  decide +kernel

theorem e8_rootSl2_202 : RootSl2E8 82 202 :=
  rootSl2_of (show 8 ≤ (82 : Fin 248).val ∧ (82 : Fin 248).val < 128 by decide) e8_rootSl2L_202

theorem e8_rootSl2L_207 : suppIn (brK 87 207) (fun c => decide (c < 8)) = true ∧ sget (brK 87 207) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 207) (· == 207) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 87 207) c * sget (brK c 207) 207 = 2 := by
  decide +kernel

theorem e8_rootSl2_207 : RootSl2E8 87 207 :=
  rootSl2_of (show 8 ≤ (87 : Fin 248).val ∧ (87 : Fin 248).val < 128 by decide) e8_rootSl2L_207

theorem e8_rootSl2L_212 : suppIn (brK 92 212) (fun c => decide (c < 8)) = true ∧ sget (brK 92 212) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 212) (· == 212) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 92 212) c * sget (brK c 212) 212 = 2 := by
  decide +kernel

theorem e8_rootSl2_212 : RootSl2E8 92 212 :=
  rootSl2_of (show 8 ≤ (92 : Fin 248).val ∧ (92 : Fin 248).val < 128 by decide) e8_rootSl2L_212

theorem e8_rootSl2L_216 : suppIn (brK 96 216) (fun c => decide (c < 8)) = true ∧ sget (brK 96 216) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 216) (· == 216) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 96 216) c * sget (brK c 216) 216 = 2 := by
  decide +kernel

theorem e8_rootSl2_216 : RootSl2E8 96 216 :=
  rootSl2_of (show 8 ≤ (96 : Fin 248).val ∧ (96 : Fin 248).val < 128 by decide) e8_rootSl2L_216

theorem e8_rootSl2L_220 : suppIn (brK 100 220) (fun c => decide (c < 8)) = true ∧ sget (brK 100 220) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 220) (· == 220) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 100 220) c * sget (brK c 220) 220 = 2 := by
  decide +kernel

theorem e8_rootSl2_220 : RootSl2E8 100 220 :=
  rootSl2_of (show 8 ≤ (100 : Fin 248).val ∧ (100 : Fin 248).val < 128 by decide) e8_rootSl2L_220

theorem e8_rootSl2L_224 : suppIn (brK 104 224) (fun c => decide (c < 8)) = true ∧ sget (brK 104 224) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 224) (· == 224) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 104 224) c * sget (brK c 224) 224 = 2 := by
  decide +kernel

theorem e8_rootSl2_224 : RootSl2E8 104 224 :=
  rootSl2_of (show 8 ≤ (104 : Fin 248).val ∧ (104 : Fin 248).val < 128 by decide) e8_rootSl2L_224

theorem e8_rootSl2L_228 : suppIn (brK 108 228) (fun c => decide (c < 8)) = true ∧ sget (brK 108 228) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 228) (· == 228) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 108 228) c * sget (brK c 228) 228 = 2 := by
  decide +kernel

theorem e8_rootSl2_228 : RootSl2E8 108 228 :=
  rootSl2_of (show 8 ≤ (108 : Fin 248).val ∧ (108 : Fin 248).val < 128 by decide) e8_rootSl2L_228

theorem e8_rootSl2L_231 : suppIn (brK 111 231) (fun c => decide (c < 8)) = true ∧ sget (brK 111 231) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 231) (· == 231) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 111 231) c * sget (brK c 231) 231 = 2 := by
  decide +kernel

theorem e8_rootSl2_231 : RootSl2E8 111 231 :=
  rootSl2_of (show 8 ≤ (111 : Fin 248).val ∧ (111 : Fin 248).val < 128 by decide) e8_rootSl2L_231

theorem e8_rootSl2L_234 : suppIn (brK 114 234) (fun c => decide (c < 8)) = true ∧ sget (brK 114 234) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 234) (· == 234) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 114 234) c * sget (brK c 234) 234 = 2 := by
  decide +kernel

theorem e8_rootSl2_234 : RootSl2E8 114 234 :=
  rootSl2_of (show 8 ≤ (114 : Fin 248).val ∧ (114 : Fin 248).val < 128 by decide) e8_rootSl2L_234

theorem e8_rootSl2L_236 : suppIn (brK 116 236) (fun c => decide (c < 8)) = true ∧ sget (brK 116 236) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 236) (· == 236) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 116 236) c * sget (brK c 236) 236 = 2 := by
  decide +kernel

theorem e8_rootSl2_236 : RootSl2E8 116 236 :=
  rootSl2_of (show 8 ≤ (116 : Fin 248).val ∧ (116 : Fin 248).val < 128 by decide) e8_rootSl2L_236

theorem e8_rootSl2L_238 : suppIn (brK 118 238) (fun c => decide (c < 8)) = true ∧ sget (brK 118 238) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 238) (· == 238) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 118 238) c * sget (brK c 238) 238 = 2 := by
  decide +kernel

theorem e8_rootSl2_238 : RootSl2E8 118 238 :=
  rootSl2_of (show 8 ≤ (118 : Fin 248).val ∧ (118 : Fin 248).val < 128 by decide) e8_rootSl2L_238

theorem e8_rootSl2L_241 : suppIn (brK 121 241) (fun c => decide (c < 8)) = true ∧ sget (brK 121 241) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 241) (· == 241) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 121 241) c * sget (brK c 241) 241 = 2 := by
  decide +kernel

theorem e8_rootSl2_241 : RootSl2E8 121 241 :=
  rootSl2_of (show 8 ≤ (121 : Fin 248).val ∧ (121 : Fin 248).val < 128 by decide) e8_rootSl2L_241

theorem e8_rootSl2L_242 : suppIn (brK 122 242) (fun c => decide (c < 8)) = true ∧ sget (brK 122 242) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 242) (· == 242) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 122 242) c * sget (brK c 242) 242 = 2 := by
  decide +kernel

theorem e8_rootSl2_242 : RootSl2E8 122 242 :=
  rootSl2_of (show 8 ≤ (122 : Fin 248).val ∧ (122 : Fin 248).val < 128 by decide) e8_rootSl2L_242

theorem e8_rootSl2L_243 : suppIn (brK 123 243) (fun c => decide (c < 8)) = true ∧ sget (brK 123 243) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 243) (· == 243) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 123 243) c * sget (brK c 243) 243 = 2 := by
  decide +kernel

theorem e8_rootSl2_243 : RootSl2E8 123 243 :=
  rootSl2_of (show 8 ≤ (123 : Fin 248).val ∧ (123 : Fin 248).val < 128 by decide) e8_rootSl2L_243

theorem e8_rootSl2L_244 : suppIn (brK 124 244) (fun c => decide (c < 8)) = true ∧ sget (brK 124 244) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 244) (· == 244) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 124 244) c * sget (brK c 244) 244 = 2 := by
  decide +kernel

theorem e8_rootSl2_244 : RootSl2E8 124 244 :=
  rootSl2_of (show 8 ≤ (124 : Fin 248).val ∧ (124 : Fin 248).val < 128 by decide) e8_rootSl2L_244

theorem e8_rootSl2L_245 : suppIn (brK 125 245) (fun c => decide (c < 8)) = true ∧ sget (brK 125 245) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 245) (· == 245) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 125 245) c * sget (brK c 245) 245 = 2 := by
  decide +kernel

theorem e8_rootSl2_245 : RootSl2E8 125 245 :=
  rootSl2_of (show 8 ≤ (125 : Fin 248).val ∧ (125 : Fin 248).val < 128 by decide) e8_rootSl2L_245

theorem e8_rootSl2L_246 : suppIn (brK 126 246) (fun c => decide (c < 8)) = true ∧ sget (brK 126 246) 7 = -1 ∧
    (∀ c, c < 8 → suppIn (brK c 246) (· == 246) = true) ∧
    ∑ c ∈ Finset.range 8, sget (brK 126 246) c * sget (brK c 246) 246 = 2 := by
  decide +kernel

theorem e8_rootSl2_246 : RootSl2E8 126 246 :=
  rootSl2_of (show 8 ≤ (126 : Fin 248).val ∧ (126 : Fin 248).val < 128 by decide) e8_rootSl2L_246

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule E8sector.f V}

theorem op_comm_end8 (a b : Fin 248) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e : Fin 248, E8sector.f a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

/-- One Heisenberg step. -/
theorem heis_step8 {a b z : Fin 248} {c : ℤ} (hc : c ≠ 0)
    (hab : ∀ e : Fin 248, fZ brK a b e = if e = z then c else 0)
    (haz : ∀ e : Fin 248, fZ brK a z e = 0) (hbz : ∀ e : Fin 248, fZ brK b z e = 0) {w : V} {p : ℕ}
    (hX : (ρ.op a 0)^[p + 1] w = 0) (hY : (ρ.op b 0)^[p + 1] w = 0) :
    (ρ.op z 0)^[2 * p + 1] w = 0 := by
  have hcomm : ∀ x y : Fin 248, (∀ e : Fin 248, fZ brK x y e = 0) →
      ρ.op x 0 * ρ.op y 0 = ρ.op y 0 * ρ.op x 0 := by
    intro x y h
    rw [← sub_eq_zero, op_comm_end8]
    refine Finset.sum_eq_zero fun e _ => ?_
    change ((fZ brK x y e : ℤ) : ℂ) • _ = 0
    rw [h e, Int.cast_zero, zero_smul]
  have hXY : ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = (c : ℂ) • ρ.op z 0 := by
    rw [op_comm_end8, Finset.sum_eq_single z (fun e _ he => by
      change ((fZ brK a b e : ℤ) : ℂ) • _ = 0
      rw [hab e, if_neg he, Int.cast_zero, zero_smul]) (by simp)]
    change ((fZ brK a b z : ℤ) : ℂ) • _ = _
    rw [hab z, if_pos rfl]
  have hXZ : ρ.op a 0 * ((c : ℂ) • ρ.op z 0) = ((c : ℂ) • ρ.op z 0) * ρ.op a 0 := by
    rw [mul_smul_comm, smul_mul_assoc, hcomm a z haz]
  have hYZ : ρ.op b 0 * ((c : ℂ) • ρ.op z 0) = ((c : ℂ) • ρ.op z 0) * ρ.op b 0 := by
    rw [mul_smul_comm, smul_mul_assoc, hcomm b z hbz]
  rw [iterate_eq_pow] at hX hY
  have h := Garland.heis_nilpotent hXY hYZ hXZ hX hY
  rw [smul_pow, LinearMap.smul_apply, smul_eq_zero] at h
  rw [iterate_eq_pow]
  exact h.resolve_left (pow_ne_zero _ (by exact_mod_cast hc))

/-- `sl₂` sharpening for a root `γ` of `E₈` with `θ(h_γ) = 1`. -/
theorem root_sharpen8 {e γ : Fin 248} (hs : RootSl2E8 e γ) {w : V} {k : ℕ}
    (hR : ∀ x : Fin 248, 8 ≤ x.val ∧ x.val < 128 → ρ.op x 0 w = 0)
    (hC : ∀ h : Fin 248, h.val < 8 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w) {N : ℕ}
    (hN : (ρ.op γ 0)^[N] w = 0) : (ρ.op γ 0)^[k + 1] w = 0 := by
  obtain ⟨he, h1, h2, h3⟩ := hs
  set H : V →ₗ[ℂ] V := -(∑ c : Fin 248, E8sector.f e γ c • ρ.op c 0) with hH
  have h3C : ∀ d : Fin 248, ∑ c : Fin 248, E8sector.f e γ c * E8sector.f c γ d =
      if d = γ then (2 : ℂ) else 0 := by
    intro d
    have h3d := h3 d
    have hpt : ∀ c : Fin 248, E8sector.f e γ c * E8sector.f c γ d =
        (((if c.val < 8 then fZ brK e γ c * fZ brK c γ d else 0 : ℤ)) : ℂ) := by
      intro c
      change ((fZ brK e γ c : ℤ) : ℂ) * ((fZ brK c γ d : ℤ) : ℂ) = _
      split_ifs with hc
      · push_cast; rfl
      · have : fZ brK e γ c = 0 := by
          by_contra h0; exact hc (h1 c h0)
        rw [this]; simp
    rw [Finset.sum_congr rfl fun c _ => hpt c, ← Int.cast_sum, h3d]
    split_ifs <;> simp
  have hin : ∀ c x, ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x) =
      ∑ d : Fin 248, E8sector.f c γ d • ρ.op d 0 x := fun c x => by simpa using ρ.comm c γ 0 0 x
  refine sl2_sharpen (-ρ.op e 0) (ρ.op γ 0) H ?_ ?_ w k ?_ ?_ hN
  · intro x
    have : ρ.op e 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op e 0 x) =
        ∑ c : Fin 248, E8sector.f e γ c • ρ.op c 0 x := by simpa using ρ.comm e γ 0 0 x
    simp only [LinearMap.neg_apply, map_neg, hH, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply]
    rw [← this]; abel
  · intro x
    calc H (ρ.op γ 0 x) - ρ.op γ 0 (H x)
        = -∑ c : Fin 248, E8sector.f e γ c • (ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x)) := by
          simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
          abel
      _ = -∑ d : Fin 248, (∑ c : Fin 248, E8sector.f e γ c * E8sector.f c γ d) • ρ.op d 0 x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
      _ = (-2 : ℂ) • ρ.op γ 0 x := by
          simp only [h3C, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [neg_smul]
  · change -ρ.op e 0 w = 0
    rw [hR e he, neg_zero]
  · simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ c : Fin 248, E8sector.f e γ c • ρ.op c 0 w =
        (E8sector.f e γ c * ((k * thetaH c : ℕ) : ℂ)) • w := by
      intro c
      by_cases hc : c.val < 8
      · rw [hC c hc, smul_smul]
      · have : fZ brK e γ c = 0 := by
          by_contra h0; exact hc (h1 c h0)
        have h0 : E8sector.f e γ c = 0 := by
          change ((fZ brK e γ c : ℤ) : ℂ) = 0
          rw [this, Int.cast_zero]
        rw [h0, zero_smul, zero_mul, zero_smul]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul,
      Finset.sum_eq_single (7 : Fin 248)]
    · change -((((fZ brK e γ 7 : ℤ) : ℂ) * ((k * thetaH 7 : ℕ) : ℂ)) • w) = (k : ℂ) • w
      rw [h2]; simp [thetaH]
    · intro c _ hc
      have : thetaH c = 0 := by unfold thetaH; simp [hc]
      rw [this]; simp
    · simp

end Module

/-- **`ThetaNilG` for `E₈`**, by the Heisenberg chain `128 → 136 → 143 → 150 → 157 → 164 → 171 → 178 → 184 → 190 → 196 → 202 → 207 → 212 → 216 → 220 → 224 → 228 → 231 → 234 → 236 → 238 → 241 → 242 → 243 → 244 → 245 → 246 → 247`. -/
theorem e8_thetaNil : ThetaNilG E8sector := by
  intro k V _ _ ρ w hR hC _ hL
  have hR' : ∀ x : Fin 248, 8 ≤ x.val ∧ x.val < 128 → ρ.op x 0 w = 0 := fun x hx => hR x hx
  have hC' : ∀ h : Fin 248, h.val < 8 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w :=
    fun h hh => hC h hh
  have hL128 : (ρ.op (128 : Fin 248) 0)^[k + 1] w = 0 := by
    have := hL (128 : Fin 248) (show ((128 : Fin 248) : ℕ) ∈ [135, 134, 133, 132, 131, 130, 129, 128] by decide)
    change (ρ.op (128 : Fin 248) 0)^[k * lowExpE8 128 + 1] w = 0 at this
    simpa [lowExpE8] using this
  have hz : ∀ i : Fin 248, 129 ≤ i.val ∧ i.val < 136 → (ρ.op i 0)^[k + 1] w = 0 := by
    intro i hi
    have := hL i (show i.val ∈ [135, 134, 133, 132, 131, 130, 129, 128] by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have h0 : lowExpE8 i = 0 := by
      unfold lowExpE8
      have : i ≠ 128 := fun h => by rw [h] at hi; simp at hi
      simp [this]
    change (ρ.op i 0)^[k * lowExpE8 i + 1] w = 0 at this
    rw [h0, mul_zero, zero_add, Function.iterate_one] at this
    rw [Function.iterate_succ_apply, this]
    exact iterate_map_zero _ k
  have h136 := heis_step8 (ρ := ρ) (a := 128) (b := 129) (z := 136) (c := 1) one_ne_zero
    e8_chainZ_0.1 e8_chainZ_0.2.1 e8_chainZ_0.2.2 hL128 (hz 129 (by decide))
  have s136 := root_sharpen8 (ρ := ρ) e8_rootSl2_136 hR' hC' h136
  have h143 := heis_step8 (ρ := ρ) (a := 136) (b := 130) (z := 143) (c := -1) (by norm_num)
    e8_chainZ_1.1 e8_chainZ_1.2.1 e8_chainZ_1.2.2 s136 (hz 130 (by decide))
  have s143 := root_sharpen8 (ρ := ρ) e8_rootSl2_143 hR' hC' h143
  have h150 := heis_step8 (ρ := ρ) (a := 143) (b := 131) (z := 150) (c := -1) (by norm_num)
    e8_chainZ_2.1 e8_chainZ_2.2.1 e8_chainZ_2.2.2 s143 (hz 131 (by decide))
  have s150 := root_sharpen8 (ρ := ρ) e8_rootSl2_150 hR' hC' h150
  have h157 := heis_step8 (ρ := ρ) (a := 150) (b := 132) (z := 157) (c := -1) (by norm_num)
    e8_chainZ_3.1 e8_chainZ_3.2.1 e8_chainZ_3.2.2 s150 (hz 132 (by decide))
  have s157 := root_sharpen8 (ρ := ρ) e8_rootSl2_157 hR' hC' h157
  have h164 := heis_step8 (ρ := ρ) (a := 157) (b := 133) (z := 164) (c := -1) (by norm_num)
    e8_chainZ_4.1 e8_chainZ_4.2.1 e8_chainZ_4.2.2 s157 (hz 133 (by decide))
  have s164 := root_sharpen8 (ρ := ρ) e8_rootSl2_164 hR' hC' h164
  have h171 := heis_step8 (ρ := ρ) (a := 164) (b := 134) (z := 171) (c := -1) (by norm_num)
    e8_chainZ_5.1 e8_chainZ_5.2.1 e8_chainZ_5.2.2 s164 (hz 134 (by decide))
  have s171 := root_sharpen8 (ρ := ρ) e8_rootSl2_171 hR' hC' h171
  have h178 := heis_step8 (ρ := ρ) (a := 171) (b := 132) (z := 178) (c := 1) one_ne_zero
    e8_chainZ_6.1 e8_chainZ_6.2.1 e8_chainZ_6.2.2 s171 (hz 132 (by decide))
  have s178 := root_sharpen8 (ρ := ρ) e8_rootSl2_178 hR' hC' h178
  have h184 := heis_step8 (ρ := ρ) (a := 178) (b := 131) (z := 184) (c := 1) one_ne_zero
    e8_chainZ_7.1 e8_chainZ_7.2.1 e8_chainZ_7.2.2 s178 (hz 131 (by decide))
  have s184 := root_sharpen8 (ρ := ρ) e8_rootSl2_184 hR' hC' h184
  have h190 := heis_step8 (ρ := ρ) (a := 184) (b := 130) (z := 190) (c := 1) one_ne_zero
    e8_chainZ_8.1 e8_chainZ_8.2.1 e8_chainZ_8.2.2 s184 (hz 130 (by decide))
  have s190 := root_sharpen8 (ρ := ρ) e8_rootSl2_190 hR' hC' h190
  have h196 := heis_step8 (ρ := ρ) (a := 190) (b := 129) (z := 196) (c := 1) one_ne_zero
    e8_chainZ_9.1 e8_chainZ_9.2.1 e8_chainZ_9.2.2 s190 (hz 129 (by decide))
  have s196 := root_sharpen8 (ρ := ρ) e8_rootSl2_196 hR' hC' h196
  have h202 := heis_step8 (ρ := ρ) (a := 196) (b := 135) (z := 202) (c := -1) (by norm_num)
    e8_chainZ_10.1 e8_chainZ_10.2.1 e8_chainZ_10.2.2 s196 (hz 135 (by decide))
  have s202 := root_sharpen8 (ρ := ρ) e8_rootSl2_202 hR' hC' h202
  have h207 := heis_step8 (ρ := ρ) (a := 202) (b := 133) (z := 207) (c := -1) (by norm_num)
    e8_chainZ_11.1 e8_chainZ_11.2.1 e8_chainZ_11.2.2 s202 (hz 133 (by decide))
  have s207 := root_sharpen8 (ρ := ρ) e8_rootSl2_207 hR' hC' h207
  have h212 := heis_step8 (ρ := ρ) (a := 207) (b := 132) (z := 212) (c := 1) one_ne_zero
    e8_chainZ_12.1 e8_chainZ_12.2.1 e8_chainZ_12.2.2 s207 (hz 132 (by decide))
  have s212 := root_sharpen8 (ρ := ρ) e8_rootSl2_212 hR' hC' h212
  have h216 := heis_step8 (ρ := ρ) (a := 212) (b := 131) (z := 216) (c := 1) one_ne_zero
    e8_chainZ_13.1 e8_chainZ_13.2.1 e8_chainZ_13.2.2 s212 (hz 131 (by decide))
  have s216 := root_sharpen8 (ρ := ρ) e8_rootSl2_216 hR' hC' h216
  have h220 := heis_step8 (ρ := ρ) (a := 216) (b := 130) (z := 220) (c := 1) one_ne_zero
    e8_chainZ_14.1 e8_chainZ_14.2.1 e8_chainZ_14.2.2 s216 (hz 130 (by decide))
  have s220 := root_sharpen8 (ρ := ρ) e8_rootSl2_220 hR' hC' h220
  have h224 := heis_step8 (ρ := ρ) (a := 220) (b := 134) (z := 224) (c := 1) one_ne_zero
    e8_chainZ_15.1 e8_chainZ_15.2.1 e8_chainZ_15.2.2 s220 (hz 134 (by decide))
  have s224 := root_sharpen8 (ρ := ρ) e8_rootSl2_224 hR' hC' h224
  have h228 := heis_step8 (ρ := ρ) (a := 224) (b := 132) (z := 228) (c := 1) one_ne_zero
    e8_chainZ_16.1 e8_chainZ_16.2.1 e8_chainZ_16.2.2 s224 (hz 132 (by decide))
  have s228 := root_sharpen8 (ρ := ρ) e8_rootSl2_228 hR' hC' h228
  have h231 := heis_step8 (ρ := ρ) (a := 228) (b := 131) (z := 231) (c := 1) one_ne_zero
    e8_chainZ_17.1 e8_chainZ_17.2.1 e8_chainZ_17.2.2 s228 (hz 131 (by decide))
  have s231 := root_sharpen8 (ρ := ρ) e8_rootSl2_231 hR' hC' h231
  have h234 := heis_step8 (ρ := ρ) (a := 231) (b := 133) (z := 234) (c := 1) one_ne_zero
    e8_chainZ_18.1 e8_chainZ_18.2.1 e8_chainZ_18.2.2 s231 (hz 133 (by decide))
  have s234 := root_sharpen8 (ρ := ρ) e8_rootSl2_234 hR' hC' h234
  have h236 := heis_step8 (ρ := ρ) (a := 234) (b := 132) (z := 236) (c := 1) one_ne_zero
    e8_chainZ_19.1 e8_chainZ_19.2.1 e8_chainZ_19.2.2 s234 (hz 132 (by decide))
  have s236 := root_sharpen8 (ρ := ρ) e8_rootSl2_236 hR' hC' h236
  have h238 := heis_step8 (ρ := ρ) (a := 236) (b := 134) (z := 238) (c := -1) (by norm_num)
    e8_chainZ_20.1 e8_chainZ_20.2.1 e8_chainZ_20.2.2 s236 (hz 134 (by decide))
  have s238 := root_sharpen8 (ρ := ρ) e8_rootSl2_238 hR' hC' h238
  have h241 := heis_step8 (ρ := ρ) (a := 238) (b := 135) (z := 241) (c := 1) one_ne_zero
    e8_chainZ_21.1 e8_chainZ_21.2.1 e8_chainZ_21.2.2 s238 (hz 135 (by decide))
  have s241 := root_sharpen8 (ρ := ρ) e8_rootSl2_241 hR' hC' h241
  have h242 := heis_step8 (ρ := ρ) (a := 241) (b := 133) (z := 242) (c := 1) one_ne_zero
    e8_chainZ_22.1 e8_chainZ_22.2.1 e8_chainZ_22.2.2 s241 (hz 133 (by decide))
  have s242 := root_sharpen8 (ρ := ρ) e8_rootSl2_242 hR' hC' h242
  have h243 := heis_step8 (ρ := ρ) (a := 242) (b := 132) (z := 243) (c := -1) (by norm_num)
    e8_chainZ_23.1 e8_chainZ_23.2.1 e8_chainZ_23.2.2 s242 (hz 132 (by decide))
  have s243 := root_sharpen8 (ρ := ρ) e8_rootSl2_243 hR' hC' h243
  have h244 := heis_step8 (ρ := ρ) (a := 243) (b := 131) (z := 244) (c := -1) (by norm_num)
    e8_chainZ_24.1 e8_chainZ_24.2.1 e8_chainZ_24.2.2 s243 (hz 131 (by decide))
  have s244 := root_sharpen8 (ρ := ρ) e8_rootSl2_244 hR' hC' h244
  have h245 := heis_step8 (ρ := ρ) (a := 244) (b := 130) (z := 245) (c := -1) (by norm_num)
    e8_chainZ_25.1 e8_chainZ_25.2.1 e8_chainZ_25.2.2 s244 (hz 130 (by decide))
  have s245 := root_sharpen8 (ρ := ρ) e8_rootSl2_245 hR' hC' h245
  have h246 := heis_step8 (ρ := ρ) (a := 245) (b := 129) (z := 246) (c := -1) (by norm_num)
    e8_chainZ_26.1 e8_chainZ_26.2.1 e8_chainZ_26.2.2 s245 (hz 129 (by decide))
  have s246 := root_sharpen8 (ρ := ρ) e8_rootSl2_246 hR' hC' h246
  have h247 := heis_step8 (ρ := ρ) (a := 246) (b := 128) (z := 247) (c := -1) (by norm_num)
    e8_chainZ_27.1 e8_chainZ_27.2.1 e8_chainZ_27.2.2 s246 hL128
  rw [← iterate_eq_pow]
  exact h247

/-- **Ravinder's kernel lemma for `E₈`, unconditional.** -/
theorem e8_ravinderKernelRel' : RavinderKernelRelG E8sector.f (ravFam E8sector) (ravKw E8sector) :=
  e8_ravinderKernelRel e8_thetaNil

/-- The count of the `E₈` Demazure fusion series: `Σ_b [q^b] fusionOf (hilbSeries e8DemazureHilb) m = 248^m`,
with finite support. This is a named input until the `E₈` count lands. -/
def E8FusionCount : Prop :=
  ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e8DemazureHilb) m) = 0) ∧
    ∑ b ∈ Finset.range B, coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e8DemazureHilb) m) = (248 : ℚ) ^ m

/-- **U5 for `E₈`** from `FusionTotalBoundG E8sector`, the Demazure realizations, and the count. -/
theorem e8_fusionModuleBound_of_totalBound (hF : FusionTotalBoundG E8sector)
    (hD : ∀ n, DemazureRealizationG E8sector (ravFam E8sector)
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e8DemazureHilb) n)
    (hcount : E8FusionCount) :
    FusionModuleBoundG E8sector
      (DeligneCarrier.fusionOf (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e8DemazureHilb)) :=
  fusionModuleBoundG_of_kernel (ravFam_zero E8sector) (ravFam_step E8sector) (ravKw_deg E8sector)
    hF e8_ravinderKernelRel' hD hcount

end

end VOA.DeligneAudit.UnivG.E8K

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.E8K.e8_thetaNil
#print axioms VOA.DeligneAudit.UnivG.E8K.e8_ravinderKernelRel'
#print axioms VOA.DeligneAudit.UnivG.E8K.e8_fusionModuleBound_of_totalBound
end AxiomAudit
