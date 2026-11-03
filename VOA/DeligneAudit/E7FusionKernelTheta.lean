/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7FusionKernel
import VOA.DeligneAudit.D4FusionKernelTheta

/-!
# `ThetaNilG` for `E₇`: `f_θ^{2k+1} w = 0` by a Heisenberg chain

the `D₄` argument (`D4FusionKernelTheta`), carried to `E₇`. In the table basis, `f_{α₁} = x₇₆` is the
simple lowering vector with `θ(h) = 1`, and `x₇₀ … x₇₅` are the six simple roots orthogonal to `θ`.

The chain (found by `Notes/deligne/campaign/generators/e7_kernel_scan.py`) starts at `x₇₆` and adds orthogonal
simple roots one at a time: `76 → 82 → 88 → 93 → 99 → 103 → 108 → 112 → 116 → 119 → 122 → 125 → 127 → 129 → 130 → 131`, reaching `f_{θ-α₁} = x₁₃₁`. Each bracket is central in its pair
(`heis_step7`). Each intermediate root `γ` has `θ(h_γ) = 1`, so the `sl₂` sharpening (`root_sharpen7`, with
partner `e_γ`, where `[e_γ, f_γ] = -h_γ` and the `h₀`-coefficient is `-1`) brings `f_γ^{2k+1} w = 0` back to
`f_γ^{k+1} w = 0`. The last step is `[f₁₃₁, f₇₆] = f_θ`.

* `e7_thetaNil : ThetaNilG E7sector`.
* `e7_ravinderKernelRel'` (unconditional).
* `e7_fusionModuleBound_of_totalBound`: U5 for `E₇` from `FusionTotalBoundG E7sector`, the Demazure
  realizations, and the count of `hilbSeries e7DemazureHilb`. The count is a named input, `E7FusionCount`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E7 (E7sector thetaH lowExpE7)

noncomputable section

/-! ## Table facts for the chain -/

theorem e7_chainZ_0 :
    (∀ e : Fin 133, fZ brK 76 74 e = if e = 82 then -1 else 0) ∧
    (∀ e : Fin 133, fZ brK 76 82 e = 0) ∧ (∀ e : Fin 133, fZ brK 74 82 e = 0) := by
  decide +kernel

theorem e7_chainZ_1 :
    (∀ e : Fin 133, fZ brK 82 73 e = if e = 88 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 82 88 e = 0) ∧ (∀ e : Fin 133, fZ brK 73 88 e = 0) := by
  decide +kernel

theorem e7_chainZ_2 :
    (∀ e : Fin 133, fZ brK 88 72 e = if e = 93 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 88 93 e = 0) ∧ (∀ e : Fin 133, fZ brK 72 93 e = 0) := by
  decide +kernel

theorem e7_chainZ_3 :
    (∀ e : Fin 133, fZ brK 93 71 e = if e = 99 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 93 99 e = 0) ∧ (∀ e : Fin 133, fZ brK 71 99 e = 0) := by
  decide +kernel

theorem e7_chainZ_4 :
    (∀ e : Fin 133, fZ brK 99 70 e = if e = 103 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 99 103 e = 0) ∧ (∀ e : Fin 133, fZ brK 70 103 e = 0) := by
  decide +kernel

theorem e7_chainZ_5 :
    (∀ e : Fin 133, fZ brK 103 75 e = if e = 108 then -1 else 0) ∧
    (∀ e : Fin 133, fZ brK 103 108 e = 0) ∧ (∀ e : Fin 133, fZ brK 75 108 e = 0) := by
  decide +kernel

theorem e7_chainZ_6 :
    (∀ e : Fin 133, fZ brK 108 73 e = if e = 112 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 108 112 e = 0) ∧ (∀ e : Fin 133, fZ brK 73 112 e = 0) := by
  decide +kernel

theorem e7_chainZ_7 :
    (∀ e : Fin 133, fZ brK 112 72 e = if e = 116 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 112 116 e = 0) ∧ (∀ e : Fin 133, fZ brK 72 116 e = 0) := by
  decide +kernel

theorem e7_chainZ_8 :
    (∀ e : Fin 133, fZ brK 116 71 e = if e = 119 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 116 119 e = 0) ∧ (∀ e : Fin 133, fZ brK 71 119 e = 0) := by
  decide +kernel

theorem e7_chainZ_9 :
    (∀ e : Fin 133, fZ brK 119 74 e = if e = 122 then -1 else 0) ∧
    (∀ e : Fin 133, fZ brK 119 122 e = 0) ∧ (∀ e : Fin 133, fZ brK 74 122 e = 0) := by
  decide +kernel

theorem e7_chainZ_10 :
    (∀ e : Fin 133, fZ brK 122 73 e = if e = 125 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 122 125 e = 0) ∧ (∀ e : Fin 133, fZ brK 73 125 e = 0) := by
  decide +kernel

theorem e7_chainZ_11 :
    (∀ e : Fin 133, fZ brK 125 72 e = if e = 127 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 125 127 e = 0) ∧ (∀ e : Fin 133, fZ brK 72 127 e = 0) := by
  decide +kernel

theorem e7_chainZ_12 :
    (∀ e : Fin 133, fZ brK 127 75 e = if e = 129 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 127 129 e = 0) ∧ (∀ e : Fin 133, fZ brK 75 129 e = 0) := by
  decide +kernel

theorem e7_chainZ_13 :
    (∀ e : Fin 133, fZ brK 129 73 e = if e = 130 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 129 130 e = 0) ∧ (∀ e : Fin 133, fZ brK 73 130 e = 0) := by
  decide +kernel

theorem e7_chainZ_14 :
    (∀ e : Fin 133, fZ brK 130 74 e = if e = 131 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 130 131 e = 0) ∧ (∀ e : Fin 133, fZ brK 74 131 e = 0) := by
  decide +kernel

theorem e7_chainZ_15 :
    (∀ e : Fin 133, fZ brK 131 76 e = if e = 132 then 1 else 0) ∧
    (∀ e : Fin 133, fZ brK 131 132 e = 0) ∧ (∀ e : Fin 133, fZ brK 76 132 e = 0) := by
  decide +kernel

/-- `sl₂` data of the root `γ` with raising partner `e`, where `[e, f_γ] = -h_γ` and `θ(h_γ) = 1`. The `sl₂`
relation is summed over the Cartan part only. -/
def RootSl2E7 (e γ : Fin 133) : Prop :=
  (7 ≤ e.val ∧ e.val < 70) ∧ (∀ c : Fin 133, fZ brK e γ c ≠ 0 → c.val < 7) ∧ fZ brK e γ 0 = -1 ∧
    ∀ d : Fin 133, ∑ c : Fin 133, (if c.val < 7 then fZ brK e γ c * fZ brK c γ d else 0) =
      if d = γ then 2 else 0

theorem e7_rootSl2_82 : RootSl2E7 19 82 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_88 : RootSl2E7 25 88 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_93 : RootSl2E7 30 93 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_99 : RootSl2E7 36 99 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_103 : RootSl2E7 40 103 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_108 : RootSl2E7 45 108 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_112 : RootSl2E7 49 112 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_116 : RootSl2E7 53 116 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_119 : RootSl2E7 56 119 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_122 : RootSl2E7 59 122 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_125 : RootSl2E7 62 125 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_127 : RootSl2E7 64 127 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_129 : RootSl2E7 66 129 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_130 : RootSl2E7 67 130 := by
  unfold RootSl2E7; decide +kernel

theorem e7_rootSl2_131 : RootSl2E7 68 131 := by
  unfold RootSl2E7; decide +kernel

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule E7sector.f V}

theorem op_comm_end7 (a b : Fin 133) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e : Fin 133, E7sector.f a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

/-- One Heisenberg step. -/
theorem heis_step7 {a b z : Fin 133} {c : ℤ} (hc : c ≠ 0)
    (hab : ∀ e : Fin 133, fZ brK a b e = if e = z then c else 0)
    (haz : ∀ e : Fin 133, fZ brK a z e = 0) (hbz : ∀ e : Fin 133, fZ brK b z e = 0) {w : V} {p : ℕ}
    (hX : (ρ.op a 0)^[p + 1] w = 0) (hY : (ρ.op b 0)^[p + 1] w = 0) :
    (ρ.op z 0)^[2 * p + 1] w = 0 := by
  have hcomm : ∀ x y : Fin 133, (∀ e : Fin 133, fZ brK x y e = 0) →
      ρ.op x 0 * ρ.op y 0 = ρ.op y 0 * ρ.op x 0 := by
    intro x y h
    rw [← sub_eq_zero, op_comm_end7]
    refine Finset.sum_eq_zero fun e _ => ?_
    change ((fZ brK x y e : ℤ) : ℂ) • _ = 0
    rw [h e, Int.cast_zero, zero_smul]
  have hXY : ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = (c : ℂ) • ρ.op z 0 := by
    rw [op_comm_end7, Finset.sum_eq_single z (fun e _ he => by
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

/-- `sl₂` sharpening for a root `γ` of `E₇` with `θ(h_γ) = 1`. -/
theorem root_sharpen7 {e γ : Fin 133} (hs : RootSl2E7 e γ) {w : V} {k : ℕ}
    (hR : ∀ x : Fin 133, 7 ≤ x.val ∧ x.val < 70 → ρ.op x 0 w = 0)
    (hC : ∀ h : Fin 133, h.val < 7 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w) {N : ℕ}
    (hN : (ρ.op γ 0)^[N] w = 0) : (ρ.op γ 0)^[k + 1] w = 0 := by
  obtain ⟨he, h1, h2, h3⟩ := hs
  set H : V →ₗ[ℂ] V := -(∑ c : Fin 133, E7sector.f e γ c • ρ.op c 0) with hH
  have h3C : ∀ d : Fin 133, ∑ c : Fin 133, E7sector.f e γ c * E7sector.f c γ d =
      if d = γ then (2 : ℂ) else 0 := by
    intro d
    have h3d := h3 d
    have hpt : ∀ c : Fin 133, E7sector.f e γ c * E7sector.f c γ d =
        (((if c.val < 7 then fZ brK e γ c * fZ brK c γ d else 0 : ℤ)) : ℂ) := by
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
      ∑ d : Fin 133, E7sector.f c γ d • ρ.op d 0 x := fun c x => by simpa using ρ.comm c γ 0 0 x
  refine sl2_sharpen (-ρ.op e 0) (ρ.op γ 0) H ?_ ?_ w k ?_ ?_ hN
  · intro x
    have : ρ.op e 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op e 0 x) =
        ∑ c : Fin 133, E7sector.f e γ c • ρ.op c 0 x := by simpa using ρ.comm e γ 0 0 x
    simp only [LinearMap.neg_apply, map_neg, hH, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply]
    rw [← this]; abel
  · intro x
    calc H (ρ.op γ 0 x) - ρ.op γ 0 (H x)
        = -∑ c : Fin 133, E7sector.f e γ c • (ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x)) := by
          simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
          abel
      _ = -∑ d : Fin 133, (∑ c : Fin 133, E7sector.f e γ c * E7sector.f c γ d) • ρ.op d 0 x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
      _ = (-2 : ℂ) • ρ.op γ 0 x := by
          simp only [h3C, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [neg_smul]
  · change -ρ.op e 0 w = 0
    rw [hR e he, neg_zero]
  · simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ c : Fin 133, E7sector.f e γ c • ρ.op c 0 w =
        (E7sector.f e γ c * ((k * thetaH c : ℕ) : ℂ)) • w := by
      intro c
      by_cases hc : c.val < 7
      · rw [hC c hc, smul_smul]
      · have : fZ brK e γ c = 0 := by
          by_contra h0; exact hc (h1 c h0)
        have h0 : E7sector.f e γ c = 0 := by
          change ((fZ brK e γ c : ℤ) : ℂ) = 0
          rw [this, Int.cast_zero]
        rw [h0, zero_smul, zero_mul, zero_smul]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul,
      Finset.sum_eq_single (0 : Fin 133)]
    · change -((((fZ brK e γ 0 : ℤ) : ℂ) * ((k * thetaH 0 : ℕ) : ℂ)) • w) = (k : ℂ) • w
      rw [h2]; simp [thetaH]
    · intro c _ hc
      have : thetaH c = 0 := by unfold thetaH; simp [hc]
      rw [this]; simp
    · simp

end Module

/-- **`ThetaNilG` for `E₇`**, by the Heisenberg chain `76 → 82 → 88 → 93 → 99 → 103 → 108 → 112 → 116 → 119 → 122 → 125 → 127 → 129 → 130 → 131 → 132`. -/
theorem e7_thetaNil : ThetaNilG E7sector := by
  intro k V _ _ ρ w hR hC _ hL
  have hR' : ∀ x : Fin 133, 7 ≤ x.val ∧ x.val < 70 → ρ.op x 0 w = 0 := fun x hx => hR x hx
  have hC' : ∀ h : Fin 133, h.val < 7 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w :=
    fun h hh => hC h hh
  have hL76 : (ρ.op (76 : Fin 133) 0)^[k + 1] w = 0 := by
    have := hL (76 : Fin 133) (show ((76 : Fin 133) : ℕ) ∈ [76, 75, 74, 73, 72, 71, 70] by decide)
    change (ρ.op (76 : Fin 133) 0)^[k * lowExpE7 76 + 1] w = 0 at this
    simpa [lowExpE7] using this
  have hz : ∀ i : Fin 133, 70 ≤ i.val ∧ i.val < 76 → (ρ.op i 0)^[k + 1] w = 0 := by
    intro i hi
    have := hL i (show i.val ∈ [76, 75, 74, 73, 72, 71, 70] by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have h0 : lowExpE7 i = 0 := by
      unfold lowExpE7
      have : i ≠ 76 := fun h => by rw [h] at hi; simp at hi
      simp [this]
    change (ρ.op i 0)^[k * lowExpE7 i + 1] w = 0 at this
    rw [h0, mul_zero, zero_add, Function.iterate_one] at this
    rw [Function.iterate_succ_apply, this]
    exact iterate_map_zero _ k
  have h82 := heis_step7 (ρ := ρ) (a := 76) (b := 74) (z := 82) (c := -1) (by norm_num)
    e7_chainZ_0.1 e7_chainZ_0.2.1 e7_chainZ_0.2.2 hL76 (hz 74 (by decide))
  have s82 := root_sharpen7 (ρ := ρ) e7_rootSl2_82 hR' hC' h82
  have h88 := heis_step7 (ρ := ρ) (a := 82) (b := 73) (z := 88) (c := 1) one_ne_zero
    e7_chainZ_1.1 e7_chainZ_1.2.1 e7_chainZ_1.2.2 s82 (hz 73 (by decide))
  have s88 := root_sharpen7 (ρ := ρ) e7_rootSl2_88 hR' hC' h88
  have h93 := heis_step7 (ρ := ρ) (a := 88) (b := 72) (z := 93) (c := 1) one_ne_zero
    e7_chainZ_2.1 e7_chainZ_2.2.1 e7_chainZ_2.2.2 s88 (hz 72 (by decide))
  have s93 := root_sharpen7 (ρ := ρ) e7_rootSl2_93 hR' hC' h93
  have h99 := heis_step7 (ρ := ρ) (a := 93) (b := 71) (z := 99) (c := 1) one_ne_zero
    e7_chainZ_3.1 e7_chainZ_3.2.1 e7_chainZ_3.2.2 s93 (hz 71 (by decide))
  have s99 := root_sharpen7 (ρ := ρ) e7_rootSl2_99 hR' hC' h99
  have h103 := heis_step7 (ρ := ρ) (a := 99) (b := 70) (z := 103) (c := 1) one_ne_zero
    e7_chainZ_4.1 e7_chainZ_4.2.1 e7_chainZ_4.2.2 s99 (hz 70 (by decide))
  have s103 := root_sharpen7 (ρ := ρ) e7_rootSl2_103 hR' hC' h103
  have h108 := heis_step7 (ρ := ρ) (a := 103) (b := 75) (z := 108) (c := -1) (by norm_num)
    e7_chainZ_5.1 e7_chainZ_5.2.1 e7_chainZ_5.2.2 s103 (hz 75 (by decide))
  have s108 := root_sharpen7 (ρ := ρ) e7_rootSl2_108 hR' hC' h108
  have h112 := heis_step7 (ρ := ρ) (a := 108) (b := 73) (z := 112) (c := 1) one_ne_zero
    e7_chainZ_6.1 e7_chainZ_6.2.1 e7_chainZ_6.2.2 s108 (hz 73 (by decide))
  have s112 := root_sharpen7 (ρ := ρ) e7_rootSl2_112 hR' hC' h112
  have h116 := heis_step7 (ρ := ρ) (a := 112) (b := 72) (z := 116) (c := 1) one_ne_zero
    e7_chainZ_7.1 e7_chainZ_7.2.1 e7_chainZ_7.2.2 s112 (hz 72 (by decide))
  have s116 := root_sharpen7 (ρ := ρ) e7_rootSl2_116 hR' hC' h116
  have h119 := heis_step7 (ρ := ρ) (a := 116) (b := 71) (z := 119) (c := 1) one_ne_zero
    e7_chainZ_8.1 e7_chainZ_8.2.1 e7_chainZ_8.2.2 s116 (hz 71 (by decide))
  have s119 := root_sharpen7 (ρ := ρ) e7_rootSl2_119 hR' hC' h119
  have h122 := heis_step7 (ρ := ρ) (a := 119) (b := 74) (z := 122) (c := -1) (by norm_num)
    e7_chainZ_9.1 e7_chainZ_9.2.1 e7_chainZ_9.2.2 s119 (hz 74 (by decide))
  have s122 := root_sharpen7 (ρ := ρ) e7_rootSl2_122 hR' hC' h122
  have h125 := heis_step7 (ρ := ρ) (a := 122) (b := 73) (z := 125) (c := 1) one_ne_zero
    e7_chainZ_10.1 e7_chainZ_10.2.1 e7_chainZ_10.2.2 s122 (hz 73 (by decide))
  have s125 := root_sharpen7 (ρ := ρ) e7_rootSl2_125 hR' hC' h125
  have h127 := heis_step7 (ρ := ρ) (a := 125) (b := 72) (z := 127) (c := 1) one_ne_zero
    e7_chainZ_11.1 e7_chainZ_11.2.1 e7_chainZ_11.2.2 s125 (hz 72 (by decide))
  have s127 := root_sharpen7 (ρ := ρ) e7_rootSl2_127 hR' hC' h127
  have h129 := heis_step7 (ρ := ρ) (a := 127) (b := 75) (z := 129) (c := 1) one_ne_zero
    e7_chainZ_12.1 e7_chainZ_12.2.1 e7_chainZ_12.2.2 s127 (hz 75 (by decide))
  have s129 := root_sharpen7 (ρ := ρ) e7_rootSl2_129 hR' hC' h129
  have h130 := heis_step7 (ρ := ρ) (a := 129) (b := 73) (z := 130) (c := 1) one_ne_zero
    e7_chainZ_13.1 e7_chainZ_13.2.1 e7_chainZ_13.2.2 s129 (hz 73 (by decide))
  have s130 := root_sharpen7 (ρ := ρ) e7_rootSl2_130 hR' hC' h130
  have h131 := heis_step7 (ρ := ρ) (a := 130) (b := 74) (z := 131) (c := 1) one_ne_zero
    e7_chainZ_14.1 e7_chainZ_14.2.1 e7_chainZ_14.2.2 s130 (hz 74 (by decide))
  have s131 := root_sharpen7 (ρ := ρ) e7_rootSl2_131 hR' hC' h131
  have h132 := heis_step7 (ρ := ρ) (a := 131) (b := 76) (z := 132) (c := 1) one_ne_zero
    e7_chainZ_15.1 e7_chainZ_15.2.1 e7_chainZ_15.2.2 s131 hL76
  rw [← iterate_eq_pow]
  exact h132

/-- **Ravinder's kernel lemma for `E₇`, unconditional.** -/
theorem e7_ravinderKernelRel' : RavinderKernelRelG E7sector.f (ravFam E7sector) (ravKw E7sector) :=
  e7_ravinderKernelRel e7_thetaNil

/-- The count of the `E₇` Demazure fusion series: `Σ_b [q^b] fusionOf (hilbSeries e7DemazureHilb) m = 133^m`,
with finite support. This is a named input; the unclamped `E₇` count is in progress. -/
def E7FusionCount : Prop :=
  ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e7DemazureHilb) m) = 0) ∧
    ∑ b ∈ Finset.range B, coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e7DemazureHilb) m) = (133 : ℚ) ^ m

/-- **U5 for `E₇`** from `FusionTotalBoundG E7sector`, the Demazure realizations, and the count. -/
theorem e7_fusionModuleBound_of_totalBound (hF : FusionTotalBoundG E7sector)
    (hD : ∀ n, DemazureRealizationG E7sector (ravFam E7sector)
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e7DemazureHilb) n)
    (hcount : E7FusionCount) :
    FusionModuleBoundG E7sector
      (DeligneCarrier.fusionOf (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e7DemazureHilb)) :=
  fusionModuleBoundG_of_kernel (ravFam_zero E7sector) (ravFam_step E7sector) (ravKw_deg E7sector)
    hF e7_ravinderKernelRel' hD hcount

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.e7_thetaNil
#print axioms VOA.DeligneAudit.UnivG.e7_ravinderKernelRel'
#print axioms VOA.DeligneAudit.UnivG.e7_fusionModuleBound_of_totalBound
end AxiomAudit
