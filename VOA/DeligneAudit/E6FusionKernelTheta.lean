import VOA.DeligneAudit.E6FusionKernelThetaCheck00
import VOA.DeligneAudit.E6FusionKernelThetaCheck01
import VOA.DeligneAudit.E6FusionKernelThetaCheck02
import VOA.DeligneAudit.E6FusionKernelThetaCheck03
import VOA.DeligneAudit.E6FusionKernelThetaCheck04
import VOA.DeligneAudit.E6FusionKernelThetaCheck05
import VOA.DeligneAudit.E6FusionKernelThetaCheck06
import VOA.DeligneAudit.E6FusionKernelThetaCheck07
import VOA.DeligneAudit.E6FusionKernelThetaCheck08
import VOA.DeligneAudit.E6FusionKernelThetaCheck09
import VOA.DeligneAudit.E6FusionKernelThetaCheck10
import VOA.DeligneAudit.E6FusionKernelThetaCheck11
import VOA.DeligneAudit.E6FusionKernelThetaCheck12
import VOA.DeligneAudit.E6FusionKernelThetaCheck13
import VOA.DeligneAudit.E6FusionKernelThetaCheck14
import VOA.DeligneAudit.E6FusionKernelThetaCheck15
import VOA.DeligneAudit.E6FusionKernelThetaCheck16
import VOA.DeligneAudit.E6FusionKernelThetaCheck17
import VOA.DeligneAudit.E6FusionKernelThetaCheck18
/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6FusionKernel
import VOA.DeligneAudit.D4FusionKernelTheta

/-!
# `ThetaNilG` for `E₆`: `f_θ^{2k+1} w = 0` by a Heisenberg chain

the `D₄` argument, carried to `E₆` exactly as for `E₇` (`E7FusionKernelTheta`). In the table basis,
`f_{α₂} = x₄₆` is the simple lowering vector with `θ(h₁) = 1`, and `x₄₂ … x₄₅` and `x₄₇` are the five simple
roots orthogonal to `θ`.

The chain (found by `Notes/deligne/campaign/generators/e6_kernel_scan.py`) is `46 → 51 → 55 → 59 → 63 → 67 → 70 → 73 → 75 → 76`, reaching
`f_{θ-α₂} = x₇₆`. Each step is followed by `sl₂` sharpening (`root_sharpen6`; the `h₁`-coefficient of
`[e_γ, f_γ]` is `-1`). The last step is `[f₇₆, f₄₆] = f_θ`.

* `e6_thetaNil : ThetaNilG E6sector`, unconditional.
* `e6_ravinderKernelRel'`.
* `e6_fusionModuleBound_of_totalBound`: U5 for `E₆` from `FusionTotalBoundG E6sector`, the Demazure
  realizations, and the named count `E6FusionCount`.

The declarations are in the namespace `UnivG.E6K`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.E6K

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (E6sector thetaH lowExpE6)

noncomputable section

/-! ## Table facts for the chain -/

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule E6sector.f V}

theorem op_comm_end6 (a b : Fin 78) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e : Fin 78, E6sector.f a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

/-- One Heisenberg step. -/
theorem heis_step6 {a b z : Fin 78} {c : ℤ} (hc : c ≠ 0)
    (hab : ∀ e : Fin 78, fZ brK a b e = if e = z then c else 0)
    (haz : ∀ e : Fin 78, fZ brK a z e = 0) (hbz : ∀ e : Fin 78, fZ brK b z e = 0) {w : V} {p : ℕ}
    (hX : (ρ.op a 0)^[p + 1] w = 0) (hY : (ρ.op b 0)^[p + 1] w = 0) :
    (ρ.op z 0)^[2 * p + 1] w = 0 := by
  have hcomm : ∀ x y : Fin 78, (∀ e : Fin 78, fZ brK x y e = 0) →
      ρ.op x 0 * ρ.op y 0 = ρ.op y 0 * ρ.op x 0 := by
    intro x y h
    rw [← sub_eq_zero, op_comm_end6]
    refine Finset.sum_eq_zero fun e _ => ?_
    change ((fZ brK x y e : ℤ) : ℂ) • _ = 0
    rw [h e, Int.cast_zero, zero_smul]
  have hXY : ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = (c : ℂ) • ρ.op z 0 := by
    rw [op_comm_end6, Finset.sum_eq_single z (fun e _ he => by
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

/-- `sl₂` sharpening for a root `γ` of `E₆` with `θ(h_γ) = 1`. -/
theorem root_sharpen6 {e γ : Fin 78} (hs : RootSl2E6 e γ) {w : V} {k : ℕ}
    (hR : ∀ x : Fin 78, 6 ≤ x.val ∧ x.val < 42 → ρ.op x 0 w = 0)
    (hC : ∀ h : Fin 78, h.val < 6 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w) {N : ℕ}
    (hN : (ρ.op γ 0)^[N] w = 0) : (ρ.op γ 0)^[k + 1] w = 0 := by
  obtain ⟨he, h1, h2, h3⟩ := hs
  set H : V →ₗ[ℂ] V := -(∑ c : Fin 78, E6sector.f e γ c • ρ.op c 0) with hH
  have h3C : ∀ d : Fin 78, ∑ c : Fin 78, E6sector.f e γ c * E6sector.f c γ d =
      if d = γ then (2 : ℂ) else 0 := by
    intro d
    have h3d := h3 d
    have hpt : ∀ c : Fin 78, E6sector.f e γ c * E6sector.f c γ d =
        (((if c.val < 6 then fZ brK e γ c * fZ brK c γ d else 0 : ℤ)) : ℂ) := by
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
      ∑ d : Fin 78, E6sector.f c γ d • ρ.op d 0 x := fun c x => by simpa using ρ.comm c γ 0 0 x
  refine sl2_sharpen (-ρ.op e 0) (ρ.op γ 0) H ?_ ?_ w k ?_ ?_ hN
  · intro x
    have : ρ.op e 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op e 0 x) =
        ∑ c : Fin 78, E6sector.f e γ c • ρ.op c 0 x := by simpa using ρ.comm e γ 0 0 x
    simp only [LinearMap.neg_apply, map_neg, hH, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply]
    rw [← this]; abel
  · intro x
    calc H (ρ.op γ 0 x) - ρ.op γ 0 (H x)
        = -∑ c : Fin 78, E6sector.f e γ c • (ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x)) := by
          simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
          abel
      _ = -∑ d : Fin 78, (∑ c : Fin 78, E6sector.f e γ c * E6sector.f c γ d) • ρ.op d 0 x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
      _ = (-2 : ℂ) • ρ.op γ 0 x := by
          simp only [h3C, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [neg_smul]
  · change -ρ.op e 0 w = 0
    rw [hR e he, neg_zero]
  · simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ c : Fin 78, E6sector.f e γ c • ρ.op c 0 w =
        (E6sector.f e γ c * ((k * thetaH c : ℕ) : ℂ)) • w := by
      intro c
      by_cases hc : c.val < 6
      · rw [hC c hc, smul_smul]
      · have : fZ brK e γ c = 0 := by
          by_contra h0; exact hc (h1 c h0)
        have h0 : E6sector.f e γ c = 0 := by
          change ((fZ brK e γ c : ℤ) : ℂ) = 0
          rw [this, Int.cast_zero]
        rw [h0, zero_smul, zero_mul, zero_smul]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul,
      Finset.sum_eq_single (1 : Fin 78)]
    · change -((((fZ brK e γ 1 : ℤ) : ℂ) * ((k * thetaH 1 : ℕ) : ℂ)) • w) = (k : ℂ) • w
      rw [h2]; simp [thetaH]
    · intro c _ hc
      have : thetaH c = 0 := by unfold thetaH; simp [hc]
      rw [this]; simp
    · simp

end Module

/-- **`ThetaNilG` for `E₆`**, by the Heisenberg chain `46 → 51 → 55 → 59 → 63 → 67 → 70 → 73 → 75 → 76 → 77`. -/
theorem e6_thetaNil : ThetaNilG E6sector := by
  intro k V _ _ ρ w hR hC _ hL
  have hR' : ∀ x : Fin 78, 6 ≤ x.val ∧ x.val < 42 → ρ.op x 0 w = 0 := fun x hx => hR x hx
  have hC' : ∀ h : Fin 78, h.val < 6 → ρ.op h 0 w = ((k * thetaH h : ℕ) : ℂ) • w :=
    fun h hh => hC h hh
  have hL46 : (ρ.op (46 : Fin 78) 0)^[k + 1] w = 0 := by
    have := hL (46 : Fin 78) (show ((46 : Fin 78) : ℕ) ∈ [47, 46, 45, 44, 43, 42] by decide)
    change (ρ.op (46 : Fin 78) 0)^[k * lowExpE6 46 + 1] w = 0 at this
    simpa [lowExpE6] using this
  have hz : ∀ i : Fin 78, (42 ≤ i.val ∧ i.val < 48 ∧ i.val ≠ 46) → (ρ.op i 0)^[k + 1] w = 0 := by
    intro i hi
    have := hL i (show i.val ∈ [47, 46, 45, 44, 43, 42] by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)
    have h0 : lowExpE6 i = 0 := by
      unfold lowExpE6
      have : i ≠ 46 := fun h => by rw [h] at hi; simp at hi
      simp [this]
    change (ρ.op i 0)^[k * lowExpE6 i + 1] w = 0 at this
    rw [h0, mul_zero, zero_add, Function.iterate_one] at this
    rw [Function.iterate_succ_apply, this]
    exact iterate_map_zero _ k
  have h51 := heis_step6 (ρ := ρ) (a := 46) (b := 44) (z := 51) (c := -1) (by norm_num)
    e6_chainZ_0.1 e6_chainZ_0.2.1 e6_chainZ_0.2.2 hL46 (hz 44 (by decide))
  have s51 := root_sharpen6 (ρ := ρ) e6_rootSl2_51 hR' hC' h51
  have h55 := heis_step6 (ρ := ρ) (a := 51) (b := 43) (z := 55) (c := 1) one_ne_zero
    e6_chainZ_1.1 e6_chainZ_1.2.1 e6_chainZ_1.2.2 s51 (hz 43 (by decide))
  have s55 := root_sharpen6 (ρ := ρ) e6_rootSl2_55 hR' hC' h55
  have h59 := heis_step6 (ρ := ρ) (a := 55) (b := 42) (z := 59) (c := 1) one_ne_zero
    e6_chainZ_2.1 e6_chainZ_2.2.1 e6_chainZ_2.2.2 s55 (hz 42 (by decide))
  have s59 := root_sharpen6 (ρ := ρ) e6_rootSl2_59 hR' hC' h59
  have h63 := heis_step6 (ρ := ρ) (a := 59) (b := 45) (z := 63) (c := -1) (by norm_num)
    e6_chainZ_3.1 e6_chainZ_3.2.1 e6_chainZ_3.2.2 s59 (hz 45 (by decide))
  have s63 := root_sharpen6 (ρ := ρ) e6_rootSl2_63 hR' hC' h63
  have h67 := heis_step6 (ρ := ρ) (a := 63) (b := 44) (z := 67) (c := 1) one_ne_zero
    e6_chainZ_4.1 e6_chainZ_4.2.1 e6_chainZ_4.2.2 s63 (hz 44 (by decide))
  have s67 := root_sharpen6 (ρ := ρ) e6_rootSl2_67 hR' hC' h67
  have h70 := heis_step6 (ρ := ρ) (a := 67) (b := 43) (z := 70) (c := 1) one_ne_zero
    e6_chainZ_5.1 e6_chainZ_5.2.1 e6_chainZ_5.2.2 s67 (hz 43 (by decide))
  have s70 := root_sharpen6 (ρ := ρ) e6_rootSl2_70 hR' hC' h70
  have h73 := heis_step6 (ρ := ρ) (a := 70) (b := 47) (z := 73) (c := -1) (by norm_num)
    e6_chainZ_6.1 e6_chainZ_6.2.1 e6_chainZ_6.2.2 s70 (hz 47 (by decide))
  have s73 := root_sharpen6 (ρ := ρ) e6_rootSl2_73 hR' hC' h73
  have h75 := heis_step6 (ρ := ρ) (a := 73) (b := 45) (z := 75) (c := -1) (by norm_num)
    e6_chainZ_7.1 e6_chainZ_7.2.1 e6_chainZ_7.2.2 s73 (hz 45 (by decide))
  have s75 := root_sharpen6 (ρ := ρ) e6_rootSl2_75 hR' hC' h75
  have h76 := heis_step6 (ρ := ρ) (a := 75) (b := 44) (z := 76) (c := 1) one_ne_zero
    e6_chainZ_8.1 e6_chainZ_8.2.1 e6_chainZ_8.2.2 s75 (hz 44 (by decide))
  have s76 := root_sharpen6 (ρ := ρ) e6_rootSl2_76 hR' hC' h76
  have h77 := heis_step6 (ρ := ρ) (a := 76) (b := 46) (z := 77) (c := 1) one_ne_zero
    e6_chainZ_9.1 e6_chainZ_9.2.1 e6_chainZ_9.2.2 s76 hL46
  rw [← iterate_eq_pow]
  exact h77

/-- **Ravinder's kernel lemma for `E₆`, unconditional.** -/
theorem e6_ravinderKernelRel' : RavinderKernelRelG E6sector.f (ravFam E6sector) (ravKw E6sector) :=
  e6_ravinderKernelRel e6_thetaNil

/-- The count of the `E₆` Demazure fusion series: `Σ_b [q^b] fusionOf (hilbSeries e6DemazureHilb) m = 78^m`,
with finite support. This is a named input until the `E₆` count lands. -/
def E6FusionCount : Prop :=
  ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb) m) = 0) ∧
    ∑ b ∈ Finset.range B, coeff b (DeligneCarrier.fusionOf
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb) m) = (78 : ℚ) ^ m

/-- **U5 for `E₆`** from `FusionTotalBoundG E6sector`, the Demazure realizations, and the count. -/
theorem e6_fusionModuleBound_of_totalBound (hF : FusionTotalBoundG E6sector)
    (hD : ∀ n, DemazureRealizationG E6sector (ravFam E6sector)
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb) n)
    (hcount : E6FusionCount) :
    FusionModuleBoundG E6sector
      (DeligneCarrier.fusionOf (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb)) :=
  fusionModuleBoundG_of_kernel (ravFam_zero E6sector) (ravFam_step E6sector) (ravKw_deg E6sector)
    hF e6_ravinderKernelRel' hD hcount

end

end VOA.DeligneAudit.UnivG.E6K

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.E6K.e6_thetaNil
#print axioms VOA.DeligneAudit.UnivG.E6K.e6_ravinderKernelRel'
#print axioms VOA.DeligneAudit.UnivG.E6K.e6_fusionModuleBound_of_totalBound
end AxiomAudit
