/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2FusionKernel

/-!
# `ThetaNilG` for `G₂` and the `G₂` case from the named fusion inputs

`x₄ = f_{α₁}` (short, `θ(h_{α₁}) = 0`, so `x₄ w = 0`), `x₁₃ = f_{α₂}` (long, `x₁₃^{k+1} w = 0`):

`[x₄, x₁₃] = x₁₁`, `[x₄, x₁₁] = 2 x₈`, `[x₄, x₈] = 3 x₃`, `[x₄, x₃] = 0`,

so `(ad x₄)^3 x₁₃ = 6 x₃` and `(ad x₄)^4 x₁₃ = 0`; `nil_of_ad` gives `x₃^{k+1} w = 0`. The long
roots form an `A₂`: `[x₁₃, x₃] = x₁₂ = f_θ`, central in `⟨x₁₃, x₃⟩`, and the `heis_nilpotent`
gives `f_θ^{2k+1} w = 0`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.G2 Finset

noncomputable section

theorem g2_chainZ :
    (∀ e : Fin 14, fZ br 4 13 e = if e = 11 then 1 else 0) ∧
    (∀ e : Fin 14, fZ br 4 11 e = if e = 8 then 2 else 0) ∧
    (∀ e : Fin 14, fZ br 4 8 e = if e = 3 then 3 else 0) ∧
    (∀ e : Fin 14, fZ br 4 3 e = 0) ∧
    (∀ e : Fin 14, fZ br 13 3 e = if e = 12 then 1 else 0) ∧
    (∀ e : Fin 14, fZ br 13 12 e = 0) ∧ (∀ e : Fin 14, fZ br 3 12 e = 0) := by
  decide +kernel

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule fG2 V}

theorem op_comm_g2 (a b : Fin 14) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e, fG2 a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

theorem sum_single_g2 {a b z : Fin 14} {c : ℤ}
    (h : ∀ e : Fin 14, fZ br a b e = if e = z then c else 0) :
    ∑ e, fG2 a b e • ρ.op e 0 = (c : ℂ) • ρ.op z 0 := by
  rw [Finset.sum_eq_single z (fun e _ he => by rw [fG2_eq, h e, if_neg he, Int.cast_zero,
    zero_smul]) (by simp), fG2_eq, h z, if_pos rfl]

theorem sum_zero_g2 {a b : Fin 14} (h : ∀ e : Fin 14, fZ br a b e = 0) :
    ∑ e, fG2 a b e • ρ.op e 0 = 0 :=
  Finset.sum_eq_zero fun e _ => by rw [fG2_eq, h e, Int.cast_zero, zero_smul]

end Module

/-- **`ThetaNilG` for `G₂`.** -/
theorem g2_thetaNil : ThetaNilG G2sector := by
  intro k V _ _ ρ w _ _ _ hL
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := g2_chainZ
  have hA : ρ.op (4 : Fin 14) 0 w = 0 := by
    have := hL (4 : Fin 14) (show ((4 : Fin 14) : ℕ) ∈ ([4, 13] : List ℕ) by decide)
    change (ρ.op (4 : Fin 14) 0)^[k * lowExpS 4 + 1] w = 0 at this
    simpa [lowExpS] using this
  have hX : ((ρ.op (13 : Fin 14) 0) ^ (k + 1)) w = 0 := by
    have := hL (13 : Fin 14) (show ((13 : Fin 14) : ℕ) ∈ ([4, 13] : List ℕ) by decide)
    change (ρ.op (13 : Fin 14) 0)^[k * lowExpS 13 + 1] w = 0 at this
    rw [Module.End.pow_apply]
    simpa [lowExpS] using this
  set A := ρ.op (4 : Fin 14) 0 with hAdef
  have hstep : ∀ x : Fin 14, adL A (ρ.op x 0) = ∑ e, fG2 4 x e • ρ.op e 0 :=
    fun x => op_comm_g2 (ρ := ρ) 4 x
  have h3 : (adL A)^[3] (ρ.op (13 : Fin 14) 0) = (6 : ℂ) • ρ.op (3 : Fin 14) 0 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hstep, sum_single_g2 c1, map_smul, hstep, sum_single_g2 c2, smul_smul, map_smul, hstep,
      sum_single_g2 c3, smul_smul]
    norm_num
  have h4 : (adL A)^[3 + 1] (ρ.op (13 : Fin 14) 0) = 0 := by
    rw [Function.iterate_succ_apply', h3, map_smul, hstep, sum_zero_g2 c4, smul_zero]
  have hY := nil_of_ad A hA h4 hX
  rw [h3, smul_pow, LinearMap.smul_apply, smul_eq_zero] at hY
  have hY' : ((ρ.op (3 : Fin 14) 0) ^ (k + 1)) w = 0 :=
    hY.resolve_left (pow_ne_zero _ (by norm_num))
  have hXY : ρ.op (13 : Fin 14) 0 * ρ.op (3 : Fin 14) 0 - ρ.op (3 : Fin 14) 0 * ρ.op (13 : Fin 14) 0
      = ρ.op (12 : Fin 14) 0 := by
    rw [op_comm_g2, sum_single_g2 c5]; simp
  have hXZ : ρ.op (13 : Fin 14) 0 * ρ.op (12 : Fin 14) 0 =
      ρ.op (12 : Fin 14) 0 * ρ.op (13 : Fin 14) 0 := by
    rw [← sub_eq_zero, op_comm_g2, sum_zero_g2 c6]
  have hYZ : ρ.op (3 : Fin 14) 0 * ρ.op (12 : Fin 14) 0 =
      ρ.op (12 : Fin 14) 0 * ρ.op (3 : Fin 14) 0 := by
    rw [← sub_eq_zero, op_comm_g2, sum_zero_g2 c7]
  exact Garland.heis_nilpotent hXY hYZ hXZ hX hY'

/-- **Ravinder's kernel lemma for `G₂`, unconditional.** -/
theorem g2_ravinderKernelRel : RavinderKernelRelG G2sector.f (ravFam G2sector) (ravKw G2sector) :=
  ravinderKernelRelG_of_table G2sector g2KernelTable g2_thetaNil

/-- **U5 for `G₂`** (`FusionModuleBoundG G2sector g2FusionFZ`) from `FusionTotalBoundG G2sector`
and the `G₂` Demazure realizations; the count is proved (`g2FusionFZ_count_holds`). -/
theorem g2_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG G2sector)
    (hD : ∀ n, DemazureRealizationG G2sector (ravFam G2sector) DeligneCarrier.g2HilbSeriesZ n) :
    FusionModuleBoundG G2sector DeligneCarrier.g2FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero G2sector) (ravFam_step G2sector) (ravKw_deg G2sector)
    hF g2_ravinderKernelRel hD DeligneCarrier.g2FusionFZ_count_holds

/-- **The `G₂` case from `FusionTotalBoundG`, the Demazure realizations and `G2StarBound`.** -/
theorem g2_classicallyFree_of_totalBound (hF : FusionTotalBoundG G2sector)
    (hD : ∀ n, DemazureRealizationG G2sector (ravFam G2sector) DeligneCarrier.g2HilbSeriesZ n)
    (hB : DeligneCharacter.G2StarBound) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .G2 G2Lie.g2W
        G2Lie.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass G2Lie.g2W 1 ⟨G2Lie.explicitPresentation.gen i,
          G2Lie.explicitPresentation.gen_weight_one i⟩).toRingHom =
        G2Lie.explicitPresentation.ideal := by
  have hU5 := g2_fusionModuleBoundZ_of_totalBound hF hD
  exact G2Lie.g2_classicallyFree_concrete ((DeligneCarrier.g2FusionF_eq_Z hU5) ▸ hU5) hB

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.g2_thetaNil
#print axioms VOA.DeligneAudit.UnivG.g2_ravinderKernelRel
#print axioms VOA.DeligneAudit.UnivG.g2_fusionModuleBoundZ_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.g2_classicallyFree_of_totalBound
end AxiomAudit
