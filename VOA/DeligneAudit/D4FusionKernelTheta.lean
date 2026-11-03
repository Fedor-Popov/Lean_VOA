/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernel

/-!
# `ThetaNilG` for `D₄`: `f_θ^{2k+1} w = 0` by a Heisenberg chain

`θ = α₁ + 2α₂ + α₃ + α₄`. In the table basis (`f_{α₂} = x₁₈`, the orthogonal simple roots
`x₁₆, x₁₇, x₁₉`):

`[f₁₈, f₁₆] = -f₂₀`, `[f₂₀, f₁₇] = f₂₃`, `[f₂₃, f₁₉] = -f₂₆`, `[f₂₆, f₁₈] = -f₂₇ = -f_θ`,

each bracket central in the pair (`heis_step`). From `f₁₈^{k+1} w = 0` and
`f₁₆ w = f₁₇ w = f₁₉ w = 0`, the `heis_nilpotent` gives `f_γ^{2k+1} w = 0` at each step. The
`sl₂` sharpening `sl2_sharpen` (a highest-weight vector of weight `k` on which `F` is nilpotent
satisfies `F^{k+1} u = 0`) brings it back to `f_γ^{k+1} w = 0`, for `γ = 20, 23, 26`
(`root_sharpen`, with `e_γ = 8, 11, 14`). The last step gives `f_θ^{2k+1} w = 0`.

`d4_thetaNil : ThetaNilG D4sector`; `d4_ravinderKernelRel'` (unconditional), and
`d4_fusionModuleBoundZ_of_totalBound` / `d4_classicallyFree_of_totalBound`: `D₄` from
`FusionTotalBoundG D4sector` and the Demazure realizations, matching `A₂`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-! ## Generic `sl₂` sharpening -/

section SL2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A highest-weight vector of weight `k` on which `F` is nilpotent satisfies `F^{k+1} u = 0`. -/
theorem sl2_sharpen (E F H : V →ₗ[ℂ] V) (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x) (u : V) (k : ℕ) (hE : E u = 0)
    (hH : H u = (k : ℂ) • u) {N : ℕ} (hN : F^[N] u = 0) : F^[k + 1] u = 0 := by
  set v0 := F^[k + 1] u with hv0
  have hEv : E v0 = 0 := by
    rw [hv0, sl2_E_Fpow E F H hEF hHF u _ hE hH k]
    simp
  have hHv : H v0 = ((k : ℂ) - 2 * ((k + 1 : ℕ) : ℂ)) • v0 := sl2_H_Fpow F H hHF u _ hH (k + 1)
  have hNv : F^[N] v0 = 0 := by
    rw [hv0, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hN]
    exact iterate_map_zero F (k + 1)
  have key : ∀ m j, j + m = N → F^[j] v0 = 0 := by
    intro m
    induction m with
    | zero => intro j hj; rw [show j = N by omega]; exact hNv
    | succ m ih =>
        intro j hj
        have h1 := ih (j + 1) (by omega)
        have h2 := sl2_E_Fpow E F H hEF hHF v0 _ hEv hHv j
        rw [h1, map_zero, eq_comm, smul_eq_zero] at h2
        refine h2.resolve_left ?_
        push_cast
        refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero j) ?_
        intro h0
        have := congrArg Complex.re h0
        simp at this
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
  exact key N 0 (by omega)

end SL2

/-! ## `D₄` table facts for the chain -/

theorem d4_chainZ :
    (∀ e : Fin 28, fZ br 18 16 e = if e = 20 then -1 else 0) ∧
    (∀ e : Fin 28, fZ br 18 20 e = 0) ∧ (∀ e : Fin 28, fZ br 16 20 e = 0) ∧
    (∀ e : Fin 28, fZ br 20 17 e = if e = 23 then 1 else 0) ∧
    (∀ e : Fin 28, fZ br 20 23 e = 0) ∧ (∀ e : Fin 28, fZ br 17 23 e = 0) ∧
    (∀ e : Fin 28, fZ br 23 19 e = if e = 26 then -1 else 0) ∧
    (∀ e : Fin 28, fZ br 23 26 e = 0) ∧ (∀ e : Fin 28, fZ br 19 26 e = 0) ∧
    (∀ e : Fin 28, fZ br 26 18 e = if e = 27 then -1 else 0) ∧
    (∀ e : Fin 28, fZ br 26 27 e = 0) ∧ (∀ e : Fin 28, fZ br 18 27 e = 0) := by
  decide +kernel

/-- `sl₂` data of the root `γ` with raising partner `e`. -/
def RootSl2 (e γ : Fin 28) : Prop :=
  (4 ≤ e.val ∧ e.val < 16) ∧ (∀ c : Fin 28, fZ br e γ c ≠ 0 → c.val < 4) ∧ fZ br e γ 1 = -1 ∧
    ∀ d : Fin 28, ∑ c : Fin 28, fZ br e γ c * fZ br c γ d = if d = γ then 2 else 0

instance (e γ : Fin 28) : Decidable (RootSl2 e γ) := by unfold RootSl2; infer_instance

theorem d4_rootSl2 : RootSl2 8 20 ∧ RootSl2 11 23 ∧ RootSl2 14 26 := by decide +kernel

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule fD4 V}

theorem op_comm_end4 (a b : Fin 28) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e, fD4 a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

theorem iterate_eq_pow (A : Module.End ℂ V) (n : ℕ) (x : V) : A^[n] x = (A ^ n) x := by
  rw [Module.End.pow_apply]

/-- One Heisenberg step. -/
theorem heis_step {a b z : Fin 28} {c : ℤ} (hc : c ≠ 0)
    (hab : ∀ e : Fin 28, fZ br a b e = if e = z then c else 0) (haz : ∀ e : Fin 28, fZ br a z e = 0)
    (hbz : ∀ e : Fin 28, fZ br b z e = 0) {w : V} {p : ℕ} (hX : (ρ.op a 0)^[p + 1] w = 0)
    (hY : (ρ.op b 0)^[p + 1] w = 0) : (ρ.op z 0)^[2 * p + 1] w = 0 := by
  have hcomm : ∀ x y : Fin 28, (∀ e : Fin 28, fZ br x y e = 0) →
      ρ.op x 0 * ρ.op y 0 = ρ.op y 0 * ρ.op x 0 := by
    intro x y h
    rw [← sub_eq_zero, op_comm_end4]
    refine Finset.sum_eq_zero fun e _ => ?_
    change ((fZ br x y e : ℤ) : ℂ) • _ = 0
    rw [h e, Int.cast_zero, zero_smul]
  have hXY : ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = (c : ℂ) • ρ.op z 0 := by
    rw [op_comm_end4, Finset.sum_eq_single z (fun e _ he => by
      change ((fZ br a b e : ℤ) : ℂ) • _ = 0
      rw [hab e, if_neg he, Int.cast_zero, zero_smul]) (by simp)]
    change ((fZ br a b z : ℤ) : ℂ) • _ = _
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

/-- `sl₂` sharpening for a root `γ` of `D₄` with `θ(h_γ) = 1`. -/
theorem root_sharpen {e γ : Fin 28} (hs : RootSl2 e γ) {w : V} {k : ℕ}
    (hR : ∀ x : Fin 28, 4 ≤ x.val ∧ x.val < 16 → ρ.op x 0 w = 0)
    (hC : ∀ h : Fin 28, h.val < 4 → ρ.op h 0 w = ((k * thetaD4 h : ℕ) : ℂ) • w) {N : ℕ}
    (hN : (ρ.op γ 0)^[N] w = 0) : (ρ.op γ 0)^[k + 1] w = 0 := by
  obtain ⟨he, h1, h2, h3⟩ := hs
  set H : V →ₗ[ℂ] V := -(∑ c, fD4 e γ c • ρ.op c 0) with hH
  have h3C : ∀ d, ∑ c, fD4 e γ c * fD4 c γ d = if d = γ then (2 : ℂ) else 0 := by
    intro d
    change ∑ c : Fin 28, ((fZ br e γ c : ℤ) : ℂ) * ((fZ br c γ d : ℤ) : ℂ) = _
    have := h3 d
    split_ifs at this ⊢ <;> exact_mod_cast this
  have hin : ∀ c x, ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x) =
      ∑ d, fD4 c γ d • ρ.op d 0 x := fun c x => by simpa using ρ.comm c γ 0 0 x
  refine sl2_sharpen (-ρ.op e 0) (ρ.op γ 0) H ?_ ?_ w k ?_ ?_ hN
  · intro x
    have := ρ.comm e γ 0 0 x
    simp only [add_zero] at this
    simp only [LinearMap.neg_apply, map_neg, hH, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply]
    rw [← this]; abel
  · intro x
    calc H (ρ.op γ 0 x) - ρ.op γ 0 (H x)
        = -∑ c, fD4 e γ c • (ρ.op c 0 (ρ.op γ 0 x) - ρ.op γ 0 (ρ.op c 0 x)) := by
          simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply,
            LinearMap.smul_apply, map_neg, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
          abel
      _ = -∑ d, (∑ c, fD4 e γ c * fD4 c γ d) • ρ.op d 0 x := by
          simp only [hin, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
      _ = (-2 : ℂ) • ρ.op γ 0 x := by
          simp only [h3C, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [neg_smul]
  · change -ρ.op e 0 w = 0
    rw [hR e he, neg_zero]
  · simp only [hH, LinearMap.neg_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ c : Fin 28, fD4 e γ c • ρ.op c 0 w =
        (fD4 e γ c * ((k * thetaD4 c : ℕ) : ℂ)) • w := by
      intro c
      by_cases hc : c.val < 4
      · rw [hC c hc, smul_smul]
      · have : fZ br e γ c = 0 := by
          by_contra h0; exact hc (h1 c h0)
        have h0 : fD4 e γ c = 0 := by
          change ((fZ br e γ c : ℤ) : ℂ) = 0
          rw [this, Int.cast_zero]
        rw [h0, zero_smul, zero_mul, zero_smul]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_smul,
      Finset.sum_eq_single (1 : Fin 28)]
    · change -((((fZ br e γ 1 : ℤ) : ℂ) * ((k * thetaD4 1 : ℕ) : ℂ)) • w) = (k : ℂ) • w
      rw [h2]; simp [thetaD4]
    · intro c _ hc
      have hc1 : c.val ≠ 1 := fun h => hc (Fin.ext h)
      simp [thetaD4, hc1]
    · simp

end Module

/-- **`ThetaNilG` for `D₄`**, by the Heisenberg chain `18 →16→ 20 →17→ 23 →19→ 26 →18→ 27`. -/
theorem d4_thetaNil : ThetaNilG D4sector := by
  intro k V _ _ ρ w hR hC _ hL
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := d4_chainZ
  obtain ⟨r20, r23, r26⟩ := d4_rootSl2
  have hR' : ∀ x : Fin 28, 4 ≤ x.val ∧ x.val < 16 → ρ.op x 0 w = 0 := fun x hx => hR x hx
  have hC' : ∀ h : Fin 28, h.val < 4 → ρ.op h 0 w = ((k * thetaD4 h : ℕ) : ℂ) • w :=
    fun h hh => hC h hh
  have hL18 : (ρ.op (18 : Fin 28) 0)^[k + 1] w = 0 := by
    have := hL (18 : Fin 28) (show 16 ≤ ((18 : Fin 28) : ℕ) ∧ ((18 : Fin 28) : ℕ) < 20 by decide)
    change (ρ.op (18 : Fin 28) 0)^[k * lowExpD4 18 + 1] w = 0 at this
    simpa [lowExpD4] using this
  have hz : ∀ i : Fin 28, i.val = 16 ∨ i.val = 17 ∨ i.val = 19 → (ρ.op i 0)^[k + 1] w = 0 := by
    intro i hi
    have := hL i (show 16 ≤ i.val ∧ i.val < 20 by omega)
    have h0 : lowExpD4 i = 0 := by unfold lowExpD4; rw [if_neg (by omega)]
    change (ρ.op i 0)^[k * lowExpD4 i + 1] w = 0 at this
    rw [h0, mul_zero, zero_add, Function.iterate_one] at this
    rw [Function.iterate_succ_apply, this]
    exact iterate_map_zero _ k
  have h20 := heis_step (ρ := ρ) (a := 18) (b := 16) (z := 20) (c := -1) (by norm_num) c1 c2 c3
    hL18 (hz 16 (by decide))
  have s20 := root_sharpen (ρ := ρ) r20 hR' hC' h20
  have h23 := heis_step (ρ := ρ) (a := 20) (b := 17) (z := 23) (c := 1) one_ne_zero c4 c5 c6
    s20 (hz 17 (by decide))
  have s23 := root_sharpen (ρ := ρ) r23 hR' hC' h23
  have h26 := heis_step (ρ := ρ) (a := 23) (b := 19) (z := 26) (c := -1) (by norm_num) c7 c8 c9
    s23 (hz 19 (by decide))
  have s26 := root_sharpen (ρ := ρ) r26 hR' hC' h26
  have h27 := heis_step (ρ := ρ) (a := 26) (b := 18) (z := 27) (c := -1) (by norm_num) c10 c11 c12
    s26 hL18
  rw [← iterate_eq_pow]
  exact h27

/-- **Ravinder's kernel lemma for `D₄`, unconditional.** -/
theorem d4_ravinderKernelRel' : RavinderKernelRelG D4sector.f (ravFam D4sector) (ravKw D4sector) :=
  d4_ravinderKernelRel d4_thetaNil

/-- **U5 for `D₄`** from `FusionTotalBoundG D4sector` and the `D₄` Demazure realizations. -/
theorem d4_fusionModuleBoundZ_of_totalBound (hF : FusionTotalBoundG D4sector)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    FusionModuleBoundG D4sector VOA.DeligneAudit.DeligneCharacter.D4Wp.d4FusionFZ :=
  d4_fusionModuleBoundZ_of_named hF d4_thetaNil hD

/-- **The `D₄` case from `FusionTotalBoundG` and the Demazure realizations** (matching `A₂`'s
`classicallyFree_of_totalBound`). -/
theorem d4_classicallyFree_of_totalBound (hF : FusionTotalBoundG D4sector)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  d4_classicallyFree_of_named hF d4_thetaNil hD

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.sl2_sharpen
#print axioms VOA.DeligneAudit.UnivG.d4_thetaNil
#print axioms VOA.DeligneAudit.UnivG.d4_ravinderKernelRel'
#print axioms VOA.DeligneAudit.UnivG.d4_fusionModuleBoundZ_of_totalBound
#print axioms VOA.DeligneAudit.UnivG.d4_classicallyFree_of_totalBound
end AxiomAudit
