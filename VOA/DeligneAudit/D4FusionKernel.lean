/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.DeligneCharacterDemazureCountTypes
import VOA.DeligneAudit.DeligneCharacterD4Positivity

/-!
# `D₄`: Ravinder's family, the kernel lemma, and U5 from the named fusion inputs

* `d4KernelTable : KernelTable D4sector`: the structure-constant facts, by kernel `decide` on the
  integer table. `e_θ = x₁₅` (with `s_θ = -1`), the simple `sl₂`'s, `β(x)` with `[e_β, f_θ] = κ f_x`
  for the eight fusion roots with `(θ, α_x^∨) = 1`; the three roots orthogonal to `θ` (`16, 17, 19`)
  are simple with `θ(h) = 0`. The table scan was done outside Lean.
* `d4_ravinderKernelRel : ThetaNilG D4sector → RavinderKernelRelG …`.
* `d4_fusionModuleBoundZ_of_named`: U5 for `D₄` (`FusionModuleBoundG D4sector d4FusionFZ`) from
  `FusionTotalBoundG D4sector`, `ThetaNilG D4sector` and the `D₄` Demazure realizations (the count
  `d4FusionFZ_count` is proved).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem fD4_eq (a b c : Fin 28) : D4sector.f a b c = (fZ br a b c : ℂ) := rfl

/-- A Cartan acting diagonally and invertibly on each negative root vector. -/
def d4hsel (x : Fin 28) : Fin 28 :=
  if x.val = 16 ∨ x.val = 17 ∨ x.val = 19 ∨ x.val = 27 then 1 else 0

theorem d4_truncUpZ : ∀ x : Fin 28, 16 ≤ x.val →
    (d4hsel x).val < 4 ∧ fZ br (d4hsel x) x x ≠ 0 ∧
      ∀ c : Fin 28, c ≠ x → fZ br (d4hsel x) x c = 0 := by
  decide +kernel

theorem d4_raisThetaZ : ∀ e c : Fin 28, 4 ≤ e.val → e.val < 16 → fZ br e 27 c ≠ 0 →
    c.val < 4 ∨ (16 ≤ c.val ∧ c ≠ 27) := by decide +kernel

theorem d4_cartThetaZ : ∀ h c : Fin 28, h.val < 4 →
    fZ br h 27 c = if c = 27 then -(thetaD4 h : ℤ) else 0 := by decide +kernel

theorem d4_lowCommZ : ∀ x c : Fin 28, 16 ≤ x.val → fZ br x 27 c = 0 := by decide +kernel

theorem d4_simpleZ : (∀ c : Fin 28, fZ br 6 18 c = if c = 1 then 1 else 0) ∧
    (∀ c : Fin 28, fZ br 1 18 c = if c = 18 then -2 else 0) := by decide +kernel

theorem d4_eθZ : (∀ c : Fin 28, fZ br 15 27 c ≠ 0 → c.val < 4) ∧ fZ br 15 27 1 = -2 := by
  decide +kernel

/-- `β(x)` and `κ(x)`: `[e_β, f_θ] = κ f_x`. -/
def d4bsel (x : Fin 28) : Fin 28 :=
  if x.val = 26 then 6 else if x.val = 25 then 8 else if x.val = 24 then 9 else
  if x.val = 23 then 10 else if x.val = 22 then 11 else if x.val = 21 then 12 else
  if x.val = 20 then 13 else 14

def d4ksel (x : Fin 28) : ℤ :=
  if x.val = 26 ∨ x.val = 22 ∨ x.val = 21 ∨ x.val = 20 ∨ x.val = 18 then 1 else -1

theorem d4_rootZ : ∀ x : Fin 28, 16 ≤ x.val → x ≠ 27 → x.val ≠ 16 → x.val ≠ 17 → x.val ≠ 19 →
    4 ≤ (d4bsel x).val ∧ (d4bsel x).val < 16 ∧ d4ksel x ≠ 0 ∧
      ∀ c : Fin 28, fZ br (d4bsel x) 27 c = if c = x then d4ksel x else 0 := by decide +kernel

theorem d4_truncUp (x : Fin 28) (hx : 16 ≤ x.val ∨ (16 ≤ x.val ∧ x.val < 20)) :
    ∃ h : Fin 28, h.val < 4 ∧ fD4 h x x ≠ 0 ∧ ∀ c, c ≠ x → fD4 h x c = 0 := by
  have hx' : 16 ≤ x.val := by
    rcases hx with hx | hx
    · exact hx
    · exact hx.1
  obtain ⟨h1, h2, h3⟩ := d4_truncUpZ x hx'
  refine ⟨d4hsel x, h1, ?_, fun c hc => ?_⟩
  · change ((fZ br (d4hsel x) x x : ℤ) : ℂ) ≠ 0; exact_mod_cast h2
  · change ((fZ br (d4hsel x) x c : ℤ) : ℂ) = 0; rw [h3 c hc, Int.cast_zero]

theorem d4_raisTheta (e : Fin 28) (he : 4 ≤ e.val ∧ e.val < 16) (c : Fin 28) (hc : fD4 e 27 c ≠ 0) :
    c.val < 4 ∨ (16 ≤ c.val ∧ c ≠ 27) := by
  have : ((fZ br e 27 c : ℤ) : ℂ) ≠ 0 := hc
  exact d4_raisThetaZ e c he.1 he.2 (by exact_mod_cast this)

theorem d4_cartTheta (h : Fin 28) (hh : h.val < 4) (c : Fin 28) :
    fD4 h 27 c = if c = 27 then -((thetaD4 h : ℕ) : ℂ) else 0 := by
  change ((fZ br h 27 c : ℤ) : ℂ) = _
  rw [d4_cartThetaZ h c hh]
  split_ifs <;> simp

theorem d4_lowComm (x : Fin 28) (hx : 16 ≤ x.val ∨ (16 ≤ x.val ∧ x.val < 20)) (c : Fin 28) :
    fD4 x 27 c = 0 := by
  have hx' : 16 ≤ x.val := by
    rcases hx with hx | hx
    · exact hx
    · exact hx.1
  change ((fZ br x 27 c : ℤ) : ℂ) = 0
  rw [d4_lowCommZ x c hx', Int.cast_zero]

theorem d4_lowExp_le (i : Fin 28) : lowExpD4 i ≤ 1 := by
  unfold lowExpD4; split_ifs <;> omega

theorem d4_simple (i : Fin 28) (h1 : lowExpD4 i = 1) :
    ∃ e hi : Fin 28, (4 ≤ e.val ∧ e.val < 16) ∧ hi.val < 4 ∧
      (∀ c, fD4 e i c = if c = hi then 1 else 0) ∧ thetaD4 hi = 1 ∧
      (∀ c, fD4 hi i c = if c = i then -2 else 0) := by
  have hi18 : i = (18 : Fin 28) := by
    unfold lowExpD4 at h1
    split_ifs at h1 with h
    exact Fin.ext h
  subst hi18
  refine ⟨6, 1, by decide, by decide, fun c => ?_, by decide, fun c => ?_⟩
  · change ((fZ br 6 18 c : ℤ) : ℂ) = _
    rw [d4_simpleZ.1 c]; split_ifs <;> simp
  · change ((fZ br 1 18 c : ℤ) : ℂ) = _
    rw [d4_simpleZ.2 c]; split_ifs <;> simp

theorem d4_eθ_cartan (c : Fin 28) (hc : fD4 15 27 c ≠ 0) : c.val < 4 := by
  have : ((fZ br 15 27 c : ℤ) : ℂ) ≠ 0 := hc
  exact d4_eθZ.1 c (by exact_mod_cast this)

theorem d4_eθ_theta : (-1 : ℂ) * ∑ c : Fin 28, fD4 15 27 c * ((thetaD4 c : ℕ) : ℂ) = 2 := by
  rw [Finset.sum_eq_single (1 : Fin 28)]
  · have : fD4 15 27 1 = ((-2 : ℤ) : ℂ) := by
      change ((fZ br 15 27 1 : ℤ) : ℂ) = _; rw [d4_eθZ.2]
    rw [this]; simp [thetaD4]
  · intro c _ hc
    have hc1 : c.val ≠ 1 := fun h => hc (Fin.ext h)
    have : thetaD4 c = 0 := by simp [thetaD4, hc1]
    rw [this]; simp
  · simp

theorem d4_fusionRoot (x : Fin 28) (hx : 16 ≤ x.val) (hx0 : x ≠ 27) :
    (∃ (β : Fin 28) (κ : ℂ), (4 ≤ β.val ∧ β.val < 16) ∧ κ ≠ 0 ∧
      ∀ c, fD4 β 27 c = if c = x then κ else 0) ∨
      ((16 ≤ x.val ∧ x.val < 20) ∧ lowExpD4 x = 0) := by
  by_cases h16 : x.val = 16 ∨ x.val = 17 ∨ x.val = 19
  · right
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    unfold lowExpD4; rw [if_neg (by omega)]
  · left
    simp only [not_or] at h16
    obtain ⟨h1, h2, h3, h4⟩ := d4_rootZ x hx hx0 h16.1 h16.2.1 h16.2.2
    refine ⟨d4bsel x, (d4ksel x : ℂ), ⟨h1, h2⟩, by exact_mod_cast h3, fun c => ?_⟩
    change ((fZ br (d4bsel x) 27 c : ℤ) : ℂ) = _
    rw [h4 c]; split_ifs <;> simp

theorem d4_simple' (i : Fin 28) (h1 : lowExpD4 i = 1) :
    ∃ e : Fin 28, (4 ≤ e.val ∧ e.val < 16) ∧ (∀ c, fD4 e i c ≠ 0 → c.val < 4) ∧
      ∑ c, fD4 e i c * ((thetaD4 c : ℕ) : ℂ) = 1 ∧
      ∀ d, ∑ c, fD4 e i c * fD4 c i d = if d = i then -2 else 0 := by
  obtain ⟨e, hi, he, hhi, hei, hth, hhf⟩ := d4_simple i h1
  refine ⟨e, he, fun c hc => ?_, ?_, fun d => ?_⟩
  · by_cases hci : c = hi
    · rw [hci]; exact hhi
    · rw [hei c, if_neg hci] at hc; exact absurd rfl hc
  · rw [Finset.sum_eq_single hi (fun c _ hc => by rw [hei c, if_neg hc, zero_mul]) (by simp),
      hei, if_pos rfl, hth]; simp
  · rw [Finset.sum_eq_single hi (fun c _ hc => by rw [hei c, if_neg hc, zero_mul]) (by simp),
      hei, if_pos rfl, one_mul, hhf d]

/-- **The `D₄` kernel table.** -/
def d4KernelTable : KernelTable D4sector where
  τ c := ((thetaD4 c : ℕ) : ℂ)
  tauH _ _ := rfl
  tauN _ hh := hh.elim
  c0_fusion := show 16 ≤ ((27 : Fin 28) : ℕ) by decide
  truncUp x hx := by
    obtain ⟨h, h1, h2, h3⟩ := d4_truncUp x hx
    exact ⟨h, Or.inl h1, h2, h3⟩
  raisTheta e he c hc := by
    rcases d4_raisTheta e he c hc with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  cartTau h hh c := by
    rcases hh with hh | hh
    · exact d4_cartTheta h hh c
    · exact hh.elim
  lowComm := d4_lowComm
  lowExp_le i _ := d4_lowExp_le i
  simple i _ h1 := by
    obtain ⟨e, he, hc, h2, h3⟩ := d4_simple' i h1
    exact ⟨e, 1, he, fun c hf => Or.inl (hc c hf), by simpa using h2, fun d => by simpa using h3 d⟩
  eθ := (15 : Fin 28)
  sθ := -1
  eθ_raising := show 4 ≤ ((15 : Fin 28) : ℕ) ∧ ((15 : Fin 28) : ℕ) < 16 by decide
  eθ_cartan c hc := Or.inl (d4_eθ_cartan c hc)
  eθ_theta := d4_eθ_theta
  kill0 x := D4sector.lowering x ∧ D4sector.lowExp x = 0
  rk _ := 0
  kill0_low _ h := Or.inr h.1
  kill0_gen _ h := Or.inl h
  fusionRoot := d4_fusionRoot

/-- **Ravinder's kernel lemma for `D₄`**, from the integrability input `ThetaNilG`. -/
theorem d4_ravinderKernelRel (hN : ThetaNilG D4sector) :
    RavinderKernelRelG D4sector.f (ravFam D4sector) (ravKw D4sector) :=
  ravinderKernelRelG_of_table D4sector d4KernelTable hN

/-- **The `D₄` squeeze inputs** for the universal characters of Ravinder's family. -/
theorem d4_fusionSqueezeInputs_of_named (hF : FusionTotalBoundG D4sector)
    (hN : ThetaNilG D4sector)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    DeligneCarrier.FusionSqueezeInputsG VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ 28
      (MuniG D4sector (ravFam D4sector)) :=
  fusionSqueezeInputsG_of_kernel (ravFam_zero D4sector) (ravFam_step D4sector) (ravKw_deg D4sector)
    hF (d4_ravinderKernelRel hN) hD

/-- **U5 for `D₄`** (`FusionModuleBoundG D4sector d4FusionFZ`) from `FusionTotalBoundG`,
`ThetaNilG` and the `D₄` Demazure realizations; the count is proved (`d4FusionFZ_count`). -/
theorem d4_fusionModuleBoundZ_of_named (hF : FusionTotalBoundG D4sector) (hN : ThetaNilG D4sector)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    FusionModuleBoundG D4sector VOA.DeligneAudit.DeligneCharacter.D4Wp.d4FusionFZ :=
  fusionModuleBoundG_of_kernel (ravFam_zero D4sector) (ravFam_step D4sector) (ravKw_deg D4sector)
    hF (d4_ravinderKernelRel hN) hD DeligneCarrier.d4FusionFZ_count

/-- **The `D₄` case from the named fusion inputs**: `L_{-2}(so₈)` is classically free with ideal
`I₂ⁿˢ`, from `FusionTotalBoundG`, `ThetaNilG` and the Demazure realizations. -/
theorem d4_classicallyFree_of_named (hF : FusionTotalBoundG D4sector) (hN : ThetaNilG D4sector)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4Lie.classicallyFree_of_fusionBoundZ (d4_fusionModuleBoundZ_of_named hF hN hD)

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.d4KernelTable
#print axioms VOA.DeligneAudit.UnivG.d4_ravinderKernelRel
#print axioms VOA.DeligneAudit.UnivG.d4_fusionModuleBoundZ_of_named
#print axioms VOA.DeligneAudit.UnivG.d4_classicallyFree_of_named
end AxiomAudit
