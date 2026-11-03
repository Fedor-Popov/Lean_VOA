/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.SPinning
import VOA.Huang.HuangRigidG1
import VOA.Huang.HuangModularityAlgebra
import VOA.Modularity.GNProp8PBW

/-!
# Zhu's modular data on the labels of `COne.IsModularData`, and its numerical consequences

For a nice `W` and `D : COne.ModularData W` with `hD : D.IsModularData`:

* `exists_zhuData` — a library Zhu modular datum `D'` with `D'.Mfam = famOf D hD`,
  `D'.h = hOf D`, `ZhuModularityAnalytic D'` (pinned Zhu modularity, `VOA.pbw`);
* `irredundant_famOf`, `complete_famOf` — the labelled family is a complete irredundant family;
* `fusionEigen_S` — the columns of `D.S` are common eigenvectors of the fusion matrices
  `N_{ax}^y = fusionRule (M_a, M_x; M_y)` (Huang's Theorem 5.2, `fusionEigenInput_holds`,
  transported along `S_eq_repS`);
* `sum_fusion_d` — `Σ_c N_{ab}^c d_c = d_a d_b` (the vacuum column of `D.S`);
* `S_TSTST` — `t_a (Σ_c S_ac t_c S_cb) t_b = S_ab`, `t_a = e^{2πi(h_a - c/24)}`;
* `balancing_S` — for symmetric `D.S`:
  `Σ_c N_{ab}^c e^{-2πi h_c} d_c S₀₀ = e^{-2πi h_a} e^{-2πi h_b} S_ab`.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HuangModularity

open VOA VOA.Classification.COne VOA.Huang.SPinning VOA.Huang.VerlindeEigen
  VOA.Huang.VerlindeFusion VOA.VHat VOA.VHat.DLM3 VOA.Huang.ZhuFiniteIrr VOA.Huang.ZhuSemisimple
  Complex

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The labelled family is irredundant. -/
theorem irredundant_famOf (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    Irredundant (famOf D hD) := fun i j h => hD.distinct i j h

/-- The labelled family is complete. -/
theorem complete_famOf (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    Complete (famOf D hD) := fun X => by
  obtain ⟨a, ⟨e⟩⟩ := hD.exhaust X.carrier X.isMod X.irreducible
  exact ⟨a, ⟨e⟩⟩

/-- **Zhu's modular data on the labels of `D`** (pinned modularity, PBW from `VOA.pbw`). -/
theorem exists_zhuData (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) :
    ∃ D' : VOA.ModularData W D.ι, D'.Mfam = famOf D hD ∧ D'.h = hOf D ∧
      ZhuModularityAnalytic D' := by
  classical
  have hSR : StronglyRational W := hW.1
  let Pr := voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))
  have hss := isSemisimpleRing_A_of_admissiblyRational Pr hSR.rational
  let e : D.ι ≃ Φ W :=
    equivΦ_of_irredundant_complete (famOf D hD) (irredundant_famOf D hD) (complete_famOf D hD)
  haveI : Finite (Φ W) := Finite.of_equiv D.ι e
  have hcard : Fintype.card D.ι = Nat.card (Φ W) := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.card_congr e
  refine zhuModularity_pinned_of_C2Cofinite_voaPBW (famOf D hD) (hOf D) hSR.c2Cofinite hss hcard
    (hasConformalWeight_famOf D hD) ?_
  intro j k hjk _
  constructor
  intro e'
  let Pj : IrrLWModule W := ⟨lwOfLabel D hD j, hD.irred j⟩
  let Pk : IrrLWModule W := ⟨lwOfLabel D hD k, hD.irred k⟩
  have hf : forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pj) =
      forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pk) := by
    rw [forwardMapIrr_mk, forwardMapIrr_mk]
    exact Quotient.sound ⟨e'⟩
  have he := Quotient.exact ((zhuBijective Pr).1 hf)
  exact hjk (hD.distinct j k he)

/-- `d_vac = 1`. -/
theorem d_vac (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) :
    D.d D.vac = 1 := by
  have h := hD.S_vac_right D.vac
  rw [hD.S_vac_vac] at h
  have hS : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have h' : (D.S00 : ℂ) * ((D.d D.vac : ℂ) - 1) = 0 := by
    have : (D.S00 : ℂ) = (D.S00 : ℂ) * (D.d D.vac : ℂ) := by exact_mod_cast h
    linear_combination -this
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd h0 hS
  · exact_mod_cast sub_eq_zero.mp h0

/-- The fusion rule of three labels. -/
def fus (D : VOA.Classification.COne.ModularData W) (a b c : D.ι) : ℕ :=
  fusionRule (D.module a) (D.module b) (D.module c)

/-- The data of `exists_zhuData`, destructured so that `Mfam` and `h` are definitional. -/
theorem zhu_facts (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) :
    FusionEigen (fus D) D.S ∧ (∀ a y, fus D a D.vac y = if y = a then 1 else 0) ∧
      (∀ a b, modularTEntry W (D.h a : ℂ) *
        (∑ c, D.S a c * modularTEntry W (D.h c : ℂ) * D.S c b) * modularTEntry W (D.h b : ℂ) =
          D.S a b) := by
  obtain ⟨⟨Mfam, h, hw, rep, repS, hrS, hrT⟩, hM, hh, hZ⟩ := exists_zhuData hW D hD
  simp only at hM hh
  subst hM hh
  set D' : VOA.ModularData W D.ι := ⟨famOf D hD, hOf D, hw, rep, repS, hrS, hrT⟩ with hD'
  obtain ⟨Pr⟩ := ZhuModData.zhuPBWBottomInput_of_pbw 𝒱 W
  have hSeq : D.S = D'.repS :=
    S_eq_repS Pr hW.1.c2Cofinite D hD D' hZ (fun _ _ _ => rfl)
  have hirr : Irredundant D'.Mfam := irredundant_famOf D hD
  have hcomp : Complete D'.Mfam := complete_famOf D hD
  have hv0 : Nonempty (ModuleEquiv W (D'.Mfam D.vac).isMod (adjointModule W)) := hD.vac_iso
  refine ⟨?_, ?_, ?_⟩
  · have := GenusOneG1f.fusionEigenInput_holds.{u, 0} 𝒱 W hW D.ι D' hZ hirr hcomp D.vac hv0
    rw [hSeq]
    exact this
  · exact famFusion_vac_right D' hirr D.vac hv0
  · intro a b
    rw [hSeq]
    exact rep_TSTST_apply D' a b

/-- **The dimensions form the Perron–Frobenius eigenvector**: `Σ_c N_ab^c d_c = d_a d_b`. -/
theorem sum_fusion_d (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) (a b : D.ι) :
    ∑ c, (fus D a b c : ℂ) * (D.d c : ℂ) = (D.d a : ℂ) * (D.d b : ℂ) := by
  obtain ⟨hE, hunit, -⟩ := zhu_facts hW D hD
  have h1 := eigval_spec hE a D.vac b
  have h2 := eq_eigval_mul hunit hE a D.vac
  simp only [hD.S_vac_right, d_vac D hD] at h1 h2
  have hS : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have hl : eigval hE a D.vac = (D.d a : ℂ) := by
    have h2' : (D.S00 : ℂ) * (D.d a : ℂ) = eigval hE a D.vac * (D.S00 : ℂ) := by
      push_cast at h2; simpa using h2
    have : (D.S00 : ℂ) * ((D.d a : ℂ) - eigval hE a D.vac) = 0 := by linear_combination h2'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hS
    · linear_combination -h0
  have h1' : ∑ c, (fus D a b c : ℂ) * ((D.S00 : ℂ) * (D.d c : ℂ)) =
      eigval hE a D.vac * ((D.S00 : ℂ) * (D.d b : ℂ)) := by
    rw [← h1]
  rw [hl] at h1'
  have : (D.S00 : ℂ) * ∑ c, (fus D a b c : ℂ) * (D.d c : ℂ) =
      (D.S00 : ℂ) * ((D.d a : ℂ) * (D.d b : ℂ)) := by
    rw [Finset.mul_sum]
    calc _ = ∑ c, (fus D a b c : ℂ) * ((D.S00 : ℂ) * (D.d c : ℂ)) :=
          Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [h1']; ring
  exact mul_left_cancel₀ hS this

/-- `e^{2πi h}`, the categorical twist eigenvalue. -/
def twistOf (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

theorem modularTEntry_eq (x : ℂ) :
    modularTEntry W x = twistOf x * modularTEntry W 0 := by
  simp only [modularTEntry, twistOf, ← Complex.exp_add]
  congr 1
  ring

/-- **The balancing identity for Zhu's `S`** (for symmetric `D.S`):
`S₀₀ Σ_c N_{ab}^c e^{-2πi h_c} d_c = e^{-2πi h_a} e^{-2πi h_b} S_ab`. -/
theorem balancing_S (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) (hsym : ∀ a b, D.S a b = D.S b a) (a b : D.ι) :
    (D.S00 : ℂ) * ∑ c, (fus D a b c : ℂ) * ((twistOf (D.h c : ℂ))⁻¹ * (D.d c : ℂ)) =
      (twistOf (D.h a : ℂ))⁻¹ * (twistOf (D.h b : ℂ))⁻¹ * D.S a b := by
  obtain ⟨hE, hunit, hrel⟩ := zhu_facts hW D hD
  have hvac : ∀ z, D.S z D.vac = D.S D.vac z := fun z => by
    rw [hD.S_vac_left, hD.S_vac_right]
  have ht : ∀ a, modularTEntry W (D.h a : ℂ) ≠ 0 := fun a => modularTEntry_ne_zero _
  have h := balancing_of_eigen hunit hE hvac hsym hrel ht a b
  set t0 := modularTEntry W (0 : ℂ) with ht0def
  have ht0 : t0 ≠ 0 := modularTEntry_ne_zero _
  have e1 : ∀ x, modularTEntry W (D.h x : ℂ) = twistOf (D.h x : ℂ) * t0 := fun x =>
    modularTEntry_eq _
  have ev : twistOf (D.h D.vac : ℂ) = 1 := by
    simp [twistOf, hD.h_vac]
  simp only [e1, ev, one_mul, hD.S_vac_right] at h
  have hL : ∑ c, (fus D a b c : ℂ) * ((twistOf (D.h c : ℂ) * t0)⁻¹ * ((D.S00 : ℂ) * (D.d c : ℂ)))
      = t0⁻¹ * ((D.S00 : ℂ) * ∑ c, (fus D a b c : ℂ) * ((twistOf (D.h c : ℂ))⁻¹ * (D.d c : ℂ))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_inv]; ring
  have hR : t0 * (twistOf (D.h a : ℂ) * t0)⁻¹ * (twistOf (D.h b : ℂ) * t0)⁻¹ * D.S a b =
      t0⁻¹ * ((twistOf (D.h a : ℂ))⁻¹ * (twistOf (D.h b : ℂ))⁻¹ * D.S a b) := by
    field_simp
  rw [hL, hR] at h
  exact mul_left_cancel₀ (inv_ne_zero ht0) h

end VOA.Huang.HuangModularity
