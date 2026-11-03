/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaKeyAdj
import VOA.Moonshine.SimpleForm

/-!
# SigmaKey, part 3: the isometry conditions are top-level statements

`PhiIso D` and `ThetaIso D` (`SigmaKeyAdj.lean`) quantify over the whole infinite-dimensional
sectors.  Both are differences of two **`V₀⁺`-invariant** forms on a `V₀⁺`-cyclic module, so they
are determined by their values against the cyclic vector on its own weight space:

* `phiIso_of_top` — if `z₀ ∈ V₃⁺` is `V₀⁺`-cyclic of weight `w`, then
  `TPForm(Φz₀, Φb) = leechBV(z₀, b)` for all `b ∈ (V₃⁺)_w` implies `PhiIso D`;
* `thetaIso_of_top` — if `x' ∈ T_{s+1}⁺` is `V₀⁺`-cyclic of weight `w`, then
  `TPForm(Θx', Θy) = TPForm(x', y)` for all `y ∈ (T_{s+1}⁺)_w` implies `ThetaIso D`;
* `sigmaKey_of_top` — `SigmaKey D β t` from the two **finite** (49152-dimensional
  weight-2) isometry conditions `PhiTop`, `ThetaTop` and the self-coupling identity `KeySkew`.

Proof: with `F` the difference form, FHL invariance of `TPForm` (`TPForm_fhlInv`) and of
`leechBV` (`leechBV_inv`), the twisted-intertwining property of `Φ`/`Θ` and `σ L₁ = L₁ σ` give
`F(u₍ₙ₎a, b) = (−1)^k ∑_j F(a, (L₁ʲu)₍₂ₖ₋ₙ₋₂₋ⱼ₎ b)` for homogeneous `u ∈ V₀⁺` (`Fphi_inv`,
`Fth_inv`); cyclicity then reduces `F = 0` to `F(z₀, ·) = 0`, symmetry plus cyclicity once more to
`F(z₀, c) = 0` for homogeneous `c`, and weight orthogonality to `c` of the weight of `z₀`.

`sorry`-free; unconditional apart from `D` and the displayed hypotheses.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaKey

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen M8hKey
open LatticeTwisted TwistedHeisenberg FrameT InvForm SkewAdjoint VertexOperatorAlgebra SigmaExist

variable (D : SigmaData)

/-! ## §0  Bookkeeping -/

theorem sig_L1_pow_coe (u : V0Sub.carrier) (j : ℕ) :
    ((sig (((V0P.L 1) ^ j) u) : V0Sub.carrier) : VPlus)
      = ((leechVOAPlus.L 1) ^ j) ((sig u : V0Sub.carrier) : VPlus) := by
  change ((v0Sigma (((V0P.L 1) ^ j) u) : V0Sub.carrier) : VPlus) = _
  rw [Aut.map_L_pow, V0P_coe_L_pow]
  rfl

theorem actT_eq_mode (u : V0Sub.carrier) (n : ℤ) (y : TP) :
    actT u n y = mode (plusModule.YM (u : VPlus)) n y := rfl

theorem Phi_weight {x : VPlus} (hx : x ∈ frameSector 1) {k : ℤ} (hk : x ∈ leechVOAPlus.grading k) :
    D.Φ x ∈ plusModule.weight (k : ℂ) := by
  apply eigenvector_mem_weight
  have h := IsSigmaV3T.L0_comm D.isSigma_Φ hx
  rw [← h]
  have e : mode (leechVOAPlus.Y leechVOAPlus.conformalVector) 1 x = (k : ℂ) • x :=
    leechVOAPlus.L0_grading x hk
  rw [e, map_smul]

theorem Theta_weight {y : TP} (hy : y ∈ TPframe (D.s + 1)) {k : ℂ} (hk : y ∈ plusModule.weight k) :
    D.Θ y ∈ plusModule.weight k := by
  apply eigenvector_mem_weight
  have h := IsSigmaTT.L0_comm D.isSigma_Θ hy
  rw [← h, plusModule.L0_weight _ _ hk, map_smul]

/-! ## §1  `Φ` -/

/-- The defect form `F(a,b) = TPForm(Φa, Φb) − leechBV(a, b)`. -/
noncomputable def Fphi : LinearMap.BilinForm ℂ VPlus :=
  TPForm.compl₁₂ D.Φ D.Φ - leechBV

theorem Fphi_apply (a b : VPlus) : Fphi D a b = TPForm (D.Φ a) (D.Φ b) - leechBV a b := rfl

theorem Fphi_symm (a b : VPlus) : Fphi D a b = Fphi D b a := by
  rw [Fphi_apply, Fphi_apply, TPForm_symm, SimpleNat.leechBV_symm]

/-- **Invariance of the defect form** under homogeneous `u ∈ V₀⁺`. -/
theorem Fphi_inv {k : ℤ} (u : V0Sub.carrier) (hu : (u : VPlus) ∈ leechVOAPlus.grading k) (n : ℤ)
    {a b : VPlus} (ha : a ∈ frameSector 1) (hb : b ∈ frameSector 1) :
    Fphi D (actV u n a) b = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • Fphi D a (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b) := by
  have hT : TPForm (D.Φ (actV u n a)) (D.Φ b) = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • TPForm (D.Φ a) (D.Φ (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b)) := by
    rw [D.isSigma_Φ u (Set.mem_univ _) n a ha, actT_eq_mode,
      TPForm_fhlInv (sig_mem_grading hu) n (D.Φ a) (D.Φ b)]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [D.isSigma_Φ _ (Set.mem_univ _) _ b hb, actT_eq_mode, sig_L1_pow_coe]
  have hV : leechBV (actV u n a) b = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • leechBV a (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b) := by
    rw [actV_apply, leechBV_inv k u hu n a b]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [actV_apply, V0P_coe_L_pow]
  rw [Fphi_apply, hT, hV, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fphi_apply, smul_sub]

/-- Cyclic induction: a statement about `actV u n z₀`, proved for homogeneous `u`, holds on the
whole `V₀⁺`-span. -/
theorem span_V3_induction {z₀ : VPlus}
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z₀}
      = frameSector 1)
    (P : VPlus → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a))
    (hhom : ∀ (k : ℤ) (u : V0Sub.carrier), (u : VPlus) ∈ leechVOAPlus.grading k → ∀ n, P (actV u n z₀))
    {a : VPlus} (ha : a ∈ frameSector 1) : P a := by
  rw [← hcyc] at ha
  refine Submodule.span_induction (p := fun a _ => P a) ?_ h0 (fun a b _ _ => hadd a b)
    (fun c a _ => hsmul c a) ha
  rintro _ ⟨u, -, n, rfl⟩
  refine DirectSum.Decomposition.inductionOn V0P.grading (motive := fun u => P (actV u n z₀)) ?_ ?_ ?_ u
  · have : actV (0 : V0Sub.carrier) n z₀ = 0 := by
      rw [actV_apply]; simp [leechVOAPlus.smul_zero_left]
    change P _
    rw [this]; exact h0
  · intro k m
    exact hhom k (m : V0Sub.carrier) m.2 n
  · intro m m' hm hm'
    rw [actV_add_left]
    exact hadd _ _ hm hm'

theorem Fphi_orth {z₀ : VPlus} (hz₀ : z₀ ∈ frameSector 1) {w : ℤ} (hzw : z₀ ∈ leechVOAPlus.grading w)
    {c : VPlus} (hc : c ∈ frameSector 1) {w' : ℤ} (hcw : c ∈ leechVOAPlus.grading w') (hne : w ≠ w') :
    Fphi D z₀ c = 0 := by
  rw [Fphi_apply, leechBV_orth w w' hne z₀ hzw c hcw,
    TPForm_weightOrth (w : ℂ) (w' : ℂ) (by exact_mod_cast hne) _ (Phi_weight D hz₀ hzw) _
      (Phi_weight D hc hcw), sub_zero]

/-- **`PhiIso` from its top-level instance** against a cyclic vector. -/
theorem phiIso_of_top {z₀ : VPlus} (hz₀ : z₀ ∈ frameSector 1) {w : ℤ}
    (hzw : z₀ ∈ leechVOAPlus.grading w)
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z₀}
      = frameSector 1)
    (htop : ∀ b ∈ frameSector 1, b ∈ leechVOAPlus.grading w →
      TPForm (D.Φ z₀) (D.Φ b) = leechBV z₀ b) : PhiIso D := by
  -- `F(z₀, c) = 0` for homogeneous `c ∈ V₃⁺`
  have hhomog : ∀ c ∈ frameSector 1, ∀ w' : ℤ, c ∈ leechVOAPlus.grading w' → Fphi D z₀ c = 0 := by
    intro c hc w' hcw
    by_cases h : w = w'
    · subst h; rw [Fphi_apply, htop c hc hcw, sub_self]
    · exact Fphi_orth D hz₀ hzw hc hcw h
  -- `F(b, z₀) = 0` for all `b ∈ V₃⁺`
  have hz : ∀ b ∈ frameSector 1, Fphi D b z₀ = 0 := by
    intro b hb
    refine span_V3_induction hcyc (fun b => Fphi D b z₀ = 0) (by simp)
      (fun a b ha hb' => by simp only at ha hb' ⊢; rw [map_add, LinearMap.add_apply, ha, hb', add_zero])
      (fun c a ha => by simp only at ha ⊢; rw [map_smul, LinearMap.smul_apply, ha, smul_zero])
      (fun k u hu n => ?_) hb
    simp only
    rw [Fphi_inv D u hu n hz₀ hz₀]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
    have hj := L_one_pow_mem V0P (k := k) (x := u) hu j
    exact hhomog _ (actV_stab _ (Set.mem_univ _) _ _ hz₀) _
      (leechVOAPlus.smul_mem_grading (show (((V0P.L 1) ^ j) u : VPlus) ∈ leechVOAPlus.grading (k - j) from hj) hzw _)
  -- `F(a, b) = 0` everywhere
  intro a ha b hb
  have key := span_V3_induction hcyc (fun a => ∀ b ∈ frameSector 1, Fphi D a b = 0)
    (fun b _ => by simp)
    (fun a a' h h' b hb => by rw [map_add, LinearMap.add_apply, h b hb, h' b hb, add_zero])
    (fun c a h b hb => by rw [map_smul, LinearMap.smul_apply, h b hb, smul_zero])
    (fun k u hu n b hb => by
      rw [Fphi_inv D u hu n hz₀ hb]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
      rw [Fphi_symm]
      exact hz _ (actV_stab _ (Set.mem_univ _) _ _ hb)) ha b hb
  have := key
  rw [Fphi_apply, sub_eq_zero] at this
  exact this

/-! ## §2  `Θ` -/

/-- The defect form `F(y,y') = TPForm(Θy, Θy') − TPForm(y, y')`. -/
noncomputable def Fth : LinearMap.BilinForm ℂ TP :=
  TPForm.compl₁₂ D.Θ D.Θ - TPForm

theorem Fth_apply (y y' : TP) : Fth D y y' = TPForm (D.Θ y) (D.Θ y') - TPForm y y' := rfl

theorem Fth_symm (y y' : TP) : Fth D y y' = Fth D y' y := by
  rw [Fth_apply, Fth_apply, TPForm_symm, TPForm_symm y]

theorem Fth_inv {k : ℤ} (u : V0Sub.carrier) (hu : (u : VPlus) ∈ leechVOAPlus.grading k) (n : ℤ)
    {y y' : TP} (hy : y ∈ TPframe (D.s + 1)) (hy' : y' ∈ TPframe (D.s + 1)) :
    Fth D (actT u n y) y' = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • Fth D y (actT (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) y') := by
  have hT : TPForm (D.Θ (actT u n y)) (D.Θ y') = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • TPForm (D.Θ y) (D.Θ (actT (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) y')) := by
    rw [D.isSigma_Θ u (Set.mem_univ _) n y hy, actT_eq_mode,
      TPForm_fhlInv (sig_mem_grading hu) n (D.Θ y) (D.Θ y')]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [D.isSigma_Θ _ (Set.mem_univ _) _ y' hy', actT_eq_mode, sig_L1_pow_coe]
  have hV : TPForm (actT u n y) y' = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • TPForm y (actT (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) y') := by
    rw [actT_eq_mode, TPForm_fhlInv hu n y y']
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [actT_eq_mode, V0P_coe_L_pow]
  rw [Fth_apply, hT, hV, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fth_apply, smul_sub]

theorem span_T_induction {s' : ZMod 2} {x' : TP}
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x'}
      = TPframe s')
    (P : TP → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a))
    (hhom : ∀ (k : ℤ) (u : V0Sub.carrier), (u : VPlus) ∈ leechVOAPlus.grading k → ∀ n, P (actT u n x'))
    {a : TP} (ha : a ∈ TPframe s') : P a := by
  rw [← hcyc] at ha
  refine Submodule.span_induction (p := fun a _ => P a) ?_ h0 (fun a b _ _ => hadd a b)
    (fun c a _ => hsmul c a) ha
  rintro _ ⟨u, -, n, rfl⟩
  refine DirectSum.Decomposition.inductionOn V0P.grading (motive := fun u => P (actT u n x')) ?_ ?_ ?_ u
  · have : actT (0 : V0Sub.carrier) n x' = 0 := by
      rw [actT_eq_mode]; simp
    change P _
    rw [this]; exact h0
  · intro k m
    exact hhom k (m : V0Sub.carrier) m.2 n
  · intro m m' hm hm'
    rw [actT_add_left]
    exact hadd _ _ hm hm'

/-- **`ThetaIso` from its top-level instance** against a cyclic vector. -/
theorem thetaIso_of_top {x' : TP} (hx' : x' ∈ TPframe (D.s + 1)) {w : ℂ}
    (hxw : x' ∈ plusModule.weight w)
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x'}
      = TPframe (D.s + 1))
    (htop : ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight w →
      TPForm (D.Θ x') (D.Θ y) = TPForm x' y) : ThetaIso D := by
  have hhomog : ∀ c ∈ TPframe (D.s + 1), ∀ w' : ℂ, c ∈ plusModule.weight w' → Fth D x' c = 0 := by
    intro c hc w' hcw
    by_cases h : w = w'
    · subst h; rw [Fth_apply, htop c hc hcw, sub_self]
    · rw [Fth_apply, TPForm_weightOrth w w' h _ (Theta_weight D hx' hxw) _ (Theta_weight D hc hcw),
        TPForm_weightOrth w w' h _ hxw _ hcw, sub_zero]
  have hz : ∀ b ∈ TPframe (D.s + 1), Fth D b x' = 0 := by
    intro b hb
    refine span_T_induction hcyc (fun b => Fth D b x' = 0) (by simp)
      (fun a b ha hb' => by simp only at ha hb' ⊢; rw [map_add, LinearMap.add_apply, ha, hb', add_zero])
      (fun c a ha => by simp only at ha ⊢; rw [map_smul, LinearMap.smul_apply, ha, smul_zero])
      (fun k u hu n => ?_) hb
    simp only
    rw [Fth_inv D u hu n hx' hx']
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
    have hj := L_one_pow_mem V0P (k := k) (x := u) hu j
    exact hhomog _ (actT_stab _ _ (Set.mem_univ _) _ _ hx') _
      (mode_mem_weight plusModule (show (((V0P.L 1) ^ j) u : VPlus) ∈ leechVOAPlus.grading (k - j) from hj) hxw _)
  intro a ha b hb
  have key := span_T_induction hcyc (fun a => ∀ b ∈ TPframe (D.s + 1), Fth D a b = 0)
    (fun b _ => by simp)
    (fun a a' h h' b hb => by rw [map_add, LinearMap.add_apply, h b hb, h' b hb, add_zero])
    (fun c a h b hb => by rw [map_smul, LinearMap.smul_apply, h b hb, smul_zero])
    (fun k u hu n b hb => by
      rw [Fth_inv D u hu n hx' hb]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
      rw [Fth_symm]
      exact hz _ (actT_stab _ _ (Set.mem_univ _) _ _ hb)) ha b hb
  have := key
  rw [Fth_apply, sub_eq_zero] at this
  exact this

/-! ## §3  The finite residuals and the final reduction -/

/-- **Top-level isometry of `Φ`** against `v = Ψ x`, `x = h₀(−½)𝟙 ⊗ t_s`: a statement on the
weight-2 space `(V₃⁺)₂` only. -/
def PhiTop (t : ZMod 2 → TLeechT) : Prop :=
  ∀ b ∈ frameSector 1, b ∈ leechVOAPlus.grading 2 →
    TPForm (x0T (t D.s)) (D.Φ b) = leechBV (D.Ψ (x0T (t D.s))) b

/-- **Top-level isometry of `Θ`** against `x' = h₀(−½)𝟙 ⊗ t_{s+1}`: a statement on the weight-2
space `(T_{s+1}⁺)₂` only. -/
def ThetaTop (t : ZMod 2 → TLeechT) : Prop :=
  ∀ y ∈ TPframe (D.s + 1), y ∈ plusModule.weight (2 : ℂ) →
    TPForm (D.Θ (x0T (t (D.s + 1)))) (D.Θ y) = TPForm (x0T (t (D.s + 1))) y

theorem phiIso_of_phiTop {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s)
    (ht0 : ∀ s, t s ≠ 0) (h : PhiTop D t) : PhiIso D := by
  set x := x0T (t D.s)
  have hx : x ∈ TPframe D.s := x0T_mem (ht D.s)
  have hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ) := by
    have := x0T_mem_weight (t D.s); exact_mod_cast this
  refine phiIso_of_top D (D.Ψ_mem x hx) (Psi_L0 D hx hx2) (cyc_Psi D hx (cyc_T (ht D.s) (ht0 D.s)))
    (fun b hb hb2 => ?_)
  rw [D.ΦΨ x hx]
  exact h b hb hb2

theorem thetaIso_of_thetaTop {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s)
    (ht0 : ∀ s, t s ≠ 0) (h : ThetaTop D t) : ThetaIso D :=
  thetaIso_of_top D (x0T_mem (ht (D.s + 1))) (x0T_mem_weight (t (D.s + 1)))
    (cyc_T (ht (D.s + 1)) (ht0 (D.s + 1))) h

/-- **`SigmaKey` from two finite top-level isometry statements and the self-coupling
identity.** -/
theorem sigmaKey_of_top {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiTop D t) (hΘ : ThetaTop D t) (hk : KeySkew D t) : SigmaKey D β t :=
  sigmaKey_of_skew D hβ ht ht0 (phiIso_of_phiTop D ht ht0 hΦ) (thetaIso_of_thetaTop D ht ht0 hΘ) hk

/-- **The Moonshine module** from `D`, `PhiTop`, `ThetaTop`, `KeySkew`. -/
theorem moonshine_of_top {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiTop D t) (hΘ : ThetaTop D t) (hk : KeySkew D t) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_sigma (sigmaKey_of_top D hβ ht ht0 hΦ hΘ hk)

end VOA.Moonshine.SigmaKey
