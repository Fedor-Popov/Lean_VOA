/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieKernelData
import VOA.DeligneAudit.G2FusionKernelTheta
import VOA.DeligneAudit.F4LieHeadline

/-!
# `F₄`: Ravinder's kernel lemma and `F₄` from the named fusion inputs

* `f4KernelTable : KernelTable F4sector` (data in `F4LieKernelData`; `kill0` = the `C₃` roots
  orthogonal to `θ`).
* `f4_thetaNil`: `x₂₆`, `x₁₃`, `x₄₆` kill `w` (`θ(h) = 0`), hence so do `x₁₁ = -[x₂₆, x₄₆]`,
  `x₂₀ = -[x₁₃, x₁₁]`, `x₂₉ = [x₄₆, x₂₀]`. With `x₄₇^{k+1} w = 0`, `nil_of_ad` gives
  `x₁₂^{k+1} w = 0` (`ad x₂₆ x₄₇ = -x₁₂`, `(ad x₂₆)^2 x₄₇ = 0`) and `x₄₉^{k+1} w = 0`
  (`(ad x₂₉)^2 x₄₇ = 2x₄₉`, `(ad x₂₉)^3 x₄₇ = 0`); the Heisenberg pair `[x₁₂, x₄₉] = x₄₅ = f_θ`
  gives `f_θ^{2k+1} w = 0`.
* `f4_ravinderKernelRel`, `f4_classicallyFree_of_totalBound`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG.F4K

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.F4 VOA.DeligneAudit.UnivG
  Finset

noncomputable section

theorem fF4_eq (a b c : Fin 52) : fF4 a b c = ((fZ br a b c : ℤ) : ℂ) := rfl
theorem fF4_45 (a c : Fin 52) : fF4 a 45 c = ((fZ br a 45 c : ℤ) : ℂ) := rfl
theorem fF4_23_47 (c : Fin 52) : fF4 23 47 c = ((fZ br 23 47 c : ℤ) : ℂ) := rfl
theorem fF4_c47 (c d : Fin 52) : fF4 c 47 d = ((fZ br c 47 d : ℤ) : ℂ) := rfl
theorem fF4_21_45 (c : Fin 52) : fF4 21 45 c = ((fZ br 21 45 c : ℤ) : ℂ) := rfl

theorem negL_of (x : Fin 52) (hx : x.val ∈ negL ∨ x.val ∈ ([26, 13, 46, 47] : List ℕ)) :
    x.val ∈ negL := by
  rcases hx with hx | hx
  · exact hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h <;> simp [negL, h]

theorem tauH (h : Fin 52) (hh : h.val ∈ ([0, 1, 2] : List ℕ)) :
    ((τZ h : ℤ) : ℂ) = ((thetaH h : ℕ) : ℂ) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with h0 | h0 | h0 <;> simp [τZ, thetaH, h0]

theorem tauN (h : Fin 52) (hh : h.val ∈ ([3] : List ℕ)) :
    ((τZ h : ℤ) : ℂ) = -((thetaN h : ℕ) : ℂ) := by
  have h3 : h.val = 3 := by simpa using hh
  simp [τZ, thetaN, h3]

theorem truncUp (x : Fin 52) (hx : x.val ∈ negL ∨ x.val ∈ ([26, 13, 46, 47] : List ℕ)) :
    ∃ h : Fin 52, (h.val ∈ ([0, 1, 2] : List ℕ) ∨ h.val ∈ ([3] : List ℕ)) ∧ fF4 h x x ≠ 0 ∧
      ∀ c, c ≠ x → fF4 h x c = 0 := by
  obtain ⟨h1, h2, h3⟩ := truncUpZ x (negL_of x hx)
  refine ⟨hsel x, h1, ?_, fun c hc => ?_⟩
  · rw [fF4_eq]; exact_mod_cast h2
  · rw [fF4_eq, h3 c hc, Int.cast_zero]

theorem raisTheta (e : Fin 52) (he : e.val ∈ posL) (c : Fin 52) (hc : fF4 e 45 c ≠ 0) :
    (c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ)) ∨ (c.val ∈ negL ∧ c ≠ 45) := by
  rw [fF4_45] at hc
  exact raisThetaZ e c he (by exact_mod_cast hc)

theorem cartTau (h : Fin 52) (hh : h.val ∈ ([0, 1, 2] : List ℕ) ∨ h.val ∈ ([3] : List ℕ))
    (c : Fin 52) : fF4 h 45 c = if c = 45 then -((τZ h : ℤ) : ℂ) else 0 := by
  rw [fF4_45, cartTauZ h c hh]
  split_ifs <;> simp

theorem lowComm (x : Fin 52) (hx : x.val ∈ negL ∨ x.val ∈ ([26, 13, 46, 47] : List ℕ))
    (c : Fin 52) : fF4 x 45 c = 0 := by
  rw [fF4_45, lowCommZ x c (negL_of x hx), Int.cast_zero]

theorem lowExp_le (i : Fin 52) : lowExpS i ≤ 1 := by
  unfold lowExpS; split_ifs <;> omega

theorem simple (i : Fin 52) (h1 : lowExpS i = 1) :
    ∃ (e : Fin 52) (s : ℂ), e.val ∈ posL ∧
      (∀ c, fF4 e i c ≠ 0 → c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ)) ∧
      ∑ c, s * fF4 e i c * ((τZ c : ℤ) : ℂ) = 1 ∧
      ∀ d, ∑ c, s * fF4 e i c * fF4 c i d = if d = i then -2 else 0 := by
  have hi47 : i = (47 : Fin 52) := by
    unfold lowExpS at h1
    split_ifs at h1 with h26 h13 h46 h47
    exact Fin.ext h47
  subst hi47
  obtain ⟨s1, s2, s3⟩ := simpleZ
  refine ⟨23, -1, by decide, fun c hc => ?_, ?_, fun d => ?_⟩
  · rw [fF4_23_47] at hc
    exact s1 c (by exact_mod_cast hc)
  · have := congrArg (fun z : ℤ => (z : ℂ)) s2
    push_cast at this
    rw [show (∑ c : Fin 52, (-1 : ℂ) * fF4 23 47 c * ((τZ c : ℤ) : ℂ)) =
        ∑ c : Fin 52, -((fZ br 23 47 c : ℤ) : ℂ) * ((τZ c : ℤ) : ℂ) from
      sum_congr rfl fun c _ => by rw [fF4_23_47]; ring, this]
  · have := congrArg (fun z : ℤ => (z : ℂ)) (s3 d)
    push_cast at this
    rw [show (∑ c : Fin 52, (-1 : ℂ) * fF4 23 47 c * fF4 c 47 d) =
        ∑ c : Fin 52, -((fZ br 23 47 c : ℤ) : ℂ) * ((fZ br c 47 d : ℤ) : ℂ) from
      sum_congr rfl fun c _ => by rw [fF4_23_47, fF4_c47]; ring, this]

theorem eθ_cartan (c : Fin 52) (hc : fF4 21 45 c ≠ 0) :
    c.val ∈ ([0, 1, 2] : List ℕ) ∨ c.val ∈ ([3] : List ℕ) := by
  rw [fF4_21_45] at hc
  exact eθZ.1 c (by exact_mod_cast hc)

theorem eθ_theta : (-1 : ℂ) * ∑ c : Fin 52, fF4 21 45 c * ((τZ c : ℤ) : ℂ) = 2 := by
  have := congrArg (fun z : ℤ => (z : ℂ)) eθZ.2
  push_cast at this
  simp only [fF4_21_45]
  rw [this]; norm_num

theorem kill0_low (x : Fin 52) (hx : x.val ∈ kill0L) :
    x.val ∈ negL ∨ x.val ∈ ([26, 13, 46, 47] : List ℕ) := Or.inl (kill0_negL x hx)

theorem kill0_gen (x : Fin 52) (hx : x.val ∈ kill0L) :
    (x.val ∈ ([26, 13, 46, 47] : List ℕ) ∧ lowExpS x = 0) ∨
      ∃ (a b : Fin 52) (κ : ℂ), κ ≠ 0 ∧ a.val ∈ kill0L ∧ b.val ∈ kill0L ∧ rk a < rk x ∧
        rk b < rk x ∧ ∀ c, fF4 a b c = if c = x then κ else 0 := by
  rcases kill0Z x hx with h | ⟨h1, h2, h3, h4, h5, h6⟩
  · left
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    refine ⟨by rcases h with h | h | h <;> simp [h], ?_⟩
    unfold lowExpS
    rcases h with h | h | h <;> simp [h]
  · right
    refine ⟨ag x, bg x, (kg x : ℂ), by exact_mod_cast h1, h2, h3, h4, h5, fun c => ?_⟩
    rw [fF4_eq, h6 c]; split_ifs <;> simp

theorem fusionRoot (x : Fin 52) (hx : x.val ∈ negL) (hx0 : x ≠ 45) :
    (∃ (β : Fin 52) (κ : ℂ), β.val ∈ posL ∧ κ ≠ 0 ∧ ∀ c, fF4 β 45 c = if c = x then κ else 0) ∨
      x.val ∈ kill0L := by
  by_cases hk : x.val ∈ kill0L
  · exact Or.inr hk
  · left
    obtain ⟨h1, h2, h3⟩ := rootZ x hx hx0 hk
    refine ⟨bsel x, (ksel x : ℂ), h1, by exact_mod_cast h2, fun c => ?_⟩
    rw [fF4_45, h3 c]; split_ifs <;> simp

/-- **The `F₄` kernel table.** -/
def f4KernelTable : KernelTable F4sector where
  τ c := ((τZ c : ℤ) : ℂ)
  tauH := tauH
  tauN := tauN
  c0_fusion := show ((45 : Fin 52) : ℕ) ∈ negL by decide
  truncUp := truncUp
  raisTheta := raisTheta
  cartTau := cartTau
  lowComm := lowComm
  lowExp_le i _ := lowExp_le i
  simple i _ h1 := simple i h1
  eθ := (21 : Fin 52)
  sθ := -1
  eθ_raising := show ((21 : Fin 52) : ℕ) ∈ posL by decide
  eθ_cartan := eθ_cartan
  eθ_theta := eθ_theta
  kill0 x := x.val ∈ kill0L
  rk := rk
  kill0_low := kill0_low
  kill0_gen := kill0_gen
  fusionRoot := fusionRoot

/-! ## `ThetaNilG` -/

section Module

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule fF4 V}

theorem op_comm_f4 (a b : Fin 52) :
    ρ.op a 0 * ρ.op b 0 - ρ.op b 0 * ρ.op a 0 = ∑ e, fF4 a b e • ρ.op e 0 := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simpa using ρ.comm a b 0 0 x

theorem sum_single_f4 {a b z : Fin 52} {c : ℤ}
    (h : ∀ e : Fin 52, fZ br a b e = if e = z then c else 0) :
    ∑ e, fF4 a b e • ρ.op e 0 = (c : ℂ) • ρ.op z 0 := by
  rw [Finset.sum_eq_single z (fun e _ he => by rw [fF4_eq, h e, if_neg he, Int.cast_zero,
    zero_smul]) (by simp), fF4_eq, h z, if_pos rfl]

theorem sum_zero_f4 {a b : Fin 52} (h : ∀ e : Fin 52, fZ br a b e = 0) :
    ∑ e, fF4 a b e • ρ.op e 0 = 0 :=
  Finset.sum_eq_zero fun e _ => by rw [fF4_eq, h e, Int.cast_zero, zero_smul]

/-- A bracket of two vectors killing `w` kills `w`. -/
theorem kill_bracket {a b z : Fin 52} {c : ℤ} (hc : c ≠ 0)
    (h : ∀ e : Fin 52, fZ br a b e = if e = z then c else 0) {w : V} (ha : ρ.op a 0 w = 0)
    (hb : ρ.op b 0 w = 0) : ρ.op z 0 w = 0 := by
  have := congrArg (fun T : Module.End ℂ V => T w) (op_comm_f4 (ρ := ρ) a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ha, hb, map_zero, sub_zero] at this
  rw [sum_single_f4 h, LinearMap.smul_apply, eq_comm, smul_eq_zero] at this
  exact this.resolve_left (by exact_mod_cast hc)

end Module

/-- **`ThetaNilG` for `F₄`.** -/
theorem f4_thetaNil : ThetaNilG F4sector := by
  intro k V _ _ ρ w _ _ _ hL
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := chainZ
  have hz : ∀ i : Fin 52, i.val = 26 ∨ i.val = 13 ∨ i.val = 46 → ρ.op i 0 w = 0 := by
    intro i hi
    have := hL i (show i.val ∈ ([26, 13, 46, 47] : List ℕ) by
      rcases hi with h | h | h <;> simp [h])
    have h0 : lowExpS i = 0 := by unfold lowExpS; rcases hi with h | h | h <;> simp [h]
    change (ρ.op i 0)^[k * lowExpS i + 1] w = 0 at this
    rwa [h0, mul_zero, zero_add, Function.iterate_one] at this
  have hX : ((ρ.op (47 : Fin 52) 0) ^ (k + 1)) w = 0 := by
    have := hL (47 : Fin 52) (show ((47 : Fin 52) : ℕ) ∈ ([26, 13, 46, 47] : List ℕ) by decide)
    change (ρ.op (47 : Fin 52) 0)^[k * lowExpS 47 + 1] w = 0 at this
    rw [Module.End.pow_apply]
    simpa [lowExpS] using this
  have h26 := hz 26 (by decide)
  have h13 := hz 13 (by decide)
  have h46 := hz 46 (by decide)
  have h11 := kill_bracket (ρ := ρ) (by norm_num) c1 h26 h46
  have h20 := kill_bracket (ρ := ρ) (by norm_num) c2 h13 h11
  have h29 := kill_bracket (ρ := ρ) (by norm_num) c3 h46 h20
  -- `x₁₂^{k+1} w = 0`
  have hY1 : ((ρ.op (12 : Fin 52) 0) ^ (k + 1)) w = 0 := by
    have hs : ∀ x : Fin 52, adL (ρ.op (26 : Fin 52) 0) (ρ.op x 0) = ∑ e, fF4 26 x e • ρ.op e 0 :=
      fun x => op_comm_f4 (ρ := ρ) 26 x
    have e1 : (adL (ρ.op (26 : Fin 52) 0))^[1] (ρ.op (47 : Fin 52) 0) =
        (-1 : ℂ) • ρ.op (12 : Fin 52) 0 := by
      rw [Function.iterate_one, hs, sum_single_f4 c4]; norm_num
    have e2 : (adL (ρ.op (26 : Fin 52) 0))^[1 + 1] (ρ.op (47 : Fin 52) 0) = 0 := by
      rw [Function.iterate_succ_apply', e1, map_smul, hs, sum_zero_f4 c5, smul_zero]
    have h := nil_of_ad _ h26 e2 hX
    rw [e1, smul_pow, LinearMap.smul_apply, smul_eq_zero] at h
    exact h.resolve_left (pow_ne_zero _ (by norm_num))
  -- `x₄₉^{k+1} w = 0`
  have hY2 : ((ρ.op (49 : Fin 52) 0) ^ (k + 1)) w = 0 := by
    have hs : ∀ x : Fin 52, adL (ρ.op (29 : Fin 52) 0) (ρ.op x 0) = ∑ e, fF4 29 x e • ρ.op e 0 :=
      fun x => op_comm_f4 (ρ := ρ) 29 x
    have e2 : (adL (ρ.op (29 : Fin 52) 0))^[2] (ρ.op (47 : Fin 52) 0) =
        (2 : ℂ) • ρ.op (49 : Fin 52) 0 := by
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      rw [hs, sum_single_f4 c6, map_smul, hs, sum_single_f4 c7, smul_smul]; norm_num
    have e3 : (adL (ρ.op (29 : Fin 52) 0))^[2 + 1] (ρ.op (47 : Fin 52) 0) = 0 := by
      rw [Function.iterate_succ_apply', e2, map_smul, hs, sum_zero_f4 c8, smul_zero]
    have h := nil_of_ad _ h29 e3 hX
    rw [e2, smul_pow, LinearMap.smul_apply, smul_eq_zero] at h
    exact h.resolve_left (pow_ne_zero _ (by norm_num))
  have hXY : ρ.op (12 : Fin 52) 0 * ρ.op (49 : Fin 52) 0 -
      ρ.op (49 : Fin 52) 0 * ρ.op (12 : Fin 52) 0 = ρ.op (45 : Fin 52) 0 := by
    rw [op_comm_f4, sum_single_f4 c9]; simp
  have hXZ : ρ.op (12 : Fin 52) 0 * ρ.op (45 : Fin 52) 0 =
      ρ.op (45 : Fin 52) 0 * ρ.op (12 : Fin 52) 0 := by
    rw [← sub_eq_zero, op_comm_f4, sum_zero_f4 c10]
  have hYZ : ρ.op (49 : Fin 52) 0 * ρ.op (45 : Fin 52) 0 =
      ρ.op (45 : Fin 52) 0 * ρ.op (49 : Fin 52) 0 := by
    rw [← sub_eq_zero, op_comm_f4, sum_zero_f4 c11]
  exact Garland.heis_nilpotent hXY hYZ hXZ hY1 hY2

/-- **Ravinder's kernel lemma for `F₄`, unconditional.** -/
theorem f4_ravinderKernelRel : RavinderKernelRelG F4sector.f (ravFam F4sector) (ravKw F4sector) :=
  ravinderKernelRelG_of_table F4sector f4KernelTable f4_thetaNil

/-- **U5 for `F₄`** from `FusionTotalBoundG F4sector`, the `F₄` Demazure realizations and the
count (named: `f4FusionF m (1) = 52^m`). -/
theorem f4_fusionModuleBound_of_totalBound (hF : FusionTotalBoundG F4sector)
    (hD : ∀ n, DemazureRealizationG F4sector (ravFam F4sector)
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.f4DemazureHilb) n)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (F4Lie.f4FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (F4Lie.f4FusionF m) = ((52 : ℕ) : ℚ) ^ m) :
    FusionModuleBoundG F4sector F4Lie.f4FusionF :=
  fusionModuleBoundG_of_kernel (ravFam_zero F4sector) (ravFam_step F4sector) (ravKw_deg F4sector)
    hF f4_ravinderKernelRel hD hcount

/-- **The `F₄` case from `FusionTotalBoundG`, the Demazure realizations, the count and
`F4StarBound`** (divisor comparison: the `f4_divisorComparison`). -/
theorem f4_classicallyFree_of_totalBound (hF : FusionTotalBoundG F4sector)
    (hD : ∀ n, DemazureRealizationG F4sector (ravFam F4sector)
      (DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.f4DemazureHilb) n)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (F4Lie.f4FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (F4Lie.f4FusionF m) = ((52 : ℕ) : ℚ) ^ m)
    (hB : VOA.DeligneAudit.DeligneCharacter.F4StarBound) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .F4 F4Lie.f4W
        F4Lie.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass F4Lie.f4W 1 ⟨F4Lie.explicitPresentation.gen i,
          F4Lie.explicitPresentation.gen_weight_one i⟩).toRingHom =
        F4Lie.explicitPresentation.ideal :=
  F4Lie.f4_classicallyFree_concrete' (f4_fusionModuleBound_of_totalBound hF hD hcount) hB

end

end VOA.DeligneAudit.UnivG.F4K

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.F4K.f4KernelTable
#print axioms VOA.DeligneAudit.UnivG.F4K.f4_thetaNil
#print axioms VOA.DeligneAudit.UnivG.F4K.f4_ravinderKernelRel
#print axioms VOA.DeligneAudit.UnivG.F4K.f4_classicallyFree_of_totalBound
end AxiomAudit
