/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LevelOneHeisSingular

/-!
# The charge-`2r` bottom space of `L_1(sl₂)` has dimension at most one

Write `S_r ⊆ L_1(sl₂)` for the vectors of energy `r²` and `h₀`-charge `2r`.  In the simple
quotient itself (the subspace `I` of the reflection lemma is `⊥`):

* the affine `sl₂`-triple `(e₋₁, f₁, h₀ - 1)` satisfies the `sl₂` relations on `L_1`, and `e₋₁`
  is locally nilpotent there (`nilMod_E`, descended);
* so `f₁^{2r+1}` is injective on `S_{r+1}` (the reflection lemma `mem_of_F_pow_mem`), and maps it
  into energy `r²`, charge `-2r`;
* the descended compact conjugation `ρ` is an injective *antilinear* involution flipping the
  charge, so `ρ ∘ f₁^{2r+1} : S_{r+1} → S_r` is injective and semilinear;
* `S_0 ⊆ ℂ|0⟩` (CFT type).

Since an injective semilinear map reflects "any two vectors are proportional", induction on `r`
gives `dim S_r ≤ 1`, and a functional nonzero on a spanning vector detects `S_r`.

* `bottom_proportional` — any two vectors of `S_r` are proportional (proved);
* `levelOneBottomDetected` — **`LevelOneBottomDetected` proved outright.**
-/

namespace VOA.LevelOneHeis

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Sing
open VOA.Sl2CosetConcrete VOA.CyclicEval VOA.LevelOneUnitary
open Module (End)

noncomputable section

/-- The current mode `J^a_n` of `L_1(sl₂)`, any integer `n`. -/
abbrev Md (a : Fin 3) (n : ℤ) : End ℂ BSpace := mode (BSVA.Y (bAction.current a)) n

theorem Md_mkQ (a : Fin 3) (n : ℤ) (x : WakModule 1) :
    Md a n (IB.mkQ x) = IB.mkQ (J 1 a n x) :=
  ConcreteHodge.bMode_mkQ a n x

theorem bMode_hzero : bMode bHZero = Md colH 0 := rfl

theorem Md_mem_bWeight (a : Fin 3) (n : ℤ) {E : ℤ} {b : BSpace} (hb : b ∈ bWeight E) :
    Md a n b ∈ bWeight (E - n) := by
  have h := BSVA.grading_mode _ (bAction.current_weight a) b hb n
  unfold bWeight
  convert h using 2
  push_cast; ring

/-! ### The affine `sl₂`-triple on `L_1(sl₂)` -/

/-- `e₋₁` on `L_1`. -/
abbrev Eb : End ℂ BSpace := Md colE (-1)
/-- `f₁` on `L_1`. -/
abbrev Fb : End ℂ BSpace := Md colF 1
/-- `h₀ - 1` on `L_1`. -/
abbrev Hb : End ℂ BSpace := Md colH 0 - 1

theorem Eb_mkQ (y : WakModule 1) : Eb (IB.mkQ y) = IB.mkQ (Eop y) := Md_mkQ _ _ y
theorem Fb_mkQ (y : WakModule 1) : Fb (IB.mkQ y) = IB.mkQ (Fop y) := Md_mkQ _ _ y
theorem Hb_mkQ (y : WakModule 1) : Hb (IB.mkQ y) = IB.mkQ (Hop y) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, Md_mkQ, LinearMap.sub_apply,
    Module.End.one_apply, map_sub]

theorem Eb_Fb (v : BSpace) : Eb (Fb v) = Fb (Eb v) + Hb v := by
  obtain ⟨y, rfl⟩ := IB.mkQ_surjective v
  rw [Fb_mkQ, Eb_mkQ, Eop_Fop, map_add, Eb_mkQ, Fb_mkQ, Hb_mkQ]

theorem Hb_Eb (v : BSpace) : Hb (Eb v) = Eb (Hb v) + (2 : ℂ) • Eb v := by
  obtain ⟨y, rfl⟩ := IB.mkQ_surjective v
  rw [Eb_mkQ, Hb_mkQ, Hop_Eop, map_add, map_smul, Hb_mkQ, Eb_mkQ]

theorem Hb_Fb (v : BSpace) : Hb (Fb v) = Fb (Hb v) - (2 : ℂ) • Fb v := by
  obtain ⟨y, rfl⟩ := IB.mkQ_surjective v
  rw [Fb_mkQ, Hb_mkQ, Hop_Fop, map_sub, map_smul, Hb_mkQ, Fb_mkQ]

theorem Eb_pow_mkQ (N : ℕ) (y : WakModule 1) : (Eb ^ N) (IB.mkQ y) = IB.mkQ ((Eop ^ N) y) := by
  induction N with
  | zero => simp
  | succ N ih => rw [pow_succ', Module.End.mul_apply, ih, Eb_mkQ, pow_succ', Module.End.mul_apply]

/-- `e₋₁` is locally nilpotent on `L_1(sl₂)`. -/
theorem Eb_nil (v : BSpace) : ∃ N : ℕ, (Eb ^ N) v = 0 := by
  obtain ⟨y, rfl⟩ := IB.mkQ_surjective v
  obtain ⟨N, hN⟩ := nilMod_E bNoncritical y
  exact ⟨N, by rw [Eb_pow_mkQ]; exact (Submodule.Quotient.mk_eq_zero _).mpr hN⟩

/-- **Reflection on `L_1(sl₂)`**: `f₁^λ` is injective on the `(h₀ - 1) = λ` eigenspace. -/
theorem eq_zero_of_Fb_pow {lam : ℕ} {v : BSpace} (hv : Hb v = (lam : ℂ) • v)
    (hF : (Fb ^ lam) v = 0) : v = 0 := by
  obtain ⟨N, hN⟩ := Eb_nil v
  have h := mem_of_F_pow_mem (I := (⊥ : Submodule ℂ BSpace)) Eb_Fb Hb_Eb Hb_Fb
    (fun w hw => by rw [(Submodule.mem_bot ℂ).mp hw, map_zero]; exact Submodule.zero_mem _)
    (fun w hw => by rw [(Submodule.mem_bot ℂ).mp hw, map_zero]; exact Submodule.zero_mem _)
    N lam v hv (by rw [hN]; exact Submodule.zero_mem _) (by rw [hF]; exact Submodule.zero_mem _)
  exact (Submodule.mem_bot ℂ).mp h

theorem Fb_pow_mem_bWeight (j : ℕ) {E : ℤ} {b : BSpace} (hb : b ∈ bWeight E) :
    (Fb ^ j) b ∈ bWeight (E - j) := by
  induction j with
  | zero => simpa using hb
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := Md_mem_bWeight colF 1 ih
      convert h using 2
      push_cast; ring

/-! ### The compact conjugation on `L_1(sl₂)` -/

theorem bConj_bConj (x : BSpace) : ConcreteHodge.bConj (ConcreteHodge.bConj x) = x :=
  ConcreteHodge.bCompactUnitary.sq x

theorem bConj_h0 (x : BSpace) :
    ConcreteHodge.bConj (Md colH 0 x) = -Md colH 0 (ConcreteHodge.bConj x) :=
  ConcreteHodge.bCompactUnitary.rho_mode 2 0 x

theorem bConj_mem_bWeight {E : ℤ} {x : BSpace} (hx : x ∈ bWeight E) :
    ConcreteHodge.bConj x ∈ bWeight E := by
  have hx' : x ∈ BVOA.grading E := by
    have : x ∈ BVOA.toPreVertexAlgebra.gradingC (E : ℂ) := hx
    rwa [PreVertexAlgebra.gradingC_intCast] at this
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx'
  have hρ : levelOneRealStructure.rho y ∈ WU.grading E := levelOne_isCompact.rho_mem_grading hy
  change _ ∈ BVOA.toPreVertexAlgebra.gradingC (E : ℂ)
  rw [PreVertexAlgebra.gradingC_intCast]
  rw [ConcreteHodge.bConj_mkQ]
  exact Submodule.mem_map_of_mem hρ

/-! ### The bottom spaces -/

/-- `S_r`: energy `r²`, charge `2r`. -/
def BottomVec (r : ℕ) (b : BSpace) : Prop :=
  b ∈ bWeight ((r : ℤ) * r) ∧ Md colH 0 b = (2 * (r : ℂ)) • b

/-- The map `ρ ∘ f₁^{2r+1} : S_{r+1} → S_r`. -/
def descend (r : ℕ) (b : BSpace) : BSpace := ConcreteHodge.bConj ((Fb ^ (2 * r + 1)) b)

theorem descend_mem {r : ℕ} {b : BSpace} (hb : BottomVec (r + 1) b) :
    BottomVec r (descend r b) := by
  obtain ⟨hw, hc⟩ := hb
  have hH : Hb b = (((2 * r + 1 : ℕ)) : ℂ) • b := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hc]; push_cast; module
  have hHF := H_F_pow Fb Hb Hb_Fb hH (2 * r + 1)
  have hcF : Md colH 0 ((Fb ^ (2 * r + 1)) b) = (-(2 * (r : ℂ))) • (Fb ^ (2 * r + 1)) b := by
    have : Md colH 0 ((Fb ^ (2 * r + 1)) b) = Hb ((Fb ^ (2 * r + 1)) b) +
        (Fb ^ (2 * r + 1)) b := by
      rw [LinearMap.sub_apply, Module.End.one_apply]; abel
    rw [this, hHF]; push_cast; module
  refine ⟨?_, ?_⟩
  · apply bConj_mem_bWeight
    have h := Fb_pow_mem_bWeight (2 * r + 1) hw
    convert h using 2
    push_cast; ring
  · rw [descend, ← neg_neg (Md colH 0 _), ← bConj_h0, hcF, map_smulₛₗ, ← neg_smul]
    congr 1
    rw [map_neg, map_mul, map_ofNat, map_natCast, neg_neg]

theorem descend_inj {r : ℕ} {b : BSpace} (hb : BottomVec (r + 1) b) (h0 : descend r b = 0) :
    b = 0 := by
  obtain ⟨_, hc⟩ := hb
  have hH : Hb b = (((2 * r + 1 : ℕ)) : ℂ) • b := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hc]; push_cast; module
  refine eq_zero_of_Fb_pow hH ?_
  have := congrArg ConcreteHodge.bConj h0
  rwa [descend, bConj_bConj, map_zero] at this

theorem bottomVec_sub {r : ℕ} {b₁ b₂ : BSpace} (h₁ : BottomVec r b₁) (h₂ : BottomVec r b₂)
    (d : ℂ) : BottomVec r (b₁ - d • b₂) := by
  refine ⟨Submodule.sub_mem _ h₁.1 (Submodule.smul_mem _ _ h₂.1), ?_⟩
  rw [map_sub, map_smul, h₁.2, h₂.2, smul_sub, smul_comm d]

/-- **Any two vectors of the charge-`2r` bottom space of `L_1(sl₂)` are proportional.** -/
theorem bottom_proportional : ∀ (r : ℕ) (b₁ b₂ : BSpace), BottomVec r b₁ → BottomVec r b₂ →
    b₂ = 0 ∨ ∃ c : ℂ, b₁ = c • b₂ := by
  intro r
  induction r with
  | zero =>
      intro b₁ b₂ h₁ h₂
      have hv : ∀ b, BottomVec 0 b → ∃ c : ℂ, b = c • BSVA.vacuum := by
        intro b hb
        have hb' : b ∈ BVOA.grading 0 := by
          have h0 : b ∈ bWeight 0 := by simpa using hb.1
          have : b ∈ BVOA.toPreVertexAlgebra.gradingC ((0 : ℤ) : ℂ) := h0
          rwa [PreVertexAlgebra.gradingC_intCast] at this
        rw [BVOA.vacuum_grade, Submodule.mem_span_singleton] at hb'
        obtain ⟨c, rfl⟩ := hb'
        exact ⟨c, rfl⟩
      obtain ⟨c₁, rfl⟩ := hv b₁ h₁
      obtain ⟨c₂, rfl⟩ := hv b₂ h₂
      by_cases hc : c₂ = 0
      · left; rw [hc, zero_smul]
      · right; exact ⟨c₁ / c₂, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩
  | succ r ih =>
      intro b₁ b₂ h₁ h₂
      rcases ih _ _ (descend_mem h₁) (descend_mem h₂) with h | ⟨c, hc⟩
      · left; exact descend_inj h₂ h
      · right
        refine ⟨(starRingEnd ℂ) c, ?_⟩
        rw [← sub_eq_zero]
        apply descend_inj (bottomVec_sub h₁ h₂ _)
        rw [descend, map_sub, map_smul, map_sub, map_smulₛₗ, ← descend, ← descend, hc]
        simp

/-- **`LevelOneBottomDetected`, proved outright**: the vectors of `L_1(sl₂)` of charge `2r`
and energy `r²` are detected by a single functional. -/
theorem levelOneBottomDetected : LevelOneBottomDetected := by
  intro r
  by_cases hex : ∃ b₀, BottomVec r b₀ ∧ b₀ ≠ 0
  · obtain ⟨b₀, hb₀, hne⟩ := hex
    obtain ⟨β, hβ⟩ : ∃ β : Module.Dual ℂ BSpace, β b₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ b₀).mp hall)
    refine ⟨β, fun b hb hc hβb => ?_⟩
    rcases bottom_proportional r b b₀ ⟨hb, hc⟩ hb₀ with h | ⟨c, rfl⟩
    · exact absurd h hne
    · rw [map_smul, smul_eq_mul] at hβb
      rw [(mul_eq_zero.mp hβb).resolve_right hβ, zero_smul]
  · push Not at hex
    exact ⟨0, fun b hb hc _ => hex b ⟨hb, hc⟩⟩

end

end VOA.LevelOneHeis
