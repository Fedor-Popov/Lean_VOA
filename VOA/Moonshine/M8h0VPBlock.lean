/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TTBlock
import VOA.Moonshine.M8h0Skew
import VOA.Moonshine.M8h0Goddard
import VOA.Moonshine.M8h0Translate

/-!
# M8h-0: DGM (4.22) unconditionally — `VPBlockLocal leechWbar t₁ t₂` for all `t₁, t₂ ∈ TP`

DGM (4.22) is the `V_Λ^+ → V_Λ^+` block of the twisted × twisted locality:

  `(z₁ − z₂)ᴺ [W̄(t₁,z₁) W(t₂,z₂) − W̄(t₂,z₂) W(t₁,z₁)] = 0`   on `V_Λ^+`.

## Proof

1. **Vacuum step** (`vac_step`).  For homogeneous `t₁ ∈ TP_a`, `t₂ ∈ TP_b` and `P ≥ a + b` put
   `f(z₁,z₂) = W̄(t₁,z₁)W(t₂,z₂)𝟙`, `g(z₁,z₂) = W̄(t₂,z₂)W(t₁,z₁)𝟙`, `H = (z₁−z₂)ᴾ f`,
   `H' = (z₁−z₂)ᴾ g`.  All four satisfy the translation equation `L₋₁ D = (∂₁+∂₂) D`
   (`fF_TEq`: translation covariance of `W̄` and `W(t,z)𝟙 = e^{zL₋₁}t`).  By the grading,
   `H` and `H'` are supported on the quadrant `m, n ≥ 0` (`TEq.zero_of_neg_left`).  The closed
   form `TEq.closed_form` computes `H(0,n)` from `H(·,0) = W̄(t₁)[· − P] t₂`, while
   `H'(0,n) = (−1)ᴾ W̄(t₂)[n − P] t₁`; the **skew-symmetry** `leechWbar_skew` (DGM (4.9)) says
   exactly that these agree.  Hence `H − H'` vanishes on the boundary `m = 0`, so it is zero
   (`TEq.eq_zero_of_quadrant`).
2. **Goddard step.**  On `V♮`, `B := (z₁−z₂)ᴾ [Y♮(t₁,z₁), Y♮(t₂,z₂)]` kills the vacuum by step 1
   and is three-variable local with every `Y♮(u, ·)`, `u ∈ V_Λ^+`, because each `Y♮(u)` is local
   with each `Y♮(tᵢ)` (`YnatU_YnatT_local_genuine`, `loc3_mulBySubPow_bracketDist`).  The
   two-variable Goddard lemma `goddard₂` then gives `B (u,0) = 0`, which is (4.22) on `u`.
3. **Linearity**: (4.22) is bilinear in `(t₁, t₂)`, and `TP` is spanned by integer-weight
   vectors (`iSup_plusModule_weight_int`).

## Main results
* `leechWbar_VPBlockLocal : ∀ t₁ t₂ : TP, VPBlockLocal leechWbar t₁ t₂` (unconditional).
* `vac_step`, `VPBlockLocal_homog` (with the explicit order `N = (a + b).toNat`).

## Status
`sorry`-free; unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8h0

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction SkewAdjoint InvForm
open scoped BigOperators

/-! ## `W(t,z)𝟙 = e^{zL₋₁}t` and the translation equation -/

theorem LTP_Wsk_vac (s : TP) (n : ℤ) :
    leechLTP (leechWsk s n leechVOAPlus.vacuum)
      = ((n + 1 : ℤ) : ℂ) • leechWsk s (n + 1) leechVOAPlus.vacuum := by
  rw [leechWsk_vacuum, leechWsk_vacuum]
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    rw [if_pos hn, if_pos (by omega), show ((k : ℤ) + 1).toNat = k + 1 by omega,
      Int.toNat_natCast, map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [mul_inv, ← mul_assoc, show (((k : ℤ) + 1 : ℤ) : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; rfl,
      mul_inv_cancel₀ h1, one_mul]
  · rw [if_neg hn, map_zero]
    by_cases h1 : n = -1
    · subst h1; rw [show (-1 : ℤ) + 1 = 0 by norm_num, Int.cast_zero, zero_smul]
    · rw [if_neg (by omega), smul_zero]

/-- `f(z₁,z₂) = W̄(t,z₁) W(s,z₂) 𝟙`. -/
noncomputable def fF (t s : TP) : FormalDist₂ SkewVP :=
  fun m n => leechWbar t m (leechWsk s n leechVOAPlus.vacuum)

theorem fF_TEq (t s : TP) : TEq (leechVOAPlus.L (-1)) (fF t s) := by
  intro m n
  have hc := congrArg (fun F => F (leechWsk s n leechVOAPlus.vacuum)) (leechWbar_homCov' t m)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at hc
  rw [LTP_Wsk_vac, map_smul] at hc
  change leechVOAPlus.L (-1) (leechWbar t m (leechWsk s n leechVOAPlus.vacuum)) = _
  rw [← Int.cast_smul_eq_zsmul ℂ] at hc
  rw [sub_eq_iff_eq_add] at hc
  exact hc

theorem fF_neg (t s : TP) (m n : ℤ) (hn : n < 0) : fF t s m n = 0 := by
  change leechWbar t m (leechWsk s n leechVOAPlus.vacuum) = 0
  rw [leechWsk_vacuum, if_neg (by omega), map_zero]

theorem fF_zero (t s : TP) (m : ℤ) : fF t s m 0 = leechWbar t m s := by
  change leechWbar t m (leechWsk s 0 leechVOAPlus.vacuum) = _
  rw [leechWsk_vacuum, if_pos le_rfl]
  simp

theorem leechWbar_weight_zero {a b : ℤ} {t s : TP} (ht : t ∈ plusModule.weight (a : ℂ))
    (hs : s ∈ plusModule.weight (b : ℂ)) (m : ℤ) (hm : a + b + m < 0) : leechWbar t m s = 0 := by
  have h := leechWbar_mem (-m - 1) ht hs
  rw [leechVOAPlus.positivity _ (by omega), Submodule.mem_bot] at h
  rw [leechWbar_coeff]; exact h

/-! ## Boundary values of `(z₁−z₂)ᴾ D` -/

section Bdry

variable {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲]

theorem bdry_n (D : FormalDist₂ 𝒲) (hD : ∀ m n, n < 0 → D m n = 0) (P : ℕ) :
    (∀ m n, n < 0 → mulBySubPow P D m n = 0) ∧ ∀ m, mulBySubPow P D m 0 = D (m - P) 0 := by
  induction P with
  | zero => exact ⟨hD, fun m => by simp⟩
  | succ P ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun m n hn => ?_, fun m => ?_⟩
    · rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, h1 _ _ hn, h1 _ _ (by omega),
        sub_zero]
    · rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, h2, h1 _ _ (by omega), sub_zero]
      congr 1; push_cast; omega

theorem bdry_m (D : FormalDist₂ 𝒲) (hD : ∀ m n, m < 0 → D m n = 0) (P : ℕ) :
    (∀ m n, m < 0 → mulBySubPow P D m n = 0) ∧
      ∀ n, mulBySubPow P D 0 n = ((-1 : ℂ) ^ P) • D 0 (n - P) := by
  induction P with
  | zero => exact ⟨hD, fun n => by simp⟩
  | succ P ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun m n hm => ?_, fun n => ?_⟩
    · rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, h1 _ _ hm, h1 _ _ (by omega),
        sub_zero]
    · rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, h1 _ _ (by omega), h2,
        zero_sub, pow_succ, mul_neg_one, neg_smul,
        show n - 1 - ((P : ℕ) : ℤ) = n - ((P + 1 : ℕ) : ℤ) by push_cast; ring]

end Bdry

theorem mulBySubPow_map' {𝒲 𝒲' : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] [AddCommGroup 𝒲']
    [Module ℂ 𝒲'] (f : 𝒲 →ₗ[ℂ] 𝒲') (N : ℕ) (G : FormalDist₂ 𝒲) :
    mulBySubPow N ((fun m n => f (G m n)) : FormalDist₂ 𝒲') = fun m n => f (mulBySubPow N G m n) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySubPow_succ, LinearMap.comp_apply]
    funext m n
    simp only [mulBySub_apply, map_sub]

/-! ## The vacuum step -/

/-- **The vacuum step of (4.22)**: for homogeneous `t₁ ∈ TP_a`, `t₂ ∈ TP_b` and `P ≥ a + b`,
`(z₁−z₂)ᴾ W̄(t₁,z₁)W(t₂,z₂)𝟙 = (z₁−z₂)ᴾ W̄(t₂,z₂)W(t₁,z₁)𝟙`. -/
theorem vac_step {a b : ℤ} {t₁ t₂ : TP} (ht₁ : t₁ ∈ plusModule.weight (a : ℂ))
    (ht₂ : t₂ ∈ plusModule.weight (b : ℂ)) (P : ℕ) (hP : a + b ≤ P) :
    mulBySubPow P (fF t₁ t₂) = mulBySubPow P (fun m n => fF t₂ t₁ n m) := by
  obtain ⟨Hn, H0⟩ := bdry_n (fF t₁ t₂) (fun m n hn => fF_neg t₁ t₂ m n hn) P
  obtain ⟨H'm, H'0⟩ := bdry_m ((fun m n => fF t₂ t₁ n m) : FormalDist₂ SkewVP)
    (fun m n hm => fF_neg t₂ t₁ n m hm) P
  have hT := (fF_TEq t₁ t₂).mulBySubPow P
  have hT' := (fF_TEq t₂ t₁).swap.mulBySubPow P
  set L := leechVOAPlus.L (-1)
  set H := mulBySubPow P (fF t₁ t₂) with hH
  set H' := mulBySubPow P ((fun m n => fF t₂ t₁ n m) : FormalDist₂ SkewVP) with hH'
  -- quadrant support of `H`
  have Hm : ∀ m n, m < 0 → H m n = 0 := hT.zero_of_neg_left Hn fun m hm => by
    rw [H0, fF_zero]; exact leechWbar_weight_zero ht₁ ht₂ _ (by omega)
  -- quadrant support of `H'`
  have H'n : ∀ m n, n < 0 → H' m n = 0 := by
    have hS : TEq L (fun m n => H' n m) := hT'.swap
    have := hS.zero_of_neg_left (fun m n hn => H'm n m hn) fun m hm => by
      change H' 0 m = 0
      rw [H'0]
      change ((-1 : ℂ) ^ P) • fF t₂ t₁ (m - P) 0 = 0
      rw [fF_zero, leechWbar_weight_zero ht₂ ht₁ _ (by omega), smul_zero]
    exact fun m n hn => this n m hn
  -- `D = H − H'` vanishes
  have hD : TEq L (H - H') := hT.sub hT'
  have hq : ∀ m n, (m < 0 ∨ n < 0) → (H - H') m n = 0 := by
    intro m n hmn
    change H m n - H' m n = 0
    rcases hmn with hm | hn
    · rw [Hm m n hm, H'm m n hm, sub_zero]
    · rw [Hn m n hn, H'n m n hn, sub_zero]
  have h0 : ∀ n, (H - H') 0 n = 0 := by
    intro n
    change H 0 n - H' 0 n = 0
    by_cases hn : n < 0
    · rw [Hn 0 n hn, H'n 0 n hn, sub_zero]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    rw [sub_eq_zero]
    -- `H(0,k)` by the closed form
    have hc := hT.closed_form k 0
    rw [show ((0 : ℕ) : ℤ) = 0 from rfl] at hc
    rw [hc, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      tcoef 0 i j • (L ^ i) (H ((0 + j : ℕ) : ℤ) 0)) k]
    -- `H'(0,k)` by the skew-symmetry
    rw [H'0]
    change _ = ((-1 : ℂ) ^ P) • fF t₂ t₁ ((k : ℤ) - P) 0
    rw [fF_zero, leechWbar_coeff, leechWbar_skew ht₂ ht₁]
    have hfin : (∑ᶠ i : ℕ, (((i.factorial : ℂ)⁻¹) * negOnePow (-((k : ℤ) - P) - 1 + i + 1)) •
          (L ^ i) (leechWbarMode (-((k : ℤ) - P) - 1 + i) t₁ t₂))
        = ∑ i ∈ Finset.range (k + 1), (((i.factorial : ℂ)⁻¹) * negOnePow (-((k : ℤ) - P) - 1 + i + 1)) •
          (L ^ i) (leechWbarMode (-((k : ℤ) - P) - 1 + i) t₁ t₂) := by
      refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hik
      apply hi
      have hw := leechWbar_weight_zero ht₁ ht₂ ((k : ℤ) - P - i) (by omega)
      rw [leechWbar_coeff, show -((k : ℤ) - P - i) - 1 = -((k : ℤ) - P) - 1 + i by ring] at hw
      rw [hw, map_zero, smul_zero]
    rw [hfin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [H0, fF_zero, leechWbar_coeff, smul_smul,
      show -(((0 + (k - i) : ℕ) : ℤ) - P) - 1 = -((k : ℤ) - P) - 1 + i by omega]
    congr 1
    -- the coefficients
    rw [tcoef, zero_add, Nat.choose_self, Nat.cast_one, one_mul, negOnePow_eq_zpow]
    have hs : ((-1 : ℂ) ^ (k - i)) = (-1 : ℂ) ^ P * (-1 : ℂ) ^ (-((k : ℤ) - P) - 1 + i + 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      exact neg_one_zpow_eq_of_even_sub ⟨(k : ℤ) - i - P, by omega⟩
    rw [hs]
    ring
  have := hD.eq_zero_of_quadrant hq h0
  exact sub_eq_zero.mp this

/-! ## The Goddard step on `V♮` -/

/-- The `V_Λ^+`-block of `[Y♮(t₁,z₁), Y♮(t₂,z₂)]`, as in `VPBlockLocal`. -/
noncomputable def VPfun (t₁ t₂ : TP) : FormalDist₂ (End ℂ SkewVP) :=
  fun m n => leechWbar t₁ m ∘ₗ leechWsk t₂ n - leechWbar t₂ n ∘ₗ leechWsk t₁ m

/-- `g(z₁,z₂) = W̄(t₂,z₂) W(t₁,z₁) 𝟙`. -/
noncomputable def gF (t₁ t₂ : TP) : FormalDist₂ SkewVP := fun m n => fF t₂ t₁ n m

theorem VPBlockLocal_iff (t₁ t₂ : TP) :
    VPBlockLocal leechWbar t₁ t₂ ↔ ∃ N : ℕ, mulBySubPow N (VPfun t₁ t₂) = 0 := Iff.rfl

theorem bracket_inl (t₁ t₂ : TP) (m n : ℤ) (u : SkewVP) :
    bracketDist (YnatT leechWbar t₁) (YnatT leechWbar t₂) m n (u, 0) = (VPfun t₁ t₂ m n u, 0) := by
  simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, YnatT, offF,
    blockF_apply, blockOp_apply, map_zero, add_zero, zero_add, formalDist_zero_apply,
    LinearMap.zero_apply, VPfun, LinearMap.comp_apply]
  ext <;> simp

theorem B_inl (t₁ t₂ : TP) (N : ℕ) (m n : ℤ) (u : SkewVP) :
    mulBySubPow N (bracketDist (YnatT leechWbar t₁) (YnatT leechWbar t₂)) m n (u, 0)
      = (mulBySubPow N (VPfun t₁ t₂) m n u, 0) := by
  have h1 := congrFun (congrFun (applyVec_mulBySubPow N ((u, 0) : Vnat)
    (bracketDist (YnatT leechWbar t₁) (YnatT leechWbar t₂))) m) n
  rw [applyVec_apply] at h1
  rw [h1]
  have h2 : applyVec ((u, 0) : Vnat) (bracketDist (YnatT leechWbar t₁) (YnatT leechWbar t₂))
      = fun m n => LinearMap.inl ℂ SkewVP TP (applyVec u (VPfun t₁ t₂) m n) := by
    funext m n
    rw [applyVec_apply, bracket_inl]; rfl
  rw [h2, mulBySubPow_map', ← applyVec_mulBySubPow]
  rfl

/-- **DGM (4.22) for homogeneous twisted states**, with explicit order `(a + b).toNat`. -/
theorem VPBlockLocal_homog {a b : ℤ} {t₁ t₂ : TP} (ht₁ : t₁ ∈ plusModule.weight (a : ℂ))
    (ht₂ : t₂ ∈ plusModule.weight (b : ℂ)) :
    mulBySubPow (a + b).toNat (VPfun t₁ t₂) = 0 := by
  set P := (a + b).toNat
  set B := mulBySubPow P (bracketDist (YnatT leechWbar t₁) (YnatT leechWbar t₂))
  have hvac : ∀ m n, B m n vacNat = 0 := by
    intro m n
    have hv : vacNat = (leechVOAPlus.vacuum, (0 : TP)) := rfl
    rw [hv, B_inl]
    have h3 := congrFun (congrFun (applyVec_mulBySubPow P leechVOAPlus.vacuum (VPfun t₁ t₂)) m) n
    rw [applyVec_apply] at h3
    have h4 : applyVec leechVOAPlus.vacuum (VPfun t₁ t₂) = fF t₁ t₂ - gF t₁ t₂ := by
      funext m n; rfl
    have h5 : mulBySubPow P (gF t₁ t₂) = mulBySubPow P (fF t₁ t₂) :=
      (vac_step ht₁ ht₂ P (by omega)).symm
    rw [h3, h4, map_sub, h5, sub_self]
    rfl
  refine FormalDist₂.ext fun m n => LinearMap.ext fun u => ?_
  obtain ⟨M₁, M₂, hloc⟩ := loc3_mulBySubPow_bracketDist (YnatU_YnatT_local_genuine u t₁)
    (YnatU_YnatT_local_genuine u t₂) P
  have hg := goddard₂ vacNat (YnatU u) B M₁ M₂ hloc (YnatU_vac_neg u) hvac 0 m n
  rw [YnatU_vac_zero, B_inl] at hg
  exact congrArg Prod.fst hg

/-! ## Linearity and the general statement -/

theorem leechWbar_add (t t' : TP) (m : ℤ) : leechWbar (t + t') m = leechWbar t m + leechWbar t' m := by
  have := congrArg (fun F => F m) (leechWbarLin.map_add t t')
  simpa using this

theorem leechWsk_add (t t' : TP) (m : ℤ) : leechWsk (t + t') m = leechWsk t m + leechWsk t' m := by
  have := congrArg (fun F => F m) (leechWskLin.map_add t t')
  simpa [leechWskLin] using this

theorem VPfun_add_left (t t' s : TP) : VPfun (t + t') s = VPfun t s + VPfun t' s := by
  funext m n
  change _ = VPfun t s m n + VPfun t' s m n
  simp only [VPfun, leechWbar_add, leechWsk_add, LinearMap.add_comp, LinearMap.comp_add]
  abel

theorem VPfun_add_right (t s s' : TP) : VPfun t (s + s') = VPfun t s + VPfun t s' := by
  funext m n
  change _ = VPfun t s m n + VPfun t s' m n
  simp only [VPfun, leechWbar_add, leechWsk_add, LinearMap.add_comp, LinearMap.comp_add]
  abel

theorem exists_mulBySubPow_add {F G : FormalDist₂ (End ℂ SkewVP)}
    (hF : ∃ N : ℕ, mulBySubPow N F = 0) (hG : ∃ N : ℕ, mulBySubPow N G = 0) :
    ∃ N : ℕ, mulBySubPow N (F + G) = 0 := by
  obtain ⟨N₁, h₁⟩ := hF
  obtain ⟨N₂, h₂⟩ := hG
  refine ⟨max N₁ N₂, ?_⟩
  rw [map_add, mulBySubPow_eq_zero_of_le (le_max_left N₁ N₂) h₁,
    mulBySubPow_eq_zero_of_le (le_max_right N₁ N₂) h₂, add_zero]

/-- Induction over the integer weight spaces of `TP`. -/
theorem TP_weight_induction (Q : TP → Prop) (h0 : Q 0) (hadd : ∀ x y, Q x → Q y → Q (x + y))
    (hhom : ∀ (k : ℤ) x, x ∈ plusModule.weight (k : ℂ) → Q x) (t : TP) : Q t := by
  have ht : t ∈ ⨆ k : ℤ, plusModule.weight (k : ℂ) := by
    rw [iSup_plusModule_weight_int]; trivial
  induction ht using Submodule.iSup_induction' with
  | mem k x hx => exact hhom k x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy

/-- **DGM (4.22), unconditional**: for all `t₁, t₂ ∈ TP`,
`(z₁−z₂)ᴺ [W̄(t₁,z₁)W(t₂,z₂) − W̄(t₂,z₂)W(t₁,z₁)] = 0` on `V_Λ^+` for some `N`. -/
theorem leechWbar_VPBlockLocal (t₁ t₂ : TP) : VPBlockLocal leechWbar t₁ t₂ := by
  rw [VPBlockLocal_iff]
  have hzl : ∀ s, VPfun 0 s = 0 := fun s => by
    have h := VPfun_add_left 0 0 s; rw [add_zero] at h; exact add_eq_left.mp h.symm
  have hzr : ∀ t, VPfun t 0 = 0 := fun t => by
    have h := VPfun_add_right t 0 0; rw [add_zero] at h; exact add_eq_left.mp h.symm
  -- first for homogeneous `t₂`
  have hhom2 : ∀ (b : ℤ) s, s ∈ plusModule.weight (b : ℂ) →
      ∀ t, ∃ N : ℕ, mulBySubPow N (VPfun t s) = 0 := by
    intro b s hs t
    refine TP_weight_induction (fun t => ∃ N : ℕ, mulBySubPow N (VPfun t s) = 0)
      ⟨0, by rw [hzl, map_zero]⟩ (fun x y hx hy => ?_)
      (fun a x hx => ⟨_, VPBlockLocal_homog hx hs⟩) t
    beta_reduce at hx hy ⊢; rw [VPfun_add_left]; exact exists_mulBySubPow_add hx hy
  refine TP_weight_induction (fun s => ∃ N : ℕ, mulBySubPow N (VPfun t₁ s) = 0)
    ⟨0, by rw [hzr, map_zero]⟩ (fun x y hx hy => ?_)
    (fun b s hs => hhom2 b s hs t₁) t₂
  beta_reduce at hx hy ⊢; rw [VPfun_add_right]; exact exists_mulBySubPow_add hx hy

end VOA.Moonshine.M8h0
