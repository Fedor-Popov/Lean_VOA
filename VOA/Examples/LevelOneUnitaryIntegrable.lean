/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LevelOneUnitarySl2
import VOA.Examples.AffineSl2BelowCriticalCompact
import VOA.Examples.AffineSl2BelowCriticalRigidity
import VOA.Examples.AffineSl2ChargeDecomposition
import VOA.Examples.AffineSl2Singular
import VOA.Examples.AffineSl2Reconstruction
import VOA.Examples.ConcreteHodgeSymmetry

/-!
# Integrability of `L_1(sl₂)`: the null vector, local nilpotency, and the charge bound

All statements are about the universal vacuum module `V^k(sl₂)` with its maximal graded ideal
`I = maxGradedIdeal`; "`v ∈ I`" means "`v = 0` in the simple quotient `L_k(sl₂)`".

## General level (`k + 2 ≠ 0`)

* `J_mem_maxIdeal` — current modes preserve `I`;
* `form_eq_zero_of_mem_right` — `I` lies in the right radical of the canonical form;
* `mem_maxIdeal_of_pos_kill` — a vector of positive weight killed modulo `I` by every positive
  current mode lies in `I`;
* `J_E_mem_joint`, `J_F_mem_joint`, `J_H_mem_joint`, `exists_J_mem_joint` — the current modes
  shift the joint `(L₀, h₀)` spaces by `(-m, ±2, 0)`;
* `joint_eq_zero_of_charge` — `jointSpace n μ = 0` when `|μ| > 2n`.

## Level one

* `nullVector_mem` — `(e₋₁)²|0⟩ ∈ I` (it is singular at `k = 1`);
* `nilMod_E` — `e₋₁` acts locally nilpotently on `L_1(sl₂)`;
* `charge_sq_le` — **the charge bound**: a joint vector of energy `n` and charge `μ` that is
  nonzero in `L_1(sl₂)` has `μ² ≤ 4n`.  Proof: the reflection lemma `mem_of_F_pow_mem` for the
  affine `sl₂`-triple `(e₋₁, f₁, h₀ - 1)` moves charge `μ ≥ 2` at energy `n` to charge `2 - μ`
  at energy `n + 1 - μ`, and strong induction on the energy; negative charges by the compact
  conjugation `ρ`, which flips the charge.
-/

namespace VOA.LevelOneUnitary

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Sing
open Module (End)

noncomputable section

/-! ### General level -/

section General

variable {k : ℂ} (hk : k + 2 ≠ 0)

local notation "Imax" => QuotVOA.maxGradedIdeal (universal k hk)

theorem J_mem_maxIdeal (a : Fin 3) (n : ℤ) {v : WakModule k} (hv : v ∈ Imax) :
    J k a n v ∈ Imax := by
  have h := QuotVOA.maxGradedIdeal_isIdeal (universal k hk) (currentState k a) v n hv
  rwa [smul_currentState_eq_J] at h

theorem form_eq_zero_of_mem_right {y : WakModule k} (hy : y ∈ Imax) (x : WakModule k) :
    (universalForm k hk).form x y = 0 := by
  rw [ConcreteHodge.universalForm_isSymmetric k hk]
  exact (LiRadical.mem_maxGradedIdeal_iff (universalForm_invariant k hk)
    (universalForm_normalized k hk)).mp hy x

theorem form_eq_zero_of_mem_left {y : WakModule k} (hy : y ∈ Imax) (x : WakModule k) :
    (universalForm k hk).form y x = 0 := by
  rw [ConcreteHodge.universalForm_isSymmetric k hk]; exact form_eq_zero_of_mem_right hk hy x

/-- A positive-weight vector killed modulo `I` by every positive current mode lies in `I`. -/
theorem mem_maxIdeal_of_pos_kill {E : ℤ} (hE : 0 < E) {y : WakModule k}
    (hy : y ∈ (universal k hk).grading E)
    (hkill : ∀ (a : Fin 3) (m : ℕ), 0 < m → J k a (m : ℤ) y ∈ Imax) : y ∈ Imax := by
  rw [LiRadical.mem_maxGradedIdeal_iff_grading (universalForm_invariant k hk)
    (universalForm_normalized k hk) hy]
  intro x hx
  rw [ConcreteHodge.universalForm_isSymmetric k hk]
  have hx' := grading_le_span_creation hk hE hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, x', hm, -, rfl⟩ := hz
      rw [universalForm_current_adj hk, neg_neg, form_eq_zero_of_mem_right hk (hkill a m hm),
        neg_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

theorem eq_zero_of_grading_neg {n : ℤ} (hn : n < 0) {y : WakModule k}
    (hy : y ∈ (universal k hk).grading n) : y = 0 := by
  rw [(universal k hk).positivity n hn] at hy
  exact (Submodule.mem_bot ℂ).mp hy

theorem vacuum_mem_grading_zero : vacuumA k ∈ (universal k hk).grading 0 := by
  rw [(universal k hk).vacuum_grade]
  exact Submodule.mem_span_singleton_self _

/-! #### Joint spaces -/

theorem L0_of_mem_grading {n : ℤ} {y : WakModule k} (hy : y ∈ (universal k hk).grading n) :
    (universal k hk).L 0 y = (n : ℂ) • y :=
  (universal k hk).L_zero_grading y hy

theorem joint_le_grading {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ) :
    y ∈ (universal k hk).grading n :=
  jointSpace_le_grading k hk n μ hy

theorem J_E_mem_joint (m : ℤ) {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ) :
    J k colE m y ∈ jointSpace k hk (n - m) (μ + 2) := by
  have hH := ((mem_jointSpace_iff k hk n μ y).mp hy).2
  rw [mem_jointSpace_iff]
  refine ⟨L0_of_mem_grading hk (J_mem_grading hk colE m (joint_le_grading hk hy)), ?_⟩
  rw [HEs k 0 m m (by ring), hH, map_smul]
  push_cast; module

theorem J_F_mem_joint (m : ℤ) {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ) :
    J k colF m y ∈ jointSpace k hk (n - m) (μ - 2) := by
  have hH := ((mem_jointSpace_iff k hk n μ y).mp hy).2
  rw [mem_jointSpace_iff]
  refine ⟨L0_of_mem_grading hk (J_mem_grading hk colF m (joint_le_grading hk hy)), ?_⟩
  rw [HFs k 0 m m (by ring), hH, map_smul]
  push_cast; module

theorem J_H_mem_joint (m : ℤ) {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ) :
    J k colH m y ∈ jointSpace k hk (n - m) μ := by
  have hH := ((mem_jointSpace_iff k hk n μ y).mp hy).2
  rw [mem_jointSpace_iff]
  refine ⟨L0_of_mem_grading hk (J_mem_grading hk colH m (joint_le_grading hk hy)), ?_⟩
  by_cases hm : (0 : ℤ) + m = 0
  · have hm0 : m = 0 := by omega
    subst hm0
    rw [hH, map_smul, hH]
  · rw [HHs k 0 m hm, hH, map_smul]

theorem exists_J_mem_joint (a : Fin 3) (m : ℤ) {n μ : ℤ} {y : WakModule k}
    (hy : y ∈ jointSpace k hk n μ) : ∃ μ' : ℤ, J k a m y ∈ jointSpace k hk (n - m) μ' := by
  fin_cases a
  · exact ⟨_, J_E_mem_joint hk m hy⟩
  · exact ⟨_, J_F_mem_joint hk m hy⟩
  · exact ⟨_, J_H_mem_joint hk m hy⟩

theorem joint_eq_zero_of_charge {n μ : ℤ} (h : μ < -(2 * n) ∨ 2 * n < μ) {y : WakModule k}
    (hy : y ∈ jointSpace k hk n μ) : y = 0 := by
  have hempty : IsEmpty (JointIndex n μ) := by
    refine ⟨fun i => ?_⟩
    have hb := currentCharge_bounds i.val
    rw [i.property.1, i.property.2] at hb
    omega
  rw [jointSpace, Set.range_eq_empty, Submodule.span_empty] at hy
  exact (Submodule.mem_bot ℂ).mp hy

theorem charge_window_of_ne {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ)
    (hne : y ≠ 0) : -(2 * n) ≤ μ ∧ μ ≤ 2 * n := by
  by_contra h
  exact hne (joint_eq_zero_of_charge hk (by omega) hy)

/-! #### The compact conjugation on joint spaces -/

variable {R : RealStructure (universal k hk)} (hR : IsCompactRealStructure R)
include hR

theorem rho_mem_joint {n μ : ℤ} {y : WakModule k} (hy : y ∈ jointSpace k hk n μ) :
    R.rho y ∈ jointSpace k hk n (-μ) := by
  have hH := ((mem_jointSpace_iff k hk n μ y).mp hy).2
  rw [mem_jointSpace_iff]
  refine ⟨L0_of_mem_grading hk (hR.rho_mem_grading (joint_le_grading hk hy)), ?_⟩
  have h := hR.rho_J colH 0 y
  have h2 : J k colH 0 (R.rho y) = -R.rho (J k colH 0 y) := by
    rw [h, neg_neg]; rfl
  rw [h2, hH, R.antilinear, map_intCast]
  push_cast
  rw [neg_smul]

end General

/-! ### Level one -/

section LevelOne

variable (hk : (1 : ℂ) + 2 ≠ 0)

local notation "Imax" => QuotVOA.maxGradedIdeal (universal 1 hk)

/-- The level-one null vector `(e₋₁)²|0⟩`. -/
def nullVector : WakModule 1 := J 1 colE (-1) (J 1 colE (-1) (vacuumA 1))

private theorem nullVector_kill_E (m : ℤ) (hm : 0 ≤ m) : J 1 colE m nullVector = 0 := by
  rw [nullVector, EEs 1 m (-1) (J 1 colE (-1) (vacuumA 1)), EEs 1 m (-1) (vacuumA 1),
    J_vac 1 colE hm, map_zero, map_zero]

private theorem nullVector_kill_H (m : ℤ) (hm : 1 ≤ m) : J 1 colH m nullVector = 0 := by
  rw [nullVector, HEs 1 m (-1) (m - 1) (by ring) (J 1 colE (-1) (vacuumA 1)),
    HEs 1 m (-1) (m - 1) (by ring) (vacuumA 1), J_vac 1 colH (by omega),
    J_vac 1 colE (by omega : (0 : ℤ) ≤ m - 1), EEs 1 (m - 1) (-1) (vacuumA 1),
    J_vac 1 colE (by omega : (0 : ℤ) ≤ m - 1)]
  simp

private theorem nullVector_kill_F1 : J 1 colF 1 nullVector = 0 := by
  rw [nullVector, FEz 1 1 (-1) (by norm_num) (J 1 colE (-1) (vacuumA 1)), F1E1, H0E1]
  rw [map_smul]
  push_cast
  module

private theorem nullVector_kill_F2 : J 1 colF 2 nullVector = 0 := by
  rw [nullVector, FEs 1 2 (-1) 1 (by norm_num) (by norm_num) (J 1 colE (-1) (vacuumA 1)),
    FEs 1 2 (-1) 1 (by norm_num) (by norm_num) (vacuumA 1), H1E1,
    J_vac 1 colF (by norm_num : (0 : ℤ) ≤ 2), J_vac 1 colH (by norm_num : (0 : ℤ) ≤ 1)]
  simp

theorem nullVector_mem_grading : nullVector ∈ (universal 1 hk).grading 2 := by
  have h := J_mem_grading hk colE (-1) (J_mem_grading hk colE (-1)
    (vacuum_mem_grading_zero hk))
  norm_num at h
  exact h

/-- **The level-one null vector** `(e₋₁)²|0⟩` vanishes in `L_1(sl₂)`. -/
theorem nullVector_mem : nullVector ∈ Imax := by
  apply mem_maxIdeal_of_pos_kill hk (by norm_num : (0 : ℤ) < 2) (nullVector_mem_grading hk)
  intro a m hm
  by_cases h3 : 3 ≤ m
  · have hg := J_mem_grading hk a (m : ℤ) (nullVector_mem_grading hk)
    rw [eq_zero_of_grading_neg hk (by omega) hg]
    exact Submodule.zero_mem _
  · fin_cases a
    · change J 1 colE (m : ℤ) nullVector ∈ Imax
      rw [nullVector_kill_E (m : ℤ) (by omega)]
      exact Submodule.zero_mem _
    · change J 1 colF (m : ℤ) nullVector ∈ Imax
      interval_cases m
      · rw [Nat.cast_one, nullVector_kill_F1]; exact Submodule.zero_mem _
      · rw [Nat.cast_ofNat, nullVector_kill_F2]; exact Submodule.zero_mem _
    · change J 1 colH (m : ℤ) nullVector ∈ Imax
      rw [nullVector_kill_H (m : ℤ) (by omega)]
      exact Submodule.zero_mem _

/-- The raising operator `e₋₁` of the affine simple root `α₀`. -/
abbrev Eop : End ℂ (WakModule 1) := J 1 colE (-1)

theorem nilMod_J_E (n : ℤ) : ∀ y, NilMod Eop Imax y → NilMod Eop Imax (J 1 colE n y) :=
  nilMod_of_comm (Y := 0) (fun v hv => J_mem_maxIdeal hk _ _ hv)
    (fun v hv => J_mem_maxIdeal hk _ _ hv)
    (fun v => by rw [LinearMap.zero_apply, add_zero]; exact EEs 1 (-1) n v)
    (fun y _ => by rw [LinearMap.zero_apply]; exact nilMod_zero)

theorem nilMod_J_H (n : ℤ) : ∀ y, NilMod Eop Imax y → NilMod Eop Imax (J 1 colH n y) :=
  nilMod_of_comm (Y := (-2 : ℂ) • J 1 colE (-1 + n)) (fun v hv => J_mem_maxIdeal hk _ _ hv)
    (fun v hv => J_mem_maxIdeal hk _ _ hv)
    (fun v => by
      rw [EHs 1 (-1) n (-1 + n) rfl v, LinearMap.smul_apply]; module)
    (fun y hy => by
      rw [LinearMap.smul_apply]; exact nilMod_smul _ (nilMod_J_E hk _ y hy))

theorem nilMod_J_F (n : ℤ) : ∀ y, NilMod Eop Imax y → NilMod Eop Imax (J 1 colF n y) := by
  by_cases hn : -1 + n = 0
  · exact nilMod_of_comm (Y := J 1 colH 0 + ((-1 : ℂ)) • (1 : End ℂ (WakModule 1)))
      (fun v hv => J_mem_maxIdeal hk _ _ hv) (fun v hv => J_mem_maxIdeal hk _ _ hv)
      (fun v => by
        rw [EFz 1 (-1) n hn v, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        push_cast; module)
      (fun y hy => by
        rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        exact nilMod_add (fun v hv => J_mem_maxIdeal hk _ _ hv) (nilMod_J_H hk 0 y hy)
          (nilMod_smul _ hy))
  · exact nilMod_of_comm (Y := J 1 colH (-1 + n))
      (fun v hv => J_mem_maxIdeal hk _ _ hv) (fun v hv => J_mem_maxIdeal hk _ _ hv)
      (fun v => EFs 1 (-1) n (-1 + n) rfl hn v)
      (fun y hy => nilMod_J_H hk _ y hy)

theorem nilMod_J (a : Fin 3) (n : ℤ) (y : WakModule 1) (hy : NilMod Eop Imax y) :
    NilMod Eop Imax (J 1 a n y) := by
  fin_cases a
  · exact nilMod_J_E hk n y hy
  · exact nilMod_J_F hk n y hy
  · exact nilMod_J_H hk n y hy

/-- **Local nilpotency of `e₋₁` on `L_1(sl₂)`.** -/
theorem nilMod_E (y : WakModule 1) : NilMod Eop Imax y := by
  have hwords : ∀ w, NilMod Eop Imax (wordStateA 1 w) := by
    intro w
    induction w with
    | nil =>
        refine ⟨2, ?_⟩
        rw [wordStateA_nil, pow_two, Module.End.mul_apply]
        exact nullVector_mem hk
    | cons b w ih =>
        rw [wordStateA_cons]
        exact nilMod_J hk _ _ _ ih
  have hy : y ∈ Submodule.span ℂ (Set.range (wordStateA 1)) := by
    rw [wordStateA_span]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact hwords w
  | zero => exact nilMod_zero
  | add a b _ _ ha hb => exact nilMod_add (fun v hv => J_mem_maxIdeal hk _ _ hv) ha hb
  | smul c a _ ha => exact nilMod_smul c ha

/-! #### The charge bound -/

/-- The lowering operator `f₁` of the affine simple root `α₀`. -/
abbrev Fop : End ℂ (WakModule 1) := J 1 colF 1

/-- The coroot `h₀ - k` of `α₀` at `k = 1`. -/
abbrev Hop : End ℂ (WakModule 1) := J 1 colH 0 - 1

theorem Eop_Fop (v : WakModule 1) : Eop (Fop v) = Fop (Eop v) + Hop v := by
  rw [EFz 1 (-1) 1 (by norm_num) v, LinearMap.sub_apply, Module.End.one_apply]
  push_cast; module

theorem Hop_Eop (v : WakModule 1) : Hop (Eop v) = Eop (Hop v) + (2 : ℂ) • Eop v := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [HEs 1 0 (-1) (-1) (by norm_num) v]
  abel

theorem Hop_Fop (v : WakModule 1) : Hop (Fop v) = Fop (Hop v) - (2 : ℂ) • Fop v := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [HFs 1 0 1 1 (by norm_num) v]
  abel

theorem Fop_pow_mem_joint (j : ℕ) {n μ : ℤ} {y : WakModule 1}
    (hy : y ∈ jointSpace 1 hk n μ) : (Fop ^ j) y ∈ jointSpace 1 hk (n - j) (μ - 2 * j) := by
  induction j with
  | zero => simpa using hy
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := J_F_mem_joint hk 1 ih
      convert h using 2 <;> push_cast <;> ring

/-- The charge-bound statement at energy `n`. -/
def ChargeBoundAt (n : ℤ) : Prop :=
  ∀ (μ : ℤ) (y : WakModule 1), y ∈ jointSpace 1 hk n μ → y ∉ Imax → μ ^ 2 ≤ 4 * n

/-- The reflection step for a charge `μ ≥ 2`. -/
theorem charge_sq_le_step {n : ℤ} (hlow : ∀ n' < n, ChargeBoundAt hk n') {μ : ℤ} (hμ : 2 ≤ μ)
    {y : WakModule 1} (hy : y ∈ jointSpace 1 hk n μ) (hyI : y ∉ Imax) : μ ^ 2 ≤ 4 * n := by
  set lam : ℕ := (μ - 1).toNat with hlam
  have hlamz : (lam : ℤ) = μ - 1 := by rw [hlam]; omega
  have hH : Hop y = (lam : ℂ) • y := by
    have h := ((mem_jointSpace_iff 1 hk n μ y).mp hy).2
    rw [LinearMap.sub_apply, Module.End.one_apply, h]
    have : (lam : ℂ) = (μ : ℂ) - 1 := by exact_mod_cast hlamz
    rw [this, sub_smul, one_smul]
  have hF : (Fop ^ lam) y ∉ Imax := by
    intro hF
    obtain ⟨N, hN⟩ := nilMod_E hk y
    exact hyI (mem_of_F_pow_mem Eop_Fop Hop_Eop Hop_Fop
      (fun v hv => J_mem_maxIdeal hk _ _ hv) (fun v hv => J_mem_maxIdeal hk _ _ hv)
      N lam y hH hN hF)
  have hmem := Fop_pow_mem_joint hk lam hy
  rw [hlamz] at hmem
  have hne : (Fop ^ lam) y ≠ 0 := fun h => hF (h ▸ Submodule.zero_mem _)
  have hE' : 0 ≤ n - (μ - 1) := by
    by_contra hneg
    exact hne (eq_zero_of_grading_neg hk (by omega) (joint_le_grading hk hmem))
  have hb := hlow (n - (μ - 1)) (by omega) _ _ hmem hF
  nlinarith

variable {hk}

/-- **The charge bound for `L_1(sl₂)`**: a joint vector of energy `n` and charge `μ` which is
nonzero in the simple quotient satisfies `μ² ≤ 4n`. -/
theorem charge_sq_le {R : RealStructure (universal 1 hk)} (hR : IsCompactRealStructure R)
    (hρI : ∀ y ∈ Imax, R.rho y ∈ Imax) (hρρ : ∀ y, R.rho (R.rho y) = y) :
    ∀ n : ℤ, ChargeBoundAt hk n := by
  suffices H : ∀ N : ℕ, ∀ n : ℤ, n ≤ N → ChargeBoundAt hk n by
    intro n
    exact H n.toNat n (Int.self_le_toNat n)
  intro N
  induction N with
  | zero =>
      intro n hn μ y hy hyI
      have hne : y ≠ 0 := fun h => hyI (h ▸ Submodule.zero_mem _)
      rcases lt_or_eq_of_le hn with hlt | heq
      · exact absurd (eq_zero_of_grading_neg hk (by exact_mod_cast hlt)
          (joint_le_grading hk hy)) hne
      · have hw := charge_window_of_ne hk hy hne
        push_cast at heq
        subst heq
        have : μ = 0 := by omega
        subst this; norm_num
  | succ N ih =>
      intro n hn
      rcases le_or_gt n N with hle | hgt
      · exact ih n hle
      have hlow : ∀ n' < n, ChargeBoundAt hk n' := fun n' hn' => ih n' (by omega)
      intro μ y hy hyI
      rcases le_or_gt 2 μ with h2 | h2
      · exact charge_sq_le_step hk hlow h2 hy hyI
      rcases le_or_gt μ (-2) with h3 | h3
      · have hρy := rho_mem_joint hk hR hy
        have hρI' : R.rho y ∉ Imax := fun h => hyI (by simpa [hρρ] using hρI _ h)
        have := charge_sq_le_step hk hlow (by omega) hρy hρI'
        nlinarith
      · have h1 : 1 ≤ n := by omega
        nlinarith

end LevelOne

end

end VOA.LevelOneUnitary
