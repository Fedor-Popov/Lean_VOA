/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.WbarCore

/-!
# `W̄`: intertwining commutator, locality and translation covariance  (M8c, `W̄` part 5)

Hypotheses (all displayed, none hidden):

* on `𝒱`: `GradedOrth W BV`, `GradedNondeg W BV`, and FHL invariance `VInv W BV` (the shape of
  `InvariantForm.IsFullyInvariant`); `L₁𝒱₁ = 0` (for the quasi-primary decomposition `qpDecomp`);
* on `M`: `WeightOrth N BM` and FHL invariance `FHLInv N BM wt u` for every homogeneous `u`.

Results:

* `WbarMode_comm_qp` — the commutator formula for quasi-primary homogeneous `u`, by adjunction
  from the form-free `Wdag_comm_qp`.
* `WbarMode_comm` — for **all** `u ∈ 𝒱`, all `m n`, and any `J` past the truncation of `u` on `t`:
  `u₍ₘ₎ W̄(t)₍ₙ₎a − W̄(t)₍ₙ₎(u₍ₘ₎a) = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎a`
  (quasi-primary case, closure under `+`, `•`, `L₋₁` (`(L₋₁u)₍ₘ₎ = −m u₍ₘ₋₁₎`), and `qpDecomp`).
* `Wbar_local` — `(z₁−z₂)ᴺ [Y(u,z₁) W̄(t,z₂) − W̄(t,z₂) Y_M(u,z₁)] = 0` in
  `Hom(M,𝒱)⟦z₁^±,z₂^±⟧` (the `c'`-hypothesis shape of `VnatBlock.local_diag_off`).
* `Wbar_homCov` — `L₋₁ W̄(t,z)ₖ − W̄(t,z)ₖ L₋₁ᴹ = (k+1) W̄(t,z)ₖ₊₁` (the `HomCov` shape).

## Status
All declarations proved; no `sorry`/axioms.  Conditional only on the displayed hypotheses.
-/

namespace VOA.Moonshine.SkewAdjoint

open Module (End Dual)
open VertexOperatorAlgebra SkewIntertwiner InvForm
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- FHL invariance of a form on the VOA itself (the shape of `InvariantForm.IsFullyInvariant`). -/
def VInv (W : VertexOperatorAlgebra 𝒱) (BV : LinearMap.BilinForm ℂ 𝒱) : Prop :=
  ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (a b : 𝒱),
    BV (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          BV a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

theorem vInv_of_isFullyInvariant (B : InvariantForm W) (hB : B.IsFullyInvariant) :
    VInv W B.form := hB

/-- The quasi-primary collapse of an `L₁`-tower sum. -/
theorem sum_L1_qp {X : Type*} [AddCommGroup X] [Module ℂ X] {u : 𝒱} (hqp : W.L 1 u = 0) (k : ℕ)
    (F : ℕ → 𝒱 → X) (hF : ∀ j, F j 0 = 0) :
    ∑ j ∈ Finset.range (k + 1), ((j.factorial : ℂ)⁻¹) • F j (((W.L 1) ^ j) u) = F 0 u := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, hqp, map_zero, hF, smul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h

variable {BV : LinearMap.BilinForm ℂ 𝒱} {N : OrdVModule W M} {BM : LinearMap.BilinForm ℂ M}
  {hO : WeightOrth N BM}

/-- The commutator formula for a quasi-primary homogeneous `u` and `t ∈ M_w`. -/
theorem WbarMode_comm_qp (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) (hVinv : VInv W BV)
    (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p) (hqp : W.L 1 u = 0) {w : ℤ} {t : M}
    (ht : t ∈ N.weight (w : ℂ)) (m n : ℤ) (J : ℕ) (hJ : ∀ j : ℕ, J ≤ j → N.act u j t = 0)
    (a : M) :
    W.smul u m (WbarMode BV N BM hO n t a) - WbarMode BV N BM hO n t (N.act u m a)
      = ∑ r ∈ Finset.range J, gBinom m r • WbarMode BV N BM hO (m + n - r) (N.act u r t) a := by
  refine eq_of_form hVo hVnd fun φ => ?_
  have h1 : BV (W.smul u m (WbarMode BV N BM hO n t a)) φ
      = (-1 : ℂ) ^ p • BM a (Wdag N n t (W.smul u (2 * p - m - 2) φ)) := by
    rw [hVinv p u hu m, sum_L1_qp hqp _ (fun j v => BV (WbarMode BV N BM hO n t a)
      (W.smul v (2 * p - m - 2 - (j : ℤ)) φ)) (fun j => by simp), form_WbarMode hVo hVnd]
    simp
  have h2 : BV (WbarMode BV N BM hO n t (N.act u m a)) φ
      = (-1 : ℂ) ^ p • BM a (N.act u (2 * p - m - 2) (Wdag N n t φ)) := by
    rw [form_WbarMode hVo hVnd, WeakModule.act_def, hMinv p u hu m a, sum_L1_qp hqp _
      (fun j v => BM a (mode (N.YM v) (2 * p - m - 2 - (j : ℤ)) (Wdag N n t φ)))
      (fun j => by dsimp only; rw [map_zero, mode_zero, LinearMap.zero_apply, map_zero])]
    simp
  rw [map_sub, LinearMap.sub_apply, h1, h2, ← smul_sub, ← map_sub, ← map_smul,
    Wdag_comm_qp N hu hqp ht m n J hJ φ, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, form_WbarMode hVo hVnd]

/-! ## Extension to all states -/

/-- The commutator formula at `u`, for all `J` beyond a `t`-dependent bound. -/
def CommGood (BV : LinearMap.BilinForm ℂ 𝒱) (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M)
    (hO : WeightOrth N BM) (u : 𝒱) : Prop :=
  ∀ t : M, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ (m n : ℤ) (a : M),
    W.smul u m (WbarMode BV N BM hO n t a) - WbarMode BV N BM hO n t (N.act u m a)
      = ∑ r ∈ Finset.range J, gBinom m r • WbarMode BV N BM hO (m + n - r) (N.act u r t) a

theorem commGood_add {u v : 𝒱} (hu : CommGood BV N BM hO u) (hv : CommGood BV N BM hO v) :
    CommGood BV N BM hO (u + v) := by
  intro t
  obtain ⟨J₁, h₁⟩ := hu t
  obtain ⟨J₂, h₂⟩ := hv t
  refine ⟨max J₁ J₂, fun J hJ m n a => ?_⟩
  rw [W.smul_add_left, WeakModule.act_add_left, map_add]
  have e1 := h₁ J (le_of_max_le_left hJ) m n a
  have e2 := h₂ J (le_of_max_le_right hJ) m n a
  simp only [WeakModule.act_add_left, WbarMode_add, LinearMap.add_apply, smul_add,
    Finset.sum_add_distrib, ← e1, ← e2]
  abel

theorem commGood_smul (c : ℂ) {u : 𝒱} (hu : CommGood BV N BM hO u) :
    CommGood BV N BM hO (c • u) := by
  intro t
  obtain ⟨J₁, h₁⟩ := hu t
  refine ⟨J₁, fun J hJ m n a => ?_⟩
  rw [W.smul_smul_left, act_smul_left, map_smul]
  simp only [act_smul_left, WbarMode_smul, LinearMap.smul_apply, smul_comm _ c,
    ← Finset.smul_sum, ← h₁ J hJ m n a, smul_sub]

theorem commGood_zero : CommGood BV N BM hO (0 : 𝒱) := by
  intro t
  refine ⟨0, fun J _ m n a => ?_⟩
  have h0 : ∀ (k : ℤ) (x : M), N.act (0 : 𝒱) k x = 0 := fun k x => by
    rw [WeakModule.act_def, map_zero, mode_zero, LinearMap.zero_apply]
  simp only [h0, W.smul_zero_left, map_zero, sub_zero, WbarMode_zero, LinearMap.zero_apply,
    smul_zero, Finset.sum_const_zero]

theorem commGood_Lm1 {c : 𝒱} (hc : CommGood BV N BM hO c) :
    CommGood BV N BM hO (W.L (-1) c) := by
  intro t
  obtain ⟨J₀, h₀⟩ := hc t
  refine ⟨J₀ + 1, fun J hJ m n a => ?_⟩
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  rw [smul_Lneg1_shift, act_T_covariance, map_smul, ← smul_sub,
    h₀ J' (by omega) (m - 1) n a, Finset.sum_range_succ', Finset.smul_sum]
  have hz : gBinom m 0 • WbarMode BV N BM hO (m + n - ((0 : ℕ) : ℤ))
      (N.act (W.L (-1) c) ((0 : ℕ) : ℤ) t) a = 0 := by
    rw [act_T_covariance]; simp [WbarMode_zero]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [act_T_covariance, WbarMode_smul, LinearMap.smul_apply, smul_smul, smul_smul]
  have hb := gBinom_succ_mul' m r
  rw [show ((r + 1 : ℕ) : ℤ) - 1 = r by push_cast; ring,
    show m + n - ((r + 1 : ℕ) : ℤ) = m - 1 + n - r by push_cast; ring]
  congr 1
  push_cast
  linear_combination hb

/-- **The commutator formula for every state**, given `L₁𝒱₁ = 0`. -/
theorem commGood_all (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) (hVinv : VInv W BV)
    (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    (hqpV : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u : 𝒱) : CommGood BV N BM hO u := by
  -- quasi-primary homogeneous states
  have hqpGood : ∀ {p : ℤ} {u : 𝒱}, u ∈ W.grading p → W.L 1 u = 0 → CommGood BV N BM hO u := by
    intro p u hu hqp t
    have ht : t ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
    induction ht using Submodule.iSup_induction' with
    | mem α t ht =>
      obtain ⟨T₀, hT₀⟩ := N.truncation u t
      refine ⟨T₀.toNat, fun J hJ m n a => ?_⟩
      have hJ' : ∀ j : ℕ, J ≤ j → N.act u j t = 0 := fun j hj => hT₀ _ (by omega)
      by_cases hα : ∃ w : ℤ, (w : ℂ) = α
      · obtain ⟨w, rfl⟩ := hα
        exact WbarMode_comm_qp hVo hVnd hVinv hMinv hu hqp ht m n J hJ' a
      · have hα' : ∀ w : ℤ, (w : ℂ) ≠ α := fun w hw => hα ⟨w, hw⟩
        rw [WbarMode_nonint_left n ht hα', LinearMap.zero_apply, LinearMap.zero_apply,
          W.smul_zero_right, sub_zero]
        refine (Finset.sum_eq_zero fun r _ => ?_).symm
        have hmem : N.act u r t ∈ N.weight (α + (p : ℂ) - ((r : ℤ) : ℂ) - 1) :=
          mode_mem_weight N hu ht r
        rw [WbarMode_nonint_left _ hmem (fun w hw => hα ⟨w - p + r + 1, by
          rw [← sub_eq_zero] at hw ⊢; push_cast at hw ⊢; rw [← hw]; ring⟩), LinearMap.zero_apply,
          smul_zero]
    | zero =>
      refine ⟨0, fun J _ m n a => ?_⟩
      simp [WbarMode_zero]
    | add t t' _ _ h1 h2 =>
      obtain ⟨J₁, e1⟩ := h1
      obtain ⟨J₂, e2⟩ := h2
      refine ⟨max J₁ J₂, fun J hJ m n a => ?_⟩
      rw [WbarMode_add, LinearMap.add_apply, LinearMap.add_apply, W.smul_add_right]
      simp only [WeakModule.act_add_right, WbarMode_add, LinearMap.add_apply, smul_add,
        Finset.sum_add_distrib]
      rw [← e1 J (le_of_max_le_left hJ) m n a, ← e2 J (le_of_max_le_right hJ) m n a]
      abel
  -- homogeneous states, by induction on the weight
  have hhom : ∀ (k : ℕ) {u : 𝒱}, u ∈ W.grading (k : ℤ) → CommGood BV N BM hO u := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hu
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        refine hqpGood hu ?_
        have h := L_one_lower W hu
        rw [W.positivity _ (by norm_num)] at h
        exact (Submodule.mem_bot ℂ).mp h
      · obtain ⟨a₀, c, ha₀, hqp₀, hc, rfl⟩ := qpDecomp W hqpV (p := (k : ℤ)) (by omega) hu
        refine commGood_add (hqpGood ha₀ hqp₀) (commGood_Lm1 (ih (k - 1) (by omega) ?_))
        rwa [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega]
  have hu : u ∈ ⨆ k, W.grading k := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem k u hu =>
    by_cases hk : 0 ≤ k
    · obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' := ⟨k.toNat, by omega⟩
      exact hhom k hu
    · rw [W.positivity k (by omega), Submodule.mem_bot] at hu
      rw [hu]; exact commGood_zero
  | zero => exact commGood_zero
  | add u v _ _ hu hv => exact commGood_add hu hv

/-- **`Wbar_comm`: the intertwining commutator formula of `W̄`** (all `u ∈ 𝒱`, all `m, n`), for
any `J` past the truncation of `u` on `t`:
`u₍ₘ₎ W̄(t)₍ₙ₎a − W̄(t)₍ₙ₎(u₍ₘ₎a) = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎a`. -/
theorem WbarMode_comm (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) (hVinv : VInv W BV)
    (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    (hqpV : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u : 𝒱) (m : ℤ) (t : M) (n : ℤ) (a : M)
    (J : ℕ) (hJ : ∀ j : ℕ, J ≤ j → N.act u j t = 0) :
    W.smul u m (WbarMode BV N BM hO n t a) - WbarMode BV N BM hO n t (N.act u m a)
      = ∑ r ∈ Finset.range J, gBinom m r • WbarMode BV N BM hO (m + n - r) (N.act u r t) a := by
  obtain ⟨J₀, h₀⟩ := commGood_all hVo hVnd hVinv hMinv hqpV u t
  rw [h₀ (max J J₀) (le_max_right _ _) m n a]
  refine (Finset.sum_subset (Finset.range_subset_range.2 (le_max_left _ _)) fun r _ hr => ?_).symm
  rw [Finset.mem_range, not_lt] at hr
  rw [hJ r hr, WbarMode_zero, LinearMap.zero_apply, smul_zero]

/-! ## Locality and translation covariance -/

/-- The commutator distribution `[Y(u,z₁), W̄(t,z₂)]` in `Hom(M, 𝒱)`. -/
noncomputable def wbarBracket (BV : LinearMap.BilinForm ℂ 𝒱) (N : OrdVModule W M)
    (BM : LinearMap.BilinForm ℂ M) (hO : WeightOrth N BM) (u : 𝒱) (t : M) :
    FormalDist₂ (M →ₗ[ℂ] 𝒱) :=
  fun a b => (W.Y u a).comp (Wbar BV N BM hO t b) - (Wbar BV N BM hO t b).comp (N.YM u a)

theorem wbarBracket_eq_sum (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV)
    (hVinv : VInv W BV) (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    (hqpV : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u : 𝒱) (t : M) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → N.act u j t = 0) :
    wbarBracket BV N BM hO u t = ∑ r ∈ Finset.range J,
      jumpDist r (fun k => WbarMode BV N BM hO (-k - 2 - r) (N.act u r t)) := by
  refine FormalDist₂.ext fun a b => ?_
  rw [fd2_finset_sum_apply]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply]
  have hc := WbarMode_comm (hO := hO) hVo hVnd hVinv hMinv hqpV u (-a - 1) t (-b - 1) x J hJ
  have h1 : W.smul u (-a - 1) = W.Y u a := by
    ext y; rw [PreVertexAlgebra.smul_def, mode_apply, show -(-a - 1) - 1 = a by ring]
  have h2 : N.act u (-a - 1) x = N.YM u a x := by
    rw [WeakModule.act_def, mode_apply, show -(-a - 1) - 1 = a by ring]
  rw [h1, h2] at hc
  show W.Y u a (WbarMode BV N BM hO (-b - 1) t x) - WbarMode BV N BM hO (-b - 1) t (N.YM u a x) = _
  rw [hc]
  refine Finset.sum_congr rfl fun r _ => ?_
  show _ = (gBinom (-a - 1) r • WbarMode BV N BM hO (-(a + b) - 2 - r) (N.act u r t)) x
  rw [LinearMap.smul_apply, show -a - 1 + (-b - 1) - (r : ℤ) = -(a + b) - 2 - r by ring]

/-- **`Wbar_local`**: `Y(u,z₁)` and `W̄(t,z₂)` are mutually local,
`(z₁−z₂)ᴺ [Y(u,z₁) W̄(t,z₂) − W̄(t,z₂) Y_M(u,z₁)] = 0` (as a `Hom(M,𝒱)`-valued distribution). -/
theorem Wbar_local (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV)
    (hVinv : VInv W BV) (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    (hqpV : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (u : 𝒱) (t : M) :
    ∃ N₀ : ℕ, mulBySubPow N₀
      (fun a b => (W.Y u a).comp (Wbar BV N BM hO t b) - (Wbar BV N BM hO t b).comp (N.YM u a) :
        FormalDist₂ (M →ₗ[ℂ] 𝒱)) = 0 := by
  obtain ⟨T₀, hT₀⟩ := N.truncation u t
  refine ⟨T₀.toNat, ?_⟩
  change mulBySubPow T₀.toNat (wbarBracket BV N BM hO u t) = 0
  rw [wbarBracket_eq_sum hVo hVnd hVinv hMinv hqpV u t T₀.toNat
    (fun j hj => hT₀ _ (by omega)), map_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_range] at hr
  exact mulBySubPow_eq_zero_of_le (by omega : r + 1 ≤ T₀.toNat) (mulBySubPow_jumpDist r _)

/-- **Translation covariance of `W̄`** (the `VnatBlock.HomCov` shape):
`L₋₁ ∘ W̄(t)ₖ − W̄(t)ₖ ∘ L₋₁ᴹ = (k+1) • W̄(t)ₖ₊₁` (coefficients of `zᵏ`). -/
theorem Wbar_homCov (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV)
    (hVinv : VInv W BV) (hMinv : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → FHLInv N BM wt u)
    (hqpV : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (t : M) (k : ℤ) :
    W.L (-1) ∘ₗ Wbar BV N BM hO t k - Wbar BV N BM hO t k ∘ₗ Lm1 N.toWeakModule
      = (k + 1 : ℤ) • Wbar BV N BM hO t (k + 1) := by
  refine LinearMap.ext fun a => ?_
  obtain ⟨T₀, hT₀⟩ := N.truncation W.conformalVector t
  have hc := WbarMode_comm (hO := hO) hVo hVnd hVinv hMinv hqpV W.conformalVector 0 t (-k - 1) a
    (T₀.toNat + 1) (fun j hj => hT₀ _ (by omega))
  rw [Finset.sum_eq_single 0 (fun r _ hr => by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
      rw [gBinom_zero_succ', zero_smul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos _)) h)] at hc
  rw [gBinom_zero, one_smul, Nat.cast_zero, sub_zero, zero_add, smul_omega_zero] at hc
  have hL : N.act W.conformalVector 0 a = Lm1 N.toWeakModule a := rfl
  have hL' : N.act W.conformalVector 0 t = Lm1 N.toWeakModule t := rfl
  rw [hL, hL', WbarMode_Lm1] at hc
  change W.L (-1) (WbarMode BV N BM hO (-k - 1) t a)
    - WbarMode BV N BM hO (-k - 1) t (Lm1 N.toWeakModule a)
    = ((k + 1 : ℤ) • WbarMode BV N BM hO (-(k + 1) - 1) t) a
  rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ,
    show -k - 1 - 1 = -(k + 1) - 1 by ring]
  push_cast
  ring_nf

end VOA.Moonshine.SkewAdjoint
