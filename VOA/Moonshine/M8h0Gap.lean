/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8h0VPBlock
import VOA.Moonshine.VnatAxioms
import VOA.Moonshine.CyclicTwisted

/-!
# M8h-0: closing the generator gap — DGM (4.23) on a mode-generating family suffices

`VnatAxioms.vnat_VOA_of_htt` needs twisted × twisted locality `Local (Y♮(t)) (Y♮(t'))` for **all**
`t, t' ∈ TP`, and `htt_of_span` reduces it only to a *linearly* spanning family.  Here the
hypothesis is reduced to DGM (4.23) (`TPBlockLocal`) on a family `g` whose `V_Λ^+`-**mode** span is
`TP`:

  `span {u₍ₙ₎ gᵢ : u ∈ V_Λ^+, n ∈ ℤ, i} = TP`.

## Proof

1. (4.22) holds for all pairs unconditionally (`leechWbar_VPBlockLocal`), so on `g`, (4.23) gives
   `Local (Y♮(gᵢ)) (Y♮(gⱼ))` (`YnatT_local_iff`).
2. **Iterate formula by Goddard** (`YnatT_eq_of_creates`).  Let `Ψ` be a `T`-covariant field that
   creates `(0, x)` from the vacuum and is local with every `Y♮(u, 0)` and every `Y♮(gⱼ)`.  Then
   `Ψ = Y♮(0, x)`.  Indeed `F := Y♮(0,x) − Ψ` kills the vacuum (`tower_unique`); it kills
   `(0, gⱼ)`, because `(z−w)ᴹ F(z) Y♮(gⱼ, w) 𝟙 = 0`: the `Y♮(0,x)` part of the commutator acts on
   `𝟙` through the `V_Λ^+` block only, which is (4.22) — this is where the unconditional (4.22) is
   used — and the `Ψ` part by hypothesis; and the set of vectors killed by `F` is stable under all
   modes of the `Y♮(u, 0)` (`kill_mode`).  The mode-span hypothesis then gives `F = 0`.
3. The field products `Y♮(u,0)₍ₖ₎ Y♮(gᵢ)` (`k ≥ 0`, `cCoeff`) and `:Y♮(u,0) Y♮(gᵢ):`
   (`k = −1`, `nprod`) satisfy the hypotheses of step 2 (Dong's lemma `dong_nonneg`/`dong_neg`,
   `DCovariant` closure, creation), so `Y♮(u₍ₖ₎gᵢ)` and `Y♮(u₍₋₁₎gᵢ)` are these products, and by
   Dong's lemma again they are pairwise local.  Modes `u₍₋₁₋ₖ₎ = (L₋₁ᵏu/k!)₍₋₁₎` reduce to `k = −1`.
4. `htt_of_span` on the family `{u₍ₙ₎gᵢ}`, then `vnat_VOA_of_htt`.

## Main results
* `YnatT_local_all_of_gen` — `Local (Y♮(t)) (Y♮(t'))` for all `t, t'` from (4.23) on `g`.
* `TPBlockLocal_all_of_gen` — (4.23) for all pairs from (4.23) on `g`.
* `vnat_VOA_of_TPBlockLocal_gen` — the VOA `V♮` from (4.23) on `g` only.
* `vnat_VOA_of_TPBlockLocal_frame` — the same with `g` the two cyclic vectors of
  `cyclic_TPframe` (so the hypothesis is (4.23) on four pairs of explicit weight-2 vectors).

## Status
`sorry`-free.  The only hypotheses are the displayed `TPBlockLocal` relations on the generating
family (DGM (4.23), step M8h — not proved on this route) and the mode-span condition (proved for the frame
family).  ⚠ The conclusion does not by itself prove simplicity of `V♮`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8h0

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction SkewAdjoint InvForm

/-! ## Generic field lemmas -/

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `F` is local with the field `A` and kills `x`, it kills every `A_q x`. -/
theorem kill_mode {F A : FormalDist (End ℂ V)} (hloc : Local F A) (hA : IsField A) {x : V}
    (hx : ∀ p, F p x = 0) (p q : ℤ) : F p (A q x) = 0 := by
  obtain ⟨N, hN⟩ := hloc
  obtain ⟨B, hB⟩ := hA x
  have hD : (fun p q : ℤ => F p (A q x)) = applyVec x (bracketDist F A) := by
    funext p q
    rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, hx, map_zero, sub_zero]
  have hkill : mulBySubPow N (fun p q : ℤ => F p (A q x)) = 0 := by
    rw [hD, ← applyVec_mulBySubPow, hN, applyVec_zero]
  have hbb : IsBddBelow₂ (fun p q : ℤ => F p (A q x)) :=
    ⟨B, fun p q hq => by change F p (A q x) = 0; rw [hB q hq, map_zero]⟩
  exact congrFun (congrFun (eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb) p) q

theorem local_sub_left {a b c : FormalDist (End ℂ V)} (ha : Local a c) (hb : Local b c) :
    Local (a - b) c := by
  have : a - b = a + (-1 : ℂ) • b := by rw [neg_one_smul, sub_eq_add_neg]
  rw [this]
  exact Local.add_left ha (Local.symm (Local.smulR _ (Local.symm hb)))

theorem local_smul_left (c : ℂ) {a b : FormalDist (End ℂ V)} (h : Local a b) : Local (c • a) b :=
  Local.symm (Local.smulR c (Local.symm h))

/-- Translation covariance of the field `k`-th product (`k ≥ 0`). -/
theorem cCoeff_DCovariant {T : End ℂ V} {a b : FormalDist (End ℂ V)} (ha : DCovariant T a)
    (hb : DCovariant T b) (k : ℕ) : DCovariant T (cCoeff k (bracketDist a b)) := by
  set cT : FormalDist₂ (End ℂ V) →ₗ[ℂ] FormalDist₂ (End ℂ V) :=
    { toFun := fun G s t => T * G s t - G s t * T
      map_add' := fun G H => by funext s t; change T * (G s t + H s t) - (G s t + H s t) * T = _
                                 ; rw [mul_add, add_mul]; change _ = (T * G s t - G s t * T) + (T * H s t - H s t * T); abel
      map_smul' := fun c G => by funext s t; change T * (c • G s t) - (c • G s t) * T = c • (T * G s t - G s t * T)
                                  ; rw [mul_smul_comm, smul_mul_assoc, smul_sub] } with hcT
  have hsub : ∀ G, cT (mulBySub G) = mulBySub (cT G) := fun G => by
    funext s t
    change T * (G (s - 1) t - G s (t - 1)) - (G (s - 1) t - G s (t - 1)) * T
      = (T * G (s - 1) t - G (s - 1) t * T) - (T * G s (t - 1) - G s (t - 1) * T)
    rw [mul_sub, sub_mul]; abel
  have hpow : ∀ j G, cT (mulBySubPow j G) = mulBySubPow j (cT G) := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih => intro G; rw [mulBySubPow_succ, LinearMap.comp_apply, hsub, ih,
        ← LinearMap.comp_apply, ← mulBySubPow_succ]
  have hbr : cT (bracketDist a b) = deriv2 (bracketDist a b) := by
    funext s t
    change T * (a s * b t - b t * a s) - (a s * b t - b t * a s) * T
      = (s + 1) • (a (s + 1) * b t - b t * a (s + 1)) + (t + 1) • (a s * b (t + 1) - b (t + 1) * a s)
    have h1 : T * a s = a s * T + (s + 1) • a (s + 1) := by rw [← ha s]; abel
    have h2 : T * b t = b t * T + (t + 1) • b (t + 1) := by rw [← hb t]; abel
    have e1 : T * (a s * b t) = a s * b t * T + (s + 1) • (a (s + 1) * b t)
        + (t + 1) • (a s * b (t + 1)) := by
      rw [← mul_assoc, h1, add_mul, mul_assoc, h2, mul_add, smul_mul_assoc, mul_smul_comm,
        ← mul_assoc]; abel
    have e2 : T * (b t * a s) = b t * a s * T + (t + 1) • (b (t + 1) * a s)
        + (s + 1) • (b t * a (s + 1)) := by
      rw [← mul_assoc, h2, add_mul, mul_assoc, h1, mul_add, smul_mul_assoc, mul_smul_comm,
        ← mul_assoc]; abel
    rw [mul_sub, e1, e2, smul_sub, smul_sub]
    simp only [sub_mul]
    abel
  intro m
  have h := congrFun (congrFun (hpow k (bracketDist a b)) (-1)) m
  rw [hbr, resByParts] at h
  exact h

/-- Creation for the field `k`-th product. -/
theorem cCoeff_vac {a b : FormalDist (End ℂ V)} (vac : V)
    (ha : ∀ q : ℤ, q < 0 → a q vac = 0) (hb : ∀ q : ℤ, q < 0 → b q vac = 0) (k : ℕ) :
    (∀ m : ℤ, m < 0 → cCoeff k (bracketDist a b) m vac = 0) ∧
      cCoeff k (bracketDist a b) 0 vac = a (-1 - k) (b 0 vac) := by
  have hq : ∀ s t : ℤ, s ≤ -1 → t ≤ -1 → applyVec vac (bracketDist a b) s t = 0 := by
    intro s t hs ht
    rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, hb t (by omega), ha s (by omega), map_zero, map_zero, sub_zero]
  have hc : ∀ m, cCoeff k (bracketDist a b) m vac = mulBySubPow k (applyVec vac (bracketDist a b)) (-1) m := by
    intro m
    change mulBySubPow k (bracketDist a b) (-1) m vac = _
    rw [← applyVec_apply, applyVec_mulBySubPow]
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [hc]; exact mulBySubPow_zero_of_quadrant hq k (-1) m le_rfl (by omega)
  · rw [hc, mulBySubPow_diag_of_quadrant hq k (-1) le_rfl, applyVec_apply, bracketDist_apply,
      LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ha _ (by omega), map_zero,
      sub_zero]

end Generic

/-! ## Block-field facts -/

theorem YnatU_apply_inr (u : SkewVP) (k : ℤ) (y : TP) :
    YnatU u k ((0 : SkewVP), y) = (0, plusModule.YM u k y) := by
  simp [YnatU, diagF, blockF_apply, blockOp_apply]

theorem YnatT_sub (a b : TP) :
    YnatT leechWbar (a - b) = YnatT leechWbar a - YnatT leechWbar b := by
  rw [sub_eq_add_neg, VnatAxioms.YnatT_add, ← neg_one_smul ℂ b, VnatAxioms.YnatT_smul,
    neg_one_smul, ← sub_eq_add_neg]

/-! ## The iterate formula by Goddard uniqueness -/

section Gap

variable {κ : Type*} (g : κ → TP)

/-- The mode-span hypothesis: `TP` is spanned by `u₍ₙ₎ gᵢ`. -/
def ModeSpan : Prop :=
  Submodule.span ℂ {x : TP | ∃ (u : SkewVP) (n : ℤ) (i : κ), x = mode (plusModule.YM u) n (g i)} = ⊤

variable {g}

/-- **Goddard identification.**  A `T`-covariant field creating `(0,x)`, local with every
`Y♮(u,0)` and every `Y♮(gⱼ)`, **is** `Y♮(0,x)` — given the mode-span hypothesis.  The `V_Λ^+`
block of the needed commutator on the vacuum is (4.22) (`leechWbar_VPBlockLocal`). -/
theorem YnatT_eq_of_creates (hspan : ModeSpan g) (x : TP) (Ψ : FormalDist (End ℂ Vnat))
    (hcov : DCovariant Tnat Ψ) (h0 : Ψ 0 vacNat = ((0 : SkewVP), x))
    (hneg : ∀ q : ℤ, q < 0 → Ψ q vacNat = 0) (hU : ∀ v : SkewVP, Local Ψ (YnatU v))
    (hT : ∀ j, Local Ψ (YnatT leechWbar (g j))) : YnatT leechWbar x = Ψ := by
  set F := YnatT leechWbar x - Ψ with hF
  have hFp : ∀ p y, F p y = YnatT leechWbar x p y - Ψ p y := fun _ _ => rfl
  -- `F` kills the vacuum
  have hFvac : ∀ p, F p vacNat = 0 := by
    intro p
    rw [hFp, tower_unique (YnatT_DCovariant_genuine x) hcov Tnat_vacNat
      (by rw [YnatT_vac_zero, h0]) (YnatT_vac_neg leechWbar x) hneg p, sub_self]
  have hFU : ∀ v, Local F (YnatU v) := fun v =>
    local_sub_left (YnatT_YnatU_local_genuine x v) (hU v)
  -- `F` kills each `(0, gⱼ)`
  have hFg : ∀ j p, F p ((0 : SkewVP), g j) = 0 := by
    intro j p
    set G := YnatT leechWbar (g j)
    obtain ⟨N₁, hN₁⟩ := leechWbar_VPBlockLocal x (g j)
    obtain ⟨N₂, hN₂⟩ := hT j
    set N := max N₁ N₂
    have hD : (fun p q : ℤ => F p (G q vacNat))
        = applyVec vacNat (bracketDist (YnatT leechWbar x) G) - applyVec vacNat (bracketDist Ψ G) := by
      funext p q
      change F p (G q vacNat) = (bracketDist (YnatT leechWbar x) G p q) vacNat - (bracketDist Ψ G p q) vacNat
      have hz : F p vacNat = 0 := hFvac p
      simp only [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply] at hz ⊢
      rw [hFp] at hz ⊢
      have : G q (YnatT leechWbar x p vacNat) = G q (Ψ p vacNat) := by
        rw [sub_eq_zero.mp hz]
      rw [this]; abel
    have hkill : mulBySubPow N (fun p q : ℤ => F p (G q vacNat)) = 0 := by
      rw [hD, map_sub, ← applyVec_mulBySubPow, ← applyVec_mulBySubPow]
      have e2 : mulBySubPow N (bracketDist Ψ G) = 0 :=
        mulBySubPow_eq_zero_of_le (le_max_right N₁ N₂) hN₂
      have e1 : applyVec vacNat (mulBySubPow N (bracketDist (YnatT leechWbar x) G)) = 0 := by
        funext m n
        change mulBySubPow N (bracketDist (YnatT leechWbar x) G) m n
          ((leechVOAPlus.vacuum, (0 : TP)) : Vnat) = 0
        have hN₁' : mulBySubPow N₁ (VPfun x (g j)) = 0 := hN₁
        rw [B_inl, mulBySubPow_eq_zero_of_le (le_max_left N₁ N₂) hN₁']
        rfl
      rw [e1, e2, applyVec_zero, sub_zero]
    have hbb : IsBddBelow₂ (fun p q : ℤ => F p (G q vacNat)) :=
      ⟨0, fun p q hq => by change F p (G q vacNat) = 0; rw [YnatT_vac_neg _ _ q hq, map_zero]⟩
    have h := congrFun (congrFun (eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb) p) 0
    change F p (G 0 vacNat) = 0 at h
    rwa [YnatT_vac_zero] at h
  -- the kernel of `F` is everything
  set K : Submodule ℂ Vnat := ⨅ p : ℤ, LinearMap.ker (F p) with hK
  have hmemK : ∀ y, y ∈ K ↔ ∀ p, F p y = 0 := by
    intro y; simp [hK, Submodule.mem_iInf, LinearMap.mem_ker]
  have hTP : ∀ t : TP, ((0 : SkewVP), t) ∈ K := by
    intro t
    have ht : t ∈ Submodule.span ℂ
        {x : TP | ∃ (u : SkewVP) (n : ℤ) (i : κ), x = mode (plusModule.YM u) n (g i)} := by
      rw [hspan]; trivial
    have hsub : Submodule.span ℂ
        {x : TP | ∃ (u : SkewVP) (n : ℤ) (i : κ), x = mode (plusModule.YM u) n (g i)}
        ≤ K.comap (LinearMap.inr ℂ SkewVP TP) := by
      rw [Submodule.span_le]
      rintro y ⟨u, n, i, rfl⟩
      change ((0 : SkewVP), mode (plusModule.YM u) n (g i)) ∈ K
      rw [hmemK]
      intro p
      rw [mode_apply, ← YnatU_apply_inr]
      exact kill_mode (hFU u) (YnatU_isField u) (hFg i) p _
    exact hsub ht
  have hVP : ∀ u : SkewVP, (u, (0 : TP)) ∈ K := by
    intro u
    rw [hmemK]
    intro p
    rw [← YnatU_vac_zero u]
    exact kill_mode (hFU u) (YnatU_isField u) hFvac p 0
  have hall : ∀ p y, F p y = 0 := by
    intro p y
    have hy : y = (y.1, 0) + (0, y.2) := by simp
    have hmem : y ∈ K := by rw [hy]; exact K.add_mem (hVP _) (hTP _)
    exact (hmemK y).1 hmem p
  have hF0 : F = 0 := by
    funext p; exact LinearMap.ext fun y => hall p y
  exact sub_eq_zero.mp hF0

variable (hspan : ModeSpan g) (htt0 : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j)))
include hspan htt0

/-- `Y♮(u₍ₖ₎ gᵢ) = Y♮(u,0)₍ₖ₎ Y♮(gᵢ)` for `k ≥ 0`. -/
theorem YnatT_mode_nonneg (u : SkewVP) (k : ℕ) (i : κ) :
    YnatT leechWbar (mode (plusModule.YM u) k (g i))
      = cCoeff k (bracketDist (YnatU u) (YnatT leechWbar (g i))) := by
  obtain ⟨hneg, hbase⟩ := cCoeff_vac vacNat (YnatU_vac_neg u) (YnatT_vac_neg leechWbar (g i)) k
  refine YnatT_eq_of_creates hspan _ _
    (cCoeff_DCovariant (YnatU_DCovariant u) (YnatT_DCovariant_genuine (g i)) k) ?_ hneg
    (fun v => dong_nonneg (YnatU_YnatT_local_genuine u (g i)) (YnatU_local u v)
      (YnatT_YnatU_local_genuine (g i) v) k)
    (fun j => dong_nonneg (YnatU_YnatT_local_genuine u (g i)) (YnatU_YnatT_local_genuine u (g j))
      (htt0 i j) k)
  rw [hbase, YnatT_vac_zero, YnatU_apply_inr, mode_apply, show -1 - (k : ℤ) = -(k : ℤ) - 1 by ring]

/-- `Y♮(u₍₋₁₎ gᵢ) = :Y♮(u,0) Y♮(gᵢ):`. -/
theorem YnatT_mode_neg_one (u : SkewVP) (i : κ) :
    YnatT leechWbar (mode (plusModule.YM u) (-1) (g i))
      = nprod (YnatU_isField u) (YnatT_isField_genuine (g i)) := by
  refine YnatT_eq_of_creates hspan _ _
    (DCovariant.nprod _ _ (YnatU_DCovariant u) (YnatT_DCovariant_genuine (g i))) ?_
    (fun q hq => nprod_vacuum_neg_gen _ _ vacNat (YnatU_vac_neg u) (YnatT_vac_neg leechWbar (g i)) hq)
    (fun v => dong_neg _ _ (YnatU_YnatT_local_genuine u (g i)) (YnatU_local u v)
      (YnatT_YnatU_local_genuine (g i) v))
    (fun j => dong_neg _ _ (YnatU_YnatT_local_genuine u (g i)) (YnatU_YnatT_local_genuine u (g j))
      (htt0 i j))
  rw [nprod_vacuum_base_gen _ _ vacNat (YnatU_vac_neg u) (YnatT_vac_neg leechWbar (g i)),
    YnatT_vac_zero, YnatU_apply_inr, mode_apply]
  congr 2

omit hspan htt0 in
/-- `u₍₋₁₋ₖ₎ x = (1/k!) (L₋₁ᵏu)₍₋₁₎ x` on the module. -/
theorem mode_neg_eq (u : SkewVP) (k : ℕ) (x : TP) :
    mode (plusModule.YM u) (-1 - k) x
      = ((k.factorial : ℂ)⁻¹) • mode (plusModule.YM (((leechVOAPlus.L (-1)) ^ k) u)) (-1) x := by
  have hd : ∀ j : ℕ, plusModule.YM (((leechVOAPlus.L (-1)) ^ j) u) = deriv^[j] (plusModule.YM u) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, VnatAxioms.module_YM_Lm1 plusModule.toWeakModule, ih,
        Function.iterate_succ_apply']
  have e : (deriv^[k] (plusModule.YM u)) 0 = ((k.factorial : ℤ)) • plusModule.YM u k := by
    rw [VertexOperatorAlgebra.deriv_pow_apply, zero_add]
    congr 1
    · rw [← Finset.prod_range_add_one_eq_factorial]; push_cast
      exact Finset.prod_congr rfl fun i _ => by ring
    · rw [zero_add]
  rw [mode_apply, mode_apply, hd, show -(-1 : ℤ) - 1 = 0 by norm_num, e,
    show -(-1 - (k : ℤ)) - 1 = k by ring, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ,
    smul_smul, Int.cast_natCast, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k),
    one_smul]

/-- The generating family `{u₍ₙ₎ gᵢ}`, split as `n ≥ 0` and `n = −1`. -/
noncomputable def famG : (SkewVP × ℕ × κ) ⊕ (SkewVP × κ) → TP
  | Sum.inl ⟨u, k, i⟩ => mode (plusModule.YM u) k (g i)
  | Sum.inr ⟨u, i⟩ => mode (plusModule.YM u) (-1) (g i)

omit htt0 in
theorem span_famG : Submodule.span ℂ (Set.range (famG (g := g))) = ⊤ := by
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro y ⟨u, n, i, rfl⟩
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    exact Submodule.subset_span ⟨Sum.inl ⟨u, k, i⟩, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -1 - k := ⟨(-1 - n).toNat, by omega⟩
    rw [SetLike.mem_coe, mode_neg_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr ⟨_, i⟩, rfl⟩)

/-- Each `Y♮(famG a)` is a field product of `Y♮(u,0)` and some `Y♮(gᵢ)`. -/
theorem famG_prop (a : (SkewVP × ℕ × κ) ⊕ (SkewVP × κ)) :
    ∃ (u : SkewVP) (i : κ), (∀ c : FormalDist (End ℂ Vnat),
        Local (YnatU u) c → Local (YnatT leechWbar (g i)) c → Local (YnatT leechWbar (famG (g := g) a)) c) := by
  rcases a with ⟨u, k, i⟩ | ⟨u, i⟩
  · refine ⟨u, i, fun c h1 h2 => ?_⟩
    change Local (YnatT leechWbar (mode (plusModule.YM u) k (g i))) c
    rw [YnatT_mode_nonneg hspan htt0]
    exact dong_nonneg (YnatU_YnatT_local_genuine u (g i)) h1 h2 k
  · refine ⟨u, i, fun c h1 h2 => ?_⟩
    change Local (YnatT leechWbar (mode (plusModule.YM u) (-1) (g i))) c
    rw [YnatT_mode_neg_one hspan htt0]
    exact dong_neg _ _ (YnatU_YnatT_local_genuine u (g i)) h1 h2

/-- `Y♮(famG a)` is local with every `Y♮(u,0)` and every `Y♮(gⱼ)`. -/
theorem famG_local_gen (a : (SkewVP × ℕ × κ) ⊕ (SkewVP × κ)) (j : κ) :
    Local (YnatT leechWbar (famG (g := g) a)) (YnatT leechWbar (g j)) := by
  obtain ⟨u, i, h⟩ := famG_prop hspan htt0 a
  exact h _ (YnatU_YnatT_local_genuine u (g j)) (htt0 i j)

/-- **Twisted × twisted locality on the whole family `{u₍ₙ₎ gᵢ}`.** -/
theorem famG_local (a b : (SkewVP × ℕ × κ) ⊕ (SkewVP × κ)) :
    Local (YnatT leechWbar (famG (g := g) a)) (YnatT leechWbar (famG (g := g) b)) := by
  obtain ⟨u, i, h⟩ := famG_prop hspan htt0 a
  refine h _ ?_ ?_
  · exact Local.symm (YnatT_YnatU_local_genuine _ u)
  · exact Local.symm (famG_local_gen hspan htt0 b i)

/-- **All twisted × twisted locality from the generating family.** -/
theorem YnatT_local_all_of_gen (t t' : TP) :
    Local (YnatT leechWbar t) (YnatT leechWbar t') :=
  VnatAxioms.htt_of_span _ (span_famG hspan) (famG_local hspan htt0) t t'

end Gap

/-! ## The packaged results -/

/-- **DGM (4.23) for all pairs from (4.23) on a mode-generating family.** -/
theorem TPBlockLocal_all_of_gen {κ : Type*} (g : κ → TP) (hspan : ModeSpan g)
    (h423 : ∀ i j, TPBlockLocal leechWbar (g i) (g j)) (t t' : TP) :
    TPBlockLocal leechWbar t t' := by
  have htt0 : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j)) := fun i j =>
    (YnatT_local_iff _ _ _).2 ⟨leechWbar_VPBlockLocal _ _, h423 i j⟩
  exact ((YnatT_local_iff _ _ _).1 (YnatT_local_all_of_gen hspan htt0 t t')).2

/-- **M8h reduced to (4.23) on a generating family.**  If `TP` is the `V_Λ^+`-mode span of a
family `g`, then DGM (4.23) on the pairs of `g` alone yields the vertex operator algebra structure
on `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+` with the genuine block vertex map, `c = 24`.  (4.22) is proved
(`leechWbar_VPBlockLocal`) and is not a hypothesis.  TRAP: simplicity is a separate theorem. -/
theorem vnat_VOA_of_TPBlockLocal_gen {κ : Type*} (g : κ → TP) (hspan : ModeSpan g)
    (h423 : ∀ i j, TPBlockLocal leechWbar (g i) (g j)) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
        V.centralCharge = 24 ∧ V.grading = gradingNat := by
  have htt0 : ∀ i j, Local (YnatT leechWbar (g i)) (YnatT leechWbar (g j)) := fun i j =>
    (YnatT_local_iff _ _ _).2 ⟨leechWbar_VPBlockLocal _ _, h423 i j⟩
  exact VnatAxioms.vnat_VOA_of_htt (YnatT_local_all_of_gen hspan htt0)

/-! ## The frame family of `cyclic_TPframe` -/

/-- The two cyclic vectors of `cyclic_TPframe` (`T₀⁺`, `T₁⁺`) form a mode-generating family. -/
theorem exists_frame_modeSpan :
    ∃ x : ZMod 2 → TP, (∀ s, x s ∈ TPframe s) ∧ ModeSpan x := by
  choose x hx hspan using cyclic_TPframe
  refine ⟨x, hx, ?_⟩
  rw [ModeSpan, eq_top_iff, ← TPframe_isCompl.sup_eq_top, sup_le_iff]
  constructor
  · rw [← hspan 0]; apply Submodule.span_mono; rintro y ⟨u, -, n, rfl⟩; exact ⟨u, n, 0, rfl⟩
  · rw [← hspan 1]; apply Submodule.span_mono; rintro y ⟨u, -, n, rfl⟩; exact ⟨u, n, 1, rfl⟩

/-- **M8h reduced to (4.23) on the two frame vectors.**  There are `x₀ ∈ T₀⁺`, `x₁ ∈ T₁⁺`
(the cyclic vectors of `cyclic_TPframe`) such that DGM (4.23) on the four pairs `(xᵢ, xⱼ)` yields
the vertex operator algebra `V♮`. -/
theorem vnat_VOA_of_TPBlockLocal_frame :
    ∃ x : ZMod 2 → TP, (∀ s, x s ∈ TPframe s) ∧
      ((∀ i j, TPBlockLocal leechWbar (x i) (x j)) →
        ∃ V : VertexOperatorAlgebra Vnat,
          V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
            V.centralCharge = 24 ∧ V.grading = gradingNat) := by
  obtain ⟨x, hx, hspan⟩ := exists_frame_modeSpan
  exact ⟨x, hx, fun h423 => vnat_VOA_of_TPBlockLocal_gen x hspan h423⟩

end VOA.Moonshine.M8h0
