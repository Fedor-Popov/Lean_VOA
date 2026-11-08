/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.AutFaithfulVnat
import VOA.Moonshine.Generation
import VOA.Moonshine.CyclicTwisted
import VOA.Moonshine.SigmaExistLeech
import VOA.Moonshine.AutLeechSpan

/-!
# Faithfulness of `Aut V♮` on the Griess algebra — the assembly
(Aut(V♮) campaign, step 3, route C, node C7 part 2, `Notes/MONSTER_AUT_PLAN.md`)

If an automorphism `g` of `V♮` fixes `V♮₂` pointwise and fixes every `(x_β, 0)`, then `g = 1`:
* the untwisted block: `{x | g (x, 0) = (x, 0)}` is a subspace of `V_Λ⁺` closed under products
  and containing `𝟙` and every `x_β`, so it is everything (`leechPlus_generated`);
* the twisted block: each frame sector `T_s⁺` is spanned by `V_Λ⁺`-modes applied to the weight-2
  vector `x0T t₀` (`span_smul_frameX0T`), which `g` fixes, and `T⁺ = T₀⁺ ⊕ T₁⁺`.

Combined with the scalar propagation of `AutFaithfulVnat` and the fact that the Leech lattice is
spanned by its minimal vectors (`LeechSpan.leech_induction`), every `(x_β, 0)` is fixed, so:

## Main results
* ⭐ `aut_eq_one_of_fix_frame`.
* ⭐⭐ `aut_eq_one_of_fix_weightTwo` — an automorphism of `V♮` fixing `V♮₂` pointwise is the identity.
* ⭐⭐⭐ `vnatGriessRestrict_injective` — **`Aut V♮` acts faithfully on the Griess algebra `V♮₂`.**
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutMonster

open VOA VOA.Moonshine GriessAut VOA.Moonshine.TrialityTw LatGen

/-- ⭐ **An automorphism fixing `V♮₂` and every `(x_β, 0)` is the identity.** -/
theorem aut_eq_one_of_fix_frame (g : AutVnat) (hg : ∀ v ∈ VnatVOA.grading 2, g v = v)
    (hx : ∀ β : leech.carrier, g ((frameX0P β, 0) : Vnat) = ((frameX0P β, 0) : Vnat)) : g = 1 := by
  -- the untwisted block is fixed
  set S : Submodule ℂ VPlus := (fixedSpace g).comap (LinearMap.inl ℂ SkewVP TP) with hS
  have hmemS : ∀ x : VPlus, x ∈ S ↔ g ((x, 0) : Vnat) = ((x, 0) : Vnat) := fun x => by
    rw [hS, Submodule.mem_comap, LinearMap.inl_apply, mem_fixedSpace]
  have hStop : S = ⊤ := by
    refine leechPlus_generated S ?_ ?_ (fun β => (hmemS _).2 (hx β))
    · rw [hmemS]
      have := g.map_vacuum
      rw [VnatVOA_vacuum] at this
      exact this
    · intro u hu x hx' n
      rw [hmemS] at hu hx' ⊢
      have h1 : VnatVOA.smul ((u, 0) : Vnat) n ((x, 0) : Vnat) = ((leechVOAPlus.smul u n x, 0) : Vnat) := by
        rw [VnatVOA_smul_inl, map_zero]
      rw [← h1, Aut.map_smul, hu, hx']
  have hU : ∀ x : VPlus, g ((x, 0) : Vnat) = ((x, 0) : Vnat) := fun x =>
    (hmemS x).1 (hStop ▸ Submodule.mem_top)
  -- the twisted block is fixed
  have hT0 : ∀ t : TP, (0, t) ∈ VnatVOA.grading 2 → g ((0, t) : Vnat) = ((0, t) : Vnat) :=
    fun t ht => hg _ ht
  set R : Submodule ℂ TP := (fixedSpace g).comap (LinearMap.inr ℂ SkewVP TP) with hR
  have hmemR : ∀ t : TP, t ∈ R ↔ g ((0, t) : Vnat) = ((0, t) : Vnat) := fun t => by
    rw [hR, Submodule.mem_comap, LinearMap.inr_apply, mem_fixedSpace]
  have hframe : ∀ s : ZMod 2, TPframe s ≤ R := by
    intro s
    obtain ⟨t₀, ht₀, h0⟩ := exists_ne_zero_leechFrameT s
    rw [← span_smul_frameX0T ht₀ h0, Submodule.span_le]
    rintro y ⟨u, -, n, rfl⟩
    rw [SetLike.mem_coe, hmemR]
    have hx0 : g ((0, x0T t₀) : Vnat) = ((0, x0T t₀) : Vnat) := by
      refine hT0 _ ?_
      rw [VnatVOA_grading, mem_gradingNat]
      exact ⟨Submodule.zero_mem _, SigmaExist.x0T_mem_weight t₀⟩
    have h1 : VnatVOA.smul ((u, 0) : Vnat) n ((0, x0T t₀) : Vnat)
        = ((0, mode (plusModule.YM u) n (x0T t₀)) : Vnat) := by
      rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
    calc g ((0, mode (plusModule.YM u) n (x0T t₀)) : Vnat)
        = g (VnatVOA.smul ((u, 0) : Vnat) n ((0, x0T t₀) : Vnat)) := by rw [h1]
      _ = VnatVOA.smul ((u, 0) : Vnat) n ((0, x0T t₀) : Vnat) := by rw [Aut.map_smul, hU u, hx0]
      _ = ((0, mode (plusModule.YM u) n (x0T t₀)) : Vnat) := h1
  have hRtop : R = ⊤ := by
    rw [eq_top_iff, ← TPframe_isCompl.sup_eq_top]
    exact sup_le (hframe 0) (hframe 1)
  have hT : ∀ t : TP, g ((0, t) : Vnat) = ((0, t) : Vnat) := fun t =>
    (hmemR t).1 (hRtop ▸ Submodule.mem_top)
  -- conclusion
  refine Aut.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, t⟩ := v
  have hsplit : ((x, t) : Vnat) = ((x, 0) : Vnat) + ((0, t) : Vnat) := by simp
  change g.toLinearEquiv (x, t) = (x, t)
  rw [hsplit, map_add, Aut.coe_toLinearEquiv, Aut.coe_toLinearEquiv, hU x, hT t]

/-- `x_0 = 2·𝟙`. -/
theorem frameX0P_zero : frameX0P (0 : leech.carrier) = (2 : ℂ) • leechVOAPlus.vacuum := by
  apply Subtype.ext
  change latChargeGen leech 0 + latChargeGen leech (-0) = (2 : ℂ) • (leechVOAPlus.vacuum : LatModuleGen leech)
  rw [plus_vacuum_coe, neg_zero, LatGen.latChargeGen_zero, two_smul]

/-- ⭐⭐ **An automorphism of `V♮` fixing `V♮₂` pointwise is the identity.** -/
theorem aut_eq_one_of_fix_weightTwo (g : AutVnat) (hg : ∀ v ∈ VnatVOA.grading 2, g v = v) :
    g = 1 := by
  refine aut_eq_one_of_fix_frame g hg fun β => ?_
  refine LeechSpan.leech_induction
    (fun β => g ((frameX0P β, 0) : Vnat) = ((frameX0P β, 0) : Vnat)) ?_ ?_ ?_ β
  · -- `β = 0`: `(x_0, 0) = 2·𝟙♮`
    have hvac : ((frameX0P (0 : leech.carrier), 0) : Vnat) = (2 : ℂ) • VnatVOA.vacuum := by
      rw [VnatVOA_vacuum, frameX0P_zero]
      change _ = (2 : ℂ) • ((leechVOAPlus.vacuum, 0) : Vnat)
      rw [Prod.smul_mk, smul_zero]
    change g.toLinearEquiv _ = _
    rw [hvac, map_smul]
    change (2 : ℂ) • g VnatVOA.vacuum = _
    rw [g.map_vacuum]
  · intro γ α hα hP
    obtain ⟨c, hc⟩ := aut_frameX0P_eigen g hg (γ + α)
    have hc' : g ((frameX0P (α + γ), 0) : Vnat) = c • ((frameX0P (α + γ), 0) : Vnat) := by
      rw [add_comm]; exact hc
    have h1 : g ((frameX0P γ, 0) : Vnat) = (1 : ℂ) • ((frameX0P γ, 0) : Vnat) := by
      rw [one_smul]; exact hP
    have := scalar_step g hg hα h1 hc'
    change g ((frameX0P (γ + α), 0) : Vnat) = _
    rw [hc, ← this, one_smul]
  · intro γ α hα hP
    have hα' : leech.form (-α) (-α) = 4 := by
      rw [LinearMap.map_neg₂, map_neg, neg_neg, hα]
    obtain ⟨c, hc⟩ := aut_frameX0P_eigen g hg (γ - α)
    have hc' : g ((frameX0P (-α + γ), 0) : Vnat) = c • ((frameX0P (-α + γ), 0) : Vnat) := by
      rw [show -α + γ = γ - α by abel]; exact hc
    have h1 : g ((frameX0P γ, 0) : Vnat) = (1 : ℂ) • ((frameX0P γ, 0) : Vnat) := by
      rw [one_smul]; exact hP
    have := scalar_step g hg hα' h1 hc'
    change g ((frameX0P (γ - α), 0) : Vnat) = _
    rw [hc, ← this, one_smul]

/-- ⭐⭐⭐ **Faithfulness: `Aut V♮` embeds in the automorphism group of the Griess algebra.**
Restriction to `(V♮₂, ×, ⟨·,·⟩₃)` is injective — with no hypotheses. -/
theorem vnatGriessRestrict_injective : Function.Injective vnatGriessRestrict := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine aut_eq_one_of_fix_weightTwo g fun v hv => ?_
  have h := congrArg (fun k : GriessAutVnat =>
    (((k : VnatVOA.grading 2 ≃ₗ[ℂ] VnatVOA.grading 2) ⟨v, hv⟩ : VnatVOA.grading 2) : Vnat)) hg
  simpa [vnatGriessRestrict] using h

end VOA.Moonshine.AutMonster
