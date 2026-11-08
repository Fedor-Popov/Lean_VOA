/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.AutFaithfulVnat
import VOA.Core.AutFromGenerators
import VOA.Moonshine.M8hKeySpan

/-!
# The triality `σ♮` is an automorphism of `V♮`
(Aut(V♮) campaign, step 6, triality lift, `Notes/MONSTER_AUT_PLAN.md`)

`M8hKey.sigNat D` is FLM's involution `σ♮` on `V♮ = V₀⁺ ⊕ V₃⁺ ⊕ T_s⁺ ⊕ T_{s+1}⁺`. It acts by
`v0Sigma` on `V₀⁺`, swaps `V₃⁺ ↔ T_s⁺` through `Φ, Ψ`, and acts by `Θ` on `T_{s+1}⁺`.  For the
standard data `Dnat` it is an automorphism of `VnatVOA`.

## Proof
Let `S` be the subspace of vectors whose modes `σ` intertwines (`AutGen.intertwineSub`).  It is
closed under products (`AutGen.intertwines_smul`) and `σ`-stable, because `σ` is an involution.
* `V₀⁺ × 0 ⊆ S` by `sigNat_YnatU_V0`.
* `(0, x) ∈ S` for `x = h₀(−½)𝟙 ⊗ t_s`, by the σ-key `SigmaKey.conj_eq`.
* `0 × T_s⁺ ⊆ S`: `T_s⁺` is spanned by `V₀⁺`-modes on `x` (`span_smul_frameX0T`).
* `V₃⁺ × 0 = σ(0 × T_s⁺) ⊆ S` (`ΨΦ`, `σ`-stability), so `V_Λ⁺ × 0 ⊆ S`.
* `0 × T⁺ ⊆ S`: `T⁺` is spanned by `V_Λ⁺`-modes on `x` (`modeSpan_x0T`).

## Main results
* `sigmaEquiv`, `sigma_intertwines_V0`, `sigma_intertwines_x`, `intertwines_sigma`.
* ⭐ `sigmaAut : AutVnat` with `sigmaAut_apply : sigmaAut v = sigNat Dnat v`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutMonster

open VOA VOA.Moonshine M8hKey SigmaAssemble AutGen TrialityTw

theorem sigNat_invol (y : Vnat) : sigNat Dnat (sigNat Dnat y) = y := by
  have h := congrArg (fun F : Module.End ℂ Vnat => F y) (sigNat_sq Dnat)
  simpa using h

/-- `σ♮` as a linear equivalence (an involution). -/
noncomputable def sigmaEquiv : Vnat ≃ₗ[ℂ] Vnat :=
  LinearEquiv.ofInvolutive (sigNat Dnat) sigNat_invol

@[simp] theorem sigmaEquiv_apply (y : Vnat) : sigmaEquiv y = sigNat Dnat y := rfl

theorem VnatVOA_smul_eq_YnatU (u : SkewVP) (n : ℤ) (y : Vnat) :
    VnatVOA.smul ((u, 0) : Vnat) n y = YnatU u (-n - 1) y := by
  change mode (VnatAxioms.YN (u, 0)) n y = _
  rw [VnatAxioms.YN_inl, mode_apply]

theorem VnatVOA_smul_eq_YnatT (t : TP) (n : ℤ) (y : Vnat) :
    VnatVOA.smul ((0, t) : Vnat) n y = YnatT leechWbar t (-n - 1) y := by
  change mode (VnatAxioms.YN (0, t)) n y = _
  rw [VnatAxioms.YN_inr, mode_apply]

/-- `σ` intertwines `V₀⁺ × 0`. -/
theorem sigma_intertwines_V0 (u : V0Sub.carrier) :
    Intertwines VnatVOA sigmaEquiv (((u : VPlus), 0) : Vnat) := by
  intro n y
  have h := congrArg (fun F : Module.End ℂ Vnat => F y) (sigNat_YnatU_V0 Dnat u (-n - 1))
  simp only [Module.End.mul_apply] at h
  rw [sigmaEquiv_apply, sigmaEquiv_apply, sigmaEquiv_apply, VnatVOA_smul_eq_YnatU, h, sigNat_V0,
    VnatVOA_smul_eq_YnatU]
  rfl

/-- The twisted generator `x = h₀(−½)𝟙 ⊗ t_s`. -/
noncomputable abbrev xGen : TP := x0T (tF Dnat.s)

theorem xGen_mem : xGen ∈ TPframe Dnat.s := x0T_mem (tF_mem _)

/-- `σ` intertwines `(0, x)` (the σ-key). -/
theorem sigma_intertwines_x : Intertwines VnatVOA sigmaEquiv ((0, xGen) : Vnat) := by
  intro n y
  have hc := congrArg (fun F => F (-n - 1)) sigmaKey_Dnat.conj_eq
  simp only [conjF_apply] at hc
  rw [sigmaEquiv_apply, sigmaEquiv_apply, sigmaEquiv_apply, VnatVOA_smul_eq_YnatT, ← hc,
    sigNat_Ts Dnat xGen_mem, VnatVOA_smul_eq_YnatU, Module.End.mul_apply, Module.End.mul_apply,
    sigNat_invol]

/-- `σ`-stability: if `σ` intertwines `u`, it intertwines `σ u`. -/
theorem intertwines_sigma {u : Vnat} (h : Intertwines VnatVOA sigmaEquiv u) :
    Intertwines VnatVOA sigmaEquiv (sigmaEquiv u) := by
  intro n y
  have h1 := h n (sigmaEquiv y)
  simp only [sigmaEquiv_apply, sigNat_invol] at h1 ⊢
  rw [← h1, sigNat_invol]

theorem sigma_omega : sigNat Dnat omegaNat = omegaNat := by
  have h := sigNat_V0 Dnat V0P.conformalVector
  rw [v0Sigma.map_omega] at h
  exact h

/-- ⭐ **`σ♮ ∈ Aut V♮`.** -/
noncomputable def sigmaAut : AutVnat where
  toLinearEquiv := sigmaEquiv
  map_smul' := by
    set S := intertwineSub VnatVOA sigmaEquiv with hS
    have hclosed : ∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, VnatVOA.smul u n v ∈ S :=
      fun u hu v hv n => intertwines_smul hu hv n
    have hx : ((0, xGen) : Vnat) ∈ S := sigma_intertwines_x
    have hV0 : ∀ u ∈ V0Sub.carrier, ((u, 0) : Vnat) ∈ S := fun u hu =>
      sigma_intertwines_V0 ⟨u, hu⟩
    -- `0 × T_s⁺ ⊆ S`
    have hTs : ∀ y ∈ TPframe Dnat.s, ((0, y) : Vnat) ∈ S := by
      intro y hy
      rw [← span_smul_frameX0T (tF_mem Dnat.s) (tF_ne Dnat.s)] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u, hu, n, rfl⟩ := hz
        have h1 : VnatVOA.smul ((u, 0) : Vnat) n ((0, xGen) : Vnat)
            = ((0, mode (plusModule.YM u) n xGen) : Vnat) := by
          rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
        change ((0, mode (plusModule.YM u) n xGen) : Vnat) ∈ S
        rw [← h1]
        refine hclosed _ (hV0 u ?_) _ hx n
        rw [V0Sub_carrier]; exact hu
      | zero => exact S.zero_mem
      | add a b _ _ ha hb =>
        have := S.add_mem ha hb
        rwa [Prod.mk_add_mk, add_zero] at this
      | smul c a _ ha =>
        have := S.smul_mem c ha
        rwa [Prod.smul_mk, smul_zero] at this
    -- `V₃⁺ × 0 ⊆ S`
    have hV3 : ∀ v ∈ frameSector 1, ((v, 0) : Vnat) ∈ S := by
      intro v hv
      have hΦ := Dnat.Φ_mem v hv
      have h1 : sigmaEquiv ((0, Dnat.Φ v) : Vnat) = ((v, 0) : Vnat) := by
        rw [sigmaEquiv_apply, sigNat_Ts Dnat hΦ, Dnat.ΨΦ v hv]
      rw [← h1]
      exact intertwines_sigma (hTs _ hΦ)
    -- `V_Λ⁺ × 0 ⊆ S`
    have hU : ∀ v : VPlus, ((v, 0) : Vnat) ∈ S := by
      intro v
      have hv : v ∈ V0Sub.carrier ⊔ frameSector 1 := by
        rw [V0_isCompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      have := S.add_mem (hV0 a ha) (hV3 b hb)
      rwa [Prod.mk_add_mk, add_zero] at this
    -- `0 × T⁺ ⊆ S`
    have hT : ∀ t : TP, ((0, t) : Vnat) ∈ S := by
      intro t
      have ht : t ∈ Submodule.span ℂ {x : TP | ∃ (u : SkewVP) (n : ℤ) (i : Unit),
          x = mode (plusModule.YM u) n ((fun _ : Unit => xGen) i)} := by
        rw [modeSpan_x0T (tF_ne Dnat.s)]; exact Submodule.mem_top
      induction ht using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨u, n, -, rfl⟩ := hz
        have h1 : VnatVOA.smul ((u, 0) : Vnat) n ((0, xGen) : Vnat)
            = ((0, mode (plusModule.YM u) n xGen) : Vnat) := by
          rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
        rw [← h1]
        exact hclosed _ (hU u) _ hx n
      | zero => exact S.zero_mem
      | add a b _ _ ha hb =>
        have := S.add_mem ha hb
        rwa [Prod.mk_add_mk, add_zero] at this
      | smul c a _ ha =>
        have := S.smul_mem c ha
        rwa [Prod.smul_mk, smul_zero] at this
    intro u n v
    have hu : u ∈ S := by
      obtain ⟨a, t⟩ := u
      have := S.add_mem (hU a) (hT t)
      rwa [Prod.mk_add_mk, add_zero, zero_add] at this
    exact hu n v
  map_vacuum := by
    change sigNat Dnat VnatVOA.vacuum = VnatVOA.vacuum
    rw [VnatVOA_vacuum]
    exact sigNat_vac Dnat
  map_omega := by
    change sigNat Dnat VnatVOA.conformalVector = VnatVOA.conformalVector
    rw [VnatVOA_conformalVector]
    exact sigma_omega

@[simp] theorem sigmaAut_apply (v : Vnat) : sigmaAut v = sigNat Dnat v := rfl

end VOA.Moonshine.AutMonster
