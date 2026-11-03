/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TrialityTwGeneric
import VOA.Moonshine.CyclicTwisted
import VOA.Moonshine.FrameBridgeGolay

/-!
# The triality `σ` on the twisted sectors: API, uniqueness, and the `T₀` ambiguity
(Moonshine step M8g twisted half)

FLM's triality `σ ∈ Aut V♮` restricts to `v0Sigma ∈ Aut V₀⁺` and must map
`V₃⁺ → T₀⁺` and `T₃⁺ → T₃⁺` as **`v0Sigma`-twisted `V₀⁺`-module maps**:

  `σ (u₍ₙ₎ x) = (v0Sigma u)₍ₙ₎ (σ x)`   for `u ∈ V₀⁺`.

This file sets up that notion for the library's sectors and proves everything about it that
does not need the existence of `σ` (not proved in this file).

## Main definitions
* `actV u n = u₍ₙ₎` on `V_Λ⁺` and `actT u n = u₍ₙ₎` on `TP = (V_Λ^T)⁺` (`plusModule`), for
  `u ∈ V₀⁺ = V0Sub.carrier`; `sig u = v0Sigma u`.
* `IsSigmaV3T Φ` — `Φ : V_Λ⁺ → TP` is a `v0Sigma`-twisted intertwiner on `V₃⁺ = frameSector 1`;
  `IsSigmaTT s Φ` — same on `T_s⁺ = TPframe s`, valued in `TP`;
  `IsSigmaTV s Φ` — `Φ : TP → V_Λ⁺` twisted on `T_s⁺`.

## Main results
* `IsSigmaV3T.eqOn` / `IsSigmaTT.eqOn` / `IsSigmaTV.eqOn` — **uniqueness**: a twisted
  intertwiner out of `V₃⁺` (resp. `T_s⁺`) is determined by its value on the explicit cyclic
  vector `x₀ = e^β + e^{−β}` (resp. `h₀(−½)𝟙 ⊗ t₀`) of `cyclic_V3` (resp. `cyclic_TPframe`).
* `IsSigmaV3T.L0_comm`, `IsSigmaTT.L0_comm` — every such map commutes with `L₀`
  (weight preservation), since `v0Sigma ω = ω`.
* `sigmaV3T_exists_iff`, `sigmaTT_exists_iff` — **existence ⇔ annihilator compatibility**
  of `(x₀, y₀)` (`TrialityTw.exists_twInt_iff`): `σ` may be *defined* as the unique twisted
  intertwiner with `x₀ ↦ y₀` once compatibility is proved.  Compatibility is NOT proved here.
* `sigma_involutive_V3` — if `Φ : V₃⁺ → T_s⁺` and `Ψ : T_s⁺ → V₃⁺` are twisted intertwiners
  with `Ψ (Φ x₀) = x₀`, then `Ψ ∘ Φ = id` on `V₃⁺` (uses `v0Sigma_sq`); `sigma_involutive_TT`
  for `T_s⁺ → T_s⁺`.
* `golayE_not_determined` — **the defining property of `golayE` does not determine it at
  `w = 8e₀`**: `golayE` and `golayE + e_β` (`e_β(a) = (−1)^{⟨β, 2a⟩}`, `β = uVec`) both satisfy
  the specification `exists_golayE` used to build `v0Sigma`, and they differ by a sign at the
  preimage `w₀` of `frameW`.  Consequence (Notes §3): which of `TPframe 0`, `TPframe 1` is the
  image `σ(V₃⁺)` (FLM's `T₀⁺`) is **not determined by the library's definitions** — the two
  choices give `v0Sigma`'s conjugate by the `V♮`-automorphism `(−1)^{⟨β,·⟩} ⊕ (1 ⊗ e_β)`,
  which swaps `TPframe 0 ↔ TPframe 1` and fixes `V₃⁺`.

## Status
`sorry`-free; `#print axioms` of every declaration: `[propext, Classical.choice, Quot.sound]`.
**Not proved: the existence of `σ` on `V₃⁺`, `T₀⁺`, `T₃⁺`** (the annihilator compatibility of
`(x₀, y₀)` for a suitable `y₀`).  It was verified numerically at weight 2.  Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.TrialityTw

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open Module (End)

/-! ## §1  The actions and the twist -/

/-- `u₍ₙ₎` on `V_Λ⁺`, for `u ∈ V₀⁺`. -/
noncomputable def actV (u : V0Sub.carrier) (n : ℤ) : VPlus →ₗ[ℂ] VPlus :=
  mode (leechVOAPlus.Y (u : VPlus)) n

/-- `u₍ₙ₎` on `TP = (V_Λ^T)⁺` (the `V_Λ⁺`-module `plusModule`), for `u ∈ V₀⁺`. -/
noncomputable def actT (u : V0Sub.carrier) (n : ℤ) : TP →ₗ[ℂ] TP :=
  mode (Moonshine.plusModule.YM (u : VPlus)) n

/-- The triality on `V₀⁺`. -/
noncomputable def sig (u : V0Sub.carrier) : V0Sub.carrier := v0Sigma u

theorem sig_sig (u : V0Sub.carrier) : sig (sig u) = u := by
  have h := congrArg (fun g : Aut V0P => g u) v0Sigma_sq
  simpa [sig] using h

theorem actV_apply (u : V0Sub.carrier) (n : ℤ) (x : VPlus) :
    actV u n x = leechVOAPlus.smul (u : VPlus) n x := rfl

theorem mem_V0 (u : V0Sub.carrier) : (u : VPlus) ∈ frameSector 0 := by
  rw [← V0Sub_carrier]; exact u.2

/-- `V₃⁺` is stable under `V₀⁺`. -/
theorem actV_stab : ∀ u ∈ (Set.univ : Set V0Sub.carrier), ∀ (n : ℤ),
    ∀ x ∈ frameSector 1, actV u n x ∈ frameSector 1 := by
  intro u _ n x hx
  have := frameSector_smul_mem (mem_V0 u) hx n
  rwa [zero_add] at this

/-- `T_s⁺` is stable under `V₀⁺`. -/
theorem actT_stab (s : ZMod 2) : ∀ u ∈ (Set.univ : Set V0Sub.carrier), ∀ (n : ℤ),
    ∀ x ∈ TPframe s, actT u n x ∈ TPframe s := by
  intro u _ n x hx
  rw [actT, mem_TPframe, mode_plusModule]
  have hfix : frameAut ((u : VPlus) : LatModuleGen leech) = u := by
    rw [frameAut_apply, (mem_frameSector.mp (mem_V0 u)), Extraspecial.sgn_zero, one_smul]
  exact YM_mem_twFrame hfix _ hx

/-! ## §2  Cyclicity in the generic form -/

theorem set_V0_eq (x₀ : VPlus) :
    {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n x₀}
      = {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = leechVOAPlus.smul u n x₀} := by
  ext y
  constructor
  · rintro ⟨u, -, n, rfl⟩
    exact ⟨u, mem_V0 u, n, rfl⟩
  · rintro ⟨u, hu, n, rfl⟩
    rw [← V0Sub_carrier] at hu
    exact ⟨⟨u, hu⟩, Set.mem_univ _, n, rfl⟩

theorem set_T0_eq (x₀ : TP) :
    {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x₀}
      = {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = mode (Moonshine.plusModule.YM u) n x₀} := by
  ext y
  constructor
  · rintro ⟨u, -, n, rfl⟩
    exact ⟨u, mem_V0 u, n, rfl⟩
  · rintro ⟨u, hu, n, rfl⟩
    rw [← V0Sub_carrier] at hu
    exact ⟨⟨u, hu⟩, Set.mem_univ _, n, rfl⟩

/-- `V₃⁺ = span{u₍ₙ₎ x₀}`, `x₀ = e^β + e^{−β}` (`β ∉ Λ₀`), in the generic form. -/
theorem cyc_V3 {β : leech.carrier} (hβ : β ∉ lambda0) :
    Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n (frameX0P β)}
      = frameSector 1 := by
  rw [set_V0_eq]; exact span_smul_frameX0 hβ

/-- The cyclic vector `h₀(−½)𝟙 ⊗ t₀` of `T_s⁺`. -/
noncomputable def x0T (t₀ : TLeechT) : TP := ⟨frameX0T t₀, frameX0T_mem_TP t₀⟩

theorem x0T_mem {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) : x0T t₀ ∈ TPframe s :=
  frameX0T_mem_twFrame ht₀

/-- `T_s⁺ = span{u₍ₙ₎ x₀}`, `x₀ = h₀(−½)𝟙 ⊗ t₀` (`0 ≠ t₀ ∈ T_s`), in the generic form. -/
theorem cyc_T {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0) :
    Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n (x0T t₀)}
      = TPframe s := by
  rw [set_T0_eq]; exact span_smul_frameX0T ht₀ h0

/-! ## §3  `σ`-twisted intertwiners on the sectors -/

/-- `Φ : V_Λ⁺ → TP` is a `v0Sigma`-twisted `V₀⁺`-intertwiner on `V₃⁺`. -/
def IsSigmaV3T (Φ : VPlus →ₗ[ℂ] TP) : Prop :=
  IsTwInt actV actT sig Set.univ (frameSector 1) Φ

/-- `Φ : TP → TP` is a `v0Sigma`-twisted `V₀⁺`-intertwiner on `T_s⁺`. -/
def IsSigmaTT (s : ZMod 2) (Φ : TP →ₗ[ℂ] TP) : Prop :=
  IsTwInt actT actT sig Set.univ (TPframe s) Φ

/-- `Φ : TP → V_Λ⁺` is a `v0Sigma`-twisted `V₀⁺`-intertwiner on `T_s⁺`. -/
def IsSigmaTV (s : ZMod 2) (Φ : TP →ₗ[ℂ] VPlus) : Prop :=
  IsTwInt actT actV sig Set.univ (TPframe s) Φ

/-- **Uniqueness on `V₃⁺`**: determined by the image of `x₀ = e^β + e^{−β}`. -/
theorem IsSigmaV3T.eqOn {β : leech.carrier} (hβ : β ∉ lambda0) {Φ Ψ : VPlus →ₗ[ℂ] TP}
    (hΦ : IsSigmaV3T Φ) (hΨ : IsSigmaV3T Ψ) (h : Φ (frameX0P β) = Ψ (frameX0P β)) :
    ∀ x ∈ frameSector 1, Φ x = Ψ x :=
  eqOn_of_cyclic (frameX0_mem_frameSector_one hβ) (cyc_V3 hβ) hΦ hΨ h

/-- **Uniqueness on `T_s⁺`**: determined by the image of `x₀ = h₀(−½)𝟙 ⊗ t₀`. -/
theorem IsSigmaTT.eqOn {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    {Φ Ψ : TP →ₗ[ℂ] TP} (hΦ : IsSigmaTT s Φ) (hΨ : IsSigmaTT s Ψ) (h : Φ (x0T t₀) = Ψ (x0T t₀)) :
    ∀ x ∈ TPframe s, Φ x = Ψ x :=
  eqOn_of_cyclic (x0T_mem ht₀) (cyc_T ht₀ h0) hΦ hΨ h

/-- Uniqueness for `T_s⁺ → V_Λ⁺`. -/
theorem IsSigmaTV.eqOn {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    {Φ Ψ : TP →ₗ[ℂ] VPlus} (hΦ : IsSigmaTV s Φ) (hΨ : IsSigmaTV s Ψ) (h : Φ (x0T t₀) = Ψ (x0T t₀)) :
    ∀ x ∈ TPframe s, Φ x = Ψ x :=
  eqOn_of_cyclic (x0T_mem ht₀) (cyc_T ht₀ h0) hΦ hΨ h

/-- The conformal vector of `V₀⁺` is fixed by the twist. -/
theorem sig_omega : sig V0P.conformalVector = V0P.conformalVector := v0Sigma.map_omega

/-- **Weight preservation on `V₃⁺`**: a twisted intertwiner commutes with `L₀ = ω₍₁₎`. -/
theorem IsSigmaV3T.L0_comm {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ) {x : VPlus}
    (hx : x ∈ frameSector 1) :
    Φ (mode (leechVOAPlus.Y leechVOAPlus.conformalVector) 1 x)
      = mode (Moonshine.plusModule.YM leechVOAPlus.conformalVector) 1 (Φ x) := by
  have h := hΦ V0P.conformalVector (Set.mem_univ _) 1 x hx
  rw [sig_omega] at h
  exact h

/-- **Weight preservation on `T_s⁺`.** -/
theorem IsSigmaTT.L0_comm {s : ZMod 2} {Φ : TP →ₗ[ℂ] TP} (hΦ : IsSigmaTT s Φ) {x : TP}
    (hx : x ∈ TPframe s) :
    Φ (mode (Moonshine.plusModule.YM leechVOAPlus.conformalVector) 1 x)
      = mode (Moonshine.plusModule.YM leechVOAPlus.conformalVector) 1 (Φ x) := by
  have h := hΦ V0P.conformalVector (Set.mem_univ _) 1 x hx
  rw [sig_omega] at h
  exact h

/-! ## §4  Existence ⇔ annihilator compatibility -/

/-- **`σ : V₃⁺ → TP` with `x₀ ↦ y₀` exists iff `(x₀, y₀)` is annihilator-compatible.** -/
theorem sigmaV3T_exists_iff {β : leech.carrier} (hβ : β ∉ lambda0) (y₀ : TP) :
    (∃ Φ : VPlus →ₗ[ℂ] TP, IsSigmaV3T Φ ∧ Φ (frameX0P β) = y₀)
      ↔ AnnCompat actV actT sig Set.univ (frameX0P β) y₀ :=
  exists_twInt_iff actV_stab (frameX0_mem_frameSector_one hβ) (cyc_V3 hβ) y₀

/-- **`σ : T_s⁺ → TP` with `x₀ ↦ y₀` exists iff `(x₀, y₀)` is annihilator-compatible.** -/
theorem sigmaTT_exists_iff {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    (y₀ : TP) :
    (∃ Φ : TP →ₗ[ℂ] TP, IsSigmaTT s Φ ∧ Φ (x0T t₀) = y₀)
      ↔ AnnCompat actT actT sig Set.univ (x0T t₀) y₀ :=
  exists_twInt_iff (actT_stab s) (x0T_mem ht₀) (cyc_T ht₀ h0) y₀

/-- `σ : T_s⁺ → V_Λ⁺` with `x₀ ↦ y₀` exists iff `(x₀, y₀)` is annihilator-compatible. -/
theorem sigmaTV_exists_iff {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    (y₀ : VPlus) :
    (∃ Φ : TP →ₗ[ℂ] VPlus, IsSigmaTV s Φ ∧ Φ (x0T t₀) = y₀)
      ↔ AnnCompat actT actV sig Set.univ (x0T t₀) y₀ :=
  exists_twInt_iff (actT_stab s) (x0T_mem ht₀) (cyc_T ht₀ h0) y₀

/-! ## §5  Involutivity from the cyclic vector -/

/-- **Involutivity on `V₃⁺`.**  If `Φ : V₃⁺ → T_s⁺` and `Ψ : T_s⁺ → V₃⁺` are
`v0Sigma`-twisted and `Ψ (Φ x₀) = x₀`, then `Ψ ∘ Φ = id` on `V₃⁺`. -/
theorem sigma_involutive_V3 {β : leech.carrier} (hβ : β ∉ lambda0) {s : ZMod 2}
    {Φ : VPlus →ₗ[ℂ] TP} {Ψ : TP →ₗ[ℂ] VPlus} (hΦ : IsSigmaV3T Φ) (hΨ : IsSigmaTV s Ψ)
    (hmap : ∀ x ∈ frameSector 1, Φ x ∈ TPframe s) (h : Ψ (Φ (frameX0P β)) = frameX0P β) :
    ∀ x ∈ frameSector 1, Ψ (Φ x) = x :=
  comp_eqOn_id (frameX0_mem_frameSector_one hβ) (cyc_V3 hβ) hΦ hΨ hmap
    (fun _ _ => Set.mem_univ _) (fun u _ => sig_sig u) h

/-- **Involutivity on `T_s⁺`.**  A `v0Sigma`-twisted `Φ : T_s⁺ → T_s⁺` with
`Φ (Φ x₀) = x₀` satisfies `Φ ∘ Φ = id` on `T_s⁺`. -/
theorem sigma_involutive_TT {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    {Φ : TP →ₗ[ℂ] TP} (hΦ : IsSigmaTT s Φ) (hmap : ∀ x ∈ TPframe s, Φ x ∈ TPframe s)
    (h : Φ (Φ (x0T t₀)) = x0T t₀) : ∀ x ∈ TPframe s, Φ (Φ x) = x :=
  comp_eqOn_id (x0T_mem ht₀) (cyc_T ht₀ h0) hΦ hΦ hmap (fun _ _ => Set.mem_univ _)
    (fun u _ => sig_sig u) h

/-! ## §6  The choice in `golayE` is not pinned at `w = 8e₀` -/

/-- The odd Leech vector `u = (5, 1²³)` (`Leech.uVec`), `u ∉ Λ₀`. -/
noncomputable def uβ : leech.carrier := ⟨Leech.uVec, Or.inr (by simp)⟩

/-- The `±1` character `e_β(a) = (−1)^{⟨β, ι a⟩}` of `Λ₀` (`ι = inclΛ`, `β = uβ`). -/
noncomputable def eBeta : lam0.carrier →+ Additive ℂˣ :=
  (zmultiplesHom (Additive ℂˣ) (Additive.ofMul (-1 : ℂˣ))).comp
    (((leech.form uβ).toAddMonoidHom).comp (inclΛ.toAddMonoidHom))

theorem charVal_eBeta (a : lam0.carrier) :
    charVal lam0 eBeta a = (-1 : ℂ) ^ (leech.form uβ (inclΛ a)) := by
  simp [charVal, eBeta, zmultiplesHom_apply]

theorem two_nsmul_eBeta : 2 • eBeta = 0 := by
  ext a
  simp [eBeta, zmultiplesHom_apply]
  exact (Int.even_or_odd _).elim (fun h => Or.inl h.neg_one_zpow) (fun h => Or.inr h.neg_one_zpow)

theorem frameChar_frameW : frameChar frameW = 0 := by
  have h := frameW_sign frameW
  have h8 : leech.form frameW frameW = 8 := by
    rw [leech_form_frameW]; rfl
  rw [h8, chiSign] at h
  norm_num at h
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (frameChar frameW) with hz | hz
  · exact hz
  · exfalso
    rw [hz, Extraspecial.sgn_one] at h
    norm_num at h

theorem frameW_mem_lambda0 : frameW ∈ lambda0 := (mem_lambda0 _).mpr frameChar_frameW

theorem frameChar_uβ : frameChar uβ = 1 := frameChar_uVec

/-- **`golayE` is not determined at `w₀`** by the specification it was chosen from.
Both `golayE` and `golayE + e_β` satisfy `exists_golayE`'s defining identity
`ψ = g_e θ g_e⁻¹`, and their values at the preimage `w₀` of `frameW = 8e₀` differ by a sign. -/
theorem golayE_not_determined :
    ∃ e₁ e₂ : lam0.carrier →+ Additive ℂˣ,
      (∀ x, lam0Psi x = charLat lam0 e₁ (thetaLat lam0 (charLat lam0 (-e₁) x))) ∧
      (∀ x, lam0Psi x = charLat lam0 e₂ (thetaLat lam0 (charLat lam0 (-e₂) x))) ∧
      ∃ w₀ : lam0.carrier, inclΛ w₀ = frameW ∧ charVal lam0 e₂ w₀ = -charVal lam0 e₁ w₀ := by
  refine ⟨golayE, golayE + eBeta, lam0Psi_eq, ?_, ?_⟩
  · intro x
    rw [lam0Psi_eq, charLat_thetaLat_conj lam0 lam0_posDef,
      charLat_thetaLat_conj lam0 lam0_posDef, smul_add, two_nsmul_eBeta, add_zero]
  · obtain ⟨w₀, hw₀⟩ := (mem_range_inclΛ frameW).mpr frameW_mem_lambda0
    refine ⟨w₀, hw₀, ?_⟩
    have hadd : charVal lam0 (golayE + eBeta) w₀ = charVal lam0 golayE w₀ * charVal lam0 eBeta w₀ := by
      simp [charVal]
    rw [hadd, charVal_eBeta, hw₀]
    have hs := frameW_sign uβ
    rw [chiSign, frameChar_uβ, Extraspecial.sgn_one] at hs
    have hsym : leech.form uβ frameW = leech.form frameW uβ :=
      LinearMap.BilinForm.isSymm_def.mp leech.isSymm uβ frameW
    rw [hsym, hs]
    ring

end VOA.Moonshine.TrialityTw
