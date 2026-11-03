/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8hKeySpan

/-!
# M8h key step, part 2: the would-be triality `σ♮` on `V♮` and `V₀⁺`-only uniqueness

Given the twisted-sector σ maps (the M8g twisted half, `SigmaExist*`, `SigmaAssemble*`), we assemble the
would-be FLM triality `σ♮ : V♮ → V♮` **sector by sector**:

| sector | `σ♮` |
|---|---|
| `V₀⁺ = frameSector 0` | `v0Sigma` (`FrameBridgeGolay.lean`) |
| `V₃⁺ = frameSector 1` | `Φ : V₃⁺ → T_s⁺` (`IsSigmaV3T`) |
| `T_s⁺ = TPframe s` | `Ψ : T_s⁺ → V₃⁺` (`IsSigmaTV s`) |
| `T_{s+1}⁺` | `Θ : T_{s+1}⁺ → T_{s+1}⁺` (`IsSigmaTT (s+1)`) |

(`s` is FLM's `T₀`-label, which the library's definitions do not pin down,
`golayE_not_determined`; it is part of the data.)

## Main definitions and results
* `SigmaData` — the σ-existence data: `Φ, Ψ, Θ` with the three `IsSigma…` predicates, the sector
  mapping properties and mutual inverseness (`Ψ Φ = id`, `Φ Ψ = id`, `Θ Θ = id`).
* `sigNat D : End ℂ Vnat` — the block operator `σ♮`; `sigNat_V0`, `sigNat_V3`, `sigNat_Ts`,
  `sigNat_Ts1` (the sector table); `sigNat_sq : σ♮ * σ♮ = 1`.
* `sigNat_YnatU_V0 : σ♮ ∘ Y♮(u) = Y♮(σu) ∘ σ♮` for `u ∈ V₀⁺` — this is *exactly* the
  twisted-intertwiner property of the three maps plus `v0Sigma ∈ Aut V₀⁺`;
  `sigNat_Tnat : σ♮ ∘ L₋₁ = L₋₁ ∘ σ♮` (the case `u = ω`).
* `conjF σ A = σ A σ` with `local_conjF`, `dCovariant_conjF`; `conjF_YnatU_V0`.
* `eq_zero_of_V0local` — **the circularity-free uniqueness lemma**: a field on `V♮` that is
  local with `Y♮(u)` for every `u ∈ V₀⁺` (only!) and kills the four `V₀⁺`-cyclic vectors
  `𝟙`, `(e^β+e^{−β}, 0)`, `(0, h₀(−½)𝟙 ⊗ t₀)`, `(0, h₀(−½)𝟙 ⊗ t₁)` is zero.

## Circularity
`M8h0.YnatT_eq_of_creates` cannot be used to identify `σ♮ Y♮(v) σ♮` with `Y♮(σ♮ v)` for
`v ∈ V₃⁺`: it requires locality with `Y♮(u)` for **all** `u ∈ V_Λ⁺`, and locality of
`σ♮ Y♮(v) σ♮` with `Y♮(u)`, `u ∈ V₃⁺`, is the conjugate statement `Local (Y♮ v) (σ♮ Y♮(u) σ♮)`
— the identity to be proved (for `u`).  `eq_zero_of_V0local` uses `V₀⁺`-locality only, which
`σ♮` transports for free (`conjF_YnatU_V0`), at the price of testing on the cyclic vectors of all
four `V₀⁺`-sectors (`cyclic_V3`, `cyclic_TPframe`).  It never uses (4.23).

## Status
`sorry`-free.  Conditional only through the displayed `SigmaData` (whose existence is the M8g
twisted half, open at the time of writing).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8hKey

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen

/-! ## §1  Conjugation of fields -/

section Conj

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `(z₁−z₂)ᴺ` commutes with a coefficientwise linear map. -/
theorem mulBySubPow_map {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
    [Module ℂ W'] (φ : W →ₗ[ℂ] W') (N : ℕ) (f : FormalDist₂ W) :
    mulBySubPow N (fun m n => φ (f m n)) = fun m n => φ (mulBySubPow N f m n) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [mulBySubPow_succ, LinearMap.comp_apply, ih, mulBySubPow_succ, LinearMap.comp_apply]
    funext m n
    simp only [mulBySub_apply, map_sub]

/-- The conjugate field `σ A(z) σ`. -/
def conjF (σ : End ℂ V) (A : FormalDist (End ℂ V)) : FormalDist (End ℂ V) :=
  fun k => σ * A k * σ

@[simp] theorem conjF_apply (σ : End ℂ V) (A : FormalDist (End ℂ V)) (k : ℤ) :
    conjF σ A k = σ * A k * σ := rfl

/-- Conjugation by an involution preserves locality. -/
theorem local_conjF {σ : End ℂ V} (hσ : σ * σ = 1) {A B : FormalDist (End ℂ V)}
    (h : Local A B) : Local (conjF σ A) (conjF σ B) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have hb : bracketDist (conjF σ A) (conjF σ B)
      = fun m n => (LinearMap.mulLeft ℂ σ ∘ₗ LinearMap.mulRight ℂ σ) (bracketDist A B m n) := by
    funext m n
    simp only [bracketDist_apply, conjF_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply]
    have e1 : σ * A m * σ * (σ * B n * σ) = σ * (A m * B n) * σ := by
      simp only [mul_assoc]; rw [← mul_assoc σ σ, hσ, one_mul]
    have e2 : σ * B n * σ * (σ * A m * σ) = σ * (B n * A m) * σ := by
      simp only [mul_assoc]; rw [← mul_assoc σ σ, hσ, one_mul]
    rw [e1, e2, ← sub_mul, ← mul_sub, mul_assoc]
  rw [hb, mulBySubPow_map, hN]
  funext m n
  exact map_zero _

/-- Conjugation by an operator commuting with `T` preserves `T`-covariance. -/
theorem dCovariant_conjF {σ T : End ℂ V} (hT : σ * T = T * σ)
    {A : FormalDist (End ℂ V)} (h : DCovariant T A) : DCovariant T (conjF σ A) := by
  intro m
  have h' := h m
  simp only [conjF_apply]
  have e1 : T * (σ * A m * σ) = σ * (T * A m) * σ := by
    have : T * σ = σ * T := hT.symm
    rw [← mul_assoc, ← mul_assoc, this, mul_assoc σ T]
  have e2 : σ * A m * σ * T = σ * (A m * T) * σ := by
    rw [mul_assoc, hT, ← mul_assoc, mul_assoc σ]
  rw [e1, e2, ← sub_mul, ← mul_sub, h', mul_smul_comm, smul_mul_assoc]

end Conj

/-! ## §2  Sector decompositions -/

theorem frameSector_isCompl : IsCompl (frameSector 0) (frameSector 1) := by
  rw [frameSector_zero_eq, frameSector_one_eq]
  exact isCompl_ker_sub_one_ker_add_one plusFrame plusFrame_plusFrame

theorem V0_isCompl : IsCompl V0Sub.carrier (frameSector 1) := by
  rw [V0Sub_carrier]; exact frameSector_isCompl

theorem TPframe_isCompl' (s : ZMod 2) : IsCompl (TPframe s) (TPframe (s + 1)) := by
  fin_cases s
  · exact TPframe_isCompl
  · exact TPframe_isCompl.symm

theorem YnatU_apply (u : SkewVP) (k : ℤ) (x : Vnat) :
    YnatU u k x = (leechVOAPlus.Y u k x.1, plusModule.YM u k x.2) := by
  simp [YnatU, diagF, blockF_apply, blockOp_apply]

theorem YnatT_apply (t : TP) (k : ℤ) (x : Vnat) :
    YnatT leechWbar t k x = (leechWbar t k x.2, leechWsk t k x.1) := by
  simp [YnatT, offF, blockF_apply, blockOp_apply]

/-- `Y(u)` on `V_Λ⁺` in mode form. -/
theorem Y_eq_actV (u : V0Sub.carrier) (k : ℤ) (x : VPlus) :
    leechVOAPlus.Y (u : VPlus) k x = actV u (-k - 1) x := by
  rw [actV, mode_apply, show -(-k - 1) - 1 = k by ring]

theorem YM_eq_actT (u : V0Sub.carrier) (k : ℤ) (x : TP) :
    plusModule.YM (u : VPlus) k x = actT u (-k - 1) x := by
  rw [actT, mode_apply, show -(-k - 1) - 1 = k by ring]

/-- **Four-sector extensionality** on `V♮`. -/
theorem vnat_ext (s : ZMod 2) {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : Vnat →ₗ[ℂ] M}
    (h0 : ∀ a ∈ V0Sub.carrier, f (a, 0) = g (a, 0)) (h3 : ∀ a ∈ frameSector 1, f (a, 0) = g (a, 0))
    (hs : ∀ t ∈ TPframe s, f (0, t) = g (0, t)) (hs1 : ∀ t ∈ TPframe (s + 1), f (0, t) = g (0, t)) :
    f = g := by
  refine LinearMap.ext fun x => ?_
  have hx : x = (V0Sub.carrier.projection (frameSector 1) V0_isCompl x.1, 0)
      + ((frameSector 1).projection V0Sub.carrier V0_isCompl.symm x.1, 0)
      + (0, (TPframe s).projection (TPframe (s + 1)) (TPframe_isCompl' s) x.2)
      + (0, (TPframe (s + 1)).projection (TPframe s) (TPframe_isCompl' s).symm x.2) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, add_zero]
      exact (Submodule.projection_add_projection_eq_self V0_isCompl x.1).symm
    · simp only [Prod.snd_add, zero_add]
      exact (Submodule.projection_add_projection_eq_self (TPframe_isCompl' s) x.2).symm
  rw [hx, map_add, map_add, map_add, map_add, map_add, map_add,
    h0 _ (Submodule.projection_apply_mem _ _), h3 _ (Submodule.projection_apply_mem _ _),
    hs _ (Submodule.projection_apply_mem _ _), hs1 _ (Submodule.projection_apply_mem _ _)]

/-! ## §3  The σ-existence data and `σ♮` -/

/-- **The σ-existence data** (M8g twisted half): the three twisted-sector maps of FLM's triality,
as `v0Sigma`-twisted `V₀⁺`-intertwiners, with their sector mapping properties and mutual
inverseness.  `s` labels the twisted frame sector `T_s⁺ = σ(V₃⁺)` (FLM's `T₀⁺`). -/
structure SigmaData where
  /-- FLM's `T₀`-label: `σ(V₃⁺) = TPframe s`. -/
  s : ZMod 2
  /-- `σ : V₃⁺ → T_s⁺`. -/
  Φ : VPlus →ₗ[ℂ] TP
  /-- `σ : T_s⁺ → V₃⁺`. -/
  Ψ : TP →ₗ[ℂ] VPlus
  /-- `σ : T_{s+1}⁺ → T_{s+1}⁺`. -/
  Θ : TP →ₗ[ℂ] TP
  isSigma_Φ : IsSigmaV3T Φ
  isSigma_Ψ : IsSigmaTV s Ψ
  isSigma_Θ : IsSigmaTT (s + 1) Θ
  Φ_mem : ∀ x ∈ frameSector 1, Φ x ∈ TPframe s
  Ψ_mem : ∀ t ∈ TPframe s, Ψ t ∈ frameSector 1
  Θ_mem : ∀ t ∈ TPframe (s + 1), Θ t ∈ TPframe (s + 1)
  ΨΦ : ∀ x ∈ frameSector 1, Ψ (Φ x) = x
  ΦΨ : ∀ t ∈ TPframe s, Φ (Ψ t) = t
  ΘΘ : ∀ t ∈ TPframe (s + 1), Θ (Θ t) = t

/-- `v0Sigma` on `V_Λ⁺`, extended by `0` on `V₃⁺`. -/
noncomputable def sig0 : VPlus →ₗ[ℂ] VPlus :=
  V0Sub.carrier.subtype ∘ₗ v0Sigma.toLinearEquiv.toLinearMap ∘ₗ
    V0Sub.carrier.projectionOnto (frameSector 1) V0_isCompl

theorem sig0_V0 (a : V0Sub.carrier) : sig0 (a : VPlus) = ((v0Sigma a : V0Sub.carrier) : VPlus) := by
  simp [sig0]

theorem sig0_V3 {a : VPlus} (ha : a ∈ frameSector 1) : sig0 a = 0 := by
  rw [sig0, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_right V0_isCompl ha, map_zero, map_zero]

variable (D : SigmaData)

/-- **The would-be triality `σ♮` on `V♮`**, sector by sector. -/
noncomputable def sigNat : End ℂ Vnat :=
  blockOp sig0
    (D.Ψ ∘ₗ (TPframe D.s).projection (TPframe (D.s + 1)) (TPframe_isCompl' D.s))
    (D.Φ ∘ₗ (frameSector 1).projection V0Sub.carrier V0_isCompl.symm)
    (D.Θ ∘ₗ (TPframe (D.s + 1)).projection (TPframe D.s) (TPframe_isCompl' D.s).symm)

theorem sigNat_V0 (a : V0Sub.carrier) :
    sigNat D ((a : VPlus), 0) = (((v0Sigma a : V0Sub.carrier) : VPlus), 0) := by
  have h : (frameSector 1).projection V0Sub.carrier V0_isCompl.symm (a : VPlus) = 0 :=
    Submodule.projection_apply_of_mem_right _ a.2
  simp [sigNat, sig0_V0, h]

theorem sigNat_V3 {a : VPlus} (ha : a ∈ frameSector 1) : sigNat D (a, 0) = (0, D.Φ a) := by
  have h : (frameSector 1).projection V0Sub.carrier V0_isCompl.symm a = a :=
    Submodule.projection_apply_left V0_isCompl.symm ⟨a, ha⟩
  simp [sigNat, sig0_V3 ha, h]

theorem sigNat_Ts {t : TP} (ht : t ∈ TPframe D.s) : sigNat D (0, t) = (D.Ψ t, 0) := by
  have h1 : (TPframe D.s).projection (TPframe (D.s + 1)) (TPframe_isCompl' D.s) t = t :=
    Submodule.projection_apply_left (TPframe_isCompl' D.s) ⟨t, ht⟩
  have h2 : (TPframe (D.s + 1)).projection (TPframe D.s) (TPframe_isCompl' D.s).symm t = 0 :=
    Submodule.projection_apply_of_mem_right _ ht
  simp [sigNat, h1, h2]

theorem sigNat_Ts1 {t : TP} (ht : t ∈ TPframe (D.s + 1)) : sigNat D (0, t) = (0, D.Θ t) := by
  have h1 : (TPframe D.s).projection (TPframe (D.s + 1)) (TPframe_isCompl' D.s) t = 0 :=
    Submodule.projection_apply_of_mem_right _ ht
  have h2 : (TPframe (D.s + 1)).projection (TPframe D.s) (TPframe_isCompl' D.s).symm t = t :=
    Submodule.projection_apply_left (TPframe_isCompl' D.s).symm ⟨t, ht⟩
  simp [sigNat, h1, h2]

/-- **`σ♮` is an involution.** -/
theorem sigNat_sq : sigNat D * sigNat D = 1 := by
  refine vnat_ext D.s ?_ ?_ ?_ ?_
  · intro a ha
    rw [Module.End.mul_apply, Module.End.one_apply]
    have e := sigNat_V0 D ⟨a, ha⟩
    simp only at e
    rw [e, sigNat_V0]
    have := sig_sig ⟨a, ha⟩
    simp only [sig] at this
    rw [this]
  · intro a ha
    rw [Module.End.mul_apply, Module.End.one_apply]
    rw [sigNat_V3 D ha, sigNat_Ts D (D.Φ_mem a ha), D.ΨΦ a ha]
  · intro t ht
    rw [Module.End.mul_apply, Module.End.one_apply]
    rw [sigNat_Ts D ht, sigNat_V3 D (D.Ψ_mem t ht), D.ΦΨ t ht]
  · intro t ht
    rw [Module.End.mul_apply, Module.End.one_apply]
    rw [sigNat_Ts1 D ht, sigNat_Ts1 D (D.Θ_mem t ht), D.ΘΘ t ht]

/-- `v0Sigma` intertwines the fields of `V₀⁺`, read in `V_Λ⁺`. -/
theorem v0Sigma_Y (u a : V0Sub.carrier) (k : ℤ) :
    ((v0Sigma ⟨leechVOAPlus.Y (u : VPlus) k a, V0Sub.coeff_mem u.2 k a.2⟩ : V0Sub.carrier) : VPlus)
      = leechVOAPlus.Y ((v0Sigma u : V0Sub.carrier) : VPlus) k ((v0Sigma a : V0Sub.carrier) : VPlus) := by
  have h := v0Sigma.map_smul u (-k - 1) a
  have e : (⟨leechVOAPlus.Y (u : VPlus) k a, V0Sub.coeff_mem u.2 k a.2⟩ : V0Sub.carrier)
      = V0P.smul u (-k - 1) a := by
    apply Subtype.ext
    rw [PreVertexAlgebra.smul_def]
    change _ = ((mode (V0Sub.YS u) (-k - 1) a : V0Sub.carrier) : VPlus)
    rw [VOASubalgebra.mode_YS_coe, mode_apply, show -(-k - 1) - 1 = k by ring]
  rw [e, h, PreVertexAlgebra.smul_def]
  change ((mode (V0Sub.YS (v0Sigma u)) (-k - 1) (v0Sigma a) : V0Sub.carrier) : VPlus) = _
  rw [VOASubalgebra.mode_YS_coe, mode_apply, show -(-k - 1) - 1 = k by ring]

/-- **`σ♮` intertwines the `V₀⁺`-fields**: `σ♮ ∘ Y♮(u) = Y♮(σu) ∘ σ♮` for `u ∈ V₀⁺`.  This is the
twisted-intertwiner property of `Φ, Ψ, Θ` together with `v0Sigma ∈ Aut V₀⁺`. -/
theorem sigNat_YnatU_V0 (u : V0Sub.carrier) (k : ℤ) :
    sigNat D * YnatU (u : VPlus) k = YnatU ((sig u : V0Sub.carrier) : VPlus) k * sigNat D := by
  refine vnat_ext D.s ?_ ?_ ?_ ?_
  · intro a ha
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have e := sigNat_V0 D ⟨a, ha⟩
    simp only at e
    rw [e, YnatU_apply, YnatU_apply]
    simp only [map_zero]
    have hmem := V0Sub.coeff_mem u.2 k ha
    have := sigNat_V0 D ⟨_, hmem⟩
    simp only at this
    rw [this, v0Sigma_Y u ⟨a, ha⟩ k]
    rfl
  · intro a ha
    rw [Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_V3 D ha, YnatU_apply, YnatU_apply]
    simp only [map_zero]
    have hmem : leechVOAPlus.Y (u : VPlus) k a ∈ frameSector 1 := by
      rw [Y_eq_actV]; exact actV_stab u (Set.mem_univ _) _ a ha
    rw [sigNat_V3 D hmem, Y_eq_actV, D.isSigma_Φ u (Set.mem_univ _) _ a ha, YM_eq_actT]
  · intro t ht
    rw [Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_Ts D ht, YnatU_apply, YnatU_apply]
    simp only [map_zero]
    have hmem : plusModule.YM (u : VPlus) k t ∈ TPframe D.s := by
      rw [YM_eq_actT]; exact actT_stab D.s u (Set.mem_univ _) _ t ht
    rw [sigNat_Ts D hmem, YM_eq_actT, D.isSigma_Ψ u (Set.mem_univ _) _ t ht, Y_eq_actV]
  · intro t ht
    rw [Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_Ts1 D ht, YnatU_apply, YnatU_apply]
    simp only [map_zero]
    have hmem : plusModule.YM (u : VPlus) k t ∈ TPframe (D.s + 1) := by
      rw [YM_eq_actT]; exact actT_stab (D.s + 1) u (Set.mem_univ _) _ t ht
    rw [sigNat_Ts1 D hmem, YM_eq_actT, D.isSigma_Θ u (Set.mem_univ _) _ t ht, YM_eq_actT]

/-- `σ♮ Y♮(u) σ♮ = Y♮(σu)` for `u ∈ V₀⁺`. -/
theorem conjF_YnatU_V0 (u : V0Sub.carrier) :
    conjF (sigNat D) (YnatU (u : VPlus)) = YnatU ((sig u : V0Sub.carrier) : VPlus) := by
  funext k
  rw [conjF_apply, sigNat_YnatU_V0, mul_assoc, sigNat_sq, mul_one]

/-- `Tnat = Y♮(ω)₍₀₎`. -/
theorem Tnat_eq : Tnat = YnatU leechVOAPlus.conformalVector (-1) := by
  rw [Tnat, YnatU, diagF, blockF_apply, VertexOperatorAlgebra.L_def]
  rfl

/-- `σ♮` commutes with the translation operator. -/
theorem sigNat_Tnat : sigNat D * Tnat = Tnat * sigNat D := by
  have h := sigNat_YnatU_V0 D V0P.conformalVector (-1)
  rw [sig_omega] at h
  rw [Tnat_eq]
  exact h

theorem sigNat_vac : sigNat D vacNat = vacNat := by
  have h := sigNat_V0 D V0P.vacuum
  rw [v0Sigma.map_vacuum] at h
  exact h

/-! ## §4  Uniqueness with `V₀⁺`-locality only -/

/-- **The circularity-free uniqueness lemma.**  A field `F` on `V♮`, local with `Y♮(u)` for every
`u ∈ V₀⁺`, that kills `𝟙`, `(e^β + e^{−β}, 0)` (`β ∉ Λ₀`) and `(0, h₀(−½)𝟙 ⊗ t s)` (`0 ≠ t s ∈ T_s`,
both `s`), is zero. -/
theorem eq_zero_of_V0local (F : FormalDist (End ℂ Vnat))
    (hloc : ∀ u : V0Sub.carrier, Local F (YnatU (u : VPlus)))
    {β : leech.carrier} (hβ : β ∉ lambda0) (t : ZMod 2 → TLeechT)
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hvac : ∀ p, F p vacNat = 0) (h3 : ∀ p, F p (frameX0P β, 0) = 0)
    (hT : ∀ s p, F p (0, x0T (t s)) = 0) : F = 0 := by
  set K : Submodule ℂ Vnat := ⨅ p : ℤ, LinearMap.ker (F p) with hK
  have hmemK : ∀ y, y ∈ K ↔ ∀ p, F p y = 0 := by
    intro y; simp [hK, Submodule.mem_iInf, LinearMap.mem_ker]
  have hstab : ∀ (u : V0Sub.carrier) (q : ℤ) {y : Vnat}, y ∈ K → YnatU (u : VPlus) q y ∈ K := by
    intro u q y hy
    rw [hmemK] at hy ⊢
    intro p
    exact kill_mode (hloc u) (YnatU_isField _) hy p q
  -- `V₀⁺`
  have hV0 : ∀ a ∈ V0Sub.carrier, ((a, 0) : Vnat) ∈ K := by
    intro a ha
    have h := hstab ⟨a, ha⟩ 0 ((hmemK _).2 hvac)
    rwa [YnatU_vac_zero] at h
  -- `V₃⁺`
  have hV3 : ∀ a ∈ frameSector 1, ((a, 0) : Vnat) ∈ K := by
    intro a ha
    rw [← cyc_V3 hβ] at ha
    have hsub : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n (frameX0P β)}
        ≤ K.comap (LinearMap.inl ℂ SkewVP TP) := by
      rw [Submodule.span_le]
      rintro y ⟨u, -, n, rfl⟩
      have h := hstab u (-n - 1) ((hmemK _).2 h3)
      rw [YnatU_apply, Y_eq_actV, show -(-n - 1) - 1 = n by ring] at h
      simpa using h
    exact hsub ha
  -- `T_s⁺`
  have hTs : ∀ s, ∀ y ∈ TPframe s, ((0, y) : Vnat) ∈ K := by
    intro s y hy
    rw [← cyc_T (ht s) (ht0 s)] at hy
    have hsub : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n (x0T (t s))}
        ≤ K.comap (LinearMap.inr ℂ SkewVP TP) := by
      rw [Submodule.span_le]
      rintro y ⟨u, -, n, rfl⟩
      have h := hstab u (-n - 1) ((hmemK _).2 (hT s))
      rw [YnatU_apply, YM_eq_actT, show -(-n - 1) - 1 = n by ring] at h
      simpa using h
    exact hsub hy
  have hall : ∀ y, y ∈ K := by
    intro y
    have := vnat_ext (M := Vnat ⧸ K) (f := K.mkQ) (g := 0) 0
      (fun a ha => by simpa [Submodule.Quotient.mk_eq_zero] using hV0 a ha)
      (fun a ha => by simpa [Submodule.Quotient.mk_eq_zero] using hV3 a ha)
      (fun t ht => by simpa [Submodule.Quotient.mk_eq_zero] using hTs 0 t ht)
      (fun t ht => by simpa [Submodule.Quotient.mk_eq_zero] using hTs _ t ht)
    have h := LinearMap.congr_fun this y
    simpa [Submodule.Quotient.mk_eq_zero] using h
  funext p
  exact LinearMap.ext fun y => (hmemK y).1 (hall y) p

end VOA.Moonshine.M8hKey
