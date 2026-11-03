/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaAssembleTop

/-!
# SigmaAssemble, part 2: the σ-existence data `D`, `PhiTop`, `ThetaTop`, and `KeySkew` as the
last hypothesis

From one seed `t₀ ∈ T_{s₀}` (`seed_in_frame seedExists`) we take the explicit top maps
`φ⋆ = phiV3 (tauStar t₀)` (`TopSigmaV3 (s₀+1)`) and `φ_B = phiTT (psiOf (Bop s₀))`
(`TopSigmaTT s₀ s₀`), and their unique twisted extensions `Φ₀ : V₃⁺ → T_{s₀+1}⁺`,
`Θ₀ : T_{s₀}⁺ → T_{s₀}⁺` (`sigmaV3T_exists_of_top`, `sigmaTT_exists_of_top`).  Sector
bookkeeping: `SigmaData.s := s₀ + 1`, so `T_{D.s+1} = T_{s₀}` (`s0_add_one_add_one`).

## Main results
* `Φ0_mem`, `Φ0_surj` (`Φ₀(V₃⁺) = T_{s₀+1}⁺`, from the cyclic vector it hits).
* `Φ0_simil`: `TPForm(Φ₀a, Φ₀b) = κ₀ leechBV(a,b)` on `V₃⁺`, with
  `κ₀ = TPForm(Φ₀z₀,Φ₀z₀)/leechBV(z₀,z₀)` (`bv_z0`: the denominator is nonzero by
  nondegeneracy).  `κ0_ne`: `κ₀ ≠ 0` (else `TPForm` would vanish on `T_{s₀+1}⁺`).
  Hence `Φ0_inj`, the inverse `Ψ0` (`Φ0_Ψ0`, `Ψ0_Φ0`), and `Ψ0_isSigma : IsSigmaTV (s₀+1) Ψ₀`.
* `Θ0_Θ0`: `Θ₀² = 1` on `T_{s₀}⁺` with **no** rescaling (`phiB_invol` + `sigma_involutive_TT`);
  `Θ0_isom` (top-level isometry, `μ = +1` proved).
* `mkData c ε hc hε : SigmaData` — `Φ = cΦ₀`, `Ψ = c⁻¹Ψ₀`, `Θ = εΘ₀`, for every `c ≠ 0` and
  `ε² = 1`: the whole normalisation freedom is exposed.
* `phiIso_mkData` (`c²κ₀ = 1` ⇒ `PhiIso`), `phiTop_of_phiIso`, `exists_norm`,
  `thetaTop_mkData` / `thetaIso_mkData` (for every `c, ε`).  `tF`, `tF_mem`, `tF_ne`: the
  nonzero frame vectors `t_{s₀} = t₀`, `t_{s₀+1} = e_{m₀}t₀`.
* `keySkew_mkData_iff`: `KeySkew (mkData c ε) tF ↔ KeySkew0 ε` — `KeySkew` does not see `c`.
* `moonshine_of_keySkew`, `moonshine_of_keySkew'`, `moonshine_of_keySkew0 :
  KeySkew0 1 ∨ KeySkew0 (-1) → (all definition-of-done targets)`.

## Status
`sorry`-free; `#print axioms` of `mkData`, `phiIso_mkData`, `thetaTop_mkData`,
`moonshine_of_keySkew0`: `[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`).
`SigmaData`, `PhiTop`, `ThetaTop` (hence `PhiIso`, `ThetaIso`) are **unconditional** for the
explicit data.  **The single remaining hypothesis to `V♮` is `KeySkew0 ε` for one sign `ε`**
(the fusion-rule-1 content; which sign holds is not determined here —
in the numerical model it is `−Θ_J`, whose relation to `Θ₀ = φ_B` is not computed).  Imported by the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaAssemble

open Module (End)
open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.Moonshine.SigmaTop
open VOA.Moonshine.InvForm VOA.Moonshine.TFormLeech
open VnatBlock SkewIntertwiner Reconstruction M8h0 M8hKey LatticeTwisted TwistedHeisenberg FrameT
  SkewAdjoint VertexOperatorAlgebra SigmaKey

/-! ## §1  The seed and the two explicit top maps -/

/-- The frame sector of the seed. -/
noncomputable def s0 : ZMod 2 := (seed_in_frame seedExists).choose

/-- The seed `t₀ ∈ T_{s₀}`. -/
noncomputable def t0 : TLeechT := (seed_in_frame seedExists).choose_spec.choose

theorem t0_mem : t0 ∈ leechFrameT s0 := (seed_in_frame seedExists).choose_spec.choose_spec.1
theorem t0_ne : t0 ≠ 0 := (seed_in_frame seedExists).choose_spec.choose_spec.2.1
theorem t0_seed : IsSeed t0 := (seed_in_frame seedExists).choose_spec.choose_spec.2.2

/-- `φ⋆ = φ_{τ⋆}` on `(V₃⁺)₂`. -/
noncomputable def phiV : VPlus →ₗ[ℂ] TP := phiV3 (tauStar t0)

/-- `φ_B` on `(T_{s₀}⁺)₂`. -/
noncomputable def phiB : TP →ₗ[ℂ] TP := phiTT (psiOf (Bop s0))

theorem topV : TopSigmaV3 (s0 + 1) phiV :=
  topSigmaV3_of_octad t0_mem t0_ne t0_seed (octadResidualV3 s0 t0 t0_mem t0_ne t0_seed)

theorem topB : TopSigmaTT s0 s0 phiB := topSigmaTT_of_seed' t0_mem t0_ne t0_seed

/-! ## §2  The unnormalised intertwiners `Φ₀ : V₃⁺ → T_{s₀+1}⁺`, `Θ₀ : T_{s₀}⁺ → T_{s₀}⁺` -/

/-- The unique `v0Sigma`-twisted intertwiner on `V₃⁺` extending `φ⋆`. -/
noncomputable def Φ0 : VPlus →ₗ[ℂ] TP := (sigmaV3T_exists_of_top topV).choose

theorem Φ0_isSigma : IsSigmaV3T Φ0 := (sigmaV3T_exists_of_top topV).choose_spec.1

theorem Φ0_top : ∀ x ∈ OmegaV3, Φ0 x = phiV x := (sigmaV3T_exists_of_top topV).choose_spec.2.1

theorem Φ0_hits : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT (s0 + 1) ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, Φ0 x = x0T t₀ :=
  (sigmaV3T_exists_of_top topV).choose_spec.2.2

/-- The unique `v0Sigma`-twisted intertwiner on `T_{s₀}⁺` extending `φ_B`. -/
noncomputable def Θ0 : TP →ₗ[ℂ] TP := (sigmaTT_exists_of_top topB t0_mem t0_ne).choose

theorem Θ0_isSigma : IsSigmaTT s0 Θ0 := (sigmaTT_exists_of_top topB t0_mem t0_ne).choose_spec.1

theorem Θ0_top : ∀ x ∈ OmegaT s0, Θ0 x = phiB x :=
  (sigmaTT_exists_of_top topB t0_mem t0_ne).choose_spec.2.1

theorem isTwInt_smul {A M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    {ρ : A → ℤ → M →ₗ[ℂ] M} {τ : A → ℤ → N →ₗ[ℂ] N} {g : A → A} {S : Set A}
    {X : Submodule ℂ M} {Φ : M →ₗ[ℂ] N} (h : IsTwInt ρ τ g S X Φ) (c : ℂ) :
    IsTwInt ρ τ g S X (c • Φ) := fun u hu n x hx => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, h u hu n x hx, map_smul]

theorem x0_mem_OmegaT {s' : ZMod 2} {t : TLeechT} (ht : t ∈ leechFrameT s') : x0T t ∈ OmegaT s' :=
  ⟨x0T_mem ht, x0T_mem_weight t⟩

/-- `Θ₀` preserves `T_{s₀}⁺`. -/
theorem Θ0_mem : ∀ y ∈ TPframe s0, Θ0 y ∈ TPframe s0 := by
  intro y hy
  have hx0 := x0_mem_OmegaT t0_mem
  have h0 : Θ0 (x0T t0) ∈ TPframe s0 := by rw [Θ0_top _ hx0]; exact topB.maps_frame _ hx0
  rw [← cyc_T t0_mem t0_ne] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, -, n, rfl⟩ := hz
    rw [Θ0_isSigma u (Set.mem_univ _) n _ hx0.1]
    exact actT_stab s0 _ (Set.mem_univ _) n _ h0
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- **`Θ₀² = 1` on `T_{s₀}⁺`** — no normalisation needed. -/
theorem Θ0_Θ0 : ∀ y ∈ TPframe s0, Θ0 (Θ0 y) = y := by
  have hx0 := x0_mem_OmegaT t0_mem
  refine sigma_involutive_TT t0_mem t0_ne Θ0_isSigma Θ0_mem ?_
  have hφ : phiB (x0T t0) ∈ OmegaT s0 := ⟨topB.maps_frame _ hx0, topB.maps_weight _ hx0⟩
  rw [Θ0_top _ hx0, Θ0_top _ hφ]
  exact phiB_invol t0_mem t0_ne t0_seed hx0

/-- **`Θ₀` is a `TPForm`-isometry of the top level `(T_{s₀}⁺)₂`.** -/
theorem Θ0_isom {x y : TP} (hx : x ∈ OmegaT s0) (hy : y ∈ OmegaT s0) :
    TPForm (Θ0 x) (Θ0 y) = TPForm x y := by
  rw [Θ0_top _ hx, Θ0_top _ hy]
  exact phiB_isom t0_mem t0_ne t0_seed hx hy

/-! ## §3  `Φ₀` is a nonzero similitude, hence bijective `V₃⁺ → T_{s₀+1}⁺` -/

theorem Φ0_mem : ∀ x ∈ frameSector 1, Φ0 x ∈ TPframe (s0 + 1) := by
  intro x hx
  have h0 : Φ0 (frameX0P β₂) ∈ TPframe (s0 + 1) := by
    rw [Φ0_top _ frameX0P_β₂_mem]; exact topV.maps_frame _ frameX0P_β₂_mem
  rw [← cyc_V3 β₂_not_mem] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, -, n, rfl⟩ := hz
    rw [Φ0_isSigma u (Set.mem_univ _) n _ (frameX0_mem_frameSector_one β₂_not_mem)]
    exact actT_stab _ _ (Set.mem_univ _) n _ h0
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem Φ0_surj : ∀ y ∈ TPframe (s0 + 1), ∃ b ∈ frameSector 1, Φ0 b = y := by
  obtain ⟨t₁, ht₁, ht₁0, x, hx, hΦx⟩ := Φ0_hits
  intro y hy
  rw [← cyc_T ht₁ ht₁0] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, -, n, rfl⟩ := hz
    refine ⟨actV (sig u) n x, actV_stab _ (Set.mem_univ _) n x hx.1, ?_⟩
    rw [Φ0_isSigma (sig u) (Set.mem_univ _) n x hx.1, sig_sig, hΦx]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' + b', add_mem ha' hb', map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨c • a', Submodule.smul_mem _ c ha', map_smul _ _ _⟩

/-- The reference top vector `z₀ = e^{n₀} + e^{−n₀}`, `n₀ = nvec 0 ∈ S₁`. -/
noncomputable def z0 : VPlus := frameX0P (nvec 0)

theorem z0_mem : z0 ∈ OmegaV3 := frameX0P_mem_OmegaV3 (nvec_mem 0)

theorem z0_cyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z0}
    = frameSector 1 := cyc_V3 (nvec_not_mem 0)

theorem z0_ne : z0 ≠ 0 := by
  intro h
  have := coefN_frameX0P (nvec_mem 0) (nvec_mem 0)
  rw [if_pos rfl] at this
  change coefN (nvec 0) z0 = 1 at this
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem isSigma_zero : IsSigmaV3T 0 := fun u _ n x _ => by simp

theorem bv_z0 : leechBV z0 z0 ≠ 0 := by
  intro h
  have hrow : ∀ b ∈ OmegaV3, leechBV z0 b = 0 := by
    intro b hb
    have hb' := OmegaV3_le_span hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, hn, rfl⟩ := hy
      by_cases hne : n = nvec 0
      · subst hne; exact h
      · exact leechBV_sep (nvec_mem 0) hn (fun e => hne e.symm)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  have hall := simil_of_top isSigma_zero 1 z0_mem.1 z0_mem.2 z0_cyc (fun b hb hb2 => by
    rw [hrow b ⟨hb, hb2⟩]; simp)
  apply z0_ne
  refine leechBV_eq_zero_of_forall (fun a => leechBV_frame_orth' z0_mem.1 (mem_V0 a)) ?_
  intro b hb
  have := hall z0 z0_mem.1 b hb
  simpa using this.symm

/-- The similitude constant of `Φ₀`: `κ₀ = TPForm(Φ₀z₀, Φ₀z₀) / leechBV(z₀, z₀)`. -/
noncomputable def κ0 : ℂ := TPForm (Φ0 z0) (Φ0 z0) / leechBV z0 z0

/-- **`Φ₀` is a similitude**: `TPForm(Φ₀a, Φ₀b) = κ₀ leechBV(a, b)` on `V₃⁺`. -/
theorem Φ0_simil : ∀ a ∈ frameSector 1, ∀ b ∈ frameSector 1,
    TPForm (Φ0 a) (Φ0 b) = κ0 * leechBV a b := by
  refine simil_of_top Φ0_isSigma κ0 z0_mem.1 z0_mem.2 z0_cyc fun b hb hb2 => ?_
  have hb' := OmegaV3_le_span (show b ∈ OmegaV3 from ⟨hb, hb2⟩)
  clear hb hb2
  induction hb' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn, rfl⟩ := hy
    by_cases hne : n = nvec 0
    · subst hne
      change TPForm (Φ0 z0) (Φ0 z0) = κ0 * leechBV z0 z0
      rw [κ0, div_mul_cancel₀ _ bv_z0]
    · rw [show z0 = frameX0P (nvec 0) from rfl, TPForm_Phi_sep Φ0_isSigma (nvec_mem 0) hn
        (fun e => hne e.symm), leechBV_sep (nvec_mem 0) hn (fun e => hne e.symm), mul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, map_add, mul_add]
  | smul c a _ ha => rw [map_smul, map_smul, ha, map_smul, smul_eq_mul, smul_eq_mul]; ring

/-- **`κ₀ ≠ 0`**: otherwise `TPForm` would vanish on `Φ₀(V₃⁺) = T_{s₀+1}⁺`, where it is
nondegenerate. -/
theorem κ0_ne : κ0 ≠ 0 := by
  intro h
  obtain ⟨t₁, ht₁, ht₁0, x, hx, hΦx⟩ := Φ0_hits
  apply x0T_ne_zero ht₁0
  refine TPForm_eq_zero_of_frame (x0T_mem ht₁) fun z hz => ?_
  obtain ⟨b, hb, rfl⟩ := Φ0_surj z hz
  rw [← hΦx, Φ0_simil x hx.1 b hb, h, zero_mul]

theorem Φ0_inj {a b : VPlus} (ha : a ∈ frameSector 1) (hb : b ∈ frameSector 1)
    (h : Φ0 a = Φ0 b) : a = b := by
  have hab : a - b ∈ frameSector 1 := sub_mem ha hb
  have h0 : Φ0 (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [← sub_eq_zero]
  refine leechBV_eq_zero_of_forall (fun u => leechBV_frame_orth' hab (mem_V0 u)) fun c hc => ?_
  have := Φ0_simil _ hab c hc
  rw [h0, map_zero, LinearMap.zero_apply] at this
  exact (mul_eq_zero.mp this.symm).resolve_left κ0_ne

/-! ## §4  The inverse `Ψ₀ : T_{s₀+1}⁺ → V₃⁺` -/

/-- `Φ₀ : V₃⁺ ≃ T_{s₀+1}⁺`. -/
noncomputable def eR : frameSector 1 ≃ₗ[ℂ] TPframe (s0 + 1) :=
  LinearEquiv.ofBijective (Φ0.restrict Φ0_mem)
    ⟨fun a b h => Subtype.ext (Φ0_inj a.2 b.2 (congrArg Subtype.val h)), fun y => by
      obtain ⟨b, hb, hby⟩ := Φ0_surj y y.2
      exact ⟨⟨b, hb⟩, Subtype.ext hby⟩⟩

theorem exists_Ψ0 : ∃ g : TP →ₗ[ℂ] VPlus,
    g ∘ₗ (TPframe (s0 + 1)).subtype = (frameSector 1).subtype ∘ₗ eR.symm.toLinearMap :=
  LinearMap.exists_extend _

/-- `Ψ₀ = Φ₀⁻¹` on `T_{s₀+1}⁺` (extended linearly). -/
noncomputable def Ψ0 : TP →ₗ[ℂ] VPlus := exists_Ψ0.choose

theorem Ψ0_apply {y : TP} (hy : y ∈ TPframe (s0 + 1)) :
    Ψ0 y = ((eR.symm ⟨y, hy⟩ : frameSector 1) : VPlus) :=
  LinearMap.congr_fun exists_Ψ0.choose_spec ⟨y, hy⟩

theorem Ψ0_mem {y : TP} (hy : y ∈ TPframe (s0 + 1)) : Ψ0 y ∈ frameSector 1 := by
  rw [Ψ0_apply hy]; exact (eR.symm ⟨y, hy⟩).2

theorem Φ0_Ψ0 {y : TP} (hy : y ∈ TPframe (s0 + 1)) : Φ0 (Ψ0 y) = y := by
  rw [Ψ0_apply hy]
  have := congrArg Subtype.val (eR.apply_symm_apply ⟨y, hy⟩)
  exact this

theorem Ψ0_Φ0 {x : VPlus} (hx : x ∈ frameSector 1) : Ψ0 (Φ0 x) = x :=
  Φ0_inj (Ψ0_mem (Φ0_mem x hx)) hx (Φ0_Ψ0 (Φ0_mem x hx))

theorem Ψ0_isSigma : IsSigmaTV (s0 + 1) Ψ0 := by
  intro u _ n y hy
  have hy' := actT_stab (s0 + 1) u (Set.mem_univ _) n y hy
  refine Φ0_inj (Ψ0_mem hy') (actV_stab _ (Set.mem_univ _) n _ (Ψ0_mem hy)) ?_
  rw [Φ0_Ψ0 hy', Φ0_isSigma (sig u) (Set.mem_univ _) n _ (Ψ0_mem hy), sig_sig, Φ0_Ψ0 hy]

/-! ## §5  The σ-existence data, with the normalisation freedom exposed -/

theorem s0_add_one_add_one : s0 + 1 + 1 = s0 := zmod2_add_one_add_one s0

/-- **The σ-existence data** `D(c, ε)`: `s = s₀ + 1`, `Φ = c Φ₀`, `Ψ = c⁻¹ Ψ₀`, `Θ = ε Θ₀`
for any `c ≠ 0` and any sign `ε² = 1` (the full freedom `SigmaData` leaves). -/
noncomputable def mkData (c ε : ℂ) (hc : c ≠ 0) (hε : ε * ε = 1) : SigmaData where
  s := s0 + 1
  Φ := c • Φ0
  Ψ := c⁻¹ • Ψ0
  Θ := ε • Θ0
  isSigma_Φ := isTwInt_smul Φ0_isSigma c
  isSigma_Ψ := isTwInt_smul Ψ0_isSigma c⁻¹
  isSigma_Θ := by rw [s0_add_one_add_one]; exact isTwInt_smul Θ0_isSigma ε
  Φ_mem x hx := by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ c (Φ0_mem x hx)
  Ψ_mem t ht := by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ c⁻¹ (Ψ0_mem ht)
  Θ_mem t ht := by
    rw [s0_add_one_add_one] at ht ⊢
    rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ ε (Θ0_mem t ht)
  ΨΦ x hx := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, Ψ0_Φ0 hx, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  ΦΨ t ht := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, Φ0_Ψ0 ht, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
  ΘΘ t ht := by
    rw [s0_add_one_add_one] at ht
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, Θ0_Θ0 t ht, smul_smul, hε, one_smul]

/-- The normalisation of `c` exists: `c² κ₀ = 1` (two solutions `±c`). -/
theorem exists_norm : ∃ c : ℂ, c * c * κ0 = 1 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq κ0⁻¹ (by norm_num : 0 < 2)
  exact ⟨c, by rw [← pow_two, hc, inv_mul_cancel₀ κ0_ne]⟩

theorem c_ne_of_norm {c : ℂ} (hc : c * c * κ0 = 1) : c ≠ 0 := by
  rintro rfl; simp at hc

/-- **`PhiIso` for the normalised data** (`c² κ₀ = 1`). -/
theorem phiIso_mkData {c ε : ℂ} (hc : c * c * κ0 = 1) (hε : ε * ε = 1) :
    PhiIso (mkData c ε (c_ne_of_norm hc) hε) := by
  intro a ha b hb
  change TPForm ((c • Φ0) a) ((c • Φ0) b) = leechBV a b
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, Φ0_simil a ha b hb]
  linear_combination (leechBV a b) * hc

/-- `PhiTop` is the instance of `PhiIso` at `Ψ x` (for any `D`). -/
theorem phiTop_of_phiIso (D : SigmaData) {t : ZMod 2 → TLeechT} (hiso : PhiIso D)
    (ht : t D.s ∈ leechFrameT D.s) : PhiTop D t := by
  intro b hb _
  have hx := x0T_mem ht
  have := hiso _ (D.Ψ_mem _ hx) b hb
  rwa [D.ΦΨ _ hx] at this

/-- The two nonzero frame vectors `t_s ∈ T_s` (`t_{s₀} = t₀`, `t_{s₀+1} = e_{m₀} t₀`). -/
noncomputable def tF (s' : ZMod 2) : TLeechT := if s' = s0 then t0 else eL (mvec 0) t0

theorem zmod2_eq_add_one {a b : ZMod 2} (h : a ≠ b) : a = b + 1 := by
  revert a b; decide

theorem tF_mem (s' : ZMod 2) : tF s' ∈ leechFrameT s' := by
  unfold tF
  split_ifs with h
  · subst h; exact t0_mem
  · rw [zmod2_eq_add_one h]
    have := eT_mem_leechFrameT (mvec 0) t0_mem
    rwa [SigmaTop.frameChar_eq_one (mvec_not_mem 0)] at this

theorem tF_ne (s' : ZMod 2) : tF s' ≠ 0 := by
  unfold tF
  split_ifs
  · exact t0_ne
  · exact fun h => t0_ne (eL_injective _ (by rw [h, map_zero]))

/-- **`ThetaTop` for every `D(c, ε)`** (the `μ = +1` condition, proved: `Θ₀ = φ_B` on the
top, `ψ_m` is a `TForm`-isometry, the blocks are `TPForm`-orthogonal). -/
theorem thetaTop_mkData (c ε : ℂ) (hc : c ≠ 0) (hε : ε * ε = 1) :
    ThetaTop (mkData c ε hc hε) tF := by
  intro y hy hy2
  have e : (mkData c ε hc hε).s + 1 = s0 := s0_add_one_add_one
  rw [e] at hy ⊢
  change TPForm ((ε • Θ0) (x0T (tF s0))) ((ε • Θ0) y) = TPForm (x0T (tF s0)) y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, Θ0_isom (x0_mem_OmegaT (tF_mem s0)) ⟨hy, hy2⟩, ← mul_assoc, hε,
    one_mul]

theorem thetaIso_mkData (c ε : ℂ) (hc : c ≠ 0) (hε : ε * ε = 1) :
    ThetaIso (mkData c ε hc hε) :=
  thetaIso_of_thetaTop _ tF_mem tF_ne (thetaTop_mkData c ε hc hε)

/-! ## §6  `KeySkew` is the only remaining hypothesis -/

/-- **The Moonshine module from `KeySkew` alone**, for the explicit data `D(c, ε)` with
`c² κ₀ = 1` and either sign `ε`. -/
theorem moonshine_of_keySkew {c ε : ℂ} (hc : c * c * κ0 = 1) (hε : ε * ε = 1)
    (hk : KeySkew (mkData c ε (c_ne_of_norm hc) hε) tF) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_top _ β₂_not_mem tF_mem tF_ne
    (phiTop_of_phiIso _ (phiIso_mkData hc hε) (tF_mem _)) (thetaTop_mkData _ _ _ hε) hk

/-- The fixed normalisation `c⋆` (`c⋆² κ₀ = 1`). -/
noncomputable def cStar0 : ℂ := exists_norm.choose

theorem cStar0_norm : cStar0 * cStar0 * κ0 = 1 := exists_norm.choose_spec

/-- The standard data `D(ε) = D(c⋆, ε)`. -/
noncomputable def Dstd (ε : ℂ) (hε : ε * ε = 1) : SigmaData :=
  mkData cStar0 ε (c_ne_of_norm cStar0_norm) hε

/-- **Definition-of-done targets from `KeySkew` for one sign of `Θ`.** -/
theorem moonshine_of_keySkew' (h : ∃ (ε : ℂ) (hε : ε * ε = 1), KeySkew (Dstd ε hε) tF) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple := by
  obtain ⟨ε, hε, hk⟩ := h
  exact moonshine_of_keySkew cStar0_norm hε hk

/-! ## §7  `KeySkew` does not see `c`: only the sign `ε` of `Θ` matters -/

/-- The cyclic vector `x = h₀(−½)𝟙 ⊗ t_{s₀+1}` of `T_{s₀+1}⁺` used by `KeySkew`. -/
noncomputable def xK : TP := x0T (tF (s0 + 1))

/-- **The `c`-free form of `KeySkew`**: `ε Θ₀(Y^T(Ψ₀x, z) x) = W(x, z) Ψ₀x`. -/
def KeySkew0 (ε : ℂ) : Prop :=
  ∀ p, ε • Θ0 (plusModule.YM (Ψ0 xK) p xK) = leechWsk xK p (Ψ0 xK)

theorem keySkew_mkData_iff (c ε : ℂ) (hc : c ≠ 0) (hε : ε * ε = 1) :
    KeySkew (mkData c ε hc hε) tF ↔ KeySkew0 ε := by
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  refine forall_congr' fun p => ?_
  change (ε • Θ0) (plusModule.YM ((c⁻¹ • Ψ0) xK) p xK) = leechWsk xK p ((c⁻¹ • Ψ0) xK) ↔ _
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul]
  change ε • Θ0 ((c⁻¹ • plusModule.YM (Ψ0 xK) p) xK) = c⁻¹ • leechWsk xK p (Ψ0 xK) ↔ _
  rw [LinearMap.smul_apply, map_smul, smul_comm ε c⁻¹]
  exact (smul_right_injective TP hci).eq_iff

/-- **The definition-of-done targets from the `c`-free self-coupling identity for one sign of
`Θ`** — the single remaining hypothesis to `V♮`. -/
theorem moonshine_of_keySkew0 (h : KeySkew0 1 ∨ KeySkew0 (-1)) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple := by
  rcases h with h | h
  · exact moonshine_of_keySkew cStar0_norm (by norm_num)
      ((keySkew_mkData_iff _ _ _ (by norm_num)).mpr h)
  · exact moonshine_of_keySkew cStar0_norm (by norm_num)
      ((keySkew_mkData_iff _ _ _ (by norm_num)).mpr h)

end VOA.Moonshine.SigmaAssemble
