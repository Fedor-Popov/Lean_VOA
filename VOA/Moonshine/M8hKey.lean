/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8hKeySigma
import VOA.Moonshine.Main

/-!
# M8h key step: DGM (4.23) from the triality σ, modulo the FLM three-point identities

The triality route to DGM (4.23).  Given the σ-existence data `D : SigmaData` (`M8hKeySigma.lean`:
`v0Sigma` on `V₀⁺`, `Φ : V₃⁺ → T_s⁺`, `Ψ : T_s⁺ → V₃⁺`, `Θ : T_{s+1}⁺ → T_{s+1}⁺`, twisted
`V₀⁺`-intertwiners, mutually inverse), let `σ♮ = sigNat D`.  For `v ∈ V₃⁺` put

  `L_v := σ♮ Y♮(v) σ♮`,   `R_v := Y♮(σ♮ v) = YnatT W̄ (Φ v)`.

## What is proved here
1. `L_v` and `R_v` are both `L₋₁`-covariant, both create `(0, Φ v)`, and both are local with every
   `Y♮(u)`, `u ∈ V₀⁺` (`L_v` because `σ♮ Y♮(u) σ♮ = Y♮(σu)`, `conjF_YnatU_V0`; `R_v` by the proved
   (4.20)–(4.21)).  By the `V₀⁺`-only uniqueness lemma `eq_zero_of_V0local`, `L_v = R_v` as soon
   as they agree on the cyclic vectors of `V₃⁺`, `T₀⁺`, `T₁⁺` (`conjF_V3_eq`; agreement on `𝟙` is
   automatic by `tower_unique`).
2. If `L_v = R_v` for one `v` with `Φ v = h₀(−½)𝟙 ⊗ t₀` (`0 ≠ t₀ ∈ T_s`), then
   `Local (Y♮(Φ v)) (Y♮(Φ v))` is the σ♮-conjugate of `Local (Y♮ v) (Y♮ v)` (`YnatU_local`), so
   (4.23) holds on that pair (`YnatT_local_iff`); since this one vector generates `TP` over
   `V_Λ⁺` (`modeSpan_x0T`, `M8hKeySpan.lean`), `TPBlockLocal_all_of_gen` gives (4.23) for **all**
   pairs (`tpBlockLocal_of_sigma`), hence the four frame pairs of
   `vnat_VOA_of_TPBlockLocal_frame`, hence `moonshine_of_sigma`.

## What is NOT proved: the residual `SigmaKey`
Agreement on the three cyclic vectors is, written out in sector components
(`x := h₀(−½)𝟙 ⊗ t_s`, `v := Ψ x`, `x₃ := e^β + e^{−β}`, `x' := h₀(−½)𝟙 ⊗ t_{s+1}`):

* `key_V3`:  `Θ (Y^T(v, z) Φ x₃) = W(x, z) x₃`              (in `T_{s+1}⁺`)
* `key_Ts`:  `v0Sigma (Y(v, z) v) = W̄(x, z) x`              (in `V₀⁺`)
* `key_Ts1`: `Ψ (Y^T(v, z) Θ x') = W̄(x, z) x'`             (in `V₃⁺`)

(`key_V3_iff`, `key_Ts_iff`, `key_Ts1_iff` prove that these are exactly the cyclic-vector
agreements.)  These are FLM's three-point identities (FLM ch. 12–13): `key_Ts1`
is the "key identity on `T₃⁺`", and `key_V3`, `key_Ts` are of the same nature (by adjunction,
`key_Ts` is an isometry statement for `Φ` and `key_V3` is the adjoint of `key_Ts1`; that
reduction is analysis, not formalised).  They do **not** follow from the twisted-intertwiner
property of the σ maps alone: each compares two different intertwining operators (e.g. for
`key_V3`, of type `V₃⁺ × T_s⁺ → T_{s+1}⁺`), and equality needs a fusion-rule/uniqueness argument
or an explicit computation.  `SigmaKey` also pins the normalisations left free by `SigmaData`
(the scalar in `Φ ↦ cΦ, Ψ ↦ c⁻¹Ψ` and the sign of `Θ`).

## Circularity check
* `eq_zero_of_V0local` uses locality with `V₀⁺`-fields only; `M8h0.YnatT_eq_of_creates` (locality
  with all `V_Λ⁺`-fields) would be circular here and is not used for the identification.
* The only use of `M8h0` machinery after the identification is `TPBlockLocal_all_of_gen`, whose
  hypothesis is (4.23) on the single generator pair — supplied by conjugation, not assumed.
* (4.22) (`leechWbar_VPBlockLocal`) is unconditional; no step assumes (4.23) for any pair.

## Main results
* `SigmaKey D β t` — the residual (structure, component form); `SigmaKey.conj_eq` — it gives
  `σ♮ Y♮(Ψ x) σ♮ = Y♮(x)`.
* `tpBlockLocal_of_sigma : SigmaKey D β t → ∀ t₁ t₂, TPBlockLocal leechWbar t₁ t₂`.
* `tpBlockLocal_frame_of_sigma` — the four frame pairs of `vnat_VOA_of_TPBlockLocal_frame`.
* `moonshine_of_sigma` — everything of `moonshine_of_frameLocality` from `SigmaKey D β t`.

## Status
`sorry`-free; **conditional** on `D : SigmaData` (σ existence, M8g twisted half) **and** on the
named residual `SigmaKey D β t` (FLM's three-point identities on cyclic vectors, open).  It is
NOT a construction of `V♮`.  Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.M8hKey

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen
open LatticeTwisted TwistedHeisenberg FrameT

/-! ## §1  Frame bookkeeping -/

theorem zmod2_cases (a b : ZMod 2) : b = a ∨ b = a + 1 := by
  revert a b; decide

/-- `V₃⁺`-modes flip the twisted frame sector. -/
theorem YM_V3_flip {v : VPlus} (hv : v ∈ frameSector 1) {s : ZMod 2} {t : TP}
    (ht : t ∈ TPframe s) (k : ℤ) : plusModule.YM v k t ∈ TPframe (s + 1) := by
  have hJJ : ∀ y : Tw, frameJL.lTensor (FockT 24) (frameJL.lTensor (FockT 24) y) = y :=
    lTensor_lTensor_of_sq (frameJ_mul_self _ _ _ _)
  have hneg : frameAut (v : LatModuleGen leech) = -(v : LatModuleGen leech) := by
    rw [frameAut_apply, mem_frameSector.mp hv, Extraspecial.sgn_one, neg_one_smul]
  have hfl := leechTwistedModule_YM_frameAut (v : LatModuleGen leech) (2 * (-k - 1))
  rw [hneg, map_neg] at hfl
  rw [mem_TPframe, mem_twFrameL] at ht ⊢
  have hm : ((plusModule.YM v k t : TP) : Tw) = leechTwistedModule.YM (v : LatModuleGen leech) (2 * (-k - 1)) t := by
    rw [← mode_plusModule, mode_apply, show -(-k - 1) - 1 = k by ring]
  rw [hm]
  have h1 := LinearMap.congr_fun hfl (frameJL.lTensor (FockT 24) (t : Tw))
  simp only [Pi.neg_apply, LinearMap.neg_apply, LinearMap.comp_apply, hJJ] at h1
  rw [ht, map_smul] at h1
  rw [← h1, Extraspecial.sgn_add, Extraspecial.sgn_one, mul_neg_one, neg_smul]

/-! ## §2  The identification `σ♮ Y♮(v) σ♮ = Y♮(σ♮ v)` from the cyclic vectors -/

variable (D : SigmaData)

/-- **`L_v = R_v` from agreement on the three non-vacuum cyclic vectors.** -/
theorem conjF_V3_eq {v : VPlus} (hv : v ∈ frameSector 1) {β : leech.carrier} (hβ : β ∉ lambda0)
    (t : ZMod 2 → TLeechT) (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (h3 : ∀ p, conjF (sigNat D) (YnatU v) p (frameX0P β, 0) = YnatT leechWbar (D.Φ v) p (frameX0P β, 0))
    (hT : ∀ s p, conjF (sigNat D) (YnatU v) p (0, x0T (t s)) = YnatT leechWbar (D.Φ v) p (0, x0T (t s))) :
    conjF (sigNat D) (YnatU v) = YnatT leechWbar (D.Φ v) := by
  set L := conjF (sigNat D) (YnatU v) with hLdef
  set R := YnatT leechWbar (D.Φ v)
  have hloc : ∀ u : V0Sub.carrier, Local (L - R) (YnatU (u : VPlus)) := by
    intro u
    refine local_sub_left ?_ (YnatT_YnatU_local_genuine _ _)
    have e := conjF_YnatU_V0 D (sig u)
    rw [sig_sig] at e
    rw [← e]
    exact local_conjF (sigNat_sq D) (YnatU_local _ _)
  have hcov : DCovariant Tnat L := dCovariant_conjF (sigNat_Tnat D) (YnatU_DCovariant v)
  have hLneg : ∀ q : ℤ, q < 0 → L q vacNat = 0 := by
    intro q hq
    rw [hLdef, conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_vac, YnatU_vac_neg v q hq, map_zero]
  have hL0 : L 0 vacNat = R 0 vacNat := by
    rw [hLdef, conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_vac, YnatU_vac_zero, sigNat_V3 D hv, YnatT_vac_zero]
  have hF := eq_zero_of_V0local (L - R) hloc hβ t ht ht0
    (fun p => by
      change L p vacNat - R p vacNat = 0
      rw [tower_unique hcov (YnatT_DCovariant_genuine _) Tnat_vacNat hL0 hLneg
        (YnatT_vac_neg leechWbar _) p, sub_self])
    (fun p => by change L p _ - R p _ = 0; rw [h3 p, sub_self])
    (fun s p => by change L p _ - R p _ = 0; rw [hT s p, sub_self])
  exact sub_eq_zero.mp hF

/-! ## §3  The residual, in sector components -/

/-- **The FLM three-point identities on cyclic vectors** (the named residual of the triality route to M8h).
With `x = h₀(−½)𝟙 ⊗ t_s ∈ T_s⁺`, `v = Ψ x ∈ V₃⁺`, `x₃ = e^β + e^{−β} ∈ V₃⁺`,
`x' = h₀(−½)𝟙 ⊗ t_{s+1} ∈ T_{s+1}⁺`:
`Θ(Y^T(v,z)Φx₃) = W(x,z)x₃`, `σ(Y(v,z)v) = W̄(x,z)x`, `Ψ(Y^T(v,z)Θx') = W̄(x,z)x'`. -/
structure SigmaKey (β : leech.carrier) (t : ZMod 2 → TLeechT) : Prop where
  hβ : β ∉ lambda0
  ht : ∀ s, t s ∈ leechFrameT s
  ht0 : ∀ s, t s ≠ 0
  key_V3 : ∀ p, D.Θ (plusModule.YM (D.Ψ (x0T (t D.s))) p (D.Φ (frameX0P β)))
    = leechWsk (x0T (t D.s)) p (frameX0P β)
  key_Ts : ∀ p, sig0 (leechVOAPlus.Y (D.Ψ (x0T (t D.s))) p (D.Ψ (x0T (t D.s))))
    = leechWbar (x0T (t D.s)) p (x0T (t D.s))
  key_Ts1 : ∀ p, D.Ψ (plusModule.YM (D.Ψ (x0T (t D.s))) p (D.Θ (x0T (t (D.s + 1)))))
    = leechWbar (x0T (t D.s)) p (x0T (t (D.s + 1)))

/-- The `V₃⁺` cyclic-vector agreement **is** `key_V3`. -/
theorem key_V3_iff {v a : VPlus} (hv : v ∈ frameSector 1) (ha : a ∈ frameSector 1) (p : ℤ) :
    conjF (sigNat D) (YnatU v) p (a, 0) = YnatT leechWbar (D.Φ v) p (a, 0)
      ↔ D.Θ (plusModule.YM v p (D.Φ a)) = leechWsk (D.Φ v) p a := by
  have hm : plusModule.YM v p (D.Φ a) ∈ TPframe (D.s + 1) := YM_V3_flip hv (D.Φ_mem a ha) p
  rw [conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [sigNat_V3 D ha, YnatU_apply, YnatT_apply]
  simp only [map_zero]
  rw [sigNat_Ts1 D hm, Prod.mk.injEq]
  simp

/-- The `T_s⁺` cyclic-vector agreement **is** `key_Ts`. -/
theorem key_Ts_iff {v : VPlus} (hv : v ∈ frameSector 1) {y : TP} (hy : y ∈ TPframe D.s) (p : ℤ) :
    conjF (sigNat D) (YnatU v) p (0, y) = YnatT leechWbar (D.Φ v) p (0, y)
      ↔ sig0 (leechVOAPlus.Y v p (D.Ψ y)) = leechWbar (D.Φ v) p y := by
  have hm : leechVOAPlus.Y v p (D.Ψ y) ∈ V0Sub.carrier := by
    have h := frameSector_smul_mem hv (D.Ψ_mem y hy) (-p - 1)
    rw [PreVertexAlgebra.smul_def, mode_apply, show -(-p - 1) - 1 = p by ring,
      show (1 : ZMod 2) + 1 = 0 by decide] at h
    rw [V0Sub_carrier]; exact h
  rw [conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [sigNat_Ts D hy, YnatU_apply, YnatT_apply]
  simp only [map_zero]
  have e := sigNat_V0 D ⟨_, hm⟩
  simp only at e
  rw [e, Prod.mk.injEq, ← sig0_V0]
  simp

/-- The `T_{s+1}⁺` cyclic-vector agreement **is** `key_Ts1`. -/
theorem key_Ts1_iff {v : VPlus} (hv : v ∈ frameSector 1) {y : TP} (hy : y ∈ TPframe (D.s + 1)) (p : ℤ) :
    conjF (sigNat D) (YnatU v) p (0, y) = YnatT leechWbar (D.Φ v) p (0, y)
      ↔ D.Ψ (plusModule.YM v p (D.Θ y)) = leechWbar (D.Φ v) p y := by
  have hm : plusModule.YM v p (D.Θ y) ∈ TPframe D.s := by
    have h := YM_V3_flip hv (D.Θ_mem y hy) p
    rwa [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero] at h
  rw [conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [sigNat_Ts1 D hy, YnatU_apply, YnatT_apply]
  simp only [map_zero]
  rw [sigNat_Ts D hm, Prod.mk.injEq]
  simp

variable {D}

theorem SigmaKey.v_mem {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t) :
    D.Ψ (x0T (t D.s)) ∈ frameSector 1 :=
  D.Ψ_mem _ (x0T_mem (h.ht D.s))

theorem SigmaKey.Φv {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t) :
    D.Φ (D.Ψ (x0T (t D.s))) = x0T (t D.s) :=
  D.ΦΨ _ (x0T_mem (h.ht D.s))

/-- **The key conjugation identity**, from the residual:
`σ♮ Y♮(Ψ x) σ♮ = Y♮(x)` for `x = h₀(−½)𝟙 ⊗ t_s`. -/
theorem SigmaKey.conj_eq {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t) :
    conjF (sigNat D) (YnatU (D.Ψ (x0T (t D.s)))) = YnatT leechWbar (x0T (t D.s)) := by
  have hv := h.v_mem
  have hx := h.Φv
  refine Eq.trans (conjF_V3_eq D hv h.hβ t h.ht h.ht0 (fun p => ?_) (fun s p => ?_)) (by rw [hx])
  · rw [key_V3_iff D hv (frameX0_mem_frameSector_one h.hβ), h.Φv]
    exact h.key_V3 p
  · rcases zmod2_cases D.s s with rfl | rfl
    · rw [key_Ts_iff D hv (x0T_mem (h.ht _)), h.Φv]
      exact h.key_Ts p
    · rw [key_Ts1_iff D hv (x0T_mem (h.ht _)), h.Φv]
      exact h.key_Ts1 p

/-! ## §4  DGM (4.23) and the Moonshine module -/

/-- **DGM (4.23) for all pairs, from σ and the FLM three-point identities.** -/
theorem tpBlockLocal_of_sigma {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t)
    (t₁ t₂ : TP) : TPBlockLocal leechWbar t₁ t₂ := by
  have hloc : Local (YnatT leechWbar (x0T (t D.s))) (YnatT leechWbar (x0T (t D.s))) := by
    rw [← h.conj_eq]
    exact local_conjF (sigNat_sq D) (YnatU_local _ _)
  have h423 : TPBlockLocal leechWbar (x0T (t D.s)) (x0T (t D.s)) :=
    ((YnatT_local_iff _ _ _).1 hloc).2
  exact TPBlockLocal_all_of_gen (fun _ : Unit => x0T (t D.s)) (modeSpan_x0T (h.ht0 D.s))
    (fun _ _ => h423) t₁ t₂

/-- **The four frame pairs** of `vnat_VOA_of_TPBlockLocal_frame`. -/
theorem tpBlockLocal_frame_of_sigma {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t) :
    ∃ x : ZMod 2 → TP, (∀ s, x s ∈ TPframe s) ∧ (∀ i j, TPBlockLocal leechWbar (x i) (x j)) ∧
      ∃ V : VertexOperatorAlgebra Vnat,
        V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
          V.centralCharge = 24 ∧ V.grading = gradingNat := by
  obtain ⟨x, hx, hV⟩ := vnat_VOA_of_TPBlockLocal_frame
  have h423 : ∀ i j, TPBlockLocal leechWbar (x i) (x j) := fun i j => tpBlockLocal_of_sigma h _ _
  exact ⟨x, hx, h423, hV h423⟩

/-- **The Moonshine module from σ and the FLM three-point identities.**  Everything of
`moonshine_of_frameLocality`, with `(D, SigmaKey D β t)` as the only hypothesis. -/
theorem moonshine_of_sigma {β : leech.carrier} {t : ZMod 2 → TLeechT} (h : SigmaKey D β t) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple := by
  obtain ⟨x, -, hV⟩ := moonshine_of_frameLocality
  exact hV fun i j => tpBlockLocal_of_sigma h _ _

end VOA.Moonshine.M8hKey
