/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaKeyForm
import VOA.Moonshine.SigmaExistLeech

/-!
# SigmaKey, part 2: the adjunction reduction of `M8hKey.SigmaKey`

`M8hKey.SigmaKey D β t` has three clauses (`key_V3`, `key_Ts`, `key_Ts1`).  For `v ∈ V₃⁺` write
`L_v = σ♮ Y♮(v) σ♮` and `R_v = Y♮(Φ v)`; `F_v := L_v − R_v` (`dF`).  This file proves, by
adjunction against the invariant forms `leechBV` (on `V_Λ⁺`) and `TPForm` (on `TP`):

1. **Creation block** (`phi_create`, unconditional given `D`): `F_v` kills `V₀⁺`, i.e.
   `Φ(v₍ₘ₎ σa) = W(Φv)₍ₘ₎ a` for `a ∈ V₀⁺` — the `V₀⁺`-locality of `F_v` plus vacuum creation.
2. **`key_Ts` ⇐ `Φ` is an isometry** (`keyTs_of_iso`): the block `T_s⁺ → V₀⁺` of `F_v` is the
   adjoint of the creation block, so it vanishes as soon as `TPForm(Φa, Φb) = leechBV(a, b)` on
   `V₃⁺` (`PhiIso`).  Uses: `leechWbar_adj'`, FHL invariance `leechBV_inv`, `leechBV_sig`
   (`v0Sigma` isometry), `V₀⁺ ⟂ V₃⁺` (`leechBV_frame_orth`), frame orthogonality of `TPForm`,
   nondegeneracy `leechBVForm_leftRadical`.
3. **`key_Ts1` ⇐ `key_V3`** (`keyTs1_of_keyV3`) given `PhiIso` and `ThetaIso`: the block
   `T_{s+1}⁺ → V₃⁺` is the adjoint of the block `V₃⁺ → T_{s+1}⁺`, which vanishes on all of `V₃⁺`
   once it vanishes on one cyclic vector (`dF_kill_V3`).
4. **`key_V3` ⇐ `KeySkew`** (`keyV3_of_skew`): the cyclic vector of `V₃⁺` may be taken to be
   `v = Ψ x` itself (`cyc_Psi`), so `key_V3` reduces to the single "self-coupling" identity
   `Θ(Y^T(v,z) x) = W(x,z) v = e^{zL₋₁} Y^T(v,−z) x` (`KeySkew`), a skew-symmetry statement
   for one vector-valued series.

`sigmaKey_of_skew : PhiIso D → ThetaIso D → KeySkew D t → SigmaKey D β t`, and
`moonshine_of_skew`.  So the three FLM clauses are reduced to: `Φ` isometric, `Θ` isometric (the
normalisations `Φ ↦ cΦ`, `Ψ ↦ c⁻¹Ψ` and the sign of `Θ` are exactly the freedom left), and ONE
genuinely three-point identity `KeySkew`.

## Status
`sorry`-free.  Conditional on `D : SigmaData` and the displayed named Props `PhiIso`, `ThetaIso`,
`KeySkew`.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaKey

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen M8hKey
open LatticeTwisted TwistedHeisenberg FrameT InvForm SkewAdjoint VertexOperatorAlgebra SigmaExist

variable (D : SigmaData)

/-! ## §1  The named normalisation conditions -/

/-- `Φ : V₃⁺ → T_s⁺` is an isometry for `leechBV` and `TPForm`. -/
def PhiIso : Prop :=
  ∀ a ∈ frameSector 1, ∀ b ∈ frameSector 1, TPForm (D.Φ a) (D.Φ b) = leechBV a b

/-- `Θ : T_{s+1}⁺ → T_{s+1}⁺` is an isometry for `TPForm`. -/
def ThetaIso : Prop :=
  ∀ y ∈ TPframe (D.s + 1), ∀ y' ∈ TPframe (D.s + 1), TPForm (D.Θ y) (D.Θ y') = TPForm y y'

/-- **The self-coupling identity** (the remaining three-point content): with `x = h₀(−½)𝟙 ⊗ t_s`
and `v = Ψ x`, `Θ(Y^T(v,z)x) = W(x,z)v`, i.e. `Θ(Y^T(v,z)x) = e^{zL₋₁}Y^T(v,−z)x`. -/
def KeySkew (t : ZMod 2 → TLeechT) : Prop :=
  ∀ p, D.Θ (plusModule.YM (D.Ψ (x0T (t D.s))) p (x0T (t D.s)))
    = leechWsk (x0T (t D.s)) p (D.Ψ (x0T (t D.s)))

/-! ## §2  The difference field and the blocks it kills -/

/-- `F_v = σ♮ Y♮(v) σ♮ − Y♮(Φ v)`. -/
noncomputable def dF (v : VPlus) : FormalDist (End ℂ Vnat) :=
  conjF (sigNat D) (YnatU v) - YnatT leechWbar (D.Φ v)

theorem dF_apply (v : VPlus) (p : ℤ) (z : Vnat) :
    dF D v p z = conjF (sigNat D) (YnatU v) p z - YnatT leechWbar (D.Φ v) p z := rfl

theorem dF_local {v : VPlus} (u : V0Sub.carrier) : Local (dF D v) (YnatU (u : VPlus)) := by
  refine local_sub_left ?_ (YnatT_YnatU_local_genuine _ _)
  have e := conjF_YnatU_V0 D (sig u)
  rw [sig_sig] at e
  rw [← e]
  exact local_conjF (sigNat_sq D) (YnatU_local _ _)

theorem dF_vac {v : VPlus} (hv : v ∈ frameSector 1) (p : ℤ) : dF D v p vacNat = 0 := by
  have hcov : DCovariant Tnat (conjF (sigNat D) (YnatU v)) :=
    dCovariant_conjF (sigNat_Tnat D) (YnatU_DCovariant v)
  have hLneg : ∀ q : ℤ, q < 0 → conjF (sigNat D) (YnatU v) q vacNat = 0 := by
    intro q hq
    rw [conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_vac, YnatU_vac_neg v q hq, map_zero]
  have hL0 : conjF (sigNat D) (YnatU v) 0 vacNat = YnatT leechWbar (D.Φ v) 0 vacNat := by
    rw [conjF_apply, Module.End.mul_apply, Module.End.mul_apply]
    rw [sigNat_vac, YnatU_vac_zero, sigNat_V3 D hv, YnatT_vac_zero]
  rw [dF_apply, tower_unique hcov (YnatT_DCovariant_genuine _) Tnat_vacNat hL0 hLneg
    (YnatT_vac_neg leechWbar _) p, sub_self]

theorem dF_kill_V0 {v : VPlus} (hv : v ∈ frameSector 1) (a : V0Sub.carrier) (p : ℤ) :
    dF D v p ((a : VPlus), 0) = 0 := by
  have hl : Local (dF D v) (YnatU (a : VPlus)) := dF_local D a
  have h := kill_mode hl (YnatU_isField (a : VPlus)) (dF_vac D hv) p 0
  rw [YnatU_vac_zero] at h
  exact h

/-- `F_v` kills all of `V₃⁺` once it kills one `V₀⁺`-cyclic vector `z` of `V₃⁺`. -/
theorem dF_kill_V3 {v z : VPlus}
    (hz : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z}
      = frameSector 1)
    (hk : ∀ p, dF D v p (z, 0) = 0) {b : VPlus} (hb : b ∈ frameSector 1) (p : ℤ) :
    dF D v p (b, 0) = 0 := by
  set K : Submodule ℂ Vnat := ⨅ p : ℤ, LinearMap.ker (dF D v p) with hK
  have hmemK : ∀ y, y ∈ K ↔ ∀ p, dF D v p y = 0 := by
    intro y; simp [hK, Submodule.mem_iInf, LinearMap.mem_ker]
  have hsub : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z}
      ≤ K.comap (LinearMap.inl ℂ SkewVP TP) := by
    rw [Submodule.span_le]
    rintro y ⟨u, -, n, rfl⟩
    change LinearMap.inl ℂ SkewVP TP (actV u n z) ∈ K
    rw [hmemK]
    intro q
    have h' := kill_mode (dF_local D (v := v) u) (YnatU_isField _) hk q (-n - 1)
    rw [YnatU_apply, Y_eq_actV, show -(-n - 1) - 1 = n by ring] at h'
    simpa using h'
  rw [← hz] at hb
  exact (hmemK _).1 (hsub hb) p

/-! ## §3  Frame bookkeeping for `W` and weight facts -/

theorem leechLTP_eq_actT (y : TP) : leechLTP y = actT V0P.conformalVector 0 y := rfl

theorem leechLTP_pow_mem {s : ZMod 2} {y : TP} (hy : y ∈ TPframe s) (i : ℕ) :
    (leechLTP ^ i) y ∈ TPframe s := by
  induction i with
  | zero => simpa using hy
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, leechLTP_eq_actT]
    exact actT_stab s _ (Set.mem_univ _) 0 _ ih

/-- `W(x)₍ₘ₎` maps `V₃⁺` from `T_s⁺` to `T_{s+1}⁺`. -/
theorem leechWsk_mem_V3 {s : ZMod 2} {x : TP} (hx : x ∈ TPframe s) {b : VPlus}
    (hb : b ∈ frameSector 1) (m : ℤ) : mode (leechWsk x) m b ∈ TPframe (s + 1) := by
  rw [mode_leechWsk]
  refine finsum_induction (p := fun y => y ∈ TPframe (s + 1)) (Submodule.zero_mem _)
    (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun i => Submodule.smul_mem _ _ ?_)
  refine leechLTP_pow_mem ?_ i
  rw [mode_apply]
  exact YM_V3_flip hb hx _

/-- `W(x)₍ₘ₎` maps `V₀⁺` into the sector of `x`. -/
theorem leechWsk_mem_V0 {s : ZMod 2} {x : TP} (hx : x ∈ TPframe s) (a : V0Sub.carrier) (m : ℤ) :
    mode (leechWsk x) m (a : VPlus) ∈ TPframe s := by
  rw [mode_leechWsk]
  refine finsum_induction (p := fun y => y ∈ TPframe s) (Submodule.zero_mem _)
    (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun i => Submodule.smul_mem _ _ ?_)
  exact leechLTP_pow_mem (actT_stab s a (Set.mem_univ _) _ x hx) i

theorem YM_mode_V3_flip {v : VPlus} (hv : v ∈ frameSector 1) {s : ZMod 2} {y : TP}
    (hy : y ∈ TPframe s) (m : ℤ) : mode (plusModule.YM v) m y ∈ TPframe (s + 1) := by
  rw [mode_apply]; exact YM_V3_flip hv hy _

theorem zmod2_add_one_add_one (s : ZMod 2) : s + 1 + 1 = s := by
  rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]

/-- `v = Ψ x` has weight 2 and is quasi-primary when `x ∈ T_s⁺` has weight 2. -/
theorem Psi_L0 {x : TP} (hx : x ∈ TPframe D.s) (hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ)) :
    D.Ψ x ∈ leechVOAPlus.grading 2 := by
  apply mem_grading_of_L0
  have hv := D.Ψ_mem x hx
  have h1 : leechVOAPlus.L 0 (D.Ψ x) ∈ frameSector 1 := by
    have := actV_stab V0P.conformalVector (Set.mem_univ _) 1 _ hv
    exact this
  have h2 : D.Φ (leechVOAPlus.L 0 (D.Ψ x)) = D.Φ (((2 : ℤ) : ℂ) • D.Ψ x) := by
    have e := D.isSigma_Φ V0P.conformalVector (Set.mem_univ _) 1 (D.Ψ x) hv
    rw [sig_omega] at e
    change D.Φ (actV V0P.conformalVector 1 (D.Ψ x)) = _
    rw [e, D.ΦΨ x hx, map_smul, D.ΦΨ x hx]
    exact plusModule.L0_weight _ _ hx2
  have := congrArg D.Ψ h2
  rwa [D.ΨΦ _ h1, D.ΨΦ _ (Submodule.smul_mem _ _ hv)] at this

theorem Psi_L1 {x : TP} (hx : x ∈ TPframe D.s) (hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ)) :
    leechVOAPlus.L 1 (D.Ψ x) = 0 := by
  have hv := D.Ψ_mem x hx
  have h1 : leechVOAPlus.L 1 (D.Ψ x) ∈ frameSector 1 :=
    actV_stab V0P.conformalVector (Set.mem_univ _) 2 _ hv
  have h2 : D.Φ (leechVOAPlus.L 1 (D.Ψ x)) = 0 := by
    have e := D.isSigma_Φ V0P.conformalVector (Set.mem_univ _) 2 (D.Ψ x) hv
    rw [sig_omega] at e
    change D.Φ (actV V0P.conformalVector 2 (D.Ψ x)) = _
    rw [e, D.ΦΨ x hx]
    exact Lp1_weight_two hx2
  have := congrArg D.Ψ h2
  rwa [D.ΨΦ _ h1, map_zero] at this

/-! ## §4  The creation block -/

/-- **The creation block**: `Φ(v₍ₘ₎ σa) = W(Φv)₍ₘ₎ a` for `v ∈ V₃⁺`, `a ∈ V₀⁺`. -/
theorem phi_create {v : VPlus} (hv : v ∈ frameSector 1) (a : V0Sub.carrier) (m : ℤ) :
    D.Φ (leechVOAPlus.smul v m ((sig a : V0Sub.carrier) : VPlus))
      = mode (leechWsk (D.Φ v)) m (a : VPlus) := by
  have h := dF_kill_V0 D hv a (-m - 1)
  rw [dF_apply, conjF_apply, Module.End.mul_apply, Module.End.mul_apply, sigNat_V0, YnatU_apply,
    map_zero, YnatT_apply, map_zero] at h
  have hm : leechVOAPlus.Y v (-m - 1) ((v0Sigma a : V0Sub.carrier) : VPlus) ∈ frameSector 1 := by
    have := frameSector_smul_mem hv (mem_V0 (sig a)) m
    rw [add_zero, PreVertexAlgebra.smul_def, mode_apply] at this
    exact this
  rw [sigNat_V3 D hm] at h
  have h2 := congrArg Prod.snd h
  simp only [Prod.snd_sub, Prod.snd_zero] at h2
  rw [PreVertexAlgebra.smul_def, mode_apply, mode_apply]
  exact sub_eq_zero.mp h2

/-! ## §5  `key_Ts` from the isometry of `Φ` -/

theorem leechBV_eq_zero_of_forall {X : VPlus}
    (h0 : ∀ a : V0Sub.carrier, leechBV X (a : VPlus) = 0)
    (h3 : ∀ b ∈ frameSector 1, leechBV X b = 0) : X = 0 := by
  have hX : X ∈ InvariantForm.leftRadical leechBVForm := by
    rw [InvariantForm.mem_leftRadical]
    refine LinearMap.ext fun φ => ?_
    have hφ : φ ∈ V0Sub.carrier ⊔ frameSector 1 := by rw [V0_isCompl.sup_eq_top]; trivial
    obtain ⟨φ₀, hφ₀, φ₃, hφ₃, rfl⟩ := Submodule.mem_sup.mp hφ
    rw [map_add, h0 ⟨φ₀, hφ₀⟩, h3 φ₃ hφ₃, add_zero]
    rfl
  rw [Moonshine.leechBVForm_leftRadical] at hX
  exact (Submodule.mem_bot ℂ).1 hX

/-- The adjunction for `W̄(x)`, `x ∈ TP₂`: `B_V(W̄(x)₍ₙ₎y, φ) = TPForm(y, W(x)₍₂₋ₙ₎ φ)`. -/
theorem leechBV_Wbar_two {x : TP} (hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ)) (n : ℤ) (y : TP)
    (φ : VPlus) : leechBV (leechWbarMode n x y) φ = TPForm y (mode (leechWsk x) (2 - n) φ) := by
  rw [leechWbar_adj' n hx2 1 (fun j hj => ?_) y φ]
  · simp only [Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero,
      Nat.cast_one, inv_one, Nat.cast_zero, sub_zero, one_smul]
    rw [show (2 : ℤ) * 2 - n - 2 = 2 - n by ring]
    norm_num
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm, pow_add, pow_one, Module.End.mul_apply, Lp1_weight_two hx2, map_zero]

/-- FHL invariance of `leechBV` for a weight-2 quasi-primary `v`. -/
theorem leechBV_qp_two {v : VPlus} (hv2 : v ∈ leechVOAPlus.grading 2)
    (hqp : leechVOAPlus.L 1 v = 0) (n : ℤ) (a b : VPlus) :
    leechBV (leechVOAPlus.smul v n a) b = leechBV a (leechVOAPlus.smul v (2 - n) b) := by
  rw [leechBV_inv 2 v hv2 n a b]
  have e := sum_L1_qp (W := leechVOAPlus) hqp 2
    (fun j w => leechBV a (leechVOAPlus.smul w (2 * 2 - n - 2 - (j : ℤ)) b))
    (fun j => by simp [leechVOAPlus.smul_zero_left])
  simp only at e
  rw [show (2 : ℤ).toNat + 1 = 2 + 1 from rfl, e]
  rw [show (2 : ℤ) * 2 - n - 2 - ((0 : ℕ) : ℤ) = 2 - n by push_cast; ring]
  norm_num

/-- FHL invariance of `TPForm` for a weight-2 quasi-primary `v`. -/
theorem TPForm_qp_two {v : VPlus} (hv2 : v ∈ leechVOAPlus.grading 2)
    (hqp : leechVOAPlus.L 1 v = 0) (n : ℤ) (a b : TP) :
    TPForm (mode (plusModule.YM v) n a) b = TPForm a (mode (plusModule.YM v) (2 - n) b) := by
  rw [TPForm_fhlInv hv2 n a b]
  have e := sum_L1_qp (W := leechVOAPlus) hqp 2
    (fun j w => TPForm a (mode (plusModule.YM w) (2 * 2 - n - 2 - (j : ℤ)) b))
    (fun j => by simp)
  simp only at e
  rw [show (2 : ℤ).toNat + 1 = 2 + 1 from rfl, e]
  rw [show (2 : ℤ) * 2 - n - 2 - ((0 : ℕ) : ℤ) = 2 - n by push_cast; ring]
  norm_num

theorem sig0_mem (z : VPlus) : sig0 z ∈ frameSector 0 := by
  rw [← V0Sub_carrier, sig0, LinearMap.comp_apply]
  exact Subtype.prop _

/-- **`key_Ts` from the isometry of `Φ`**, for every `y ∈ T_s⁺` (mode form):
`σ(v₍ₙ₎ Ψy) = W̄(x)₍ₙ₎ y` with `v = Ψ x`, `x ∈ T_s⁺` of weight 2. -/
theorem keyTs_gen (hΦ : PhiIso D) {x : TP} (hx : x ∈ TPframe D.s)
    (hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ)) {y : TP} (hy : y ∈ TPframe D.s) (n : ℤ) :
    sig0 (leechVOAPlus.smul (D.Ψ x) n (D.Ψ y)) = leechWbarMode n x y := by
  set v := D.Ψ x with hvdef
  have hv : v ∈ frameSector 1 := D.Ψ_mem x hx
  have hΦv : D.Φ v = x := D.ΦΨ x hx
  have hv2 := Psi_L0 D hx hx2
  have hqp := Psi_L1 D hx hx2
  have hΨy := D.Ψ_mem y hy
  have hz : leechVOAPlus.smul v n (D.Ψ y) ∈ V0Sub.carrier := by
    rw [V0Sub_carrier]
    have := frameSector_smul_mem hv hΨy n
    rwa [show (1 : ZMod 2) + 1 = 0 by decide] at this
  rw [← sub_eq_zero]
  refine leechBV_eq_zero_of_forall (fun a => ?_) (fun b hb => ?_)
  · rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    have hs : sig0 (leechVOAPlus.smul v n (D.Ψ y))
        = ((sig ⟨_, hz⟩ : V0Sub.carrier) : VPlus) := sig0_V0 ⟨_, hz⟩
    rw [hs, leechBV_sig_adj ⟨_, hz⟩ a]
    change leechBV (leechVOAPlus.smul v n (D.Ψ y)) _ = _
    rw [leechBV_qp_two hv2 hqp, ← hΦ _ hΨy _ (by
        have := frameSector_smul_mem hv (mem_V0 (sig a)) (2 - n)
        rwa [add_zero] at this),
      D.ΦΨ y hy, phi_create D hv a, hΦv, leechBV_Wbar_two hx2]
  · rw [map_sub, LinearMap.sub_apply, leechBV_frame_orth (sig0_mem _) hb, leechBV_Wbar_two hx2,
      TPForm_frame_orth' hy (leechWsk_mem_V3 hx hb _), sub_zero]

/-! ## §6  `key_Ts1` from `key_V3` -/

/-- **`key_Ts1` from the full `V₃⁺ → T_{s+1}⁺` block** (mode form), given both isometries. -/
theorem keyTs1_gen (hΦ : PhiIso D) (hΘ : ThetaIso D) {x : TP} (hx : x ∈ TPframe D.s)
    (hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ))
    (hV3 : ∀ b ∈ frameSector 1, ∀ m : ℤ,
      D.Θ (mode (plusModule.YM (D.Ψ x)) m (D.Φ b)) = mode (leechWsk x) m b)
    {y : TP} (hy : y ∈ TPframe (D.s + 1)) (n : ℤ) :
    D.Ψ (mode (plusModule.YM (D.Ψ x)) n (D.Θ y)) = leechWbarMode n x y := by
  set v := D.Ψ x with hvdef
  have hv : v ∈ frameSector 1 := D.Ψ_mem x hx
  have hv2 := Psi_L0 D hx hx2
  have hqp := Psi_L1 D hx hx2
  have hΘy := D.Θ_mem y hy
  have hm : mode (plusModule.YM v) n (D.Θ y) ∈ TPframe D.s := by
    have := YM_mode_V3_flip hv hΘy n
    rwa [zmod2_add_one_add_one] at this
  rw [← sub_eq_zero]
  refine leechBV_eq_zero_of_forall (fun a => ?_) (fun b hb => ?_)
  · rw [map_sub, LinearMap.sub_apply, leechBV_frame_orth' (D.Ψ_mem _ hm) (mem_V0 a),
      leechBV_Wbar_two hx2]
    have h0 := leechWsk_mem_V0 hx a (2 - n)
    rw [← zmod2_add_one_add_one D.s] at h0
    rw [TPForm_frame_orth' hy h0, sub_zero]
  · rw [map_sub, LinearMap.sub_apply, sub_eq_zero, leechBV_Wbar_two hx2, ← hV3 b hb]
    have hb' : mode (plusModule.YM v) (2 - n) (D.Φ b) ∈ TPframe (D.s + 1) :=
      YM_mode_V3_flip hv (D.Φ_mem b hb) _
    have e1 : TPForm y (D.Θ (mode (plusModule.YM v) (2 - n) (D.Φ b)))
        = TPForm (D.Θ y) (mode (plusModule.YM v) (2 - n) (D.Φ b)) := by
      rw [← hΘ _ hΘy _ hb', D.ΘΘ y hy]
    rw [e1, ← TPForm_qp_two hv2 hqp, ← hΦ _ (D.Ψ_mem _ hm) _ hb, D.ΦΨ _ hm]

/-! ## §7  `key_V3` from the self-coupling identity -/

/-- `v = Ψ x` is a `V₀⁺`-cyclic vector of `V₃⁺` when `x` is `V₀⁺`-cyclic in `T_s⁺`. -/
theorem cyc_Psi {x : TP} (hx : x ∈ TPframe D.s)
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x}
      = TPframe D.s) :
    Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n (D.Ψ x)}
      = frameSector 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨u, -, n, rfl⟩
    exact actV_stab u (Set.mem_univ _) n _ (D.Ψ_mem x hx)
  · intro b hb
    have hΦb : D.Φ b ∈ Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actT u n x} := by
      rw [hcyc]; exact D.Φ_mem b hb
    have hmap := Submodule.mem_map_of_mem (f := D.Ψ) hΦb
    rw [D.ΨΦ b hb, Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, ⟨u, -, n, rfl⟩, rfl⟩
    refine ⟨sig u, Set.mem_univ _, n, ?_⟩
    exact D.isSigma_Ψ u (Set.mem_univ _) n x hx

theorem keyV3_block_of_skew {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0) (hk : KeySkew D t)
    {b : VPlus} (hb : b ∈ frameSector 1) (p : ℤ) :
    D.Θ (plusModule.YM (D.Ψ (x0T (t D.s))) p (D.Φ b)) = leechWsk (x0T (t D.s)) p b := by
  set x := x0T (t D.s)
  have hx : x ∈ TPframe D.s := x0T_mem (ht D.s)
  have hv : D.Ψ x ∈ frameSector 1 := D.Ψ_mem x hx
  have hΦv : D.Φ (D.Ψ x) = x := D.ΦΨ x hx
  have hkill : ∀ q, dF D (D.Ψ x) q (D.Ψ x, 0) = 0 := by
    intro q
    rw [dF_apply, sub_eq_zero]
    rw [key_V3_iff D hv hv q, hΦv]
    exact hk q
  have hall := dF_kill_V3 D (cyc_Psi D hx (cyc_T (ht D.s) (ht0 D.s))) hkill hb p
  rw [dF_apply, sub_eq_zero, key_V3_iff D hv hb p, hΦv] at hall
  exact hall

/-- **`SigmaKey` from the two isometries and the self-coupling identity.** -/
theorem sigmaKey_of_skew {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiIso D) (hΘ : ThetaIso D) (hk : KeySkew D t) : SigmaKey D β t := by
  set x := x0T (t D.s)
  have hx : x ∈ TPframe D.s := x0T_mem (ht D.s)
  have hx2 : x ∈ plusModule.weight ((2 : ℤ) : ℂ) := by
    have := x0T_mem_weight (t D.s); exact_mod_cast this
  have hblock : ∀ b ∈ frameSector 1, ∀ p : ℤ,
      D.Θ (plusModule.YM (D.Ψ x) p (D.Φ b)) = leechWsk x p b :=
    fun b hb p => keyV3_block_of_skew D ht ht0 hk hb p
  refine ⟨hβ, ht, ht0, ?_, ?_, ?_⟩
  · intro p
    exact hblock _ (frameX0_mem_frameSector_one hβ) p
  · intro p
    have h := keyTs_gen D hΦ hx hx2 hx (-p - 1)
    rw [PreVertexAlgebra.smul_def, mode_apply, show -(-p - 1) - 1 = p by ring] at h
    rw [leechWbar_coeff]
    exact h
  · intro p
    have hV3 : ∀ b ∈ frameSector 1, ∀ m : ℤ,
        D.Θ (mode (plusModule.YM (D.Ψ x)) m (D.Φ b)) = mode (leechWsk x) m b := by
      intro b hb m
      rw [mode_apply, mode_apply]
      exact hblock b hb _
    have h := keyTs1_gen D hΦ hΘ hx hx2 hV3 (x0T_mem (ht (D.s + 1))) (-p - 1)
    rw [mode_apply, show -(-p - 1) - 1 = p by ring] at h
    rw [leechWbar_coeff]
    exact h

/-- **The Moonshine module from σ-data, the two isometries and the self-coupling identity.** -/
theorem moonshine_of_skew {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiIso D) (hΘ : ThetaIso D) (hk : KeySkew D t) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_sigma (sigmaKey_of_skew D hβ ht ht0 hΦ hΘ hk)

end VOA.Moonshine.SigmaKey
