/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaExistGeneric
import VOA.Moonshine.TrialityTwSigma
import VOA.Moonshine.SimpleForm
import VOA.Moonshine.Generation
import VOA.Modules.ModuleRestrictOrd
import VOA.Modules.FiniteGenerationProof
import VOA.Modules.ZeroModeMult
import VOA.Modules.ContragredientJacobi
import VOA.Modules.ContragredientTransport

/-!
# The triality `σ` on `V₃⁺` and `T₃⁺`: reduction to the top level
(Moonshine step M8g twisted half)

`TrialityTwSigma.lean` reduced the existence of `σ : V₃⁺ → T_s⁺` (resp. `T_{s'}⁺ → TP`) to the
annihilator compatibility `AnnCompat … x₀ y₀` of the explicit cyclic vector.  This file
reduces that compatibility, **unconditionally**, to a statement about the **top levels**
(weight 2, both 49152-dimensional), via the generic `SigmaExist.annCompat_of_top`.

## The named residual
`TopSigmaV3 s φ` (resp. `TopSigmaTT s' s φ`) for a linear `φ`: on the top level
`Ω = (V₃⁺)₂` (resp. `(T_{s'}⁺)₂`),
* `φ Ω ⊆ (T_s⁺)₂`;
* **zero-mode intertwining**: `φ (o(a) x) = o(σa) (φ x)` for every homogeneous `a ∈ V₀⁺`
  (`o(a) = a₍wt a − 1₎`) and `x ∈ Ω`;
* nontriviality: `φ Ω` contains a cyclic vector `x0T t₀` of `T_s⁺` (`0 ≠ t₀ ∈ T_s`).

These are **necessary** for `σ` (they are properties of `σ|_Ω`); the theorems below show they
are **sufficient**.  The residual is a finite-dimensional statement for each `a`, but it is
quantified over **all** homogeneous `a ∈ V₀⁺` (all weights): the numerical verification
covers `a ∈ (V₀⁺)₂` only.

## Main results
* `AV`, `BTs`, `AT` — `V_Λ⁺`, `σ`-twisted `TP`, and `TP` as weak `V₀⁺`-modules.
* `TPForm_frame_orth` — `T₀⁺ ⊥ T₁⁺` for `TPForm`; `TPForm_eq_zero_of_frame` — `TPForm` is
  nondegenerate on each `T_s⁺`.
* `annCompat_V3_of_top`, `annCompat_TT_of_top` — the residual implies `AnnCompat` for
  every top vector.
* `sigmaV3T_exists_of_top` — the residual gives a `v0Sigma`-twisted intertwiner
  `Φ : V_Λ⁺ → TP` on `V₃⁺` with `Φ = φ` on the top level (so `Φ ≠ 0`), for the explicit
  weight-2 cyclic vector `x₀ = e^{β₂} + e^{−β₂}`, `β₂ = u − 8e₀ = (−3, 1²³)/√8`.
* `sigmaTT_exists_of_top` — same for `T_{s'}⁺ → TP` with `x₀ = h₀(−½)𝟙 ⊗ t₀'`.
* `β₂`, `β₂_not_mem`, `frameX0P_β₂_mem` — the explicit norm-4 vector outside `Λ₀`.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]` for every declaration.
**Conditional on the named residual `TopSigmaV3` / `TopSigmaTT`**, which is not proved here.
Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.InvForm VOA.TwistedHeisenberg
open Module (End)
open Submodule

/-! ## §1  The three weak `V₀⁺`-modules -/

/-- `V_Λ⁺` as a weak `V₀⁺`-module (restricted adjoint action): `a ↦ a₍ₙ₎ = actV a n`. -/
noncomputable def AV : WeakModule V0P VPlus := V0Sub.restrictWeakModule (adjointWeakModule leechVOAPlus)

/-- `TP = (V_Λ^T)⁺` as a weak `V₀⁺`-module (restriction of `plusModule`). -/
noncomputable def AT : WeakModule V0P TP := V0Sub.restrictWeakModule plusModule.toWeakModule

/-- `TP` with the `v0Sigma`-twisted `V₀⁺`-action `a ↦ (σ a)₍ₙ₎`. -/
noncomputable def BTs : WeakModule V0P TP := twistModule AT v0Sigma

theorem mode_AV (u : V0Sub.carrier) (n : ℤ) : mode (AV.YM u) n = actV u n := rfl

theorem mode_AT (u : V0Sub.carrier) (n : ℤ) : mode (AT.YM u) n = actT u n := rfl

theorem mode_BTs (u : V0Sub.carrier) (n : ℤ) : mode (BTs.YM u) n = actT (sig u) n := rfl

theorem mem_V0P_grading {k : ℤ} {a : V0Sub.carrier} :
    a ∈ V0P.grading k ↔ (a : VPlus) ∈ leechVOAPlus.grading k := Iff.rfl

theorem sig_mem_grading {k : ℤ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading k) :
    ((sig a : V0Sub.carrier) : VPlus) ∈ leechVOAPlus.grading k :=
  mem_V0P_grading.mp (Aut.map_grading v0Sigma (mem_V0P_grading.mpr ha))

theorem actT_add_left (u v : V0Sub.carrier) (n : ℤ) (y : TP) :
    actT (u + v) n y = actT u n y + actT v n y := by
  simp only [actT, Submodule.coe_add, map_add, mode_add, LinearMap.add_apply]

theorem actV_add_left (u v : V0Sub.carrier) (n : ℤ) (y : VPlus) :
    actV (u + v) n y = actV u n y + actV v n y := by
  simp only [actV, Submodule.coe_add, map_add, mode_add, LinearMap.add_apply]

/-- Induction over the homogeneous components of a letter of `V₀⁺`. -/
theorem V0_induction {p : V0Sub.carrier → Prop} (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hhom : ∀ (k : ℤ) (a : V0Sub.carrier), (a : VPlus) ∈ leechVOAPlus.grading k → p a)
    (a : V0Sub.carrier) : p a := by
  have ha : a ∈ ⨆ k, V0P.grading k := by rw [V0P.isInternal.submodule_iSup_eq_top]; trivial
  induction ha using Submodule.iSup_induction' with
  | mem k a hak => exact hhom k a hak
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb

/-! ## §2  `TPForm` on the frame sectors -/

theorem TForm_frameJ (t t' : TLeechT) :
    TFormLeech.TForm (frameJL t) t' = 1 * TFormLeech.TForm t (frameJL t') := by
  have h8 : leech.form frameW frameW = 8 := by rw [leech_form_frameW]; rfl
  simp only [frameJL, FrameT.frameJ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    TFormLeech.TForm_eT, h8, LinearMap.smul_apply]
  norm_num

theorem twForm_frameJ (x y : Tw) :
    leechTwForm (frameJL.lTensor (FockT 24) x) y = leechTwForm x (frameJL.lTensor (FockT 24) y) := by
  have h := twForm_map (r := 24) TFormLeech.TForm (X := LinearMap.id) (X' := LinearMap.id)
    (g := frameJL) (g' := frameJL) (s₁ := 1) (s₂ := 1) (fun p q => by simp) TForm_frameJ x y
  rw [one_mul, one_mul] at h
  exact h

/-- **`T₀⁺ ⊥ T₁⁺`** for `TPForm` (the frame involution `J = c⁻¹e_w` is `TForm`-self-adjoint,
since `⟨w,w⟩/2 = 4` is even). -/
theorem TPForm_frame_orth {x y : TP} (hx : x ∈ TPframe 0) (hy : y ∈ TPframe 1) : TPForm x y = 0 := by
  rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_zero, one_smul] at hx
  rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_one, neg_one_smul] at hy
  have h := twForm_frameJ (x : Tw) (y : Tw)
  rw [hx, hy, map_neg] at h
  rw [TPForm_apply]
  have : (2 : ℂ) * leechTwForm (x : Tw) (y : Tw) = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  simpa using this

theorem TPForm_frame_orth' {s : ZMod 2} {x y : TP} (hx : x ∈ TPframe s) (hy : y ∈ TPframe (s + 1)) :
    TPForm x y = 0 := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) s with rfl | rfl
  · exact TPForm_frame_orth hx hy
  · rw [TPForm_symm]; exact TPForm_frame_orth hy hx

/-- **`TPForm` is nondegenerate on each `T_s⁺`.** -/
theorem TPForm_eq_zero_of_frame {s : ZMod 2} {y : TP} (hy : y ∈ TPframe s)
    (h : ∀ z ∈ TPframe s, TPForm y z = 0) : y = 0 := by
  apply SimpleNat.TPForm_eq_zero_of_forall
  intro z
  have hz : z ∈ TPframe s ⊔ TPframe (s + 1) := by
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) s with rfl | rfl
    · rw [zero_add, TPframe_isCompl.sup_eq_top]; trivial
    · rw [show (1 : ZMod 2) + 1 = 0 from rfl, sup_comm, TPframe_isCompl.sup_eq_top]; trivial
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add, h z₁ hz₁, TPForm_frame_orth' hy hz₂, add_zero]

/-! ## §3  The target-side hypotheses (shared by both sectors) -/

/-- Homogeneous letters of `V₀⁺`. -/
def homLetters : Set V0Sub.carrier := {c | ∃ k : ℤ, (c : VPlus) ∈ leechVOAPlus.grading k}

theorem L1_pow_mem (j : ℕ) {u : VPlus} (hu : u ∈ V0Sub.carrier) :
    ((leechVOAPlus.L 1) ^ j) u ∈ V0Sub.carrier := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, VertexOperatorAlgebra.L_def]
    exact V0Sub.smul_mem _ V0Sub.conformal_mem _ _ ih

/-- **Invariance (`hadj`) for the twisted target.**  For homogeneous `c`, the `TPForm`-adjoint of
`(σc)₍r₎` is a finite combination of `σ`-twisted modes (FHL invariance `TPForm_fhlInv`). -/
theorem hadj_BTs : ∀ c ∈ homLetters, ∀ r : ℤ, ∃ (n : ℕ) (a : ℕ → V0Sub.carrier) (q : ℕ → ℤ)
    (t : ℕ → ℂ), ∀ y y' : TP,
      TPForm y (BTs.act c r y') = TPForm (∑ i ∈ Finset.range n, t i • BTs.act (a i) (q i) y) y' := by
  rintro c ⟨k, hk⟩ r
  set u : VPlus := ((sig c : V0Sub.carrier) : VPlus)
  have hu : u ∈ leechVOAPlus.grading k := sig_mem_grading hk
  have huV : u ∈ V0Sub.carrier := (sig c).2
  refine ⟨k.toNat + 1, fun j => sig ⟨((leechVOAPlus.L 1) ^ j) u, L1_pow_mem j huV⟩,
    fun j => 2 * k - r - 2 - (j : ℤ), fun j => (-1 : ℂ) ^ k * ((j.factorial : ℂ)⁻¹), ?_⟩
  intro y y'
  have hinv := TPForm_fhlInv hu r y' y
  rw [TPForm_symm, WeakModule.act_def, mode_BTs]
  change TPForm (mode (plusModule.YM u) r y') y = _
  rw [hinv, map_sum, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [WeakModule.act_def, mode_BTs, sig_sig, map_smul, LinearMap.smul_apply, smul_eq_mul,
    TPForm_symm]
  simp only [smul_eq_mul]
  rw [mul_assoc]
  rfl

/-- The target cyclic span lies in `T_s⁺` when `φ Ω` does. -/
theorem modeSpan_BTs_le {s : ZMod 2} {X : Set TP} (hX : ∀ y ∈ X, y ∈ TPframe s) :
    modeSpan BTs X ≤ TPframe s := by
  rw [modeSpan, span_le]
  rintro _ ⟨a, q, y, hy, rfl⟩
  exact actT_stab s (sig a) (Set.mem_univ _) q y (hX y hy)

/-- `T_s⁺` lies in the test span once `φ Ω` contains a cyclic vector `x0T t₀`. -/
theorem TPframe_le_testSpan {M : Type*} [AddCommGroup M] [Module ℂ M] {s : ZMod 2}
    {Ω : Submodule ℂ M} {φ : M →ₗ[ℂ] TP} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    {xh : M} (hxh : xh ∈ Ω) (hφxh : φ xh = x0T t₀) :
    TPframe s ≤ testSpan BTs homLetters Ω φ := by
  rw [← cyc_T ht₀ h0, span_le]
  rintro _ ⟨u, -, n, rfl⟩
  revert n
  refine V0_induction (p := fun u => ∀ n, actT u n (x0T t₀) ∈ testSpan BTs homLetters Ω φ)
    ?_ ?_ ?_ u
  · intro n
    simp only [actT, ZeroMemClass.coe_zero, map_zero, mode_zero, LinearMap.zero_apply]
    exact zero_mem _
  · intro a b ha hb n
    rw [actT_add_left]; exact add_mem (ha n) (hb n)
  · intro k a ha n
    refine subset_span ⟨sig a, ⟨k, sig_mem_grading ha⟩, n, xh, hxh, ?_⟩
    rw [WeakModule.act_def, mode_BTs, sig_sig, hφxh]

/-- **Nondegeneracy (`hnd`) for the twisted target.** -/
theorem hnd_BTs {M : Type*} [AddCommGroup M] [Module ℂ M] {s : ZMod 2} {Ω : Submodule ℂ M}
    {φ : M →ₗ[ℂ] TP} (hmaps : ∀ x ∈ Ω, φ x ∈ TPframe s) {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s)
    (h0 : t₀ ≠ 0) {xh : M} (hxh : xh ∈ Ω) (hφxh : φ xh = x0T t₀) :
    ∀ y ∈ modeSpan BTs (φ '' Ω), (∀ z ∈ testSpan BTs homLetters Ω φ, TPForm y z = 0) → y = 0 := by
  intro y hy hz
  have hyT : y ∈ TPframe s :=
    modeSpan_BTs_le (by rintro _ ⟨x, hx, rfl⟩; exact hmaps x hx) hy
  exact TPForm_eq_zero_of_frame hyT
    (fun z hzT => hz z (TPframe_le_testSpan ht₀ h0 hxh hφxh hzT))

/-! ## §4  `V₃⁺ → T_s⁺` -/

/-- The top level `Ω = (V₃⁺)₂` of `V₃⁺`. -/
noncomputable def OmegaV3 : Submodule ℂ VPlus := frameSector 1 ⊓ leechVOAPlus.grading 2

/-- **The named residual for `σ` on `V₃⁺`**: a top-level `σ`-twisted zero-mode intertwiner
`φ : (V₃⁺)₂ → (T_s⁺)₂` hitting a cyclic vector of `T_s⁺`.  (Necessary for `σ`; sufficient by
`sigmaV3T_exists_of_top`.) -/
structure TopSigmaV3 (s : ZMod 2) (φ : VPlus →ₗ[ℂ] TP) : Prop where
  /-- `φ` maps the top level of `V₃⁺` into `T_s⁺`. -/
  maps_frame : ∀ x ∈ OmegaV3, φ x ∈ TPframe s
  /-- `φ` maps the top level into weight 2. -/
  maps_weight : ∀ x ∈ OmegaV3, φ x ∈ plusModule.weight (2 : ℂ)
  /-- Zero-mode intertwining: `φ (o(a) x) = o(σ a) φ x` for every homogeneous `a ∈ V₀⁺`. -/
  zero_mode : ∀ (k : ℤ) (a : V0Sub.carrier), (a : VPlus) ∈ leechVOAPlus.grading k →
    ∀ x ∈ OmegaV3, φ (actV a (k - 1) x) = actT (sig a) (k - 1) (φ x)
  /-- `φ` hits a cyclic vector `h₀(−½)𝟙 ⊗ t₀` of `T_s⁺`. -/
  hits_cyclic : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, φ x = x0T t₀

theorem hZO_V3 {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP} (hφ : TopSigmaV3 s φ) :
    ∀ (k : ℤ) (a : V0Sub.carrier), a ∈ V0P.grading k → ∀ (q : ℤ), ∀ x ∈ OmegaV3, ∀ x' ∈ OmegaV3,
      TPForm (BTs.act a q (φ x)) (φ x')
        = TPForm (φ (piHom leechVOAPlus 2 (AV.act a q x))) (φ x') := by
  intro k a ha q x hx x' hx'
  have ha' : (a : VPlus) ∈ leechVOAPlus.grading k := ha
  have hx2 : x ∈ leechVOAPlus.grading 2 := hx.2
  have hmem : AV.act a q x ∈ leechVOAPlus.grading (k + 2 - q - 1) :=
    leechVOAPlus.grading_mode _ ha' _ hx2 q
  rw [WeakModule.act_def, mode_BTs]
  by_cases hq : q = k - 1
  · subst hq
    rw [piHom_of_mem leechVOAPlus (show AV.act a (k - 1) x ∈ leechVOAPlus.grading 2 by
      convert hmem using 2; ring)]
    rw [WeakModule.act_def, mode_AV, hφ.zero_mode k a ha' x hx]
  · rw [piHom_of_mem_ne leechVOAPlus (show k + 2 - q - 1 ≠ 2 by omega) hmem, map_zero, map_zero,
      LinearMap.zero_apply]
    have hw := mode_mem_weight plusModule (sig_mem_grading ha') (hφ.maps_weight x hx) q
    refine TPForm_weightOrth _ _ ?_ _ hw _ (hφ.maps_weight x' hx')
    intro h
    apply hq
    have : ((k : ℂ) - q - 1) = 0 := by linear_combination h
    have h' : ((k - q - 1 : ℤ) : ℂ) = 0 := by push_cast; exact this
    have := Int.cast_eq_zero.mp h'
    omega

/-- **The residual implies annihilator compatibility for every top vector of `V₃⁺`.** -/
theorem annCompat_V3_of_top {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP} (hφ : TopSigmaV3 s φ) {x₀ : VPlus}
    (hx₀ : x₀ ∈ OmegaV3) : AnnCompat actV actT sig Set.univ x₀ (φ x₀) := by
  obtain ⟨t₀, ht₀, h0, xh, hxh, hφxh⟩ := hφ.hits_cyclic
  rw [annCompat_twist_iff]
  exact annCompat_of_top AV BTs TPForm OmegaV3 φ (piHom leechVOAPlus 2) homLetters
    (hZO_V3 hφ) hadj_BTs (hnd_BTs hφ.maps_frame ht₀ h0 hxh hφxh) hx₀

/-! ### The explicit weight-2 cyclic vector of `V₃⁺` -/

/-- `β₂ = u − w = (−3, 1²³)` (in `√8`-coordinates): an odd Leech vector of norm 4. -/
noncomputable def β₂ : leech.carrier := uβ - frameW

theorem β₂_not_mem : β₂ ∉ lambda0 := by
  intro h
  have hu : uβ ∈ lambda0 := by
    have := lambda0.add_mem h frameW_mem_lambda0
    rwa [β₂, sub_add_cancel] at this
  rw [mem_lambda0, frameChar_uβ] at hu
  exact one_ne_zero hu

theorem form_β₂ : leech.form β₂ β₂ = 4 := by
  rw [TFormLeech.leech_form_eq]
  change ((Leech.uVec - (8 : ℤ) • e0) ⬝ᵥ (Leech.uVec - (8 : ℤ) • e0)) / 8 = 4
  decide +kernel

theorem halfNorm_β₂ : LatGen.halfNorm leech β₂ = 2 := by
  have h2 : 2 * LatGen.halfNorm leech β₂ = leech.form β₂ β₂ := two_halfNorm leech leech_even β₂
  rw [form_β₂] at h2
  omega

theorem frameX0P_β₂_mem : frameX0P β₂ ∈ OmegaV3 :=
  ⟨frameX0_mem_frameSector_one β₂_not_mem, by
    have := frameX0P_mem_grading β₂; rwa [halfNorm_β₂] at this⟩

/-- On the top level, a twisted intertwiner with `Φ x₀ = φ x₀` agrees with `φ`. -/
theorem eqOn_top_V3 {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP} (hφ : TopSigmaV3 s φ) {β : leech.carrier}
    (hβ : β ∉ lambda0) (hx₀ : frameX0P β ∈ OmegaV3) {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ)
    (h : Φ (frameX0P β) = φ (frameX0P β)) : ∀ x ∈ OmegaV3, Φ x = φ x := by
  set x₀ := frameX0P β
  set S : Submodule ℂ VPlus := span ℂ {y | ∃ (k : ℤ) (a : V0Sub.carrier),
    (a : VPlus) ∈ leechVOAPlus.grading k ∧ y = actV a (k - 1) x₀}
  -- `Φ = φ` on `S`
  have hS : ∀ y ∈ S, Φ y = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, a, ha, rfl⟩ := hy
      rw [hΦ a (Set.mem_univ _) (k - 1) x₀ (frameX0_mem_frameSector_one hβ), h,
        hφ.zero_mode k a ha x₀ hx₀]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  -- the weight-2 component of `u₍ₙ₎ x₀` lies in `S`
  have hproj : ∀ (u : V0Sub.carrier) (n : ℤ), piHom leechVOAPlus 2 (actV u n x₀) ∈ S := by
    intro u n
    revert n
    refine V0_induction (p := fun u => ∀ n, piHom leechVOAPlus 2 (actV u n x₀) ∈ S) ?_ ?_ ?_ u
    · intro n; simp [actV]
    · intro a b ha hb n; rw [actV_add_left, map_add]; exact add_mem (ha n) (hb n)
    · intro k a ha n
      have hmem : actV a n x₀ ∈ leechVOAPlus.grading (k + 2 - n - 1) :=
        leechVOAPlus.grading_mode _ ha _ hx₀.2 n
      by_cases hn : n = k - 1
      · subst hn
        rw [piHom_of_mem leechVOAPlus (show actV a (k - 1) x₀ ∈ leechVOAPlus.grading 2 by
          convert hmem using 2; ring)]
        exact subset_span ⟨k, a, ha, rfl⟩
      · rw [piHom_of_mem_ne leechVOAPlus (show k + 2 - n - 1 ≠ 2 by omega) hmem]
        exact zero_mem _
  have key : ∀ y ∈ frameSector 1, piHom leechVOAPlus 2 y ∈ S := by
    intro y hy
    rw [← cyc_V3 hβ] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, -, n, rfl⟩ := hy
      exact hproj u n
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact smul_mem _ c ha
  intro x hx
  have hxS := key x hx.1
  rw [piHom_of_mem leechVOAPlus hx.2] at hxS
  exact hS x hxS

/-- **`σ` on `V₃⁺` from the top-level residual.**  If `TopSigmaV3 s φ`, there is a
`v0Sigma`-twisted `V₀⁺`-intertwiner `Φ : V_Λ⁺ → TP` on `V₃⁺` which equals `φ` on the top level
`(V₃⁺)₂`; in particular `Φ ≠ 0` and `Φ` hits a cyclic vector of `T_s⁺`. -/
theorem sigmaV3T_exists_of_top {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP} (hφ : TopSigmaV3 s φ) :
    ∃ Φ : VPlus →ₗ[ℂ] TP, IsSigmaV3T Φ ∧ (∀ x ∈ OmegaV3, Φ x = φ x) ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, Φ x = x0T t₀ := by
  obtain ⟨Φ, hΦ, h⟩ := (sigmaV3T_exists_iff β₂_not_mem (φ (frameX0P β₂))).mpr
    (annCompat_V3_of_top hφ frameX0P_β₂_mem)
  have heq := eqOn_top_V3 hφ β₂_not_mem frameX0P_β₂_mem hΦ h
  obtain ⟨t₀, ht₀, h0, xh, hxh, hφxh⟩ := hφ.hits_cyclic
  exact ⟨Φ, hΦ, heq, t₀, ht₀, h0, xh, hxh, by rw [heq xh hxh, hφxh]⟩

/-- The `∃ s` form (forced by `golayE_not_determined`). -/
theorem sigmaV3T_exists_of_top' (h : ∃ s φ, TopSigmaV3 s φ) :
    ∃ (s : ZMod 2) (Φ : VPlus →ₗ[ℂ] TP), IsSigmaV3T Φ ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, Φ x = x0T t₀ := by
  obtain ⟨s, φ, hφ⟩ := h
  obtain ⟨Φ, hΦ, -, hc⟩ := sigmaV3T_exists_of_top hφ
  exact ⟨s, Φ, hΦ, hc⟩

/-- Necessity of the zero-mode clause: any twisted intertwiner satisfies it on `V₃⁺`. -/
theorem IsSigmaV3T.zero_mode {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ) (k : ℤ) (a : V0Sub.carrier)
    (x : VPlus) (hx : x ∈ OmegaV3) : Φ (actV a (k - 1) x) = actT (sig a) (k - 1) (Φ x) :=
  hΦ a (Set.mem_univ _) (k - 1) x hx.1

/-! ## §5  `T_{s'}⁺ → T_s⁺` -/

/-- The cyclic vector `h₀(−½)𝟙 ⊗ t₀` has weight 2. -/
theorem x0T_mem_weight (t₀ : TLeechT) : x0T t₀ ∈ plusModule.weight (2 : ℂ) := by
  have hX : (MvPolynomial.X (0, 0) : FockT 24) ∈ gradingT 24 1 := by
    have := MvPolynomial.isWeightedHomogeneous_X ℂ (wT (r := 24)) (0, 0)
    simpa using this
  have hg : frameX0T t₀ ∈ TwistedSector.twGrading 24 leechT 1 :=
    TwistedSector.tmul_mem_twGrading 24 leechT hX t₀
  have hw : frameX0T t₀ ∈ TwistedSector.twWeight 24 leechT ((2 : ℚ)) := by
    have h := TwistedSector.twWeight_levelT 24 leechT 1
    have h1 : levelT 24 1 = (2 : ℚ) := by
      have := TwistedSector.levelT_24_odd 0
      simpa using this
    rw [h1] at h
    rw [h]; exact hg
  have hmem : frameX0T t₀ ∈ (plusModule.weight ((2 : ℚ) : ℂ)).map TP.subtype := by
    rw [map_plusModule_weight]
    exact ⟨TwistedSector.twGrading_le_twFixed (by decide) hg, hw⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = x0T t₀ := Subtype.ext hyx
  rw [← this]
  simpa using hy

/-- The top level `(T_{s'}⁺)₂`. -/
noncomputable def OmegaT (s' : ZMod 2) : Submodule ℂ TP := TPframe s' ⊓ plusModule.weight (2 : ℂ)

/-- The weight-2 projection on `TP`. -/
noncomputable def projT2 : TP →ₗ[ℂ] TP :=
  (plusModule.weight (2 : ℂ)).subtype ∘ₗ internalProjTo plusModule.isInternal (2 : ℂ)

theorem projT2_of_mem {y : TP} (hy : y ∈ plusModule.weight (2 : ℂ)) : projT2 y = y :=
  internalProjTo_coe_mem plusModule hy

theorem projT2_of_mem_ne {α : ℂ} (hα : α ≠ 2) {y : TP} (hy : y ∈ plusModule.weight α) :
    projT2 y = 0 := by
  change ((internalProjTo plusModule.isInternal (2 : ℂ) y : plusModule.weight (2 : ℂ)) : TP) = 0
  rw [internalProjTo_eq_zero_of_ne plusModule hy (Ne.symm hα)]
  rfl

/-- **The named residual for `σ` on `T_{s'}⁺`** (FLM's `T₃⁺ → T₃⁺` for the right `s'`). -/
structure TopSigmaTT (s' s : ZMod 2) (φ : TP →ₗ[ℂ] TP) : Prop where
  /-- `φ` maps the top level of `T_{s'}⁺` into `T_s⁺`. -/
  maps_frame : ∀ x ∈ OmegaT s', φ x ∈ TPframe s
  /-- `φ` maps the top level into weight 2. -/
  maps_weight : ∀ x ∈ OmegaT s', φ x ∈ plusModule.weight (2 : ℂ)
  /-- Zero-mode intertwining for every homogeneous `a ∈ V₀⁺`. -/
  zero_mode : ∀ (k : ℤ) (a : V0Sub.carrier), (a : VPlus) ∈ leechVOAPlus.grading k →
    ∀ x ∈ OmegaT s', φ (actT a (k - 1) x) = actT (sig a) (k - 1) (φ x)
  /-- `φ` hits a cyclic vector of `T_s⁺`. -/
  hits_cyclic : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s', φ x = x0T t₀

theorem cast_ne_two {k q : ℤ} (hq : q ≠ k - 1) : (2 : ℂ) + (k : ℂ) - q - 1 ≠ 2 := by
  intro h
  apply hq
  have h' : ((k - q - 1 : ℤ) : ℂ) = 0 := by push_cast; linear_combination h
  have := Int.cast_eq_zero.mp h'
  omega

theorem hZO_TT {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP} (hφ : TopSigmaTT s' s φ) :
    ∀ (k : ℤ) (a : V0Sub.carrier), a ∈ V0P.grading k → ∀ (q : ℤ), ∀ x ∈ OmegaT s', ∀ x' ∈ OmegaT s',
      TPForm (BTs.act a q (φ x)) (φ x') = TPForm (φ (projT2 (AT.act a q x))) (φ x') := by
  intro k a ha q x hx x' hx'
  have ha' : (a : VPlus) ∈ leechVOAPlus.grading k := ha
  have hmem := mode_mem_weight plusModule ha' hx.2 q
  rw [WeakModule.act_def, mode_BTs]
  by_cases hq : q = k - 1
  · subst hq
    rw [WeakModule.act_def, mode_AT, projT2_of_mem (show actT a (k - 1) x ∈ plusModule.weight (2 : ℂ) by
      convert hmem using 2; push_cast; ring), hφ.zero_mode k a ha' x hx]
  · rw [WeakModule.act_def, mode_AT, projT2_of_mem_ne (cast_ne_two hq) (y := actT a q x) hmem,
      map_zero, map_zero,
      LinearMap.zero_apply]
    have hw := mode_mem_weight plusModule (sig_mem_grading ha') (hφ.maps_weight x hx) q
    exact TPForm_weightOrth _ _ (cast_ne_two hq) _ hw _ (hφ.maps_weight x' hx')

/-- **The residual implies annihilator compatibility for every top vector of `T_{s'}⁺`.** -/
theorem annCompat_TT_of_top {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP} (hφ : TopSigmaTT s' s φ) {x₀ : TP}
    (hx₀ : x₀ ∈ OmegaT s') : AnnCompat actT actT sig Set.univ x₀ (φ x₀) := by
  obtain ⟨t₀, ht₀, h0, xh, hxh, hφxh⟩ := hφ.hits_cyclic
  rw [annCompat_twist_iff]
  exact annCompat_of_top AT BTs TPForm (OmegaT s') φ projT2 homLetters
    (hZO_TT hφ) hadj_BTs (hnd_BTs hφ.maps_frame ht₀ h0 hxh hφxh) hx₀

/-- On the top level, a twisted intertwiner with `Φ x₀ = φ x₀` agrees with `φ`. -/
theorem eqOn_top_TT {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP} (hφ : TopSigmaTT s' s φ) {t₀' : TLeechT}
    (ht₀' : t₀' ∈ leechFrameT s') (h0' : t₀' ≠ 0) {Φ : TP →ₗ[ℂ] TP} (hΦ : IsSigmaTT s' Φ)
    (h : Φ (x0T t₀') = φ (x0T t₀')) : ∀ x ∈ OmegaT s', Φ x = φ x := by
  set x₀ := x0T t₀'
  have hx₀ : x₀ ∈ OmegaT s' := ⟨x0T_mem ht₀', x0T_mem_weight t₀'⟩
  set S : Submodule ℂ TP := span ℂ {y | ∃ (k : ℤ) (a : V0Sub.carrier),
    (a : VPlus) ∈ leechVOAPlus.grading k ∧ y = actT a (k - 1) x₀}
  have hS : ∀ y ∈ S, Φ y = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, a, ha, rfl⟩ := hy
      rw [hΦ a (Set.mem_univ _) (k - 1) x₀ hx₀.1, h, hφ.zero_mode k a ha x₀ hx₀]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  have hproj : ∀ (u : V0Sub.carrier) (n : ℤ), projT2 (actT u n x₀) ∈ S := by
    intro u n
    revert n
    refine V0_induction (p := fun u => ∀ n, projT2 (actT u n x₀) ∈ S) ?_ ?_ ?_ u
    · intro n; simp [actT]
    · intro a b ha hb n; rw [actT_add_left, map_add]; exact add_mem (ha n) (hb n)
    · intro k a ha n
      have hmem := mode_mem_weight plusModule ha hx₀.2 n
      by_cases hn : n = k - 1
      · subst hn
        rw [projT2_of_mem (show actT a (k - 1) x₀ ∈ plusModule.weight (2 : ℂ) by
          convert hmem using 2; push_cast; ring)]
        exact subset_span ⟨k, a, ha, rfl⟩
      · rw [projT2_of_mem_ne (cast_ne_two hn) (y := actT a n x₀) hmem]
        exact zero_mem _
  have key : ∀ y ∈ TPframe s', projT2 y ∈ S := by
    intro y hy
    rw [← cyc_T ht₀' h0'] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, -, n, rfl⟩ := hy
      exact hproj u n
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact smul_mem _ c ha
  intro x hx
  have hxS := key x hx.1
  rw [projT2_of_mem hx.2] at hxS
  exact hS x hxS

/-- **`σ` on `T_{s'}⁺` from the top-level residual.** -/
theorem sigmaTT_exists_of_top {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP} (hφ : TopSigmaTT s' s φ)
    {t₀' : TLeechT} (ht₀' : t₀' ∈ leechFrameT s') (h0' : t₀' ≠ 0) :
    ∃ Φ : TP →ₗ[ℂ] TP, IsSigmaTT s' Φ ∧ (∀ x ∈ OmegaT s', Φ x = φ x) ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s', Φ x = x0T t₀ := by
  have hx₀ : x0T t₀' ∈ OmegaT s' := ⟨x0T_mem ht₀', x0T_mem_weight t₀'⟩
  obtain ⟨Φ, hΦ, h⟩ := (sigmaTT_exists_iff ht₀' h0' (φ (x0T t₀'))).mpr
    (annCompat_TT_of_top hφ hx₀)
  have heq := eqOn_top_TT hφ ht₀' h0' hΦ h
  obtain ⟨t₀, ht₀, h0, xh, hxh, hφxh⟩ := hφ.hits_cyclic
  exact ⟨Φ, hΦ, heq, t₀, ht₀, h0, xh, hxh, by rw [heq xh hxh, hφxh]⟩

/-- Necessity of the zero-mode clause on `T_{s'}⁺`. -/
theorem IsSigmaTT.zero_mode {s' : ZMod 2} {Φ : TP →ₗ[ℂ] TP} (hΦ : IsSigmaTT s' Φ) (k : ℤ)
    (a : V0Sub.carrier) (x : TP) (hx : x ∈ OmegaT s') :
    Φ (actT a (k - 1) x) = actT (sig a) (k - 1) (Φ x) :=
  hΦ a (Set.mem_univ _) (k - 1) x hx.1

end VOA.Moonshine.SigmaExist
