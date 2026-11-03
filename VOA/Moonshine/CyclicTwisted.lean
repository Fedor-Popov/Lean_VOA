/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.CyclicTwistedSpan
import VOA.Moonshine.CyclicTwistedFrame
import VOA.Moonshine.TwistedPlus
import VOA.Moonshine.CyclicFrameSectors

/-!
# The twisted frame sectors are cyclic `V₀⁺`-modules  (Moonshine step M8f, twisted half)

On `TP = (V_Λ^T)^+` (`Moonshine.plusModule`, an ordinary `V_Λ⁺`-module) the frame involution
`id ⊗ J` (`J = c⁻¹ e_w`, `w = 8e₀`, `FrameTwisted.lean`) splits

  `TP = T₀⁺ ⊕ T₃⁺`,  `T_s⁺ := TP ∩ (S[θ] ⊗ T_s)`  (`TPframe s`, `T_s = ker(J − (−1)^s)`).

We prove that **each `T_s⁺` is a cyclic `V₀⁺`-module** (`V₀⁺ = frameSector 0`):

  `cyclic_TPframe s : ∃ x₀ ∈ T_s⁺, span {u₍ₙ₎ x₀ | u ∈ V₀⁺, n ∈ ℤ} = T_s⁺`,

with the explicit cyclic vector `x₀ = h₀(−½)𝟙_T ⊗ t₀` (any `0 ≠ t₀ ∈ T_s`; weight `2`).

## Why not the vacuum trick

`cyclic_V3` (`CyclicFrameSectors.lean`) used `mem_span_iterate_of_vacuum`: one Borcherds identity
for a triple `(v, x₀, x₀)` with `x₀₍ₖ₎x₀ = c·𝟙`.  For `TP` the "pairing to the vacuum" is
`W̄(a)₍ₖ₎b = c·𝟙` (`a, b ∈ TP`, `leechWbar`), and writing `t = W(t)₍₋₁₎𝟙 = c⁻¹W(t)₍₋₁₎W̄(a)₍ₖ₎b`
as a combination of `Y_TP(W̄(t)₍ᵢ₎a)₍ⱼ₎ b` (with `W̄(t)₍ᵢ₎a ∈ V_Λ⁺`) is the Borcherds identity
of `V♮` for the triple `(t, a, b) ∈ TP³`:

  `Σ_i (−1)ⁱC(ℓ,i)[W(t)₍ℓ₊ₘ₋ᵢ₎W̄(a)₍ₙ₊ᵢ₎b − (−1)^ℓ W(a)₍ℓ₊ₙ₋ᵢ₎W̄(t)₍ₘ₊ᵢ₎b]`
  `  = Σ_i C(m,i) Y_TP(W̄(t)₍ℓ₊ᵢ₎a)₍ₘ₊ₙ₋ᵢ₎ b`.

This is the twisted × twisted relation (DGM (4.23); `htt` of `reconstruct_nat`), i.e. step
**M8h** (open on this route).  The available `wMode_comm`, `WbarMode_comm`, `leechWbar_comm'` are commutator
formulas with one *untwisted* argument and do not imply it.  So the vacuum-trick route for
`T_s⁺` would need M8h; we use an explicit route instead.

## The explicit route (no twisted × twisted input)

Let `A = V_Λ^{⟨g⟩}` (`frameFix`: all momenta in `Λ₀`; `g = frameAut`).  Work in the **full**
twisted `V_Λ`-module `S[θ] ⊗ T` (`leechTwistedModule`), where odd states are available.

1. `Z_A(x) = span{u₍k/2₎x | u ∈ A}` is `A`-stable (`TwistedCyclic.YM_mem_orbitSpan`, by the
   twisted Jacobi identity).
2. `h_b(−1)𝟙 ∈ A` acts by `h_b(k/2) ⊗ 1` (`leechTwistedModule_hgen`), so
   `h₀(½)x₀ = ½(1 ⊗ t₀) ∈ Z_A(x₀)`; by `span_creationWordT_vacT`, `S[θ] ⊗ t ⊆ Z_A(x₀)` whenever
   `1 ⊗ t ∈ Z_A(x₀)` (`tmul_mem_orbitSpan`).
3. `e^α ∈ A` for `α ∈ Λ₀`, and `Y^T(e^α)₍(|α|²−2)/2₎(1 ⊗ t₀) = 2^{−|α|²}(1 ⊗ e_α t₀)`
   (`leechTwistedModule_echg_vac`).
4. `T_s = span{e_α t₀ | α ∈ Λ₀}` (`mem_span_eT_lambda0`): `T` is a simple module over the
   twisted group algebra spanned by the `e_α` (`isSimpleModule_extraT`, `span_eA`), so the
   `e_α t₀` (`α ∈ Λ`) span `T`; those with `α ∉ Λ₀` land in `T_{s+1}` (`eT_mem_leechFrameT`).
5. Hence `S[θ] ⊗ T_s ⊆ Z_A(x₀)` (`twFrame_le_orbitSpan`), and projecting with `½(1 + θ_tw)`
   (`TwistedCyclic.mem_span_plus_of_mem_orbitSpan`) leaves exactly the modes of
   `V^θ ∩ A = V₀⁺` on `x₀`.
6. Conversely `V₀⁺`-modes commute with `id ⊗ J` (`leechTwistedModule_YM_frameAut`), so the span
   stays in `T_s⁺` (`YM_mem_twFrame`).

## Main results
* `frameFix`, `TPframe`, `TPframe_isCompl` (`TP = T₀⁺ ⊕ T₁⁺`), `frameX0T`, `frameX0T_mem_TP`,
  `frameX0T_mem_twFrame`.
* `YM_mem_twFrame`, `tmul_mem_orbitSpan`, `mem_span_eT_lambda0`, `twFrame_le_orbitSpan`.
* `span_smul_frameX0T`, `cyclic_TPframe`.

## Status
`sorry`-free; `#print axioms cyclic_TPframe = [propext, Classical.choice, Quot.sound]`.
Unconditional.  **Not done:** irreducibility of `T_s⁺` (every nonzero vector cyclic) — the
route above needs a vector with an `h(½)`-descendant of the form `1 ⊗ t`; a general nonzero
vector would need a Fock-space lowering argument (or the invariant form `TPForm`).  Which of
`T₀⁺`/`T₁⁺` is FLM's `T₀⁺` is a convention question of step M8g.  Imported by the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open LatticeTwisted TwistedHeisenberg IntegralLattice LatGen Extraspecial FrameT TwistedCyclic
  MvPolynomial
open Module (End)
open scoped TensorProduct

/-! ## §1  The subalgebra `A = V_Λ^{⟨g⟩}` -/

/-- `A = V_Λ^{⟨g⟩}`, `g = frameAut`: the states all of whose momenta lie in `Λ₀`. -/
noncomputable abbrev frameFix : Submodule ℂ (LatModuleGen leech) :=
  (orbifold (Subgroup.zpowers frameAut)).carrier

theorem mem_frameFix {u : LatModuleGen leech} : u ∈ frameFix ↔ frameAut u = u :=
  VOA.mem_orbifold_zpowers_iff frameAut u

theorem frameFix_smul : ∀ u ∈ frameFix, ∀ n : ℤ, ∀ v ∈ frameFix, leechVOA.smul u n v ∈ frameFix :=
  (orbifold (Subgroup.zpowers frameAut)).smul_mem

theorem frameFix_vacuum : leechVOA.vacuum ∈ frameFix :=
  (orbifold (Subgroup.zpowers frameAut)).vacuum_mem

theorem frameFix_theta {u : LatModuleGen leech} (hu : u ∈ frameFix) : leechTheta u ∈ frameFix := by
  rw [mem_frameFix] at hu ⊢
  have h := congrArg (fun g : Aut leechVOA => g u) frameAut_comm_leechTheta
  simp only [Aut.mul_apply] at h
  rw [h, hu]

theorem leechTheta_leechTheta (u : LatModuleGen leech) : leechTheta (leechTheta u) = u := by
  have h := congrArg (fun g : Aut leechVOA => g u) leechTheta_sq
  simpa using h

theorem echg_mem_frameFix {α : leech.carrier} (hα : α ∈ lambda0) : echg leech α ∈ frameFix := by
  rw [mem_frameFix, frameAut_apply, echg_eq, chiLat_tmul,
    chiSign_of_eq_zero _ _ ((mem_lambda0 α).mp hα), one_smul]

/-- Abbreviation for the orbit span inside the Leech twisted module. -/
noncomputable abbrev frameZA (x : Tw) : Submodule ℂ Tw := orbitSpan leechTwistedModule frameFix x

theorem YM_mem_ZA {u : LatModuleGen leech} (hu : u ∈ frameFix) (k : ℤ) {x y : Tw}
    (hy : y ∈ frameZA x) : leechTwistedModule.YM u k y ∈ frameZA x :=
  YM_mem_orbitSpan leechTwistedModule frameFix frameFix_smul (fun _ hu => frameFix_theta hu)
    leechTheta_leechTheta hu k hy

/-! ## §2  The frame split of `TP` -/

/-- The `T`-factor of the Leech twisted sector. -/
abbrev TLeechT : Type := Rep (cocMat leech) (isUnit_det_cocMat leech leech_even leech_isUnit_det_gramMat)

/-- The frame involution `J` on `T`. -/
noncomputable abbrev frameJL : End ℂ TLeechT := frameJ leech leech_even leech_isUnit_det_gramMat frameW

/-- The frame eigenspaces of the twisted carrier, `S[θ] ⊗ T_s`. -/
noncomputable abbrev twFrameL (s : ZMod 2) : Submodule ℂ Tw :=
  twFrame leech leech_even leech_isUnit_det_gramMat (FockT 24) frameW s

theorem mem_twFrameL {s : ZMod 2} {x : Tw} :
    x ∈ twFrameL s ↔ frameJL.lTensor (FockT 24) x = Extraspecial.sgn s • x :=
  Module.End.mem_eigenspace_iff

/-- **The twisted frame sectors** `T_s⁺ = TP ∩ (S[θ] ⊗ T_s)` (`s = 0, 1`). -/
noncomputable def TPframe (s : ZMod 2) : Submodule ℂ TP := (twFrameL s).comap TP.subtype

theorem mem_TPframe {s : ZMod 2} {x : TP} : x ∈ TPframe s ↔ (x : Tw) ∈ twFrameL s := Iff.rfl

/-- `TP = T₀⁺ ⊕ T₁⁺`. -/
theorem TPframe_isCompl : IsCompl (TPframe 0) (TPframe 1) := by
  have hJ : ∀ x : Tw, frameJL.lTensor (FockT 24) (frameJL.lTensor (FockT 24) x) = x :=
    lTensor_lTensor_of_sq (frameJ_mul_self _ _ _ _)
  have hθ : ∀ x : Tw, thetaTwLeech (frameJL.lTensor (FockT 24) x) = frameJL.lTensor (FockT 24) (thetaTwLeech x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul p t => simp [TwistedSector.twTheta_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  constructor
  · rw [Submodule.disjoint_def]
    intro x h0 h1
    rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_zero, one_smul] at h0
    rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_one, neg_one_smul, h0] at h1
    apply Subtype.ext
    have : (2 : ℂ) • (x : Tw) = 0 := by rw [two_smul]; nth_rewrite 1 [h1]; abel
    simpa using this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : thetaTwLeech (x : Tw) = x := (TwistedPlus.mem_plusSub leechThetaLift).mp x.2
    set a : Tw := (1 / 2 : ℂ) • ((x : Tw) + frameJL.lTensor (FockT 24) x)
    set b : Tw := (1 / 2 : ℂ) • ((x : Tw) - frameJL.lTensor (FockT 24) x)
    have ha : a ∈ TP := by
      rw [TwistedPlus.mem_plusSub]
      change thetaTwLeech a = a
      simp only [a, map_smul, map_add, hθ, hx]
    have hb : b ∈ TP := by
      rw [TwistedPlus.mem_plusSub]
      change thetaTwLeech b = b
      simp only [b, map_smul, map_sub, hθ, hx]
    have ha0 : (⟨a, ha⟩ : TP) ∈ TPframe 0 := by
      rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_zero, one_smul]
      simp only [a, map_smul, map_add, hJ, add_comm]
    have hb1 : (⟨b, hb⟩ : TP) ∈ TPframe 1 := by
      rw [mem_TPframe, mem_twFrameL, Extraspecial.sgn_one, neg_one_smul]
      simp only [b, map_smul, map_sub, hJ, ← smul_neg, neg_sub]
    have hsum : x = ⟨a, ha⟩ + ⟨b, hb⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, a, b, ← smul_add]
      rw [show (x : Tw) + frameJL.lTensor (FockT 24) x + ((x : Tw) - frameJL.lTensor (FockT 24) x)
          = (2 : ℂ) • (x : Tw) by rw [two_smul]; abel, smul_smul]
      norm_num
    rw [hsum]
    exact Submodule.add_mem_sup ha0 hb1

/-- The modes of `g`-fixed states preserve `S[θ] ⊗ T_s`. -/
theorem YM_mem_twFrame {u : LatModuleGen leech} (hu : frameAut u = u) (k : ℤ) {s : ZMod 2}
    {x : Tw} (hx : x ∈ twFrameL s) : leechTwistedModule.YM u k x ∈ twFrameL s := by
  have hJ : ∀ y : Tw, frameJL.lTensor (FockT 24) (frameJL.lTensor (FockT 24) y) = y :=
    lTensor_lTensor_of_sq (frameJ_mul_self _ _ _ _)
  have h := leechTwistedModule_YM_frameAut u k
  rw [hu] at h
  rw [mem_twFrameL] at hx ⊢
  conv_lhs => rw [h]
  simp only [LinearMap.comp_apply, hJ, hx, map_smul]

/-! ## §3  Generation inside the full twisted module -/

/-- If `1 ⊗ t ∈ Z_A(x)` then `y ⊗ t ∈ Z_A(x)` for every `y ∈ S[θ]`. -/
theorem tmul_mem_orbitSpan {t : TLeechT} {x : Tw} (h : vacT 24 ⊗ₜ t ∈ frameZA x) (y : FockT 24) :
    y ⊗ₜ t ∈ frameZA x := by
  have hw : ∀ l : List (ℕ × Fin 24), creationWordT 24 l (vacT 24) ⊗ₜ t ∈ frameZA x := by
    intro l
    induction l with
    | nil => simpa [creationWordT] using h
    | cons v l ih =>
        obtain ⟨u, hu, hk⟩ := leechTwistedModule_hgen v.2
        have h1 := YM_mem_ZA (mem_frameFix.mpr hu) (-(2 * (v.1 : ℤ) + 1)) ih
        rw [hk, LinearMap.rTensor_tmul] at h1
        simpa only [creationWordT, List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
  have hy : y ∈ Submodule.span ℂ (Set.range fun l => creationWordT 24 l (vacT 24)) := by
    rw [span_creationWordT_vacT]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨l, rfl⟩ := hz; exact hw l
  | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ _ ha

theorem disjoint_leechFrameT (s : ZMod 2) : Disjoint (leechFrameT s) (leechFrameT (s + 1)) := by
  fin_cases s
  · exact leechFrameT_isCompl.disjoint
  · exact leechFrameT_isCompl.disjoint.symm

theorem frameChar_eq_one {α : leech.carrier} (hα : α ∉ lambda0) : frameChar α = 1 := by
  rw [mem_lambda0] at hα
  generalize frameChar α = z at hα ⊢
  fin_cases z
  · exact absurd rfl hα
  · rfl

/-- **`T_s = span{e_α t₀ | α ∈ Λ₀}`** for any `0 ≠ t₀ ∈ T_s`. -/
theorem mem_span_eT_lambda0 {s : ZMod 2} {t₀ t : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0)
    (ht : t ∈ leechFrameT s) :
    t ∈ Submodule.span ℂ {y | ∃ α ∈ lambda0, y = eT leech leech_even leech_isUnit_det_gramMat α t₀} := by
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective (alg (cocMat leech)) h0 t
  rw [LinearMap.toSpanSingleton_apply] at ha
  let f : alg (cocMat leech) →ₗ[ℂ] TLeechT :=
    { toFun := fun a => a • t₀
      map_add' := fun a b => add_smul a b t₀
      map_smul' := fun c a => smul_assoc c a t₀ }
  have hmem : t ∈ Submodule.span ℂ
      (Set.range fun α => eT leech leech_even leech_isUnit_det_gramMat α t₀) := by
    have h1 : a ∈ Submodule.span ℂ (Set.range (eA leech)) := by
      rw [span_eA]; exact Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := f) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    rw [← ha]
    exact h2
  set S0 : Set TLeechT := {y | ∃ α ∈ lambda0, y = eT leech leech_even leech_isUnit_det_gramMat α t₀}
  set S1 : Set TLeechT := {y | ∃ α ∉ lambda0, y = eT leech leech_even leech_isUnit_det_gramMat α t₀}
  have hsub : Set.range (fun α => eT leech leech_even leech_isUnit_det_gramMat α t₀) ⊆ S0 ∪ S1 := by
    rintro _ ⟨α, rfl⟩
    by_cases hα : α ∈ lambda0
    · exact Or.inl ⟨α, hα, rfl⟩
    · exact Or.inr ⟨α, hα, rfl⟩
  have hmem' := Submodule.span_mono hsub hmem
  rw [Submodule.span_union, Submodule.mem_sup] at hmem'
  obtain ⟨y0, hy0, y1, hy1, hy⟩ := hmem'
  have h0le : Submodule.span ℂ S0 ≤ leechFrameT s := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    have := eT_mem_leechFrameT α ht₀
    rwa [(mem_lambda0 α).mp hα, add_zero] at this
  have h1le : Submodule.span ℂ S1 ≤ leechFrameT (s + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, hα, rfl⟩
    have := eT_mem_leechFrameT α ht₀
    rwa [frameChar_eq_one hα] at this
  have hy1s : y1 ∈ leechFrameT s := by
    have : y1 = t - y0 := by rw [← hy]; abel
    rw [this]
    exact Submodule.sub_mem _ ht (h0le hy0)
  have hy1z : y1 = 0 :=
    (Submodule.disjoint_def.mp (disjoint_leechFrameT s)) y1 hy1s (h1le hy1)
  rw [← hy, hy1z, add_zero]
  exact hy0

/-! ## §4  The cyclic vector -/

/-- The cyclic vector `h₀(−½)𝟙 ⊗ t₀` (weight `2`). -/
noncomputable def frameX0T (t₀ : TLeechT) : Tw := (X (0, 0) : FockT 24) ⊗ₜ t₀

theorem frameX0T_mem_TP (t₀ : TLeechT) : frameX0T t₀ ∈ TP := by
  rw [TwistedPlus.mem_plusSub]
  change TwistedSector.twTheta 24 leechT (frameX0T t₀) = frameX0T t₀
  rw [frameX0T, TwistedSector.twTheta_tmul, thetaT_X, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, neg_neg]

theorem frameX0T_mem_twFrame {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) :
    frameX0T t₀ ∈ twFrameL s := by
  rw [mem_twFrameL, frameX0T, LinearMap.lTensor_tmul, (mem_frameT _ _ _).mp ht₀,
    TensorProduct.tmul_smul]

/-- **`S[θ] ⊗ T_s ⊆ Z_A(x₀)`.** -/
theorem twFrame_le_orbitSpan {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0) :
    twFrameL s ≤ frameZA (frameX0T t₀) := by
  set Z := frameZA (frameX0T t₀)
  -- `1 ⊗ t₀ ∈ Z`, via `h₀(½)`.
  have hvac : vacT 24 ⊗ₜ t₀ ∈ Z := by
    obtain ⟨u, hu, hk⟩ := leechTwistedModule_hgen 0
    have h1 := YM_mem_orbitSpan_of_mem (T := leechTwistedModule) (A := frameFix)
      (mem_frameFix.mpr hu) 1 (frameX0T t₀)
    rw [hk, frameX0T, LinearMap.rTensor_tmul] at h1
    have hm := modeT_annihilation 24 0 0 (X (0, 0))
    rw [show (2 * ((0 : ℕ) : ℤ) + 1) = 1 by norm_num, pderiv_X_self] at hm
    rw [hm] at h1
    have h2 := Submodule.smul_mem Z (2 : ℂ) h1
    rw [← TensorProduct.smul_tmul', smul_smul] at h2
    convert h2 using 2
    norm_num [vacT]
  -- `1 ⊗ e_α t₀ ∈ Z` for `α ∈ Λ₀`.
  have hα : ∀ α ∈ lambda0,
      vacT 24 ⊗ₜ eT leech leech_even leech_isUnit_det_gramMat α t₀ ∈ Z := by
    intro α hα
    have h1 := YM_mem_ZA (echg_mem_frameFix hα) (leech.form α α - 2) hvac
    rw [leechTwistedModule_echg_vac] at h1
    have h2 := Submodule.smul_mem Z (((2 : ℂ) ^ (-(leech.form α α)))⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero), one_smul] at h2
  -- `1 ⊗ t ∈ Z` for `t ∈ T_s`.
  have ht : ∀ t ∈ leechFrameT s, vacT 24 ⊗ₜ t ∈ Z := by
    intro t ht
    have hsp := mem_span_eT_lambda0 ht₀ h0 ht
    clear ht
    induction hsp using Submodule.span_induction with
    | mem z hz => obtain ⟨α, hα', rfl⟩ := hz; exact hα α hα'
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ _ ha
  -- The projection `½(1 + (−1)^s J)` onto `T_s`.
  set Ps : End ℂ TLeechT := (1 / 2 : ℂ) • (1 + Extraspecial.sgn s • frameJL)
  have hPs : ∀ t : TLeechT, Ps t ∈ leechFrameT s := by
    intro t
    rw [mem_frameT]
    have hJJ : frameJL (frameJL t) = t := frameJ_frameJ _ _ _ _ t
    have hss : Extraspecial.sgn s * Extraspecial.sgn s = 1 := Extraspecial.sgn_mul_self s
    simp only [Ps, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, map_smul,
      map_add, hJJ, smul_add, smul_smul]
    rw [add_comm]; ring_nf
    rw [show Extraspecial.sgn s ^ 2 = 1 by rw [sq, hss], one_mul]
  have hall : ∀ x : Tw, Ps.lTensor (FockT 24) x ∈ Z := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul y t =>
        rw [LinearMap.lTensor_tmul]
        exact tmul_mem_orbitSpan (ht _ (hPs t)) y
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  intro x hx
  have hxx : Ps.lTensor (FockT 24) x = x := by
    rw [mem_twFrameL] at hx
    have hss : Extraspecial.sgn s * Extraspecial.sgn s = 1 := Extraspecial.sgn_mul_self s
    simp only [Ps, LinearMap.lTensor_smul, LinearMap.lTensor_add, LinearMap.smul_apply,
      LinearMap.add_apply, Module.End.one_eq_id, LinearMap.lTensor_id, LinearMap.id_apply, hx,
      smul_smul, hss, one_smul]
    rw [← two_smul ℂ x, smul_smul]; norm_num
  rw [← hxx]
  exact hall x

/-- `T_s ≠ 0`. -/
theorem exists_ne_zero_leechFrameT (s : ZMod 2) : ∃ t₀ ∈ leechFrameT s, t₀ ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro h
  have hdim : Module.finrank ℂ (leechFrameT s) = 2048 := by
    fin_cases s
    · exact finrank_leechFrameT_plus
    · exact finrank_leechFrameT_minus
  rw [h, finrank_bot] at hdim
  norm_num at hdim

/-- **The explicit form**: for `0 ≠ t₀ ∈ T_s`, `x₀ = h₀(−½)𝟙 ⊗ t₀` generates `T_s⁺` over `V₀⁺`. -/
theorem span_smul_frameX0T {s : ZMod 2} {t₀ : TLeechT} (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0) :
    Submodule.span ℂ {y | ∃ u ∈ frameSector 0, ∃ n : ℤ,
        y = mode (Moonshine.plusModule.YM u) n (⟨frameX0T t₀, frameX0T_mem_TP t₀⟩ : TP)}
      = TPframe s := by
  set x₀ : TP := ⟨frameX0T t₀, frameX0T_mem_TP t₀⟩
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨u, hu, n, rfl⟩
    rw [SetLike.mem_coe, mem_TPframe, mode_plusModule]
    have hfix : frameAut (u : LatModuleGen leech) = u := by
      rw [frameAut_apply, (mem_frameSector.mp hu), Extraspecial.sgn_zero, one_smul]
    exact YM_mem_twFrame hfix _ (frameX0T_mem_twFrame ht₀)
  · intro y hy
    have hZ : (y : Tw) ∈ frameZA (x₀ : Tw) := twFrame_le_orbitSpan ht₀ h0 hy
    have h := mem_span_plus_of_mem_orbitSpan leechTwistedModule frameFix
      (fun _ hu => frameFix_theta hu) leechTheta_leechTheta leechThetaLift x₀ y hZ
    refine Submodule.span_mono ?_ h
    rintro z ⟨u, hu, n, rfl⟩
    refine ⟨u, ?_, n, rfl⟩
    rw [mem_frameSector, Extraspecial.sgn_zero, one_smul, ← frameAut_apply]
    exact mem_frameFix.mp hu

/-- **M8f, twisted half: each twisted frame sector `T_s⁺` is a cyclic `V₀⁺`-module.** -/
theorem cyclic_TPframe (s : ZMod 2) : ∃ x₀ ∈ TPframe s,
    Submodule.span ℂ {y | ∃ u ∈ frameSector 0, ∃ n : ℤ, y = mode (Moonshine.plusModule.YM u) n x₀}
      = TPframe s := by
  obtain ⟨t₀, ht₀, h0⟩ := exists_ne_zero_leechFrameT s
  exact ⟨⟨frameX0T t₀, frameX0T_mem_TP t₀⟩, frameX0T_mem_twFrame ht₀, span_smul_frameX0T ht₀ h0⟩

end VOA.Moonshine
