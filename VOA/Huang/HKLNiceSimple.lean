/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtCFT
import VOA.Huang.LogRemovalBound
import VOA.Modules.OrdSubmodule
import VOA.Modules.StronglyRational

/-!
# HKL niceness, part 1: the extension of a Frobenius algebra is simple and self-dual

For the extension `W = extVOA F μ η …` of an algebra object `A` in `Ordinary V`:

* `extVOA_isSimple` — **`W` is simple** when `A` is haploid and the pairing `μ ≫ q` has trivial
  right kernel (`ker_trivial_of_isFrobeniusCounit`, the KO rigidity condition).  An ideal `I` is an
  ordinary `V`-submodule of `A` (`OrdVModule.submodule`); if `q` vanishes on `I`, the inclusion
  `I ↪ A` lies in the right kernel of `μ ≫ q`, hence is zero; otherwise `q(I)` is a nonzero ideal
  of the simple `V`, so the weight-`0` part of `I` meets `A₀ = ℂ η(𝟙)` nontrivially and `I ∋ η(𝟙)`.
  The Frobenius hypothesis is necessary (square-zero extensions).
* `L_one_weight_one` — for nice `V`, **`L₁ = 0` on the weight-one space of every ordinary
  module** (complete reducibility + pseudo-unitarity + `L₁V₁ = 0`); hence `L₁W₁ = 0`
  (`extVOA_L_one`).
* `extVOA_selfDual` — **`W` is self-dual** (Li/Dong–Mason: simple + `L₁W₁ = 0`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLNice

open CategoryTheory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt
  VOA.Huang.LogRemovalBound VOA.Huang.TensorCat.RepPackaging

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- The weight projection kills the other weight spaces. -/
theorem weightProj_of_ne {M : Type u} [AddCommGroup M] [Module ℂ M] (Am : OrdVModule V M)
    {h α : ℂ} (hα : α ≠ h) {x : M} (hx : x ∈ Am.weight α) : weightProj Am h x = 0 := by
  have hx' : x ∈ weightCompl Am h := (le_iSup₂_of_le α hα le_rfl : Am.weight α ≤ _) hx
  have := Submodule.projectionOnto_apply_right (isCompl_weightCompl Am h) ⟨x, hx'⟩
  rw [weightProj, show x = ((⟨x, hx'⟩ : weightCompl Am h) : M) from rfl, this]

/-! ## `L₁ = 0` on weight one -/

/-- For nice `V`, `L₁` vanishes on the weight-one space of every ordinary module. -/
theorem L_one_weight_one (hV : Nice V) (A : Ordinary V) {x : A.carrier}
    (hx : x ∈ A.isMod.weight 1) : mode (A.isMod.YM V.conformalVector) 2 x = 0 := by
  classical
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hV.1 A
  let g : Fin n → Ordinary V := fun j => Ordinary.of (R j).isMod
  have hcomm : ∀ {X Y : Ordinary V} (φ : X ⟶ Y) (y : X.carrier),
      φ.val (mode (X.isMod.YM V.conformalVector) 2 y) =
        mode (Y.isMod.YM V.conformalVector) 2 (φ.val y) := fun φ y => φ.property _ 2 y
  have hω : V.conformalVector ∈ V.grading 2 := V.conformal_mem
  -- each component is killed
  have hcomp : ∀ j (y : (g j).carrier), y ∈ (g j).isMod.weight 1 →
      mode ((g j).isMod.YM V.conformalVector) 2 y = 0 := by
    intro j y hy
    by_cases hj : Nonempty (vacuumObject ≅ g j)
    · obtain ⟨s⟩ := hj
      have hz : s.inv.val y ∈ (adjointModule V).weight 1 :=
        hom_mem_weight (A₂ := (g j).isMod) (A₃ := adjointModule V) s.inv.property hy
      have hz1 : s.inv.val y ∈ V.grading 1 := by
        have : (adjointModule V).weight ((1 : ℤ) : ℂ) = V.grading 1 := adjWeight_cast V 1
        rw [← this]; simpa using hz
      have hL : mode ((vacuumObject (W := V)).isMod.YM V.conformalVector) 2 (s.inv.val y) = 0 :=
        hV.1.L_one_grading_one_eq_zero hz1
      have : y = s.hom.val (s.inv.val y) := by
        rw [← Ordinary.comp_apply, s.inv_hom_id, Ordinary.id_apply]
      rw [this, ← hcomm, hL, map_zero]
    · have hpos : ∀ α : ℂ, (g j).isMod.weight α ≠ ⊥ → 0 < α.re := by
        refine hV.2 (R j).carrier (R j).isMod (hR j) ⟨fun me => hj ?_⟩
        exact ⟨(Ordinary.isoOfModuleEquiv (X := g j) (Y := vacuumObject) me).symm⟩
      have hmem := mode_mem_weight (g j).isMod hω hy 2
      have hbot : (g j).isMod.weight ((1 : ℂ) + ((2 : ℤ) : ℂ) - ((2 : ℤ) : ℂ) - 1) = ⊥ := by
        by_contra hne
        have := hpos _ hne
        norm_num at this
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
  -- reassemble
  have hx' : x = e.inv.val (e.hom.val x) := by
    rw [← Ordinary.comp_apply, e.hom_inv_id, Ordinary.id_apply]
  have htot : e.hom.val x = ∑ j, (biproduct.ι g j).val ((biproduct.π g j).val (e.hom.val x)) := by
    have h := congrArg (fun φ : (⨁ g) ⟶ (⨁ g) => φ.val (e.hom.val x)) (biproduct.total (f := g))
    simp only [Ordinary.sum_val, Ordinary.comp_apply, Ordinary.id_apply] at h
    exact h.symm
  rw [hx', ← hcomm, htot, map_sum]
  have : ∀ j, mode ((⨁ g).isMod.YM V.conformalVector) 2
      ((biproduct.ι g j).val ((biproduct.π g j).val (e.hom.val x))) = 0 := by
    intro j
    rw [← hcomm, hcomp j _ (hom_mem_weight (A₂ := (⨁ g).isMod) (A₃ := (g j).isMod)
      (biproduct.π g j).property (hom_mem_weight (A₂ := A.isMod) (A₃ := (⨁ g).isMod)
        e.hom.property hx)), map_zero]
  rw [Finset.sum_eq_zero fun j _ => this j, map_zero]

/-! ## Simplicity -/

variable {F : FusionChoice V} {A : Ordinary V} {m : tensorObj F A A ⟶ A}
  {η : vacuumObject ⟶ A}
  {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

/-- An ideal of the extension, as a weak `V`-submodule of `A`. -/
def idealSub (I : Submodule ℂ A.carrier)
    (hI : (extVOA F m η hl hr htw hloc hvac hpos).IsIdeal I) :
    WeakModule.Submodule' A.isMod.toWeakModule where
  carrier := I
  act_mem u n x hx := by
    have h := hI (η.val u) x n hx
    rw [extVOA_smul, ext_unit_left_int F m η hl] at h
    exact h

/-- The extension modes of an ideal stay in the ideal (all complex modes). -/
theorem ext_mem_ideal (I : Submodule ℂ A.carrier)
    (hI : (extVOA F m η hl hr htw hloc hvac hpos).IsIdeal I) (n : ℂ) (a : A.carrier)
    {x : A.carrier} (hx : x ∈ I) : (extIntertwiner F m).val n a x ∈ I := by
  by_cases hn : ∃ k : ℤ, (k : ℂ) = n
  · obtain ⟨k, rfl⟩ := hn
    have h := hI a x k hx
    rwa [extVOA_smul] at h
  · push Not at hn
    rw [ext_eq_zero_of_not_int F m htw hn]
    exact I.zero_mem

/-- **The extension of a haploid algebra whose pairing `μ ≫ q` has trivial right kernel is
simple.** -/
theorem extVOA_isSimple (hV : Nice V) (hhap : finrank ℂ (vacuumObject ⟶ A) = 1)
    (q : A ⟶ vacuumObject)
    (hker : ∀ (X : Ordinary V) (f : X ⟶ A), tensorHom F (𝟙 A) f ≫ m ≫ q = 0 → f = 0) :
    (extVOA F m η hl hr htw hloc hvac hpos).IsSimple := by
  set W := extVOA F m η hl hr htw hloc hvac hpos with hW
  have hinj := eta_injective (m := m) hV hl hhap
  have hvne : η.val V.vacuum ≠ 0 := fun h0 =>
    hV.1.toStronglyFinite.vacuum_ne_zero (hinj (h0.trans (map_zero η.val).symm))
  refine ⟨fun h => hvne ?_, fun I hI => ?_⟩
  · have : η.val V.vacuum ∈ (⊤ : Submodule ℂ A.carrier) := Submodule.mem_top
    rw [h] at this
    exact (Submodule.mem_bot ℂ).mp this
  set P := idealSub I hI with hP
  set XI := OrdVModule.submodule A.isMod P with hXI
  set X : Ordinary V := Ordinary.of XI with hX
  let f : X ⟶ A := ⟨I.subtype, fun u n x => rfl⟩
  by_cases hq : ∀ x ∈ I, q.val x = 0
  · -- the inclusion lies in the right kernel of `μ ≫ q`
    left
    have hzero : tensorHom F (𝟙 A) f ≫ m ≫ q = 0 := by
      refine tensor_hom_ext F _ _ fun n a x => ?_
      simp only [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]
      change q.val ((extIntertwiner F m).val n a (Subtype.val (x : P.carrier))) = 0
      exact hq _ (ext_mem_ideal I hI n a (x : P.carrier).property)
    have hf := hker X f hzero
    rw [eq_bot_iff]
    intro x hx
    have := congrArg (fun φ : X ⟶ A => φ.val ⟨x, hx⟩) hf
    exact (Submodule.mem_bot ℂ).2 this
  · -- `q(I)` is a nonzero ideal of `V`
    right
    push Not at hq
    obtain ⟨x₁, hx₁, hqx₁⟩ := hq
    set qv : A.carrier →ₗ[ℂ] 𝒱 := q.val with hqv
    have hqmode : ∀ (u : 𝒱) (k : ℤ) (x : A.carrier),
        qv (mode (A.isMod.YM u) k x) = V.smul u k (qv x) := by
      intro u k x
      have h := q.property u k x
      exact h
    set J : Submodule ℂ 𝒱 := Submodule.map qv I with hJ
    have hJideal : V.IsIdeal J := by
      rintro u _ k ⟨x, hx, rfl⟩
      exact ⟨mode (A.isMod.YM u) k x, P.act_mem u k hx, hqmode u k x⟩
    rcases hV.1.toStronglyFinite.simple.2 J hJideal with hJ0 | hJ1
    · have : qv x₁ ∈ J := ⟨x₁, hx₁, rfl⟩
      rw [hJ0] at this
      exact absurd ((Submodule.mem_bot ℂ).1 this) hqx₁
    obtain ⟨x, hx, hqx⟩ : V.vacuum ∈ J := hJ1 ▸ Submodule.mem_top
    -- the weight-zero part
    set S : Submodule ℂ 𝒱 := Submodule.map qv (I ⊓ A.isMod.weight 0) with hS
    have hproj : ∀ y : P.carrier,
        ((weightProj (adjointModule V) 0 (qv (y : A.carrier)) : _) : 𝒱) ∈ S := by
      intro y
      have hy : y ∈ ⨆ β, XI.weight β := by
        rw [XI.isInternal.submodule_iSup_eq_top]; trivial
      induction hy using Submodule.iSup_induction' with
      | zero =>
        rw [ZeroMemClass.coe_zero, LinearMap.map_zero, LinearMap.map_zero, ZeroMemClass.coe_zero]
        exact S.zero_mem
      | add y y' _ _ h h' =>
        rw [Submodule.coe_add, LinearMap.map_add, LinearMap.map_add, Submodule.coe_add]
        exact S.add_mem h h'
      | mem β y hyβ =>
        have hyA : (y : A.carrier) ∈ A.isMod.weight β := hyβ
        have hqy : qv y ∈ (adjointModule V).weight β :=
          hom_mem_weight (A₂ := A.isMod) (A₃ := adjointModule V) q.property hyA
        by_cases hβ : β = 0
        · subst hβ
          rw [show weightProj (adjointModule V) 0 (qv y) = ⟨qv y, hqy⟩ from
            weightProj_apply_self (adjointModule V) 0 ⟨qv y, hqy⟩]
          exact ⟨y, ⟨y.property, hyA⟩, rfl⟩
        · rw [weightProj_of_ne (adjointModule V) hβ hqy]
          exact S.zero_mem
    have hvS : V.vacuum ∈ S := by
      have h := hproj ⟨x, hx⟩
      have hvac0 : V.vacuum ∈ (adjointModule V).weight 0 := by
        have := vacuum_mem_adj (V := V)
        simpa using this
      change ((weightProj (adjointModule V) 0 (qv x) : _) : 𝒱) ∈ S at h
      rw [hqx, show weightProj (adjointModule V) 0 V.vacuum = ⟨V.vacuum, hvac0⟩ from
        weightProj_apply_self (adjointModule V) 0 ⟨V.vacuum, hvac0⟩] at h
      exact h
    obtain ⟨y, ⟨hyI, hy0⟩, hqy⟩ := hvS
    have hy0' : y ∈ A.isMod.weight 0 := hy0
    rw [hvac, Submodule.mem_span_singleton] at hy0'
    obtain ⟨c, rfl⟩ := hy0'
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, map_zero] at hqy
      exact hV.1.toStronglyFinite.vacuum_ne_zero hqy.symm
    have hηI : η.val V.vacuum ∈ I := by
      have := I.smul_mem c⁻¹ hyI
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [eq_top_iff]
    intro a _
    have h := hI a (η.val V.vacuum) (-1) hηI
    have e : W.smul a (-1) W.vacuum = a := W.toPreVertexAlgebra.smul_vacuum_neg_one a
    rw [extVOA_vacuum] at e
    rwa [e] at h

/-- `L₁W₁ = 0` for the extension. -/
theorem extVOA_L_one (hV : Nice V) {v : A.carrier}
    (hv : v ∈ (extVOA F m η hl hr htw hloc hvac hpos).grading 1) :
    (extVOA F m η hl hr htw hloc hvac hpos).L 1 v = 0 := by
  rw [VertexOperatorAlgebra.L_def, extVOA_conformalVector]
  change mode (extField F m (η.val V.conformalVector)) (1 + 1) v = 0
  rw [mode_extField, show ((1 + 1 : ℤ) : ℂ) = ((2 : ℤ) : ℂ) by norm_num,
    ext_unit_left_int F m η hl]
  have hv1 : v ∈ A.isMod.weight 1 := by
    have := (extVOA_grading (F := F) (m := m) (η := η) hl hr htw hloc hvac hpos 1) ▸ hv
    simpa using this
  exact L_one_weight_one hV A hv1

/-- **The extension is self-dual** (simple + `L₁W₁ = 0`). -/
theorem extVOA_selfDual (hV : Nice V) (hhap : finrank ℂ (vacuumObject ⟶ A) = 1)
    (q : A ⟶ vacuumObject)
    (hker : ∀ (X : Ordinary V) (f : X ⟶ A), tensorHom F (𝟙 A) f ≫ m ≫ q = 0 → f = 0) :
    (extVOA F m η hl hr htw hloc hvac hpos).SelfDual := by
  have hs := extVOA_isSimple hV hhap q hker (hl := hl) (hr := hr) (htw := htw) (hloc := hloc)
    (hvac := hvac) (hpos := hpos)
  exact VertexOperatorAlgebra.selfDual_of_L_one_grading_one_eq_zero hs.vacuum_ne_zero
    (fun v hv => extVOA_L_one hV hv) hs

end VOA.Huang.HKLNice
