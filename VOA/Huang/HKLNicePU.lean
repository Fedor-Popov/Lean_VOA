/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLNiceC2
import VOA.Classification.COne.PlusSplitVacuumLift

/-!
# HKL niceness, part 3: the extension is pseudo-unitary

`extVOA_pseudoUnitary`: if `V` is nice and the extension `W = extVOA F μ η …` is simple, then
`W` is pseudo-unitary: an irreducible ordinary `W`-module `N ≇ W` has only weights of positive real
part (Gannon–Rayhaun Prop. 2.7's argument).

* `restrictOrd` — a `W`-module restricts along the vertex algebra map `η : V → W` (left unit law)
  to an ordinary `V`-module with the same grading (`η(ω_V) = ω_W`);
* a weight `α` with `Re α ≤ 0` of `N` sits in an irreducible `V`-summand of `N` (complete
  reducibility, `semisimple_lw_pbw`), which by pseudo-unitarity of `V` must be `≅ V`;
* the image `z` of the vacuum is translation-invariant (`L₋₁z = 0`), so Li's vacuum-like lift
  `a ↦ a₍₋₁₎z` is a `W`-module map `W → N` (`vacuumLiftHom`), injective by simplicity of `W` and
  onto by irreducibility of `N`: `N ≅ W`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLNice

open CategoryTheory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt
  VOA.Huang.TensorCat.RepPackaging VOA.Classification.COne.PlusSplitting

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable {F : FusionChoice V} {A : Ordinary V} {m : tensorObj F A A ⟶ A}
  {η : vacuumObject ⟶ A}
  {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

/-- `η` is a vertex algebra map: `η(u₍ₙ₎v) = η(u)₍ₙ₎η(v)`. -/
theorem eta_smul (u v : 𝒱) (n : ℤ) :
    η.val (V.smul u n v) = (extVOA F m η hl hr htw hloc hvac hpos).smul (η.val u) n (η.val v) := by
  rw [extVOA_smul, ext_unit_left_int F m η hl]
  exact η.property u n v

/-- Restriction of a weak `W`-module along `η`. -/
def restrictWeak {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : WeakModule (extVOA F m η hl hr htw hloc hvac hpos) M) : WeakModule V M where
  YM := N.YM.comp η.val
  vacuum_YM := by
    change N.YM (η.val V.vacuum) = 1
    rw [← extVOA_vacuum (F := F) (m := m) (η := η) hl hr htw hloc hvac hpos]
    exact N.vacuum_YM
  truncation u x := N.truncation (η.val u) x
  jacobi u v x ℓ k n := by
    have h := N.jacobi (η.val u) (η.val v) x ℓ k n
    change (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (N.YM (η.val u)) (ℓ + k - i) (mode (N.YM (η.val v)) (n + i) x)
          - negOnePow ℓ • mode (N.YM (η.val v)) (ℓ + n - i) (mode (N.YM (η.val u)) (k + i) x)))
      = ∑ᶠ i : ℤ, cbz k i • mode (N.YM (η.val (V.smul u (ℓ + i) v))) (k + n - i) x
    rw [h]
    refine finsum_congr fun i => ?_
    rw [eta_smul]

/-- Restriction of an ordinary `W`-module along `η`: an ordinary `V`-module, same grading. -/
def restrictOrd {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M) : OrdVModule V M where
  toWeakModule := restrictWeak N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  L0_weight α x hx := by
    change mode (N.YM (η.val V.conformalVector)) 1 x = α • x
    rw [← extVOA_conformalVector (F := F) (m := m) (η := η) hl hr htw hloc hvac hpos]
    exact N.L0_weight α x hx
  finrank := N.finrank
  boundedBelow := N.boundedBelow

/-- **The extension is pseudo-unitary** (given its simplicity). -/
theorem extVOA_pseudoUnitary (hV : Nice V)
    (hWs : (extVOA F m η hl hr htw hloc hvac hpos).IsSimple) :
    PseudoUnitary (extVOA F m η hl hr htw hloc hvac hpos) := by
  classical
  set W := extVOA F m η hl hr htw hloc hvac hpos with hW
  intro M _ _ N hirr hne α hα
  by_contra hle
  push Not at hle
  set NV := restrictOrd N with hNV
  set X : Ordinary V := Ordinary.of NV with hX
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hV.1 X
  let g : Fin n → Ordinary V := fun j => Ordinary.of (R j).isMod
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  -- a component of `x` is nonzero
  have hex : ∃ j, (biproduct.π g j).val (e.hom.val x) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx0
    have htot := congrArg (fun φ : X ⟶ X => φ.val x)
      (show e.hom ≫ (∑ j, biproduct.π g j ≫ biproduct.ι g j) ≫ e.inv = 𝟙 X by
        rw [biproduct.total, Category.id_comp, e.hom_inv_id])
    simp only [Ordinary.comp_apply, Ordinary.sum_val, Ordinary.id_apply] at htot
    rw [← htot, Finset.sum_eq_zero fun j _ => by rw [hall j]; exact map_zero _]
    exact map_zero _
  obtain ⟨j, hj⟩ := hex
  have hyw : (biproduct.π g j).val (e.hom.val x) ∈ (g j).isMod.weight α :=
    hom_mem_weight (A₂ := (⨁ g).isMod) (A₃ := (g j).isMod) (biproduct.π g j).property
      (hom_mem_weight (A₂ := X.isMod) (A₃ := (⨁ g).isMod) e.hom.property hx)
  have hαne : (g j).isMod.weight α ≠ ⊥ := fun hb => hj (by
    rw [hb] at hyw; exact (Submodule.mem_bot ℂ).1 hyw)
  by_cases hiso : Nonempty (vacuumObject ≅ g j)
  swap
  · have hposj : ∀ β : ℂ, (g j).isMod.weight β ≠ ⊥ → 0 < β.re := by
      refine hV.2 (R j).carrier (R j).isMod (hR j) ⟨fun me => hiso ?_⟩
      exact ⟨(Ordinary.isoOfModuleEquiv (X := g j) (Y := vacuumObject) me).symm⟩
    exact absurd (hposj α hαne) (not_lt.2 hle)
  obtain ⟨s⟩ := hiso
  -- the vacuum-like vector
  set t : vacuumObject ⟶ X := s.hom ≫ biproduct.ι g j ≫ e.inv with ht
  set z : M := t.val V.vacuum with hz
  have ht_inj : Function.Injective t.val := by
    intro a b hab
    have h := congrArg (fun y => (s.inv).val ((biproduct.π g j).val (e.hom.val y))) hab
    simp only [ht, Ordinary.comp_apply] at h
    rw [← Ordinary.comp_apply e.inv e.hom, e.inv_hom_id, Ordinary.id_apply,
      ← Ordinary.comp_apply e.inv e.hom, e.inv_hom_id, Ordinary.id_apply,
      ← Ordinary.comp_apply (biproduct.ι g j), biproduct.ι_π_self,
      ← Ordinary.comp_apply (biproduct.ι g j), biproduct.ι_π_self,
      Ordinary.id_apply, Ordinary.id_apply, ← Ordinary.comp_apply s.hom s.inv, s.hom_inv_id,
      ← Ordinary.comp_apply s.hom s.inv, s.hom_inv_id, Ordinary.id_apply, Ordinary.id_apply] at h
    exact h
  have hz0 : z ≠ 0 := fun h0 =>
    hV.1.toStronglyFinite.vacuum_ne_zero (ht_inj (h0.trans (map_zero t.val).symm))
  have htr : translation N.toWeakModule z = 0 := by
    change mode (N.YM W.conformalVector) 0 z = 0
    rw [extVOA_conformalVector]
    change mode (X.isMod.YM V.conformalVector) 0 (t.val V.vacuum) = 0
    rw [← t.property V.conformalVector 0 V.vacuum]
    have h0 : mode (V.Y V.conformalVector) 0 V.vacuum = 0 := by
      have := VOA.VertexOperatorAlgebra.L_neg_one_vacuum V
      rwa [VertexOperatorAlgebra.L_def, show (-1 : ℤ) + 1 = 0 by norm_num] at this
    change t.val (mode (V.Y V.conformalVector) 0 V.vacuum) = 0
    rw [h0]
    exact LinearMap.map_zero _
  -- Li's lift `W → N`
  set φ := vacuumLiftHom N.toWeakModule z htr with hφ
  have hinj := vacuumLiftHom_injective hWs N.toWeakModule htr hz0
  let Pr : WeakModule.Submodule' N.toWeakModule :=
    { carrier := LinearMap.range φ.toLinearMap
      act_mem := by
        rintro u k _ ⟨a, rfl⟩
        exact ⟨W.smul u k a, φ.map_act u k a⟩ }
  have hsurj : Function.Surjective φ.toLinearMap := by
    rcases hirr.2 Pr with h | h
    · exfalso
      have : z ∈ Pr.carrier := ⟨W.vacuum, vacuumLiftHom_vacuum N.toWeakModule z htr⟩
      rw [h] at this
      exact hz0 ((Submodule.mem_bot ℂ).1 this)
    · intro y
      have : y ∈ Pr.carrier := by rw [h]; exact Submodule.mem_top
      exact this
  let eφ : A.carrier ≃ₗ[ℂ] M := LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩
  refine hne.false ⟨eφ.symm, fun u k y => ?_⟩
  apply eφ.injective
  rw [LinearEquiv.apply_symm_apply]
  change N.toWeakModule.act u k y = φ.toLinearMap (W.smul u k (eφ.symm y))
  have := φ.map_act u k (eφ.symm y)
  change φ.toLinearMap (W.smul u k (eφ.symm y)) = N.toWeakModule.act u k (φ.toLinearMap (eφ.symm y))
    at this
  rw [this]
  congr 1
  exact (eφ.apply_symm_apply y).symm

end VOA.Huang.HKLNice
