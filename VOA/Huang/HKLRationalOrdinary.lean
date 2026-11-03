/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLRationalAction

/-!
# HKL rationality, part 2: ordinary `W`-modules are completely reducible (given associativity)

For the HKL extension `W` of a commutative haploid algebra `A` with a Frobenius counit in
`Ordinary V` (`V` nice):

* `isModeHom_of_isLinear` — an `A`-linear morphism of `Ordinary V` between the underlying objects
  of two ordinary `W`-modules intertwines every `W`-mode;
* `subIncl` — a weak `W`-submodule `P` of an ordinary `W`-module is an ordinary `W`-module
  (`OrdVModule.submodule`), and its inclusion is an `A`-linear morphism;
* `vRetraction` — `P` has a `V`-linear retraction (`ordinary_complements`, `V` rational);
* `ordinary_weakCompletelyReducible` — **KO Maschke**: if the action morphism of every
  ordinary `W`-module is associative (`hassoc`) and `c ≫ μ ≠ 0` for the Frobenius copairing
  (`hdim`, i.e. `dim A ≠ 0`), every ordinary `W`-module is completely reducible: the `V`-linear
  retraction is averaged into an `A`-linear one (`exists_linear_retraction_of_frobenius`), which
  intertwines the `W`-modes; its kernel is a `W`-complement.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt VOA.Huang.HKLNice
  VOA.Huang.TensorCat.RepPackaging

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable {F : FusionChoice V} {A : Ordinary V} {m : tensorObj F A A ⟶ A}
  {η : vacuumObject ⟶ A}
  {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

/-- **`A`-linear morphisms intertwine the `W`-modes.** -/
theorem isModeHom_of_isLinear {M M' : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup M']
    [Module ℂ M'] {N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M}
    {N' : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M'} (f : actObj N' ⟶ actObj N)
    (hf : tensorHom F (𝟙 A) f ≫ act N = act N' ≫ f) :
    IsModeHom N.toWeakModule N'.toWeakModule f.val := by
  intro a k y
  have h := congrArg (fun g : tensorObj F A (actObj N') ⟶ actObj N =>
    g.val ((F A (actObj N')).intertwiner.val (k : ℂ) a y)) hf
  simp only [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply,
    act_intertwiner_int] at h
  exact h.symm

/-! ## Submodules -/

section Sub

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
  (N : OrdVModule (extVOA F m η hl hr htw hloc hvac hpos) M)
  (P : WeakModule.Submodule' N.toWeakModule)

/-- The modes of the submodule module, coerced. -/
theorem moduleModes_submodule_coe (n : ℂ) (a : A.carrier) (x : P.carrier) :
    ((moduleModes (OrdVModule.submodule N P) n a x : P.carrier) : M) = moduleModes N n a x := by
  unfold moduleModes
  split_ifs with h
  · exact WeakModule.submoduleYM_mode_coe N.toWeakModule P a _ x
  · rfl

/-- The inclusion of a weak `W`-submodule, as a morphism of `Ordinary V`. -/
def subIncl : actObj (OrdVModule.submodule N P) ⟶ actObj N :=
  ⟨P.carrier.subtype, fun u n x =>
    WeakModule.submoduleYM_mode_coe N.toWeakModule P (η.val u) n x⟩

@[simp] theorem subIncl_val (x : P.carrier) : (subIncl N P).val x = (x : M) := rfl

/-- The inclusion is `A`-linear. -/
theorem subIncl_linear :
    tensorHom F (𝟙 A) (subIncl N P) ≫ act N = act (OrdVModule.submodule N P) ≫ subIncl N P := by
  apply tensor_hom_ext F
  intro n a x
  simp only [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply, act_intertwiner,
    subIncl_val]
  exact (moduleModes_submodule_coe N P n a x).symm

/-- `P` as a weak `V`-submodule of the restriction. -/
def subV : WeakModule.Submodule' (actObj N).isMod.toWeakModule :=
  ⟨P.carrier, fun u n _ hx => P.act_mem (η.val u) n hx⟩

/-- Projection along a complement commutes with an endomorphism preserving both summands. -/
theorem projectionOnto_comm {p q : Submodule ℂ M} (h : IsCompl p q) (T : M →ₗ[ℂ] M)
    (hp : ∀ x ∈ p, T x ∈ p) (hq : ∀ x ∈ q, T x ∈ q) (x : M) :
    ((p.projectionOnto q h (T x) : p) : M) = T (p.projectionOnto q h x) := by
  have hx := Submodule.projection_add_projection_eq_self h x
  conv_lhs => rw [← hx]
  rw [map_add, map_add]
  have h1 : p.projectionOnto q h (T (p.projection q h x)) =
      ⟨T (p.projection q h x), hp _ (Submodule.projection_apply_mem h x)⟩ :=
    Submodule.projectionOnto_apply_left h ⟨_, _⟩
  have h2 : p.projectionOnto q h (T (q.projection p h.symm x)) = 0 :=
    Submodule.projectionOnto_apply_of_mem_right h (hq _ (Submodule.projection_apply_mem _ x))
  rw [h1, h2, add_zero]
  rfl

end Sub

/-! ## Maschke for ordinary `W`-modules -/

/-- **Ordinary `W`-modules are completely reducible**, given the associativity of the
`A`-action of every ordinary `W`-module (`hassoc`) and `dim A ≠ 0` in the form `c ≫ μ ≠ 0` for
every Frobenius copairing (`hdim`). -/
theorem ordinary_weakCompletelyReducible (hV : Nice V) (F : FusionChoice V) :
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → ∀ htw : (twistIso A).hom = 𝟙 A,
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 → ∀ q : A ⟶ 𝟙_ (Ordinary V), IsFrobeniusCounit A q →
      ∀ hloc hvac hpos,
      (∀ c : 𝟙_ (Ordinary V) ⟶ A ⊗ A, Zig₁ c (MonObj.mul ≫ q) → c ≫ MonObj.mul ≠ 0) →
      (∀ (M : Type u) [AddCommGroup M] [Module ℂ M]
        (N : OrdVModule (extVOA F (MonObj.mul : tensorObj F A A ⟶ A)
          (MonObj.one : vacuumObject ⟶ A) (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac
          hpos) M),
        (MonObj.mul ▷ actObj N) ≫ act N = (α_ A A (actObj N)).hom ≫ (A ◁ act N) ≫ act N) →
      ∀ (M : Type u) [AddCommGroup M] [Module ℂ M]
        (N : OrdVModule (extVOA F (MonObj.mul : tensorObj F A A ⟶ A)
          (MonObj.one : vacuumObject ⟶ A) (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac
          hpos) M),
        WeakCompletelyReducible N.toWeakModule := by
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap q hfrob hloc hvac hpos hdim hassoc M _ _ N P
  letI := monoidalPreadditive_pbw F hV.1
  letI := monoidalLinear_pbw F hV.1
  obtain ⟨c, hc⟩ := hfrob
  have hZ : Zig₁ c (MonObj.mul ≫ q) := hc
  -- the unit is nonzero
  have hη : (MonObj.one : 𝟙_ (Ordinary V) ⟶ A) ≠ 0 := by
    intro h0
    have h1 := MonObj.one_mul A
    rw [h0, MonoidalPreadditive.zero_whiskerRight, zero_comp] at h1
    have hid : 𝟙 A = 0 := by
      calc 𝟙 A = (λ_ A).inv ≫ (λ_ A).hom := by simp
        _ = 0 := by rw [← h1, comp_zero]
    have hsub : Subsingleton (𝟙_ (Ordinary V) ⟶ A) :=
      ⟨fun f g => by rw [← Category.comp_id f, ← Category.comp_id g, hid, comp_zero, comp_zero]⟩
    have := Module.finrank_zero_of_subsingleton (R := ℂ) (M := 𝟙_ (Ordinary V) ⟶ A)
    omega
  obtain ⟨t, ht⟩ : ∃ t : ℂ, c ≫ MonObj.mul = t • MonObj.one := by
    obtain ⟨t, h⟩ := (finrank_eq_one_iff_of_nonzero' _ hη).mp hhap (c ≫ MonObj.mul)
    exact ⟨t, h.symm⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hdim c hZ ht
  -- the `V`-linear retraction onto `P`
  obtain ⟨Q, hQ⟩ := ordinary_complements hV.1 (actObj N) (subV N P)
  replace hQ : IsCompl P.carrier Q.carrier := hQ
  let r : actObj N ⟶ actObj (OrdVModule.submodule N P) :=
    ⟨P.carrier.projectionOnto Q.carrier hQ, fun u n x => by
      apply Subtype.ext
      change ((P.carrier.projectionOnto Q.carrier hQ
        (mode (N.YM ((MonObj.one : vacuumObject ⟶ A).val u)) n x) : P.carrier) : M) = _
      rw [projectionOnto_comm hQ (mode (N.YM ((MonObj.one : vacuumObject ⟶ A).val u)) n) ?_ ?_]
      · exact (WeakModule.submoduleYM_mode_coe N.toWeakModule P _ n _).symm
      · intro y hy; exact P.act_mem _ n hy
      · intro y hy; exact Q.act_mem u n hy⟩
  have hir : subIncl N P ≫ r = 𝟙 _ := by
    apply Ordinary.hom_ext
    intro x
    exact Submodule.projectionOnto_apply_left hQ x
  -- Maschke
  have hX : IsLeftAct (act N) := ⟨act_unit N, hassoc M N⟩
  have hY : IsLeftAct (act (OrdVModule.submodule N P)) :=
    ⟨act_unit _, hassoc _ (OrdVModule.submodule N P)⟩
  obtain ⟨r', hr'lin, hr'⟩ := exists_linear_retraction_of_frobenius hZ ht0 ht hX hY
    (subIncl_linear N P) hir
  have hmode := isModeHom_of_isLinear r' hr'lin
  have hr'x : ∀ x : P.carrier, r'.val (x : M) = x := fun x =>
    congrArg (fun g : actObj (OrdVModule.submodule N P) ⟶ actObj (OrdVModule.submodule N P) =>
      g.val x) hr'
  refine ⟨⟨LinearMap.ker r'.val, fun a k x hx => ?_⟩, ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    have h := hmode a k x
    erw [hx, map_zero] at h
    exact h
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxP, hxK⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hxK
    have h : r'.val x = ⟨x, hxP⟩ := hr'x ⟨x, hxP⟩
    have h0 : (⟨x, hxP⟩ : P.carrier) = 0 := h.symm.trans hxK
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h0
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    let y : P.carrier := r'.val x
    have h1 : (y : M) ∈ P.carrier := y.2
    have h2 : x - (y : M) ∈ LinearMap.ker r'.val := by
      change r'.val (x - (y : M)) = 0
      have hy : r'.val (y : M) = y := hr'x y
      erw [map_sub, hy]
      exact sub_self _
    have := Submodule.add_mem_sup h1 h2
    rwa [add_sub_cancel] at this


end VOA.Huang.HKLRational
