/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtVOA

/-!
# HKL extensions: algebra automorphisms, the fixed points `W^Γ ≅ V`, and the assembly

For the extension `W = extVOA F μ η …` of an algebra object `A`:

* `extAut` — an **algebra automorphism** `φ` of `A` (`(φ ⊠ φ) ≫ μ = μ ≫ φ`, `η ≫ φ = η`) is a VOA
  automorphism of `W` (`φ(Y_W(a,z)b) = Y_W(φa,z)φb` by the universal property);
* `extAutHom` — a group of algebra automorphisms acts on `W` through VOA automorphisms;
  `Γ := (extAutHom ρ).range` is finite;
* `eta_injective` — the unit `η : V → A` is injective (simplicity of `V` + haploidity);
* `voaIsomorphic_orbifold` — **`V ≅ W^Γ`**: `η` is a VOA homomorphism `V → W` (left unit law
  + `η` a module map) onto the `Γ`-fixed points, the latter because the average `Σ_g ρ(g)` is
  `q ≫ η` (a fixed `x` satisfies `|G| x = η(q x)`).

Assembly: `hklOrdinaryInput_of_inputs : HKLLocalityInput → HKLCFTTypeInput → HKLNiceInput →
HKLOrdinaryInput`, hence (`hklRepInputRigid_of_ordinary`, `gannonRayhaun_huang_rigid`) the
forward Gannon–Rayhaun theorem rests, on the HKL side, on exactly three named TRUE inputs:

* `HKLLocalityInput` — locality of `Y_W` for a commutative algebra with trivial twist (HKL 2015
  Thm 3.2, analytic core);
* `HKLCFTTypeInput` — a haploid algebra in `Rep V` of nice `V` has `A_0 = ℂ η(𝟙)`, `A_{<0} = 0`
  (complete reducibility + pseudo-unitarity + CFT type of `V`);
* `HKLNiceInput` — the extension of a Frobenius (KO-rigid) haploid commutative algebra is nice
  (Kirillov–Ostrik 2002 Thm 3.3/4.5, HKL 2015 Thm 3.4, CKM 2017, GR Prop. 2.7).  The Frobenius
  hypothesis is NECESSARY: the square-zero extension `V ⊕ M` is a VOA that is not simple.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory MonoidalCategory Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable (F : FusionChoice V) {A : Ordinary V} (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)

/-! ## Algebra automorphisms are VOA automorphisms -/

/-- An algebra endomorphism commutes with `Y_W`: `φ(a_k b) = (φ a)_k (φ b)`. -/
theorem ext_map_hom (φ : A ⟶ A) (hm : tensorHom F φ φ ≫ m = m ≫ φ) (n : ℂ) (a b : A.carrier) :
    φ.val ((extIntertwiner F m).val n a b) = (extIntertwiner F m).val n (φ.val a) (φ.val b) := by
  rw [extIntertwiner_val, extIntertwiner_val, ← tensorHom_intertwiner F φ φ n a b,
    ← Ordinary.comp_apply, ← Ordinary.comp_apply, hm]

variable {F m η}
variable {hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom}
  {hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom} {htw : (twistIso A).hom = 𝟙 A}
  {hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b)}
  {hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum}
  {hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥}

variable (hl hr htw hloc hvac hpos) in
/-- **An algebra automorphism of `A` is a VOA automorphism of the extension.** -/
def extAut (φ : A ≅ A) (hm : tensorHom F φ.hom φ.hom ≫ m = m ≫ φ.hom) (hη : η ≫ φ.hom = η) :
    Aut (extVOA F m η hl hr htw hloc hvac hpos) where
  toLinearEquiv :=
    { toLinearMap := φ.hom.val
      invFun := φ.inv.val
      left_inv := fun x => by
        change (φ.hom ≫ φ.inv).val x = x
        rw [φ.hom_inv_id]; rfl
      right_inv := fun x => by
        change (φ.inv ≫ φ.hom).val x = x
        rw [φ.inv_hom_id]; rfl }
  map_smul' u n v := by
    change φ.hom.val ((extVOA F m η hl hr htw hloc hvac hpos).smul u n v) =
      (extVOA F m η hl hr htw hloc hvac hpos).smul (φ.hom.val u) n (φ.hom.val v)
    rw [extVOA_smul, extVOA_smul]
    exact ext_map_hom F m φ.hom hm (n : ℂ) u v
  map_vacuum := by
    change φ.hom.val (η.val V.vacuum) = η.val V.vacuum
    rw [← Ordinary.comp_apply, hη]
  map_omega := by
    change φ.hom.val (η.val V.conformalVector) = η.val V.conformalVector
    rw [← Ordinary.comp_apply, hη]

@[simp] theorem extAut_apply (φ : A ≅ A) (hm hη) (x : A.carrier) :
    extAut hl hr htw hloc hvac hpos φ hm hη x = φ.hom.val x := rfl

variable {G : Type} [Group G]

variable (hl hr htw hloc hvac hpos) in
/-- A group of algebra automorphisms acts on the extension by VOA automorphisms. -/
def extAutHom (ρ : G →* CategoryTheory.Aut A)
    (hm : ∀ g, tensorHom F (ρ g).hom (ρ g).hom ≫ m = m ≫ (ρ g).hom)
    (hη : ∀ g, η ≫ (ρ g).hom = η) :
    G →* Aut (extVOA F m η hl hr htw hloc hvac hpos) where
  toFun g := extAut hl hr htw hloc hvac hpos (ρ g) (hm g) (hη g)
  map_one' := by
    apply Aut.ext; apply LinearEquiv.ext; intro x
    change (ρ 1).hom.val x = x
    rw [map_one]; rfl
  map_mul' g h := by
    apply Aut.ext; apply LinearEquiv.ext; intro x
    change (ρ (g * h)).hom.val x = (ρ g).hom.val ((ρ h).hom.val x)
    rw [map_mul, CategoryTheory.Aut.Aut_mul_def]; rfl

/-! ## The unit is injective, and `V ≅ W^Γ` -/

/-- The kernel of a module map out of the adjoint module is an ideal. -/
theorem ker_isIdeal (η : vacuumObject ⟶ A) : V.IsIdeal (LinearMap.ker η.val) := by
  intro u v n hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h := η.property u n v
  change η.val (mode (V.Y u) n v) = mode (A.isMod.YM u) n (η.val v) at h
  rw [PreVertexAlgebra.smul_def]
  exact h.trans (by erw [hv]; exact map_zero _)

/-- **The unit of a haploid algebra is injective** (simplicity of `V`). -/
theorem eta_injective (hV : Nice V) (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom)
    (hhap : finrank ℂ (vacuumObject ⟶ A) = 1) : Function.Injective η.val := by
  rcases hV.1.toStronglyFinite.simple.2 _ (ker_isIdeal η) with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exfalso
    have hz : ∀ b : A.carrier, b = 0 := by
      intro b
      have h1 := ext_vacuum_left F m η hl (-1) b
      rw [if_pos rfl] at h1
      have h0 : η.val V.vacuum = 0 := by
        have hmem : V.vacuum ∈ (⊤ : Submodule ℂ 𝒱) := Submodule.mem_top
        rw [← h] at hmem
        exact hmem
      rw [h0, map_zero, LinearMap.zero_apply] at h1
      exact h1.symm
    haveI : Subsingleton (vacuumObject ⟶ A) :=
      ⟨fun f g => Ordinary.hom_ext f g fun x => by rw [hz (f.val x), hz (g.val x)]⟩
    rw [finrank_zero_of_subsingleton] at hhap
    exact zero_ne_one hhap

variable [Fintype G]

/-- **`V ≅ W^Γ`** for `Γ` the image of a finite group of algebra automorphisms whose average is
`q ≫ η`. -/
theorem voaIsomorphic_orbifold (hV : Nice V) (hhap : finrank ℂ (vacuumObject ⟶ A) = 1)
    (ρ : G →* CategoryTheory.Aut A)
    (hm : ∀ g, tensorHom F (ρ g).hom (ρ g).hom ≫ m = m ≫ (ρ g).hom)
    (hη : ∀ g, η ≫ (ρ g).hom = η) (q : A ⟶ vacuumObject) (hq : ∑ g, (ρ g).hom = q ≫ η) :
    VOAIsomorphic V (orbifoldVOA (extAutHom hl hr htw hloc hvac hpos ρ hm hη).range) := by
  set Γ := (extAutHom hl hr htw hloc hvac hpos ρ hm hη).range
  have hfix : ∀ v : 𝒱, η.val v ∈ (orbifold Γ).carrier := by
    rintro v _ ⟨g, rfl⟩
    change (ρ g).hom.val (η.val v) = η.val v
    rw [← Ordinary.comp_apply, hη]
  let e₀ : 𝒱 →ₗ[ℂ] (orbifold Γ).carrier := LinearMap.codRestrict _ η.val hfix
  have hinj : Function.Injective e₀ := fun x y hxy =>
    eta_injective hV hl hhap (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨x, hx⟩
    have hxg : ∀ g, (ρ g).hom.val x = x := fun g =>
      hx _ ⟨g, rfl⟩
    have hsum := congrArg (fun f : A ⟶ A => f.val x) hq
    simp only [Ordinary.sum_val, hxg, Finset.sum_const, Finset.card_univ,
      Ordinary.comp_apply] at hsum
    refine ⟨((Fintype.card G : ℂ))⁻¹ • q.val x, Subtype.ext ?_⟩
    change η.val (((Fintype.card G : ℂ))⁻¹ • q.val x) = x
    rw [map_smul, ← hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  let e : 𝒱 ≃ₗ[ℂ] (orbifold Γ).carrier := LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩
  refine ⟨e, ⟨Subtype.ext rfl, fun u n v => Subtype.ext ?_⟩, Subtype.ext rfl⟩
  change η.val (V.smul u n v) =
    (extVOA F m η hl hr htw hloc hvac hpos).smul (η.val u) n (η.val v)
  rw [extVOA_smul, ext_unit_left_int F m η hl]
  exact η.property u n v

/-! ## The named inputs and the assembly -/

/-- **HKL 2015 Thm 3.2, analytic core**: for nice `V`, the vertex operator `Y_W(a,z)b = μ(𝒴(a,z)b)`
of a commutative algebra with trivial twist in `Rep V` is local. -/
def HKLLocalityInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → (twistIso A).hom = 𝟙 A →
      ∀ a b : A.carrier, Local (extField F (MonObj.mul : tensorObj F A A ⟶ A) a)
        (extField F (MonObj.mul : tensorObj F A A ⟶ A) b)

/-- **CFT type of a haploid algebra** (complete reducibility of ordinary modules of a rational
`V`, pseudo-unitarity, CFT type of `V`): `A_0 = ℂ η(𝟙)` and `A_k = 0` for `k < 0`. -/
def HKLCFTTypeInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 →
      A.isMod.weight 0 = ℂ ∙ (MonObj.one : vacuumObject ⟶ A).val V.vacuum ∧
        ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥

/-- **Niceness of the extension** (Kirillov–Ostrik 2002, HKL 2015 Thm 3.4, CKM 2017, GR Prop. 2.7):
the extension of a commutative haploid algebra with trivial twist and a Frobenius counit is nice.
(False without the Frobenius hypothesis: square-zero extensions are not simple.) -/
def HKLNiceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → ∀ htw : (twistIso A).hom = 𝟙 A,
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 → ∀ q : A ⟶ 𝟙_ (Ordinary V), IsFrobeniusCounit A q →
      ∀ hloc hvac hpos,
        Nice (extVOA F (MonObj.mul : tensorObj F A A ⟶ A) (MonObj.one : vacuumObject ⟶ A)
          (MonObj.one_mul A) (MonObj.mul_one A) htw hloc hvac hpos)

/-- **The Ordinary-level HKL input from its three named parts**: the extension
`W = extVOA F μ η …` (locality and CFT type supplied), `Γ` the image of `G` (`extAutHom`), and
`V ≅ W^Γ` (`voaIsomorphic_orbifold`); `dim W_n = dim A_n` by construction. -/
theorem hklOrdinaryInput_of_inputs (hL : HKLLocalityInput.{u}) (hC : HKLCFTTypeInput.{u})
    (hN : HKLNiceInput.{u}) : HKLOrdinaryInput.{u} := by
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap G _ _ ρ hρ q hq hfrob
  have hloc := hL 𝒱 V hV F A hcomm htw
  obtain ⟨hvac, hpos⟩ := hC 𝒱 V hV F A hhap
  have hW := hN 𝒱 V hV F A hcomm htw hhap q hfrob hloc hvac hpos
  have hm : ∀ g, tensorHom F (ρ g).hom (ρ g).hom ≫ (MonObj.mul : tensorObj F A A ⟶ A) =
      MonObj.mul ≫ (ρ g).hom := fun g => (hρ g).mul_hom.symm
  have hη : ∀ g, (MonObj.one : vacuumObject ⟶ A) ≫ (ρ g).hom = MonObj.one := fun g =>
    (hρ g).one_hom
  refine ⟨A.carrier, inferInstance, inferInstance, _, _, hW, ?_, rfl,
    voaIsomorphic_orbifold (hl := MonObj.one_mul A) (hr := MonObj.mul_one A) hV hhap ρ hm hη q hq,
    fun n => rfl⟩
  exact Set.finite_range _ |>.to_subtype

end VOA.Huang.HKLExt
