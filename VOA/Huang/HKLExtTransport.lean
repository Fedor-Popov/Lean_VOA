/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtRigid

/-!
# HKL extensions: transport from a pinned realization to `Rep V` itself

`HKLRepInputRigid` quantifies over realizations `H` pinned to `Rep V` by a monoidal equivalence
`E : H.C ⥤ Ordinary V`.  Everything in the extension property is transported along `E`, so the
input is implied by a statement about **commutative algebras in the actual braided category of
ordinary `V`-modules** (`monoidalCategoryOfStronglyRational_pbw`,
`HexagonClose.braidedCategory_stronglyRational_pbw`, twist `twistIso`):

* `HKLOrdinaryInput` — for nice `V`, any choice of fusion products, and a commutative haploid
  algebra `A` in `Ordinary V` with `θ_A = 𝟙`, a finite group of algebra automorphisms whose average
  is `q ≫ η`, and `q` a Frobenius counit: a nice `W` with `c_W = c_V`, a finite `Γ ≤ Aut W`,
  `V ≅ W^Γ`, and `dim W_n = dim A_n` (the weight-`n` space of the module `A`).
  This is HKL 2015 Thm 3.2/3.4 (`W = A` with `Y_W(a,z)b = μ(𝒴(a,z)b)`), KO 2002 (rigid ⇒
  separable), CKM 2017 / GR Prop. 2.7 (niceness), and the fixed-point identification
  `W^Γ = image of η ≅ V` (the averaging identity).
* `hklRepInputRigid_of_ordinary : HKLOrdinaryInput → HKLRepInputRigid` — proved: commutativity
  through the braided equivalence (`IsRepRealization`'s braiding clause makes `E` lax braided),
  twist, haploidity (`E` fully faithful linear), the group action and averaging identity, the
  Frobenius counit (`zigzag_map`), and the graded-dimension formula from semisimplicity:
  `dim A_n = Σ_k dim (V_{lab (f k)})_n` for `A ≅ ⊕_k X_{f k}` (`finrank_weight_of_decomp`,
  `finrank_weight_congr`) regrouped by multiplicity `#{k | f k = i} = dim Hom(A, X_i)`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory MonoidalCategory Limits Module Complex
open Functor.LaxMonoidal Functor.OplaxMonoidal
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.Tannakian
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.FusionUnit

universe u

/-! ## Weight spaces of ordinary modules under isomorphisms and decompositions -/

section Weights

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- The value of a finite sum of module maps. -/
theorem Ordinary.sum_val {X Y : Ordinary V} {J : Type*} (s : Finset J) (f : J → (X ⟶ Y))
    (x : X.carrier) : (∑ k ∈ s, f k).val x = ∑ k ∈ s, (f k).val x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (f a).val x + (∑ k ∈ s, f k).val x = _
    rw [ih]

/-- A module map restricted to weight spaces. -/
def weightMap {X Y : Ordinary V} (f : X ⟶ Y) (α : ℂ) :
    X.isMod.weight α →ₗ[ℂ] Y.isMod.weight α where
  toFun x := ⟨f.val x, hom_mem_weight f.property x.2⟩
  map_add' x y := Subtype.ext (f.val.map_add x y)
  map_smul' c x := Subtype.ext (f.val.map_smul c x)

@[simp] theorem weightMap_val {X Y : Ordinary V} (f : X ⟶ Y) (α : ℂ) (x : X.isMod.weight α) :
    ((weightMap f α x : Y.isMod.weight α) : Y.carrier) = f.val x := rfl

/-- Isomorphic ordinary modules have isomorphic weight spaces. -/
theorem finrank_weight_congr {X Y : Ordinary V} (e : X ≅ Y) (α : ℂ) :
    finrank ℂ (X.isMod.weight α) = finrank ℂ (Y.isMod.weight α) := by
  refine LinearEquiv.finrank_eq
    { weightMap e.hom α with
      invFun := weightMap e.inv α
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun y => Subtype.ext ?_ }
  · change (e.hom ≫ e.inv).val x.1 = x.1
    rw [e.hom_inv_id]; rfl
  · change (e.inv ≫ e.hom).val y.1 = y.1
    rw [e.inv_hom_id]; rfl

/-- **Weight spaces of a finite decomposition.**  If `X` splits into `Y k` by maps `p k`, `i k`
with `Σ_k p_k ≫ i_k = 𝟙`, `i_k ≫ p_k = 𝟙`, `i_k ≫ p_l = 0` (`k ≠ l`), then
`dim X_α = Σ_k dim (Y k)_α`. -/
theorem finrank_weight_of_decomp {J : Type} [Fintype J] {X : Ordinary V}
    (Y : J → Ordinary V) (p : ∀ k, X ⟶ Y k) (i : ∀ k, Y k ⟶ X)
    (htot : ∑ k, p k ≫ i k = 𝟙 X) (hself : ∀ k, i k ≫ p k = 𝟙 (Y k))
    (hne : ∀ k l, k ≠ l → i k ≫ p l = 0) (α : ℂ) :
    finrank ℂ (X.isMod.weight α) = ∑ k, finrank ℂ ((Y k).isMod.weight α) := by
  classical
  haveI : ∀ k, FiniteDimensional ℂ ((Y k).isMod.weight α) := fun k => (Y k).isMod.finrank α
  let φ : X.isMod.weight α →ₗ[ℂ] ((k : J) → (Y k).isMod.weight α) :=
    LinearMap.pi fun k => weightMap (p k) α
  let ψ : ((k : J) → (Y k).isMod.weight α) →ₗ[ℂ] X.isMod.weight α :=
    ∑ k, (weightMap (i k) α).comp (LinearMap.proj k)
  have hψ : ∀ y, ((ψ y : X.isMod.weight α) : X.carrier) = ∑ k, (i k).val (y k) := by
    intro y
    change ((∑ k, (weightMap (i k) α).comp (LinearMap.proj k)) y : X.isMod.weight α).1 = _
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  rw [← Module.finrank_pi_fintype]
  refine LinearEquiv.finrank_eq
    { φ with
      invFun := ψ
      left_inv := fun x => Subtype.ext ?_
      right_inv := fun y => funext fun l => Subtype.ext ?_ }
  · rw [hψ]
    have h := congrArg (fun g : X ⟶ X => g.val x.1) htot
    simp only [Ordinary.sum_val, Ordinary.comp_apply, Ordinary.id_apply] at h
    exact h
  · change (p l).val ((ψ y : X.isMod.weight α) : X.carrier) = (y l : (Y l).carrier)
    rw [hψ, map_sum, Finset.sum_eq_single l]
    · change (i l ≫ p l).val (y l).1 = _
      rw [hself]; rfl
    · intro k _ hk
      change (i k ≫ p l).val (y k).1 = 0
      rw [hne k l hk]; rfl
    · intro h; exact absurd (Finset.mem_univ l) h

end Weights

/-! ## The Ordinary-level HKL input and the transport -/

/-- **HKL on the actual category of ordinary modules** (HKL 2015 Thm 3.2/3.4, KO 2002, CKM 2017,
GR Prop. 2.7): for nice `V` and any fusion products `F`, a commutative haploid algebra `A` in the
braided category `Ordinary V` with `θ_A = 𝟙`, a finite group of algebra automorphisms with
average `q ≫ η`, and `q` a Frobenius counit, yields a nice `W` (carrier in `V`'s universe) with
the same central charge, a finite `Γ ≤ Aut W` with `V ≅ W^Γ`, and `dim W_n = dim A_n`. -/
def HKLOrdinaryInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (hV : Nice V)
    (F : FusionChoice V),
    letI := monoidalCategoryOfStronglyRational_pbw F hV.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
    ∀ (A : Ordinary V) [MonObj A], IsCommMonObj A → (twistIso A).hom = 𝟙 A →
      finrank ℂ (𝟙_ (Ordinary V) ⟶ A) = 1 →
      ∀ (G : Type) [Group G] [Fintype G] (ρ : G →* CategoryTheory.Aut A),
        (∀ g, IsMonHom (ρ g).hom) →
      ∀ q : A ⟶ 𝟙_ (Ordinary V), ∑ g, (ρ g).hom = q ≫ MonObj.one → IsFrobeniusCounit A q →
      ∃ (𝒲 : Type u) (_ : AddCommGroup 𝒲) (_ : Module ℂ 𝒲) (W : VertexOperatorAlgebra 𝒲)
        (Γ : Subgroup (Aut W)), Nice W ∧ Finite Γ ∧ W.centralCharge = V.centralCharge ∧
        VOAIsomorphic V (orbifoldVOA Γ) ∧
        ∀ n : ℕ, finrank ℂ (W.grading n) = finrank ℂ (A.isMod.weight (n : ℂ))

/-- **The repaired HKL input reduces to `Rep V` itself.** -/
theorem hklRepInputRigid_of_ordinary (h : HKLOrdinaryInput.{u}) : HKLRepInputRigid.{u} := by
  intro 𝒱 _ _ V hV D hD H hH
  obtain ⟨F, hV', E, hEq, hEadd, hElin, hEmon, hbr, htwE, hsimp⟩ := hH
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  letI : E.LaxBraided := { (inferInstance : E.LaxMonoidal) with braided := hbr }
  intro A _ hcomm htw hhap G _ _ ρ hρ q hq hfrob
  letI : MonObj (E.obj A) := Functor.monObjObj A
  have hcomm' : IsCommMonObj (E.obj A) := Functor.isCommMonObj_obj
  have htw' : (twistIso (E.obj A)).hom = 𝟙 (E.obj A) := by
    rw [← htwE A, htw, CategoryTheory.Functor.map_id]
  have hhap' : finrank ℂ (𝟙_ (Ordinary V) ⟶ E.obj A) = 1 := by
    rw [← hhap, (homLinearEquivOfFullyFaithful E (𝟙_ H.C) A).finrank_eq]
    exact (Linear.homCongr ℂ (Functor.Monoidal.εIso E) (Iso.refl (E.obj A))).finrank_eq
  let ρ' : G →* CategoryTheory.Aut (E.obj A) := (E.mapAut A).comp ρ
  have hρ' : ∀ g, IsMonHom (ρ' g).hom := fun g => by
    haveI := hρ g
    change IsMonHom (E.map (ρ g).hom)
    infer_instance
  let q' : E.obj A ⟶ 𝟙_ (Ordinary V) := E.map q ≫ (Functor.Monoidal.εIso E).inv
  have hq' : ∑ g, (ρ' g).hom = q' ≫ MonObj.one := by
    change ∑ g, E.map (ρ g).hom = _
    rw [← Functor.map_sum, hq, Functor.map_comp]
    change _ = (E.map q ≫ (Functor.Monoidal.εIso E).inv) ≫ (Functor.LaxMonoidal.ε E ≫ E.map MonObj.one)
    simp
  have hfrob' : IsFrobeniusCounit (E.obj A) q' := by
    obtain ⟨c, hc⟩ := hfrob
    refine ⟨ε E ≫ E.map c ≫ δ E A A, ?_⟩
    have hz := zigzag_map E c (MonObj.mul ≫ q) hc
    have hp : (MonObj.mul : E.obj A ⊗ E.obj A ⟶ E.obj A) ≫ q' =
        μ E A A ≫ E.map (MonObj.mul ≫ q) ≫ η E := by
      change (μ E A A ≫ E.map MonObj.mul) ≫ E.map q ≫ η E = _
      rw [Functor.map_comp]
      simp only [Category.assoc]
    rw [hp]
    exact hz
  obtain ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, hdW⟩ :=
    h 𝒱 V hV F (E.obj A) hcomm' htw' hhap' G ρ' hρ' q' hq' hfrob'
  refine ⟨𝒲, i1, i2, W, Γ, hW, hΓ, hc, hiso, fun n => ?_⟩
  rw [hdW n]
  -- the graded dimension from the semisimple decomposition of `A`
  obtain ⟨m, f, ⟨e⟩⟩ := H.fusion.semisimple A
  let Y : Fin m → Ordinary V := fun k => E.obj (H.fusion.simple (f k))
  have hdec : finrank ℂ ((E.obj A).isMod.weight (n : ℂ)) =
      ∑ k, finrank ℂ ((Y k).isMod.weight (n : ℂ)) := by
    rw [finrank_weight_congr (E.mapIso e)]
    refine finrank_weight_of_decomp Y
      (fun k => E.map (biproduct.π (fun k => H.fusion.simple (f k)) k))
      (fun k => E.map (biproduct.ι (fun k => H.fusion.simple (f k)) k)) ?_ ?_ ?_ _
    · simp_rw [← Functor.map_comp]
      rw [← Functor.map_sum, biproduct.total, CategoryTheory.Functor.map_id]
    · intro k
      rw [← Functor.map_comp, biproduct.ι_π_self, CategoryTheory.Functor.map_id]
    · intro k l hkl
      rw [← Functor.map_comp, biproduct.ι_π_ne _ hkl, Functor.map_zero]
  have hY : ∀ k, finrank ℂ ((Y k).isMod.weight (n : ℂ)) =
      finrank ℂ ((D.module (H.lab (f k))).weight (n : ℂ)) := fun k =>
    finrank_weight_congr (hsimp (f k)).some (n : ℂ)
  have hmult : ∀ i, (finrank ℂ (A ⟶ H.fusion.simple i) : ℝ) =
      ((Finset.univ.filter fun k => f k = i).card : ℝ) := by
    intro i
    rw [← VOA.Huang.HuangModularity.mult_eq_finrank_hom_to,
      VOA.Huang.HuangModularity.mult_eq_card f e]
  rw [hdec]
  push_cast
  simp_rw [hY, hmult]
  rw [← Finset.sum_fiberwise Finset.univ f
    (fun k => (finrank ℂ ((D.module (H.lab (f k))).weight (n : ℂ)) : ℝ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (finrank ℂ ((D.module (H.lab i)).weight (n : ℂ)) : ℝ)),
    Finset.sum_const, nsmul_eq_mul]
  intro k hk
  rw [(Finset.mem_filter.mp hk).2]

end VOA.Huang.HKLExt
