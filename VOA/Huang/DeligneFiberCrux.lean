/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberDeriv

/-!
# Deligne's fiber functor — the Gram–Schmidt crux: the pivot is not nilpotent

Let `G` be a lax braided functor (a commutative algebra `A` of `Ind(C)`) carrying an orthonormal
`m`-family `(e, f)` on `X`, with `symDim X = n > m`.  In the free extension
`H = A ⊗ Sym(Xᘁ ⊞ X)` (`tensorG G (symGCMon (Xᘁ ⊞ X))`) adjoin the generic vector `e'` and the
generic covector `f'` and put `P e' = e' - Σ_j ⟨f_j, e'⟩ e_j`, `q = ⟨f', P e'⟩ ∈ H 𝟙`.

**Theorem** (`pw_ne_zero`): `q^k ≠ 0` for every `k`.

Proof (a Laplacian argument, in two first-order steps).  Let `∂_{f'}`, `∂_{e'}` be the
polarization derivations (`tder`, tails `X` and `Xᘁ`).  If `q^k = 0` then
`0 = ∂_{f'}(q^k) = k q^{k-1} · P e'`; applying `∂_{e'}` and contracting the tails,
`0 = q^{k-1} tr(P) + (k-1) q^{k-2} ⟨f' P, P e'⟩ = (n - m + k - 1) q^{k-1}`,
so `q^{k-1} = 0`; finally `q^0 = 1 ≠ 0`.  Positivity enters through `n - m ≥ 1`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal
open scoped TensorProduct DirectSum

universe v u

section ActGeneral

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (H : C ⥤ ModuleCat.{0} ℂ) [H.LaxBraided]

theorem act_act {Y : C} (r s : H.obj (𝟙_ C)) (z : H.obj Y) : act H r (act H s z) = act H (act H r s) z := by
  change (H.map (λ_ Y).hom).hom ((μ H (𝟙_ C) Y).hom (r ⊗ₜ (H.map (λ_ Y).hom).hom ((μ H (𝟙_ C) Y).hom (s ⊗ₜ z)))) =
    (H.map (λ_ Y).hom).hom ((μ H (𝟙_ C) Y).hom ((H.map (λ_ (𝟙_ C)).hom).hom ((μ H (𝟙_ C) (𝟙_ C)).hom (r ⊗ₜ s)) ⊗ₜ z))
  rw [← μ_whiskerLeft_apply, ← μ_assoc_apply, ← μ_whiskerRight_apply, ← map_comp_apply, ← map_comp_apply,
    ← map_comp_apply]
  congr 3
  monoidal

end ActGeneral

section DerConseq

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] {B : GCMon C} {W : C} (D : GCDer B W)

local notation "H" => tensorG G B

/-- Moving a tail past a vector: `r' · y` for `r' ∈ H(𝟙 ⊗ W)`, `y ∈ H Y`. -/
def tmulT {Y : C} (r' : (H).obj (𝟙_ C ⊗ W)) (y : (H).obj Y) : (H).obj (Y ⊗ W) :=
  ((H).map ((λ_ Y).hom ▷ W)).hom (((H).map (tauSq W (𝟙_ C) Y)).hom ((μ (H) (𝟙_ C ⊗ W) Y).hom (r' ⊗ₜ y)))

theorem tder_act {Y : C} (r : (H).obj (𝟙_ C)) (y : (H).obj Y) :
    tder G D Y (act (H) r y) = act (H) r (tder G D Y y) + tmulT G (tder G D (𝟙_ C) r) y := by
  change tder G D Y (((H).map (λ_ Y).hom).hom ((μ (H) (𝟙_ C) Y).hom (r ⊗ₜ y))) = _
  rw [tder_map, tder_μ]
  simp only [mulSnd, map_add]
  congr 1
  have e : (α_ (𝟙_ C) Y W).inv ≫ ((λ_ Y).hom ▷ W) = (λ_ (Y ⊗ W)).hom := by monoidal
  rw [map_map_apply, e]
  rfl

theorem tmulT_unit (r' : (H).obj (𝟙_ C ⊗ W)) (s : (H).obj (𝟙_ C)) : tmulT G r' s = act (H) s r' := by
  have e : (β_ (𝟙_ C) (𝟙_ C ⊗ W)).hom ≫ tauSq W (𝟙_ C) (𝟙_ C) ≫ ((λ_ (𝟙_ C)).hom ▷ W) =
      (λ_ (𝟙_ C ⊗ W)).hom := by
    simp only [tauSq, braiding_tensorUnit_left, braiding_tensorUnit_right]
    monoidal
  rw [tmulT, ← μ_braid_apply, map_map_apply, map_map_apply, e]
  rfl

theorem tmulT_add_left {Y : C} (r₁ r₂ : (H).obj (𝟙_ C ⊗ W)) (y : (H).obj Y) :
    tmulT G (r₁ + r₂) y = tmulT G r₁ y + tmulT G r₂ y := by
  simp [tmulT, TensorProduct.add_tmul]

theorem tmulT_smul_left {Y : C} (c : ℂ) (r : (H).obj (𝟙_ C ⊗ W)) (y : (H).obj Y) :
    tmulT G (c • r) y = c • tmulT G r y := by
  simp [tmulT, ← TensorProduct.smul_tmul']

theorem tmulT_act_left {Y : C} (a : (H).obj (𝟙_ C)) (r : (H).obj (𝟙_ C ⊗ W)) (y : (H).obj Y) :
    tmulT G (act (H) a r) y = act (H) a (tmulT G r y) := by
  simp only [tmulT]
  rw [μ_act_left, act_natural, act_natural]

/-- Powers `q^k` (iterated action). -/
def pw (q : (H).obj (𝟙_ C)) : ℕ → (H).obj (𝟙_ C)
  | 0 => (ε (H)).hom 1
  | k + 1 => act (H) q (pw q k)

theorem tder_unit_one : tder G D (𝟙_ C) ((ε (H)).hom 1) = 0 := tder_ε G D 1

/-- `∂(q^{k+1}) = (k+1) q^k ∂q`. -/
theorem tder_pw (q : (H).obj (𝟙_ C)) : ∀ k : ℕ,
    tder G D (𝟙_ C) (pw G q (k + 1)) = ((k + 1 : ℕ) : ℂ) • act (H) (pw G q k) (tder G D (𝟙_ C) q)
  | 0 => by
    simp only [pw]
    rw [tder_act, tder_unit_one, act_zero_right, zero_add, tmulT_unit]
    simp
  | k + 1 => by
    have ih := tder_pw q k
    change tder G D (𝟙_ C) (act (H) q (pw G q (k + 1))) = _
    rw [tder_act, ih, act_smul_right, tmulT_unit, act_act]
    change ((k + 1 : ℕ) : ℂ) • act (H) (pw G q (k + 1)) _ + act (H) (pw G q (k + 1)) _ = _
    rw [Nat.cast_succ (k + 1), add_smul, one_smul]

theorem tder_pairG [RightRigidCategory C] {X : C} (g : (H).obj Xᘁ) (x : (H).obj X) :
    tder G D (𝟙_ C) (pairG (H) g x) =
      ((H).map (ε_ X Xᘁ ▷ W)).hom (((H).map (α_ Xᘁ X W).inv).hom ((μ (H) Xᘁ (X ⊗ W)).hom (g ⊗ₜ tder G D X x)) +
        ((H).map (tauSq W Xᘁ X)).hom ((μ (H) (Xᘁ ⊗ W) X).hom (tder G D Xᘁ g ⊗ₜ x))) := by
  rw [pairG, tder_map, tder_μ]
  rfl

end DerConseq

section Generic

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [HasKernels C]

theorem symL_one (V : C) : symL V 1 = 𝟙 _ := by
  simp [symL_succ, symL_zero, cycI_zero]

/-- A degree-one generator `W' ⟶ S^1 V` from `g : W' ⟶ V`. -/
def inj1 {V W' : C} (g : W' ⟶ V) : W' ⟶ symPow V 1 := (λ_ W').inv ≫ (𝟙_ C ◁ g) ≫ symπ V 1

theorem inj1_symD {V W W' : C} (φ : V ⟶ W) (g : W' ⟶ V) :
    inj1 g ≫ symD φ 0 = (λ_ W').inv ≫ (symπ V 0 ⊗ₘ (g ≫ φ)) := by
  simp only [inj1, symD, Category.assoc, Linear.comp_smul]
  rw [← Category.assoc (symπ V 1), symπ_symι, symL_one, Category.id_comp, whiskerLeft_comp_tensorHom]
  simp

end Generic

section Crux

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  [HasKernels C] [HasBinaryBiproducts C] (X : C)

/-- The generic vector `e'` (degree one, `Xᘁ`-component of `V = Xᘁ ⊞ X`). -/
def ue : 𝟙_ C ⟶ symPow (Xᘁ ⊞ X) 1 ⊗ X :=
  η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ (inj1 (biprod.inl : Xᘁ ⟶ Xᘁ ⊞ X) ▷ X)

/-- The generic covector `f'` (degree one, `X`-component). -/
def uf : 𝟙_ C ⟶ symPow (Xᘁ ⊞ X) 1 ⊗ Xᘁ :=
  η_ X Xᘁ ≫ (inj1 (biprod.inr : X ⟶ Xᘁ ⊞ X) ▷ Xᘁ)

/-- `∂_{e'}`: polarization along `fst : Xᘁ ⊞ X ⟶ Xᘁ` (tail `Xᘁ`). -/
def D1 : GCDer (symGCMon (Xᘁ ⊞ X)) Xᘁ := symGCDer (biprod.fst : Xᘁ ⊞ X ⟶ Xᘁ)

/-- `∂_{f'}`: polarization along `snd : Xᘁ ⊞ X ⟶ X` (tail `X`). -/
def D2 : GCDer (symGCMon (Xᘁ ⊞ X)) X := symGCDer (biprod.snd : Xᘁ ⊞ X ⟶ X)

theorem Δ0_of_inj1 {W W' Y : C} (φ : Xᘁ ⊞ X ⟶ W) (g : W' ⟶ Xᘁ ⊞ X) :
    (inj1 g ▷ Y) ≫ (symGCDer φ).Δ 0 Y =
      ((λ_ W').inv ▷ Y) ≫ (((symπ (Xᘁ ⊞ X) 0) ⊗ₘ (g ≫ φ)) ▷ Y) ≫ (α_ _ _ _).hom ≫
        (symPow (Xᘁ ⊞ X) 0 ◁ (β_ W Y).hom) := by
  simp only [GCDer.Δ, symGCDer, Category.assoc]
  erw [← comp_whiskerRight_assoc (inj1 g), inj1_symD, comp_whiskerRight, Category.assoc]
  rfl

theorem ue_Δ1 : ue X ≫ (D1 X).Δ 0 X = η_ X Xᘁ ≫ (symGCMon (Xᘁ ⊞ X)).ι0 (X ⊗ Xᘁ) := by
  have h1 : (β_ X Xᘁ).hom ≫ ((λ_ Xᘁ).inv ▷ X) ≫ (α_ (𝟙_ C) Xᘁ X).hom ≫ (𝟙_ C ◁ (β_ Xᘁ X).hom) =
      (λ_ (X ⊗ Xᘁ)).inv := by
    calc _ = (β_ X Xᘁ).hom ≫ (λ_ (Xᘁ ⊗ X)).inv ≫ (𝟙_ C ◁ (β_ Xᘁ X).hom) := by monoidal
      _ = (β_ X Xᘁ).hom ≫ (β_ Xᘁ X).hom ≫ (λ_ (X ⊗ Xᘁ)).inv := by rw [← leftUnitor_inv_naturality]
      _ = _ := by rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  rw [ue, Category.assoc, Category.assoc, D1, Δ0_of_inj1, biprod.inl_fst, tensorHom_id]
  simp only [GCMon.ι0, symGCMon]
  congr 1
  rw [associator_naturality_left_assoc, ← whisker_exchange, ← reassoc_of% h1]

theorem uf_Δ2 : uf X ≫ (D2 X).Δ 0 Xᘁ = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ (symGCMon (Xᘁ ⊞ X)).ι0 (Xᘁ ⊗ X) := by
  have h1 : ((λ_ X).inv ▷ Xᘁ) ≫ (α_ (𝟙_ C) X Xᘁ).hom ≫ (𝟙_ C ◁ (β_ X Xᘁ).hom) =
      (β_ X Xᘁ).hom ≫ (λ_ (Xᘁ ⊗ X)).inv := by
    calc _ = (λ_ (X ⊗ Xᘁ)).inv ≫ (𝟙_ C ◁ (β_ X Xᘁ).hom) := by monoidal
      _ = _ := by rw [← leftUnitor_inv_naturality]
  rw [uf, Category.assoc, D2, Δ0_of_inj1, biprod.inr_snd, tensorHom_id]
  simp only [GCMon.ι0, symGCMon]
  congr 1
  rw [associator_naturality_left_assoc, ← whisker_exchange, reassoc_of% h1]

theorem ue_Δ2 : ue X ≫ (D2 X).Δ 0 X = 0 := by
  rw [ue, Category.assoc, Category.assoc, D2, Δ0_of_inj1, biprod.inl_snd]
  simp only [MonoidalPreadditive.tensor_zero, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp,
    Limits.comp_zero]
  erw [Limits.comp_zero, Limits.comp_zero]

theorem uf_Δ1 : uf X ≫ (D1 X).Δ 0 Xᘁ = 0 := by
  rw [uf, Category.assoc, D1, Δ0_of_inj1, biprod.inr_fst]
  simp only [MonoidalPreadditive.tensor_zero, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp,
    Limits.comp_zero]
  erw [Limits.comp_zero]

end Crux

section Zig

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  (H : C ⥤ ModuleCat.{0} ℂ) [H.LaxBraided]

/-- D-level snake: `λ⁻¹ ≫ ((η ≫ β) ▷ X) ≫ τ ≫ (ε ▷ X) = λ⁻¹`. -/
theorem snake_tau (X : C) :
    (λ_ X).inv ≫ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ X) ≫ tauSq X Xᘁ X ≫ (ε_ X Xᘁ ▷ X) = (λ_ X).inv := by
  have hz := ExactPairing.evaluation_coevaluation X Xᘁ
  calc (λ_ X).inv ≫ ((η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ X) ≫ tauSq X Xᘁ X ≫ (ε_ X Xᘁ ▷ X)
      = (λ_ X).inv ≫ (η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ ((β_ X (Xᘁ ⊗ X)).hom ≫ (ε_ X Xᘁ ▷ X)) := by
        simp only [tauSq, BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight, Category.assoc]
        monoidal
    _ = (λ_ X).inv ≫ ((η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ (X ◁ ε_ X Xᘁ)) ≫ (β_ X (𝟙_ C)).hom := by
        rw [← BraidedCategory.braiding_naturality_right]
        simp only [Category.assoc]
    _ = (λ_ X).inv := by
        rw [hz, braiding_tensorUnit_right]
        simp

theorem zig_apply {X : C} (v : H.obj X) :
    (H.map (ε_ X Xᘁ ▷ X)).hom ((H.map (tauSq X Xᘁ X)).hom ((μ H (Xᘁ ⊗ X) X).hom
      ((H.map (η_ X Xᘁ ≫ (β_ X Xᘁ).hom)).hom ((ε H).hom 1) ⊗ₜ v))) = (H.map (λ_ X).inv).hom v := by
  rw [← μ_whiskerRight_apply, unit_left_inv_apply, one_smul, map_map_apply, map_map_apply, map_map_apply]
  rw [snake_tau]

/-- Moving a covector tail past a vector: `tmulT (λ⁻¹ g) x = x · g`. -/
theorem tmulT_lam {Y W : C} (g : H.obj W) (x : H.obj Y) :
    (H.map ((λ_ Y).hom ▷ W)).hom ((H.map (tauSq W (𝟙_ C) Y)).hom ((μ H (𝟙_ C ⊗ W) Y).hom
      ((H.map (λ_ W).inv).hom g ⊗ₜ x))) = (μ H Y W).hom (x ⊗ₜ g) := by
  have e : (β_ Y W).hom ≫ ((λ_ W).inv ▷ Y) ≫ tauSq W (𝟙_ C) Y ≫ ((λ_ Y).hom ▷ W) = 𝟙 _ := by
    calc _ = (β_ Y W).hom ≫ (β_ W Y).hom := by
          simp only [tauSq]
          monoidal
      _ = 𝟙 _ := SymmetricCategory.symmetry _ _
  rw [← μ_whiskerRight_apply, ← μ_braid_apply H x g, map_map_apply, map_map_apply, map_map_apply]
  rw [e, H.map_id]
  rfl

end Zig

section PairAlg

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  (H : C ⥤ ModuleCat.{0} ℂ) [H.LaxBraided] {X : C}

theorem pairG_add_right (g : H.obj Xᘁ) (v w : H.obj X) : pairG H g (v + w) = pairG H g v + pairG H g w := by
  simp [pairG, TensorProduct.tmul_add]

theorem pairG_sub_right (g : H.obj Xᘁ) (v w : H.obj X) : pairG H g (v - w) = pairG H g v - pairG H g w := by
  simp [pairG, TensorProduct.tmul_sub]

theorem pairG_sum_right {ι : Type*} (s : Finset ι) (g : H.obj Xᘁ) (v : ι → H.obj X) :
    pairG H g (∑ i ∈ s, v i) = ∑ i ∈ s, pairG H g (v i) := by
  simp [pairG, TensorProduct.tmul_sum]

theorem pairG_sub_left (g h : H.obj Xᘁ) (v : H.obj X) : pairG H (g - h) v = pairG H g v - pairG H h v := by
  simp [pairG, TensorProduct.sub_tmul]

theorem pairG_sum_left {ι : Type*} (s : Finset ι) (g : ι → H.obj Xᘁ) (v : H.obj X) :
    pairG H (∑ i ∈ s, g i) v = ∑ i ∈ s, pairG H (g i) v := by
  simp [pairG, TensorProduct.sum_tmul]

theorem pairG_act_right (g : H.obj Xᘁ) (r : H.obj (𝟙_ C)) (v : H.obj X) :
    pairG H g (act H r v) = act H r (pairG H g v) := by
  rw [pairG, μ_act_right, act_natural]
  rfl

theorem pairG_act_left (g : H.obj Xᘁ) (r : H.obj (𝟙_ C)) (v : H.obj X) :
    pairG H (act H r g) v = act H r (pairG H g v) := by
  rw [pairG, μ_act_left, act_natural]
  rfl

theorem act_comm (r s : H.obj (𝟙_ C)) : act H r s = act H s r :=
  (unitRing H).mul_comm r s

theorem act_add_left {Y : C} (r s : H.obj (𝟙_ C)) (y : H.obj Y) : act H (r + s) y = act H r y + act H s y := by
  simp [act, TensorProduct.add_tmul]

theorem act_smul_left {Y : C} (c : ℂ) (r : H.obj (𝟙_ C)) (y : H.obj Y) : act H (c • r) y = c • act H r y := by
  simp [act, ← TensorProduct.smul_tmul']

theorem act_sub_right {Y : C} (r : H.obj (𝟙_ C)) (y z : H.obj Y) : act H r (y - z) = act H r y - act H r z := by
  simp [act, TensorProduct.tmul_sub]

theorem act_sum_right {Y : C} {ι : Type*} (s : Finset ι) (r : H.obj (𝟙_ C)) (y : ι → H.obj Y) :
    act H r (∑ i ∈ s, y i) = ∑ i ∈ s, act H r (y i) := by
  simp [act, TensorProduct.tmul_sum]

theorem μ_unit_left_act {Y : C} (r : H.obj (𝟙_ C)) (y : H.obj Y) :
    (μ H (𝟙_ C) Y).hom (r ⊗ₜ y) = (H.map (λ_ Y).inv).hom (act H r y) := by
  change _ = (H.map (λ_ Y).inv).hom ((H.map (λ_ Y).hom).hom ((μ H (𝟙_ C) Y).hom (r ⊗ₜ y)))
  rw [← map_comp_apply, Iso.hom_inv_id, H.map_id]
  rfl

variable {m : ℕ} (E : Fin m → H.obj X) (F : Fin m → H.obj Xᘁ)

/-- The projection `P v = v - Σ_j ⟨F_j, v⟩ E_j` onto the orthogonal complement. -/
def Pv (v : H.obj X) : H.obj X := v - ∑ j, act H (pairG H (F j) v) (E j)

/-- The dual projection `g P = g - Σ_j ⟨g, E_j⟩ F_j`. -/
def Pc (g : H.obj Xᘁ) : H.obj Xᘁ := g - ∑ j, act H (pairG H g (E j)) (F j)

variable (horth : ∀ i j, pairG H (F i) (E j) = if i = j then (ε H).hom 1 else 0)
include horth

theorem pairG_Pv (i : Fin m) (v : H.obj X) : pairG H (F i) (Pv H E F v) = 0 := by
  rw [Pv, pairG_sub_right, pairG_sum_right]
  simp only [pairG_act_right, horth]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), act_zero_right]) (by simp),
    if_pos rfl, act_unit_right, sub_self]

theorem pairG_Pc_E (g : H.obj Xᘁ) (j : Fin m) : pairG H (Pc H E F g) (E j) = 0 := by
  rw [Pc, pairG_sub_left, pairG_sum_left]
  simp only [pairG_act_left, horth]
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi, act_zero_right]) (by simp),
    if_pos rfl, act_unit_right, sub_self]

theorem pairG_Pc_Pv (g : H.obj Xᘁ) (v : H.obj X) : pairG H (Pc H E F g) (Pv H E F v) = pairG H g (Pv H E F v) := by
  rw [Pc, pairG_sub_left, pairG_sum_left]
  simp only [pairG_act_left, pairG_Pv H E F horth, act_zero_right, Finset.sum_const_zero, sub_zero]

end PairAlg

section CruxMain

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  [HasKernels C] [HasBinaryBiproducts C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ] (X : C)

local notation "SB" => symGCMon (Xᘁ ⊞ X)
local notation "HH" => tensorG G (symGCMon (Xᘁ ⊞ X))

/-- The generic vector `e' ∈ H X`. -/
def ev' : (HH).obj X := tlof G (SB) X 1 ((G.map (ue X)).hom ((ε G).hom 1))

/-- The generic covector `f' ∈ H Xᘁ`. -/
def fv' : (HH).obj Xᘁ := tlof G (SB) Xᘁ 1 ((G.map (uf X)).hom ((ε G).hom 1))

theorem tder_inclG {W : C} (D : GCDer (SB) W) {Y : C} (x : G.obj Y) : tder G D Y (inclG G (SB) Y x) = 0 :=
  tder_lof_zero G D Y _

theorem tder1_ev : tder G (D1 X) X (ev' G X) = ((HH).map (η_ X Xᘁ)).hom ((ε (HH)).hom 1) := by
  change tder G (D1 X) X (tlof G (SB) X (0 + 1) _) = _
  rw [tder_lof_succ]
  erw [map_map_apply]
  erw [ue_Δ1]
  rw [← map_map_apply, inclG_ε, inclG_map]
  rfl

theorem tder2_ev : tder G (D2 X) X (ev' G X) = 0 := by
  change tder G (D2 X) X (tlof G (SB) X (0 + 1) _) = _
  rw [tder_lof_succ]
  erw [map_map_apply]
  erw [ue_Δ2]
  rw [G.map_zero]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  rfl

theorem tder1_fv : tder G (D1 X) Xᘁ (fv' G X) = 0 := by
  change tder G (D1 X) Xᘁ (tlof G (SB) Xᘁ (0 + 1) _) = _
  rw [tder_lof_succ]
  erw [map_map_apply]
  erw [uf_Δ1]
  rw [G.map_zero]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  rfl

theorem tder2_fv : tder G (D2 X) Xᘁ (fv' G X) = ((HH).map (η_ X Xᘁ ≫ (β_ X Xᘁ).hom)).hom ((ε (HH)).hom 1) := by
  change tder G (D2 X) Xᘁ (tlof G (SB) Xᘁ (0 + 1) _) = _
  rw [tder_lof_succ]
  erw [map_map_apply]
  erw [uf_Δ2]
  rw [← Category.assoc, ← map_map_apply, inclG_ε, inclG_map]
  rfl

theorem tmulT_zero {W Y : C} (y : (HH).obj Y) : tmulT G (0 : (HH).obj (𝟙_ C ⊗ W)) y = 0 := by
  simp [tmulT]

theorem tder_act_zero {W : C} (D : GCDer (SB) W) {Y : C} (r : (HH).obj (𝟙_ C)) (y : (HH).obj Y) (hr : tder G D (𝟙_ C) r = 0)
    (hy : tder G D Y y = 0) : tder G D Y (act (HH) r y) = 0 := by
  rw [tder_act, hr, hy, act_zero_right, tmulT_zero, add_zero]

theorem tder_pairG_zero {W : C} (D : GCDer (SB) W) (g : (HH).obj Xᘁ) (x : (HH).obj X) (hg : tder G D Xᘁ g = 0)
    (hx : tder G D X x = 0) : tder G D (𝟙_ C) (pairG (HH) g x) = 0 := by
  rw [tder_pairG, hg, hx]
  simp

variable {m : ℕ} (e : Fin m → G.obj X) (f : Fin m → G.obj Xᘁ)

/-- The old frame, transported to the free extension. -/
def EE : Fin m → (HH).obj X := fun j => inclG G (SB) X (e j)
def FF : Fin m → (HH).obj Xᘁ := fun j => inclG G (SB) Xᘁ (f j)

/-- The **pivot** `q = ⟨f', P e'⟩`. -/
def qq : (HH).obj (𝟙_ C) := pairG (HH) (fv' G X) (Pv (HH) (EE G X e) (FF G X f) (ev' G X))

theorem tder2_Pv : tder G (D2 X) X (Pv (HH) (EE G X e) (FF G X f) (ev' G X)) = 0 := by
  rw [Pv, map_sub, map_sum, tder2_ev, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  refine tder_act_zero G X (D2 X) _ _ ?_ (tder_inclG G X (D2 X) _)
  exact tder_pairG_zero G X (D2 X) _ _ (tder_inclG G X (D2 X) _) (tder2_ev G X)

theorem tder2_qq : tder G (D2 X) (𝟙_ C) (qq G X e f) =
    ((HH).map (λ_ X).inv).hom (Pv (HH) (EE G X e) (FF G X f) (ev' G X)) := by
  rw [qq, tder_pairG, tder2_Pv, tder2_fv, TensorProduct.tmul_zero, map_zero, map_zero, zero_add, zig_apply]

/-- **Step A**: `q^{k+1} = 0 ⟹ q^k · P e' = 0`. -/
theorem stepA (k : ℕ) (h : pw G (qq G X e f) (k + 1) = 0) :
    act (HH) (pw G (qq G X e f) k) (Pv (HH) (EE G X e) (FF G X f) (ev' G X)) = 0 := by
  have h1 := congrArg (tder G (D2 X) (𝟙_ C)) h
  rw [tder_pw, map_zero, tder2_qq, ← act_natural] at h1
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (by exact_mod_cast Nat.succ_ne_zero k)
  · have := congrArg ((HH).map (λ_ X).hom).hom h2
    rwa [map_map_apply, Iso.inv_hom_id, (HH).map_id, map_zero] at this

theorem orthoH (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) (i j : Fin m) :
    pairG (HH) (FF G X f i) (EE G X e j) = if i = j then (ε (HH)).hom 1 else 0 := by
  have : pairG (HH) (FF G X f i) (EE G X e j) = inclG G (SB) (𝟙_ C) (pairG G (f i) (e j)) := by
    simp only [pairG, FF, EE]
    rw [inclG_μ, inclG_map]
  rw [this, horth]
  split_ifs
  · rfl
  · exact map_zero _

theorem tder1_pairG_FF_ev (j : Fin m) :
    tder G (D1 X) (𝟙_ C) (pairG (HH) (FF G X f j) (ev' G X)) = ((HH).map (λ_ Xᘁ).inv).hom (FF G X f j) := by
  rw [tder_pairG, tder1_ev, FF, tder_inclG, TensorProduct.zero_tmul, map_zero, map_zero, add_zero,
    map_map_apply, ← FF, contr_eta]

theorem tder1_Pv : tder G (D1 X) X (Pv (HH) (EE G X e) (FF G X f) (ev' G X)) =
    defect (HH) (EE G X e) (FF G X f) := by
  rw [Pv, map_sub, map_sum, tder1_ev, defect]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tder_act, EE, tder_inclG, act_zero_right, zero_add, tder1_pairG_FF_ev, ← EE, tmulT]
  exact tmulT_lam (HH) _ _

theorem tder1_qq : tder G (D1 X) (𝟙_ C) (qq G X e f) =
    ((HH).map (λ_ Xᘁ).inv).hom (Pc (HH) (EE G X e) (FF G X f) (fv' G X)) := by
  rw [qq, tder_pairG, tder1_fv, TensorProduct.zero_tmul, map_zero, map_zero, add_zero, tder1_Pv,
    map_map_apply, defect, TensorProduct.tmul_sub, TensorProduct.tmul_sum, map_sub, map_sub, map_sum, map_sum,
    contr_eta, Pc, map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contr_prod, μ_unit_left_act]

/-- The trace `tr = H(β ≫ ε) : H(X ⊗ Xᘁ) → H 𝟙`. -/
abbrev trH : (HH).obj (X ⊗ Xᘁ) ⟶ (HH).obj (𝟙_ C) := (HH).map ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ)

theorem trH_μ (v : (HH).obj X) (g : (HH).obj Xᘁ) :
    (trH G X).hom ((μ (HH) X Xᘁ).hom (v ⊗ₜ g)) = pairG (HH) g v := by
  rw [trH, map_comp_apply, μ_braid_apply]
  rfl

theorem trH_η {n : ℕ} (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ C)) :
    (trH G X).hom (((HH).map (η_ X Xᘁ)).hom ((ε (HH)).hom 1)) = (n : ℂ) • (ε (HH)).hom 1 := by
  rw [trH, map_map_apply, htr, Functor.map_smul, (HH).map_id]
  rfl

theorem trH_defect {n : ℕ} (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ C))
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) :
    (trH G X).hom (defect (HH) (EE G X e) (FF G X f)) = ((n : ℂ) - m) • (ε (HH)).hom 1 := by
  rw [defect, map_sub, map_sum, trH_η G X htr]
  rw [Finset.sum_congr rfl (fun j _ => by rw [trH_μ, orthoH G X e f horth, if_pos rfl])]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, sub_smul, ← Nat.cast_smul_eq_nsmul ℂ]

/-- **Step B**: `q^k · P e' = 0 ⟹ q^k = 0` (given `n > m`). -/
theorem stepB {n : ℕ} (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ C)) (hmn : m < n)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) (k : ℕ)
    (h : act (HH) (pw G (qq G X e f) k) (Pv (HH) (EE G X e) (FF G X f) (ev' G X)) = 0) :
    pw G (qq G X e f) k = 0 := by
  have horthH := orthoH G X e f horth
  have h1 := congrArg (tder G (D1 X) X) h
  rw [tder_act, map_zero, tder1_Pv] at h1
  have h2 := congrArg (trH G X).hom h1
  rw [map_add, map_zero, act_natural, trH_defect G X e f htr horth, act_smul_right, act_unit_right] at h2
  have key : (trH G X).hom (tmulT G (tder G (D1 X) (𝟙_ C) (pw G (qq G X e f) k))
      (Pv (HH) (EE G X e) (FF G X f) (ev' G X))) = (k : ℂ) • pw G (qq G X e f) k := by
    cases k with
    | zero =>
      simp only [pw, tder_unit_one, tmulT_zero, map_zero, Nat.cast_zero, zero_smul]
    | succ j =>
      rw [tder_pw, tder1_qq, tmulT_smul_left, tmulT_act_left, tmulT, tmulT_lam, map_smul,
        act_natural, trH_μ, pairG_Pc_Pv (HH) _ _ horthH, act_comm]
      rfl
  rw [key, ← add_smul] at h2
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have : ((n : ℂ) - m + k) = ((n - m + k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hmn.le]; ring
    rw [this] at h3
    exact absurd h3 (by exact_mod_cast (show n - m + k ≠ 0 by omega))
  · exact h3

/-- **The pivot is not nilpotent**: `q^k ≠ 0` for all `k`. -/
theorem pw_ne_zero {n : ℕ} (htr : η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = (n : ℂ) • 𝟙 (𝟙_ C)) (hmn : m < n)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) (hne : (ε G).hom 1 ≠ 0) :
    ∀ k, pw G (qq G X e f) k ≠ 0
  | 0 => by
    intro h
    apply hne
    apply inclG_injective G (SB) (𝟙_ C)
    rw [map_zero, ← inclG_ε]
    exact h
  | k + 1 => by
    intro h
    exact pw_ne_zero htr hmn horth hne k (stepB G X e f htr hmn horth k (stepA G X e f k h))

end CruxMain

end VOA.Huang.TensorCat.DeligneFiber
