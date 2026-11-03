/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberGraded

/-!
# Deligne's fiber functor — polarization derivations of the symmetric algebra

For a morphism `φ : V ⟶ W`, the **polarization** `d_k = (k+1)·(π_k ⊗ φ) ∘ ι_{k+1} :
S^{k+1}V ⟶ S^k V ⊗ W` is a derivation of `Sym V` with values in the "tail" `W`:

* `symD_leib_both`, `symD_leib_left`, `symD_leib_right` — the Leibniz rule on `S^a ⊗ S^b`
  (the coset recursion of the symmetrizer splits the strands into the two blocks; the second block
  by `whiskerLeft_cycI_cat`, the first by the strand-moving lemma `cat_cycI_mv`);
* the generic structure `GCDer B W` (a derivation of a graded commutative monoid) and the derived
  derivation `tder` of `tensorG G B` with `tder_μ` (Leibniz, in the form of the square-zero
  extension `sqZero`), `tder_map`, `tder_ε`.

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

section SymDer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [HasKernels C]
  {V W : C} (φ : V ⟶ W)

/-- The polarization `d_k : S^{k+1} V ⟶ S^k V ⊗ W`. -/
def symD (k : ℕ) : symPow V (k + 1) ⟶ symPow V k ⊗ W :=
  ((k + 1 : ℂ)) • (symι V (k + 1) ≫ (symπ V k ⊗ₘ φ))

theorem sum_cycI_symL (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (cycI V (k + 1) j (k - j) ≫ (symL V k ▷ V : tpow V (k + 1) ⟶ tpow V (k + 1))) =
      ((k + 1 : ℂ)) • symL V (k + 1) := by
  rw [symL_succ, smul_smul, mul_inv_cancel₀ (by norm_cast), one_smul]

theorem tensorHom_smul_right {P Q R S : C} (f : P ⟶ Q) (c : ℂ) (g : R ⟶ S) : f ⊗ₘ (c • g) = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

theorem tensorHom_smul_left {P Q R S : C} (c : ℂ) (f : P ⟶ Q) (g : R ⟶ S) : (c • f) ⊗ₘ g = c • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

theorem absorbL_π (a b : ℕ) : (tpow V a ◁ symL V b) ≫ cat V a b ≫ symπ V (a + b) = cat V a b ≫ symπ V (a + b) := by
  rw [← symL_symπ (a + b), symL_whiskerLeft_absorb_assoc]

theorem absorbR_π (a b : ℕ) : (symL V a ▷ tpow V b) ≫ cat V a b ≫ symπ V (a + b) = cat V a b ≫ symπ V (a + b) := by
  rw [← symL_symπ (a + b), symL_whiskerRight_absorb_assoc]

/-- `cat a (b'+1) ≫ (π ⊗ φ) = α⁻¹ ≫ ((cat a b' ≫ π) ⊗ φ)`. -/
theorem cat_succ_tail (a b' : ℕ) :
    cat V a (b' + 1) ≫ (symπ V (a + b') ⊗ₘ φ) = (α_ _ _ _).inv ≫ ((cat V a b' ≫ symπ V (a + b')) ⊗ₘ φ) := by
  rw [cat_succ, Category.assoc, whiskerRight_comp_tensorHom]

/-- Inserting `σ_{b'}` on the second block (tail `φ` on the last strand). -/
theorem ins_right {P Q : C} {a b' : ℕ} (f : P ⟶ tpow V a) (g : Q ⟶ tpow V (b' + 1)) :
    (f ⊗ₘ (g ≫ (symL V b' ▷ V : tpow V (b' + 1) ⟶ tpow V (b' + 1)))) ≫ cat V a (b' + 1) ≫
        (symπ V (a + b') ⊗ₘ φ) = (f ⊗ₘ g) ≫ cat V a (b' + 1) ≫ (symπ V (a + b') ⊗ₘ φ) := by
  rw [← tensorHom_comp_whiskerLeft, Category.assoc, cat_succ_tail]
  congr 1
  have hn := associator_inv_naturality_middle (tpow V a) (symL V b') V
  erw [reassoc_of% hn]
  rw [whiskerRight_comp_tensorHom, absorbL_π]

/-- Inserting `σ_{a'}` on the first `a'` strands before moving the last strand of the block. -/
theorem ins_left {P Q : C} {a' b : ℕ} (g : P ⟶ tpow V (a' + 1)) (f : Q ⟶ tpow V b) :
    ((g ≫ (symL V a' ▷ V : tpow V (a' + 1) ⟶ tpow V (a' + 1))) ⊗ₘ f) ≫ tauSq V (tpow V a') (tpow V b) ≫
        ((cat V a' b ≫ symπ V (a' + b)) ⊗ₘ φ) =
      (g ⊗ₘ f) ≫ tauSq V (tpow V a') (tpow V b) ≫ ((cat V a' b ≫ symπ V (a' + b)) ⊗ₘ φ) := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc]
  congr 1
  erw [reassoc_of% (tauSq_natural_left V (symL V a') (tpow V b))]
  rw [whiskerRight_comp_tensorHom, absorbR_π]

theorem tauSq_tail (Y Y' : C) : ((Y ◁ φ) ▷ Y') ≫ tauSq W Y Y' = tauSq V Y Y' ≫ ((Y ⊗ Y') ◁ φ) := by
  simp only [tauSq, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp_assoc, associator_inv_naturality_right]

/-- The second-block part of the polarization of a product. -/
theorem symD_SB (a b' : ℕ) :
    ∑ j ∈ Finset.range (b' + 1), (symι V a ⊗ₘ symι V (b' + 1)) ≫ cat V a (b' + 1) ≫
        cycI V (a + b' + 1) (a + j) (b' - j) ≫ (symπ V (a + b') ⊗ₘ φ) =
      (symPow V a ◁ symD φ b') ≫ (α_ _ _ _).inv ≫ (symMul V a b' ▷ W) := by
  have hterm : ∀ j ∈ Finset.range (b' + 1), (symι V a ⊗ₘ symι V (b' + 1)) ≫ cat V a (b' + 1) ≫
      cycI V (a + b' + 1) (a + j) (b' - j) ≫ (symπ V (a + b') ⊗ₘ φ) =
      (symι V a ⊗ₘ (symι V (b' + 1) ≫ cycI V (b' + 1) j (b' - j) ≫
        (symL V b' ▷ V : tpow V (b' + 1) ⟶ tpow V (b' + 1)))) ≫ cat V a (b' + 1) ≫ (symπ V (a + b') ⊗ₘ φ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← Category.assoc (symι V (b' + 1)), ins_right, ← tensorHom_comp_whiskerLeft, Category.assoc,
      ← Category.assoc (tpow V a ◁ _), whiskerLeft_cycI_cat a (b' + 1) (b' - j) j (by omega)]
    simp only [Category.assoc]
    rfl
  rw [Finset.sum_congr rfl hterm, ← Preadditive.sum_comp, ← tensor_sum, ← Preadditive.comp_sum,
    sum_cycI_symL, Linear.comp_smul, symι_symL, tensorHom_smul_right, Linear.smul_comp]
  rw [symD, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  congr 1
  rw [cat_succ_tail, symMul_def]
  -- left side: `(ι_a ⊗ ι) ≫ α⁻¹ ≫ ((cat ≫ π) ⊗ φ)`
  have hπ : (symPow V a ◁ symπ V b') ≫ (symι V a ⊗ₘ symι V b') ≫ cat V a b' ≫ symπ V (a + b') =
      (symι V a ▷ tpow V b') ≫ cat V a b' ≫ symπ V (a + b') := by
    rw [whiskerLeft_comp_tensorHom_assoc, symπ_symι, ← Category.id_comp (symL V b'), symL_tensor_absorb_right,
      tensorHom_id]
  have hα : (symPow V a ◁ (symπ V b' ⊗ₘ φ)) ≫ (α_ _ _ _).inv = (α_ _ _ _).inv ≫ ((symPow V a ◁ symπ V b') ⊗ₘ φ) := by
    have := associator_inv_naturality (𝟙 (symPow V a)) (symπ V b') φ
    rwa [id_tensorHom, id_tensorHom] at this
  symm
  calc (symPow V a ◁ (symι V (b' + 1) ≫ (symπ V b' ⊗ₘ φ))) ≫ (α_ _ _ _).inv ≫
        (((symι V a ⊗ₘ symι V b') ≫ cat V a b' ≫ symπ V (a + b')) ▷ W)
      = (symPow V a ◁ symι V (b' + 1)) ≫ ((symPow V a ◁ (symπ V b' ⊗ₘ φ)) ≫ (α_ _ _ _).inv) ≫
          (((symι V a ⊗ₘ symι V b') ≫ cat V a b' ≫ symπ V (a + b')) ▷ W) := by
        rw [whiskerLeft_comp]; simp only [Category.assoc]
    _ = (symPow V a ◁ symι V (b' + 1)) ≫ (α_ _ _ _).inv ≫
          (((symι V a ▷ tpow V b') ≫ cat V a b' ≫ symπ V (a + b')) ⊗ₘ φ) := by
        rw [hα, Category.assoc, tensorHom_comp_whiskerRight, hπ]
    _ = (symι V a ⊗ₘ symι V (b' + 1)) ≫ (α_ _ _ _).inv ≫ ((cat V a b' ≫ symπ V (a + b')) ⊗ₘ φ) := by
        rw [tensorHom_def' (symι V a), Category.assoc]
        congr 1
        erw [reassoc_of% (associator_inv_naturality_left (symι V a) (tpow V b') V)]
        rw [whiskerRight_comp_tensorHom]

/-- The first-block part of the polarization of a product (strand moved past the second block). -/
theorem symD_FB (a' b : ℕ) :
    ∑ j ∈ Finset.range (a' + 1), (symι V (a' + 1) ⊗ₘ symι V b) ≫ cat V (a' + 1) b ≫
        cycI V (a' + 1 + b) j (a' + b - j) ≫ castT V (Nat.succ_add a' b) ≫ (symπ V (a' + b) ⊗ₘ φ) =
      (symD φ a' ▷ symPow V b) ≫ tauSq W (symPow V a') (symPow V b) ≫ (symMul V a' b ▷ W) := by
  have hterm : ∀ j ∈ Finset.range (a' + 1), (symι V (a' + 1) ⊗ₘ symι V b) ≫ cat V (a' + 1) b ≫
      cycI V (a' + 1 + b) j (a' + b - j) ≫ castT V (Nat.succ_add a' b) ≫ (symπ V (a' + b) ⊗ₘ φ) =
      ((symι V (a' + 1) ≫ cycI V (a' + 1) j (a' - j) ≫ (symL V a' ▷ V : tpow V (a' + 1) ⟶ tpow V (a' + 1))) ⊗ₘ
        symι V b) ≫ tauSq V (tpow V a') (tpow V b) ≫ ((cat V a' b ≫ symπ V (a' + b)) ⊗ₘ φ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hc : cat V (a' + 1) b ≫ cycI V (a' + 1 + b) j (a' - j) =
        (cycI V (a' + 1) j (a' - j) ▷ tpow V b) ≫ cat V (a' + 1) b := by
      rw [whiskerRight_cat, extR_cycI (show j + (a' - j) < a' + 1 by omega)]
    rw [← Category.assoc (symι V (a' + 1)), ins_left, ← tensorHom_comp_whiskerRight, Category.assoc,
      show a' + b - j = (a' - j) + b by omega, cycI_add, show j + (a' - j) = a' by omega]
    simp only [Category.assoc]
    rw [reassoc_of% hc, reassoc_of% (cat_cycI_mv (X := V) a' b), whiskerRight_comp_tensorHom]
  rw [Finset.sum_congr rfl hterm, ← Preadditive.sum_comp, ← sum_tensor, ← Preadditive.comp_sum,
    sum_cycI_symL, Linear.comp_smul, symι_symL, tensorHom_smul_left, Linear.smul_comp]
  rw [symD, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  congr 1
  have hπ : (symπ V a' ▷ symPow V b) ≫ (symι V a' ⊗ₘ symι V b) ≫ cat V a' b ≫ symπ V (a' + b) =
      (tpow V a' ◁ symι V b) ≫ cat V a' b ≫ symπ V (a' + b) := by
    rw [whiskerRight_comp_tensorHom_assoc, symπ_symι, ← Category.id_comp (symL V a'), symL_tensor_absorb_left,
      id_tensorHom]
  symm
  calc (symι V (a' + 1) ≫ (symπ V a' ⊗ₘ φ)) ▷ symPow V b ≫ tauSq W (symPow V a') (symPow V b) ≫
        (symMul V a' b ▷ W)
      = (symι V (a' + 1) ▷ symPow V b) ≫ ((symπ V a' ▷ V) ▷ symPow V b) ≫
          (((symPow V a' ◁ φ) ▷ symPow V b) ≫ tauSq W (symPow V a') (symPow V b)) ≫ (symMul V a' b ▷ W) := by
        rw [tensorHom_def, comp_whiskerRight, comp_whiskerRight]; simp only [Category.assoc]
    _ = (symι V (a' + 1) ▷ symPow V b) ≫ (((symπ V a' ▷ V) ▷ symPow V b) ≫ tauSq V (symPow V a') (symPow V b)) ≫
          ((symPow V a' ⊗ symPow V b) ◁ φ) ≫ (symMul V a' b ▷ W) := by
        rw [tauSq_tail]; simp only [Category.assoc]
    _ = (symι V (a' + 1) ▷ symPow V b) ≫ tauSq V (tpow V a') (symPow V b) ≫
          (((symπ V a' ▷ symPow V b) ≫ symMul V a' b) ⊗ₘ φ) := by
        rw [tauSq_natural_left]
        simp only [Category.assoc]
        rw [whisker_exchange, tensorHom_def, comp_whiskerRight]
        simp only [Category.assoc]
    _ = (symι V (a' + 1) ⊗ₘ symι V b) ≫ tauSq V (tpow V a') (tpow V b) ≫ ((cat V a' b ≫ symπ V (a' + b)) ⊗ₘ φ) := by
        rw [symMul_def, hπ, tensorHom_def (symι V (a' + 1)), Category.assoc]
        congr 1
        erw [reassoc_of% (tauSq_natural_right V (tpow V a') (symι V b))]
        rw [whiskerRight_comp_tensorHom]

/-- Expansion of `π ≫ d` by the coset recursion. -/
theorem comp_symπ_symD {P : C} (n : ℕ) (f : P ⟶ tpow V (n + 1)) :
    f ≫ symπ V (n + 1) ≫ symD φ n =
      ∑ j ∈ Finset.range (n + 1), f ≫ cycI V (n + 1) j (n - j) ≫ (symπ V n ⊗ₘ φ) := by
  rw [symD, Linear.comp_smul, Linear.comp_smul, ← Category.assoc (symπ V (n + 1)), symπ_symι, symL_succ,
    Linear.smul_comp, Linear.comp_smul, smul_smul, mul_inv_cancel₀ (by norm_cast), one_smul,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Category.assoc, whiskerRight_comp_tensorHom, symL_symπ]

theorem tail_cast {m m' : ℕ} (h : m' = m) :
    castT V (show m' + 1 = m + 1 by rw [h]) ≫ (symπ V m ⊗ₘ φ) ≫ (eqToHom (congrArg (symPow V) h.symm) ▷ W) =
      symπ V m' ⊗ₘ φ := by
  subst h; simp [castT]

/-- **Leibniz rule** (both factors of positive degree). -/
theorem symD_leib_both (a b : ℕ) :
    symMul V (a + 1) (b + 1) ≫ symD φ (a + 1 + b) =
      (symPow V (a + 1) ◁ symD φ b) ≫ (α_ _ _ _).inv ≫ (symMul V (a + 1) b ▷ W) +
        (symD φ a ▷ symPow V (b + 1)) ≫ tauSq W (symPow V a) (symPow V (b + 1)) ≫ (symMul V a (b + 1) ▷ W) ≫
          (eqToHom (congrArg (symPow V) (show a + (b + 1) = a + 1 + b by omega)) ▷ W) := by
  rw [symMul_def]
  have h := comp_symπ_symD φ (a + 1 + b) ((symι V (a + 1) ⊗ₘ symι V (b + 1)) ≫ cat V (a + 1) (b + 1))
  simp only [Category.assoc] at h
  simp only [Category.assoc]
  erw [h]
  rw [show Finset.range (a + 1 + b + 1) = Finset.range ((a + 1) + (b + 1)) from rfl,
    Finset.sum_range_add]
  refine (add_comm _ _).trans ?_
  congr 1
  · rw [← symD_SB φ (a + 1) b]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show a + 1 + b - (a + 1 + j) = b - j by omega]
  · rw [← reassoc_of% (symD_FB φ a (b + 1)), Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [Category.assoc]
    rw [show a + 1 + b - j = a + (b + 1) - j by omega]
    congr 3
    exact (tail_cast φ (show a + 1 + b = a + (b + 1) by omega)).symm

/-- Leibniz rule, second factor of degree `0`. -/
theorem symD_leib_left (a : ℕ) :
    symMul V (a + 1) 0 ≫ symD φ a =
      (symD φ a ▷ symPow V 0) ≫ tauSq W (symPow V a) (symPow V 0) ≫ (symMul V a 0 ▷ W) := by
  rw [symMul_def]
  have h := comp_symπ_symD φ a ((symι V (a + 1) ⊗ₘ symι V 0) ≫ cat V (a + 1) 0)
  simp only [Category.assoc] at h
  simp only [Category.assoc]
  erw [h]
  rw [← symD_FB φ a 0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [castT_self, Category.id_comp]
  rfl

/-- Leibniz rule, first factor of degree `0`. -/
theorem symD_leib_right (b : ℕ) :
    symMul V 0 (b + 1) ≫ symD φ (0 + b) =
      (symPow V 0 ◁ symD φ b) ≫ (α_ _ _ _).inv ≫ (symMul V 0 b ▷ W) := by
  rw [symMul_def]
  have h := comp_symπ_symD φ (0 + b) ((symι V 0 ⊗ₘ symι V (b + 1)) ≫ cat V 0 (b + 1))
  simp only [Category.assoc] at h
  simp only [Category.assoc]
  erw [h]
  rw [← symD_SB φ 0 b, show Finset.range (0 + b + 1) = Finset.range (b + 1) by simp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 0 + b - j = b - j by omega, Nat.zero_add j]

end SymDer

section Coherence

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

theorem pureR (A Y K W Z : C) :
    tensorμ A Y (K ⊗ W) Z ≫ ((α_ A K W).inv ▷ (Y ⊗ Z)) ≫ (α_ (A ⊗ K) W (Y ⊗ Z)).hom ≫
        ((A ⊗ K) ◁ (β_ W (Y ⊗ Z)).hom) =
      ((A ⊗ Y) ◁ ((α_ K W Z).hom ≫ (K ◁ (β_ W Z).hom))) ≫ tensorμ A Y K (Z ⊗ W) ≫
        ((A ⊗ K) ◁ (α_ Y Z W).inv) := by
  calc _ = 𝟙 _ ⊗≫ (A ◁ (β_ Y K).hom ▷ W ▷ Z) ⊗≫ (A ◁ K ◁ ((β_ Y W).hom ≫ (β_ W Y).hom) ▷ Z) ⊗≫
          (A ◁ K ◁ Y ◁ (β_ W Z).hom) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight, whiskerLeft_comp]
        monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ ((β_ Y K).hom ▷ (W ⊗ Z) ≫ (K ⊗ Y) ◁ (β_ W Z).hom)) ⊗≫ 𝟙 _ := by
        rw [SymmetricCategory.symmetry]
        monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ ((Y ⊗ K) ◁ (β_ W Z).hom ≫ (β_ Y K).hom ▷ (Z ⊗ W))) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = _ := by
        simp only [tensorμ, BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight, whiskerLeft_comp]
        monoidal

theorem pureL (K W Y B Z : C) :
    tensorμ (K ⊗ W) Y B Z ≫ (tauSq W K B ▷ (Y ⊗ Z)) ≫ (α_ (K ⊗ B) W (Y ⊗ Z)).hom ≫
        ((K ⊗ B) ◁ (β_ W (Y ⊗ Z)).hom) =
      (((α_ K W Y).hom ≫ (K ◁ (β_ W Y).hom)) ▷ (B ⊗ Z)) ≫ tensorμ K (Y ⊗ W) B Z ≫
        ((K ⊗ B) ◁ tauSq W Y Z) := by
  calc _ = 𝟙 _ ⊗≫ (K ◁ ((W ◁ (β_ Y B).hom) ≫ (β_ W (B ⊗ Y)).hom) ▷ Z) ⊗≫ (K ◁ B ◁ Y ◁ (β_ W Z).hom) ⊗≫ 𝟙 _ := by
        simp only [tensorμ, tauSq, BraidedCategory.braiding_tensor_right_hom, comp_whiskerRight,
          whiskerLeft_comp]
        monoidal
    _ = 𝟙 _ ⊗≫ (K ◁ ((β_ W (Y ⊗ B)).hom ≫ ((β_ Y B).hom ▷ W)) ▷ Z) ⊗≫ (K ◁ B ◁ Y ◁ (β_ W Z).hom) ⊗≫ 𝟙 _ := by
        rw [BraidedCategory.braiding_naturality_right]
    _ = _ := by
        simp only [tensorμ, tauSq, BraidedCategory.braiding_tensor_right_hom,
          BraidedCategory.braiding_tensor_left_hom, comp_whiskerRight, whiskerLeft_comp]
        monoidal

theorem cohR {A Y Bb K N Z W : C} (e : Bb ⟶ K ⊗ W) (mm : A ⊗ K ⟶ N) :
    tensorμ A Y Bb Z ≫ (((A ◁ e) ≫ (α_ A K W).inv ≫ (mm ▷ W)) ▷ (Y ⊗ Z)) ≫ (α_ N W (Y ⊗ Z)).hom ≫
        (N ◁ (β_ W (Y ⊗ Z)).hom) =
      ((A ⊗ Y) ◁ ((e ▷ Z) ≫ (α_ K W Z).hom ≫ (K ◁ (β_ W Z).hom))) ≫ tensorμ A Y K (Z ⊗ W) ≫
        (mm ▷ (Y ⊗ (Z ⊗ W))) ≫ (N ◁ (α_ Y Z W).inv) := by
  have hn := tensorμ_natural_right A Y e (𝟙 Z)
  rw [tensorHom_id, MonoidalCategory.whiskerLeft_id, tensorHom_id] at hn
  calc _ = ((A ⊗ Y) ◁ (e ▷ Z)) ≫ (tensorμ A Y (K ⊗ W) Z ≫ ((α_ A K W).inv ▷ (Y ⊗ Z)) ≫
          (α_ (A ⊗ K) W (Y ⊗ Z)).hom ≫ ((A ⊗ K) ◁ (β_ W (Y ⊗ Z)).hom)) ≫ (mm ▷ ((Y ⊗ Z) ⊗ W)) := by
        simp only [comp_whiskerRight, Category.assoc]
        rw [← reassoc_of% hn, associator_naturality_left_assoc, ← whisker_exchange]
    _ = _ := by
        rw [pureR]
        simp only [whiskerLeft_comp, Category.assoc]
        rw [whisker_exchange]

theorem cohL {A' Y Bb K N Z W : C} (e : A' ⟶ K ⊗ W) (mm : K ⊗ Bb ⟶ N) :
    tensorμ A' Y Bb Z ≫ (((e ▷ Bb) ≫ tauSq W K Bb ≫ (mm ▷ W)) ▷ (Y ⊗ Z)) ≫ (α_ N W (Y ⊗ Z)).hom ≫
        (N ◁ (β_ W (Y ⊗ Z)).hom) =
      (((e ▷ Y) ≫ (α_ K W Y).hom ≫ (K ◁ (β_ W Y).hom)) ▷ (Bb ⊗ Z)) ≫ tensorμ K (Y ⊗ W) Bb Z ≫
        (mm ▷ ((Y ⊗ W) ⊗ Z)) ≫ (N ◁ tauSq W Y Z) := by
  have hn := tensorμ_natural_left e (𝟙 Y) Bb Z
  rw [tensorHom_id, id_whiskerRight, tensorHom_id] at hn
  calc _ = ((e ▷ Y) ▷ (Bb ⊗ Z)) ≫ (tensorμ (K ⊗ W) Y Bb Z ≫ (tauSq W K Bb ▷ (Y ⊗ Z)) ≫
          (α_ (K ⊗ Bb) W (Y ⊗ Z)).hom ≫ ((K ⊗ Bb) ◁ (β_ W (Y ⊗ Z)).hom)) ≫ (mm ▷ ((Y ⊗ Z) ⊗ W)) := by
        simp only [comp_whiskerRight, Category.assoc]
        rw [← reassoc_of% hn, associator_naturality_left_assoc, ← whisker_exchange]
    _ = _ := by
        rw [pureL]
        simp only [comp_whiskerRight, Category.assoc]
        rw [whisker_exchange]

end Coherence

section GCDer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]

/-- A **derivation** of a graded commutative monoid with values in the tail `W`. -/
structure GCDer (B : GCMon C) (W : C) where
  d : ∀ k, B.B (k + 1) ⟶ B.B k ⊗ W
  leib_both : ∀ a b, B.m (a + 1) (b + 1) ≫ d (a + 1 + b) =
    (B.B (a + 1) ◁ d b) ≫ (α_ _ _ _).inv ≫ (B.m (a + 1) b ▷ W) +
      (d a ▷ B.B (b + 1)) ≫ tauSq W (B.B a) (B.B (b + 1)) ≫ (B.m a (b + 1) ▷ W) ≫
        (B.castB (show a + (b + 1) = a + 1 + b by omega) ▷ W)
  leib_left : ∀ a, B.m (a + 1) 0 ≫ d a = (d a ▷ B.B 0) ≫ tauSq W (B.B a) (B.B 0) ≫ (B.m a 0 ▷ W)
  leib_right : ∀ b, B.m 0 (b + 1) ≫ d (0 + b) = (B.B 0 ◁ d b) ≫ (α_ _ _ _).inv ≫ (B.m 0 b ▷ W)

/-- The polarization derivation of `Sym V` along `φ : V ⟶ W`. -/
def symGCDer [HasKernels C] {V W : C} (φ : V ⟶ W) : GCDer (symGCMon V) W where
  d := symD φ
  leib_both := symD_leib_both φ
  leib_left := symD_leib_left φ
  leib_right := symD_leib_right φ

namespace GCDer

variable {B : GCMon C} {W : C} (D : GCDer B W)

/-- `Δ_k = (d_k ▷ Y) ≫ α ≫ (B_k ◁ β_{W,Y}) : B_{k+1} ⊗ Y ⟶ B_k ⊗ (Y ⊗ W)`. -/
def Δ (k : ℕ) (Y : C) : B.B (k + 1) ⊗ Y ⟶ B.B k ⊗ (Y ⊗ W) :=
  (D.d k ▷ Y) ≫ (α_ _ _ _).hom ≫ (B.B k ◁ (β_ W Y).hom)

theorem Δ_natural (k : ℕ) {Y Y' : C} (f : Y ⟶ Y') :
    (B.B (k + 1) ◁ f) ≫ D.Δ k Y' = D.Δ k Y ≫ (B.B k ◁ (f ▷ W)) := by
  simp only [Δ, Category.assoc]
  rw [whisker_exchange_assoc, associator_naturality_right_assoc, ← whiskerLeft_comp,
    BraidedCategory.braiding_naturality_right, whiskerLeft_comp]

theorem Φ_Δ_both (a b : ℕ) (Y Z : C) :
    B.Φ (a + 1) (b + 1) Y Z ≫ D.Δ (a + 1 + b) (Y ⊗ Z) =
      ((B.B (a + 1) ⊗ Y) ◁ D.Δ b Z) ≫ B.Φ (a + 1) b Y (Z ⊗ W) ≫ (B.B (a + 1 + b) ◁ (α_ Y Z W).inv) +
        (D.Δ a Y ▷ (B.B (b + 1) ⊗ Z)) ≫ B.Φ a (b + 1) (Y ⊗ W) Z ≫ (B.B (a + (b + 1)) ◁ tauSq W Y Z) ≫
          (B.castB (show a + (b + 1) = a + 1 + b by omega) ▷ ((Y ⊗ Z) ⊗ W)) := by
  have hL := D.leib_both a b
  calc B.Φ (a + 1) (b + 1) Y Z ≫ D.Δ (a + 1 + b) (Y ⊗ Z)
      = tensorμ _ _ _ _ ≫ ((B.m (a + 1) (b + 1) ≫ D.d (a + 1 + b)) ▷ (Y ⊗ Z)) ≫ (α_ _ _ _).hom ≫
          (B.B (a + 1 + b) ◁ (β_ W (Y ⊗ Z)).hom) := by
        simp only [GCMon.Φ, Δ, comp_whiskerRight, Category.assoc]
    _ = _ := by
        rw [hL, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]
        congr 1
        · rw [cohR]
          simp only [Δ, GCMon.Φ, Category.assoc]
        · rw [← comp_whiskerRight (B.m a (b + 1)), cohL]
          simp only [Δ, GCMon.Φ, comp_whiskerRight, Category.assoc]
          rw [whisker_exchange]

theorem Φ_Δ_left (a : ℕ) (Y Z : C) :
    B.Φ (a + 1) 0 Y Z ≫ D.Δ a (Y ⊗ Z) =
      (D.Δ a Y ▷ (B.B 0 ⊗ Z)) ≫ B.Φ a 0 (Y ⊗ W) Z ≫ (B.B (a + 0) ◁ tauSq W Y Z) := by
  have hL := D.leib_left a
  calc B.Φ (a + 1) 0 Y Z ≫ D.Δ a (Y ⊗ Z)
      = tensorμ _ _ _ _ ≫ ((B.m (a + 1) 0 ≫ D.d a) ▷ (Y ⊗ Z)) ≫ (α_ (B.B (a + 0)) W (Y ⊗ Z)).hom ≫
          (B.B (a + 0) ◁ (β_ W (Y ⊗ Z)).hom) := by
        simp only [GCMon.Φ, Δ, comp_whiskerRight, Category.assoc]
        rfl
    _ = _ := by
        rw [hL, cohL]
        simp only [Δ, GCMon.Φ, Category.assoc]

theorem Φ_Δ_right (b : ℕ) (Y Z : C) :
    B.Φ 0 (b + 1) Y Z ≫ D.Δ (0 + b) (Y ⊗ Z) =
      ((B.B 0 ⊗ Y) ◁ D.Δ b Z) ≫ B.Φ 0 b Y (Z ⊗ W) ≫ (B.B (0 + b) ◁ (α_ Y Z W).inv) := by
  have hL := D.leib_right b
  calc B.Φ 0 (b + 1) Y Z ≫ D.Δ (0 + b) (Y ⊗ Z)
      = tensorμ _ _ _ _ ≫ ((B.m 0 (b + 1) ≫ D.d (0 + b)) ▷ (Y ⊗ Z)) ≫ (α_ _ _ _).hom ≫
          (B.B (0 + b) ◁ (β_ W (Y ⊗ Z)).hom) := by
        simp only [GCMon.Φ, Δ, comp_whiskerRight, Category.assoc]
    _ = _ := by
        rw [hL, cohR]
        simp only [Δ, GCMon.Φ, Category.assoc]

end GCDer

end GCDer

section TensorDer

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] {B : GCMon C} {W : C} (D : GCDer B W)

/-- The components of the derivation. -/
def tderComp (Y : C) : (k : ℕ) → (tcomp G B Y k →ₗ[ℂ] tsum G B (Y ⊗ W))
  | 0 => 0
  | k + 1 => tlof G B (Y ⊗ W) k ∘ₗ (G.map (D.Δ k Y)).hom

/-- The derivation `∂ : A ⊗ Sym → (A ⊗ Sym) ⊗ W` of the free extension (tail `W`). -/
def tder (Y : C) : (tensorG G B).obj Y →ₗ[ℂ] (tensorG G B).obj (Y ⊗ W) :=
  DirectSum.toModule ℂ ℕ _ (tderComp G D Y)

theorem tder_lof_zero (Y : C) (x : tcomp G B Y 0) : tder G D Y (tlof G B Y 0 x) = 0 := by
  unfold tder tlof
  erw [DirectSum.toModule_lof]
  rfl

theorem tder_lof_succ (Y : C) (k : ℕ) (x : tcomp G B Y (k + 1)) :
    tder G D Y (tlof G B Y (k + 1) x) = tlof G B (Y ⊗ W) k ((G.map (D.Δ k Y)).hom x) := by
  unfold tder
  erw [DirectSum.toModule_lof]
  rfl

theorem tensorG_induction {Y : C} {P : (tensorG G B).obj Y → Prop} (h0 : P 0)
    (hof : ∀ k x, P (tlof G B Y k x)) (hadd : ∀ p q, P p → P q → P (p + q)) (p : (tensorG G B).obj Y) : P p :=
  DirectSum.induction_on (β := tcomp G B Y) (motive := P) p h0 (fun k x => hof k x) hadd

theorem tder_map_lof {Y Y' : C} (f : Y ⟶ Y') (k : ℕ) (x : tcomp G B Y k) :
    tder G D Y' (((tensorG G B).map f).hom (tlof G B Y k x)) =
      ((tensorG G B).map (f ▷ W)).hom (tder G D Y (tlof G B Y k x)) := by
  rw [tensorG_map_lof]
  cases k with
  | zero => rw [tder_lof_zero, tder_lof_zero, map_zero]
  | succ k =>
    rw [tder_lof_succ, tder_lof_succ, tensorG_map_lof, map_map_apply, map_map_apply, GCDer.Δ_natural]

theorem tder_map {Y Y' : C} (f : Y ⟶ Y') (p : (tensorG G B).obj Y) :
    tder G D Y' (((tensorG G B).map f).hom p) = ((tensorG G B).map (f ▷ W)).hom (tder G D Y p) := by
  induction p using tensorG_induction G with
  | h0 => simp
  | hof k x => exact tder_map_lof G D f k x
  | hadd p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem tder_ε (c : ℂ) : tder G D (𝟙_ C) ((ε (tensorG G B)).hom c) = 0 := by
  rw [tensorG_ε_apply, tder_lof_zero]

theorem tder_μ_lof (Y Z : C) (a b : ℕ) (x : tcomp G B Y a) (y : tcomp G B Z b) :
    tder G D (Y ⊗ Z) ((μ (tensorG G B) Y Z).hom (tlof G B Y a x ⊗ₜ tlof G B Z b y)) =
      mulSnd (tensorG G B) W Y Z (tlof G B Y a x, tder G D Y (tlof G B Y a x))
        (tlof G B Z b y, tder G D Z (tlof G B Z b y)) := by
  simp only [mulSnd]
  rw [tensorG_μ_lof]
  cases a with
  | zero =>
    cases b with
    | zero =>
      rw [tder_lof_zero, tder_lof_zero, tder_lof_zero]
      simp
    | succ b =>
      rw [tder_lof_zero, TensorProduct.zero_tmul, map_zero, map_zero, add_zero]
      change tder G D (Y ⊗ Z) (tlof G B (Y ⊗ Z) ((0 + b) + 1) _) = _
      rw [tder_lof_succ, tder_lof_succ, tensorG_μ_lof, tensorG_map_lof, ← μ_whiskerLeft_apply,
        map_map_apply, map_map_apply, map_map_apply]
      congr 2
      rw [← GCDer.Φ_Δ_right]
  | succ a =>
    cases b with
    | zero =>
      rw [tder_lof_zero, TensorProduct.tmul_zero, map_zero, map_zero, zero_add]
      change tder G D (Y ⊗ Z) (tlof G B (Y ⊗ Z) (a + 1) _) = _
      rw [tder_lof_succ, tder_lof_succ, tensorG_μ_lof, tensorG_map_lof, ← μ_whiskerRight_apply,
        map_map_apply, map_map_apply, map_map_apply]
      congr 2
      rw [GCDer.Φ_Δ_left]
    | succ b =>
      have e1 : ((tensorG G B).map (α_ Y Z W).inv).hom ((μ (tensorG G B) Y (Z ⊗ W)).hom
          (tlof G B Y (a + 1) x ⊗ₜ tder G D Z (tlof G B Z (b + 1) y))) =
          tlof G B ((Y ⊗ Z) ⊗ W) (a + 1 + b) ((G.map (((B.B (a + 1) ⊗ Y) ◁ D.Δ b Z) ≫
            B.Φ (a + 1) b Y (Z ⊗ W) ≫ (B.B (a + 1 + b) ◁ (α_ Y Z W).inv))).hom ((μ G _ _).hom (x ⊗ₜ y))) := by
        rw [tder_lof_succ, tensorG_μ_lof, tensorG_map_lof, ← μ_whiskerLeft_apply, map_map_apply,
          map_map_apply]
      have e2 : ((tensorG G B).map (tauSq W Y Z)).hom ((μ (tensorG G B) (Y ⊗ W) Z).hom
          (tder G D Y (tlof G B Y (a + 1) x) ⊗ₜ tlof G B Z (b + 1) y)) =
          tlof G B ((Y ⊗ Z) ⊗ W) (a + 1 + b) ((G.map ((D.Δ a Y ▷ (B.B (b + 1) ⊗ Z)) ≫
            B.Φ a (b + 1) (Y ⊗ W) Z ≫ (B.B (a + (b + 1)) ◁ tauSq W Y Z) ≫
            (B.castB (show a + (b + 1) = a + 1 + b by omega) ▷ ((Y ⊗ Z) ⊗ W)))).hom ((μ G _ _).hom (x ⊗ₜ y))) := by
        rw [tder_lof_succ, tensorG_μ_lof, tensorG_map_lof, tlof_cast G B _ (show a + (b + 1) = a + 1 + b by omega),
          ← μ_whiskerRight_apply, map_map_apply, map_map_apply, map_map_apply]
      rw [e1, e2]
      erw [← map_add]
      rw [ ← LinearMap.add_apply, ← ModuleCat.hom_add, ← G.map_add, ← GCDer.Φ_Δ_both]
      change tder G D (Y ⊗ Z) (tlof G B (Y ⊗ Z) ((a + 1 + b) + 1) _) = _
      rw [tder_lof_succ, map_map_apply]
      rfl

/-- **Leibniz rule** for the free extension, in square-zero form. -/
theorem tder_μ (Y Z : C) (p : (tensorG G B).obj Y) (q : (tensorG G B).obj Z) :
    tder G D (Y ⊗ Z) ((μ (tensorG G B) Y Z).hom (p ⊗ₜ q)) =
      mulSnd (tensorG G B) W Y Z (p, tder G D Y p) (q, tder G D Z q) := by
  induction p using tensorG_induction G with
  | h0 => simp [mulSnd]
  | hof a x =>
    induction q using tensorG_induction G with
    | h0 => simp [mulSnd]
    | hof b y => exact tder_μ_lof G D Y Z a b x y
    | hadd q q' hq hq' =>
      rw [TensorProduct.tmul_add, map_add, map_add, hq, hq']
      simp only [mulSnd, map_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
      abel
  | hadd p p' hp hp' =>
    rw [TensorProduct.add_tmul, map_add, map_add, hp, hp']
    simp only [mulSnd, map_add, TensorProduct.tmul_add, TensorProduct.add_tmul]
    abel

end TensorDer

end VOA.Huang.TensorCat.DeligneFiber
