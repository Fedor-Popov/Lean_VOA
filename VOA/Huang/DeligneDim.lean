/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneTrace
import VOA.Huang.DeligneNumeric

/-!
# Deligne's theorem, stages D2/D3 — the braided dimension in a symmetric fusion category

Let `D` be a symmetric fusion category over `ℂ` (T1 `FusionCategory`) whose simples have braided
dimension `symDim` of positive real part (the hypothesis of `DeligneTannakian`).

* `trMor_id_eq_smul` — `ε c η = symDim X • 𝟙`;
* `symDim_of_iso`, `symDim_biproduct`, `symDim_of_iso_biproduct`, `symDim_of_isZero`,
  `symDim_unit` (`= 1`), `symDim_tensor` (`symDim (X ⊗ Y) = symDim X · symDim Y`),
  `symDim_tpow` (`symDim X^{⊗n} = (symDim X)^n`);
* `re_symDim_pos` — under positivity, every nonzero object has `re symDim > 0`;
  `isZero_of_symDim_eq_zero`;
* `symDim_simple_real_pos` — under positivity, `symDim X_i` is a **positive real number**
  (apply `im_eq_zero_of_pow_re_pos` to the nonzero objects `X_i^{⊗n}`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

theorem symDim_eq_toScalar (X : D) : symDim X = toScalar (trMor (𝟙 X)) := by
  rw [trMor_id]; rfl

/-- `ε_X ∘ c_{X,Xᘁ} ∘ η_X = symDim X • 𝟙`. -/
theorem trMor_id_eq_smul (X : D) : trMor (𝟙 X) = symDim X • 𝟙 (𝟙_ D) := by
  rw [symDim_eq_toScalar, toScalar_smul_id FusionCategory.finrank_end_unit]

theorem symDim_eq_of_trMor {X : D} {c : ℂ} (h : trMor (𝟙 X) = c • 𝟙 (𝟙_ D)) : symDim X = c := by
  rw [symDim_eq_toScalar, h, toScalar_smul FusionCategory.finrank_end_unit]

theorem symDim_of_iso {X Y : D} (e : X ≅ Y) : symDim X = symDim Y := by
  rw [symDim_eq_toScalar, symDim_eq_toScalar, trMor_id_of_iso e]

theorem symDim_of_isZero {X : D} (hX : IsZero X) : symDim X = 0 := by
  apply symDim_eq_of_trMor
  rw [trMor_id_eq_zero_of_isZero hX, zero_smul]

theorem symDim_biproduct {J : Type} [Fintype J] (f : J → D) :
    symDim (⨁ f) = ∑ j, symDim (f j) := by
  apply symDim_eq_of_trMor
  rw [trMor_id_biproduct, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => trMor_id_eq_smul (f j)

theorem symDim_of_iso_biproduct {X : D} {J : Type} [Fintype J] {f : J → D} (e : X ≅ ⨁ f) :
    symDim X = ∑ j, symDim (f j) := by
  rw [symDim_of_iso e, symDim_biproduct]

/-- `symDim 𝟙 = 1`. -/
theorem symDim_unit : symDim (𝟙_ D) = 1 := by
  apply symDim_eq_of_trMor
  rw [trMor_eq_trWith (𝟙 (𝟙_ D)) exactPairingUnit, one_smul]
  simp only [trWith, id_whiskerRight, Category.id_comp]
  exact (by simp [unitors_inv_equal] : (ρ_ (𝟙_ D)).inv ≫ (β_ (𝟙_ D) (𝟙_ D)).hom ≫
    (ρ_ (𝟙_ D)).hom = 𝟙 _)

/-- **Multiplicativity**: `symDim (X ⊗ Y) = symDim X · symDim Y`. -/
theorem symDim_tensor (X Y : D) : symDim (X ⊗ Y) = symDim X * symDim Y := by
  apply symDim_eq_of_trMor
  have hY : trWith (inferInstance : ExactPairing Y Yᘁ) (𝟙 Y) = symDim Y • 𝟙 (𝟙_ D) := by
    rw [← trMor_eq_trWith]; exact trMor_id_eq_smul Y
  rw [trMor_eq_trWith (𝟙 (X ⊗ Y)) (tensorPairing X Xᘁ Y Yᘁ), ← id_tensorHom_id,
    trWith_tensor (inferInstance : ExactPairing X Xᘁ) (inferInstance : ExactPairing Y Yᘁ) _ _ hY,
    ← trMor_eq_trWith, trMor_id_eq_smul, smul_smul, mul_comm]

theorem symDim_tpow (X : D) (n : ℕ) : symDim (tpow X n) = symDim X ^ n := by
  induction n with
  | zero => exact symDim_unit
  | succ n ih => rw [tpow, symDim_tensor, ih, pow_succ]

/-- Under positivity on simples, every nonzero object has `re symDim > 0`. -/
theorem re_symDim_pos (hpos : ∀ i, 0 < (symDim (F.simple i)).re) {X : D} (hX : ¬ IsZero X) :
    0 < (symDim X).re := by
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
  rw [symDim_of_iso_biproduct e, Complex.re_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply hX
    refine IsZero.of_iso ((IsZero.iff_id_eq_zero _).mpr ?_) e
    rw [← biproduct.total]
    simp
  · exact Finset.sum_pos (fun k _ => hpos (f k)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem isZero_of_symDim_eq_zero (hpos : ∀ i, 0 < (symDim (F.simple i)).re) {X : D}
    (h : symDim X = 0) : IsZero X := by
  by_contra hX
  have := re_symDim_pos hpos hX
  rw [h, Complex.zero_re] at this
  exact lt_irrefl _ this

/-- Under positivity, the braided dimension of every simple object is a **positive real**. -/
theorem symDim_simple_real_pos (hpos : ∀ i, 0 < (symDim (F.simple i)).re) (i : F.ι) :
    (symDim (F.simple i)).im = 0 ∧ 0 < (symDim (F.simple i)).re := by
  apply Deligne.im_eq_zero_of_pow_re_pos
  intro n _
  have hd : symDim (F.simple i) ≠ 0 := fun h0 => by
    have := hpos i; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hnz : ¬ IsZero (tpow (F.simple i) n) := fun hz => by
    have := symDim_of_isZero hz
    rw [symDim_tpow] at this
    exact pow_ne_zero n hd this
  rw [← symDim_tpow]
  exact re_symDim_pos hpos hnz

end VOA.Huang.TensorCat
