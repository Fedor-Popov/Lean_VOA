/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneIntegral

/-!
# Deligne's theorem — the determinant object

In a symmetric fusion category over `ℂ` with positive braided dimensions:

* `symDim_dual` — `symDim Xᘁ = symDim X` (any braided category: swap the pairing);
* `one_le_symDim` — a nonzero object has `symDim ≥ 1`;
* `simple_of_symDim_eq_one` — an object of dimension `1` is simple;
* `tensor_dual_iso_unit_of_symDim_eq_one` — an object `L` of dimension `1` is invertible:
  `L ⊗ Lᘁ ≅ 𝟙`;
* `det_invertible` — the **determinant** `det X = Λ^{dim X} X` has dimension `1`, hence
  `det X ⊗ (det X)ᘁ ≅ 𝟙`.

These are the inputs (`Λ^{n+1} X = 0` — `isZero_extPow_of_lt` — and `Λ^n X` invertible) of
Deligne's construction of a fiber functor (the algebra of frames `Sym(X ⊗ ℂ^{n*})[det⁻¹]`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]

/-- The braided trace of `𝟙_{Xᘁ}` equals that of `𝟙_X` (compute with the swapped pairing). -/
theorem trMor_id_dual (X : C) : trMor (𝟙 Xᘁ) = trMor (𝟙 X) := by
  rw [trMor_eq_trWith (𝟙 Xᘁ) (BraidedCategory.exactPairing_swap X Xᘁ)]
  simp only [trWith, trMor, id_whiskerRight, Category.id_comp]
  change (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = _
  simp

end Braided

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

theorem symDim_dual (X : D) : symDim Xᘁ = symDim X := by
  rw [symDim_eq_toScalar, symDim_eq_toScalar, trMor_id_dual]

variable (hpos : ∀ i, 0 < (symDim (F.simple i)).re)
include hpos

/-- A nonzero object has dimension at least `1`. -/
theorem one_le_symDim {X : D} (hX : ¬ IsZero X) : ∃ n : ℕ, 1 ≤ n ∧ symDim X = n := by
  obtain ⟨n, hn⟩ := symDim_eq_nat hpos X
  refine ⟨n, ?_, hn⟩
  have := re_symDim_pos hpos hX
  rw [hn, Complex.natCast_re] at this
  exact_mod_cast this

/-- The single summand of a biproduct over `Fin 1`. -/
def biproductFinOneIso (f : Fin 1 → D) : (⨁ f) ≅ f 0 where
  hom := biproduct.π f 0
  inv := biproduct.ι f 0
  hom_inv_id := by
    rw [← biproduct.total, Fin.sum_univ_one]
  inv_hom_id := biproduct.ι_π_self f 0

/-- An object of dimension `1` is simple. -/
theorem simple_of_symDim_eq_one {X : D} (h : symDim X = 1) : Simple X := by
  obtain ⟨m, f, ⟨e⟩⟩ := F.semisimple X
  have hsum := symDim_of_iso_biproduct e
  rw [h] at hsum
  -- every summand has dimension a positive integer
  have hge : ∀ k, ∃ n : ℕ, 1 ≤ n ∧ symDim (F.simple (f k)) = n := fun k => by
    obtain ⟨n, hn, hd⟩ := symDim_simple_nat hpos (f k)
    exact ⟨n, hn, hd⟩
  choose n hn hd using hge
  rw [Finset.sum_congr rfl fun k _ => hd k] at hsum
  have hsumN : (∑ k, n k : ℕ) = 1 := by exact_mod_cast hsum.symm
  have hm : m = 1 := by
    have h1 : m ≤ ∑ k, n k := by
      calc m = ∑ _k : Fin m, 1 := by simp
        _ ≤ ∑ k, n k := Finset.sum_le_sum fun k _ => hn k
    rcases Nat.lt_or_ge m 1 with h0 | h0
    · obtain rfl : m = 0 := by omega
      simp at hsumN
    · omega
  subst hm
  haveI := F.isSimple (f 0)
  exact Simple.of_iso (e ≪≫ biproductFinOneIso _)

/-- An object of dimension `1` is invertible: `L ⊗ Lᘁ ≅ 𝟙`. -/
theorem tensor_dual_iso_unit_of_symDim_eq_one {L : D} (h : symDim L = 1) :
    Nonempty (L ⊗ Lᘁ ≅ 𝟙_ D) := by
  haveI : Simple (L ⊗ Lᘁ) := simple_of_symDim_eq_one hpos (by
    rw [symDim_tensor, symDim_dual, h, one_mul])
  haveI := F.isSimple F.unitLabel
  haveI : Simple (𝟙_ D) := Simple.of_iso F.unitIso.symm
  have hη : η_ L Lᘁ ≠ 0 := by
    intro h0
    have hz := ExactPairing.evaluation_coevaluation L Lᘁ
    rw [h0, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp] at hz
    have hL : 𝟙 L = 0 := by
      have := congrArg (fun g => (λ_ L).inv ≫ g ≫ (ρ_ L).hom) hz
      simpa using this.symm
    have hLz : IsZero L := (IsZero.iff_id_eq_zero L).mpr hL
    rw [symDim_of_isZero hLz] at h
    exact zero_ne_one h
  haveI := isIso_of_hom_simple hη
  exact ⟨(asIso (η_ L Lᘁ)).symm⟩

/-- The **determinant** `det X = Λ^{dim X} X` is invertible. -/
theorem det_invertible (X : D) {n : ℕ} (hn : symDim X = n) :
    symDim (extPow X n) = 1 ∧ Nonempty (extPow X n ⊗ (extPow X n)ᘁ ≅ 𝟙_ D) := by
  have h1 : symDim (extPow X n) = 1 := by
    rw [symDim_extPow, hn, descPochhammer_eval_eq_descFactorial ℂ n n, Nat.descFactorial_self]
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  exact ⟨h1, tensor_dual_iso_unit_of_symDim_eq_one hpos h1⟩

end VOA.Huang.TensorCat
