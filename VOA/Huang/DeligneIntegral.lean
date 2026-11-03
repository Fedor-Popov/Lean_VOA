/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneDim
import VOA.Huang.DeligneExterior
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Deligne's theorem — braided dimensions are natural numbers

In a symmetric fusion category over `ℂ` whose simples have braided dimension of positive real part:

* `extPow X k` — the **exterior power** `Λ^k X`, the image of the antisymmetrizer `e_k` (idempotents
  split since the category has kernels), with `extPowι`/`extPowπ`;
* `symDim_extPow` — `symDim (Λ^k X) = d(d-1)⋯(d-k+1)/k!` with `d = symDim X`;
* `symDim_eq_nat` — `symDim X` is a natural number for **every** object `X`
  (Deligne's integrality: `Λ^k X` is zero or has positive dimension, and `d(d-1)⋯(d-k+1) ≥ 0` for
  all `k` forces `d ∈ ℕ`);
* `symDim_simple_nat` — `symDim X_i ∈ ℤ_{>0}` for every simple `X_i`;
* `isZero_extPow_of_lt` — `Λ^k X = 0` for `k > symDim X` (the key input of Deligne's fiber-functor
  construction).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module Polynomial

universe v u

theorem descPochhammer_eval_ofReal (k : ℕ) (x : ℝ) :
    (descPochhammer ℂ k).eval (x : ℂ) = (((descPochhammer ℝ k).eval x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [descPochhammer_succ_eval, descPochhammer_succ_eval, ih]; push_cast; ring

variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]

instance isIdempotentComplete_of_fusion : IsIdempotentComplete D :=
  (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels D).mpr fun _ _ _ => inferInstance

/-- A splitting of the antisymmetrizer `e_k = π ≫ ι`, `ι ≫ π = 𝟙`. -/
theorem antisym_split (X : D) (k : ℕ) : ∃ (Y : D) (i : Y ⟶ tpow X k) (e : tpow X k ⟶ Y),
    i ≫ e = 𝟙 Y ∧ e ≫ i = antisym X k :=
  IsIdempotentComplete.idempotents_split _ _ (antisym_idem k)

/-- The exterior power `Λ^k X` (image of the antisymmetrizer). -/
def extPow (X : D) (k : ℕ) : D := (antisym_split X k).choose

/-- `symDim (Λ^k X) = d(d-1)⋯(d-k+1)/k!`. -/
theorem symDim_extPow (X : D) (k : ℕ) :
    symDim (extPow X k) = (descPochhammer ℂ k).eval (symDim X) / (k.factorial : ℂ) := by
  obtain ⟨i, e, hie, hei⟩ := (antisym_split X k).choose_spec
  apply symDim_eq_of_trMor
  change trMor (𝟙 (antisym_split X k).choose) = _
  rw [← hie, trMor_comp_comm, hei, trMor_antisym (trMor_id_eq_smul X)]

variable (hpos : ∀ i, 0 < (symDim (F.simple i)).re)
include hpos

/-- Every object has real braided dimension. -/
theorem symDim_im_eq_zero (X : D) : (symDim X).im = 0 := by
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
  rw [symDim_of_iso_biproduct e, Complex.im_sum]
  exact Finset.sum_eq_zero fun k _ => (symDim_simple_real_pos hpos (f k)).1

/-- **Deligne's integrality**: the braided dimension of every object is a natural number. -/
theorem symDim_eq_nat (X : D) : ∃ n : ℕ, symDim X = n := by
  set d := symDim X with hd
  have hdre : d = ((d.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [symDim_im_eq_zero hpos X, hd]
  obtain ⟨n, hn⟩ := Deligne.exists_nat_of_descPochhammer_nonneg (d := d.re) (fun k => by
    have hk := symDim_extPow X k
    rw [← hd, hdre, descPochhammer_eval_ofReal] at hk
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    by_cases hz : IsZero (extPow X k)
    · rw [symDim_of_isZero hz] at hk
      have h0 : (((descPochhammer ℝ k).eval d.re : ℝ) : ℂ) = 0 := by
        have := hk.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h (by exact_mod_cast hfac.ne')
      exact (Complex.ofReal_eq_zero.mp h0).ge
    · have hp := re_symDim_pos hpos hz
      rw [hk] at hp
      have : ((((descPochhammer ℝ k).eval d.re : ℝ) : ℂ) / ((k.factorial : ℝ) : ℂ)).re =
          (descPochhammer ℝ k).eval d.re / k.factorial := by
        rw [← Complex.ofReal_div, Complex.ofReal_re]
      push_cast at this
      rw [this] at hp
      exact (div_pos_iff_of_pos_right hfac).mp hp |>.le)
  exact ⟨n, by rw [hdre, hn]; simp⟩

/-- The braided dimension of every simple is a positive integer. -/
theorem symDim_simple_nat (i : F.ι) : ∃ n : ℕ, 0 < n ∧ symDim (F.simple i) = n := by
  obtain ⟨n, hn⟩ := symDim_eq_nat hpos (F.simple i)
  refine ⟨n, ?_, hn⟩
  have := hpos i
  rw [hn] at this
  simp only [Complex.natCast_re] at this
  exact_mod_cast this

/-- `Λ^k X = 0` for `k > symDim X`. -/
theorem isZero_extPow_of_lt (X : D) {n : ℕ} (hn : symDim X = n) {k : ℕ} (hk : n < k) :
    IsZero (extPow X k) := by
  apply isZero_of_symDim_eq_zero hpos
  rw [symDim_extPow, hn, descPochhammer_eval_eq_descFactorial ℂ n k,
    Nat.descFactorial_eq_zero_iff_lt.mpr hk]
  simp

end VOA.Huang.TensorCat
