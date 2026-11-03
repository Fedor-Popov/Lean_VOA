/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.RootCounts
import VOA.AffineGeneral.LatticeKilling
import VOA.AffineGeneral.LatticeNormalizationChecks

/-!
# The normalization `Killing/(2h∨)`: roots have length `2`

For each simply-laced Deligne lattice and every root `β`, `∑_γ ⟨β,γ⟩² = 4h∨` (enumerated over the roots,
`decide +kernel`), so by `killing_hV_hV` the Killing form gives `Killing(hβ, hβ) = 4h∨` and
`κ = Killing/(2h∨)` gives **`κ(hβ, hβ) = 2`** (`*_standard`).  This identifies the parameter `hv` of
`standardData` with the dual Coxeter number in the usual sense (long roots of length `2`): `h∨ = 3, 6, 12,
18, 30` for `A₂, D₄, E₆, E₇, E₈`.  Hence the levels `-3/2, -2, -3, -4, -6` used in `A2General`,
`LatticeDeligne`, `E8Deligne` are the Deligne levels `-h∨/6 - 1` in the standard normalization.
-/

set_option linter.style.longLine false

namespace VOA.AffineGeneral.Normalization

open VOA.CartanLattices VOA.LatGen VOA.AffineGeneral.RootEnum VOA.AffineGeneral.RootCounts
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple

noncomputable section

/-- **`∑_γ ⟨β,γ⟩²` over the roots, by enumeration.** -/
theorem sum_sq_form {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (hPos : (ofCartan G hG).PosDef) (rows : List Row) (hlen : rows.length = n)
    (hadm : Admissible 2 rows)
    (hid : ∀ v : Fin n → ℤ, ((Matrix.toBilin' G v v : ℤ) : ℚ) = tailSum rows (List.ofFn v))
    (hnd : (rootList rows).Nodup) (GM : List (List ℤ))
    (hform : ∀ v w : Fin n → ℤ, Matrix.toBilin' G v w = formL GM (List.ofFn v) (List.ofFn w))
    (c : ℤ) (hc : ∀ s ∈ rootList rows, ((rootList rows).map fun t => formL GM s t ^ 2).sum = c)
    (β : Root (ofCartan G hG) hPos) :
    ∑ γ : Root (ofCartan G hG) hPos, (((ofCartan G hG).form β.1 γ.1 : ℤ) : ℂ) ^ 2 = c := by
  classical
  have himg := image_normEq_eq G hG hPos rows hlen hadm hid
  have hinj : Function.Injective (fun v : (ofCartan G hG).carrier => List.ofFn (n := n) v) :=
    fun a b h => List.ofFn_injective h
  set g : List ℤ → ℤ := fun t => formL GM (List.ofFn (n := n) β.1) t ^ 2
  have hsum : ∑ γ ∈ normEq (ofCartan G hG) hPos 2, ((ofCartan G hG).form β.1 γ) ^ 2 = c := by
    calc ∑ γ ∈ normEq (ofCartan G hG) hPos 2, ((ofCartan G hG).form β.1 γ) ^ 2
        = ∑ γ ∈ normEq (ofCartan G hG) hPos 2, g (List.ofFn (n := n) γ) := by
          refine Finset.sum_congr rfl fun γ _ => ?_
          simp only [g, ← hform]
          rfl
      _ = ∑ t ∈ (normEq (ofCartan G hG) hPos 2).image
            (fun v : (ofCartan G hG).carrier => List.ofFn (n := n) v), g t :=
          (Finset.sum_image fun a _ b _ h => hinj h).symm
      _ = ((rootList rows).map g).sum := by rw [himg, List.sum_toFinset _ hnd]
      _ = c := by
          apply hc
          rw [← List.mem_toFinset, ← himg]
          exact Finset.mem_image_of_mem _ β.2
  rw [← Finset.sum_coe_sort] at hsum
  have := congrArg (fun z : ℤ => (z : ℂ)) hsum
  push_cast at this
  exact this

/-! ## `a2` -/

theorem a2_form (v w : Fin 2 → ℤ) :
    Matrix.toBilin' (CartanMatrix.A 2) v w = formL a2GL (List.ofFn v) (List.ofFn w) := by
  rw [Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, formL, a2GL, List.ofFn_succ, CartanMatrix.A]

theorem a2_sumsq : ∀ s ∈ rootList a2Rows, ((rootList a2Rows).map fun t => formL a2GL s t ^ 2).sum = 12 := by
  have hrows : a2Rows = Certificate.a2RowsData := rfl
  have hroots : rootList a2Rows = Certificate.a2Roots := by
    change Certificate.enumRoots a2Rows = Certificate.a2Roots
    rw [hrows]
    exact Certificate.a2_enumRoots
  rw [hroots]
  exact Certificate.a2_literal_sumsq

/-! ## `d4` -/

theorem d4_form (v w : Fin 4 → ℤ) :
    Matrix.toBilin' (CartanMatrix.D 4) v w = formL d4GL (List.ofFn v) (List.ofFn w) := by
  rw [Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, formL, d4GL, List.ofFn_succ, CartanMatrix.D]

theorem d4_sumsq : ∀ s ∈ rootList d4Rows, ((rootList d4Rows).map fun t => formL d4GL s t ^ 2).sum = 24 := by
  have hrows : d4Rows = Certificate.d4RowsData := rfl
  have hroots : rootList d4Rows = Certificate.d4Roots := by
    change Certificate.enumRoots d4Rows = Certificate.d4Roots
    rw [hrows]
    exact Certificate.d4_enumRoots
  rw [hroots]
  exact Certificate.d4_literal_sumsq

/-! ## `e6` -/

theorem e6_form (v w : Fin 6 → ℤ) :
    Matrix.toBilin' (CartanMatrix.E₆) v w = formL e6GL (List.ofFn v) (List.ofFn w) := by
  rw [Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, formL, e6GL, List.ofFn_succ, CartanMatrix.E₆]

theorem e6_sumsq : ∀ s ∈ rootList e6Rows, ((rootList e6Rows).map fun t => formL e6GL s t ^ 2).sum = 48 := by
  have hrows : e6Rows = Certificate.e6RowsData := rfl
  have hroots : rootList e6Rows = Certificate.e6Roots := by
    change Certificate.enumRoots e6Rows = Certificate.e6Roots
    rw [hrows]
    exact Certificate.e6_enumRoots
  rw [hroots]
  exact Certificate.e6_literal_sumsq

/-! ## `e7` -/

theorem e7_form (v w : Fin 7 → ℤ) :
    Matrix.toBilin' (CartanMatrix.E₇) v w = formL e7GL (List.ofFn v) (List.ofFn w) := by
  rw [Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, formL, e7GL, List.ofFn_succ, CartanMatrix.E₇]

theorem e7_sumsq : ∀ s ∈ rootList e7Rows, ((rootList e7Rows).map fun t => formL e7GL s t ^ 2).sum = 72 := by
  have hrows : e7Rows = Certificate.e7RowsData := rfl
  have hroots : rootList e7Rows = Certificate.e7Roots := by
    change Certificate.enumRoots e7Rows = Certificate.e7Roots
    rw [hrows]
    exact Certificate.e7_enumRoots
  rw [hroots]
  exact Certificate.e7_literal_sumsq

/-! ## `e8` -/

theorem e8_form (v w : Fin 8 → ℤ) :
    Matrix.toBilin' (CartanMatrix.E₈) v w = formL e8GL (List.ofFn v) (List.ofFn w) := by
  rw [Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, formL, e8GL, List.ofFn_succ, CartanMatrix.E₈]

theorem e8_sumsq : ∀ s ∈ rootList e8Rows, ((rootList e8Rows).map fun t => formL e8GL s t ^ 2).sum = 120 := by
  have hrows : e8Rows = Certificate.e8RowsData := rfl
  have hroots : rootList e8Rows = Certificate.e8Roots := by
    change Certificate.enumRoots e8Rows = Certificate.e8Roots
    rw [hrows]
    exact Certificate.e8_enumRoots
  rw [hroots]
  exact Certificate.e8_literal_sumsq

/-! ## The Killing form on coroots, and the standard normalization -/

/-- `Killing(hβ, hβ) = 12 = 4h∨` for every root `β` of `a2`. -/
theorem a2_killing (β : Root a2 a2_posDef) :
    killingForm ℂ a2Lie (hV a2 a2_even a2_posDef β) (hV a2 a2_even a2_posDef β) = 12 := by
  rw [killing_hV_hV a2_even (simpleRoot (CartanMatrix.A 2) (CartanMatrix.A_isSymm 2) a2_posDef (by decide)) (closure_single (n := 2))
    (DeligneLatticeLie.rank_ofCartan _ _) β]
  exact_mod_cast sum_sq_form (CartanMatrix.A 2) (CartanMatrix.A_isSymm 2) a2_posDef a2Rows rfl a2_adm a2_id a2_nodup a2GL a2_form
    12 a2_sumsq β

/-- **`Killing/6` is the standard normalization on `a2Lie`**: every root has length `2`. -/
theorem a2_standard (β : Root a2 a2_posDef) :
    ((2 * 3 : ℂ)⁻¹ • killingForm ℂ a2Lie) (hV a2 a2_even a2_posDef β)
      (hV a2 a2_even a2_posDef β) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, a2_killing]
  norm_num

/-- `Killing(hβ, hβ) = 24 = 4h∨` for every root `β` of `d4`. -/
theorem d4_killing (β : Root d4 d4_posDef) :
    killingForm ℂ d4Lie (hV d4 d4_even d4_posDef β) (hV d4 d4_even d4_posDef β) = 24 := by
  rw [killing_hV_hV d4_even (simpleRoot (CartanMatrix.D 4) (CartanMatrix.D_isSymm 4) d4_posDef (by decide)) (closure_single (n := 4))
    (DeligneLatticeLie.rank_ofCartan _ _) β]
  exact_mod_cast sum_sq_form (CartanMatrix.D 4) (CartanMatrix.D_isSymm 4) d4_posDef d4Rows rfl d4_adm d4_id d4_nodup d4GL d4_form
    24 d4_sumsq β

/-- **`Killing/12` is the standard normalization on `d4Lie`**: every root has length `2`. -/
theorem d4_standard (β : Root d4 d4_posDef) :
    ((2 * 6 : ℂ)⁻¹ • killingForm ℂ d4Lie) (hV d4 d4_even d4_posDef β)
      (hV d4 d4_even d4_posDef β) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, d4_killing]
  norm_num

/-- `Killing(hβ, hβ) = 48 = 4h∨` for every root `β` of `e6`. -/
theorem e6_killing (β : Root e6 e6_posDef) :
    killingForm ℂ e6Lie (hV e6 e6_even e6_posDef β) (hV e6 e6_even e6_posDef β) = 48 := by
  rw [killing_hV_hV e6_even (simpleRoot (CartanMatrix.E₆) CartanMatrix.E₆_isSymm e6_posDef (by decide)) (closure_single (n := 6))
    (DeligneLatticeLie.rank_ofCartan _ _) β]
  exact_mod_cast sum_sq_form (CartanMatrix.E₆) CartanMatrix.E₆_isSymm e6_posDef e6Rows rfl e6_adm e6_id e6_nodup e6GL e6_form
    48 e6_sumsq β

/-- **`Killing/24` is the standard normalization on `e6Lie`**: every root has length `2`. -/
theorem e6_standard (β : Root e6 e6_posDef) :
    ((2 * 12 : ℂ)⁻¹ • killingForm ℂ e6Lie) (hV e6 e6_even e6_posDef β)
      (hV e6 e6_even e6_posDef β) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e6_killing]
  norm_num

/-- `Killing(hβ, hβ) = 72 = 4h∨` for every root `β` of `e7`. -/
theorem e7_killing (β : Root e7 e7_posDef) :
    killingForm ℂ e7Lie (hV e7 e7_even e7_posDef β) (hV e7 e7_even e7_posDef β) = 72 := by
  rw [killing_hV_hV e7_even (simpleRoot (CartanMatrix.E₇) CartanMatrix.E₇_isSymm e7_posDef (by decide)) (closure_single (n := 7))
    (DeligneLatticeLie.rank_ofCartan _ _) β]
  exact_mod_cast sum_sq_form (CartanMatrix.E₇) CartanMatrix.E₇_isSymm e7_posDef e7Rows rfl e7_adm e7_id e7_nodup e7GL e7_form
    72 e7_sumsq β

/-- **`Killing/36` is the standard normalization on `e7Lie`**: every root has length `2`. -/
theorem e7_standard (β : Root e7 e7_posDef) :
    ((2 * 18 : ℂ)⁻¹ • killingForm ℂ e7Lie) (hV e7 e7_even e7_posDef β)
      (hV e7 e7_even e7_posDef β) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e7_killing]
  norm_num

/-- `Killing(hβ, hβ) = 120 = 4h∨` for every root `β` of `e8`. -/
theorem e8_killing (β : Root e8 e8_posDef) :
    killingForm ℂ e8Lie (hV e8 e8_even e8_posDef β) (hV e8 e8_even e8_posDef β) = 120 := by
  rw [killing_hV_hV e8_even (simpleRoot (CartanMatrix.E₈) CartanMatrix.E₈_isSymm e8_posDef (by decide)) (closure_single (n := 8))
    (DeligneLatticeLie.rank_ofCartan _ _) β]
  exact_mod_cast sum_sq_form (CartanMatrix.E₈) CartanMatrix.E₈_isSymm e8_posDef e8Rows rfl e8_adm e8_id e8_nodup e8GL e8_form
    120 e8_sumsq β

/-- **`Killing/60` is the standard normalization on `e8Lie`**: every root has length `2`. -/
theorem e8_standard (β : Root e8 e8_posDef) :
    ((2 * 30 : ℂ)⁻¹ • killingForm ℂ e8Lie) (hV e8 e8_even e8_posDef β)
      (hV e8 e8_even e8_posDef β) = 2 := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e8_killing]
  norm_num

end

end VOA.AffineGeneral.Normalization

#print axioms VOA.AffineGeneral.Normalization.a2_sumsq
#print axioms VOA.AffineGeneral.Normalization.a2_standard
#print axioms VOA.AffineGeneral.Normalization.d4_sumsq
#print axioms VOA.AffineGeneral.Normalization.d4_standard
#print axioms VOA.AffineGeneral.Normalization.e6_sumsq
#print axioms VOA.AffineGeneral.Normalization.e6_standard
#print axioms VOA.AffineGeneral.Normalization.e7_sumsq
#print axioms VOA.AffineGeneral.Normalization.e7_standard
#print axioms VOA.AffineGeneral.Normalization.e8_sumsq
#print axioms VOA.AffineGeneral.Normalization.e8_standard
