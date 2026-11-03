/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.LatticeV1Simple
import Mathlib.Algebra.Lie.Killing

/-!
# A basis of `(V_L)₁` and the Killing form on coroots

Given simple roots `s : Fin n → Root` generating `L` with `rank L = n`, the family
`Sum.elim eV (hV ∘ s) : Root ⊕ Fin n → (V_L)₁` spans and has `rank + #roots = dim` elements, hence is a
basis (`v1Basis`).  In it `ad (hV α)` is diagonal, so

  `Killing(hV α, hV α) = ∑_β ⟨α,β⟩²`   (`killing_hV_hV`).

For a simply-laced root system this sum is `4h∨`; with `κ = Killing/(2h∨)` the coroots then have
`κ(hα, hα) = 2`, i.e. `Killing/(2h∨)` is the standard normalization (`RootCounts`-style evaluations of
the sum are in `LatticeNormalization`).
-/

namespace VOA.AffineGeneral.LatticeLie

open VOA VOA.LatGen VOA.IntegralLattice Submodule

noncomputable section

variable {L : IntegralLattice} (hEven : L.Even) {hPos : L.PosDef}

/-- The Heisenberg state `α(-1)𝟙` for any lattice vector, in `(V_L)₁`. -/
def hVL (α : L.carrier) : V1 L hEven hPos := ⟨hSt L α, hSt_mem_gradingLatGen L α⟩

theorem hVL_add (α β : L.carrier) : hVL hEven (hPos := hPos) (α + β) = hVL hEven α + hVL hEven β :=
  Subtype.ext (hSt_add L α β)

theorem hVL_neg (α : L.carrier) : hVL hEven (hPos := hPos) (-α) = -hVL hEven α :=
  Subtype.ext (hSt_neg L α)

theorem hVL_zero : hVL hEven (hPos := hPos) (0 : L.carrier) = 0 :=
  Subtype.ext (hSt_zero L)

variable {n : ℕ} (s : Fin n → Root L hPos)
  (hsgen : AddSubgroup.closure (Set.range fun i => (s i).1) = ⊤)

include hsgen in
theorem hVL_mem_span (α : L.carrier) :
    hVL hEven α ∈ span ℂ (Set.range fun i => hV L hEven hPos (s i)) := by
  have hα : α ∈ AddSubgroup.closure (Set.range fun i => (s i).1) := by
    rw [hsgen]; exact AddSubgroup.mem_top α
  induction hα using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact subset_span ⟨i, rfl⟩
  | zero => rw [hVL_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [hVL_add]; exact add_mem hx hy
  | neg x _ hx => rw [hVL_neg]; exact neg_mem hx

include hsgen in
theorem span_eV_hV_simple :
    span ℂ (Set.range (Sum.elim (eV L hEven hPos) fun i => hV L hEven hPos (s i))) = ⊤ := by
  rw [Set.Sum.elim_range, eq_top_iff, ← span_eV_hV hEven (rootsGenerate_of_simple s hsgen)]
  apply span_le.mpr
  rintro _ (⟨β, rfl⟩ | ⟨β, rfl⟩)
  · exact subset_span (Or.inl ⟨β, rfl⟩)
  · exact span_mono Set.subset_union_right (hVL_mem_span hEven s hsgen β.1)

/-- **A basis of `(V_L)₁`**: the root vectors and the simple coroots. -/
def v1Basis (hrank : rank L = n) : Module.Basis (Root L hPos ⊕ Fin n) ℂ (V1 L hEven hPos) :=
  basisOfTopLeSpanOfCardEqFinrank (Sum.elim (eV L hEven hPos) fun i => hV L hEven hPos (s i))
    (span_eV_hV_simple hEven s hsgen).ge
    (by rw [finrank_V1, Fintype.card_sum, Fintype.card_fin, hrank, Fintype.card_coe, add_comm])

theorem v1Basis_apply (hrank : rank L = n) (x : Root L hPos ⊕ Fin n) :
    v1Basis hEven s hsgen hrank x = Sum.elim (eV L hEven hPos) (fun i => hV L hEven hPos (s i)) x := by
  rw [v1Basis, coe_basisOfTopLeSpanOfCardEqFinrank]

include hsgen in
/-- **`Killing(hV α, hV α) = ∑_β ⟨α,β⟩²`.** -/
theorem killing_hV_hV (hrank : rank L = n) (α : Root L hPos) :
    killingForm ℂ (V1 L hEven hPos) (hV L hEven hPos α) (hV L hEven hPos α)
      = ∑ β : Root L hPos, ((L.form α.1 β.1 : ℤ) : ℂ) ^ 2 := by
  classical
  set b := v1Basis hEven s hsgen hrank
  rw [killingForm_apply_apply, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace,
    Fintype.sum_sum_type]
  have h1 : ∀ β : Root L hPos, Matrix.diag (LinearMap.toMatrix b b
      (LieAlgebra.ad ℂ (V1 L hEven hPos) (hV L hEven hPos α) ∘ₗ
        LieAlgebra.ad ℂ (V1 L hEven hPos) (hV L hEven hPos α))) (Sum.inl β)
      = ((L.form α.1 β.1 : ℤ) : ℂ) ^ 2 := by
    intro β
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply,
      LieAlgebra.ad_apply, LieAlgebra.ad_apply, v1Basis_apply, Sum.elim_inl, hV_eV, lie_smul, hV_eV,
      smul_smul]
    have hb : eV L hEven hPos β = b (Sum.inl β) := by rw [v1Basis_apply, Sum.elim_inl]
    rw [hb, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, sq]
  have h2 : ∀ i : Fin n, Matrix.diag (LinearMap.toMatrix b b
      (LieAlgebra.ad ℂ (V1 L hEven hPos) (hV L hEven hPos α) ∘ₗ
        LieAlgebra.ad ℂ (V1 L hEven hPos) (hV L hEven hPos α))) (Sum.inr i) = 0 := by
    intro i
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply,
      LieAlgebra.ad_apply, LieAlgebra.ad_apply, v1Basis_apply, Sum.elim_inr, hV_hV, lie_zero,
      map_zero, Finsupp.zero_apply]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

end

end VOA.AffineGeneral.LatticeLie
