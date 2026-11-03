/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8LieKilling
import VOA.DeligneAudit.E8LieDataChecks
import VOA.DeligneAudit.D4LieData

/-!
# `LieData` for `𝔢₈ = e8Lie` in the cert basis

* `bracket_xs`: `⁅xs a, xs b⁆ = ∑ c, sZ a b c • xs c` (cert structure constants).
* `span_xs`, `bB`: the 248 vectors span (every root is a cert weight, the `card_roots_e8`), hence a
  basis (`finrank_e8Lie = 248`).
* `κ8 = Killing/60` (the `e8Data` form) equals the cert form `Gz` on this basis (`killing_xs`).
* **`e8CertData : LieData κ8 (Fin 248)`**: basis `xs`, dual `∑ (Gi2/2) xs`, `h = 30`, Casimir transferred
  from the `e8Data` (`D4Lie.casimir_transfer`); `structureConstant_eq`, `formTable_eq`.
-/

namespace VOA.DeligneAudit.E8Lie

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple VOA.AffineGeneral.LatticeDeligne
  VOA.AffineGeneral.RootCounts VOA.AffineGeneral.E8Deligne VOA.AffineGeneral.E8Dim

noncomputable section

/-! ## Sparse sums as `Finset` sums -/

theorem spL_eq_sum (l : List (Fin 248 × ℤ)) :
    spL l = ∑ c, (((l.map fun t => if t.1 = c then t.2 else 0).sum : ℤ) : ℂ) • xs c := by
  induction l with
  | nil => simp [spL]
  | cons t l ih =>
      rw [spL, List.map_cons, List.sum_cons, ← spL, ih]
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

theorem bracket_xs (a b : Fin 248) : ⁅xs a, xs b⁆ = ∑ c, (sZ a b c : ℂ) • xs c := by
  rw [bracket, spL_eq_sum]
  rfl

/-! ## Spanning and the basis -/

theorem e8_rootsGenerate : RootsGenerate e8 :=
  rootsGenerate_of_simple (simpleRoot (CartanMatrix.E₈) CartanMatrix.E₈_isSymm e8_posDef
    (by decide)) (closure_single (n := 8))

theorem root_eq_wt (β : e8.carrier) (hβ : β ∈ normEq e8 e8_posDef 2) :
    ∃ a : Fin 248, 8 ≤ a.val ∧ wt a = β := by
  classical
  let S : Finset e8.carrier := (Finset.univ.filter fun a : Fin 248 => 8 ≤ a.val).image wt
  have hsub : S ⊆ normEq e8 e8_posDef 2 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_normEq, e8_form_eq]
    exact wt_norm a (Finset.mem_filter.mp ha).2
  have hcard : S.card = 240 := by
    rw [Finset.card_image_of_injOn, card_rootIdx]
    intro a ha b hb h
    exact wt_inj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h
  have heq : S = normEq e8 e8_posDef 2 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_roots_e8, hcard])
  rw [← heq] at hβ
  obtain ⟨a, ha, h⟩ := Finset.mem_image.mp hβ
  exact ⟨a, (Finset.mem_filter.mp ha).2, h⟩

theorem f_ne_zero (v : Lat) : f v ≠ 0 := by
  intro h
  have := f_mul_self v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem u_ne_zero (a : Fin 248) : (u a : ℂ) ≠ 0 := by
  intro h
  have := u_sq a
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- **The 248 cert vectors span `e8Lie`.** -/
theorem span_xs : ⊤ ≤ Submodule.span ℂ (Set.range xs) := by
  rw [← span_eV_hV e8_even e8_rootsGenerate, Submodule.span_le]
  rintro _ (⟨β, rfl⟩ | ⟨β, rfl⟩)
  · obtain ⟨a, ha, hwa⟩ := root_eq_wt β.1 β.2
    have he : eV e8 e8_even e8_posDef β = ((u a : ℂ) * f (wt a))⁻¹ • xs a := by
      rw [xs_root a ha, smul_smul, inv_mul_cancel₀ (mul_ne_zero (u_ne_zero a) (f_ne_zero _)),
        one_smul]
      apply Subtype.ext
      show latChargeGen e8 β.1 = latChargeGen e8 (wt a)
      rw [hwa]
    rw [SetLike.mem_coe, he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · have hh : hV e8 e8_even e8_posDef β = hst β.1 := rfl
    rw [SetLike.mem_coe, hh, hst_decomp]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← xs_cI]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **The cert basis of `e8Lie`.** -/
irreducible_def bB : Module.Basis (Fin 248) ℂ e8Lie :=
  basisOfTopLeSpanOfCardEqFinrank xs span_xs (by rw [Fintype.card_fin, finrank_e8Lie])

theorem bB_apply (a : Fin 248) : bB a = xs a := by
  rw [bB_def, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem repr_xs (g e : Fin 248) : bB.repr (xs g) e = if g = e then 1 else 0 := by
  rw [← bB_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem repr_sum (k : Fin 248 → ℂ) (e : Fin 248) : bB.repr (∑ c, k c • xs c) e = k e := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, repr_xs, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-! ## The form and the dual family -/

/-- The `E₈` form: the normalization `Killing/60`. -/
def κ8 : LinearMap.BilinForm ℂ e8Lie := (2 * 30 : ℂ)⁻¹ • killingForm ℂ e8Lie

theorem κ8_xs (a c : Fin 248) : κ8 (xs a) (xs c) = Gz a c := by
  rw [κ8, LinearMap.smul_apply, LinearMap.smul_apply, killing_xs, smul_eq_mul]
  ring

/-- The dual family `x^b = ∑ (Gi2 b c / 2) x_c`. -/
def dualx (b : Fin 248) : e8Lie := ((Gi2L b).map fun t => ((t.2 : ℂ) / 2) • xs t.1).sum

theorem κ8_dualx (a b : Fin 248) :
    κ8 (xs a) (dualx b) = (((Gi2L b).map fun t => t.2 * Gz a t.1).sum : ℤ) / 2 := by
  unfold dualx
  induction Gi2L b with
  | nil => simp
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, κ8_xs] at ih ⊢
      rw [ih]
      push_cast
      ring

theorem pair_xs (a b : Fin 248) : κ8 (xs a) (dualx b) = if a = b then 1 else 0 := by
  have h := pairRow_all a
  simp only [pairRowOK, List.all_eq_true, decide_eq_true_eq] at h
  rw [κ8_dualx, h b (List.mem_finRange b)]
  split_ifs <;> norm_num

theorem κ8_dual (y : e8Lie) (j : Fin 248) : κ8 y (dualx j) = bB.repr y j := by
  conv_lhs => rw [← bB.sum_repr y]
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smul₂, bB_apply, pair_xs, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand_xs (y : e8Lie) : y = ∑ j, κ8 y (dualx j) • xs j := by
  conv_lhs => rw [← bB.sum_repr y]
  simp only [κ8_dual, bB_apply]

/-- **`LieData` of `e8Lie` in the cert basis** (form `Killing/60`, `h = 30`). -/
irreducible_def e8CertData : LieData κ8 (Fin 248) where
  invariant := e8Data.invariant
  basis := bB
  dual := dualx
  pair i j := by rw [bB_apply]; exact pair_xs i j
  h := 30
  casimir x := by
    have h := D4Lie.casimir_transfer e8Data (fun j => bB j) dualx
      (fun y => by simp only [bB_apply]; exact expand_xs y) x
    rw [h, e8Data.casimir, e8Data_h]

theorem e8CertData_generator (a : Fin 248) : e8CertData.generator a = xs a := by
  rw [e8CertData_def]; exact bB_apply a

theorem e8CertData_h : e8CertData.h = 30 := by
  rw [e8CertData_def]

theorem e8CertData_basis : e8CertData.basis = bB := by
  rw [e8CertData_def]

theorem e8CertData_dual (b : Fin 248) : e8CertData.dual b = dualx b := by
  rw [e8CertData_def]

theorem structureConstant_eq (a b c : Fin 248) :
    e8CertData.structureConstant a b c = (sZ a b c : ℂ) := by
  rw [LieData.structureConstant, LieData.coordinates, e8CertData_generator, e8CertData_generator,
    bracket_xs, e8CertData_basis]
  exact repr_sum _ c

theorem formTable_eq (a b : Fin 248) : e8CertData.formTable a b = (Gz a b : ℂ) := by
  rw [LieData.formTable, e8CertData_generator, e8CertData_generator, κ8_xs]

end

end VOA.DeligneAudit.E8Lie

section AxiomAudit
open VOA.DeligneAudit.E8Lie
#print axioms bB
#print axioms e8CertData
#print axioms structureConstant_eq
#print axioms formTable_eq
end AxiomAudit
