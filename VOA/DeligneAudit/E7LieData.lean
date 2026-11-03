/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieKilling
import VOA.DeligneAudit.D4LieCasimirTransfer

/-!
# `LieData` for `𝔢₇ = e7Lie` in the cert basis

* `bracket_xs`: `⁅xs a, xs b⁆ = ∑ c, sZ a b c • xs c` (cert structure constants).
* `span_xs`, `bB`: the 133 vectors span (every root is a cert weight, the `card_roots_e7`), hence a
  basis (`finrank_e7Lie = 133`).
* `κ7 = Killing/36` (the `e7Data` form) equals the cert form `Gz` on this basis (`killing_xs`).
* **`e7CertData : LieData κ7 (Fin 133)`**: basis `xs`, dual `∑ (Gi2/2) xs`, `h = 18`, Casimir transferred
  from the `e7Data` (`D4Lie.casimir_transfer`); `structureConstant_eq`, `formTable_eq`.
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple VOA.AffineGeneral.LatticeDeligne
  VOA.AffineGeneral.RootCounts

noncomputable section

/-! ## Sparse sums as `Finset` sums -/

theorem spL_eq_sum (l : List (Fin 133 × ℤ)) :
    spL l = ∑ c, (((l.map fun t => if t.1 = c then t.2 else 0).sum : ℤ) : ℂ) • xs c := by
  induction l with
  | nil => simp [spL]
  | cons t l ih =>
      rw [spL, List.map_cons, List.sum_cons, ← spL, ih]
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

theorem bracket_xs (a b : Fin 133) : ⁅xs a, xs b⁆ = ∑ c, (sZ a b c : ℂ) • xs c := by
  rw [bracket, spL_eq_sum]
  rfl

/-! ## Spanning and the basis -/

theorem wt_inj : ∀ a b : Fin 133, 7 ≤ a.val → 7 ≤ b.val → wt a = wt b → a = b := by
  decide +kernel

theorem card_rootIdx : (Finset.univ.filter fun a : Fin 133 => 7 ≤ a.val).card = 126 := by
  decide +kernel

theorem e7_rootsGenerate : RootsGenerate e7 :=
  rootsGenerate_of_simple (simpleRoot (CartanMatrix.E₇) CartanMatrix.E₇_isSymm e7_posDef
    (by decide)) (closure_single (n := 7))

theorem root_eq_wt (β : e7.carrier) (hβ : β ∈ normEq e7 e7_posDef 2) :
    ∃ a : Fin 133, 7 ≤ a.val ∧ wt a = β := by
  classical
  let S : Finset e7.carrier := (Finset.univ.filter fun a : Fin 133 => 7 ≤ a.val).image wt
  have hsub : S ⊆ normEq e7 e7_posDef 2 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_normEq, e7_form_eq]
    exact wt_norm a (Finset.mem_filter.mp ha).2
  have hcard : S.card = 126 := by
    rw [Finset.card_image_of_injOn, card_rootIdx]
    intro a ha b hb h
    exact wt_inj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h
  have heq : S = normEq e7 e7_posDef 2 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_roots_e7, hcard])
  rw [← heq] at hβ
  obtain ⟨a, ha, h⟩ := Finset.mem_image.mp hβ
  exact ⟨a, (Finset.mem_filter.mp ha).2, h⟩

theorem f_ne_zero (v : Lat) : f v ≠ 0 := by
  intro h
  have := f_mul_self v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem u_ne_zero (a : Fin 133) : (u a : ℂ) ≠ 0 := by
  intro h
  have := u_sq a
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- **The 133 cert vectors span `e7Lie`.** -/
theorem span_xs : ⊤ ≤ Submodule.span ℂ (Set.range xs) := by
  rw [← span_eV_hV e7_even e7_rootsGenerate, Submodule.span_le]
  rintro _ (⟨β, rfl⟩ | ⟨β, rfl⟩)
  · obtain ⟨a, ha, hwa⟩ := root_eq_wt β.1 β.2
    have he : eV e7 e7_even e7_posDef β = ((u a : ℂ) * f (wt a))⁻¹ • xs a := by
      rw [xs_root a ha, smul_smul, inv_mul_cancel₀ (mul_ne_zero (u_ne_zero a) (f_ne_zero _)),
        one_smul]
      apply Subtype.ext
      show latChargeGen e7 β.1 = latChargeGen e7 (wt a)
      rw [hwa]
    rw [SetLike.mem_coe, he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · have hh : hV e7 e7_even e7_posDef β = hst β.1 := rfl
    rw [SetLike.mem_coe, hh, hst_decomp]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← xs_cI]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **The cert basis of `e7Lie`.** -/
irreducible_def bB : Module.Basis (Fin 133) ℂ e7Lie :=
  basisOfTopLeSpanOfCardEqFinrank xs span_xs (by rw [Fintype.card_fin, finrank_e7Lie])

theorem bB_apply (a : Fin 133) : bB a = xs a := by
  rw [bB_def, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem repr_xs (g e : Fin 133) : bB.repr (xs g) e = if g = e then 1 else 0 := by
  rw [← bB_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem repr_sum (k : Fin 133 → ℂ) (e : Fin 133) : bB.repr (∑ c, k c • xs c) e = k e := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, repr_xs, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-! ## The form and the dual family -/

/-- The `E₇` form: the normalization `Killing/36`. -/
def κ7 : LinearMap.BilinForm ℂ e7Lie := (2 * 18 : ℂ)⁻¹ • killingForm ℂ e7Lie

theorem κ7_xs (a c : Fin 133) : κ7 (xs a) (xs c) = Gz a c := by
  rw [κ7, LinearMap.smul_apply, LinearMap.smul_apply, killing_xs, smul_eq_mul]
  ring

/-- The dual family `x^b = ∑ (Gi2 b c / 2) x_c`. -/
def dualx (b : Fin 133) : e7Lie := ((Gi2L b).map fun t => ((t.2 : ℂ) / 2) • xs t.1).sum

theorem κ7_dualx (a b : Fin 133) :
    κ7 (xs a) (dualx b) = (((Gi2L b).map fun t => t.2 * Gz a t.1).sum : ℤ) / 2 := by
  unfold dualx
  induction Gi2L b with
  | nil => simp
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, κ7_xs] at ih ⊢
      rw [ih]
      push_cast
      ring

theorem pair_xs (a b : Fin 133) : κ7 (xs a) (dualx b) = if a = b then 1 else 0 := by
  have h := pairRow_all a
  simp only [pairRowOK, List.all_eq_true, decide_eq_true_eq] at h
  rw [κ7_dualx, h b (List.mem_finRange b)]
  split_ifs <;> norm_num

theorem κ7_dual (y : e7Lie) (j : Fin 133) : κ7 y (dualx j) = bB.repr y j := by
  conv_lhs => rw [← bB.sum_repr y]
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smul₂, bB_apply, pair_xs, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand_xs (y : e7Lie) : y = ∑ j, κ7 y (dualx j) • xs j := by
  conv_lhs => rw [← bB.sum_repr y]
  simp only [κ7_dual, bB_apply]

/-- **`LieData` of `e7Lie` in the cert basis** (form `Killing/36`, `h = 18`). -/
irreducible_def e7CertData : LieData κ7 (Fin 133) where
  invariant := e7Data.invariant
  basis := bB
  dual := dualx
  pair i j := by rw [bB_apply]; exact pair_xs i j
  h := 18
  casimir x := by
    have h := D4Lie.casimir_transfer e7Data (fun j => bB j) dualx
      (fun y => by simp only [bB_apply]; exact expand_xs y) x
    rw [h, e7Data.casimir, e7Data_h]

theorem e7CertData_generator (a : Fin 133) : e7CertData.generator a = xs a := by
  rw [e7CertData_def]; exact bB_apply a

theorem e7CertData_h : e7CertData.h = 18 := by
  rw [e7CertData_def]

theorem e7CertData_basis : e7CertData.basis = bB := by
  rw [e7CertData_def]

theorem e7CertData_dual (b : Fin 133) : e7CertData.dual b = dualx b := by
  rw [e7CertData_def]

theorem structureConstant_eq (a b c : Fin 133) :
    e7CertData.structureConstant a b c = (sZ a b c : ℂ) := by
  rw [LieData.structureConstant, LieData.coordinates, e7CertData_generator, e7CertData_generator,
    bracket_xs, e7CertData_basis]
  exact repr_sum _ c

theorem formTable_eq (a b : Fin 133) : e7CertData.formTable a b = (Gz a b : ℂ) := by
  rw [LieData.formTable, e7CertData_generator, e7CertData_generator, κ7_xs]

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
open VOA.DeligneAudit.E7Lie
#print axioms bB
#print axioms e7CertData
#print axioms structureConstant_eq
#print axioms formTable_eq
end AxiomAudit
