/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieBasis
import VOA.DeligneAudit.D4LieCasimirTransfer

/-!
# `LieData` for `𝔰𝔬₈ = d4Lie` in the cert basis

* `bracket_xs`: `⁅xs a, xs b⁆ = ∑ c, sZ a b c • xs c` (cert structure constants).
* `span_xs`, `bB`: the 28 vectors `xs` span `d4Lie` (every root is a `wt a`, by the count of
  24 roots), hence form a basis (`finrank_d4Lie = 28`).
* `killing_xs`: `Killing(x_a, x_c) = 12 · Gz a c`, so `κ = Killing/12` (the `d4Data` form) is the
  cert form `Gz` on this basis.
* `casimir_transfer`: the adjoint Casimir does not depend on the dual pair.
* **`d4CertData : LieData ((2 * 6)⁻¹ • killingForm ℂ d4Lie) (Fin 28)`**: basis `xs`, dual family
  `∑ (Gi2/2) xs`, `h = 6`; `structureConstant_eq : d4CertData.structureConstant = sZ` and
  `formTable_eq : d4CertData.formTable = Gz`.
-/

namespace VOA.DeligneAudit.D4Lie

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple VOA.AffineGeneral.LatticeDeligne
  VOA.AffineGeneral.RootCounts Submodule

noncomputable section

/-! ## Generic: the Casimir does not depend on the dual pair -/



/-! ## The cert brackets -/

theorem bracket_xs (a b : Fin 28) : ⁅xs a, xs b⁆ = ∑ c, (sZ a b c : ℂ) • xs c := by
  rw [bracket_model]
  simp only [sZ_eq_model]

/-! ## Spanning and the basis -/

theorem wt_inj : ∀ a b : Fin 28, 4 ≤ a.val → 4 ≤ b.val → wt a = wt b → a = b := by decide +kernel

theorem card_rootIdx : (Finset.univ.filter fun a : Fin 28 => 4 ≤ a.val).card = 24 := by decide

theorem d4_rootsGenerate : RootsGenerate d4 :=
  rootsGenerate_of_simple (simpleRoot (CartanMatrix.D 4) (CartanMatrix.D_isSymm 4) d4_posDef
    (by decide)) (closure_single (n := 4))

/-- **Every root of `D₄` is one of the cert weights.** -/
theorem root_eq_wt (β : d4.carrier) (hβ : β ∈ normEq d4 d4_posDef 2) :
    ∃ a : Fin 28, 4 ≤ a.val ∧ wt a = β := by
  classical
  let S : Finset d4.carrier := (Finset.univ.filter fun a : Fin 28 => 4 ≤ a.val).image wt
  have hsub : S ⊆ normEq d4 d4_posDef 2 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_normEq, d4_form_eq]
    exact wt_norm a (Finset.mem_filter.mp ha).2
  have hcard : S.card = 24 := by
    rw [Finset.card_image_of_injOn, card_rootIdx]
    intro a ha b hb h
    exact wt_inj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 h
  have heq : S = normEq d4 d4_posDef 2 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_roots_d4, hcard])
  rw [← heq] at hβ
  obtain ⟨a, ha, h⟩ := Finset.mem_image.mp hβ
  exact ⟨a, (Finset.mem_filter.mp ha).2, h⟩

theorem f_ne_zero (v : Lat) : f v ≠ 0 := by
  intro h
  have := f_mul_self v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem u_ne_zero (a : Fin 28) : (u a : ℂ) ≠ 0 := by
  intro h
  have := u_sq a
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem hst_single_eq (i : Fin 4) : hst (Pi.single i 1) = xs ⟨i.val, by omega⟩ := by
  rw [xs_cartan _ (by simp), hvec_eq]

/-- **The 28 cert vectors span `d4Lie`.** -/
theorem span_xs : ⊤ ≤ Submodule.span ℂ (Set.range xs) := by
  rw [← span_eV_hV d4_even d4_rootsGenerate, Submodule.span_le]
  rintro _ (⟨β, rfl⟩ | ⟨β, rfl⟩)
  · obtain ⟨a, ha, hwa⟩ := root_eq_wt β.1 β.2
    have he : eV d4 d4_even d4_posDef β = ((u a : ℂ) * f (wt a))⁻¹ • xs a := by
      rw [xs_root a ha, smul_smul, inv_mul_cancel₀ (mul_ne_zero (u_ne_zero a) (f_ne_zero _)),
        one_smul]
      apply Subtype.ext
      show latChargeGen d4 β.1 = latChargeGen d4 (wt a)
      rw [hwa]
    rw [SetLike.mem_coe, he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · have hh : hV d4 d4_even d4_posDef β = hst β.1 := rfl
    rw [SetLike.mem_coe, hh, hst_decomp, hst_single_eq, hst_single_eq, hst_single_eq,
      hst_single_eq]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **The cert basis of `d4Lie`.** -/
irreducible_def bB : Module.Basis (Fin 28) ℂ d4Lie :=
  basisOfTopLeSpanOfCardEqFinrank xs span_xs (by rw [Fintype.card_fin, finrank_d4Lie])

theorem bB_apply (a : Fin 28) : bB a = xs a := by
  rw [bB_def, coe_basisOfTopLeSpanOfCardEqFinrank]

theorem repr_xs (g e : Fin 28) : bB.repr (xs g) e = if g = e then 1 else 0 := by
  rw [← bB_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem repr_sum (k : Fin 28 → ℂ) (e : Fin 28) : bB.repr (∑ c, k c • xs c) e = k e := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, repr_xs, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-! ## The Killing form on the cert basis -/

theorem sum_sZ_mul (c e : Fin 28) (F : Fin 28 → ℤ) :
    ∑ d, sZ c e d * F d = ((sL c e).map fun t => t.2 * F t.1).sum := by
  unfold sZ
  induction sL c e with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem killing_xs (a c : Fin 28) : killingForm ℂ d4Lie (xs a) (xs c) = 12 * (Gz a c : ℂ) := by
  rw [LieModule.traceForm_apply_apply, LinearMap.trace_eq_matrix_trace ℂ bB, Matrix.trace]
  have hdiag : ∀ e, (LinearMap.toMatrix bB bB (LieModule.toEnd ℂ d4Lie d4Lie (xs a) ∘ₗ
      LieModule.toEnd ℂ d4Lie d4Lie (xs c))).diag e = ((∑ d, sZ c e d * sZ a d e : ℤ) : ℂ) := by
    intro e
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, bB_apply, LinearMap.comp_apply,
      LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply, bracket_xs, lie_sum]
    simp only [lie_smul, bracket_xs, Finset.smul_sum, smul_smul]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, repr_xs, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    rfl
  simp only [hdiag, sum_sZ_mul]
  have := killZ_eq a c
  unfold killZ at this
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this

/-- The `D₄` form: the normalization `Killing/12`. -/
def κ4 : LinearMap.BilinForm ℂ d4Lie := (2 * 6 : ℂ)⁻¹ • killingForm ℂ d4Lie

theorem κ4_xs (a c : Fin 28) : κ4 (xs a) (xs c) = Gz a c := by
  rw [κ4, LinearMap.smul_apply, LinearMap.smul_apply, killing_xs, smul_eq_mul]
  ring

/-- The dual family `x^b = ∑ (Gi2 b c / 2) x_c`. -/
def dualx (b : Fin 28) : d4Lie := ∑ c, ((Gi2 b c : ℂ) / 2) • xs c

theorem pair_xs (a b : Fin 28) : κ4 (xs a) (dualx b) = if a = b then 1 else 0 := by
  rw [dualx, map_sum]
  simp only [map_smul, κ4_xs, smul_eq_mul]
  have h := pair_cert a b
  have hc : (∑ c, ((Gi2 b c : ℂ) / 2) * (Gz a c : ℂ)) = ((∑ c, Gz a c * Gi2 b c : ℤ) : ℂ) / 2 := by
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hc, h]
  split_ifs <;> norm_num

theorem κ4_dual (y : d4Lie) (j : Fin 28) : κ4 y (dualx j) = bB.repr y j := by
  conv_lhs => rw [← bB.sum_repr y]
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smul₂, bB_apply, pair_xs, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand_xs (y : d4Lie) : y = ∑ j, κ4 y (dualx j) • xs j := by
  conv_lhs => rw [← bB.sum_repr y]
  simp only [κ4_dual, bB_apply]

/-- **`LieData` of `d4Lie` in the cert basis** (form `Killing/12`, `h = 6`). -/
irreducible_def d4CertData : LieData κ4 (Fin 28) where
  invariant := d4Data.invariant
  basis := bB
  dual := dualx
  pair i j := by rw [bB_apply]; exact pair_xs i j
  h := 6
  casimir x := by
    have h := casimir_transfer d4Data (fun j => bB j) dualx
      (fun y => by simp only [bB_apply]; exact expand_xs y) x
    rw [h, d4Data.casimir, d4Data_h]

theorem d4CertData_generator (a : Fin 28) : d4CertData.generator a = xs a := by
  rw [d4CertData_def]; exact bB_apply a

theorem d4CertData_h : d4CertData.h = 6 := by
  rw [d4CertData_def]

theorem d4CertData_basis : d4CertData.basis = bB := by
  rw [d4CertData_def]

theorem structureConstant_eq (a b c : Fin 28) :
    d4CertData.structureConstant a b c = (sZ a b c : ℂ) := by
  rw [LieData.structureConstant, LieData.coordinates, d4CertData_generator, d4CertData_generator,
    bracket_xs, d4CertData_basis]
  exact repr_sum _ c

theorem formTable_eq (a b : Fin 28) : d4CertData.formTable a b = (Gz a b : ℂ) := by
  rw [LieData.formTable, d4CertData_generator, d4CertData_generator, κ4_xs]

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
open VOA.DeligneAudit.D4Lie
#print axioms bracket_xs
#print axioms bB
#print axioms d4CertData
#print axioms structureConstant_eq
#print axioms formTable_eq
end AxiomAudit
