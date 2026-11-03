/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPolyFields
import VOA.Examples.VirasoroTopSymbol

/-!
# The polynomial structure tensor of `V(c,0)`

This is step 3(A) of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`). It works in the
`c`-free model `PV := List ℕ →₀ ℂ[X]` (vectors with polynomial coefficients over creation words):

* `tensor n : PV →ₗ[ℂ[X]] PV →ₗ[ℂ[X]] PV`, the `n`-th product as a `ℂ[X]`-bilinear map, with values
  supported on sorted words (`sorted_tensor`);
* `polyComb_tensor`: at every `c`, `polyComb c (tensor n A B) = A(c)₍ₙ₎ B(c)`;
* `lift c : VirUniv c →ₗ[ℂ] PV`, the constant sorted coordinates of a vector at a fixed `c`, with
  `polyComb_lift : polyComb c (lift c x) = x`.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-- The `c`-free model. -/
abbrev PV := List ℕ →₀ ℂ[X]

theorem Sorted.zero : Sorted (0 : PV) := fun u hu => by simp at hu

theorem Sorted.add {P Q : PV} (hP : Sorted P) (hQ : Sorted Q) : Sorted (P + Q) := fun u hu =>
  (Finset.mem_union.mp (Finsupp.support_add hu)).elim (hP u) (hQ u)

theorem Sorted.smul {P : PV} (q : ℂ[X]) (hP : Sorted P) : Sorted (q • P) := fun u hu =>
  hP u (Finsupp.support_smul hu)

theorem Sorted.sub {P Q : PV} (hP : Sorted P) (hQ : Sorted Q) : Sorted (P - Q) := fun u hu =>
  (Finset.mem_union.mp (Finsupp.support_sub hu)).elim (hP u) (hQ u)

/-- The structure constants on two creation words: the unique sorted polynomial expansion of
`u₍ₙ₎ w`. -/
noncomputable def tensorW (u : List ℕ) (n : ℤ) (w : List ℕ) : PV :=
  (exists_sorted_polyComb_mode u w n).choose

theorem sorted_tensorW (u : List ℕ) (n : ℤ) (w : List ℕ) : Sorted (tensorW u n w) :=
  (exists_sorted_polyComb_mode u w n).choose_spec.1

theorem polyComb_tensorW (u : List ℕ) (n : ℤ) (w : List ℕ) (c : ℂ) :
    polyComb c (tensorW u n w) = mode (virYA c (negWordVir c u)) n (negWordVir c w) :=
  ((exists_sorted_polyComb_mode u w n).choose_spec.2 c).symm

/-- The `n`-th product on the polynomial model, `ℂ[X]`-bilinear. -/
noncomputable def tensor (n : ℤ) : PV →ₗ[ℂ[X]] PV →ₗ[ℂ[X]] PV :=
  Finsupp.linearCombination ℂ[X] fun u => Finsupp.linearCombination ℂ[X] fun w => tensorW u n w

@[simp] theorem tensor_single_single (n : ℤ) (u w : List ℕ) (p q : ℂ[X]) :
    tensor n (Finsupp.single u p) (Finsupp.single w q) = (p * q) • tensorW u n w := by
  simp [tensor, Finsupp.linearCombination_single, mul_smul, smul_comm p q]

theorem sorted_tensor (n : ℤ) (A B : PV) : Sorted (tensor n A B) := by
  induction A using Finsupp.induction_linear with
  | zero => simpa using Sorted.zero
  | add A A' hA hA' => rw [map_add, LinearMap.add_apply]; exact hA.add hA'
  | single u p =>
      induction B using Finsupp.induction_linear with
      | zero => simpa using Sorted.zero
      | add B B' hB hB' => rw [map_add]; exact hB.add hB'
      | single w q => rw [tensor_single_single]; exact (sorted_tensorW u n w).smul _

/-- **The polynomial tensor computes the vertex products at every central charge.** -/
theorem polyComb_tensor (n : ℤ) (A B : PV) (c : ℂ) :
    polyComb c (tensor n A B) = mode (virYA c (polyComb c A)) n (polyComb c B) := by
  induction A using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]; rfl
  | add A A' hA hA' =>
      rw [map_add, LinearMap.add_apply, map_add, hA, hA', map_add, map_add, mode_add,
        LinearMap.add_apply]
  | single u p =>
      induction B using Finsupp.induction_linear with
      | zero => simp
      | add B B' hB hB' => rw [map_add, map_add, hB, hB', map_add, map_add]
      | single w q =>
          rw [tensor_single_single, polyComb_smul, polyComb_tensorW, polyComb_single,
            polyComb_single]
          simp only [map_smul, mode_smul, LinearMap.smul_apply, smul_smul, eval_mul, mul_comm]

/-! ## Constant coordinates at a fixed central charge -/

/-- The sorted coordinates of a vector at a fixed `c`, as constant polynomials. -/
noncomputable def lift (c : ℂ) : VirUniv c →ₗ[ℂ] PV :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap ℂ ℂ[X])).comp
    ((Finsupp.lmapDomain ℂ ℂ Subtype.val).comp (sortedBasisVir c).repr.toLinearMap)

theorem lift_basis (c : ℂ) (w : {w : List ℕ // SortedWord w}) :
    lift c (negWordVir c w.1) = Finsupp.single w.1 1 := by
  rw [← sortedBasisVir_apply]
  simp only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single]
  simp

theorem sorted_lift (c : ℂ) (x : VirUniv c) : Sorted (lift c x) := by
  intro u hu
  have h1 : u ∈ (Finsupp.mapDomain Subtype.val ((sortedBasisVir c).repr x)).support := by
    by_contra h
    rw [Finsupp.notMem_support_iff] at h
    exact (Finsupp.mem_support_iff.mp hu) (by simp [lift, h])
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h1)
  exact v.2

theorem polyComb_csmul (c a : ℂ) (P : PV) : polyComb c (a • P) = a • polyComb c P := by
  rw [show a • P = Polynomial.C a • P by
    ext u n; simp [Polynomial.coeff_C_mul, Finsupp.smul_apply]]
  rw [polyComb_smul, eval_C]

/-- `polyComb c` as a `ℂ`-linear map. -/
noncomputable def polyCombL (c : ℂ) : PV →ₗ[ℂ] VirUniv c where
  toFun := polyComb c
  map_add' := map_add _
  map_smul' := polyComb_csmul c

/-- The constant coordinates reconstruct the vector. -/
theorem polyComb_lift (c : ℂ) (x : VirUniv c) : polyComb c (lift c x) = x := by
  have h : (polyCombL c).comp (lift c) = LinearMap.id := by
    refine (sortedBasisVir c).ext fun w => ?_
    rw [LinearMap.comp_apply, sortedBasisVir_apply, lift_basis]
    simp [polyCombL]
  exact LinearMap.congr_fun h x

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.polyComb_tensor
#print axioms VOA.VirPoly.sorted_tensor
#print axioms VOA.VirPoly.polyComb_lift
end AxiomAudit
