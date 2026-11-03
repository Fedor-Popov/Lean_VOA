/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPolyEnergy

/-!
# The `c`-derivative on the polynomial model, and the Leibniz rule

This is step 3(B2) of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`).

* `D : PV →ₗ[ℂ] PV`, the coefficientwise derivative `d/dc`, with `D_smul` (Leibniz for `ℂ[X]`
  scalars).
* `tensor' n`: the tensor with structure constants `D (tensorW u n w)`.
* `D_tensor`: `D (tensor n A B) = tensor' n A B + tensor n (D A) B + tensor n A (D B)`.
* `evalC c`: evaluate every coefficient at `c` and keep it as a constant polynomial.
  `polyComb_bilin` shows that, at `c`, a `ℂ[X]`-bilinear map only sees the values of its arguments at
  `c`.
* `lift_polyComb`: `lift c (polyComb c A) = evalC c A` for sorted `A`.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-- The coefficientwise derivative `d/dc`. -/
noncomputable def D : PV →ₗ[ℂ] PV := Finsupp.mapRange.linearMap (Polynomial.derivative (R := ℂ))

@[simp] theorem D_apply (P : PV) (u : List ℕ) : D P u = derivative (P u) := rfl

@[simp] theorem D_single (u : List ℕ) (p : ℂ[X]) :
    D (Finsupp.single u p) = Finsupp.single u (derivative p) := by
  ext v; simp [Finsupp.single_apply]; split_ifs <;> simp

theorem D_smul (r : ℂ[X]) (P : PV) : D (r • P) = derivative r • P + r • D P := by
  ext u; simp [derivative_mul]

theorem Sorted.D {P : PV} (hP : Sorted P) : Sorted (VirPoly.D P) := fun u hu => by
  apply hP u
  rw [Finsupp.mem_support_iff] at hu ⊢
  intro h; exact hu (by simp [h])

/-- The derived tensor: structure constants `d/dc (u₍ₙ₎w)`. -/
noncomputable def tensor' (n : ℤ) : PV →ₗ[ℂ[X]] PV →ₗ[ℂ[X]] PV :=
  Finsupp.linearCombination ℂ[X] fun u => Finsupp.linearCombination ℂ[X] fun w => D (tensorW u n w)

@[simp] theorem tensor'_single_single (n : ℤ) (u w : List ℕ) (p q : ℂ[X]) :
    tensor' n (Finsupp.single u p) (Finsupp.single w q) = (p * q) • D (tensorW u n w) := by
  simp [tensor', Finsupp.linearCombination_single, mul_smul, smul_comm p q]

theorem sorted_tensor' (n : ℤ) (A B : PV) : Sorted (tensor' n A B) := by
  induction A using Finsupp.induction_linear with
  | zero => simpa using Sorted.zero
  | add A A' hA hA' => rw [map_add, LinearMap.add_apply]; exact hA.add hA'
  | single u p =>
      induction B using Finsupp.induction_linear with
      | zero => simpa using Sorted.zero
      | add B B' hB hB' => rw [map_add]; exact hB.add hB'
      | single w q => rw [tensor'_single_single]; exact (sorted_tensorW u n w).D.smul _

/-- **Leibniz rule** for the polynomial tensor. -/
theorem D_tensor (n : ℤ) (A B : PV) :
    D (tensor n A B) = tensor' n A B + tensor n (D A) B + tensor n A (D B) := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A A' hA hA' =>
      simp only [map_add, LinearMap.add_apply, hA, hA']
      abel
  | single u p =>
      induction B using Finsupp.induction_linear with
      | zero => simp
      | add B B' hB hB' =>
          simp only [map_add, hB, hB']
          abel
      | single w q =>
          rw [D_single, D_single, tensor_single_single, D_smul, tensor'_single_single,
            tensor_single_single, tensor_single_single, derivative_mul, add_smul]
          abel

/-! ## Evaluation at a fixed central charge -/

/-- Evaluate every coefficient at `c`, keeping it as a constant polynomial. -/
noncomputable def evalC (c : ℂ) : PV →ₗ[ℂ] PV :=
  Finsupp.mapRange.linearMap ((Algebra.linearMap ℂ ℂ[X]).comp (Polynomial.leval c))

@[simp] theorem evalC_apply (c : ℂ) (P : PV) (u : List ℕ) :
    evalC c P u = Polynomial.C ((P u).eval c) := rfl

theorem evalC_single (c : ℂ) (u : List ℕ) (p : ℂ[X]) :
    evalC c (Finsupp.single u p) = Finsupp.single u (Polynomial.C (p.eval c)) := by
  ext v; simp [Finsupp.single_apply]; split_ifs <;> simp

/-- At `c`, a `ℂ[X]`-linear map into `PV` only sees the values of its argument at `c`. -/
theorem polyComb_linear (c : ℂ) (T : PV →ₗ[ℂ[X]] PV) (A : PV) :
    polyComb c (T A) = polyComb c (T (evalC c A)) := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add A A' hA hA' => rw [map_add, map_add, hA, hA', ← map_add, ← map_add, map_add (evalC c)]
  | single u p =>
      rw [evalC_single, show Finsupp.single u p = p • Finsupp.single u 1 by simp,
        show Finsupp.single u (Polynomial.C (p.eval c)) = Polynomial.C (p.eval c) • Finsupp.single u 1
          by simp, LinearMap.map_smul T, LinearMap.map_smul T, polyComb_smul, polyComb_smul, eval_C]

/-- The same for a `ℂ[X]`-bilinear map, in both arguments. -/
theorem polyComb_bilin (c : ℂ) (T : PV →ₗ[ℂ[X]] PV →ₗ[ℂ[X]] PV) (A B : PV) :
    polyComb c (T A B) = polyComb c (T (evalC c A) (evalC c B)) := by
  rw [polyComb_linear c (T A) B]
  exact polyComb_linear c (T.flip (evalC c B)) A

/-- `lift` of an evaluation is the evaluation, for sorted `A`. -/
theorem lift_polyComb (c : ℂ) {A : PV} (hA : Sorted A) : lift c (polyComb c A) = evalC c A := by
  ext u : 1
  by_cases hu : SortedWord u
  · have h := repr_polyComb c hA ⟨u, hu⟩
    simp only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lmapDomain_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, evalC_apply]
    rw [show u = (⟨u, hu⟩ : {w : List ℕ // SortedWord w}).1 from rfl,
      Finsupp.mapDomain_apply Subtype.val_injective, h]
    rfl
  · have hA0 : A u = 0 := Finsupp.notMem_support_iff.mp fun h => hu (hA u h)
    simp only [lift, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lmapDomain_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, evalC_apply, hA0, eval_zero,
      map_zero]
    rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨v, rfl⟩; exact hu v.2)]
    simp

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.D_tensor
#print axioms VOA.VirPoly.polyComb_bilin
#print axioms VOA.VirPoly.lift_polyComb
end AxiomAudit
