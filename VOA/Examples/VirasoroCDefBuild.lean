/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroPolyDeriv
import VOA.Examples.VirasoroCDeformation

/-!
# Building `∂_c Y` on `V(c,0)`, part 1: definition, truncation, vacuum, creation

This is step 3(C1) of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`). At a fixed central
charge `c`:

  `Y₁(x)₍ₖ₎ y := polyComb c (tensor' k (lift c x) (lift c y))`,

that is, the `c`-derivative of the polynomial structure constants, evaluated at `c`.

* `Bounded`: energy bounds, with `bounded_tensor` and `bounded_tensor'`.
* `tensor_vac_left`, `tensor_vac_right`: the vacuum and creation axioms as identities in `PV`, and
  their derivatives `tensor'_vac_left` and `tensor'_vac_right`.
* `Y1 c`, `mode_Y1`, and `mode_Y1_polyComb`, which evaluates `tensor'` on sorted inputs.
* `Y1_truncation`, `Y1_vacuum`, `Y1_creation`.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-! ## Energy bounds -/

/-- All words in the support have energy at most `N`. -/
def Bounded (P : PV) (N : ℤ) : Prop := ∀ u ∈ P.support, (energyVir u : ℤ) ≤ N

theorem eq_zero_of_bounded_neg {P : PV} {N : ℤ} (hP : Bounded P N) (hN : N < 0) : P = 0 := by
  ext u : 1
  by_contra h
  have := hP u (Finsupp.mem_support_iff.mpr h)
  omega

theorem Bounded.add {P Q : PV} {N : ℤ} (hP : Bounded P N) (hQ : Bounded Q N) :
    Bounded (P + Q) N := fun u hu =>
  (Finset.mem_union.mp (Finsupp.support_add hu)).elim (hP u) (hQ u)

theorem Bounded.smul {P : PV} {N : ℤ} (r : ℂ[X]) (hP : Bounded P N) : Bounded (r • P) N :=
  fun u hu => hP u (Finsupp.support_smul hu)

theorem bounded_sum {ι : Type*} (s : Finset ι) (f : ι → PV) {N : ℤ}
    (hf : ∀ i ∈ s, Bounded (f i) N) : Bounded (∑ i ∈ s, f i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => intro u hu; simp at hu
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem Bounded.D {P : PV} {N : ℤ} (hP : Bounded P N) : Bounded (VirPoly.D P) N := fun u hu => by
  apply hP u
  rw [Finsupp.mem_support_iff] at hu ⊢
  intro h; exact hu (by simp [h])

theorem tensor_eq_sum (k : ℤ) (A B : PV) :
    tensor k A B = ∑ u ∈ A.support, ∑ w ∈ B.support, (A u * B w) • tensorW u k w := by
  conv_lhs => rw [← Finsupp.sum_single A, ← Finsupp.sum_single B]
  simp [Finsupp.sum, map_sum, Finset.sum_comm (s := A.support)]

theorem tensor'_eq_sum (k : ℤ) (A B : PV) :
    tensor' k A B = ∑ u ∈ A.support, ∑ w ∈ B.support, (A u * B w) • D (tensorW u k w) := by
  conv_lhs => rw [← Finsupp.sum_single A, ← Finsupp.sum_single B]
  simp [Finsupp.sum, map_sum, Finset.sum_comm (s := A.support)]

theorem bounded_tensorW (u : List ℕ) (k : ℤ) (w : List ℕ) {a b : ℤ}
    (hu : (energyVir u : ℤ) ≤ a) (hw : (energyVir w : ℤ) ≤ b) :
    Bounded (tensorW u k w) (a + b - k - 1) := fun v hv => by
  rw [energy_tensorW u k w v hv]; omega

theorem bounded_tensor (k : ℤ) {A B : PV} {a b : ℤ} (hA : Bounded A a) (hB : Bounded B b) :
    Bounded (tensor k A B) (a + b - k - 1) := by
  rw [tensor_eq_sum]
  exact bounded_sum _ _ fun u hu => bounded_sum _ _ fun w hw =>
    (bounded_tensorW u k w (hA u hu) (hB w hw)).smul _

theorem bounded_tensor' (k : ℤ) {A B : PV} {a b : ℤ} (hA : Bounded A a) (hB : Bounded B b) :
    Bounded (tensor' k A B) (a + b - k - 1) := by
  rw [tensor'_eq_sum]
  exact bounded_sum _ _ fun u hu => bounded_sum _ _ fun w hw =>
    (bounded_tensorW u k w (hA u hu) (hB w hw)).D.smul _

/-- Every finitely supported `P` is bounded by the largest energy in its support. -/
theorem bounded_sup (P : PV) : Bounded P (P.support.sup energyVir : ℕ) := fun u hu => by
  exact_mod_cast Finset.le_sup (f := energyVir) hu

/-! ## The vacuum and creation axioms as polynomial identities -/

/-- The vacuum vector of the polynomial model. -/
noncomputable def vacP : PV := Finsupp.single [] 1

theorem sorted_vacP : Sorted vacP := by
  intro u hu
  simp only [vacP, Finsupp.mem_support_iff, Finsupp.single_apply] at hu
  split_ifs at hu with h
  · exact h ▸ sortedWord_nil
  · exact absurd rfl hu

theorem polyComb_vacP (c : ℂ) : polyComb c vacP = vacVec c := by simp [vacP]

theorem D_vacP : D vacP = 0 := by simp [vacP]

/-- `𝟙₍ₖ₎ B = δ_{k,−1} B`, as an identity in `PV`. -/
theorem tensor_vac_left (k : ℤ) {B : PV} (hB : Sorted B) :
    tensor k vacP B = if k = -1 then B else 0 := by
  refine polyComb_injective (sorted_tensor _ _ _) (by split_ifs; exacts [hB, Sorted.zero])
    fun c => ?_
  rw [polyComb_tensor, polyComb_vacP]
  have h := PreVertexAlgebra.smul_vacuum_left (virasoroVOA c).toPreVertexAlgebra k (polyComb c B)
  change mode (virYA c (vacVec c)) k (polyComb c B) = _ at h
  rw [h]
  split_ifs <;> simp

/-- `A₍ₖ₎ 𝟙 = δ_{k,−1} A` for `k ≥ −1`, as an identity in `PV`. -/
theorem tensor_vac_right {k : ℤ} (hk : -1 ≤ k) {A : PV} (hA : Sorted A) :
    tensor k A vacP = if k = -1 then A else 0 := by
  refine polyComb_injective (sorted_tensor _ _ _) (by split_ifs; exacts [hA, Sorted.zero])
    fun c => ?_
  rw [polyComb_tensor, polyComb_vacP]
  split_ifs with h
  · subst h
    exact PreVertexAlgebra.smul_vacuum_neg_one (virasoroVOA c).toPreVertexAlgebra (polyComb c A)
  · rw [map_zero]
    exact PreVertexAlgebra.smul_vacuum_nonneg (virasoroVOA c).toPreVertexAlgebra (polyComb c A)
      (by omega)

theorem tensor'_vac_left (k : ℤ) {B : PV} (hB : Sorted B) : tensor' k vacP B = 0 := by
  have h := congrArg D (tensor_vac_left k hB)
  rw [D_tensor, D_vacP, map_zero, LinearMap.zero_apply, add_zero, tensor_vac_left k hB.D] at h
  split_ifs at h with hk
  · exact add_eq_right.mp h
  · simpa using h

theorem tensor'_vac_right {k : ℤ} (hk : -1 ≤ k) {A : PV} (hA : Sorted A) :
    tensor' k A vacP = 0 := by
  have h := congrArg D (tensor_vac_right hk hA)
  rw [D_tensor, D_vacP, map_zero, add_zero, tensor_vac_right hk hA.D] at h
  split_ifs at h with hk'
  · exact add_eq_right.mp h
  · simpa using h

/-! ## The deformation `Y₁` at a fixed central charge -/

theorem smul_eq_C_smul (a : ℂ) (P : PV) : a • P = Polynomial.C a • P := by
  ext u n; simp [Polynomial.coeff_C_mul, Finsupp.smul_apply]

theorem lift_vac (c : ℂ) : lift c (vacVec c) = vacP :=
  lift_basis c ⟨[], sortedWord_nil⟩

/-- The `k`-th product of `Y₁` at `c`, bilinear. -/
noncomputable def Y1map (c : ℂ) (k : ℤ) : VirUniv c →ₗ[ℂ] VirUniv c →ₗ[ℂ] VirUniv c :=
  LinearMap.mk₂ ℂ (fun x y => polyComb c (tensor' k (lift c x) (lift c y)))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun a x y => by
      show polyComb c (tensor' k (lift c (a • x)) (lift c y))
        = a • polyComb c (tensor' k (lift c x) (lift c y))
      rw [map_smul (lift c), smul_eq_C_smul, map_smul, LinearMap.smul_apply, polyComb_smul,
        eval_C])
    (fun x y y' => by simp only [map_add])
    (fun a x y => by
      show polyComb c (tensor' k (lift c x) (lift c (a • y)))
        = a • polyComb c (tensor' k (lift c x) (lift c y))
      rw [map_smul (lift c), smul_eq_C_smul, map_smul, polyComb_smul, eval_C])

/-- **`∂_c Y` at `c`**: the first-order correction field. -/
noncomputable def Y1 (c : ℂ) : VirUniv c →ₗ[ℂ] FormalDist (Module.End ℂ (VirUniv c)) where
  toFun x := fun t => Y1map c (-t - 1) x
  map_add' x y := by funext t; simp
  map_smul' a x := by funext t; simp

theorem mode_Y1 (c : ℂ) (x : VirUniv c) (k : ℤ) (y : VirUniv c) :
    mode (Y1 c x) k y = polyComb c (tensor' k (lift c x) (lift c y)) := by
  rw [mode_apply]
  show Y1map c (-(-k - 1) - 1) x y = _
  rw [show -(-k - 1) - 1 = k by ring]
  rfl

/-- On sorted inputs, `Y₁` is computed by `tensor'`. -/
theorem mode_Y1_polyComb (c : ℂ) {A B : PV} (hA : Sorted A) (hB : Sorted B) (k : ℤ) :
    mode (Y1 c (polyComb c A)) k (polyComb c B) = polyComb c (tensor' k A B) := by
  rw [mode_Y1, lift_polyComb c hA, lift_polyComb c hB, ← polyComb_bilin]

theorem Y1_truncation (c : ℂ) (x y : VirUniv c) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y1 c x) n y = 0 := by
  refine ⟨((lift c x).support.sup energyVir : ℕ) + ((lift c y).support.sup energyVir : ℕ),
    fun n hn => ?_⟩
  rw [mode_Y1, eq_zero_of_bounded_neg (bounded_tensor' n (bounded_sup _) (bounded_sup _))
    (by omega), map_zero]

theorem Y1_vacuum (c : ℂ) : Y1 c (vacVec c) = 0 := by
  funext t
  refine LinearMap.ext fun y => ?_
  have h := mode_Y1 c (vacVec c) (-t - 1) y
  rw [mode_apply, show -(-t - 1) - 1 = t by ring, lift_vac,
    tensor'_vac_left _ (sorted_lift c y), map_zero] at h
  rw [h]
  rfl

theorem Y1_creation (c : ℂ) (u : VirUniv c) (n : ℤ) (hn : -1 ≤ n) :
    mode (Y1 c u) n (vacVec c) = 0 := by
  rw [mode_Y1, lift_vac, tensor'_vac_right hn (sorted_lift c u), map_zero]

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.bounded_tensor'
#print axioms VOA.VirPoly.tensor'_vac_left
#print axioms VOA.VirPoly.tensor'_vac_right
#print axioms VOA.VirPoly.Y1_truncation
#print axioms VOA.VirPoly.Y1_vacuum
#print axioms VOA.VirPoly.Y1_creation
end AxiomAudit
