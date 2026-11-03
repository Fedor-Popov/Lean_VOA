/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroCDefJacobi

/-!
# `V(c,0)` is not rigid: `∂_c Y` is a graded, non-trivial first-order deformation

This is step 3(D), the last step of the `∂_c` route (the steps are listed in `VirasoroPolyStructure`).

* `cDeformation_isGraded`: `∂_c Y` preserves the energy grading.
* `cDeformation_omega_one`: `ω¹₍₁₎ω = 0`, because `ω₍₁₎ω = 2ω` carries no `c`.
* `cDeformation_omega_three`: `ω¹₍₃₎ω = ½𝟙`, because `ω₍₃₎ω = (c/2)𝟙`.
* `isCDeformation_cDeformation : VirCDef.IsCDeformation c (cDeformation c)`.
* `not_isRigidGraded_virasoroVOA : ¬ Deform.IsRigidGraded (virasoroVOA c)`, for **every** `c ∈ ℂ`.
  This is the first machine-checked non-rigid VOA in the library.
-/

namespace VOA.VirPoly

open VOA VOA.VirModule Polynomial

/-! ## Grading -/

/-- All words in the support have energy exactly `N`. -/
def Homog (P : PV) (N : ℤ) : Prop := ∀ u ∈ P.support, (energyVir u : ℤ) = N

theorem homog_sum {ι : Type*} (s : Finset ι) (f : ι → PV) {N : ℤ}
    (hf : ∀ i ∈ s, Homog (f i) N) : Homog (∑ i ∈ s, f i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => intro u hu; simp at hu
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      intro u hu
      exact (Finset.mem_union.mp (Finsupp.support_add hu)).elim
        (hf a (Finset.mem_insert_self a s) u) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) u)

theorem homog_lift (c : ℂ) {N : ℤ} {x : VirUniv c} (hx : x ∈ gradingVir c N) :
    Homog (lift c x) N := by
  intro u hu
  have h1 : u ∈ (Finsupp.mapDomain Subtype.val ((sortedBasisVir c).repr x)).support := by
    by_contra h
    rw [Finsupp.notMem_support_iff] at h
    exact (Finsupp.mem_support_iff.mp hu) (by simp [lift, h])
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support h1)
  exact repr_support_energy c hx v hv

theorem homog_tensor' (k : ℤ) {A B : PV} {a b : ℤ} (hA : Homog A a) (hB : Homog B b) :
    Homog (tensor' k A B) (a + b - k - 1) := by
  rw [tensor'_eq_sum]
  refine homog_sum _ _ fun u hu => homog_sum _ _ fun w hw => ?_
  intro v hv
  have hv' : v ∈ (tensorW u k w).support := by
    have h2 := Finsupp.support_smul hv
    rw [Finsupp.mem_support_iff] at h2 ⊢
    intro h; exact h2 (by simp [h])
  rw [energy_tensorW u k w v hv', hA u hu, hB w hw]

theorem polyComb_mem_grading (c : ℂ) {P : PV} {N : ℤ} (hP : Homog P N) :
    polyComb c P ∈ gradingVir c N := by
  rw [polyComb_eq_sum]
  refine Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ ?_
  have := negWord_mem_gradingVir c u
  rwa [hP u hu] at this

theorem cDeformation_isGraded (c : ℂ) : (cDeformation c).IsGraded := by
  intro k ℓ u hu v hv n
  change mode (Y1 c u) n v ∈ gradingVir c (k + ℓ - n - 1)
  rw [mode_Y1]
  exact polyComb_mem_grading c (homog_tensor' n (homog_lift c hu) (homog_lift c hv))

/-! ## The two structure constants at `ω` -/

theorem lift_omega (c : ℂ) : lift c (omegaVir c) = Finsupp.single [0] 1 :=
  lift_basis c ⟨[0], sortedWord_singleton 0⟩

theorem sorted_single {u : List ℕ} (hu : SortedWord u) (p : ℂ[X]) :
    Sorted (Finsupp.single u p) := by
  intro v hv
  rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hv
  split_ifs at hv with h
  · exact h ▸ hu
  · exact absurd rfl hv

theorem tensorW_omega_one : tensorW [0] 1 [0] = Finsupp.single [0] (Polynomial.C 2) := by
  refine polyComb_injective (sorted_tensorW _ _ _) (sorted_single (sortedWord_singleton 0) _)
    fun c => ?_
  rw [polyComb_tensorW, polyComb_single, eval_C]
  exact VirCDef.conformal_smul_one (virasoroVOA c)

theorem tensorW_omega_three :
    tensorW [0] 3 [0] = Finsupp.single [] (Polynomial.C (2⁻¹ : ℂ) * X) := by
  refine polyComb_injective (sorted_tensorW _ _ _) (sorted_single sortedWord_nil _) fun c => ?_
  rw [polyComb_tensorW, polyComb_single]
  have h := VirCDef.conformal_smul_three (virasoroVOA c)
  change mode (virYA c (omegaVir c)) 3 (omegaVir c) = (c / 2) • vacVec c at h
  rw [show negWordVir c [0] = omegaVir c from rfl, h, eval_mul, eval_C, eval_X,
    div_eq_mul_inv, mul_comm]
  rfl

theorem cDeformation_omega_one (c : ℂ) :
    (cDeformation c).smul₁ (omegaVir c) 1 (omegaVir c) = 0 := by
  change mode (Y1 c (omegaVir c)) 1 (omegaVir c) = 0
  rw [mode_Y1, lift_omega, tensor'_single_single, tensorW_omega_one, D_single,
    derivative_C, Finsupp.single_zero, smul_zero, map_zero]

theorem cDeformation_omega_three (c : ℂ) :
    (cDeformation c).smul₁ (omegaVir c) 3 (omegaVir c) = (2⁻¹ : ℂ) • vacVec c := by
  change mode (Y1 c (omegaVir c)) 3 (omegaVir c) = _
  rw [mode_Y1, lift_omega, tensor'_single_single, tensorW_omega_three, D_single, one_mul,
    one_smul, polyComb_single]
  simp

/-- **`∂_c Y` has the `∂/∂c` normalisation.** -/
theorem isCDeformation_cDeformation (c : ℂ) : VirCDef.IsCDeformation c (cDeformation c) :=
  ⟨cDeformation_isGraded c, cDeformation_omega_one c, cDeformation_omega_three c⟩

/-- **`V(c,0)` is not rigid**, at every central charge: `∂_c Y` is a graded first-order
deformation that is not a coboundary. -/
theorem not_isRigidGraded_virasoroVOA (c : ℂ) : ¬ Deform.IsRigidGraded (virasoroVOA c) :=
  VirCDef.not_isRigidGraded_of_isCDeformation c (isCDeformation_cDeformation c)

end VOA.VirPoly

section AxiomAudit
#print axioms VOA.VirPoly.cDeformation_isGraded
#print axioms VOA.VirPoly.isCDeformation_cDeformation
#print axioms VOA.VirPoly.not_isRigidGraded_virasoroVOA
end AxiomAudit
