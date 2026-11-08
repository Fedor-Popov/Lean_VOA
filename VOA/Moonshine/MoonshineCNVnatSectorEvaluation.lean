import VOA.Moonshine.MoonshineCNVnatSectorAction

/-! # Constant-polynomial evaluation on the actual longitudinal vacuum space -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat MvPolynomial
open scoped TensorProduct BigOperators

theorem hypTensorOneFamily_induction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Fin 2) {P : V ⊗[ℂ] hypFock → Prop} (hzero : P 0)
    (hadd : ∀ u v, P u → P v → P (u + v))
    (hpure : ∀ v p, p ∈ hypOneFamily a → P (v ⊗ₜ[ℂ] p))
    (u : V ⊗[ℂ] hypFock) (hu : u ∈ hypTensorOneFamily a) : P u := by
  classical
  rw [hypTensor_expansion u]
  apply Finset.sum_induction _ _ hadd hzero
  intro e he
  exact hpure _ _ ((hypTensorSupported_mem _ u).mp hu e (Finsupp.mem_support_iff.mp he))

def vnatSectorEval : (Vnat ⊗[ℂ] hypFock) →ₗ[ℂ] Vnat :=
  (Finsupp.lapply 0).comp hypTensorCoordinates.toLinearMap

theorem vnatSectorEval_tmul (v : Vnat) (p : hypFock) :
    vnatSectorEval (v ⊗ₜ[ℂ] p) = coeff 0 p • v := hypTensorCoordinates_tmul v p 0

theorem hypLevel_constantCoeff_eq_zero (j : ℤ) (hj : j ≠ 0) (p : hypFock)
    (hp : p ∈ hypLevel j) : coeff 0 p = 0 := by
  have h := congrArg constantCoeff (hypSugawara_zero_level 0 0 j p hp)
  rw [hypSugawara_zero_constantCoeff, constantCoeff_smul] at h
  simp only [zero_mul, zero_add, smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hj)

theorem vnatSectorEval_weight (x y N : ℤ) (u : Vnat ⊗[ℂ] hypFock)
    (hu : u ∈ vnatSectorWeight x y N) : vnatSectorEval u ∈ VnatVOA.grading (N - x * y) := by
  induction hu using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, v, p, hv, hp, hij, rfl⟩ := ht
    rw [vnatSectorEval_tmul]
    by_cases hj : j = 0
    · subst j
      rw [show N - x * y = i by omega]
      exact Submodule.smul_mem _ _ hv
    · rw [hypLevel_constantCoeff_eq_zero j hj p hp, zero_smul]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem vnatSectorEval_oneFamily_form (a : Fin 2) (u v : Vnat ⊗[ℂ] hypFock)
    (hu : u ∈ hypTensorOneFamily a) (hv : v ∈ hypTensorOneFamily a) :
    vnatHypForm u v = natForm (vnatSectorEval u) (vnatSectorEval v) := by
  refine hypTensorOneFamily_induction a (P := fun u =>
    vnatHypForm u v = natForm (vnatSectorEval u) (vnatSectorEval v))
    (by simp only [map_zero, LinearMap.zero_apply]) ?_ ?_ u hu
  · intro u w hu hw
    simp only [map_add, LinearMap.add_apply, hu, hw]
  · intro w p hp
    refine hypTensorOneFamily_induction a (P := fun v =>
      vnatHypForm (w ⊗ₜ[ℂ] p) v =
        natForm (vnatSectorEval (w ⊗ₜ[ℂ] p)) (vnatSectorEval v))
      (by simp only [map_zero]) ?_ ?_ v hv
    · intro v z hv hz; simp only [map_add, hv, hz]
    · intro z q hq
      rw [vnatSectorEval_tmul, vnatSectorEval_tmul]
      change hypForm p q * natForm w z = natForm (coeff 0 p • w) (coeff 0 q • z)
      rw [hypOneFamily_form a p q hp hq, LinearMap.map_smul₂, map_smul]
      simp only [smul_eq_mul]
      ring

theorem vnatMatterVacuumTensor_mem (x y N : ℤ) (v : Vnat)
    (hv : v ∈ VnatVOA.grading (N - x * y)) :
    v ⊗ₜ[ℂ] (1 : hypFock) ∈ vnatSectorWeight x y N := by
  have hp : (1 : hypFock) ∈ hypLevel 0 := by
    rw [hypLevel_zero]
    exact Submodule.mem_span_singleton_self _
  convert vnatSectorWeight_tmul x y (N - x * y) 0 v 1 hv hp using 1
  congr 1
  omega

theorem vnatSectorEval_action (g : AutVnat) (u : Vnat ⊗[ℂ] hypFock) :
    vnatSectorEval (vnatSectorAction g u) = g (vnatSectorEval u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | add u v hu hv =>
    change vnatSectorEval (vnatSectorAction g (u + v)) = g.toLinearEquiv (vnatSectorEval (u + v))
    rw [(vnatSectorAction g).map_add, vnatSectorEval.map_add, vnatSectorEval.map_add,
      g.toLinearEquiv.map_add]
    exact congrArg₂ (· + ·) hu hv
  | tmul v p =>
    rw [vnatSectorAction_tmul, vnatSectorEval_tmul, vnatSectorEval_tmul]
    exact (g.toLinearEquiv.map_smul _ _).symm

end VOA.Moonshine.ConwayNorton
