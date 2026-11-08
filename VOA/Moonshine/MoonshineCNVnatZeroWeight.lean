import VOA.Moonshine.MoonshineCNVnatSectorAction

/-! # The weight-one space and physical states at zero momentum -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster MvPolynomial HeisenbergN TensorFieldLift
open scoped TensorProduct BigOperators

theorem hypWeightOne_exponent (e : (ℕ × Fin 2) →₀ ℕ)
    (he : Finsupp.weight weightFnN e = 1) : ∃ a : Fin 2, e = Finsupp.single (0, a) 1 := by
  have hn : e ≠ 0 := by intro hz; simp [hz] at he
  obtain ⟨v, hv⟩ : ∃ v, e v ≠ 0 := by
    by_contra! h
    exact hn (Finsupp.ext h)
  have hw := Finsupp.weight_sub_single_add (w := weightFnN) hv
  rw [he, weightFnN_apply] at hw
  have hz : Finsupp.weight weightFnN (e - Finsupp.single v 1) = 0 := by omega
  have hv0 : v.1 = 0 := by omega
  have he0 : e - Finsupp.single v 1 = 0 := by
    ext t
    have hle := Finsupp.le_weight weightFnN
      (show weightFnN t ≠ 0 by simp [weightFnN]) (e - Finsupp.single v 1)
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  have h := Finsupp.sub_add_single_one_cancel hv
  rw [he0, zero_add] at h
  refine ⟨v.2, ?_⟩
  simpa only [← hv0, Prod.eta] using h.symm

theorem hypLevel_one_span :
    hypLevel 1 = Submodule.span ℂ (Set.range fun a : Fin 2 => (X (0, a) : hypFock)) := by
  classical
  apply le_antisymm
  · intro p hp
    have hp' : p.IsWeightedHomogeneous weightFnN 1 := by
      simpa only [hypLevel, gradingZN_of_nonneg (by norm_num : (0 : ℤ) ≤ 1)] using hp
    rw [p.as_sum]
    apply Submodule.sum_mem
    intro e he
    obtain ⟨a, ha⟩ := hypWeightOne_exponent e (hp' (mem_support_iff.mp he))
    have hm : monomial e (coeff e p) = coeff e p • X (0, a) := by
      rw [ha, X, smul_monomial, smul_eq_mul, mul_one]
    rw [hm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change X (0, a) ∈ gradingZN 2 1
    rw [gradingZN_of_nonneg (by norm_num : (0 : ℤ) ≤ 1)]
    exact isWeightedHomogeneous_X ℂ weightFnN (0, a)

def vnatZeroBasisVector (a : Fin 2) : Vnat ⊗[ℂ] hypFock :=
  VnatVOA.vacuum ⊗ₜ[ℂ] X (0, a)

theorem vnatZeroBasisVector_mem (a : Fin 2) :
    vnatZeroBasisVector a ∈ vnatSectorWeight 0 0 1 := by
  have hp : X (0, a) ∈ hypLevel 1 := by
    rw [hypLevel_one_span]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact vnatSectorWeight_tmul 0 0 0 1 VnatVOA.vacuum _ VnatVOA.vacuum_mem hp

theorem vnatZeroWeight_span :
    vnatSectorWeight 0 0 1 = Submodule.span ℂ (Set.range vnatZeroBasisVector) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro t ⟨i, j, v, p, hv, hp, hij, rfl⟩
    simp only [mul_zero, add_zero] at hij
    by_cases hi : i < 0
    · rw [VnatVOA.positivity i hi] at hv
      rw [show v = 0 from hv, TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
    by_cases hi0 : i = 0
    · subst i
      have hj : j = 1 := by omega
      subst j
      rw [VnatVOA.vacuum_grade, Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      rw [hypLevel_one_span] at hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨a, rfl⟩ := hp
        change (c • VnatVOA.vacuum) ⊗ₜ[ℂ] X (0, a) ∈ _
        rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add p q _ _ hp hq => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hp hq
      | smul d p _ hp => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ d hp
    by_cases hi1 : i = 1
    · subst i
      rw [VnatVOA_grading_one] at hv
      rw [show v = 0 from hv, TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
    · rw [hypLevel_negative j (by omega)] at hp
      rw [show p = 0 from hp, TensorProduct.tmul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact vnatZeroBasisVector_mem a

theorem vnatZeroBasisVector_physical (a : Fin 2) :
    vnatZeroBasisVector a ∈ (vnatStringModule 0 0 0).physical := by
  rw [StringModule.mem_physical_iff]
  intro j
  change vnatHypMode (0 : ℤ) (0 : ℤ) (j + 1 : ℤ) (vnatZeroBasisVector a) = 0
  simp only [Int.cast_zero]
  by_cases hj : j = 0
  · subst j
    have hm : nearVirasoroMode VnatVOA.toNearVOA 1 VnatVOA.vacuum = 0 :=
      VnatVOA.toPreVertexAlgebra.smul_vacuum_nonneg VnatVOA.conformalVector (by norm_num)
    have hp : hypSugawara 0 0 1 (X (0, a)) = 0 := by
      have he := hypSugawara_positive (0 : ℂ) 0 0 (X (0, a))
      norm_num only [Nat.cast_zero, zero_add] at he
      rw [he]
      simp [hypPositiveSecondOrder, hypLoweringDerivation_X]
    simp only [Nat.cast_zero, zero_add, vnatHypMode, tensorTranslation,
      vnatZeroBasisVector, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, hm, hp, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · have h := vnatSectorWeight_mode 0 0 (j + 1) 1 _ (vnatZeroBasisVector_mem a)
    rw [vnatSectorWeight_negative 0 0 (1 - (j + 1)) (by omega)] at h
    simpa only [Int.cast_zero, Submodule.mem_bot] using h

theorem vnatZeroWeight_physical :
    vnatSectorWeight 0 0 1 ≤ (vnatStringModule 0 0 0).physical := by
  rw [vnatZeroWeight_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact vnatZeroBasisVector_physical a

end VOA.Moonshine.ConwayNorton
