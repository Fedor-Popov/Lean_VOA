import VOA.Moonshine.MoonshineCNVnatSectorOperators
import VOA.Moonshine.MoonshineCNTensorGrading
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The finite integer grading of the actual moonshine string sector -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster TensorFieldLift
open scoped TensorProduct

/-- Matter weight plus polynomial level plus half the momentum norm. -/
def vnatSectorWeight (x y N : ℤ) : Submodule ℂ (Vnat ⊗[ℂ] hypFock) :=
  Submodule.span ℂ {t | ∃ (i j : ℤ) (v : Vnat) (p : hypFock),
    v ∈ VnatVOA.grading i ∧ p ∈ hypLevel j ∧ i + j + x * y = N ∧ v ⊗ₜ[ℂ] p = t}

theorem vnatSectorWeight_tmul (x y i j : ℤ) (v : Vnat) (p : hypFock)
    (hv : v ∈ VnatVOA.grading i) (hp : p ∈ hypLevel j) :
    v ⊗ₜ[ℂ] p ∈ vnatSectorWeight x y (i + j + x * y) :=
  Submodule.subset_span ⟨i, j, v, p, hv, hp, rfl, rfl⟩

theorem vnatSectorWeight_energy (x y N : ℤ) (u : Vnat ⊗[ℂ] hypFock)
    (hu : u ∈ vnatSectorWeight x y N) : vnatHypMode x y 0 u = (N : ℂ) • u := by
  induction hu using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, v, p, hv, hp, hij, rfl⟩ := ht
    simp only [vnatHypMode, tensorTranslation, LinearMap.add_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      hypSugawara_zero_level _ _ _ _ hp, nearVirasoroMode, zero_add,
      VnatVOA.toNearVOA.L0_grading v hv, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    rw [← TensorProduct.add_tmul, ← add_smul]
    congr 2
    rw [← hij]
    push_cast
    ring
  | zero => simp only [map_zero, smul_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb, smul_add]
  | smul c a _ ha => simp only [map_smul, ha, smul_comm c]

theorem vnatSectorWeight_top (x y : ℤ) : (⨆ N, vnatSectorWeight x y N) = ⊤ := by
  apply TensorVA.eq_top_of_tmul_mem VnatVOA.isInternal.submodule_iSup_eq_top
    hypLevel_isInternal.submodule_iSup_eq_top
  intro i j v hv p hp
  exact Submodule.mem_iSup_of_mem _ (vnatSectorWeight_tmul x y i j v p hv hp)

theorem vnatSectorWeight_isInternal (x y : ℤ) :
    DirectSum.IsInternal (vnatSectorWeight x y) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ (vnatSectorWeight_top x y)
  have hi := (Module.End.eigenspaces_iSupIndep (vnatHypMode x y 0)).comp
    (show Function.Injective (fun n : ℤ => (n : ℂ)) from Int.cast_injective)
  exact hi.mono fun N u hu => Module.End.mem_eigenspace_iff.mpr
    (vnatSectorWeight_energy x y N u hu)

theorem vnatSectorWeight_eq_eigenspace (x y N : ℤ) :
    vnatSectorWeight x y N = (vnatHypMode x y 0).eigenspace (N : ℂ) := by
  have h := VOA.Deform.iSup_inf_eq_of_le_independent (p := vnatSectorWeight x y)
    (q := fun Q : ℤ => (vnatHypMode x y 0).eigenspace (Q : ℂ))
    (fun Q u hu => Module.End.mem_eigenspace_iff.mpr (vnatSectorWeight_energy x y Q u hu))
    ((Module.End.eigenspaces_iSupIndep _).comp
      (show Function.Injective (fun n : ℤ => (n : ℂ)) from Int.cast_injective)) N
  simpa only [vnatSectorWeight_top, top_inf_eq] using h.symm

theorem vnatSectorWeight_negative (x y N : ℤ) (hN : N < x * y) :
    vnatSectorWeight x y N = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro t ⟨i, j, v, p, hv, hp, hij, rfl⟩
  by_cases hi : i < 0
  · rw [VnatVOA.positivity i hi] at hv
    rw [show v = 0 from hv, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  · have hj : j < 0 := by omega
    rw [hypLevel_negative j hj] at hp
    rw [show p = 0 from hp, TensorProduct.tmul_zero]
    exact Submodule.zero_mem _

/-- A finite-dimensional pair of homogeneous factors mapped into the sector. -/
def vnatSectorWeight_pairRange (i j : ℤ) : Submodule ℂ (Vnat ⊗[ℂ] hypFock) :=
  LinearMap.range (TensorProduct.map (VnatVOA.grading i).subtype (hypLevel j).subtype)

theorem vnatSectorWeight_finiteDimensional (x y N : ℤ) :
    FiniteDimensional ℂ (vnatSectorWeight x y N) := by
  let S (k : Fin ((N - x * y).toNat + 1)) :=
    vnatSectorWeight_pairRange (k : ℤ) (N - x * y - k)
  haveI (k : Fin ((N - x * y).toNat + 1)) : FiniteDimensional ℂ (S k) := by
    haveI := VnatVOA.finrank (k : ℤ)
    haveI := hypLevel_finiteDimensional (N - x * y - k)
    haveI : FiniteDimensional ℂ
        ((VnatVOA.grading (k : ℤ)) ⊗[ℂ] (hypLevel (N - x * y - k))) := inferInstance
    exact Module.Finite.range
      (TensorProduct.map (VnatVOA.grading (k : ℤ)).subtype
        (hypLevel (N - x * y - k)).subtype)
  apply Submodule.finiteDimensional_of_le (S₂ := ⨆ k, S k)
  apply Submodule.span_le.mpr
  rintro t ⟨i, j, v, p, hv, hp, hij, rfl⟩
  by_cases hi : i < 0
  · rw [VnatVOA.positivity i hi] at hv
    rw [show v = 0 from hv, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  by_cases hj : j < 0
  · rw [hypLevel_negative j hj] at hp
    rw [show p = 0 from hp, TensorProduct.tmul_zero]
    exact Submodule.zero_mem _
  let k : Fin ((N - x * y).toNat + 1) := ⟨i.toNat, by omega⟩
  apply Submodule.mem_iSup_of_mem k
  have hk : (k : ℤ) = i := by dsimp [k]; omega
  change _ ∈ vnatSectorWeight_pairRange (k : ℤ) (N - x * y - k)
  rw [hk, show N - x * y - i = j by omega]
  exact ⟨⟨v, hv⟩ ⊗ₜ[ℂ] ⟨p, hp⟩, rfl⟩

end VOA.Moonshine.ConwayNorton
