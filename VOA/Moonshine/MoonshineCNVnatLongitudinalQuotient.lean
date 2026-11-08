import VOA.Moonshine.MoonshineCNVnatSectorEvaluation
import VOA.Moonshine.MoonshineCNStringSymmetry

/-! # The longitudinal radical quotient is the actual matter weight space -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster SimpleNat
open scoped TensorProduct

local instance vnatStringWeightAddCommGroup (x y : ℤ) (a : Fin 2) (N : ℤ) :
    AddCommGroup ((vnatStringModule x y a).wt N) := Submodule.addCommGroup _

local instance vnatStringSliceAddCommGroup (x y : ℤ) (a : Fin 2)
    (U : Submodule ℂ (Vnat ⊗[ℂ] hypFock)) (N : ℤ) :
    AddCommGroup ((vnatStringModule x y a).weightSlice U N) := Submodule.addCommGroup _

theorem vnatStringModule_kVacuum (x y : ℤ) (a : Fin 2) :
    (vnatStringModule x y a).kVacuum = hypTensorOneFamily a :=
  (hypTensorOneFamily_eq_commonKernel a (if a = 0 then (x : ℂ) else y)).symm

def vnatKVacuumEvaluation (x y : ℤ) (a : Fin 2) (N : ℤ) :
    (vnatStringModule x y a).weightSlice (vnatStringModule x y a).kVacuum N →ₗ[ℂ]
      VnatVOA.grading (N - x * y) where
  toFun u := ⟨vnatSectorEval u.val.val, vnatSectorEval_weight x y N u.val u.val.property⟩
  map_add' u v := Subtype.ext (vnatSectorEval.map_add u.val.val v.val.val)
  map_smul' c u := Subtype.ext (vnatSectorEval.map_smul c u.val.val)

theorem vnatKVacuumEvaluation_surjective (x y : ℤ) (a : Fin 2) (N : ℤ) :
    Function.Surjective (vnatKVacuumEvaluation x y a N) := by
  intro v
  have hk : v.val ⊗ₜ[ℂ] (1 : hypFock) ∈ (vnatStringModule x y a).kVacuum := by
    rw [vnatStringModule_kVacuum]
    exact hypTensorOneFamily_tmul a v.val 1 (by simpa using hypOneFamily_constant_mem a 1)
  refine ⟨⟨⟨v.val ⊗ₜ[ℂ] 1, vnatMatterVacuumTensor_mem x y N v.val v.property⟩, hk⟩, ?_⟩
  apply Subtype.ext
  change vnatSectorEval (v.val ⊗ₜ[ℂ] 1) = v.val
  simp [vnatSectorEval_tmul]

theorem vnatKVacuumEvaluation_radical (x y : ℤ) (a : Fin 2) (N : ℤ)
    (u : (vnatStringModule x y a).weightSlice (vnatStringModule x y a).kVacuum N) :
    u ∈ (vnatStringModule x y a).weightRadical (vnatStringModule x y a).kVacuum N ↔
      vnatKVacuumEvaluation x y a N u = 0 := by
  let M := vnatStringModule x y a
  have hform (u v : M.weightSlice M.kVacuum N) :
      M.B u.val v.val = natForm (vnatKVacuumEvaluation x y a N u)
        (vnatKVacuumEvaluation x y a N v) :=
    vnatSectorEval_oneFamily_form a u.val v.val
      ((vnatStringModule_kVacuum x y a) ▸ u.property)
      ((vnatStringModule_kVacuum x y a) ▸ v.property)
  rw [M.mem_weightRadical_iff]
  constructor
  · intro hu
    apply (vnatVOA_invariantForm_nondegenerate vnat_twistedLocality).2.2.2 (N - x * y) |>.1
    intro v
    obtain ⟨w, rfl⟩ := vnatKVacuumEvaluation_surjective x y a N v
    exact (hform u w).symm.trans (hu w)
  · intro hu v
    rw [hform, hu]
    exact natForm.map_zero₂ _

theorem vnatKVacuumEvaluation_ker (x y : ℤ) (a : Fin 2) (N : ℤ) :
    (vnatStringModule x y a).weightRadical (vnatStringModule x y a).kVacuum N =
      LinearMap.ker (vnatKVacuumEvaluation x y a N) := by
  ext u
  exact vnatKVacuumEvaluation_radical x y a N u

/-- The kernel of evaluation is exactly the intersection with actual negative K ranges. -/
theorem vnatKVacuum_augmentation (x y : ℤ) (a : Fin 2) (N : ℤ)
    (u : (vnatStringModule x y a).weightSlice (vnatStringModule x y a).kVacuum N) :
    (u.val : Vnat ⊗[ℂ] hypFock) ∈ (vnatStringModule x y a).kSpurious ↔
      vnatKVacuumEvaluation x y a N u = 0 := by
  rw [← vnatKVacuumEvaluation_radical]
  change _ ↔ u.val ∈ (vnatStringModule x y a).formRadicalIn _ N
  rw [StringModule.kVacuum_radical_eq]
  exact ⟨fun h => ⟨u.property, h⟩, fun h => h.2⟩

def vnatKVacuumQuotientEquiv (x y : ℤ) (a : Fin 2) (N : ℤ) :
    (vnatStringModule x y a).weightRadicalQuotient (vnatStringModule x y a).kVacuum N ≃ₗ[ℂ]
      VnatVOA.grading (N - x * y) :=
  (Submodule.quotEquivOfEq _ _ (vnatKVacuumEvaluation_ker x y a N)).trans
    (LinearMap.quotKerEquivOfSurjective _ (vnatKVacuumEvaluation_surjective x y a N))

theorem vnatKVacuumQuotientEquiv_mk (x y : ℤ) (a : Fin 2) (N : ℤ)
    (u : (vnatStringModule x y a).weightSlice (vnatStringModule x y a).kVacuum N) :
    vnatKVacuumQuotientEquiv x y a N (Submodule.Quotient.mk u) =
      vnatKVacuumEvaluation x y a N u := rfl

theorem vnatKVacuumQuotientEquiv_isometry (x y : ℤ) (a : Fin 2) (N : ℤ)
    (u v : (vnatStringModule x y a).weightRadicalQuotient (vnatStringModule x y a).kVacuum N) :
    natForm (vnatKVacuumQuotientEquiv x y a N u) (vnatKVacuumQuotientEquiv x y a N v) =
      (vnatStringModule x y a).radicalQuotientForm (vnatStringModule x y a).kVacuum N u v := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact (vnatSectorEval_oneFamily_form a u.val v.val
    ((vnatStringModule_kVacuum x y a) ▸ u.property)
    ((vnatStringModule_kVacuum x y a) ▸ v.property)).symm

theorem vnatKVacuumQuotientEquiv_equivariant (x y : ℤ) (a : Fin 2) (N : ℤ) (g : AutVnat)
    (u : (vnatStringModule x y a).weightRadicalQuotient (vnatStringModule x y a).kVacuum N) :
    vnatKVacuumQuotientEquiv x y a N
      ((vnatStringGroupAction x y a).stableWeightQuotientAction _
        (vnatStringGroupAction x y a).action_preserves_kVacuum N g u) =
      GriessAut.autRestrict g (N - x * y) (vnatKVacuumQuotientEquiv x y a N u) := by
  induction u using Submodule.Quotient.induction_on with | _ u =>
  apply Subtype.ext
  exact vnatSectorEval_action g u.val

end VOA.Moonshine.ConwayNorton
