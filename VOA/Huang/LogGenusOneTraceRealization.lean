import VOA.Huang.LogGenusOneWeightTrace
import VOA.Modularity.LogarithmicPseudoTraceBlock

/-! Canonical honest trace realization for every genuine logarithmic module.
The coefficient algebra is the actual scalar algebra; finite projectivity,
mode commutation, and the real VOA zero-mode blocks are constructed here,
so no operational trace-data witness is assumed. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogGenusOne
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open Module (End)
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The genuine global VOA zero mode preserves every true generalized block. -/
theorem logOMod_mem_generalized_weight (N : LogVModule W M) (v : V)
    {b : ℂ} {y : M} (hy : y∈N.weight b) : logOMod N v y∈N.weight b := by
  have hv : v∈⨆ d,W.grading d := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading (motive := fun v => logOMod N v y∈N.weight b) hv ?_ ?_ ?_
  · intro d v hv
    rw [logOMod_homogeneous N hv]
    have he := N.mode_mem_weight hv hy (d-1)
    convert he using 1 <;> push_cast <;> ring
  · beta_reduce
    rw [map_zero,LinearMap.zero_apply]
    exact (N.weight b).zero_mem
  · intro v w hv hw
    rw [map_add,LinearMap.add_apply]
    exact (N.weight b).add_mem hv hw

/-- Actual zero-mode blocks, linear in every VOA insertion. -/
def moduleZeroModeLinear (N : LogVModule W M) (b : ℂ) : V →ₗ[ℂ] End ℂ (N.weight b) where
  toFun v := (logOMod N v).restrict (fun y hy => logOMod_mem_generalized_weight N v hy)
  map_add' v w := by
    ext y
    simp only [LinearMap.restrict_apply,LinearMap.add_apply,map_add,LinearMap.add_apply]
    rfl
  map_smul' s v := by
    ext y
    simp only [LinearMap.restrict_apply,LinearMap.smul_apply,map_smul,LinearMap.smul_apply]
    rfl

@[simp] theorem moduleZeroModeLinear_coe (N : LogVModule W M) (b : ℂ) (v : V) (y : N.weight b) :
    (moduleZeroModeLinear N b v y : M)=logOMod N v y := rfl

/-- The global genuine module zero mode commutes with the full Jordan part. -/
theorem logOMod_commute_nil (N : LogVModule W M) (v : V) :
    Commute (logOMod N v) N.L0nil := by
  ext y
  have hv : v∈⨆ d,W.grading d := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading (motive := fun v =>
    logOMod N v (N.L0nil y)=N.L0nil (logOMod N v y)) hv ?_ ?_ ?_
  · intro d v hv
    rw [logOMod_homogeneous N hv]
    exact (DFunLike.congr_fun (L0nil_comm_mode N v (d-1)) y).symm
  · simp
  · intro v w hv hw
    simp only [map_add,LinearMap.add_apply,hv,hw]

/-- The actual scalar-coefficient trace data exists on every generalized
module. Each finite weight space is automatically finite projective over ℂ. -/
def actualTraceData (N : LogVModule W M) : LogPseudoTraceCommutantData N ℂ where
  finite_algebra := inferInstance
  finite_piece b := N.finrank b
  projective_piece b := inferInstance
  phi := idSymmetric ℂ
  mode_commutes a α β v n y hy := by
    simp only [SetLike.val_smul,map_smul]
  zeroModeA := moduleZeroModeLinear N
  zeroModeA_coe b v y := rfl

/-- Actual honest traces therefore satisfy the genuine cyclic, translation,
and Zhu zero-mode identities, without any trace-data witness. -/
theorem actualTrace_isCyclicBlock (N : LogVModule W M) :
    LogPseudoTraceCommutantData.IsLogPseudoTraceCyclicBlock (W := W)
      (actualTraceData N).logPseudoTraceOnePointHom (actualTraceData N).logPseudoCharacter :=
  (actualTraceData N).isLogPseudoTraceCyclicBlock

/-- The actual zero-mode block is precisely the
homogeneous module zero mode. -/
theorem moduleZeroModeLinear_homogeneous (N : LogVModule W M) (b : ℂ)
    {d : ℤ} {v : V} (hv : v∈W.grading d) :
    moduleZeroModeLinear N b v=moduleZeroModePiece N hv b := by
  ext y
  change logOMod N v y=mode (N.YM v) (d-1) y
  rw [logOMod_homogeneous N hv]

end VOA.Huang.LogGenusOne
