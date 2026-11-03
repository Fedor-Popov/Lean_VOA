import VOA.Modules.LogTensorContraCoordinates

/-! # The nilpotent L(0) part commutes with actual module modes

This is the logarithmic part of coordinate covariance. It is derived from the
actual module vertex operator's L(0) bracket and the generalized grading.
-/
namespace VOA.LogTensor.Contra
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual Jordan-nilpotent part of L(0) commutes with every homogeneous mode. -/
theorem L0nil_comm_mode_homogeneous (N : LogVModule W M) {β : ℤ} {v : V}
    (hv : v ∈ W.grading β) (n : ℤ) :
    N.L0nil * mode (N.YM v) n = mode (N.YM v) n * N.L0nil := by
  apply N.ext_on_weight
  intro α x hx
  change N.L0nil (mode (N.YM v) n x) = mode (N.YM v) n (N.L0nil x)
  have hv0 : L0s (adjointModule W).toWeakModule (β : ℂ) v = 0 := by
    change W.L 0 v - (β : ℂ) • v = 0
    exact sub_eq_zero.mpr (W.L_zero_grading v hv)
  have h := (isLogIntertwining_module N.toWeakModule).shifted_bracket
    (β : ℂ) α v x (n : ℂ) 0
  simp only [ofOrd_zero,ofOrd_succ,weakModuleModes_apply_intCast,hv0,
    map_zero,LinearMap.zero_apply,smul_zero,zero_add,add_zero] at h
  rw [N.L0nil_apply_of_mem (N.mode_mem_weight hv hx n),N.L0nil_apply_of_mem hx]
  simpa only [L0s,L0,LogVModule.L0op,add_comm α (β : ℂ)] using h

/-- The commutation law holds for arbitrary VOA states by their homogeneous decomposition. -/
theorem L0nil_comm_mode (N : LogVModule W M) (v : V) (n : ℤ) :
    N.L0nil * mode (N.YM v) n = mode (N.YM v) n * N.L0nil := by
  have hv : v ∈ ⨆ β, W.grading β := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => N.L0nil * mode (N.YM v) n = mode (N.YM v) n * N.L0nil)
    hv (fun β v hv => L0nil_comm_mode_homogeneous N hv n) ?_ ?_
  · simp only [map_zero, mode_zero, mul_zero, zero_mul]
  · intro a b ha hb
    simp only [map_add,mode_add,mul_add,add_mul,ha,hb]

theorem L0nil_pow_comm_mode (N : LogVModule W M) (v : V) (n : ℤ) (k : ℕ) :
    N.L0nil^k * mode (N.YM v) n = mode (N.YM v) n * N.L0nil^k :=
  (show Commute N.L0nil (mode (N.YM v) n) from L0nil_comm_mode N v n).pow_left k

/-- The actual nilpotent coordinate exponential intertwines all module modes. -/
theorem nilExp_mode (N : LogVModule W M) (c : ℂ) (v : V) (n : ℤ) (x : M) :
    nilExp N c (mode (N.YM v) n x) = mode (N.YM v) n (nilExp N c x) := by
  obtain ⟨k,hk⟩ := L0nil_locallyNilpotent N x
  have he (j : ℕ) : (N.L0nil^j) (mode (N.YM v) n x) =
      mode (N.YM v) n ((N.L0nil^j) x) := by
    exact DFunLike.congr_fun (L0nil_pow_comm_mode N v n j) x
  have hm : (N.L0nil^k) (mode (N.YM v) n x) = 0 := by rw [he,hk,map_zero]
  rw [nilExp_finite N c hm,nilExp_finite N c hk,map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [he,map_smul])

/-- exp(c L(0)_nil), as an actual weak-module endomorphism. -/
def nilExpHom (N : LogVModule W M) (c : ℂ) : N.toWeakModule.Hom N.toWeakModule where
  toLinearMap := (nilExp N c).toLinearMap
  map_act := nilExp_mode N c

end
end VOA.LogTensor.Contra
