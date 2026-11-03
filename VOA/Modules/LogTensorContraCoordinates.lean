import VOA.Modules.LogTensorOrdinary
import VOA.Modules.LogTensorGraded
import VOA.Huang.LiRegularExp
import Mathlib.Data.Real.Archimedean

/-! # Actual logarithmic coordinate operators for the contragredient transform

The generalized grading obeys the mode-shift law, and its nilpotent L(0)
part exponentiates on each vector by a finite sum. L(1) is locally nilpotent
without an L(0)-semisimplicity assumption. These are coordinate ingredients
for the logarithmic A-transform; this file does not assume or assert its Jacobi identity.
-/
namespace VOA
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual generalized-eigenspace grading obeys the ordinary mode-shift law. -/
theorem LogVModule.mode_mem_weight (N : LogVModule W M) {β : ℤ} {v : V}
    (hv : v ∈ W.grading β) {α : ℂ} {x : M} (hx : x ∈ N.weight α) (n : ℤ) :
    mode (N.YM v) n x ∈ N.weight (α + (β : ℂ) - n - 1) := by
  have hv' : v ∈ (adjointModule W).toLog.weight (β : ℂ) := by
    change v ∈ adjWeight W (β : ℂ)
    rwa [adjWeight_cast]
  have h := LogTensor.IsLogIntertwining.mem_weight
    (LogTensor.isLogIntertwining_module N.toWeakModule) hv' hx (n : ℂ) 0
  simpa only [LogTensor.ofOrd,if_true,LogTensor.weakModuleModes_apply_intCast,
    add_comm α (β : ℂ)] using h

/-- A grading-restricted generalized module is an actual graded weak module. -/
def LogVModule.toGW (N : LogVModule W M) : C2Rigid.GWModule W M where
  toWeakModule := N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  mode_mem_weight' := fun hv _ _ hx n => N.mode_mem_weight hv hx n
  finrank := N.finrank
  boundedBelow := N.boundedBelow

namespace LogTensor.Contra
open VOA.Huang.LiRegular

/-- L(1) on an actual graded weak module. -/
def L1 (N : C2Rigid.GWModule W M) : End ℂ M := mode (N.YM W.conformalVector) 2

theorem L1_pow_mem_weight (N : C2Rigid.GWModule W M) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) (k : ℕ) :
    (L1 N ^ k) x ∈ N.weight (α - k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,L1]
    have h := C2Rigid.mode_mem_weight N W.conformalVector_mem_grading_two ih 2
    convert h using 2
    push_cast
    ring

/-- Lower-bounded generalized modules have locally nilpotent L(1). -/
theorem L1_locallyNilpotent (N : C2Rigid.GWModule W M) : LocNil (L1 N) := by
  intro x
  have hx : x ∈ ⨆ α, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight
    (motive := fun x => ∃ k : ℕ, (L1 N ^ k) x = 0) hx ?_ ⟨0,by simp⟩ ?_
  · intro α y hy
    obtain ⟨B,hB⟩ := N.boundedBelow
    obtain ⟨k,hk⟩ := exists_nat_gt (α.re-B)
    refine ⟨k,?_⟩
    have hm := L1_pow_mem_weight N hy k
    have hb : N.weight (α-k) = ⊥ := by
      by_contra h
      have hh := hB _ h
      simp only [Complex.sub_re,Complex.natCast_re] at hh
      linarith
    rwa [hb,Submodule.mem_bot] at hm
  · rintro a b ⟨j,hj⟩ ⟨k,hk⟩
    exact ⟨max j k,by rw [map_add,
      pow_apply_eq_zero_of_le hj (le_max_left _ _),
      pow_apply_eq_zero_of_le hk (le_max_right _ _),add_zero]⟩

/-- The actual nilpotent L(0) part is locally nilpotent on the entire module. -/
theorem L0nil_locallyNilpotent (N : LogVModule W M) : LocNil N.L0nil := by
  intro x
  have hx : x ∈ ⨆ α, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N.weight
    (motive := fun x => ∃ k : ℕ, (N.L0nil ^ k) x = 0) hx ?_ ⟨0,by simp⟩ ?_
  · intro α y hy
    exact N.L0nil_locNilpotent hy
  · rintro a b ⟨j,hj⟩ ⟨k,hk⟩
    exact ⟨max j k,by rw [map_add,
      pow_apply_eq_zero_of_le hj (le_max_left _ _),
      pow_apply_eq_zero_of_le hk (le_max_right _ _),add_zero]⟩

/-- exp(c L(0)_nil) is an actual linear equivalence, with inverse exp(-c L(0)_nil). -/
def nilExp (N : LogVModule W M) (c : ℂ) : M ≃ₗ[ℂ] M where
  toLinearMap := expOp (L0nil_locallyNilpotent N) c
  invFun := expOp (L0nil_locallyNilpotent N) (-c)
  left_inv := expOp_cancel_neg (L0nil_locallyNilpotent N) c
  right_inv := expOp_neg_cancel (L0nil_locallyNilpotent N) c

theorem nilExp_add (N : LogVModule W M) (c d : ℂ) (x : M) :
    nilExp N c (nilExp N d x) = nilExp N (c+d) x :=
  expOp_add (L0nil_locallyNilpotent N) c d x

theorem nilExp_finite (N : LogVModule W M) (c : ℂ) {x : M} {k : ℕ}
    (hk : (N.L0nil ^ k) x = 0) :
    nilExp N c x = ∑ j ∈ Finset.range k,
      (c^j/(j.factorial : ℂ)) • (N.L0nil^j) x :=
  expOp_eq_sum (L0nil_locallyNilpotent N) c hk

theorem L0nil_pow_mem_weight (N : LogVModule W M) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) (k : ℕ) : (N.L0nil^k) x ∈ N.weight α := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply]
    exact N.L0nil_mem_weight ih

/-- The nilpotent exponential preserves each actual generalized weight space. -/
theorem nilExp_mem_weight (N : LogVModule W M) (c : ℂ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : nilExp N c x ∈ N.weight α := by
  obtain ⟨k,hk⟩ := L0nil_locallyNilpotent N x
  rw [nilExp_finite N c hk]
  exact Submodule.sum_mem _ (fun j _ =>
    (N.weight α).smul_mem _ (L0nil_pow_mem_weight N hx j))

end LogTensor.Contra
end
end VOA
