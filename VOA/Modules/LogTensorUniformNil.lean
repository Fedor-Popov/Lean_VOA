import VOA.Modules.LogTensorContraNilModes
import VOA.Modules.LogTensorTargets

/-! # A uniform Jordan bound on finitely generated generalized modules

The actual nilpotent L(0) part commutes with every genuine module mode. Its
local nilpotence on finitely many generators therefore gives a single power
vanishing on the entire module, independent of generalized weight.
-/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Contra
open Module (End)
open VOA.Huang.LiRegular
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Finitely generated logarithmic modules have a global nilpotent Jordan bound. -/
theorem L0nil_isNilpotent_of_finGen (N : LogVModule W M) (hN : FinGen N.toWeakModule) :
    IsNilpotent N.L0nil := by
  classical
  obtain ⟨S,hS,hgen⟩ := hN
  let k : M → ℕ := fun x => (L0nil_locallyNilpotent N x).choose
  have hk : ∀ x, (N.L0nil ^ k x) x = 0 := fun x =>
    (L0nil_locallyNilpotent N x).choose_spec
  let K := hS.toFinset.sup k
  let P := LinearMap.ker (N.L0nil ^ K)
  have hSP : S ⊆ P := by
    intro x hx
    exact pow_apply_eq_zero_of_le (hk x)
      (Finset.le_sup (hS.mem_toFinset.mpr hx))
  have hstable : ModeStable N.toWeakModule P := by
    intro a n x hx
    change (N.L0nil ^ K) (mode (N.YM a) n x) = 0
    rw [← Module.End.mul_apply,L0nil_pow_comm_mode N a n K,Module.End.mul_apply]
    rw [show (N.L0nil ^ K) x = 0 from hx,map_zero]
  have hP : P = ⊤ := hgen P hSP hstable
  exact ⟨K,LinearMap.ker_eq_top.mp hP⟩

end VOA.LogTensor.Contra
