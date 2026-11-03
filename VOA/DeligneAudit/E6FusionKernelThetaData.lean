import VOA.DeligneAudit.E6FusionKernelRawTable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

/-- `sl₂` data of the root `γ` with raising partner `e`, where `[e, f_γ] = -h_γ` and `θ(h_γ) = 1`. The `sl₂`
relation is summed over the Cartan part only. -/
def RootSl2E6 (e γ : Fin 78) : Prop :=
  (6 ≤ e.val ∧ e.val < 42) ∧ (∀ c : Fin 78, fZ brK e γ c ≠ 0 → c.val < 6) ∧ fZ brK e γ 1 = -1 ∧
    ∀ d : Fin 78, ∑ c : Fin 78, (if c.val < 6 then fZ brK e γ c * fZ brK c γ d else 0) =
      if d = γ then 2 else 0


end VOA.DeligneAudit.UnivG.E6K
