import VOA.DeligneAudit.DeligneFusionCVBound
import VOA.DeligneAudit.DeligneFusionGarland

/-! The local Weyl bound for an arbitrary current `sl₂` action. -/

namespace VOA.DeligneAudit.CVsl2

open VOA.DeligneAudit.CVPart

universe u

/-- A vector satisfying the local Weyl relations of weight `n` has a
lowering-current orbit of rank at most `2 ^ n`. -/
theorem local_weyl_fspan_bound
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {E H F : ℕ → Module.End ℂ V} (hS : SL2 E H F)
    {y : V} (hE : ∀ s, E s y = 0)
    (hH : ∀ s, 0 < s → H s y = 0)
    (hH0 : ∃ c : ℂ, H 0 y = c • y)
    (n : ℕ) (hF0 : (F 0 ^ (n + 1)) y = 0) :
    FiniteDimensional ℂ (Fspan F y) ∧
      Module.finrank ℂ (Fspan F y) ≤ 2 ^ n := by
  have hR : CVRel F (List.replicate n 1) y := by
    intro r s k hr hrs
    have hT : T k (List.replicate n 1) = n - k := by
      simp [T_replicate]
    rw [hT] at hrs
    have hk : k ≤ r * k := by nlinarith
    have hsum : n + 1 ≤ r + s := by omega
    have hEF : ∀ k, E 1 * F k - F k * E 1 = H (k + 1) := by
      intro k
      simpa only [add_comm] using hS.hEF 1 k
    exact VOA.DeligneAudit.Garland.garland hEF
      (fun m k => hS.hHF (m + 1) k) hS.hFF
      (hE 1) (fun m => hH (m + 1) (by omega)) r hr hF0 s hsum
  have hC := cv_bound (List.replicate n 1)
    (by simp) (by intro x hx; rw [List.eq_of_mem_replicate hx])
    V E H F hS y hE hH hH0 hR
  simpa using hC

end VOA.DeligneAudit.CVsl2

#print axioms VOA.DeligneAudit.CVsl2.local_weyl_fspan_bound
