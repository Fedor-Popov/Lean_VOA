import VOA.DeligneAudit.DeligneFusionKernel

/-! A highest-weight nilpotence lemma needing no finite-dimensional ambient module. -/

namespace VOA.DeligneAudit.LeviTypeA

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If some lowering power kills an `sl₂` highest-weight vector of natural
weight `m`, the standard power `m + 1` already kills it. -/
theorem sl2_lowering_of_nilpotent (E F H : V →ₗ[ℂ] V)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u : V) (m N : ℕ) (hE : E u = 0) (hH : H u = (m : ℂ) • u)
    (hN : F^[N] u = 0) (hmN : m + 1 ≤ N) : F^[m + 1] u = 0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases heq : N = m + 1
    · simpa [heq] using hN
    have hlt : m + 1 < N := by omega
    let k := N - 1
    have hk : N = k + 1 := by omega
    have hkm : m < k := by omega
    have hc₁ : (k : ℂ) + 1 ≠ 0 := by
      norm_cast
    have hc₂ : (m : ℂ) - k ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast (show m ≠ k by omega)
    have hkill : F^[k] u = 0 := by
      have h := VOA.DeligneAudit.SectorWeyl.sl2_E_Fpow E F H hEF hHF
        u (m : ℂ) hE hH k
      rw [← hk, hN, map_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left (mul_ne_zero hc₁ hc₂)
    exact ih k (by omega) hkill (by omega)

end VOA.DeligneAudit.LeviTypeA

#print axioms VOA.DeligneAudit.LeviTypeA.sl2_lowering_of_nilpotent
