import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSeedBasic

/-! A nilpotent negative-weight highest vector vanishes without finite dimensionality. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem two_sl2_negative_two_of_nilpotent (E F H : V →ₗ[ℂ] V)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u : V) (hE : E u = 0) (hH : H u = (-2 : ℂ) • u)
    (hN : ∃ N : ℕ, F^[N] u = 0) : u = 0 := by
  obtain ⟨N, hN⟩ := hN
  induction N with
  | zero => simpa using hN
  | succ n ih =>
      by_cases hp : F^[n] u = 0
      · exact ih hp
      · have h := sl2_E_Fpow E F H hEF hHF u (-2) hE hH n
        rw [hN, map_zero] at h
        have hcoef : ((n : ℂ) + 1) * ((-2 : ℂ) - n) ≠ 0 := by
          apply mul_ne_zero
          · exact_mod_cast Nat.succ_ne_zero n
          · intro hz
            have hre := congrArg Complex.re hz
            have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            norm_num at hre
            linarith
        exact (hp ((smul_eq_zero.mp h.symm).resolve_left hcoef)).elim

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_sl2_negative_two_of_nilpotent
