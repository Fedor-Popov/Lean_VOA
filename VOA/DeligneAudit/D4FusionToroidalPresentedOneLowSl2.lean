import VOA.DeligneAudit.D4FusionToroidalPresentedOneLowBasic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! A negative-weight highest vector vanishes in a finite-dimensional module. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem sl2_negative_two_of_finite (E F H : V →ₗ[ℂ] V)
    (hEF : ∀ x, E (F x) - F (E x) = H x)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (u : V) (hE : E u = 0) (hH : H u = (-2 : ℂ) • u) : u = 0 := by
  have hnil : ∃ N : ℕ, F^[N] u = 0 := by
    by_contra hn
    have hnz : ∀ n : ℕ, F^[n] u ≠ 0 := by
      intro n hzero
      exact hn ⟨n, hzero⟩
    have hinj : Function.Injective (fun n : ℕ => (-2 : ℂ) - 2 * (n : ℂ)) := by
      intro n m h
      have hcast : (n : ℂ) = (m : ℂ) := by linear_combination (-1 / 2) * h
      exact_mod_cast hcast
    have hsub : Set.range (fun n : ℕ => (-2 : ℂ) - 2 * (n : ℂ)) ⊆
        Module.End.HasEigenvalue H := by
      rintro μ ⟨n, rfl⟩
      apply Module.End.hasEigenvalue_of_hasEigenvector
      exact (Module.End.hasEigenvector_iff).mpr
        ⟨(Module.End.mem_eigenspace_iff).mpr
          (sl2_H_Fpow F H hHF u (-2) hH n), hnz n⟩
    have hfinite : (Set.range (fun n : ℕ => (-2 : ℂ) - 2 * (n : ℂ))).Finite :=
      (Module.End.finite_hasEigenvalue H).subset hsub
    exact hfinite.not_infinite (Set.infinite_range_of_injective hinj)
  obtain ⟨N, hN⟩ := hnil
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

#print axioms VOA.DeligneAudit.Toroidal.sl2_negative_two_of_finite
