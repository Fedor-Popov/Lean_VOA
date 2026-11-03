import VOA.DeligneAudit.D4LeviKSPairSpectator

/-! The exact linear factorization criterion for the symmetric PAIR map. -/

namespace VOA.DeligneAudit.D4Levi

private noncomputable def pairSymmetricLinear (a b c : ℕ) :
    pairSourceSymmetric a b c →ₗ[ℂ] pairTargetSymmetric a b c :=
  (pairSymmetricRestriction a b c).toLinearMap

private theorem pairSymmetricLinear_surjective (a b c : ℕ) :
    Function.Surjective (pairSymmetricLinear a b c) :=
  pairSymmetricRestriction_surjective a b c

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A linear map that kills the symmetric PAIR kernel descends uniquely
    through the surjective symmetric restriction. -/
noncomputable def pairSymmetricFactor (a b c : ℕ)
    (q : pairSourceSymmetric a b c →ₗ[ℂ] V)
    (hker : ∀ P, pairSymmetricRestriction a b c P = 0 → q P = 0) :
    pairTargetSymmetric a b c →ₗ[ℂ] V := by
  let μ := pairSymmetricLinear a b c
  have hμ : μ.ker ≤ q.ker := by
    intro P hP
    exact hker P hP
  exact (μ.ker.liftQ q hμ).comp
    (μ.quotKerEquivOfSurjective
      (pairSymmetricLinear_surjective a b c)).symm.toLinearMap

theorem pairSymmetricFactor_comp (a b c : ℕ)
    (q : pairSourceSymmetric a b c →ₗ[ℂ] V)
    (hker : ∀ P, pairSymmetricRestriction a b c P = 0 → q P = 0)
    (P : pairSourceSymmetric a b c) :
    pairSymmetricFactor a b c q hker (pairSymmetricRestriction a b c P) =
      q P := by
  let μ := pairSymmetricLinear a b c
  have hμ : μ.ker ≤ q.ker := by
    intro R hR
    exact hker R hR
  change (μ.ker.liftQ q hμ)
    ((μ.quotKerEquivOfSurjective
      (pairSymmetricLinear_surjective a b c)).symm (μ P)) = q P
  rw [μ.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- PAIR factorization is equivalent to annihilating exactly the kernel
    inside the separately symmetric source algebra. -/
theorem pairSymmetric_factor_iff (a b c : ℕ)
    (q : pairSourceSymmetric a b c →ₗ[ℂ] V) :
    (∃ qbar : pairTargetSymmetric a b c →ₗ[ℂ] V,
      ∀ P, qbar (pairSymmetricRestriction a b c P) = q P) ↔
      ∀ P, pairSymmetricRestriction a b c P = 0 → q P = 0 := by
  constructor
  · rintro ⟨qbar, hqbar⟩ P hP
    rw [← hqbar P, hP, map_zero]
  · intro hker
    exact ⟨pairSymmetricFactor a b c q hker,
      pairSymmetricFactor_comp a b c q hker⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricFactor_comp
#print axioms VOA.DeligneAudit.D4Levi.pairSymmetric_factor_iff
