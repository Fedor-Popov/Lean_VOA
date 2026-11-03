import VOA.Huang.GenusTwoPointElliptic
import VOA.Huang.GenusTwoPointWard

/-!
# Regular coefficients for a conditional two-insertion q-equation

The coefficient functions are the explicit Eisenstein and elliptic Fourier
generators. Their cusp regularity is proved, rather than hypothesized.
Trace descent and the differential Ward identity remain explicit hypotheses:
the raw-mode identities in `GenusTwoPointWard` do not discharge them.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA VOA.Huang.FusionC2
open scoped BigOperators
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}

/-- A positive-order relation, uniform over trace functionals, with coefficients
analytic at q = 0. The two trace Ward obligations are retained without weakening. -/
theorem exists_regular_uniform_qEquation (x : ℂ)
    (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : ModuleC2Cofinite A.toWeakModule) (hB : ModuleC2Cofinite B.toWeakModule)
    (c : Kernels (coefficientAlgebra (ellipticGenerators x)))
    (t : ℕ → Tensor (coefficientAlgebra (ellipticGenerators x)) M₁ M₂) :
    ∃ (m : ℕ) (a : ℕ → coefficientAlgebra (ellipticGenerators x)), 0 < m ∧
      (∀ k, AnalyticAt ℂ (a k).val 0) ∧
      ∀ {F : Type*} [AddCommGroup F] [Module (coefficientAlgebra (ellipticGenerators x)) F]
        (φ : Tensor (coefficientAlgebra (ellipticGenerators x)) M₁ M₂ →ₗ[
          coefficientAlgebra (ellipticGenerators x)] F),
        TraceDescent A.toWeakModule B.toWeakModule c φ →
        ∀ D : ℕ → F → F, QOrbitCompatibility φ t D →
          qIterate D (φ (t 0)) m =
            ∑ k ∈ Finset.range m, a k • qIterate D (φ (t 0)) k := by
  obtain ⟨m, a, hm, ha⟩ := exists_uniform_qEquation A B hA hB c t
  exact ⟨m, a, hm, fun k => elliptic_coefficient_analyticAt_zero x (a k), ha⟩

end VOA.Huang.GenusTwoPoint.QEquation
