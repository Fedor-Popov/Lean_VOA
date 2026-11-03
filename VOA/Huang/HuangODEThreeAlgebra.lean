import VOA.Huang.MatrixCoeffODE

/-! # The three-insertion configuration ring and the uniform ODE engine

This is the algebraic extraction step, with its filtration hypotheses explicit.
The ring contains inverses of all insertion coordinates and all pairwise
collisions. Finite generation here gives equations, not regularity. In particular,
this file does not assert that an arbitrary quotient is finitely generated.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open scoped BigOperators
open MvPolynomial VOA.Huang.MatrixCoeffODE

/-- The divisor of the three-point configuration space (the fourth point is zero). -/
abbrev configurationDen : MvPolynomial (Fin 3) ℂ :=
  X 0 * X 1 * X 2 * (X 0 - X 1) * (X 0 - X 2) * (X 1 - X 2)

/-- `ℂ[z₁±¹,z₂±¹,z₃±¹,(z₁-z₂)⁻¹,(z₁-z₃)⁻¹,(z₂-z₃)⁻¹]`. -/
abbrev ConfigurationRing : Type := Localization.Away configurationDen

instance : IsNoetherianRing ConfigurationRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers configurationDen) ConfigurationRing
    inferInstance

theorem isUnit_configurationDen :
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing configurationDen) :=
  IsLocalization.Away.algebraMap_isUnit configurationDen

/-- All six excluded divisors are invertible, individually. -/
theorem configuration_units :
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 0)) ∧
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 1)) ∧
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 2)) ∧
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 0 - X 1)) ∧
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 0 - X 2)) ∧
    IsUnit (algebraMap (MvPolynomial (Fin 3) ℂ) ConfigurationRing (X 1 - X 2)) := by
  have h := isUnit_configurationDen
  simp only [configurationDen, map_mul, IsUnit.mul_iff] at h
  tauto

section Quotient
variable {T : Type*} [AddCommGroup T] [Module ConfigurationRing T]
variable {ι : Type*} [Preorder ι] [WellFoundedLT ι]

/-- The same finite quotient gives three differential equations whose coefficients
are chosen before, and hence independently of, every evaluation killing `J`.
The missing VOA step is the five-slot weight-filtration reduction `hstep`. -/
theorem exists_three_odes_of_filtration
    (F : ι → Submodule ConfigurationRing T) (hmono : Monotone F)
    (hexh : ∀ t : T, ∃ n, t ∈ F n) (J : Submodule ConfigurationRing T)
    (N : ι) (hFN : (F N).FG)
    (hstep : ∀ n, ¬ n ≤ N → F n ≤ J ⊔ ⨆ m, ⨆ (_ : m < n), F m)
    (t : Fin 3 → ℕ → T) :
    ∃ (order : Fin 3 → ℕ) (a : Fin 3 → ℕ → ConfigurationRing),
      ∀ {E : Type*} [AddCommGroup E] [Module ConfigurationRing E]
        (φ : T →ₗ[ConfigurationRing] E) (_ : J ≤ LinearMap.ker φ)
        (D : Fin 3 → E → E)
        (_ : ∀ i k, φ (t i k) = (D i)^[k] (φ (t i 0))) (i : Fin 3),
        (D i)^[order i] (φ (t i 0)) =
          ∑ k ∈ Finset.range (order i), a i k • (D i)^[k] (φ (t i 0)) := by
  letI : Module.Finite ConfigurationRing (T ⧸ J) :=
    finite_quotient_of_filtration F hmono hexh J N hFN hstep
  choose order a ha using fun i => exists_ode_of_finite_quotient J (t i)
  exact ⟨order, a, fun φ hφ D hD i => ha i φ hφ (D i) (hD i)⟩

end Quotient
end VOA.Huang.HuangODEThree
