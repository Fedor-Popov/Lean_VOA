import VOA.Huang.NgSchauenburgMixedRepresentation

/-! # Congruence from the exact mixed-indicator invariance needed

This proves the complete separation and descent implication at any specified
level. The arithmetic invariance premise is retained explicitly; it is not
proved by finite order of T or by the modular generator relations.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open scoped MatrixGroups

/-- Principal congruence is stable under conjugation. -/
theorem inPrincipalCongruence_conjugate {N : ℕ} (δ : SL(2, ℤ)) {γ : SL(2, ℤ)}
    (h : InPrincipalCongruence N γ) : InPrincipalCongruence N (δ⁻¹ * γ * δ) := by
  classical
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))
  have he : f γ = 1 := by
    ext i j
    exact h i j
  have hc : f (δ⁻¹ * γ * δ) = 1 := by rw [map_mul, map_mul, map_inv, he]; simp
  intro i j
  exact congrArg (fun g : SL(2, ZMod N) => g i j) hc

open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- Center-free congruence descent. Only invariance of the actual mixed (1,0)
rows is needed, uniformly on the principal congruence subgroup. -/
theorem projectiveCongruence_of_mixed_invariance (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (N : ℕ)
    (hrow : ∀ γ, InPrincipalCongruence N γ → ∀ (a : F.Label) (z : F.Label × F.Label → ℂ),
      equivariantIndicator F (fun p => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 (mixedRepresentation ρ γ z) =
      equivariantIndicator F (fun p => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 z) :
    ProjectiveKernelContainsGamma ρ N := by
  let μ := matrixLinearEquiv.symm.toMonoidHom.comp ρ
  have hs : matrixDouble.toHomUnits (μ ModularGroup.S) =
      matrixDouble.toHomUnits (categoricalSUnit F M) := by
    apply Units.ext
    exact mixedRepresentation_S_matrix F M ρ hr
  have hrows (γ : SL(2, ℤ)) (hγ : InPrincipalCongruence N γ) (a k l : F.Label) :
      (∑ p : F.Label × F.Label,
        generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
          (F.simple a) 1 0 * matrixDouble (μ γ) p (k, l)) =
        generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l))
          (F.simple a) 1 0 := by
    have hh := hrow γ hγ a (Pi.single (k, l) 1)
    rw [equivariantIndicator_basis] at hh
    change (∑ p, mixedRepresentation ρ γ (Pi.single (k, l) 1) p *
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0) = _ at hh
    simpa only [mixedRepresentation_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      mul_comm] using hh
  intro γ hγ
  have he : matrixDouble ((categoricalSUnit F M)⁻¹ * μ γ * categoricalSUnit F M) =
      matrixDouble (μ (ModularGroup.S⁻¹ * γ * ModularGroup.S)) := by
    have hu : matrixDouble.toHomUnits
        ((categoricalSUnit F M)⁻¹ * μ γ * categoricalSUnit F M) =
        matrixDouble.toHomUnits (μ (ModularGroup.S⁻¹ * γ * ModularGroup.S)) := by
      simp only [map_mul, map_inv, hs]
    exact congrArg (fun U : (Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ)ˣ =>
      (U : Matrix (F.Label × F.Label) (F.Label × F.Label) ℂ)) hu
  obtain ⟨c, hc, ha⟩ := scalar_of_mixed_indicator_invariance F M (μ γ) (hrows γ hγ)
    (by simpa only [he] using (hrows (ModularGroup.S⁻¹ * γ * ModularGroup.S)
          (inPrincipalCongruence_conjugate ModularGroup.S hγ)))
  refine ⟨Units.mk0 c hc, fun z => ?_⟩
  calc
    ρ γ z = matrixLinearEquiv (μ γ) z := by simp [μ]
    _ = (μ γ : Matrix F.Label F.Label ℂ).mulVec z := rfl
    _ = c • z := by rw [ha, Matrix.smul_mulVec, Matrix.one_mulVec]

open Classical in
/-- The same invariance also forces identity on the whole directly constructed double. -/
theorem mixedCongruence_of_mixed_invariance (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (N : ℕ)
    (hrow : ∀ γ, InPrincipalCongruence N γ → ∀ (a : F.Label) (z : F.Label × F.Label → ℂ),
      equivariantIndicator F (fun p => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 (mixedRepresentation ρ γ z) =
      equivariantIndicator F (fun p => mixedCenter (F.simple p.1) (F.simple p.2))
        (F.simple a) 1 0 z) :
    KernelContainsGamma (mixedRepresentation ρ) N := by
  have hp := projectiveCongruence_of_mixed_invariance F M ρ hr N hrow
  intro γ hγ
  obtain ⟨c, hc⟩ := hp γ hγ
  have hm : (matrixLinearEquiv.symm (ρ γ) : Matrix F.Label F.Label ℂ) =
      (c : ℂ) • 1 := by
    ext i j
    rw [matrixLinearEquiv_symm_apply, hc]
    simp [Pi.single_apply, Matrix.one_apply]
  have hd := matrixDouble_eq_one_of_scalar _ c.ne_zero hm
  ext z p
  rw [mixedRepresentation_apply, hd]
  simp

end VOA.Huang.NgSchauenburg
