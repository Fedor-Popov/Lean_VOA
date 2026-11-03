import VOA.Examples.VirasoroWardClosedKernel

/-! Specialization of normalized finite Ward families without evaluating coordinates
of a large state or choosing limits of a particular meromorphic formula. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV

/-- If the limiting Ward kernel is determined by its ground coefficient,
compact kernel specialization preserves a nonzero ground coefficient. -/
theorem normalized_kernel_of_tendsto {I J X : Type*} [Fintype J]
    {l : Filter X} [l.NeBot] (M : X → Matrix I J ℂ) (M0 : Matrix I J ℂ)
    (top : (J → ℂ) →ₗ[ℂ] ℂ)
    (hlim : Filter.Tendsto M l (nhds M0))
    (hker : ∀ᶠ x in l, ∃ v : J → ℂ, v ≠ 0 ∧ (M x).mulVec v = 0)
    (hground : ∀ v : J → ℂ, M0.mulVec v = 0 → top v = 0 → v = 0) :
    ∃ v : J → ℂ, top v = 1 ∧ M0.mulVec v = 0 := by
  obtain ⟨u, hu, hMu⟩ := VOA.VirasoroWardTopology.nonzero_kernel_of_tendsto M M0 hlim hker
  have htop : top u ≠ 0 := fun he => hu (hground u hMu he)
  refine ⟨(top u)⁻¹ • u, ?_, ?_⟩
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ htop]
  · rw [Matrix.mulVec_smul, hMu, smul_zero]

/-- Coefficient identities may be included as extra homogeneous rows.
Their limits then hold for the normalized genuine kernel vector. -/
theorem normalized_kernel_with_scalar_rows {I J R X : Type*} [Fintype J]
    {l : Filter X} [l.NeBot] (M : X → Matrix (I ⊕ R) J ℂ)
    (M0 : Matrix (I ⊕ R) J ℂ) (top : (J → ℂ) →ₗ[ℂ] ℂ)
    (value : R → ℂ) (measure : R → (J → ℂ) →ₗ[ℂ] ℂ)
    (hlim : Filter.Tendsto M l (nhds M0))
    (hker : ∀ᶠ x in l, ∃ v : J → ℂ, v ≠ 0 ∧ (M x).mulVec v = 0)
    (hground : ∀ v : J → ℂ, M0.mulVec v = 0 → top v = 0 → v = 0)
    (hrows : ∀ r v, M0.mulVec v (Sum.inr r) = measure r v - value r * top v) :
    ∃ v : J → ℂ, top v = 1 ∧ M0.mulVec v = 0 ∧ ∀ r, measure r v = value r := by
  obtain ⟨v, hv, hMv⟩ := normalized_kernel_of_tendsto M M0 top hlim hker hground
  refine ⟨v, hv, hMv, fun r => ?_⟩
  have he := congrFun hMv (Sum.inr r)
  rw [hrows, hv, mul_one] at he
  exact sub_eq_zero.mp he

end VOA.Classification.COne.OrbIcoV
