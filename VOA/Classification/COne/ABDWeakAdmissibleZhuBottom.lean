import VOA.Classification.COne.ABDWeakAdmissibleNormal
import VOA.Classification.COne.C2WindowDetectsZhuSpectrum
import Mathlib.Data.Int.LeastGreatest

/-! Uniform Zhu bounds for ordinary modules supported in one integral coset. -/
namespace VOA.Classification.COne.ABDWeakAdmissible
open VOA.Huang.LogRemovalAdmissible
attribute [local instance] instRingA instAlgebraA

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- An ordinary module supported in one integral coset has a lowest weight. -/
theorem ordinary_coset_has_lowest (N : OrdVModule W M) (α : ℂ)
    (hα : N.weight α ≠ ⊥)
    (hcos : ∀ β, N.weight β ≠ ⊥ → ∃ d : ℤ, β = α + (d : ℂ)) :
    ∃ (μ : ℂ) (n : ℕ), IsLowestWeight N μ ∧ N.weight μ ≠ ⊥ ∧ α = μ + n := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  have hb : ∃ b : ℤ, ∀ d : ℤ, N.weight (α + (d : ℂ)) ≠ ⊥ → b ≤ d := by
    refine ⟨⌈B - α.re⌉, ?_⟩
    intro d hd
    apply Int.ceil_le.mpr
    have h := hB _ hd
    simp only [Complex.add_re, Complex.intCast_re] at h
    linarith
  obtain ⟨d, hd, hmin⟩ := Int.exists_least_of_bdd hb ⟨0, by simpa using hα⟩
  have hd0 : d ≤ 0 := hmin 0 (by simpa using hα)
  refine ⟨α + (d : ℂ), (-d).toNat, ?_, hd, ?_⟩
  · intro β hβ
    obtain ⟨e, rfl⟩ := hcos β hβ
    have hde := hmin e hβ
    refine ⟨(e - d).toNat, ?_⟩
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring

/-- A finite set controls all ordinary lowest weights, without semisimplicity. -/
theorem exists_finite_ordinary_lowest_spectrum (hC2 : C2Cofinite W) :
    ∃ s : Finset ℂ, ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
      (N : OrdVModule W M) (μ : ℂ), IsLowestWeight N μ → N.weight μ ≠ ⊥ → μ ∈ s := by
  obtain ⟨s, hs⟩ := C2WindowDetects.exists_finite_zhu_conformal_spectrum.{u,u} W hC2
  refine ⟨s, ?_⟩
  intro M _ _ N μ hlow hne
  letI := moduleMh W hlow
  letI : IsScalarTower ℂ (VOA.A W) (N.weight μ) :=
    ⟨fun c a y => by
      change actA N hlow (c • a) y = c • actA N hlow a y
      rw [map_smul]
      rfl⟩
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let z : N.weight μ := ⟨y, hy⟩
  apply hs μ z (fun h => hy0 (congrArg Subtype.val h))
  change actA N hlow (mk W W.conformalVector) z = μ • z
  apply Subtype.ext
  rw [actA_mk_apply_coe, oMod_homogeneous _ W.conformal_mem]
  exact N.L0_weight μ y hy

/-- Every weight in a one-coset ordinary module is a Zhu lowest weight plus a natural. -/
theorem exists_finite_ordinary_coset_spectrum (hC2 : C2Cofinite W) :
    ∃ s : Finset ℂ, ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
      (N : OrdVModule W M) (α : ℂ), N.weight α ≠ ⊥ →
      (∀ β, N.weight β ≠ ⊥ → ∃ d : ℤ, β = α + (d : ℂ)) →
      ∃ μ ∈ s, ∃ n : ℕ, α = μ + n := by
  obtain ⟨s, hs⟩ := exists_finite_ordinary_lowest_spectrum (W := W) hC2
  refine ⟨s, ?_⟩
  intro M _ _ N α hα hcos
  obtain ⟨μ, n, hlow, hμ, he⟩ := ordinary_coset_has_lowest N α hα hcos
  exact ⟨μ, hs N μ hlow hμ, n, he⟩

end VOA.Classification.COne.ABDWeakAdmissible
