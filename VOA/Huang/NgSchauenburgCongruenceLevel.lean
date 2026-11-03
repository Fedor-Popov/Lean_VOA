import VOA.Huang.NgSchauenburgCongruence
import VOA.Huang.NgSchauenburgDualCoherence
import VOA.Huang.NgSchauenburgVafaAlgebra
import VOA.Huang.NgSchauenburgBantayConsequences
import VOA.Huang.NgSchauenburgCenterLinear

/-! # Necessary congruence levels and the center theorem contract

The projective containment part of NS 0806.2493 Theorem 6.8 is still open.
The lower-bound part is proved here: any projective congruence level is
divisible by the order of the raw categorical twist, regardless of the
scalar normalization of the genuine linear lift.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

theorem T_pow_inPrincipalCongruence (N : ℕ) :
    InPrincipalCongruence N (ModularGroup.T ^ N) := by
  intro i j
  have ht := ModularGroup.coe_T_zpow (N : ℤ)
  rw [zpow_natCast] at ht
  have he := congrFun (congrFun ht i) j
  change ((ModularGroup.T ^ N).val i j : ZMod N) = _
  rw [he]
  fin_cases i <;> fin_cases j <;> simp

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

section Modular
variable [BraidedCategory C]

/-- The normalization scalar cancels against the unit label. Thus any
projective congruence level kills every *raw* twist eigenvalue. -/
theorem twistOrder_dvd_of_projectiveGamma (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) {N : ℕ}
    (h : ProjectiveKernelContainsGamma ρ N) : M.toRibbon.twistOrder ∣ N := by
  obtain ⟨a, b, ha, hb⟩ := hr
  have hp : ∀ (k : ℕ) (z : F.Label → ℂ) (i : F.Label),
      ρ (ModularGroup.T ^ k) z i = ((b : ℂ) * M.twistScalar i) ^ k * z i := by
    intro k
    induction k with
    | zero => intro z i; simp
    | succ k ih =>
      intro z i
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, ih, hb, pow_succ]
      ring
  obtain ⟨c, hc⟩ := h _ (T_pow_inPrincipalCongruence N)
  have hi (i : F.Label) : ((b : ℂ) * M.twistScalar i) ^ N = (c : ℂ) := by
    have he := congrFun (hc (fun _ => 1)) i
    rw [hp] at he
    simpa using he
  have hu : (b : ℂ) ^ N = (c : ℂ) := by
    simpa [M.toRibbon.twistScalar_unitLabel] using hi F.unitLabel
  rw [Ribbon.twistOrder, orderOf_dvd_iff_pow_eq_one]
  ext i
  have he := hi i
  rw [mul_pow, ← hu] at he
  exact (mul_left_cancel₀ (pow_ne_zero _ b.ne_zero)) (he.trans (mul_one _).symm)

/-- A positive projective congruence level already forces finite categorical
twist order, without any use of Vafa. -/
theorem finite_twist_of_projectiveGamma (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) {N : ℕ} (hN : 0 < N)
    (h : ProjectiveKernelContainsGamma ρ N) :
    0 < M.toRibbon.twistOrder ∧ M.toRibbon.twistOrder ≤ N := by
  have hd := twistOrder_dvd_of_projectiveGamma F M ρ hr h
  exact ⟨Nat.pos_of_dvd_of_pos hd hN, Nat.le_of_dvd hN hd⟩

/-- Once the substantive NS containment and exponent identity are supplied,
the minimality clause in the existing Theorem 6.8 contract is automatic. -/
theorem projectiveCongruenceTheorem_of_containment (F : SphericalFusion C) (M : Modular F)
    (he : ModularExponentTheorem F M)
    (hc : ∀ ρ, IsModularRepresentation F M ρ →
      ProjectiveKernelContainsGamma ρ (fsExponent F)) :
    ProjectiveCongruenceTheorem F M := by
  refine ⟨he.1, fun ρ hr => ⟨hc ρ hr, fun N hN h => ?_⟩⟩
  rw [he.2]
  exact (finite_twist_of_projectiveGamma F M ρ hr hN h).2

end Modular

section Center

variable [RightRigidCategory (Center C)]
  [HasKernels (Center C)] [HasFiniteBiproducts (Center C)]

/-- NS 0806.2493 Theorem 6.7 for the pinned canonical center representation.
This is a named unproved target. The level is the exponent of the underlying
category, not an arbitrary order of a normalized T matrix. -/
def CenterCongruenceTheorem (F : SphericalFusion C) (Z : SphericalFusion (Center C))
    (M : Modular Z) : Prop :=
  0 < fsExponent F ∧ ∀ ρ, CanonicalCenterRepresentation F Z M ρ →
    KernelContainsGamma ρ (fsExponent F) ∧
      ∀ N : ℕ, 0 < N → KernelContainsGamma ρ N → fsExponent F ≤ N

/-- The actual generalized-indicator equivariance specializes on a canonical
center congruence kernel to invariance of the indicators under the row action.
Both substantive premises are kept explicit. -/
theorem indicator_row_invariant_of_center_kernel (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (he : GeneralizedIndicatorEquivariance F Z M)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ)
    (γ : SL(2, ℤ)) (hk : ρ (modularInvolution γ) = 1)
    (V : C) (m l : ℤ) (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V (rowAction m l γ).1 (rowAction m l γ).2 z =
      equivariantIndicator F Z.simple V m l z := by
  rw [he ρ hr V m l γ z, hk]
  rfl

end Center
end VOA.Huang.NgSchauenburg
