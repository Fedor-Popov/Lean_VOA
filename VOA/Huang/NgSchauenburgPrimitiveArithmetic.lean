import VOA.Huang.NgSchauenburgMixedRows
import VOA.Huang.NgSchauenburgEquivarianceReduction

/-! # The primitive-row arithmetic needed by mixed scalar detection

Integer Galois powers are reduced to the proved trace-polynomial argument.
For the (1,0) row, primitive rescaling and T-periodicity suffice; no assertion
about all nonprimitive lattice orbits is needed. Categorical equivariance and
the smaller-field membership remain explicit hypotheses.
-/
noncomputable section
namespace VOA.Huang.NgSchauenburg
open scoped MatrixGroups

section Trace
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- The Galois trace argument for integer powers, including negative exponents. -/
theorem trace_zpow_mul_eq_of_modEq (E : W ≃ₗ[ℂ] W) {m N : ℕ}
    (hm : 0 < m) (hN : 0 < N) (hE : E ^ (m * N) = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (m * N)) (k l : ℤ)
    (hk : Int.gcd k (m * N) = 1) (hmod : Int.ModEq N k 1)
    (hmem : LinearMap.trace ℂ W (E ^ l).toLinearMap ∈
      Algebra.adjoin ℚ ({ζ ^ m} : Set ℂ)) :
    LinearMap.trace ℂ W (E ^ (k * l)).toLinearMap =
      LinearMap.trace ℂ W (E ^ l).toLinearMap := by
  let K : ℕ := (k % (m * N : ℕ)).toNat
  have hMN : (m * N : ℤ) ≠ 0 := by positivity
  have hK : (K : ℤ) = k % (m * N : ℕ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hMN))
  have hcop : Nat.Coprime K (m * N) := by
    change Nat.gcd K (m * N) = 1
    rw [← Int.gcd_natCast_natCast, hK, Int.gcd_emod]
    exact hk
  have heq : Int.ModEq N (K : ℤ) k := by
    rw [hK]
    apply Int.ModEq.of_dvd _ (Int.mod_modEq k (m * N : ℕ))
    exact_mod_cast (dvd_mul_left N m)
  have hnat : Nat.ModEq N K 1 := Int.natCast_modEq_iff.mp (heq.trans hmod)
  let f := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ℂ) (M := W)
  have hEl : (f (E ^ l)) ^ (m * N) = 1 := by
    rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm l,
      zpow_mul, zpow_natCast, hE, one_zpow, map_one]
  have ht := trace_power_eq_of_modEq (f (E ^ l)) hm hN hEl hζ hcop hnat hmem
  have hEk : E ^ k = E ^ K := by
    rw [zpow_eq_zpow_emod' k hE, ← hK, zpow_natCast]
  have hp : f (E ^ (k * l)) = (f (E ^ l)) ^ K := by
    rw [← map_pow]
    congr 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm l, zpow_mul E k l, hEk,
      ← zpow_natCast, ← zpow_mul]
  change LinearMap.trace ℂ W (f (E ^ (k * l))) = _
  rw [hp]
  exact ht
end Trace

section Indicators
universe v u
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Integer rescaling for the genuine rotation, with the central twist and
the smaller cyclotomic field made explicit. -/
theorem generalizedIndicatorInt_zmul_eq_of_modEq (F : SphericalFusion C)
    (X : Center C) (V : C) (n : ℕ) {N : ℕ} (hN : 0 < N)
    {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j X.1).hom = t • centralDrinfeldMorphism X) (htN : t ^ N = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ ((n + 1) * N)) (k l : ℤ)
    (hk : Int.gcd k ((n + 1) * N) = 1) (hmod : Int.ModEq N k 1)
    (hmem : generalizedIndicatorInt F.toPivotal X V n l ∈
      Algebra.adjoin ℚ ({ζ ^ (n + 1)} : Set ℂ)) :
    generalizedIndicatorInt F.toPivotal X V n (k * l) =
      generalizedIndicatorInt F.toPivotal X V n l := by
  letI := F.homFinite X.1 (tensorPower V (n + 1))
  have hrot : generalizedRotation F.toPivotal X V n ^ ((n + 1) * N) = 1 := by
    apply LinearEquiv.toLinearMap_injective
    change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (R := ℂ) (M := X.1 ⟶ tensorPower V (n + 1))) _ = _
    rw [map_pow]
    exact generalizedRotation_pow_mul_eq_one F.toPivotal X V n N ht hj htN
  exact trace_zpow_mul_eq_of_modEq _ (Nat.succ_pos n) hN hrot hζ k l hk hmod hmem
end Indicators

section Rows
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A primitive first row of a principal congruence element. -/
theorem principal_first_row (N : ℕ) (γ : SL(2, ℤ))
    (hγ : InPrincipalCongruence N γ) :
    IsCoprime (γ 0 0) (γ 0 1) ∧
      (γ 0 0 : ZMod N) = 1 ∧ (γ 0 1 : ZMod N) = 0 := by
  refine ⟨⟨γ 1 1, -γ 1 0, ?_⟩, ?_, ?_⟩
  · have h := γ.property
    rw [Matrix.det_fin_two] at h
    nlinarith
  · simpa using hγ 0 0
  · simpa using hγ 0 1

/-- Only primitive rescaling of (b,-1) is required for uniform (1,0) invariance.
This is an arithmetic implication, not a categorical equivariance assumption
discharged by generator relations. -/
theorem one_zero_invariant_of_primitive_rescaling
    (σ : SL(2, ℤ) →* (W ≃ₗ[ℂ] W)) (I : ℤ → ℤ → W → ℂ) (N : ℕ)
    (he : ∀ m l γ z,
      I (rowAction m l γ).1 (rowAction m l γ).2 z =
        I m l (σ (modularInvolution γ) z))
    (hT : (σ ModularGroup.T) ^ N = 1)
    (hscale : ∀ a b : ℤ, IsCoprime a b → (a : ZMod N) = 1 →
      ∀ z, I b (-a) z = I b (-1) z)
    (γ : SL(2, ℤ)) (hγ : InPrincipalCongruence N γ) (z : W) :
    I 1 0 (σ γ z) = I 1 0 z := by
  have hrow (δ : SL(2, ℤ)) (hδ : InPrincipalCongruence N δ) (w : W) :
      I (δ 0 0) (δ 0 1) w = I 1 0 w := by
    obtain ⟨hab, ha, hb⟩ := principal_first_row N δ hδ
    have hS (a b : ℤ) : I b (-a) (σ ModularGroup.S w) = I a b w := by
      have h := he a b ModularGroup.S (σ ModularGroup.S w)
      rw [rowAction_S, modularInvolution_S, map_inv] at h
      simpa using h
    rw [← hS (δ 0 0) (δ 0 1), hscale _ _ hab ha, hS 1 (δ 0 1)]
    obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
    have hp : σ (ModularGroup.T ^ (δ 0 1)) = 1 := by
      rw [hq, map_zpow, zpow_mul, zpow_natCast, hT, one_zpow]
    have hi : modularInvolution (ModularGroup.T ^ (δ 0 1)) =
        (ModularGroup.T ^ (δ 0 1))⁻¹ := by
      change modularOuterAutomorphism _ = _
      rw [map_zpow]
      change (modularInvolution ModularGroup.T) ^ _ = _
      rw [modularInvolution_T, inv_zpow]
    have h := he 1 0 (ModularGroup.T ^ (δ 0 1)) w
    rw [hi, map_inv, hp, inv_one] at h
    simpa [rowAction, ModularGroup.coe_T_zpow] using h
  have h := he 1 0 (modularInvolution γ) z
  rw [modularInvolution_involutive] at h
  rw [← h]
  simpa [rowAction] using hrow (modularInvolution γ)
    (modularInvolution_inPrincipalCongruence hγ) z

end Rows
end VOA.Huang.NgSchauenburg
