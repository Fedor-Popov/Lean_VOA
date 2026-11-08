import VOA.Moonshine.MoonshineCNFockAdjoint
import VOA.Moonshine.MoonshineCNCurrentCharge

/-! Adjointness of the actual complex-frame dressing, with no positivity assumption. -/

set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators
open Module (End)
open IntegralLattice HeisenbergN MvPolynomial Nondeg

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem directionOscillator_dressingField_apply (a : Fin (rank L)) (γ : L.carrier) {n : ℤ} (hn : n ≠ 0) (t : ℤ)
    (y : FockN (rank L)) :
    oscN (rank L) 1 a n (dressingField F γ t y)
      = dressingField F γ t (oscN (rank L) 1 a n y) + frameCoordinate F γ a • dressingField F γ (t - n) y := by
  have h := congrArg (fun T : End ℂ (FockN (rank L)) => T y)
    (bosonCurrent_comm_dressingField F a γ (-n - 1) t)
  simp only [bracketDist_apply, currentN_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [if_neg (by omega), show -(-n - 1) - 1 = n by ring, show t + (-n - 1) + 1 = t - n by ring,
    LinearMap.smul_apply] at h
  rw [← h]; abel

theorem creationVariable_constantCoeff (γ : L.carrier) (m : ℕ) : constantCoeff (creationVariable F γ m) = 0 := by
  simp [creationVariable, map_sum]

theorem creationCoefficient_succ_constantCoeff (γ : L.carrier) (N : ℕ) :
    constantCoeff (creationCoefficient F γ (N + 1)) = 0 := by
  rw [creationCoefficient_succ, smul_eq_C_mul, map_mul, map_sum]
  simp [creationVariable_constantCoeff]

theorem dressingField_vacuum_constantCoeff (γ : L.carrier) (t : ℤ) :
    coeff 0 (dressingField F γ t 1) = if t = 0 then 1 else 0 := by
  have h := dressingField_vacuum F γ t
  rw [vacuumN] at h
  rw [h, ← constantCoeff_eq]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, t = N := ⟨t.toNat, by omega⟩
    rcases N with _ | N
    · simp [creationCoefficient_zero]
    · rw [Int.toNat_natCast, creationCoefficient_succ_constantCoeff, if_neg (by omega)]
  · rw [if_neg ht, if_neg (by omega), map_zero]

theorem uForm_dressingField_vacuum (γ : L.carrier) (y' : FockN (rank L)) (t : ℤ) :
    uForm (rank L) (dressingField F γ t 1) y' = uForm (rank L) 1 (dressingField F γ (-t) y') := by
  induction y' using MvPolynomial.induction_on generalizing t with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank L)) = c • (1 : FockN (rank L)) by rw [smul_eq_C_mul, mul_one],
      map_smul, map_smul, map_smul, uForm_symm, uForm_one, uForm_one, smul_eq_mul, smul_eq_mul,
      dressingField_vacuum_constantCoeff, dressingField_vacuum_constantCoeff]
    by_cases ht : t = 0
    · subst ht; simp
    · rw [if_neg ht, if_neg (by omega)]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X y x hy =>
    obtain ⟨m, b⟩ := x
    rw [X_mul_eq_oscN]
    have hn : ((m : ℤ) + 1) ≠ 0 := by omega
    have hL : uForm (rank L) (dressingField F γ t 1) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
        = -(frameCoordinate F γ b * uForm (rank L) 1 (dressingField F γ (-(t - ((m : ℤ) + 1))) y)) := by
      rw [uForm_symm, uForm_oscN, neg_neg, directionOscillator_dressingField_apply F b γ hn,
        oscN_one_nonneg L b (by omega), map_zero, zero_add, map_smul, smul_eq_mul, uForm_symm, hy]
    have hR : uForm (rank L) 1 (dressingField F γ (-t) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y))
        = -(frameCoordinate F γ b * uForm (rank L) 1 (dressingField F γ (-t - -((m : ℤ) + 1)) y)) := by
      rw [show dressingField F γ (-t) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
          = oscN (rank L) 1 b (-((m : ℤ) + 1)) (dressingField F γ (-t) y)
            - frameCoordinate F γ b • dressingField F γ (-t - -((m : ℤ) + 1)) y by
        rw [directionOscillator_dressingField_apply F b γ (by omega)]; abel,
        map_sub, uForm_one_oscN_creation, map_smul, smul_eq_mul, zero_sub]
    rw [hL, hR, show -t - -((m : ℤ) + 1) = -(t - ((m : ℤ) + 1)) by ring]

/-- **`E⁻E⁺` is self-adjoint up to inversion**: `F(EE(γ)ₜ y, y') = F(y, EE(γ)₋ₜ y')`, i.e.
`(E⁻(γ,z)E⁺(γ,z))ᵗ = E⁻(γ,z⁻¹)E⁺(γ,z⁻¹)` for the form with `h(n)ᵗ = −h(−n)`. -/
theorem uForm_dressingField_adjoint (γ : L.carrier) (t : ℤ) (y y' : FockN (rank L)) :
    uForm (rank L) (dressingField F γ t y) y' = uForm (rank L) y (dressingField F γ (-t) y') := by
  induction y using MvPolynomial.induction_on generalizing t y' with
  | C c =>
    rw [show (MvPolynomial.C c : FockN (rank L)) = c • (1 : FockN (rank L)) by rw [smul_eq_C_mul, mul_one]]
    simp only [map_smul, LinearMap.smul_apply, uForm_dressingField_vacuum]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X y x hy =>
    obtain ⟨m, b⟩ := x
    rw [X_mul_eq_oscN]
    have hK : -((m : ℤ) + 1) ≠ 0 := by omega
    have hn : ((m : ℤ) + 1) ≠ 0 := by omega
    have hL : uForm (rank L) (dressingField F γ t (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)) y'
        = -uForm (rank L) y (dressingField F γ (-t) (oscN (rank L) 1 b ((m : ℤ) + 1) y'))
          - frameCoordinate F γ b * uForm (rank L) y (dressingField F γ (-(t - -((m : ℤ) + 1))) y') := by
      rw [show dressingField F γ t (oscN (rank L) 1 b (-((m : ℤ) + 1)) y)
          = oscN (rank L) 1 b (-((m : ℤ) + 1)) (dressingField F γ t y)
            - frameCoordinate F γ b • dressingField F γ (t - -((m : ℤ) + 1)) y by
        rw [directionOscillator_dressingField_apply F b γ hK]; abel,
        map_sub, LinearMap.sub_apply, uForm_oscN, neg_neg, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hy, hy]
    have hR : uForm (rank L) (oscN (rank L) 1 b (-((m : ℤ) + 1)) y) (dressingField F γ (-t) y')
        = -uForm (rank L) y (dressingField F γ (-t) (oscN (rank L) 1 b ((m : ℤ) + 1) y'))
          - frameCoordinate F γ b * uForm (rank L) y (dressingField F γ (-t - ((m : ℤ) + 1)) y') := by
      rw [uForm_oscN, neg_neg, directionOscillator_dressingField_apply F b γ hn, map_add, map_smul, smul_eq_mul]
      ring
    rw [hL, hR, show -(t - -((m : ℤ) + 1)) = -t - ((m : ℤ) + 1) by ring]

end VOA.Moonshine.ConwayNorton
