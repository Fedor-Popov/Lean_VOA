import VOA.Classification.COne.OrbOctaRDecomposition

/-! Exact candidate numbers from the rational free-boson calculation.

These are for the normalization `T2 I4 = 2 wv 4 0 + 28 wv 4 4 + 2 wv 4 8`.
The external calculation identifies its neutral polynomial as `(2/5) s_(4,4,4,4)`
in power sums `y_k = sqrt(2) h(-k)`, and its charge-four coefficients as 2.
The neutral polynomial has 77 nonzero monomials and leading coefficient 1/2177280000.

At levels 16 and 18 in the charge-four Fock space, the images of L(-1) and L(-3)
form matrices of sizes 277 by 231 and 473 by 385. Each has codimension one.
Normalize the annihilating functional on L(-2)^(level/2) of the charged ground state.
Skew symmetry reduces the charged self-product measurement to an exponential acting
on the neutral polynomial. The neutral all-first-oscillator coefficient determines
what remains of the vacuum coefficient.

The determinant and the conversion from intrinsic remainders are kernel checked here.
The two actual remainder hypotheses in the final theorem are NOT discharged here.
-/

set_option Elab.async false

namespace VOA.Classification.COne.OrbOctaR
open VOA VertexOperatorAlgebra OrbOcta OrbC2b OrbC2c

def candidateA32 : ℚ := 1182839383900570201856 / 612649221284532756933984375
def candidateB32 : ℚ := 3400250349334312 / 213671504723551875
def candidateA34 : ℚ := 37778562460734258675712 / 343696213140622876639965234375
def candidateB34 : ℚ := 6437642020519936 / 7051159655877211875

def candidateDet : ℚ :=
  -9145248854097493361096873163510185015115776 /
    34331356708712389165696982386575738517797576278411865234375

theorem candidate_determinant :
    candidateA34 * (candidateA34 + candidateB34 * candidateB32) -
      candidateB34 * candidateA32 * candidateB34 = candidateDet := by
  norm_num [candidateA32, candidateB32, candidateA34, candidateB34, candidateDet]

theorem candidate_determinant_ne_zero :
    (candidateA34 : ℂ) * (candidateA34 + candidateB34 * candidateB32) -
      candidateB34 * candidateA32 * candidateB34 ≠ 0 := by
  norm_num [candidateA32, candidateB32, candidateA34, candidateB34]

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

/-- Converting a state-level remainder uses the intrinsic C2 space of A. -/
theorem quotient_of_vir_remainder (x : V) (k : ℤ) (r s : ℕ) (a b : ℂ)
    (h : A.smul x k x - (a • ((A.L (-2)) ^ r) A.vacuum + b • ((A.L (-2)) ^ s) x) ∈
      virError A A.vacuum ⊔ virError A x) :
    mk₂ A (A.smul x k x) =
      a • (exceptionalConformalEnd A ^ r) (mk₂ A A.vacuum) +
        b • (exceptionalConformalEnd A ^ s) (mk₂ A x) := by
  have hz := (mk₂_eq_zero_iff A).mpr
    ((sup_le (virError_le_c2 A A.vacuum) (virError_le_c2 A x)) h)
  rw [map_sub, map_add, map_smul, map_smul,
    ← exceptionalConformalEnd_pow_mk, ← exceptionalConformalEnd_pow_mk] at hz
  exact sub_eq_zero.mp hz

end General

/-- The remaining semantic certificates, with explicit verified nondegeneracy. -/
theorem nilpotent_of_candidate_remainders
    (h32 : W.smul X (-1) X -
      ((candidateA32 : ℂ) • ((W.L (-2)) ^ 16) W.vacuum +
        (candidateB32 : ℂ) • ((W.L (-2)) ^ 8) X) ∈
          virError W W.vacuum ⊔ virError W X)
    (h34 : W.smul X (-3) X -
      ((candidateA34 : ℂ) • ((W.L (-2)) ^ 17) W.vacuum +
        (candidateB34 : ℂ) • ((W.L (-2)) ^ 9) X) ∈
          virError W W.vacuum ⊔ virError W X) :
    (exceptionalConformalEnd W ^ 25) (mk₂ W W.vacuum) = 0 := by
  have h1 := quotient_of_vir_remainder W X (-1) 16 8 _ _ h32
  have h2 := quotient_of_vir_remainder W X (-3) 17 9 _ _ h34
  have hz : mk₂ W (W.smul X (-3) X) = 0 :=
    (mk₂_eq_zero_iff W).mpr (smul_le_neg_two_mem_O₂ W X X (by norm_num))
  rw [hz] at h2
  apply conformal_nilpotent_of_quadratic W (mk₂ W X) 8
    candidateA32 candidateB32 candidateA34 candidateB34 candidate_determinant_ne_zero
  · rw [A₂mul_mk]
    exact h1
  · exact h2.symm

end VOA.Classification.COne.OrbOctaR
