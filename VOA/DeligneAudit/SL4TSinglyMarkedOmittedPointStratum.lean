import VOA.DeligneAudit.SL4TUnmarkedFlagStrata
import VOA.DeligneAudit.SL4TMarkedFlagTopCoefficient

/-!
# Toward the omitted-point stratum of the singly marked full flag: subleading coefficients

**Status: preparatory.** The omitted-point stratum bound itself is not proved in this file. For a
set `Y` of roots with complement `Z`, the stratum ideal of the singly marked flag without doubles
is `(∏ Z, s · c(Z))` with `s = ∏ (V ∩ Y)`, where `c(Z)` is the coefficient of `t^(|Z|-1)` in
`∏_Z (1 - x t)`. This file records:

* the subleading coefficient `c(Z)` (`groupSubtopCoefficient`) and its compatibility with ring
  homomorphisms (`groupElementaryPolynomial_map`, `groupSubtopCoefficient_map`);
* the coefficient of `t^(a+b-1)` in a product of polynomials of degrees at most `a, b ≥ 1`
  (`coeff_mul_top_sub_one`), which splits `c(V)` over `V = (V ∩ Y) ⊔ Z` into the two generators
  of the stratum ideal.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-! ### The subleading coefficient of a group -/

section Subtop

variable {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]

/-- The coefficient of `t^(|Z|-1)` in `∏_Z (1 - x t)`, i.e. `(-1)^(|Z|-1) e_(|Z|-1)(Z)`. -/
def groupSubtopCoefficient (x : ι → A) (Z : Finset ι) : A :=
  (groupElementaryPolynomial x Z).coeff (Z.card - 1)

theorem groupElementaryPolynomial_map {D : Type*} [CommRing D] (f : A →+* D) (x : ι → A)
    (Z : Finset ι) :
    (groupElementaryPolynomial x Z).map f = groupElementaryPolynomial (fun i => f (x i)) Z := by
  simp [groupElementaryPolynomial, Polynomial.map_prod]

theorem groupSubtopCoefficient_map {D : Type*} [CommRing D] (f : A →+* D) (x : ι → A)
    (Z : Finset ι) :
    f (groupSubtopCoefficient x Z) = groupSubtopCoefficient (fun i => f (x i)) Z := by
  rw [groupSubtopCoefficient, ← Polynomial.coeff_map, groupElementaryPolynomial_map]
  rfl

/-- The coefficient of `t^(a+b-1)` in a product of polynomials of degrees at most `a ≥ 1` and
`b ≥ 1`. -/
theorem coeff_mul_top_sub_one (P Q : Polynomial A) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b) :
    (P * Q).coeff (a + b - 1) = P.coeff a * Q.coeff (b - 1) + P.coeff (a - 1) * Q.coeff b := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_add_of_mem (a, b - 1) (a - 1, b)
    (Finset.mem_antidiagonal.mpr (by simp; omega)) (Finset.mem_antidiagonal.mpr (by simp; omega))
    (by simp; omega)]
  rintro ⟨i, j⟩ hij hne
  rw [Finset.mem_antidiagonal] at hij
  simp only at hij
  rcases Nat.lt_or_ge a i with h | h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt h), zero_mul]
  rcases Nat.lt_or_ge b j with h' | h'
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.trans_lt h'), mul_zero]
  exfalso
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact hne.1 (Prod.ext rfl (by simp; omega))
  · exact hne.2 (Prod.ext (by simp; omega) (by simp; omega))

end Subtop

end

end VOA.DeligneAudit.SL4T
