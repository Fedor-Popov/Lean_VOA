import VOA.Classification.COne.PlusSplitZhuSchur

/-! Explicit candidate for the remaining Schur-to-Zhu polynomial identity.
The candidate identity is an OPEN input. Its quotient consequences below are
proved without identifying a quotient element from its values on simple tops. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuSquarePolynomial
open Polynomial PlusZhuNormalForms PlusZhuSchur

/-- The monic lattice part of the omega annihilator. -/
def latticePolynomial (m : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range m, (X - Polynomial.C ((i : ℂ)^2 / (4 * m)))

/-- The normalization of the lattice polynomial in E squared. -/
def latticeScale (m : ℕ) : ℂ := 2 * (4 * m : ℂ)^m / ((2 * m).factorial : ℂ)

def curvePolynomial (m : ℕ) : Polynomial ℂ := Polynomial.C (latticeScale m) * latticePolynomial m

/-- Square of the even twisted E eigenvalue; a rational expression in m. -/
def twistedSquare (m : ℕ) : ℂ := (2 / (2 : ℂ)^(2 * m))^2

/-- The quadratic coefficient of W - 2 omega. This is explicit Lagrange
interpolation at 1, 1/16, 9/16; defining it does not prove the Zhu identity. -/
def correctionPolynomial (m : ℕ) : Polynomial ℂ :=
  Polynomial.C (-(curvePolynomial m).eval 1 / 10 * (256 / 105)) *
    (X - Polynomial.C (1/16)) * (X - Polynomial.C (9/16)) +
  Polynomial.C ((64/5) * ((curvePolynomial m).eval (1/16) - twistedSquare m) * (32/15)) *
    (X - Polynomial.C 1) * (X - Polynomial.C (9/16)) +
  Polynomial.C ((64/75) * ((4 * m - 1 : ℂ)^2 * twistedSquare m -
    (curvePolynomial m).eval (9/16)) * (-32/7)) *
    (X - Polynomial.C 1) * (X - Polynomial.C (1/16))

def heisenbergPolynomial : Polynomial ℂ :=
  (X - Polynomial.C 1) * (X - Polynomial.C (1/16)) * (X - Polynomial.C (9/16))

def chargedPolynomial (m : ℕ) : Polynomial ℂ :=
  (X - Polynomial.C ((m : ℂ)/4)) * (X - Polynomial.C (1/16)) * (X - Polynomial.C (9/16))

/-- Degree m+4, before the extra square-case eliminations. -/
def broadOmegaPolynomial (m : ℕ) : Polynomial ℂ :=
  heisenbergPolynomial * (X - Polynomial.C ((m : ℂ)/4)) * latticePolynomial m

theorem latticePolynomial_monic (m : ℕ) : (latticePolynomial m).Monic := by
  exact monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)

theorem latticePolynomial_natDegree (m : ℕ) : (latticePolynomial m).natDegree = m := by
  have h := natDegree_prod_of_monic (s := Finset.range m)
    (f := fun i : ℕ => (X - Polynomial.C ((i : ℂ)^2 / (4 * m))))
    (fun i _ => monic_X_sub_C _)
  simpa only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, latticePolynomial] using h

theorem heisenbergPolynomial_monic : heisenbergPolynomial.Monic :=
  ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem broadOmegaPolynomial_monic (m : ℕ) : (broadOmegaPolynomial m).Monic :=
  (heisenbergPolynomial_monic.mul (monic_X_sub_C _)).mul (latticePolynomial_monic m)

theorem broadOmegaPolynomial_natDegree (m : ℕ) : (broadOmegaPolynomial m).natDegree = m + 4 := by
  rw [broadOmegaPolynomial,
    (heisenbergPolynomial_monic.mul (monic_X_sub_C _)).natDegree_mul (latticePolynomial_monic m),
    heisenbergPolynomial_monic.natDegree_mul (monic_X_sub_C _), latticePolynomial_natDegree]
  unfold heisenbergPolynomial
  rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp only [natDegree_X_sub_C]
  omega

theorem latticeScale_ne_zero (m : ℕ) (hm : 1 ≤ m) : latticeScale m ≠ 0 := by
  unfold latticeScale
  exact div_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega)))))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem curvePolynomial_natDegree_le (m : ℕ) : (curvePolynomial m).natDegree ≤ m := by
  calc
    _ ≤ (Polynomial.C (latticeScale m)).natDegree + (latticePolynomial m).natDegree :=
      natDegree_mul_le
    _ = m := by simp [latticePolynomial_natDegree]

theorem correctionPolynomial_natDegree_le (m : ℕ) :
    (correctionPolynomial m).natDegree ≤ 2 := by
  have hc (a b c : ℂ) :
      (Polynomial.C a * (X - Polynomial.C b) * (X - Polynomial.C c)).natDegree ≤ 2 := by
    calc
      _ ≤ (Polynomial.C a * (X - Polynomial.C b)).natDegree +
        (X - Polynomial.C c).natDegree := natDegree_mul_le
      _ ≤ ((Polynomial.C a).natDegree + (X - Polynomial.C b).natDegree) +
        (X - Polynomial.C c).natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
      _ = 2 := by simp
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hc _ _ _) (hc _ _ _))
    (hc _ _ _)

theorem correctionPolynomial_values (m : ℕ) :
    (correctionPolynomial m).eval 1 = -(curvePolynomial m).eval 1 / 10 ∧
    (correctionPolynomial m).eval (1/16) =
      (64/5) * ((curvePolynomial m).eval (1/16) - twistedSquare m) ∧
    (correctionPolynomial m).eval (9/16) =
      (64/75) * ((4 * m - 1 : ℂ)^2 * twistedSquare m -
        (curvePolynomial m).eval (9/16)) := by
  simp only [correctionPolynomial, eval_add, eval_mul, eval_sub, eval_X, eval_C]
  constructor
  · ring
  constructor <;> ring

variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
@[reducible] local instance squareRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance squareAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- OPEN: the explicit Schur state reduces to this polynomial in omega and W.
This equality is required in the actual quotient, not just on simple tops. -/
def SchurZhuIdentity : Prop :=
  VOA.mk (V2mPlus m hm) (squareState m hm) =
    aeval (generator m hm 0) (curvePolynomial m) +
      aeval (generator m hm 0) (correctionPolynomial m) *
        (generator m hm 1 - (2 : ℂ) • generator m hm 0)

theorem E_squared_of_schurZhuIdentity (h : SchurZhuIdentity m hm) :
    generator m hm 2 ^ 2 =
      aeval (generator m hm 0) (curvePolynomial m) +
        aeval (generator m hm 0) (correctionPolynomial m) *
          (generator m hm 1 - (2 : ℂ) • generator m hm 0) := by
  change VOA.mk (V2mPlus m hm) (PlusUnitary.EP m hm) ^ 2 = _
  rw [pow_two, ← mk_zhuMul, E_zhuMul_E]
  exact h

/-- The existing W relation annihilates precisely the deviation W - 2 omega. -/
theorem heisenberg_annihilates_deviation :
    aeval (generator m hm 0) heisenbergPolynomial *
      (generator m hm 1 - (2 : ℂ) • generator m hm 0) = 0 := by
  have h := omega_cubed_W m hm
  apply_fun (fun z => z - (generator m hm 0 ^ 3 * generator m hm 1)) at h
  simp only [sub_self] at h
  symm at h
  simp only [heisenbergPolynomial, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_one, one_mul, pow_succ, pow_zero, mul_assoc] at h ⊢
  convert congrArg Neg.neg h using 1
  module

include hm2 in
theorem charged_annihilates_E :
    aeval (generator m hm 0) (chargedPolynomial m) * generator m hm 2 = 0 := by
  have h := omega_E_nested_relation m hm hm2
  dsimp only at h
  simp only [chargedPolynomial, map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_one, one_mul, mul_assoc] at h ⊢
  convert h using 1
  module

include hm2 in
/-- The explicit E-square identity implies a genuine monic degree-(m+4)
omega relation. This is the desired degree in the nonsquare case only. -/
theorem broadOmega_annihilates_of_schurZhuIdentity (h : SchurZhuIdentity m hm) :
    aeval (generator m hm 0) (broadOmegaPolynomial m) = 0 := by
  letI : CommRing (VOA.A (V2mPlus m hm)) :=
    { instRingA _ with mul_comm := zhu_mul_comm m hm hm2 }
  let w := generator m hm 0
  let e := generator m hm 2
  let d := generator m hm 1 - (2 : ℂ) • w
  let r : Polynomial ℂ := X - Polynomial.C ((m : ℂ)/4)
  have hp : heisenbergPolynomial * r = (X - Polynomial.C 1) * chargedPolynomial m := by
    dsimp [heisenbergPolynomial, chargedPolynomial, r]
    ring
  have hz : aeval w (heisenbergPolynomial * r) * e ^ 2 = 0 := by
    rw [hp, map_mul, pow_two, mul_assoc, ← mul_assoc (aeval w (chargedPolynomial m))]
    rw [charged_annihilates_E m hm hm2, zero_mul, mul_zero]
  have hd : aeval w heisenbergPolynomial * d = 0 := heisenberg_annihilates_deviation m hm
  have hs := E_squared_of_schurZhuIdentity m hm h
  change e ^ 2 = aeval w (curvePolynomial m) + aeval w (correctionPolynomial m) * d at hs
  have hz' : aeval w (heisenbergPolynomial * r) * aeval w (curvePolynomial m) = 0 := by
    calc
      _ = aeval w (heisenbergPolynomial * r) * e ^ 2 -
          aeval w r * aeval w (correctionPolynomial m) *
            (aeval w heisenbergPolynomial * d) := by rw [hs, map_mul]; ring
      _ = 0 := by rw [hz, hd]; simp
  have hz'' : latticeScale m • aeval w (broadOmegaPolynomial m) = 0 := by
    convert hz' using 1
    simp only [broadOmegaPolynomial, curvePolynomial, map_mul, aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul]
    rfl
  exact (smul_eq_zero.mp hz'').resolve_left (latticeScale_ne_zero m hm)

end VOA.Classification.COne.PlusZhuSquarePolynomial
