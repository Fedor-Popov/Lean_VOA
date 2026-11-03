import VOA.Classification.COne.PlusSplitZhuSquarePolynomial

/-! Exact polynomial inputs sufficient for the original boundary reductions.
The omega and Schur inputs remain open. The even-square W boundary is proved. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuSquarePolynomial
open Polynomial PlusZhuNormalForms

/-- Extra roots not already supplied by the lattice part of the polynomial. -/
def exceptionalPolynomial (m : ℕ) : Polynomial ℂ :=
  if IsSquare m then
    if Even (Nat.sqrt m) then 1 else (X - Polynomial.C (1/16)) * (X - Polynomial.C (9/16))
  else heisenbergPolynomial

/-- The prescribed degree-omegaCount polynomial, with explicit factors. -/
def sharpOmegaPolynomial (m : ℕ) : Polynomial ℂ :=
  exceptionalPolynomial m * (X - Polynomial.C ((m : ℂ)/4)) * latticePolynomial m

theorem exceptionalPolynomial_monic (m : ℕ) : (exceptionalPolynomial m).Monic := by
  unfold exceptionalPolynomial
  split
  · split
    · exact monic_one
    · exact (monic_X_sub_C _).mul (monic_X_sub_C _)
  · exact heisenbergPolynomial_monic

theorem sharpOmegaPolynomial_monic (m : ℕ) : (sharpOmegaPolynomial m).Monic :=
  ((exceptionalPolynomial_monic m).mul (monic_X_sub_C _)).mul (latticePolynomial_monic m)

theorem sharpOmegaPolynomial_natDegree (m : ℕ) :
    (sharpOmegaPolynomial m).natDegree = omegaCount m := by
  rw [sharpOmegaPolynomial,
    ((exceptionalPolynomial_monic m).mul (monic_X_sub_C _)).natDegree_mul
      (latticePolynomial_monic m),
    (exceptionalPolynomial_monic m).natDegree_mul (monic_X_sub_C _),
    natDegree_X_sub_C, latticePolynomial_natDegree]
  unfold exceptionalPolynomial omegaCount wCount
  split
  · split
    · simp only [natDegree_one]; omega
    · rw [(monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
      simp only [natDegree_X_sub_C]; omega
  · unfold heisenbergPolynomial
    rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
      (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
    simp only [natDegree_X_sub_C]; omega

variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance boundaryPolyRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance boundaryPolyAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- OPEN: the explicit sharp monic polynomial vanishes in the actual quotient. -/
def SharpOmegaIdentity : Prop := aeval (generator m hm 0) (sharpOmegaPolynomial m) = 0

/-- A monic annihilator of exactly the list length proves the pure-omega boundary. -/
theorem omega_boundary_of_monic (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : p.natDegree = omegaCount m) (hz : aeval (generator m hm 0) p = 0) :
    generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul, hdeg] at hz
  have he : generator m hm 0 ^ omegaCount m =
      -(∑ i ∈ Finset.range (omegaCount m), p.coeff i • generator m hm 0 ^ i) :=
    eq_neg_of_add_eq_zero_right hz
  rw [he]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (omega_power_mem m hm i (Finset.mem_range.mp hi)))

theorem omega_boundary_of_sharpOmegaIdentity (h : SharpOmegaIdentity m hm) :
    generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)) :=
  omega_boundary_of_monic m hm _ (sharpOmegaPolynomial_monic m)
    (sharpOmegaPolynomial_natDegree m) h

/-- In the nonsquare case the Schur identity already gives the right-degree
omega relation; no separate sharp-omega input is necessary in that case. -/
theorem sharpOmegaIdentity_of_nonsquare (hm2 : 2 ≤ m) (hns : ¬ IsSquare m)
    (h : SchurZhuIdentity m hm) : SharpOmegaIdentity m hm := by
  unfold SharpOmegaIdentity sharpOmegaPolynomial exceptionalPolynomial
  rw [if_neg hns]
  exact broadOmega_annihilates_of_schurZhuIdentity m hm hm2 h

/-- The W boundary is unconditional for every even square m >= 2. -/
theorem W_boundary_of_even_square (hm2 : 2 ≤ m) (hs : IsSquare m)
    (he : Even (Nat.sqrt m)) :
    generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  have hw : wCount m = 3 := by simp [wCount, hs, he]
  have hm4 : 4 ≤ m := by
    obtain ⟨n, hn⟩ := hs
    have hn2 : 2 ≤ n := by nlinarith
    nlinarith
  have ho : 5 ≤ omegaCount m := by unfold omegaCount; rw [hw]; omega
  rw [hw]
  exact omega_cubed_W_mem m hm (by omega) ho

/-- In the three-W-column case the explicit degree bounds reduce E squared
directly; no omega-boundary assumption is needed. -/
theorem E_squared_mem_of_schurZhuIdentity_three_columns (h : SchurZhuIdentity m hm)
    (hw : 3 ≤ wCount m) (ho : m < omegaCount m) (ho4 : 4 ≤ omegaCount m) :
    generator m hm 2 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  rw [E_squared_of_schurZhuIdentity m hm h, mul_sub, mul_smul_comm, ← add_sub_assoc]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.smul_mem _ _ ?_)
  · rw [aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (omega_power_mem m hm i (by
        have := curvePolynomial_natDegree_le m
        have := Finset.mem_range.mp hi
        omega))
  · rw [aeval_eq_sum_range, Finset.sum_mul]
    exact Submodule.sum_mem _ fun i hi => by
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ (omega_power_W_mem m hm i (by
        have := correctionPolynomial_natDegree_le m
        have := Finset.mem_range.mp hi
        omega))
  · rw [aeval_eq_sum_range, Finset.sum_mul]
    exact Submodule.sum_mem _ fun i hi => by
      rw [smul_mul_assoc, ← pow_succ]
      exact Submodule.smul_mem _ _ (omega_power_mem m hm (i + 1) (by
        have := correctionPolynomial_natDegree_le m
        have := Finset.mem_range.mp hi
        omega))

/-- Polynomial multiples stay in the span once its omega boundary and W
boundary are known. This uses the original list, with no enlargement. -/
theorem polynomial_mul_mem_of_boundaries (hm2 : 2 ≤ m)
    (ho : generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)))
    (hw : generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)))
    (p : Polynomial ℂ) (x : VOA.A (V2mPlus m hm))
    (hx : x ∈ Submodule.span ℂ (Set.range (monomial m hm))) :
    aeval (generator m hm 0) p * x ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  have hs := omega_stable_of_boundaries m hm hm2 ho hw
  have hp (n : ℕ) : generator m hm 0 ^ n * x ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [pow_succ', mul_assoc] using hs _ ih
  rw [aeval_eq_sum_range, Finset.sum_mul]
  exact Submodule.sum_mem _ fun i _ => by
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (hp i)

/-- The explicit Schur identity plus the first two original boundaries
proves the third original boundary, E squared. -/
theorem E_squared_mem_of_schurZhuIdentity (hm2 : 2 ≤ m) (h : SchurZhuIdentity m hm)
    (ho : generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)))
    (hw : generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm))) :
    generator m hm 2 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  rw [E_squared_of_schurZhuIdentity m hm h]
  have hW : generator m hm 1 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
    by_cases hz : wCount m = 0
    · simpa only [hz, pow_zero, one_mul] using hw
    · simpa using omega_power_W_mem m hm 0 (by omega)
  have hw1 : generator m hm 0 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
    simpa using omega_power_mem m hm 1 (by have := omegaCount_ge_four m hm2; omega)
  refine Submodule.add_mem _ ?_ ?_
  · simpa using polynomial_mul_mem_of_boundaries m hm hm2 ho hw (curvePolynomial m) 1
      (one_mem_span m hm)
  · exact polynomial_mul_mem_of_boundaries m hm hm2 ho hw (correctionPolynomial m) _
      (Submodule.sub_mem _ hW (Submodule.smul_mem _ _ hw1))

end VOA.Classification.COne.PlusZhuSquarePolynomial

namespace VOA.Classification.COne
open PlusZhuNormalForms PlusZhuSquarePolynomial

/-- OPEN: a single explicit neutral Schur-to-Zhu reduction for each m. -/
def V2mPlusSchurZhuIdentities : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → SchurZhuIdentity m hm

/-- OPEN: only square m require the sharper omega relation; only nonsquares
and odd squares require the shorter W boundary. -/
def V2mPlusSquareCasePolynomialBoundaries : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    (IsSquare m → SharpOmegaIdentity m hm) ∧
    (¬ (IsSquare m ∧ Even (Nat.sqrt m)) →
      generator m hm 0 ^ wCount m * generator m hm 1 ∈
        Submodule.span ℂ (Set.range (monomial m hm)))

theorem boundaryReductions_of_schur_polynomialBoundaries
    (hs : V2mPlusSchurZhuIdentities) (hb : V2mPlusSquareCasePolynomialBoundaries) :
    V2mPlusZhuBoundaryReductions := by
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  obtain ⟨ho, hw⟩ := hb m hm hm2
  have hp : SharpOmegaIdentity m hm := by
    by_cases hsq : IsSquare m
    · exact ho hsq
    · exact sharpOmegaIdentity_of_nonsquare m hm hm2 hsq (hs m hm hm2)
  have ho' := omega_boundary_of_sharpOmegaIdentity m hm hp
  have hw' : generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
    by_cases he : IsSquare m ∧ Even (Nat.sqrt m)
    · exact W_boundary_of_even_square m hm hm2 he.1 he.2
    · exact hw he
  exact ⟨ho', hw', E_squared_mem_of_schurZhuIdentity m hm hm2 (hs m hm hm2) ho' hw'⟩

theorem rationality_of_twistedTopModels_schur_polynomialBoundaries_resonant
    (ht : V2mPlusTwistedTopModels) (hs : V2mPlusSchurZhuIdentities)
    (hb : V2mPlusSquareCasePolynomialBoundaries)
    (hgen : V2mPlusResonantGeneratorComplements) : V2mPlusRationalFactGe2 :=
  rationality_of_twistedTopModels_boundaryReductions_resonant ht
    (boundaryReductions_of_schur_polynomialBoundaries hs hb) hgen

end VOA.Classification.COne
