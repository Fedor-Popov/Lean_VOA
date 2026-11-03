/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FiniteWeightedJetRelations
import VOA.Commutative.ModeParticlePairing

/-!
# Exact coefficient duality for arbitrary quadratic jet presentations

A finite basis `σ` and coefficients `Q : ρ → σ × σ → K` independently define
a quadratic ideal in `K[σ]` and its finite jet algebra. A coefficient family
assigns a scalar to each commutative jet monomial. This file proves that it
descends to the dual of the presented jet algebra exactly when every ordered
quadratic mode convolution vanishes, with every spectator monomial.

In particular, annihilating the displayed quadratic generators alone is not
substituted for annihilating their ideal: polynomial spectators and ideal
generation are dealt with explicitly. No Hilbert series, dimension equality,
or functional-carrier identification is assumed. Reindexing these coefficient
families as symmetric tensor-valued particle polynomials, and restricting to
fixed particle and derivative degrees, are separate steps.
-/

namespace VOA.QuadraticJetCoefficientPairing

open VOA.FiniteJet VOA.ModeParticlePairing
open scoped BigOperators

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-- The literal quadratic polynomial encoded by an ordered coefficient matrix. -/
def quadraticRelation (q : σ × σ → K) : MvPolynomial σ K :=
  ∑ xy, q xy • (MvPolynomial.X xy.1 * MvPolynomial.X xy.2)

/-- The defining ideal, before introducing jets or any dual carrier. -/
def quadraticIdeal (Q : ρ → σ × σ → K) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range (fun r => quadraticRelation (Q r)))

omit [Fintype σ] in
/-- Reindex a retained Cauchy coefficient by bounded ordered mode pairs. -/
theorem antidiagonal_eq_coefficientPairs (N q : ℕ) (hq : q ≤ N) (i j : σ) :
    (∑ ab ∈ Finset.antidiagonal q,
      jetVariable (R := K) N i ab.1 * jetVariable (R := K) N j ab.2) =
    ∑ ab ∈ coefficientPairs N q,
      jetVariable (R := K) N i ab.1 * jetVariable (R := K) N j ab.2 := by
  classical
  refine Finset.sum_bij
    (fun ab hab =>
      (⟨ab.1, Nat.lt_succ_iff.mpr (by
          have hab' := Finset.mem_antidiagonal.mp hab
          omega)⟩,
       ⟨ab.2, Nat.lt_succ_iff.mpr (by
          have hab' := Finset.mem_antidiagonal.mp hab
          omega)⟩)) ?_ ?_ ?_ ?_
  · intro ab hab
    simp only [mem_coefficientPairs]
    exact Finset.mem_antidiagonal.mp hab
  · intro ab₁ hab₁ ab₂ hab₂ h
    exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)
  · intro ab hab
    refine ⟨(ab.1.val, ab.2.val), ?_, ?_⟩
    · exact Finset.mem_antidiagonal.mpr ((mem_coefficientPairs ab.1 ab.2).mp hab)
    · exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  · intros
    rfl

/-- Every quadratic Hasse--Schmidt relation is exactly its ordered convolution. -/
theorem relationCoeff_quadraticRelation (q : σ × σ → K) (N n : ℕ) (hn : n ≤ N) :
    relationCoeff (R := K) N n (quadraticRelation q) =
      ∑ xy, ∑ ab ∈ coefficientPairs N n,
        q xy • (MvPolynomial.X (⟨xy.1, ab.1⟩ : JetVar σ N) *
          MvPolynomial.X (⟨xy.2, ab.2⟩ : JetVar σ N)) := by
  classical
  rw [← jetCoeff_apply N ⟨n, Nat.lt_succ_iff.mpr hn⟩, quadraticRelation, map_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [map_smul, jetCoeff_apply, relationCoeff_X_mul_X,
    antidiagonal_eq_coefficientPairs N n hn, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [jetVariable_of_le N xy.1 ab.1 (Nat.lt_succ_iff.mp ab.1.isLt),
    jetVariable_of_le N xy.2 ab.2 (Nat.lt_succ_iff.mp ab.2.isLt)]

/-- Insert the two modes in a spectator monomial's exponent vector. -/
def insertExponent (N : ℕ) (e : JetVar σ N →₀ ℕ)
    (xy : σ × σ) (ab : Fin (N + 1) × Fin (N + 1)) : JetVar σ N →₀ ℕ :=
  e + Finsupp.single ⟨xy.1, ab.1⟩ 1 + Finsupp.single ⟨xy.2, ab.2⟩ 1

/-- A monomial-valued coefficient family extends uniquely by linearity. -/
def coefficientFunctional {N : ℕ} (F : (JetVar σ N →₀ ℕ) → K) :
    JetPoly K σ N →ₗ[K] K :=
  Finsupp.lsum K (fun e => LinearMap.mulRight K (F e))

omit [Fintype σ] in
@[simp]
theorem coefficientFunctional_monomial {N : ℕ} (F : (JetVar σ N →₀ ℕ) → K)
    (e : JetVar σ N →₀ ℕ) (c : K) :
    coefficientFunctional F (MvPolynomial.monomial e c) = c * F e := by
  change (Finsupp.lsum K (fun e => LinearMap.mulRight K (F e)))
    (Finsupp.single e c) = _
  simp

/-- The literal adjunction between a quadratic mode relation and its coefficient sum. -/
theorem coefficientFunctional_spectator_relationCoeff {N : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (q : σ × σ → K) (n : ℕ) (hn : n ≤ N)
    (e : JetVar σ N →₀ ℕ) :
    coefficientFunctional F
      (MvPolynomial.monomial e 1 * relationCoeff (R := K) N n (quadraticRelation q)) =
    ∑ xy, ∑ ab ∈ coefficientPairs N n, q xy * F (insertExponent N e xy ab) := by
  rw [relationCoeff_quadraticRelation q N n hn, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [mul_smul_comm, map_smul]
  change q xy * coefficientFunctional F
    (MvPolynomial.monomial e 1 *
      (MvPolynomial.monomial (Finsupp.single _ 1) 1 *
        MvPolynomial.monomial (Finsupp.single _ 1) 1)) = _
  rw [← mul_assoc, MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
  simp [insertExponent]

/-- The complete coefficient equations, including every spectator exponent.
Both orderings of distinct modes occur; equal modes occur once. -/
def CoefficientEquations (Q : ρ → σ × σ → K) (N : ℕ)
    (F : (JetVar σ N →₀ ℕ) → K) : Prop :=
  ∀ r (n : Fin (N + 1)) e,
    (∑ xy, ∑ ab ∈ coefficientPairs N n, Q r xy * F (insertExponent N e xy ab)) = 0

/-- Monomial spectator equations imply the equations for every polynomial spectator. -/
theorem coefficientFunctional_polynomialSpectator {Q : ρ → σ × σ → K} {N : ℕ}
    {F : (JetVar σ N →₀ ℕ) → K} (hF : CoefficientEquations Q N F)
    (r : ρ) (n : Fin (N + 1)) (p : JetPoly K σ N) :
    coefficientFunctional F (p * relationCoeff (R := K) N n (quadraticRelation (Q r))) =
      0 := by
  classical
  have hp : p = ∑ e ∈ p.support, p.coeff e • MvPolynomial.monomial e 1 := by
    calc
      p = ∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e) := MvPolynomial.as_sum p
      _ = _ := by simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hp, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [smul_mul_assoc, map_smul, coefficientFunctional_spectator_relationCoeff
    F (Q r) n (Nat.lt_succ_iff.mp n.isLt), hF r n e, smul_zero]

/-- The complete coefficient equations annihilate the independently generated finite jet
ideal. The induction includes arbitrary spectators, as required for ideal generation. -/
theorem coefficientFunctional_ideal_eq_zero {Q : ρ → σ × σ → K} {N : ℕ}
    {F : (JetVar σ N →₀ ℕ) → K} (hF : CoefficientEquations Q N F)
    (g : JetPoly K σ N) (hg : g ∈ jetIdeal (R := K) N (quadraticIdeal Q)) :
    coefficientFunctional F g = 0 := by
  have hg' : g ∈ Submodule.span (JetPoly K σ N)
      (jetRelationSetOfSet (R := K) N (Set.range (fun r => quadraticRelation (Q r)))) := by
    rw [quadraticIdeal, jetIdeal_span_eq_jetIdealOfSet, jetIdealOfSet] at hg
    simpa only [Ideal.submodule_span_eq] using hg
  have hstrong : ∀ p : JetPoly K σ N, coefficientFunctional F (p * g) = 0 :=
    Submodule.span_induction
      (p := fun x _ => ∀ p : JetPoly K σ N, coefficientFunctional F (p * x) = 0)
      (fun x hx p => by
        rcases hx with ⟨f, ⟨r, rfl⟩, n, rfl⟩
        rw [jetCoeff_apply]
        exact coefficientFunctional_polynomialSpectator hF r n p)
      (by intro p; simp)
      (fun x y hx hy ihx ihy p => by
        rw [mul_add, map_add, ihx p, ihy p, add_zero])
      (fun a x hx ih p => by
        rw [smul_eq_mul, ← mul_assoc]
        exact ih (p * a))
      hg'
  simpa using hstrong 1

/-- Exactness: the explicit equations are necessary and sufficient for annihilating the
finite jet ideal. No presentation-to-carrier identification is a hypothesis. -/
theorem coefficientEquations_iff_annihilates (Q : ρ → σ × σ → K) (N : ℕ)
    (F : (JetVar σ N →₀ ℕ) → K) :
    CoefficientEquations Q N F ↔
      ∀ g ∈ jetIdeal (R := K) N (quadraticIdeal Q), coefficientFunctional F g = 0 := by
  constructor
  · exact fun h g hg => coefficientFunctional_ideal_eq_zero h g hg
  · intro h r n e
    rw [← coefficientFunctional_spectator_relationCoeff F (Q r) n
      (Nat.lt_succ_iff.mp n.isLt) e]
    apply h
    apply Ideal.mul_mem_left
    exact relationCoeff_mem_jetIdeal N n (quadraticIdeal Q) (quadraticRelation (Q r))
      (Ideal.subset_span ⟨r, rfl⟩) (Nat.lt_succ_iff.mp n.isLt)

/-- Actual descent of a compatible coefficient family to the presented jet algebra. -/
def quotientFunctional {Q : ρ → σ × σ → K} {N : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (hF : CoefficientEquations Q N F) :
    PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K :=
  { QuotientAddGroup.lift (jetIdeal (R := K) N (quadraticIdeal Q)).toAddSubgroup
      (coefficientFunctional F).toAddMonoidHom
      (fun g hg => coefficientFunctional_ideal_eq_zero hF g hg) with
    map_smul' := by
      rintro k ⟨g⟩
      exact (coefficientFunctional F).map_smul k g }

@[simp]
theorem quotientFunctional_mk {Q : ρ → σ × σ → K} {N : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (hF : CoefficientEquations Q N F)
    (p : JetPoly K σ N) :
    quotientFunctional F hF (presentedJetMk (R := K) N (quadraticIdeal Q) p) =
      coefficientFunctional F p := rfl

/-- Evaluate a quotient functional on the canonical classes of commutative monomials. -/
def dualCoefficients {Q : ρ → σ × σ → K} {N : ℕ}
    (L : PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K) :
    (JetVar σ N →₀ ℕ) → K :=
  fun e => L (presentedJetMk (R := K) N (quadraticIdeal Q) (MvPolynomial.monomial e 1))

/-- Polynomial reconstruction from monomial values recovers the pullback of a quotient
functional. This is the spanning half of the coefficient pairing. -/
theorem coefficientFunctional_dualCoefficients {Q : ρ → σ × σ → K} {N : ℕ}
    (L : PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K) :
    coefficientFunctional (dualCoefficients L) =
      L.comp (presentedJetMk (R := K) N (quadraticIdeal Q)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro e c
  change coefficientFunctional (dualCoefficients L) (MvPolynomial.monomial e c) =
    L (presentedJetMk (R := K) N (quadraticIdeal Q) (MvPolynomial.monomial e c))
  rw [coefficientFunctional_monomial]
  have hmono : MvPolynomial.monomial e c = c • (MvPolynomial.monomial e 1 : JetPoly K σ N) :=
    by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul]
  rfl

/-- Every quotient functional satisfies the full convolution equations. -/
theorem dualCoefficients_equations {Q : ρ → σ × σ → K} {N : ℕ}
    (L : PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K) :
    CoefficientEquations Q N (dualCoefficients L) := by
  apply (coefficientEquations_iff_annihilates Q N _).mpr
  intro g hg
  rw [coefficientFunctional_dualCoefficients, LinearMap.comp_apply]
  have hz : presentedJetMk (R := K) N (quadraticIdeal Q) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hg
  change L (presentedJetMk (R := K) N (quadraticIdeal Q) g) = 0
  rw [hz, map_zero]

@[simp]
theorem dualCoefficients_quotientFunctional {Q : ρ → σ × σ → K} {N : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (hF : CoefficientEquations Q N F) :
    dualCoefficients (quotientFunctional F hF) = F := by
  funext e
  simp [dualCoefficients]

/-- All quotient functionals are determined by these concrete coefficients. -/
theorem dualCoefficients_injective (Q : ρ → σ × σ → K) (N : ℕ) :
    Function.Injective (dualCoefficients (Q := Q) (N := N)) := by
  intro L M h
  have heq := congrArg coefficientFunctional h
  rw [coefficientFunctional_dualCoefficients, coefficientFunctional_dualCoefficients] at heq
  apply LinearMap.ext
  intro x
  obtain ⟨p, rfl⟩ := presentedJetMk_surjective (R := K) N (quadraticIdeal Q) x
  exact DFunLike.congr_fun heq p

/-- The literal solution space of the simultaneous ordered coefficient equations. -/
def coefficientCarrier (Q : ρ → σ × σ → K) (N : ℕ) :
    Submodule K ((JetVar σ N →₀ ℕ) → K) where
  carrier := {F | CoefficientEquations Q N F}
  zero_mem' := by
    intro r n e
    simp
  add_mem' := by
    intro F G hF hG r n e
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hF r n e, hG r n e,
      add_zero]
  smul_mem' := by
    intro a F hF r n e
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ xy, ∑ ab ∈ coefficientPairs N n,
        Q r xy * (a * F (insertExponent N e xy ab))) =
          a * ∑ xy, ∑ ab ∈ coefficientPairs N n,
            Q r xy * F (insertExponent N e xy ab) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro xy hxy
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ab hab
              ring
      _ = 0 := by rw [hF r n e, mul_zero]

/-- The coefficient pairing as a linear map on the dual of the actual presented algebra. -/
def quotientDualToCoefficients (Q : ρ → σ × σ → K) (N : ℕ) :
    (PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K) →ₗ[K] coefficientCarrier Q N where
  toFun L := ⟨dualCoefficients L, dualCoefficients_equations L⟩
  map_add' L M := by
    apply Subtype.ext
    rfl
  map_smul' a L := by
    apply Subtype.ext
    rfl

theorem quotientDualToCoefficients_bijective (Q : ρ → σ × σ → K) (N : ℕ) :
    Function.Bijective (quotientDualToCoefficients Q N) := by
  constructor
  · intro L M h
    exact dualCoefficients_injective Q N (congrArg Subtype.val h)
  · intro F
    refine ⟨quotientFunctional F.1 F.2, ?_⟩
    apply Subtype.ext
    exact dualCoefficients_quotientFunctional F.1 F.2

/-- Exact coefficient duality, valid for every finite jet order and every quadratic
presentation over a field. In particular no characteristic-zero hypothesis is used. -/
def quotientDualEquivCoefficients (Q : ρ → σ × σ → K) (N : ℕ) :
    (PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] K) ≃ₗ[K] coefficientCarrier Q N :=
  LinearEquiv.ofBijective (quotientDualToCoefficients Q N)
    (quotientDualToCoefficients_bijective Q N)

end

end VOA.QuadraticJetCoefficientPairing

section AxiomAudit
#print axioms VOA.QuadraticJetCoefficientPairing.relationCoeff_quadraticRelation
#print axioms VOA.QuadraticJetCoefficientPairing.coefficientEquations_iff_annihilates
#print axioms VOA.QuadraticJetCoefficientPairing.quotientDualEquivCoefficients
end AxiomAudit
