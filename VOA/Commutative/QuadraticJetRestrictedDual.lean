/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentCollisionCoefficients

/-!
# The actual quadratic jet restricted dual and its current carrier

The source is the image of the polynomial particle/derivative bidegree in the
independently presented finite jet quotient. Homogeneous projection preserves
the quadratic jet ideal, so restriction of its dual is exact. Combining the
source coefficient pairing with the proved collision comparison identifies
this actual quotient-piece dual with the homogeneous current carrier.
-/

namespace VOA.QuadraticJetRestrictedDual

open VOA.FiniteJet VOA.ModeParticlePairing
open VOA.QuadraticJetCoefficientPairing
open VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticCurrentCoefficientReindexing
open VOA.QuadraticCurrentCollisionCoefficients
open scoped BigOperators

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-- Independent particle number and derivative order of one jet variable. -/
def bidegreeWeight (N : ℕ) : JetVar σ N → ℕ × ℕ := fun v => (1, v.order.val)

local instance bigradedAlgebra (N : ℕ) :
    GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight (σ := σ) N)) :=
  MvPolynomial.weightedGradedAlgebra K (bidegreeWeight N)

omit [Fintype σ] in
/-- The product grading is exactly the pair of independently defined scalar weights. -/
theorem weight_bidegreeWeight (N : ℕ) (e : JetVar σ N →₀ ℕ) :
    Finsupp.weight (bidegreeWeight N) e =
      (Finsupp.weight (fun _ : JetVar σ N => 1) e,
       Finsupp.weight (fun v : JetVar σ N => v.order.val) e) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp only [map_zero]; rfl
  | single_add a n e ha hn ih =>
    simp only [map_add, Finsupp.weight_single, ih, bidegreeWeight,
      Prod.smul_mk, Prod.mk_add_mk]

/-- A retained quadratic coefficient has bidegree `(2,n)`. -/
theorem relationCoeff_bihomogeneous (Q : σ × σ → K) (N n : ℕ) (hn : n ≤ N) :
    (relationCoeff (R := K) N n (quadraticRelation Q)).IsWeightedHomogeneous
      (bidegreeWeight N) (2, n) := by
  rw [relationCoeff_quadraticRelation Q N n hn]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro xy hxy
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  have hprod := (MvPolynomial.isWeightedHomogeneous_X K (bidegreeWeight N)
      (⟨xy.1, ab.1⟩ : JetVar σ N)).mul
    (MvPolynomial.isWeightedHomogeneous_X K (bidegreeWeight N) (⟨xy.2, ab.2⟩ : JetVar σ N))
  have hdegree : bidegreeWeight N (⟨xy.1, ab.1⟩ : JetVar σ N) +
      bidegreeWeight N (⟨xy.2, ab.2⟩ : JetVar σ N) = (2, n) := by
    apply Prod.ext
    · rfl
    · exact (mem_coefficientPairs ab.1 ab.2).mp hab
  rw [hdegree] at hprod
  exact (MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight N) (2, n)).smul_mem
    (Q xy) hprod

/-- The actual quadratic jet ideal is bihomogeneous, proved from its displayed generators. -/
theorem quadraticJetIdeal_bihomogeneous (Q : ρ → σ × σ → K) (N : ℕ) :
    (jetIdeal (R := K) N (quadraticIdeal Q)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight N)) := by
  rw [quadraticIdeal, jetIdeal_span_eq_jetIdealOfSet, jetIdealOfSet]
  apply Ideal.homogeneous_span
  intro f hf
  rcases hf with ⟨g, ⟨s, rfl⟩, n, rfl⟩
  refine ⟨(2, n.val), ?_⟩
  rw [jetCoeff_apply]
  exact relationCoeff_bihomogeneous (Q s) N n (Nat.lt_succ_iff.mp n.isLt)

/-- Bidegree projection preserves the independently generated jet ideal. -/
theorem bidegreeComponent_mem_ideal (Q : ρ → σ × σ → K) (N m r : ℕ)
    (p : JetPoly K σ N) (hp : p ∈ jetIdeal (R := K) N (quadraticIdeal Q)) :
    MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r) p ∈
      jetIdeal (R := K) N (quadraticIdeal Q) := by
  have h := quadraticJetIdeal_bihomogeneous Q N (m, r) hp
  change ((MvPolynomial.weightedDecomposition K (bidegreeWeight N)).decompose' p (m, r) :
    JetPoly K σ N) ∈ jetIdeal (R := K) N (quadraticIdeal Q) at h
  rw [MvPolynomial.weightedDecomposition.decompose'_apply] at h
  exact h

/-- The literal polynomial bidegree, before passing to the quotient. -/
def polynomialPiece (N m r : ℕ) : Submodule K (JetPoly K σ N) :=
  MvPolynomial.weightedHomogeneousSubmodule K (bidegreeWeight N) (m, r)

/-- The actual bidegree image in the presented quadratic jet algebra. -/
def quotientPiece (Q : ρ → σ × σ → K) (N m r : ℕ) :
    Submodule K (PresentedJet (R := K) N (quadraticIdeal Q)) :=
  LinearMap.range ((presentedJetMk (R := K) N (quadraticIdeal Q)).toLinearMap.comp
    (polynomialPiece (K := K) (σ := σ) N m r).subtype)

/-- Project a polynomial to its bidegree and then take its canonical quotient class. -/
def polynomialToPiece (Q : ρ → σ × σ → K) (N m r : ℕ) :
    JetPoly K σ N →ₗ[K] quotientPiece Q N m r where
  toFun p := ⟨presentedJetMk (R := K) N (quadraticIdeal Q)
      (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r) p),
    ⟨⟨MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r) p,
      MvPolynomial.weightedHomogeneousComponent_mem _ _ _⟩, rfl⟩⟩
  map_add' p q := by apply Subtype.ext; simp only [map_add, Submodule.coe_add]
  map_smul' a p := by
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_smul, RingHom.id_apply]

/-- The bidegree projection kills the jet ideal. -/
theorem polynomialToPiece_ideal_eq_zero (Q : ρ → σ × σ → K) (N m r : ℕ)
    (p : JetPoly K σ N) (hp : p ∈ jetIdeal (R := K) N (quadraticIdeal Q)) :
    polynomialToPiece Q N m r p = 0 := by
  apply Subtype.ext
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (bidegreeComponent_mem_ideal Q N m r p hp)

/-- A genuine linear projection from the presented quotient to its actual bidegree image. -/
def quotientProjection (Q : ρ → σ × σ → K) (N m r : ℕ) :
    PresentedJet (R := K) N (quadraticIdeal Q) →ₗ[K] quotientPiece Q N m r :=
  { QuotientAddGroup.lift (jetIdeal (R := K) N (quadraticIdeal Q)).toAddSubgroup
      (polynomialToPiece Q N m r).toAddMonoidHom
      (fun p hp => polynomialToPiece_ideal_eq_zero Q N m r p hp) with
    map_smul' := by
      rintro a ⟨p⟩
      exact (polynomialToPiece Q N m r).map_smul a p }

@[simp] theorem quotientProjection_mk (Q : ρ → σ × σ → K) (N m r : ℕ)
    (p : JetPoly K σ N) :
    quotientProjection Q N m r (presentedJetMk (R := K) N (quadraticIdeal Q) p) =
      polynomialToPiece Q N m r p := rfl

/-- The quotient projection fixes every element of the independently defined image. -/
theorem quotientProjection_piece (Q : ρ → σ × σ → K) (N m r : ℕ)
    (p : quotientPiece Q N m r) : quotientProjection Q N m r p.1 = p := by
  obtain ⟨f, hf⟩ := p.2
  apply Subtype.ext
  change presentedJetMk (R := K) N (quadraticIdeal Q) f.1 = p.1 at hf
  rw [← hf, quotientProjection_mk]
  change presentedJetMk (R := K) N (quadraticIdeal Q)
    (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r) f.1) =
      presentedJetMk (R := K) N (quadraticIdeal Q) f.1
  rw [f.2.weightedHomogeneousComponent_same]

/-- Coefficients of an actual quotient-piece functional, extended by homogeneous projection. -/
def pieceDualCoefficients {Q : ρ → σ × σ → K} {N m r : ℕ}
    (L : quotientPiece Q N m r →ₗ[K] K) : (JetVar σ N →₀ ℕ) → K :=
  dualCoefficients (L.comp (quotientProjection Q N m r))

omit [Fintype σ] in
/-- A homogeneous projection of a monomial is that monomial or zero, with its exact degree. -/
theorem bidegreeComponent_monomial (N m r : ℕ) (e : JetVar σ N →₀ ℕ) (c : K) :
    MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)
        (MvPolynomial.monomial e c) =
      if Finsupp.weight (bidegreeWeight N) e = (m, r) then MvPolynomial.monomial e c else 0 := by
  classical
  have h := MvPolynomial.isWeightedHomogeneous_monomial (bidegreeWeight N) e c rfl
  rw [MvPolynomial.weightedHomogeneousComponent_of_mem h]
  by_cases hd : Finsupp.weight (bidegreeWeight N) e = (m, r)
  · simp only [hd, if_true]
  · rw [if_neg (Ne.symm hd), if_neg hd]

/-- The coefficient extension is supported in exactly the chosen particle/derivative sector. -/
theorem pieceDualCoefficients_supported {Q : ρ → σ × σ → K} {N m r : ℕ}
    (L : quotientPiece Q N m r →ₗ[K] K) :
    SupportedBidegree N m r (pieceDualCoefficients L) := by
  intro e he
  have hdeg : Finsupp.weight (bidegreeWeight N) e = (m, r) := by
    by_contra hn
    have hz : polynomialToPiece Q N m r (MvPolynomial.monomial e 1) = 0 := by
      apply Subtype.ext
      change presentedJetMk (R := K) N (quadraticIdeal Q)
        (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)
          (MvPolynomial.monomial e 1)) = 0
      rw [bidegreeComponent_monomial, if_neg hn, map_zero]
    apply he
    change L (quotientProjection Q N m r
      (presentedJetMk (R := K) N (quadraticIdeal Q) (MvPolynomial.monomial e 1))) = 0
    rw [quotientProjection_mk, hz, map_zero]
  rw [weight_bidegreeWeight, Prod.mk.injEq] at hdeg
  exact hdeg

/-- The coefficient extension satisfies all quadratic equations because it comes from a
functional on the actual presented quotient. -/
theorem pieceDualCoefficients_equations {Q : ρ → σ × σ → K} {N m r : ℕ}
    (L : quotientPiece Q N m r →ₗ[K] K) :
    CoefficientEquations Q N (pieceDualCoefficients L) :=
  dualCoefficients_equations (L.comp (quotientProjection Q N m r))

omit [Fintype σ] in
/-- Fixed-bidegree coefficient functionals are unchanged by bidegree projection. -/
theorem coefficientFunctional_bidegreeComponent {N m r : ℕ}
    (F : (JetVar σ N →₀ ℕ) → K) (hF : SupportedBidegree N m r F) :
    (coefficientFunctional F).comp
      (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)) =
      coefficientFunctional F := by
  apply Finsupp.lhom_ext
  intro e c
  change coefficientFunctional F
    (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)
      (MvPolynomial.monomial e c)) = coefficientFunctional F (MvPolynomial.monomial e c)
  rw [bidegreeComponent_monomial]
  split_ifs with hd
  · rfl
  · have hz : F e = 0 := by
      by_contra hn
      apply hd
      rw [weight_bidegreeWeight]
      exact Prod.ext (hF e hn).1 (hF e hn).2
    rw [map_zero, coefficientFunctional_monomial, hz, mul_zero]

/-- Coefficients recover every actual quotient-piece functional. -/
theorem pieceDualCoefficients_injective (Q : ρ → σ × σ → K) (N m r : ℕ) :
    Function.Injective (pieceDualCoefficients (Q := Q) (N := N) (m := m) (r := r)) := by
  intro L M h
  have hpull := dualCoefficients_injective Q N h
  apply LinearMap.ext
  intro p
  have hp := DFunLike.congr_fun hpull p.1
  simpa only [LinearMap.comp_apply, quotientProjection_piece] using hp

/-- Restrict the descended full-quotient functional to the independently defined piece. -/
def supportedCoefficientPieceDual {Q : ρ → σ × σ → K} {N m r : ℕ}
    (F : fixedQuadraticCoefficientSpace Q N m r) : quotientPiece Q N m r →ₗ[K] K :=
  (quotientFunctional F.1 F.2.2).comp (quotientPiece Q N m r).subtype

/-- Restriction followed by coefficient extraction returns the given family, with its zero
extension outside the selected bidegree. -/
theorem pieceDualCoefficients_supportedCoefficientPieceDual
    {Q : ρ → σ × σ → K} {N m r : ℕ} (F : fixedQuadraticCoefficientSpace Q N m r) :
    pieceDualCoefficients (supportedCoefficientPieceDual F) = F.1 := by
  funext e
  change quotientFunctional F.1 F.2.2
    (polynomialToPiece Q N m r (MvPolynomial.monomial e 1)).1 = F.1 e
  change quotientFunctional F.1 F.2.2
    (presentedJetMk (R := K) N (quadraticIdeal Q)
      (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)
        (MvPolynomial.monomial e 1))) = F.1 e
  rw [quotientFunctional_mk]
  have hc := DFunLike.congr_fun (coefficientFunctional_bidegreeComponent F.1 F.2.1)
    (MvPolynomial.monomial e 1)
  change coefficientFunctional F.1
    (MvPolynomial.weightedHomogeneousComponent (bidegreeWeight N) (m, r)
      (MvPolynomial.monomial e 1)) = _ at hc
  rw [hc, coefficientFunctional_monomial, one_mul]

/-- The exact source-side coefficient map, retaining the actual quotient image as source. -/
def pieceDualToCoefficients (Q : ρ → σ × σ → K) (N m r : ℕ) :
    (quotientPiece Q N m r →ₗ[K] K) →ₗ[K] fixedQuadraticCoefficientSpace Q N m r where
  toFun L := ⟨pieceDualCoefficients L,
    pieceDualCoefficients_supported L, pieceDualCoefficients_equations L⟩
  map_add' L M := by apply Subtype.ext; rfl
  map_smul' a L := by apply Subtype.ext; rfl

theorem pieceDualToCoefficients_bijective (Q : ρ → σ × σ → K) (N m r : ℕ) :
    Function.Bijective (pieceDualToCoefficients Q N m r) := by
  constructor
  · intro L M h
    exact pieceDualCoefficients_injective Q N m r (congrArg Subtype.val h)
  · intro F
    refine ⟨supportedCoefficientPieceDual F, ?_⟩
    apply Subtype.ext
    exact pieceDualCoefficients_supportedCoefficientPieceDual F

/-- The dual of the actual bidegree quotient image is exactly the supported coefficient
solution space. No carrier identification or dimension formula occurs as a hypothesis. -/
def pieceDualEquivCoefficients (Q : ρ → σ × σ → K) (N m r : ℕ) :
    (quotientPiece Q N m r →ₗ[K] K) ≃ₗ[K] fixedQuadraticCoefficientSpace Q N m r :=
  LinearEquiv.ofBijective (pieceDualToCoefficients Q N m r)
    (pieceDualToCoefficients_bijective Q N m r)

/-- The complete finite-jet restricted-dual realization: the actual quotient's fixed
particle/derivative piece has dual canonically isomorphic to the literal current carrier.
Order `N ≥ r` is enough, and no characteristic-zero or representation-theoretic input is used. -/
def restrictedDualEquivCurrentCarrier (Q : ρ → σ × σ → K) (N m r : ℕ) (hr : r ≤ N) :
    (quotientPiece Q N m r →ₗ[K] K) ≃ₗ[K] degreePiece (currentCarrier Q m 0) r :=
  (pieceDualEquivCoefficients Q N m r).trans (fixedQuadraticReindexingEquiv Q N m r hr)

/-- The complete equivalence retains the original monomial evaluation normalization. -/
theorem restrictedDualEquivCurrentCarrier_coeff {Q : ρ → σ × σ → K} {N m r : ℕ}
    (hr : r ≤ N) (L : quotientPiece Q N m r →ₗ[K] K)
    (t : Fin m → σ) (a : Fin m → Fin (N + 1)) :
    MvPolynomial.coeff (VOA.ModeParticlePolynomial.labelledExponent a)
      ((restrictedDualEquivCurrentCarrier Q N m r hr L).1.1 t) =
      L (polynomialToPiece Q N m r (MvPolynomial.monomial (coloredExponent t a) 1)) := by
  change MvPolynomial.coeff _ (tensorPolynomial (pieceDualCoefficients L) t) = _
  rw [coeff_tensorPolynomial]
  rfl

end

end VOA.QuadraticJetRestrictedDual

section AxiomAudit
open VOA.QuadraticJetRestrictedDual in
#print axioms quadraticJetIdeal_bihomogeneous
open VOA.QuadraticJetRestrictedDual in
#print axioms pieceDualEquivCoefficients
open VOA.QuadraticJetRestrictedDual in
#print axioms restrictedDualEquivCurrentCarrier
end AxiomAudit
