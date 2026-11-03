/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.QuadraticCurrentAuxiliaryTensor
import VOA.Commutative.QuadraticCurrentGradedCarrier

/-!
# The grading on the auxiliary tensor factor

Splitting the auxiliary roots from a homogeneous current-carrier polynomial
has an exact grading law: the coefficient of an auxiliary monomial of degree
`s` is a current-only carrier vector of degree `r - s`, and it vanishes when
`s > r`.  The converse holds as well.  Thus the ungraded auxiliary tensor
equivalence restricts to an equivalence with the finite-support coefficient
families on this complementary-degree diagonal.

This is the coefficient form of the Hilbert-series convolution.  It uses only
the literal polynomial carrier and does not assume a character formula or a
representation-theoretic realization.
-/

namespace VOA.QuadraticCurrentAuxiliaryGrading

open VOA.DeligneAuxiliaryCollision
open VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticCurrentAuxiliaryCoefficients
open VOA.QuadraticCurrentAuxiliaryTensor
open VOA.SymmetricPolynomialTensorCoefficients

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ]

/-! ## Coefficients and total degree -/

/-- Join a current-root exponent and an auxiliary-root exponent in the
original `Fin (m + d)` variable set. -/
def combinedExponent (m d : ℕ) (f : Fin m →₀ ℕ) (a : Fin d →₀ ℕ) :
    Particle m d →₀ ℕ :=
  Finsupp.mapDomain finSumFinEquiv (f.sumElim a)

private theorem iterToSum_monomial_monomial
    {R A B : Type*} [CommSemiring R]
    (e : A →₀ ℕ) (f : B →₀ ℕ) (r : R) :
    MvPolynomial.iterToSum R A B
        (MvPolynomial.monomial e (MvPolynomial.monomial f r)) =
      MvPolynomial.monomial (e.sumElim f) r := by
  classical
  rw [MvPolynomial.iterToSum, MvPolynomial.eval₂Hom_monomial]
  rw [show MvPolynomial.monomial f r =
    MvPolynomial.C r * f.prod (fun n k => MvPolynomial.X n ^ k) from
      MvPolynomial.monomial_eq]
  rw [show MvPolynomial.monomial (e.sumElim f) r =
    MvPolynomial.C r * (e.sumElim f).prod (fun n k => MvPolynomial.X n ^ k) from
      MvPolynomial.monomial_eq]
  rw [Finsupp.prod_sumElim]
  simp only [map_mul, map_finsuppProd, map_pow, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Function.comp_apply]
  ac_rfl

private theorem coeff_iterToSum
    {R A B : Type*} [CommSemiring R]
    (P : MvPolynomial A (MvPolynomial B R)) (e : A →₀ ℕ) (f : B →₀ ℕ) :
    MvPolynomial.coeff (e.sumElim f) (MvPolynomial.iterToSum R A B P) =
      MvPolynomial.coeff f (MvPolynomial.coeff e P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add]
      rw [hP, hQ]
  | monomial u c =>
      induction c using MvPolynomial.induction_on' with
      | add c₁ c₂ hc₁ hc₂ =>
          rw [map_add (MvPolynomial.monomial u)]
          simp only [map_add, MvPolynomial.coeff_add]
          rw [hc₁, hc₂]
      | monomial v r =>
          rw [iterToSum_monomial_monomial]
          classical
          simp only [MvPolynomial.coeff_monomial]
          by_cases hu : u = e
          · subst u
            by_cases hv : v = f
            · subst v
              simp
            · have hsum : e.sumElim v ≠ e.sumElim f := by
                intro h
                apply hv
                simpa using congrArg (fun w =>
                  Finsupp.comapDomain Sum.inr w Sum.inr_injective.injOn) h
              simp [hv, hsum]
          · have hsum : u.sumElim v ≠ e.sumElim f := by
              intro h
              apply hu
              simpa using congrArg (fun w =>
                Finsupp.comapDomain Sum.inl w Sum.inl_injective.injOn) h
            simp [hu, hsum]

private theorem coeff_sumAlgEquiv
    {R A B : Type*} [CommSemiring R]
    (p : MvPolynomial (A ⊕ B) R) (e : A →₀ ℕ) (f : B →₀ ℕ) :
    MvPolynomial.coeff f ((MvPolynomial.sumAlgEquiv R A B p).coeff e) =
      MvPolynomial.coeff (e.sumElim f) p := by
  rw [← coeff_iterToSum]
  exact congrArg (MvPolynomial.coeff (e.sumElim f))
    ((MvPolynomial.sumRingEquiv R A B).left_inv p)

omit [Fintype σ] in
/-- A coefficient after splitting is the coefficient at the joined exponent
before splitting. -/
theorem coeff_auxiliaryCoefficient {m d : ℕ} (a : Fin d →₀ ℕ)
    (f : Fin m →₀ ℕ) (p : TensorPolynomial (K := K) (σ := σ) m d)
    (t : Fin m → σ) :
    MvPolynomial.coeff f (auxiliaryCoefficient a p t) =
      MvPolynomial.coeff (combinedExponent m d f a) (p t) := by
  rw [auxiliaryCoefficient, split]
  change MvPolynomial.coeff f
      (MvPolynomial.coeff a
        (MvPolynomial.sumAlgEquiv K (Fin d) (Fin m)
          (MvPolynomial.rename
            (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin d))) (p t)))) = _
  rw [coeff_sumAlgEquiv]
  let E : Particle m d ≃ (Fin d ⊕ Fin m) :=
    finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m) (Fin d))
  have hmap : Finsupp.mapDomain E (combinedExponent m d f a) = a.sumElim f := by
    rw [combinedExponent, ← Finsupp.mapDomain_comp]
    have hcomp : (E : Particle m d → (Fin d ⊕ Fin m)) ∘
        (finSumFinEquiv : (Fin m ⊕ Fin d) → Particle m d) = Sum.swap := by
      funext i
      cases i <;> simp [E]
    rw [hcomp]
    exact Finsupp.mapDomain_swap_sumElim f a
  rw [← hmap]
  exact MvPolynomial.coeff_rename_mapDomain E E.injective (p t) _

omit [Fintype σ] in
@[simp] theorem combinedExponent_degree (m d : ℕ)
    (f : Fin m →₀ ℕ) (a : Fin d →₀ ℕ) :
    (combinedExponent m d f a).degree = f.degree + a.degree := by
  rw [combinedExponent, Finsupp.degree_mapDomain]
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Finsupp.sum_sumElim]
  simp [Finsupp.degree_apply, Finsupp.sum]

omit [Fintype σ] in
/-- A coefficient in auxiliary degree `s` of a homogeneous polynomial of
total degree `r` is homogeneous of degree `r - s`. -/
theorem auxiliaryCoefficient_isWeightedHomogeneous {m d r : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d)
    (hp : ∀ t, (p t).IsWeightedHomogeneous (fun _ => 1) r)
    (a : Fin d →₀ ℕ) (t : Fin m → σ) :
    (auxiliaryCoefficient a p t).IsWeightedHomogeneous
      (fun _ => 1) (r - a.degree) := by
  intro f hf
  have hsource : MvPolynomial.coeff (combinedExponent m d f a) (p t) ≠ 0 := by
    rwa [← coeff_auxiliaryCoefficient]
  have hweight := hp t hsource
  rw [← Finsupp.degree_eq_weight_one] at hweight ⊢
  rw [combinedExponent_degree] at hweight
  omega

omit [Fintype σ] in
/-- Auxiliary monomials whose degree exceeds the total degree have zero
coefficient. -/
theorem auxiliaryCoefficient_eq_zero_of_degree_lt {m d r : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d)
    (hp : ∀ t, (p t).IsWeightedHomogeneous (fun _ => 1) r)
    (a : Fin d →₀ ℕ) (hra : r < a.degree) :
    auxiliaryCoefficient a p = 0 := by
  funext t
  apply MvPolynomial.ext
  intro f
  change MvPolynomial.coeff f (auxiliaryCoefficient a p t) = 0
  rw [coeff_auxiliaryCoefficient]
  apply (hp t).coeff_eq_zero
  rw [← Finsupp.degree_eq_weight_one]
  rw [show (combinedExponent (m + 0) d f a).degree = f.degree + a.degree by
    simpa only [Nat.add_zero] using combinedExponent_degree m d f a]
  omega

omit [Fintype σ] in
/-- Complementary homogeneity of all auxiliary coefficients, including
vanishing above the total degree, recovers total homogeneity. -/
theorem isWeightedHomogeneous_of_auxiliaryCoefficients {m d r : ℕ}
    (p : TensorPolynomial (K := K) (σ := σ) m d)
    (hhom : ∀ a t, (auxiliaryCoefficient a p t).IsWeightedHomogeneous
      (fun _ => 1) (r - a.degree))
    (hzero : ∀ a, r < a.degree → auxiliaryCoefficient a p = 0) :
    ∀ t, (p t).IsWeightedHomogeneous (fun _ => 1) r := by
  intro t u hu
  let v : (Fin m ⊕ Fin d) →₀ ℕ := Finsupp.mapDomain finSumFinEquiv.symm u
  let fa := Finsupp.sumFinsuppEquivProdFinsupp v
  let f : Fin m →₀ ℕ := fa.1
  let a : Fin d →₀ ℕ := fa.2
  have hv : f.sumElim a = v := by
    exact Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply v
  have hjoin : combinedExponent m d f a = u := by
    rw [combinedExponent, hv]
    ext i
    simp [v, Finsupp.mapDomain_equiv_apply]
  have hcoefficient : MvPolynomial.coeff f (auxiliaryCoefficient a p t) ≠ 0 := by
    rw [coeff_auxiliaryCoefficient, hjoin]
    exact hu
  have har : a.degree ≤ r := by
    by_contra hle
    have hra : r < a.degree := Nat.lt_of_not_ge hle
    have hz := congrFun (hzero a hra) t
    have hz' : auxiliaryCoefficient a p t = 0 := by simpa using hz
    rw [hz', MvPolynomial.coeff_zero] at hcoefficient
    exact hcoefficient rfl
  have hf := hhom a t hcoefficient
  rw [← Finsupp.degree_eq_weight_one] at hf ⊢
  rw [← hjoin, combinedExponent_degree, hf]
  omega

omit [Fintype σ] in
/-- Renaming variables preserves ordinary total degree.  The map need not be
surjective (or even injective); variables of weight one remain of weight one. -/
theorem rename_isWeightedHomogeneous_one {I J : Type*} (f : I → J)
    (p : MvPolynomial I K) (r : ℕ)
    (hp : p.IsWeightedHomogeneous (fun _ => 1) r) :
    (MvPolynomial.rename f p).IsWeightedHomogeneous (fun _ => 1) r := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isWeightedHomogeneous_zero K _ r
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial e k hk =>
      rw [MvPolynomial.rename_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [← Finsupp.degree_eq_weight_one] at hk ⊢
      rw [Finsupp.degree_mapDomain]
      exact hk

/-! ## The symmetric tensor factor respects total degree -/

/-- Ordinary degree `s` inside the scalar symmetric-polynomial factor. -/
def symmetricDegreePiece (d s : ℕ) :
    Submodule K (MvPolynomial.symmetricSubalgebra (Fin d) K) where
  carrier := {p | p.1.IsWeightedHomogeneous (fun _ => 1) s}
  zero_mem' := MvPolynomial.isWeightedHomogeneous_zero K _ s
  add_mem' := fun hp hq => hp.add hq
  smul_mem' := by
    intro k p hp
    change (k • p.1).IsWeightedHomogeneous (fun _ => 1) s
    exact (MvPolynomial.weightedHomogeneousSubmodule K (fun _ : Fin d => 1) s).smul_mem k hp

/-- On pure tensors, the exact auxiliary tensor factorization adds the
current degree and the ordinary symmetric-polynomial degree. -/
theorem currentAuxiliaryTensorEquiv_symm_tmul_mem_degreePiece
    (Q : ρ → σ × σ → K) (m d j s : ℕ)
    (w : degreePiece (currentCarrier Q m 0) j)
    (q : symmetricDegreePiece (K := K) d s) :
    (currentAuxiliaryTensorEquiv Q m d).symm (w.1 ⊗ₜ[K] q.1) ∈
      degreePiece (currentCarrier Q m d) (s + j) := by
  intro t
  rw [currentAuxiliaryTensorEquiv_symm_tmul]
  exact (rename_isWeightedHomogeneous_one (Fin.natAdd m) q.1.1 s q.2).mul
    (rename_isWeightedHomogeneous_one (Fin.castAdd d) (w.1.1 t) j (w.2 t))

/-! ## The exact graded coefficient equivalence -/

/-- The invariant auxiliary coefficient families on the total-degree `r`
diagonal. -/
def gradedInvariantCoefficients (Q : ρ → σ × σ → K) (m d r : ℕ) :
    Submodule K (invariantCoefficients (K := K) (W := currentCarrier Q m 0) d) where
  carrier := {c | ∀ a,
    c.1 a ∈ degreePiece (currentCarrier Q m 0) (r - a.degree) ∧
      (r < a.degree → c.1 a = 0)}
  zero_mem' := by
    intro a
    exact ⟨(degreePiece (currentCarrier Q m 0) (r - a.degree)).zero_mem,
      fun _ => rfl⟩
  add_mem' := by
    intro c e hc he a
    exact ⟨(degreePiece (currentCarrier Q m 0) (r - a.degree)).add_mem
        (hc a).1 (he a).1,
      fun h => by
        change c.1 a + e.1 a = 0
        rw [(hc a).2 h, (he a).2 h, add_zero]⟩
  smul_mem' := by
    intro k c hc a
    exact ⟨(degreePiece (currentCarrier Q m 0) (r - a.degree)).smul_mem k (hc a).1,
      fun h => by
        change k • c.1 a = 0
        rw [(hc a).2 h, smul_zero]⟩

/-- Membership in one total-degree piece is exactly the complementary-degree
condition on every auxiliary coefficient. -/
theorem mem_degreePiece_iff_auxiliaryCoefficients
    (Q : ρ → σ × σ → K) (m d r : ℕ) (p : currentCarrier Q m d) :
    p ∈ degreePiece (currentCarrier Q m d) r ↔
      ∀ a,
        coefficientLinear Q m d a p ∈
            degreePiece (currentCarrier Q m 0) (r - a.degree) ∧
          (r < a.degree → coefficientLinear Q m d a p = 0) := by
  constructor
  · intro hp a
    refine ⟨?_, ?_⟩
    · intro t
      exact auxiliaryCoefficient_isWeightedHomogeneous p.1 hp a t
    · intro hra
      apply Subtype.ext
      exact auxiliaryCoefficient_eq_zero_of_degree_lt p.1 hp a hra
  · intro h
    exact isWeightedHomogeneous_of_auxiliaryCoefficients p.1
      (fun a t => (h a).1 t)
      (fun a hra => congrArg Subtype.val ((h a).2 hra))

/-- Coefficient extraction restricted to one total-degree diagonal. -/
def gradedCoefficientsLinear (Q : ρ → σ × σ → K) (m d r : ℕ) :
    degreePiece (currentCarrier Q m d) r →ₗ[K]
      gradedInvariantCoefficients Q m d r where
  toFun p := ⟨invariantCoefficientsLinear Q m d p.1, by
    intro a
    exact (mem_degreePiece_iff_auxiliaryCoefficients Q m d r p.1).mp p.2 a⟩
  map_add' p q := by
    apply Subtype.ext
    exact (invariantCoefficientsLinear Q m d).map_add p.1 q.1
  map_smul' k p := by
    apply Subtype.ext
    exact (invariantCoefficientsLinear Q m d).map_smul k p.1

theorem gradedCoefficientsLinear_bijective
    (Q : ρ → σ × σ → K) (m d r : ℕ) :
    Function.Bijective (gradedCoefficientsLinear Q m d r) := by
  constructor
  · intro p q h
    apply Subtype.ext
    exact (invariantCoefficientsLinear_bijective Q m d).1
      (congrArg Subtype.val h)
  · intro c
    obtain ⟨p, hp⟩ := (invariantCoefficientsLinear_bijective Q m d).2 c.1
    have hdegree : p ∈ degreePiece (currentCarrier Q m d) r := by
      apply (mem_degreePiece_iff_auxiliaryCoefficients Q m d r p).mpr
      intro a
      have ha : coefficientLinear Q m d a p = c.1.1 a := by
        exact DFunLike.congr_fun (congrArg Subtype.val hp) a
      rw [ha]
      exact c.2 a
    refine ⟨⟨p, hdegree⟩, ?_⟩
    apply Subtype.ext
    exact hp

/-- Exact graded coefficient factorization of the current carrier.  The target
is finite support and is supported only in auxiliary degrees `0,…,r`. -/
def gradedCoefficientsEquiv (Q : ρ → σ × σ → K) (m d r : ℕ) :
    degreePiece (currentCarrier Q m d) r ≃ₗ[K]
      gradedInvariantCoefficients Q m d r :=
  LinearEquiv.ofBijective (gradedCoefficientsLinear Q m d r)
    (gradedCoefficientsLinear_bijective Q m d r)

end

end VOA.QuadraticCurrentAuxiliaryGrading

section AxiomAudit
open VOA.QuadraticCurrentAuxiliaryGrading in
#print axioms currentAuxiliaryTensorEquiv_symm_tmul_mem_degreePiece
open VOA.QuadraticCurrentAuxiliaryGrading in
#print axioms mem_degreePiece_iff_auxiliaryCoefficients
open VOA.QuadraticCurrentAuxiliaryGrading in
#print axioms gradedCoefficientsEquiv
end AxiomAudit
