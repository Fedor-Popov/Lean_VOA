import VOA.DeligneAudit.D4FusionContactAllMCountResearchTransport

/-! # Grouped-seed differential expressions in the actual all-m ideal

The source coefficient is kept whole, with its multiplicity 1/2. Every
expression has genuine candidate-ideal membership. An exact linear split
separates the endpoint expression from its middle-mode correction.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open BoundaryPair

noncomputable section

inductive WheelExpr where
  | base
  | plus (a b : WheelExpr)
  | scale (numerator denominator : ℤ) (a : WheelExpr)
  | mul (v : Fin 18) (a : WheelExpr)
  | deriv (d : Fin 36) (a : WheelExpr)

variable {m : ℕ} (b : BoundaryPair m)

def evalMap : WheelExpr → Module.End ℂ (MvPolynomial (Vars m) ℂ)
  | .base => LinearMap.id
  | .plus a c => evalMap a + evalMap c
  | .scale n d a => ((n:ℂ)/(d:ℂ)) • evalMap a
  | .mul v a => (LinearMap.mulLeft ℂ (MvPolynomial.X (b.embed (M2Certificate.varIndex v)))).comp
      (evalMap a)
  | .deriv d a =>
      (Polynomial.AllM.candidateDeriv m
        (b.mapDeriv (M2Certificate.derivationIndex d))).toLinearMap.comp (evalMap a)

def twoEvalMap : WheelExpr → Module.End ℂ (MvPolynomial (Vars 2) ℂ)
  | .base => LinearMap.id
  | .plus a c => twoEvalMap a + twoEvalMap c
  | .scale n d a => ((n:ℂ)/(d:ℂ)) • twoEvalMap a
  | .mul v a => (LinearMap.mulLeft ℂ (MvPolynomial.X (M2Certificate.varIndex v))).comp
      (twoEvalMap a)
  | .deriv d a => (Polynomial.candidateDeriv (M2Certificate.derivationIndex d)).toLinearMap.comp
      (twoEvalMap a)

def quadraticSeedIndex : Polynomial.AllM.SeedIndex m :=
  ⟨(false,2,b.lower.val+b.top.val),by
    constructor
    · change 1 ≤ 2
      decide
    · simp only [Polynomial.AllM.seedThreshold,Bool.false_eq_true,if_false]
      have := b.last
      omega⟩

def groupedSeed : MvPolynomial (Vars m) ℂ :=
  (1/2:ℂ) • Polynomial.AllM.seedPoly m (quadraticSeedIndex b)

theorem groupedSeed_whole : groupedSeed b = (1/2:ℂ) •
    PowerSeries.coeff (b.lower.val+b.top.val) (Polynomial.AllM.current m 0 ^ 2) := rfl

theorem groupedSeed_mem : groupedSeed b ∈ Polynomial.AllM.candidateIdeal m :=
  (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ |>.smul_mem _
    (Polynomial.AllM.seed_mem_candidate m (quadraticSeedIndex b))

/-- Arbitrary multipliers and actual current derivatives are both retained. -/
theorem evalMap_mem (e : WheelExpr) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ Polynomial.AllM.candidateIdeal m) :
    evalMap b e p ∈ Polynomial.AllM.candidateIdeal m := by
  induction e with
  | base => exact hp
  | plus a c iha ihc => exact Ideal.add_mem _ iha ihc
  | scale n d a ih =>
      exact ((Polynomial.AllM.candidateIdeal m).restrictScalars ℂ).smul_mem _ ih
  | mul v a ih => exact Ideal.mul_mem_left _ _ ih
  | deriv d a ih => exact Polynomial.AllM.candidateIdeal_deriv m _ ih

def corrected (e : WheelExpr) : MvPolynomial (Vars m) ℂ := evalMap b e (groupedSeed b)

theorem corrected_mem (e : WheelExpr) : corrected b e ∈ Polynomial.AllM.candidateIdeal m :=
  evalMap_mem b e (groupedSeed_mem b)

theorem evalMap_transport (e : WheelExpr) (p : MvPolynomial (Vars 2) ℂ) :
    evalMap b e (MvPolynomial.rename b.embed p) =
      MvPolynomial.rename b.embed (twoEvalMap e p) := by
  induction e with
  | base => rfl
  | plus a c iha ihc => simp only [evalMap,twoEvalMap,LinearMap.add_apply,iha,ihc,map_add]
  | scale n d a ih => simp only [evalMap,twoEvalMap,LinearMap.smul_apply,ih,map_smul]
  | mul v a ih =>
      simp only [evalMap,twoEvalMap,LinearMap.comp_apply,LinearMap.mulLeft_apply,ih,
        map_mul,MvPolynomial.rename_X]
  | deriv d a ih =>
      simp only [evalMap,twoEvalMap,LinearMap.comp_apply,ih,Derivation.coeFn_coe]
      exact (transport_deriv b (M2Certificate.derivationIndex d) (twoEvalMap a p)).symm

def twoSeed : MvPolynomial (Vars 2) ℂ := MvPolynomial.X (0,0) * MvPolynomial.X (0,1)

def middleSeed : MvPolynomial (Vars m) ℂ :=
  groupedSeed b - MvPolynomial.rename b.embed twoSeed

/-- This exact decomposition retains the grouped middle coefficients. -/
theorem corrected_split (e : WheelExpr) : corrected b e =
    MvPolynomial.rename b.embed (twoEvalMap e twoSeed) + evalMap b e (middleSeed b) := by
  simp only [corrected,middleSeed,map_sub,evalMap_transport]
  abel

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.corrected_mem
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.corrected_split
