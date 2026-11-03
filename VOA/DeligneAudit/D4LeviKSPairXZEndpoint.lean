import VOA.DeligneAudit.D4LeviKSPairXZIter

/-! Identify the recoloured XZ endpoint with PAIR restriction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def pairYExponent (b : ℕ) (d : Fin b →₀ ℕ) (r : ℕ) : ℕ :=
  if h : r < b then d ⟨r, h⟩ else 0

theorem pairYExponent_at (b : ℕ) (d : Fin b →₀ ℕ) (y : Fin b) :
    pairYExponent b d y.val = d y := by
  simp [pairYExponent, y.isLt]

theorem pairXZEarlierFactor_full (a b c : ℕ) (d : Fin b →₀ ℕ) :
    pairXZEarlierFactor a b c b (fun y => d y) =
      pairPairedXZFinsuppMonomial a b c d := by
  classical
  simp only [pairXZEarlierFactor, Fin.isLt, Finset.filter_true]
  simp [pairPairedXZFinsuppMonomial, monomial_eq,
    pairPairedXZSlot, map_prod, map_pow]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairXZCoeff_adjoint_full
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) (d : Fin b →₀ ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28))
        ((List.range b).map (pairYExponent b d))
        (pairXZRecolourOperator ρ a b c 0
          (coeff d (pairSplitAlgebra a b c P))) w =
      ((-1 : ℂ) ^ b * (Nat.descFactorial (a + b) b : ℂ)) •
        xyzEvaluation ρ w (pairRecolourTargetShape a b c)
          (pairRestriction a b c
            (pairYFinsuppMonomial a b c d *
              rename (pairXZSource a b c)
                (coeff d (pairSplitAlgebra a b c P)))) := by
  have hQ (s t : Fin b ⊕ Fin a) :=
    pairYCoeff_swap_xz a b c s t P hP d
  have h := congrArg (fun A : Module.End ℂ V => A w)
    (pairXZRecolour_adjoint_full ρ a b c (pairYExponent b d)
      (coeff d (pairSplitAlgebra a b c P)) hQ)
  simpa only [LinearMap.smul_apply, pairXZRecolourOperator_apply,
    pairYExponent_at, pairXZEarlierFactor_full,
    pairXZRecolourShape_final,
    pairRestriction_yFinsupp_evaluation] using h

/-- The sum of all Y-coefficient transfers is the restriction polynomial
    evaluated at the paired XZ shape. -/
theorem pairXZCoeff_adjoint_sum
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (P : MvPolynomial (PairSource a b c) ℂ)
    (hP : P ∈ pairSourceSymmetric a b c) :
    (∑ d ∈ (pairSplitAlgebra a b c P).support,
      pairAdjoint (ρ.op (17 : Fin 28))
        ((List.range b).map (pairYExponent b d))
        (pairXZRecolourOperator ρ a b c 0
          (coeff d (pairSplitAlgebra a b c P))) w) =
      ((-1 : ℂ) ^ b * (Nat.descFactorial (a + b) b : ℂ)) •
        xyzEvaluation ρ w (pairRecolourTargetShape a b c)
          (pairRestriction a b c P) := by
  rw [pairRestriction_y_decomposition]
  simp only [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [pairRestriction_yFinsupp_xz] using
    pairXZCoeff_adjoint_full ρ w a b c P hP d

theorem pairXZCoeff_adjoint_sum_zero
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (P : pairSourceSymmetric a b c)
    (hP : pairSymmetricRestriction a b c P = 0) :
    (∑ d ∈ (pairSplitAlgebra a b c P).support,
      pairAdjoint (ρ.op (17 : Fin 28))
        ((List.range b).map (pairYExponent b d))
        (pairXZRecolourOperator ρ a b c 0
          (coeff d (pairSplitAlgebra a b c P))) w) = 0 := by
  rw [pairXZCoeff_adjoint_sum ρ w a b c P P.property]
  have hr : pairRestriction a b c P = 0 := by
    simpa only [pairSymmetricRestriction_apply, Subalgebra.coe_zero] using
      congrArg Subtype.val hP
  rw [hr, map_zero, smul_zero]

/-- Kernel cancellation holds as an identity of operators, so it can be
    applied after adjoining the U(0) spectator. -/
theorem pairXZCoeff_adjoint_sum_operator_zero
    (ρ : CurrentModule D4sector.f V) (a b c : ℕ)
    (P : pairSourceSymmetric a b c)
    (hP : pairSymmetricRestriction a b c P = 0) :
    (∑ d ∈ (pairSplitAlgebra a b c P).support,
      pairAdjoint (ρ.op (17 : Fin 28))
        ((List.range b).map (pairYExponent b d))
        (pairXZRecolourOperator ρ a b c 0
          (coeff d (pairSplitAlgebra a b c P)))) = 0 := by
  ext v
  simpa only [LinearMap.sum_apply, LinearMap.zero_apply] using
    pairXZCoeff_adjoint_sum_zero ρ v a b c P hP

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairYExponent_at
#print axioms VOA.DeligneAudit.D4Levi.pairXZEarlierFactor_full
#print axioms VOA.DeligneAudit.D4Levi.pairXZCoeff_adjoint_full
#print axioms VOA.DeligneAudit.D4Levi.pairXZCoeff_adjoint_sum
#print axioms VOA.DeligneAudit.D4Levi.pairXZCoeff_adjoint_sum_zero
#print axioms VOA.DeligneAudit.D4Levi.pairXZCoeff_adjoint_sum_operator_zero
