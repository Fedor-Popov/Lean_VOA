import VOA.DeligneAudit.D4LeviKSPairXZTarget

/-! Recolour the Y-free XZ coefficients without inserting Y(0) slots. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def pairXZRecolourShape (a b c k : ℕ) : PairXZ a b c → Fin 6 :=
  pairRecolourShape a b c k ∘ pairXZSource a b c

theorem pairXZRecolourShape_zero (a b c : ℕ) :
    pairXZRecolourShape a b c 0 =
      fun t => match t with
        | Sum.inl _ => 1
        | Sum.inr _ => 5 := by
  funext t
  rcases t with (y | x) | z <;>
    simp [pairXZRecolourShape, pairRecolourShape, pairXZSource]

theorem pairXZRecolourShape_final (a b c : ℕ) :
    pairXZRecolourShape a b c b = pairXZFinalShape a b c := by
  funext t
  rcases t with (y | x) | z
  · simp [pairXZRecolourShape, pairXZSource,
      pairRecolourShape_paired_final, pairXZFinalShape]
  · rfl
  · rfl

theorem pairXZRecolourShape_ne_u (a b c k : ℕ) (t : PairXZ a b c) :
    pairXZRecolourShape a b c k t ≠ 2 :=
  pairRecolourShape_ne_u a b c k (pairXZSource a b c t)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def pairXZRecolourOperator
    (ρ : CurrentModule D4sector.f V) (a b c k : ℕ) :
    MvPolynomial (PairXZ a b c) ℂ →ₗ[ℂ] Module.End ℂ V :=
  (pairWordOpEvaluation ρ).comp
    (pairPolynomialWords (pairXZRecolourShape a b c k))

theorem pairXZRecolourOperator_apply
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c k : ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairXZRecolourOperator ρ a b c k Q w =
      xyzEvaluation ρ w (pairXZRecolourShape a b c k) Q := by
  exact pairPolynomialWords_eval ρ w (pairXZRecolourShape a b c k) Q

/-- One f₃ mode converts precisely the remaining X positions of an XZ
    coefficient. The Y letters are absent from this operator. -/
theorem pairXZRecolour_adjoint_positions
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c k r : ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r]
        (pairXZRecolourOperator ρ a b c k Q) w =
      -pairPositionalEvaluation ρ w (pairXZRecolourShape a b c k) r Q := by
  change pairAdjoint (ρ.op (17 : Fin 28)) [r]
      (pairWordOpEvaluation ρ
        (pairPolynomialWords (pairXZRecolourShape a b c k) Q)) w = _
  rw [pairWordOpEvaluation_convert]
  change -pairWordOpEvaluation ρ
      (pairPolynomialConvert (pairXZRecolourShape a b c k) r Q) w = _
  rw [pairPolynomialConvert_evaluation_positions ρ w
    (pairXZRecolourShape a b c k)
    (pairXZRecolourShape_ne_u a b c k) r Q]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolourShape_zero
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolourShape_final
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolourShape_ne_u
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolourOperator_apply
#print axioms VOA.DeligneAudit.D4Levi.pairXZRecolour_adjoint_positions
