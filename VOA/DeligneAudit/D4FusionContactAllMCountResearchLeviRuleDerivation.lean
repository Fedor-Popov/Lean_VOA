import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleChecks
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import Lean.Elab.Tactic.Omega

/-! The exact color cancellation lifts to every current cutoff. Truncating
an intermediate nonnegative mode also truncates the final summed mode. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section

variable {A : Type*} [CommRing A]

theorem bracket_value (v : Fin 9 → A) (a b : Fin 18) (i : Fin 9) :
    coeff b i • (coeff a (target b i) • v (target a (target b i))) -
      coeff a i • (coeff b (target a i) • v (target b (target a i))) =
      bracketCoeff a b • (coeff (bracketTarget a b) i • v (target (bracketTarget a b) i)) := by
  have h := Rows.eval_zero_of_collect v (bracketRow a b i) (bracketRow_check a b i)
  simp only [bracketRow,Rows.eval_cons,Rows.wordEval,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,Rows.eval_nil,neg_smul,add_zero] at h
  apply sub_eq_zero.mp
  simp only [smul_smul]
  convert h using 1
  abel

variable (K : Type*) [CommRing K]
abbrev Ring (m : ℕ) := MvPolynomial (Fin 9 × Fin m) K

def mode (m : ℕ) (i : Fin 9) (r : ℕ) : Ring K m :=
  if hr : r < m then MvPolynomial.X (i,⟨r,hr⟩) else 0

def deriv (m : ℕ) (a : Fin 18) (k : ℕ) : Derivation K (Ring K m) (Ring K m) :=
  MvPolynomial.mkDerivation K (fun x => coeff a x.1 • mode K m (target a x.1) (k+x.2.val))

theorem deriv_X (m : ℕ) (a : Fin 18) (k : ℕ) (x : Fin 9 × Fin m) :
    deriv K m a k (MvPolynomial.X x) = coeff a x.1 • mode K m (target a x.1) (k+x.2.val) :=
  MvPolynomial.mkDerivation_X K _ _

theorem deriv_mode (m : ℕ) (a : Fin 18) (k : ℕ) (i : Fin 9) (r : ℕ) :
    deriv K m a k (mode K m i r) = coeff a i • mode K m (target a i) (k+r) := by
  by_cases hr : r < m
  · rw [mode,dif_pos hr,deriv_X]
  · have hkr : ¬ k+r < m := by omega
    simp only [mode,dif_neg hr,dif_neg hkr,map_zero,zsmul_zero]

/-- The entire18-operator current Lie relation, with no mode restriction. -/
theorem deriv_bracket (m : ℕ) (a b : Fin 18) (k l : ℕ) :
    ⁅deriv K m a k,deriv K m b l⁆ =
      bracketCoeff a b • deriv K m (bracketTarget a b) (k+l) := by
  apply MvPolynomial.derivation_ext
  intro x
  simp only [Derivation.commutator_apply,Derivation.smul_apply,deriv_X,map_zsmul,deriv_mode]
  rw [show k+(l+x.2.val) = k+l+x.2.val by omega,
    show l+(k+x.2.val) = k+l+x.2.val by omega]
  exact bracket_value (fun i => mode K m i (k+l+x.2.val)) a b x.1

theorem deriv_high (m : ℕ) (a : Fin 18) (k : ℕ) (hk : m ≤ k) : deriv K m a k = 0 := by
  apply MvPolynomial.derivation_ext
  intro x
  rw [deriv_X]
  have hkr : ¬ k+x.2.val < m := by omega
  simp only [mode,dif_neg hkr,zsmul_zero,Derivation.zero_apply]

end
#print axioms deriv_bracket
#print axioms deriv_high
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
