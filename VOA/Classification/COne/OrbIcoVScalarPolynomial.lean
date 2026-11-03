import VOA.Classification.COne.OrbIcoVUniformSource
import Mathlib.Algebra.Polynomial.Derivative

/-! Polynomial semantics of the normalized even C2 scalar source.
Multiplication by X is the surviving L-minus-two term; X times derivative
retains the exact exponent contribution. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma Polynomial
open scoped Classical

def polyWidthStep (H K : ℂ) (r j : ℕ) (P : ℂ[X]) : ℂ[X] :=
  (if r-j=2 then X*P else 0) + (-1:ℂ)^(r-j) •
    ((((r-j:ℕ):ℂ)+1)*H-K+(j:ℂ)) • P -
    (-1:ℂ)^(r-j) • ((2:ℂ) • (X*P.derivative))

theorem coeff_euler (P : ℂ[X]) (n : ℕ) :
    (X*P.derivative).coeff n = (n:ℂ)*P.coeff n := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_X_mul,coeff_derivative]; push_cast; ring

theorem polyWidthStep_coeff (H K : ℂ) (r j n : ℕ) (P : ℂ[X]) :
    (polyWidthStep H K r j P).coeff n =
      (-1:ℂ)^(r-j)*((((r-j:ℕ):ℂ)+1)*H-K+(j:ℂ)-2*(n:ℂ))*P.coeff n +
        if r-j=2 ∧ 0<n then P.coeff (n-1) else 0 := by
  simp only [polyWidthStep,coeff_sub,coeff_add,coeff_smul,smul_eq_mul,coeff_euler]
  by_cases hk : r-j=2
  · rw [if_pos hk]
    cases n with
    | zero => simp; ring
    | succ n => simp [hk,coeff_X_mul]; ring
  · rw [if_neg hk,coeff_zero,if_neg (by tauto)]
    ring

def polyWidthStage (H K t : ℂ) : ℕ → ℂ[X] → ℂ[X]
  | 0,P => P
  | r+1,P => (-t/(((r:ℂ)+1)*(13-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), polyWidthStep H K (r+1) j (polyWidthStage H K t j P)
termination_by r => r

def polyWidthSource (H K t : ℂ) (P : ℂ[X]) : ℂ[X] :=
  ∑ j : Fin 13, polyWidthStep H K 13 j (polyWidthStage H K t j P)

theorem polyWidthStep_add (H K : ℂ) (r j : ℕ) (P Q : ℂ[X]) :
    polyWidthStep H K r j (P+Q)=polyWidthStep H K r j P+polyWidthStep H K r j Q := by
  simp only [polyWidthStep,derivative_add,mul_add,smul_add]
  split_ifs <;> module

theorem polyWidthStep_smul (H K a : ℂ) (r j : ℕ) (P : ℂ[X]) :
    polyWidthStep H K r j (a • P)=a • polyWidthStep H K r j P := by
  simp only [polyWidthStep,derivative_smul,mul_smul_comm,smul_add,smul_sub,smul_smul]
  split_ifs
  all_goals try simp only [smul_zero,zero_add]
  all_goals module

theorem polyWidthStage_add (H K t : ℂ) (r : ℕ) (P Q : ℂ[X]) :
    polyWidthStage H K t r (P+Q)=polyWidthStage H K t r P+polyWidthStage H K t r Q := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp only [polyWidthStage]
    | succ r =>
      simp only [polyWidthStage]
      have he (j : Fin (r+1)) := ih j j.isLt
      simp only [he,polyWidthStep_add,Finset.sum_add_distrib,smul_add]

theorem polyWidthStage_smul (H K t a : ℂ) (r : ℕ) (P : ℂ[X]) :
    polyWidthStage H K t r (a • P)=a • polyWidthStage H K t r P := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp only [polyWidthStage]
    | succ r =>
      simp only [polyWidthStage]
      have he (j : Fin (r+1)) := ih j j.isLt
      simp only [he,polyWidthStep_smul,← Finset.smul_sum,smul_smul]
      rw [mul_comm]

end VOA.Classification.COne.OrbIcoV
