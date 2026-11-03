import VOA.DeligneAudit.D4LeviKSMixedTargetHomogeneous
import VOA.DeligneAudit.D4LeviKSPairSpectatorEval

/-! Commuting a radical current past a fixed-shape polynomial evaluation. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem radicalWord_comm_spectator
    (ρ : CurrentModule D4sector.f V) (w : V)
    (l : List (Fin 6 × ℕ)) (j : Fin 6) (r : ℕ) :
    radicalWord ρ (ρ.op (radicalColour j) r w) l =
      ρ.op (radicalColour j) r (radicalWord ρ w l) := by
  have hp : (l ++ [(j, r)]).Perm ((j, r) :: l) := by
    simpa using (List.perm_append_comm (l₁ := l) (l₂ := [(j, r)]))
  calc
    _ = radicalWord ρ w (l ++ [(j, r)]) := by
      simp [radicalWord_eq_prod, List.map_append, List.prod_append,
        Module.End.mul_apply]
    _ = radicalWord ρ w ((j, r) :: l) := radicalWord_perm ρ w hp
    _ = _ := rfl

theorem xyzEvaluation_comm_spectator {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (P : MvPolynomial σ ℂ)
    (j : Fin 6) (r : ℕ) :
    xyzEvaluation ρ (ρ.op (radicalColour j) r w) shape P =
      ρ.op (radicalColour j) r (xyzEvaluation ρ w shape P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d t =>
      have hm : (monomial d t : MvPolynomial σ ℂ) =
          t • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul, map_smul]
      simp only [xyzEvaluation, modeWordEvaluation_monomial]
      exact congrArg (t • ·) (radicalWord_comm_spectator ρ w _ j r)
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ]

theorem xyzEvaluation_yZero_pow {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : σ → Fin 6) (P : MvPolynomial σ ℂ) (b : ℕ) :
    xyzEvaluation ρ (((yOp ρ 0) ^ b) w) shape P =
      ((yOp ρ 0) ^ b) (xyzEvaluation ρ w shape P) := by
  induction b with
  | zero => simp
  | succ b ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change xyzEvaluation ρ (ρ.op (radicalColour 4) 0
        (((yOp ρ 0) ^ b) w)) shape P = _
      rw [xyzEvaluation_comm_spectator, ih]
      rfl

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radicalWord_comm_spectator
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_comm_spectator
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_yZero_pow
