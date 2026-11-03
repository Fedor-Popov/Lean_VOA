import VOA.DeligneAudit.D4LeviKSPairYCoeffSym

/-! The Y-free recolouring endpoint has exactly the PAIR target shape. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def pairXZTargetEquiv (a b c : ℕ) : PairXZ a b c ≃ PairTarget a b c where
  toFun := pairXZTarget a b c
  invFun
    | Sum.inl x => Sum.inl (Sum.inr x)
    | Sum.inr (Sum.inl y) => Sum.inl (Sum.inl y)
    | Sum.inr (Sum.inr z) => Sum.inr z
  left_inv := by
    intro t
    rcases t with (y | x) | z <;> rfl
  right_inv := by
    intro t
    rcases t with x | (y | z) <;> rfl

def pairXZFinalShape (a b c : ℕ) : PairXZ a b c → Fin 6
  | Sum.inl (Sum.inl _) => 3
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr _ => 5

theorem pairXZFinalShape_target (a b c : ℕ) :
    pairRecolourTargetShape a b c ∘ pairXZTargetEquiv a b c =
      pairXZFinalShape a b c := by
  funext t
  rcases t with (y | x) | z <;> rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Fixed-shape evaluation is equivariant under a bijection between two
    finite position types. -/
theorem xyzEvaluation_rename_bijection {σ τ : Type*}
    [Fintype σ] [Fintype τ]
    (ρ : CurrentModule D4sector.f V) (w : V)
    (shape : τ → Fin 6) (e : σ ≃ τ) (P : MvPolynomial σ ℂ) :
    xyzEvaluation ρ w shape (rename e P) =
      xyzEvaluation ρ w (shape ∘ e) P := by
  classical
  have hword (d : σ →₀ ℕ) :
      (shapedModes shape Finset.univ.toList (d.mapDomain e)).Perm
        (shapedModes (shape ∘ e) Finset.univ.toList d) := by
    have hp : (Finset.univ.toList.map (e : σ → τ)).Perm
        (Finset.univ.toList : List τ) := by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (Finset.nodup_toList _).map e.injective
      · exact Finset.nodup_toList _
      · ext i
        simp
        exact e.surjective i
    have h := hp.map fun j => (shape j, d (e.symm j))
    simpa [shapedModes, List.map_map, Function.comp_def,
      Finsupp.mapDomain_equiv_apply] using h.symm
  induction P using MvPolynomial.induction_on' with
  | monomial d t =>
      have hm : (monomial d t : MvPolynomial σ ℂ) =
          t • modeMonomial σ d := by
        simp [modeMonomial, smul_monomial]
      rw [hm]
      simp only [map_smul]
      have hr : rename e (modeMonomial σ d) =
          modeMonomial τ (d.mapDomain e) := by
        simp [modeMonomial, rename_monomial]
      rw [hr]
      simp only [xyzEvaluation, modeWordEvaluation_monomial]
      exact congrArg (t • ·) (radicalWord_perm ρ w (hword d))
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ]

/-- The target evaluator agrees with the Y-free endpoint after the
    bijective relabelling of paired X, unpaired X, and Z positions. -/
theorem pairXZFinalEvaluation_target
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c : ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    xyzEvaluation ρ w (pairRecolourTargetShape a b c)
        (rename (pairXZTarget a b c) Q) =
      xyzEvaluation ρ w (pairXZFinalShape a b c) Q := by
  have h := xyzEvaluation_rename_bijection ρ w
    (pairRecolourTargetShape a b c) (pairXZTargetEquiv a b c) Q
  simpa only [pairXZFinalShape_target] using h

theorem pairRestriction_yFinsupp_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V) (a b c : ℕ)
    (d : Fin b →₀ ℕ) (Q : MvPolynomial (PairXZ a b c) ℂ) :
    xyzEvaluation ρ w (pairRecolourTargetShape a b c)
        (pairRestriction a b c
          (pairYFinsuppMonomial a b c d * rename (pairXZSource a b c) Q)) =
      xyzEvaluation ρ w (pairXZFinalShape a b c)
        (pairPairedXZFinsuppMonomial a b c d * Q) := by
  rw [pairRestriction_yFinsupp_xz]
  exact pairXZFinalEvaluation_target ρ w a b c _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairXZFinalShape_target
#print axioms VOA.DeligneAudit.D4Levi.xyzEvaluation_rename_bijection
#print axioms VOA.DeligneAudit.D4Levi.pairXZFinalEvaluation_target
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_yFinsupp_evaluation
