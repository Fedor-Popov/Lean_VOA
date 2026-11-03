import VOA.DeligneAudit.D4LeviKSRzMonomialEval

/-! X and Z label permutations preserve the D4 source word evaluator. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def rzSourceXPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    Equiv.Perm (PairSource a b c) :=
  Equiv.sumCongr e (Equiv.refl _)

def rzSourceZPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin c)) :
    Equiv.Perm (PairSource a b c) :=
  Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCongr (Equiv.refl _) e)

theorem pairSourceShape_XPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin b ⊕ Fin a)) :
    pairSourceShape a b c ∘ rzSourceXPerm a b c e =
      pairSourceShape a b c := by
  funext t
  rcases t with x | (y | z) <;> rfl

theorem pairSourceShape_ZPerm (a b c : ℕ)
    (e : Equiv.Perm (Fin c)) :
    pairSourceShape a b c ∘ rzSourceZPerm a b c e =
      pairSourceShape a b c := by
  funext t
  rcases t with x | (y | z) <;> rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pairSourceEvaluation_XPerm (ρ : CurrentModule D4sector.f V)
    (w : V) (a b c : ℕ) (e : Equiv.Perm (Fin b ⊕ Fin a))
    (P : MvPolynomial (PairSource a b c) ℂ) :
    xyzEvaluation ρ w (pairSourceShape a b c)
        (rename (rzSourceXPerm a b c e) P) =
      xyzEvaluation ρ w (pairSourceShape a b c) P := by
  rw [xyzEvaluation_rename_equiv, pairSourceShape_XPerm]

theorem pairSourceEvaluation_ZPerm (ρ : CurrentModule D4sector.f V)
    (w : V) (a b c : ℕ) (e : Equiv.Perm (Fin c))
    (P : MvPolynomial (PairSource a b c) ℂ) :
    xyzEvaluation ρ w (pairSourceShape a b c)
        (rename (rzSourceZPerm a b c e) P) =
      xyzEvaluation ρ w (pairSourceShape a b c) P := by
  rw [xyzEvaluation_rename_equiv, pairSourceShape_ZPerm]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSourceShape_XPerm
#print axioms VOA.DeligneAudit.D4Levi.pairSourceShape_ZPerm
#print axioms VOA.DeligneAudit.D4Levi.pairSourceEvaluation_XPerm
#print axioms VOA.DeligneAudit.D4Levi.pairSourceEvaluation_ZPerm
