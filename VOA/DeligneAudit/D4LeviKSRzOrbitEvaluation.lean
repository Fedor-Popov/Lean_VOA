import VOA.DeligneAudit.D4LeviKSRzBlockPerm

/-! Evaluation of the two block orbit sums in the Rz source. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def rzRawSourceGenerator (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ) :
    MvPolynomial (PairSource a b (k + l)) ℂ :=
  rename Sum.inl (rzXSeed a b α) *
    rename (fun z : Fin (k + l) =>
      (Sum.inr (Sum.inr z) : PairSource a b (k + l)))
      (rzZSeed k l s β)

theorem rzSourceGenerator_orbit_term (a b k l s : ℕ)
    (α : Fin b ⊕ Fin a → ℕ) (β : Fin l → ℕ)
    (eX : Equiv.Perm (Fin b ⊕ Fin a))
    (eZ : Equiv.Perm (Fin (k + l))) :
    rename Sum.inl (rename eX (rzXSeed a b α)) *
        rename (fun z : Fin (k + l) =>
          (Sum.inr (Sum.inr z) : PairSource a b (k + l)))
          (rename eZ (rzZSeed k l s β)) =
      rename (rzSourceXPerm a b (k + l) eX)
        (rename (rzSourceZPerm a b (k + l) eZ)
          (rzRawSourceGenerator a b k l s α β)) := by
  simp only [rzRawSourceGenerator, map_mul, rename_rename]
  congr 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzSourceGenerator_orbit_term_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) (eX : Equiv.Perm (Fin b ⊕ Fin a))
    (eZ : Equiv.Perm (Fin (k + l))) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rename Sum.inl (rename eX (rzXSeed a b α)) *
          rename (fun z : Fin (k + l) =>
            (Sum.inr (Sum.inr z) : PairSource a b (k + l)))
            (rename eZ (rzZSeed k l s β))) =
      xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzRawSourceGenerator a b k l s α β) := by
  rw [rzSourceGenerator_orbit_term]
  rw [pairSourceEvaluation_XPerm, pairSourceEvaluation_ZPerm]

theorem rzSourceGenerator_evaluation
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzSourceGenerator a b k l s α β) =
      (Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) *
        Nat.card (Equiv.Perm (Fin (k + l)))) •
        xyzEvaluation ρ w (pairSourceShape a b (k + l))
          (rzRawSourceGenerator a b k l s α β) := by
  classical
  calc
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzSourceGenerator a b k l s α β) =
      ∑ eX : Equiv.Perm (Fin b ⊕ Fin a),
        ∑ eZ : Equiv.Perm (Fin (k + l)),
          xyzEvaluation ρ w (pairSourceShape a b (k + l))
            (rename Sum.inl (rename eX (rzXSeed a b α)) *
              rename (fun z : Fin (k + l) =>
                (Sum.inr (Sum.inr z) : PairSource a b (k + l)))
                (rename eZ (rzZSeed k l s β))) := by
      simp only [rzSourceGenerator, rzOrbitSum, map_sum,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr
      · ext eX
        simp
      · intro eX heX
        apply Finset.sum_congr
        · ext eZ
          simp
        · intro eZ heZ
          rfl
    _ = ∑ _eX : Equiv.Perm (Fin b ⊕ Fin a),
          ∑ _eZ : Equiv.Perm (Fin (k + l)),
            xyzEvaluation ρ w (pairSourceShape a b (k + l))
              (rzRawSourceGenerator a b k l s α β) := by
      apply Finset.sum_congr rfl
      intro eX heX
      apply Finset.sum_congr rfl
      intro eZ heZ
      exact rzSourceGenerator_orbit_term_evaluation ρ w a b k l s α β eX eZ
    _ = (Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) *
          Nat.card (Equiv.Perm (Fin (k + l)))) •
          xyzEvaluation ρ w (pairSourceShape a b (k + l))
            (rzRawSourceGenerator a b k l s α β) := by
      simp [Nat.card_eq_fintype_card, mul_smul]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_orbit_term
#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_orbit_term_evaluation
#print axioms VOA.DeligneAudit.D4Levi.rzSourceGenerator_evaluation
