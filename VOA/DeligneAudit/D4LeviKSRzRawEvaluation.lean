import VOA.DeligneAudit.D4LeviKSRzSourceOrder

/-! Evaluate the raw Rz source with its X, Y, and Z slots separated. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzRawModeWord_perm
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) (e : Fin k → ℕ) :
    radicalWord ρ w
        ((Finset.univ.toList : List (PairSource a b (k + l))).map
          fun t => (pairSourceShape a b (k + l) t,
            rzRawModes a b k l α β e t)) =
      radicalWord ρ w
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
            fun x => ((1 : Fin 6), α x)) ++
          List.replicate b ((4 : Fin 6), 0) ++
          ((Finset.univ.toList : List (Fin k)).map
            fun z => ((5 : Fin 6), e z)) ++
          ((Finset.univ.toList : List (Fin l)).map
            fun z => ((5 : Fin 6), β z))) := by
  classical
  have hp := (rz_source_univ_perm a b k l).map
    (fun t => (pairSourceShape a b (k + l) t,
      rzRawModes a b k l α β e t))
  rw [radicalWord_perm ρ w hp]
  simp [List.map_append, List.map_map, Function.comp_def,
    pairSourceShape, rzRawModes, Fin.addCases_left, Fin.addCases_right]

theorem rzRawSourceGenerator_eval_vectors
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzRawSourceGenerator a b k l s α β) =
      ∑ e : {e : Fin k → ℕ // ∑ i, e i = s},
        radicalWord ρ w
          (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
              fun x => ((1 : Fin 6), α x)) ++
            List.replicate b ((4 : Fin 6), 0) ++
            ((Finset.univ.toList : List (Fin k)).map
              fun z => ((5 : Fin 6), e.1 z)) ++
            ((Finset.univ.toList : List (Fin l)).map
              fun z => ((5 : Fin 6), β z))) := by
  classical
  rw [rzRawSourceGenerator_eq_sum_monomials, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [xyzEvaluation_prod_X_pow]
  exact rzRawModeWord_perm ρ w a b k l α β e.1

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzRawModeWord_perm
#print axioms VOA.DeligneAudit.D4Levi.rzRawSourceGenerator_eval_vectors
