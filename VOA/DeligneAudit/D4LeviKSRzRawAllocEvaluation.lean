import VOA.DeligneAudit.D4LeviKSRzRawEvaluation

/-! Replace the Rz mode-vector sum by the ordered allocation list. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_finset_modes_perm (k : ℕ) (e : Fin k → ℕ) :
    ((Finset.univ.toList : List (Fin k)).map e).Perm (List.ofFn e) := by
  classical
  have hperm : (Finset.univ.toList : List (Fin k)).Perm
      (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList _) (List.nodup_finRange _)).2
    intro t
    simp
  simpa only [List.ofFn_eq_map] using hperm.map e

theorem rzRawSourceGenerator_eval_allocations
    (ρ : CurrentModule D4sector.f V) (w : V)
    (a b k l s : ℕ) (α : Fin b ⊕ Fin a → ℕ)
    (β : Fin l → ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b (k + l))
        (rzRawSourceGenerator a b k l s α β) =
      ((modeAllocations (List.replicate k 0) s).map fun modes =>
        radicalWord ρ w
          (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
              fun x => ((1 : Fin 6), α x)) ++
            List.replicate b ((4 : Fin 6), 0) ++
            (modes.map fun z => ((5 : Fin 6), z)) ++
            ((Finset.univ.toList : List (Fin l)).map
              fun z => ((5 : Fin 6), β z)))).sum := by
  classical
  rw [rzRawSourceGenerator_eval_vectors]
  rw [rz_zero_alloc_sum_eq_vector_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hp := (rz_finset_modes_perm k e.1).map
    (fun z => ((5 : Fin 6), z))
  have hp' := (hp.append_right
    ((Finset.univ.toList : List (Fin l)).map
      fun z => ((5 : Fin 6), β z))).append_left
    (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map
      fun x => ((1 : Fin 6), α x)) ++
      List.replicate b ((4 : Fin 6), 0))
  have hw := radicalWord_perm ρ w hp'
  simpa only [List.map_map, List.append_assoc] using hw

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_finset_modes_perm
#print axioms VOA.DeligneAudit.D4Levi.rzRawSourceGenerator_eval_allocations
