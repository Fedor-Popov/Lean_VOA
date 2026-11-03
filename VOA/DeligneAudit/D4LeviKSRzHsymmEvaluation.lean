import VOA.DeligneAudit.D4LeviKSRzAllocationVectors

/-! Evaluate a complete homogeneous Z polynomial as finite radical words. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rz_hsymm_z_evaluation_vectors
    (ρ : CurrentModule D4sector.f V) (w : V) (k s : ℕ) :
    xyzEvaluation ρ w (fun _ : Fin k => (5 : Fin 6))
      (hsymm (Fin k) ℂ s) =
      ∑ e : {e : Fin k → ℕ // ∑ i, e i = s},
        radicalWord ρ w ((List.ofFn e.1).map fun r => ((5 : Fin 6), r)) := by
  classical
  rw [rz_hsymm_eq_sum_vectors, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [xyzEvaluation_prod_X_pow]
  have hperm : (Finset.univ.toList : List (Fin k)).Perm
      (List.finRange k) := by
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList _) (List.nodup_finRange _)).2
    intro t
    simp
  have hword := hperm.map
    (fun t : Fin k => ((5 : Fin 6), e.1 t))
  rw [radicalWord_perm ρ w hword]
  simp only [List.ofFn_eq_map, List.map_map, Function.comp_def]

theorem rz_hsymm_z_evaluation_allocations
    (ρ : CurrentModule D4sector.f V) (w : V) (k s : ℕ) :
    xyzEvaluation ρ w (fun _ : Fin k => (5 : Fin 6))
      (hsymm (Fin k) ℂ s) =
      ((modeAllocations (List.replicate k 0) s).map fun modes =>
        radicalWord ρ w (modes.map fun r => ((5 : Fin 6), r))).sum := by
  rw [rz_hsymm_z_evaluation_vectors]
  exact (rz_zero_alloc_sum_eq_vector_sum k s
    (fun modes => radicalWord ρ w
      (modes.map fun r => ((5 : Fin 6), r)))).symm

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rz_hsymm_z_evaluation_vectors
#print axioms VOA.DeligneAudit.D4Levi.rz_hsymm_z_evaluation_allocations
