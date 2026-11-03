import VOA.DeligneAudit.D4LeviKSMixedZeroPrefix
import VOA.DeligneAudit.D4LeviKSRzHsymmEvaluation

/-! Complete homogeneous mode polynomials for mixed radical colours. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem xyz_hsymm_evaluation_allocations
    (ρ : CurrentModule D4sector.f V) (w : V)
    (n s : ℕ) (shape : Fin n → Fin 6) :
    xyzEvaluation ρ w shape (hsymm (Fin n) ℂ s) =
      ((modeAllocations (List.replicate n 0) s).map fun modes =>
        radicalWord ρ w
          ((List.finRange n).zip modes |>.map fun p => (shape p.1, p.2))).sum := by
  classical
  rw [rz_hsymm_eq_sum_vectors, map_sum]
  have hvec : ∀ e : {e : Fin n → ℕ // ∑ i, e i = s},
      xyzEvaluation ρ w shape
        (∏ i : Fin n, X i ^ e.1 i) =
        radicalWord ρ w
          ((List.finRange n).map fun i => (shape i, e.1 i)) := by
    intro e
    rw [xyzEvaluation_prod_X_pow]
    have hperm : (Finset.univ.toList : List (Fin n)).Perm
        (List.finRange n) := by
      apply (List.perm_ext_iff_of_nodup
        (Finset.nodup_toList _) (List.nodup_finRange _)).2
      intro t
      simp
    exact radicalWord_perm ρ w (hperm.map fun i => (shape i, e.1 i))
  simp_rw [hvec]
  have hzip (e : Fin n → ℕ) :
      ((List.finRange n).zip (List.ofFn e) |>.map fun p =>
        (shape p.1, p.2)) =
        (List.finRange n).map (fun i => (shape i, e i)) := by
    simp only [List.ofFn_eq_map]
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons i l ih => simp [ih]
  simp_rw [← hzip]
  rw [← rz_zero_alloc_sum_eq_vector_sum n s
    (fun modes => radicalWord ρ w
      ((List.finRange n).zip modes |>.map fun p => (shape p.1, p.2)))]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xyz_hsymm_evaluation_allocations
