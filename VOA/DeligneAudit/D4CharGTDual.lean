import VOA.DeligneAudit.D4CharGaussian

/-! GT duality from reversal of the interlacing rows and Gaussian symmetry. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

def gtDual {N : ℕ} (lam : Fin N → ℤ) : Fin N → ℤ := fun i => -lam i.rev

theorem gtDual_involutive {N : ℕ} (lam : Fin N → ℤ) : gtDual (gtDual lam) = lam := by
  funext i
  simp [gtDual]

theorem gtRows_dual {N : ℕ} (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) :
    gtDual μ ∈ gtRows (gtDual lam) ↔ μ ∈ gtRows lam := by
  rw [mem_gtRows, mem_gtRows]
  constructor
  · intro h i
    have hi := h i.rev
    simpa [gtDual, Fin.rev_succ, Fin.rev_castSucc, and_comm] using hi
  · intro h i
    have hi := h i.rev
    simpa [gtDual, Fin.rev_succ, Fin.rev_castSucc, and_comm] using hi

theorem gtDual_sum {N : ℕ} (lam : Fin N → ℤ) :
    (∑ i, gtDual lam i) = -(∑ i, lam i) := by
  simp only [gtDual, Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp Fin.revPerm lam

theorem gtPsi_dual {R : Type*} [CommRing R] (q : R) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam) :
    gtPsi q (gtDual lam) (gtDual μ) = gtPsi q lam μ := by
  unfold gtPsi
  apply Fintype.prod_equiv Fin.revPerm
  intro i
  have hm := (mem_gtRows lam μ).mp hμ i.rev
  simp only [gtDual, Fin.rev_castSucc, Fin.rev_succ, neg_sub_neg, Fin.revPerm_apply]
  have he : (μ i.rev - lam i.rev.succ).toNat =
      (lam i.rev.castSucc - lam i.rev.succ).toNat -
        (lam i.rev.castSucc - μ i.rev).toNat := by omega
  rw [he]
  exact qbinom_symm q _ _ (by omega)

theorem sum_gtRows_dual {R : Type*} [AddCommMonoid R] {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (f : (Fin N → ℤ) → R) :
    (∑ μ ∈ gtRows (gtDual lam), f μ) = ∑ μ ∈ gtRows lam, f (gtDual μ) := by
  classical
  refine Finset.sum_bij' (fun μ _ => gtDual μ) (fun μ _ => gtDual μ)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simpa only [gtDual_involutive] using (gtRows_dual (gtDual lam) μ).mpr hμ
  · intro μ hμ
    exact (gtRows_dual lam μ).mpr hμ
  · intro μ _
    exact gtDual_involutive μ
  · intro μ _
    exact gtDual_involutive μ
  · intro μ _
    rw [gtDual_involutive]

/-- Lemma 3.2(b), for every rank and every integer row. -/
theorem gtEval_duality {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ)
    (N : ℕ) (lam : Fin N → ℤ) :
    gtEval q u N (gtDual lam) = gtEval q (fun i => (u i)⁻¹) N lam := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [gtEval, sum_gtRows_dual, gtEval]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [gtPsi_dual q lam μ hμ, ih, gtDual_sum, gtDual_sum]
      rw [show -(∑ i, lam i) - -(∑ i, μ i) = -((∑ i, lam i) - ∑ i, μ i) by ring,
        zpow_neg, inv_zpow]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtDual_involutive
#print axioms VOA.DeligneAudit.D4Char.gtRows_dual
#print axioms VOA.DeligneAudit.D4Char.gtDual_sum
#print axioms VOA.DeligneAudit.D4Char.gtPsi_dual
#print axioms VOA.DeligneAudit.D4Char.sum_gtRows_dual
#print axioms VOA.DeligneAudit.D4Char.gtEval_duality
