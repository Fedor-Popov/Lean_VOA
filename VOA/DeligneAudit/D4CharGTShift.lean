import VOA.DeligneAudit.D4CharGT

/-! Central shift, including negative weights, directly from GT branching. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

theorem sum_gtRows_shift {R : Type*} [AddCommMonoid R] {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (c : ℤ) (f : (Fin N → ℤ) → R) :
    (∑ μ ∈ gtRows (fun i => lam i + c), f μ) =
      ∑ μ ∈ gtRows lam, f (fun i => μ i + c) := by
  classical
  refine Finset.sum_bij' (fun μ _ i => μ i - c) (fun μ _ i => μ i + c)
    ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    have hm := (mem_gtRows _ _).mp hμ
    apply (mem_gtRows _ _).mpr
    intro i
    have hi := hm i
    dsimp only at hi ⊢
    constructor <;> omega
  · intro μ hμ
    exact (gtRows_shift lam μ c).mpr hμ
  · intro μ _
    funext i
    exact sub_add_cancel _ _
  · intro μ _
    funext i
    exact add_sub_cancel_right _ _
  · intro μ _
    congr 1
    funext i
    exact (sub_add_cancel _ _).symm

/-- Lemma 3.2(c), uniformly in the rank and the integer central shift. -/
theorem gtEval_central_shift {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ)
    (N : ℕ) (lam : Fin N → ℤ) (c : ℤ) :
    gtEval q u N (fun i => lam i + c) =
      (∏ i : Fin N, (((u i) ^ c : Rˣ) : R)) * gtEval q u N lam := by
  induction N with
  | zero => simp [gtEval]
  | succ N ih =>
      rw [gtEval, sum_gtRows_shift]
      simp only [gtPsi_shift, gt_degree_shift, ih, zpow_add, Units.val_mul]
      rw [Fin.prod_univ_castSucc, gtEval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      simp only [Fin.val_castSucc, Fin.val_last]
      ring

theorem gtEval_zero_weight {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ) (N : ℕ) :
    gtEval q u N (fun _ => 0) = 1 := by
  induction N with
  | zero => rfl
  | succ N ih => simp [gtEval, gtRows, gtPsi, ih]

/-- Determinant weights, valid for all integer c. -/
theorem gtEval_constant_weight {R : Type*} [CommRing R] (q : R) (u : ℕ → Rˣ)
    (N : ℕ) (c : ℤ) :
    gtEval q u N (fun _ => c) = ∏ i : Fin N, (((u i) ^ c : Rˣ) : R) := by
  simpa only [zero_add, gtEval_zero_weight, mul_one] using
    gtEval_central_shift q u N (fun _ => 0) c

/-- Lemma 3.2(c) for the Laurent polynomials themselves. -/
theorem gtP_central_shift (N : ℕ) (lam : Fin N → ℤ) (c : ℤ) :
    gtP N (fun i => lam i + c) =
      (∏ i : Fin N, (((gtVariable i) ^ c : GTLaurentˣ) : GTLaurent)) * gtP N lam :=
  gtEval_central_shift _ _ N lam c

theorem gtP_zero_weight (N : ℕ) : gtP N (fun _ => 0) = 1 :=
  gtEval_zero_weight _ _ N

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sum_gtRows_shift
#print axioms VOA.DeligneAudit.D4Char.gtEval_central_shift
#print axioms VOA.DeligneAudit.D4Char.gtEval_zero_weight
#print axioms VOA.DeligneAudit.D4Char.gtEval_constant_weight
#print axioms VOA.DeligneAudit.D4Char.gtP_central_shift
#print axioms VOA.DeligneAudit.D4Char.gtP_zero_weight
