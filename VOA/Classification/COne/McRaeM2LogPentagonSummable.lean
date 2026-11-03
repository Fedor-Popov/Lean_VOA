import VOA.Classification.COne.McRaeM2LogPentagonSkew

/-! Joint absolute convergence of all five literal logarithmic pentagon
expansions on the common chart `0<r<s, r+s<1`, for every linear functional,
and the resulting unconditional equality of the two pentagon paths after
completed five-point evaluation. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat VOA.LogSkew
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The norm of a ratio of exponentials of real logarithms. -/
theorem norm_exp_log_sub_log {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    ‖Complex.exp (Complex.log (x : ℂ)-Complex.log (y : ℂ))‖=x/y := by
  rw [Complex.exp_sub, norm_div, norm_exp_log hx, norm_exp_log hy]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- Absolute convergence of the literal left vertex `((N ⊠ P) ⊠ Q) ⊠ R`. -/
theorem fivePointTerm_left_summable_norm (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R .left a b c d β x y z w r s f p.1 p.2‖) := by
  obtain ⟨J,hJ⟩ := fivePointTerm_left_skew hC2 N P Q R a b c d β x y z w r s f
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  have hnt : ‖Complex.exp (Complex.log (s : ℂ)-0)‖=s := by rw [sub_zero]; exact norm_exp_log hs
  have hnu : ‖Complex.exp (Complex.log (r : ℂ)-Complex.log (s : ℂ))‖=r/s :=
    norm_exp_log_sub_log hr hs
  have ht : ‖Complex.exp (Complex.log (s : ℂ)-0)‖+
      ‖Complex.exp (Complex.log (s : ℂ)-0)‖*‖Complex.exp (Complex.log (r : ℂ)-Complex.log (s : ℂ))‖<1 := by
    rw [hnt,hnu,mul_div_cancel₀ _ hs.ne']
    linarith [hD.2.2]
  have hu : ‖Complex.exp (Complex.log (r : ℂ)-Complex.log (s : ℂ))‖<1 := by
    rw [hnu, div_lt_one hs]
    exact hD.2.1
  apply fivePoint_summable_norm_of_rows
  intro h h'
  refine summable_norm_finite_sum_rows
    (F := fun p : ℕ × ℕ => fivePointTerm hC2 N P Q R .left a b c d β x y z w r s f
      (h+p.1) (h'+p.2)) J
    (fun j p => (omegaPhase 0 ((h'+p.2)+d-β-1))⁻¹*sc j)
    (fun j p => midPointProfile (fivePointObject hC2 N P Q R .left).act R.act Q.act N.act P.act
            (tensorObject hC2 N P).act (tensorObject hC2 (tensorObject hC2 N P) Q).act
            (rootSkewIntertwiner (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
              (fivePointObject hC2 N P Q R .left).act
              (tensorIntertwiner hC2 (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
                (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration R.finiteGeneration))
            (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
              (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration)
            (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
            0 (Complex.log s) (Complex.log r) d c a b (β-j) (h+p.1) (h'+p.2) w z x y
            (f ∘ₗ Lm1 (fivePointObject hC2 N P Q R .left).act.toWeakModule^j))
    (fun j => ‖(omegaPhase 0 (h'+d-β-1))⁻¹‖*‖sc j‖) ?_ ?_ ?_
  · intro j p
    simp only []
    rw [norm_mul]
    have he : h'+(p.2 : ℂ)+d-β-1=(h'+d-β-1)+(p.2 : ℂ) := by ring
    rw [he, rootSkew_phase_norm_add_nat]
  · intro j
    exact midPointProfile_row_summable _ _ _ _ _ _ _ hC2
      (fivePointObject hC2 N P Q R .left).finiteGeneration
      R.finiteGeneration Q.finiteGeneration N.finiteGeneration P.finiteGeneration
      (tensorObject hC2 N P).finiteGeneration
      (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration _ _ _
      0 (Complex.log s) (Complex.log r) d c a b (β-j) w z x y _ h h' ht hu
  · intro p
    simp only []
    rw [hJ]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- Absolute convergence of the literal inner vertex `(N ⊠ (P ⊠ Q)) ⊠ R`. -/
theorem fivePointTerm_inner_summable_norm (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .inner →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f p.1 p.2‖) := by
  obtain ⟨J,hJ⟩ := fivePointTerm_inner_skew hC2 N P Q R a b c d β x y z w r s f
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  have hc : ((s+r : ℝ) : ℂ)=(s : ℂ)+(r : ℂ) := by push_cast; ring
  have ht : ‖Complex.exp (Complex.log ((s : ℂ)+(r : ℂ))-0)‖<1 := by
    rw [sub_zero, ← hc, norm_exp_log (by linarith)]
    linarith [hD.2.2]
  have hu : ‖Complex.exp (Complex.log (s : ℂ)-Complex.log ((s : ℂ)+(r : ℂ)))‖<1 := by
    rw [← hc]
    exact norm_exp_log_sub_log_lt_one hs (by linarith)
  apply fivePoint_summable_norm_of_rows
  intro h h'
  refine summable_norm_finite_sum_rows
    (F := fun p : ℕ × ℕ => fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f
      (h+p.1) (h'+p.2)) J
    (fun j p => (omegaPhase 0 ((h'+p.2)+d-β-1))⁻¹*sc j)
    (fun j p => productPointProfile (fivePointObject hC2 N P Q R .inner).act R.act N.act P.act Q.act
            (tensorObject hC2 P Q).act (tensorObject hC2 N (tensorObject hC2 P Q)).act
            (rootSkewIntertwiner (tensorObject hC2 N (tensorObject hC2 P Q)).act R.act
              (fivePointObject hC2 N P Q R .inner).act
              (tensorIntertwiner hC2 (tensorObject hC2 N (tensorObject hC2 P Q)).act R.act
                (tensorObject hC2 N (tensorObject hC2 P Q)).finiteGeneration R.finiteGeneration))
            (tensorIntertwiner hC2 N.act (tensorObject hC2 P Q).act
              N.finiteGeneration (tensorObject hC2 P Q).finiteGeneration)
            (tensorIntertwiner hC2 P.act Q.act P.finiteGeneration Q.finiteGeneration)
            0 (Complex.log ((s : ℂ)+(r : ℂ))) (Complex.log s) d a b c (β-j) (h+p.1) (h'+p.2) w x y z
            (f ∘ₗ Lm1 (fivePointObject hC2 N P Q R .inner).act.toWeakModule^j))
    (fun j => ‖(omegaPhase 0 (h'+d-β-1))⁻¹‖*‖sc j‖) ?_ ?_ ?_
  · intro j p
    simp only []
    rw [norm_mul]
    have he : h'+(p.2 : ℂ)+d-β-1=(h'+d-β-1)+(p.2 : ℂ) := by ring
    rw [he, rootSkew_phase_norm_add_nat]
  · intro j
    exact productPointProfile_row_summable _ _ _ _ _ _ _ hC2
      (fivePointObject hC2 N P Q R .inner).finiteGeneration
      R.finiteGeneration N.finiteGeneration P.finiteGeneration Q.finiteGeneration
      (tensorObject hC2 P Q).finiteGeneration
      (tensorObject hC2 N (tensorObject hC2 P Q)).finiteGeneration _ _ _
      0 (Complex.log ((s : ℂ)+(r : ℂ))) (Complex.log s) d a b c (β-j) w x y z _ h h' ht hu
  · intro p
    simp only []
    rw [hJ]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- Every literal logarithmic pentagon expansion converges absolutely. -/
theorem fivePointTerm_summable_norm (N P Q R : LogModuleCat W) (tree : FiveTree)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2‖) := by
  cases tree with
  | left => exact fivePointTerm_left_summable_norm hC2 N P Q R a b c d β x y z w r s hD f
  | inner => exact fivePointTerm_inner_summable_norm hC2 N P Q R a b c d β x y z w r s hD f
  | middle => exact fivePointTerm_middle_summable_norm hC2 N P Q R a b c d β x y z w r s hD f
  | right => exact fivePointTerm_right_summable_norm hC2 N P Q R a b c d β x y z w r s hD f
  | pair => exact fivePointTerm_pair_summable_norm hC2 N P Q R a b c d β x y z w r s hD f

-- Actual fourfold categorical point profiles require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- The two actual pentagon paths agree after completed five-point
evaluation, for every functional and every point of the common chart. -/
theorem pentagon_evaluation (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ) :
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (tensorPentagonLong hC2 N P Q R).1)=
    fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (tensorPentagonShort hC2 N P Q R).1) :=
  pentagon_evaluation_of_summable hC2 N P Q R a b c d β x y z w r s hD f
    (fivePointTerm_summable_norm hC2 N P Q R .left a b c d β x y z w r s hD _).of_norm
    (fivePointTerm_summable_norm hC2 N P Q R .left a b c d β x y z w r s hD _).of_norm
    (fivePointTerm_summable_norm hC2 N P Q R .inner a b c d β x y z w r s hD _).of_norm
    (fivePointTerm_summable_norm hC2 N P Q R .middle a b c d β x y z w r s hD _).of_norm
    (fivePointTerm_summable_norm hC2 N P Q R .pair a b c d β x y z w r s hD _).of_norm
    (fivePointTerm_summable_norm hC2 N P Q R .right a b c d β x y z w r s hD _).of_norm

end VOA.Huang.LogAssocFivePoint
