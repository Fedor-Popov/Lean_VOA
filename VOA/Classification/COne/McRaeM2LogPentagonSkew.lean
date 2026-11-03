import VOA.Classification.COne.McRaeM2LogPentagonProfileRows
import VOA.Huang.LogAssocFivePointRootSkew

/-! Absolute convergence of the two iterate-rooted vertices of the logarithmic
pentagon, `((N ⊠ P) ⊠ Q) ⊠ R` and `(N ⊠ (P ⊠ Q)) ⊠ R`. The root coefficient at
the point `1` is reflected by the genuine per-log root skew-symmetry
(`exists_rootSkew_scalar_profiles`); this turns each term into a finite,
uniformly truncated sum of iterate-in-product (left) or product (inner)
profiles with the fourth input moved to the front, at the chart ratios
`s, r/s` (left) and `s+r, s/(s+r)` (inner). -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat VOA.LogSkew
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- Finite reflected sums of absolutely convergent rows with row-constant
coefficient norms are absolutely convergent. -/
theorem summable_norm_finite_sum_rows {F : ℕ × ℕ → ℂ} (J : ℕ) (c : ℕ → ℕ × ℕ → ℂ)
    (G : ℕ → ℕ × ℕ → ℂ) (C : ℕ → ℝ) (hc : ∀ j p,‖c j p‖=C j)
    (hG : ∀ j,Summable fun p => ‖G j p‖)
    (hF : ∀ p,F p=∑ j∈Finset.range J,c j p*G j p) :
    Summable fun p => ‖F p‖ := by
  have hs : Summable fun p => ∑ j∈Finset.range J,C j*‖G j p‖ :=
    summable_sum fun j _ => (hG j).mul_left (C j)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs
  rw [hF p]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_mul,hc]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- The left vertex term is a uniformly finite root-reflected sum of genuine
iterate-in-product profiles with the fourth input in front. -/
theorem fivePointTerm_left_skew (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) :
    ∃ J : ℕ,∀ γ δ : ℂ,
      fivePointTerm hC2 N P Q R .left a b c d β x y z w r s f γ δ=
        ∑ j∈Finset.range J,(omegaPhase 0 (δ+d-β-1))⁻¹*sc j*
          midPointProfile (fivePointObject hC2 N P Q R .left).act R.act Q.act N.act P.act
            (tensorObject hC2 N P).act (tensorObject hC2 (tensorObject hC2 N P) Q).act
            (rootSkewIntertwiner (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
              (fivePointObject hC2 N P Q R .left).act
              (tensorIntertwiner hC2 (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
                (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration R.finiteGeneration))
            (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
              (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration)
            (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
            0 (Complex.log s) (Complex.log r) d c a b (β-j) γ δ w z x y
            (f ∘ₗ Lm1 (fivePointObject hC2 N P Q R .left).act.toWeakModule^j) := by
  let T := tensorObject hC2 N P
  let L := tensorObject hC2 T Q
  let O := fivePointObject hC2 N P Q R .left
  let YLR := tensorIntertwiner hC2 L.act R.act L.finiteGeneration R.finiteGeneration
  obtain ⟨J,hJ⟩ := exists_rootSkew_scalar_profiles L.act R.act O.act YLR β
  refine ⟨J,fun γ δ => ?_⟩
  let v : L.act.weight δ := pointTensorBlock hC2 T Q (Complex.log s) γ c δ
    (pointTensor hC2 N P (Complex.log r) x y γ) z
  have h0 : fivePointTerm hC2 N P Q R .left a b c d β x y z w r s f γ δ=
      f (YLR.1 (δ+d-β-1) 0 v w) := by
    simp only [fivePointTerm]
    exact congrArg f (pointEvaluationBlock_zero_branch L.act R.act O.act YLR δ d β v w)
  rw [h0]
  refine (hJ δ d v w v.2 w.2 f 0).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [midPointProfile]
  rw [← pointTensor_eq_block hC2 N P (Complex.log r) a b]
  congr 1
  have he : d+δ-(β-(j : ℂ))-1=δ+d-β-1+(j : ℂ) := by ring
  rw [pointEvaluationBlock_zero_branch, he]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 6000000 in
/-- The inner vertex term is a uniformly finite root-reflected sum of genuine
product profiles with the fourth input in front. -/
theorem fivePointTerm_inner_skew (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R .inner →ₗ[ℂ] ℂ) :
    ∃ J : ℕ,∀ γ δ : ℂ,
      fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f γ δ=
        ∑ j∈Finset.range J,(omegaPhase 0 (δ+d-β-1))⁻¹*sc j*
          productPointProfile (fivePointObject hC2 N P Q R .inner).act R.act N.act P.act Q.act
            (tensorObject hC2 P Q).act (tensorObject hC2 N (tensorObject hC2 P Q)).act
            (rootSkewIntertwiner (tensorObject hC2 N (tensorObject hC2 P Q)).act R.act
              (fivePointObject hC2 N P Q R .inner).act
              (tensorIntertwiner hC2 (tensorObject hC2 N (tensorObject hC2 P Q)).act R.act
                (tensorObject hC2 N (tensorObject hC2 P Q)).finiteGeneration R.finiteGeneration))
            (tensorIntertwiner hC2 N.act (tensorObject hC2 P Q).act
              N.finiteGeneration (tensorObject hC2 P Q).finiteGeneration)
            (tensorIntertwiner hC2 P.act Q.act P.finiteGeneration Q.finiteGeneration)
            0 (Complex.log (s+r)) (Complex.log s) d a b c (β-j) γ δ w x y z
            (f ∘ₗ Lm1 (fivePointObject hC2 N P Q R .inner).act.toWeakModule^j) := by
  let S := tensorObject hC2 P Q
  let H := tensorObject hC2 N S
  let O := fivePointObject hC2 N P Q R .inner
  let YHR := tensorIntertwiner hC2 H.act R.act H.finiteGeneration R.finiteGeneration
  obtain ⟨J,hJ⟩ := exists_rootSkew_scalar_profiles H.act R.act O.act YHR β
  refine ⟨J,fun γ δ => ?_⟩
  let v : H.act.weight δ := pointTensorBlock hC2 N S (Complex.log (s+r)) a γ δ x
    (pointTensor hC2 P Q (Complex.log s) y z γ)
  have h0 : fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f γ δ=
      f (YHR.1 (δ+d-β-1) 0 v w) := by
    simp only [fivePointTerm]
    exact congrArg f (pointEvaluationBlock_zero_branch H.act R.act O.act YHR δ d β v w)
  rw [h0]
  refine (hJ δ d v w v.2 w.2 f 0).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [productPointProfile]
  rw [← pointTensor_eq_block hC2 P Q (Complex.log s) b c]
  congr 1
  have he : d+δ-(β-(j : ℂ))-1=δ+d-β-1+(j : ℂ) := by ring
  rw [pointEvaluationBlock_zero_branch, he]

end VOA.Huang.LogAssocFivePoint
