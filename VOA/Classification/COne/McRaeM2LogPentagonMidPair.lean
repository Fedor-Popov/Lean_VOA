import VOA.Classification.COne.McRaeM2LogPentagonRight

/-! Absolute convergence of the literal middle vertex `N ⊠ ((P ⊠ Q) ⊠ R)` and
pair vertex `(N ⊠ P) ⊠ (Q ⊠ R)` of the logarithmic pentagon. Each term is the
genuine iterate-in-product, respectively two-cluster, point profile of the
canonical tensor intertwiners; the natural rows are the proved full-log arrays
at the chart ratios `1/(1+s+r), s` (middle) and, in the blow-up indexing,
`1/(1+s), r` (pair). -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded
open scoped BigOperators
universe u

section Generic
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
    [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
    [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
    [AddCommGroup M₆] [Module ℂ M₆]
    (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (N₆ : LogVModule W M₆)

/-- The full-log middle array is the literal log polynomial at shifted modes. -/
theorem fullLogMidProductCoefficient_eq
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (f : M₀ →ₗ[ℂ] ℂ) (A B C e₁ e₂ e₃ : ℂ) (m n : ℕ) :
    fullLogMidProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃ (x := x) (y := y) (z := z) (w := w)
      f A B C e₁ e₂ e₃ m n=
    productLogPolynomial Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w (A+m) (B-m+n) (C-n) e₁ e₂ e₃ :=
  rfl

/-- The full-log pair array is the literal log polynomial at shifted modes. -/
theorem fullLogPairCoefficient_eq
    (P : LogIntertwiningOperator N₅.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (ZT : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule N₆.toWeakModule)
    (XY : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (f : M₀ →ₗ[ℂ] ℂ) (A B C e₁ e₂ e₃ : ℂ) (m n : ℕ) :
    fullLogPairCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆ P ZT XY (x := x) (y := y) (z := z) (w := w)
      f A B C e₁ e₂ e₃ m n=
    pairLogPolynomial P.1 ZT.1 XY.1 f x y z w (A+m) (B-m+n) (C-n) e₁ e₂ e₃ :=
  rfl

end Generic

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The reciprocal exponential of a positive logarithm. -/
theorem norm_exp_neg_log {y : ℝ} (hy : 0<y) : ‖Complex.exp (-Complex.log (y : ℂ))‖=y⁻¹ := by
  rw [Complex.exp_neg, norm_inv, norm_exp_log hy]

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- The middle vertex term is literally the iterate-in-product point profile. -/
theorem fivePointTerm_middle_eq (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R .middle →ₗ[ℂ] ℂ) (γ δ : ℂ) :
    fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s f γ δ=
      midPointProfile
        (tensorObject hC2 N (tensorObject hC2 (tensorObject hC2 P Q) R)).act N.act R.act P.act Q.act
        (tensorObject hC2 P Q).act (tensorObject hC2 (tensorObject hC2 P Q) R).act
        (tensorIntertwiner hC2 N.act (tensorObject hC2 (tensorObject hC2 P Q) R).act
          N.finiteGeneration (tensorObject hC2 (tensorObject hC2 P Q) R).finiteGeneration)
        (tensorIntertwiner hC2 (tensorObject hC2 P Q).act R.act
          (tensorObject hC2 P Q).finiteGeneration R.finiteGeneration)
        (tensorIntertwiner hC2 P.act Q.act P.finiteGeneration Q.finiteGeneration)
        (Complex.log (1+s+r)) 0 (Complex.log s) a d b c β γ δ x w y z f := by
  simp only [fivePointTerm]
  rw [pointTensor_eq_block hC2 P Q (Complex.log s) b c]
  rfl

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- The pair vertex term is literally the two-cluster point profile. -/
theorem fivePointTerm_pair_eq (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
    (f : fivePointObject hC2 N P Q R .pair →ₗ[ℂ] ℂ) (γ δ : ℂ) :
    fivePointTerm hC2 N P Q R .pair a b c d β x y z w r s f γ δ=
      pairPointProfile
        (tensorObject hC2 (tensorObject hC2 N P) (tensorObject hC2 Q R)).act R.act Q.act N.act P.act
        (tensorObject hC2 N P).act (tensorObject hC2 Q R).act
        (tensorIntertwiner hC2 (tensorObject hC2 N P).act (tensorObject hC2 Q R).act
          (tensorObject hC2 N P).finiteGeneration (tensorObject hC2 Q R).finiteGeneration)
        (tensorIntertwiner hC2 Q.act R.act Q.finiteGeneration R.finiteGeneration)
        (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
        (Complex.log (1+s)) 0 (Complex.log r) d c a b β γ δ w z x y f := by
  simp only [fivePointTerm]
  rw [pointTensor_eq_block hC2 N P (Complex.log r) a b,
    pointTensor_eq_block hC2 Q R 0 c d]
  rfl

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- Absolute convergence of the literal middle vertex of the logarithmic pentagon. -/
theorem fivePointTerm_middle_summable_norm (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .middle →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s f p.1 p.2‖) := by
  apply fivePoint_summable_norm_of_rows
  intro h h'
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  set e₁ : ℂ := Complex.log (1+s+r) with he₁
  set e₃ : ℂ := Complex.log s with he₃
  have hc₁ : ((1+s+r : ℝ) : ℂ)=1+s+r := by push_cast; ring
  have hnt : ‖Complex.exp (-e₁)‖=(1+s+r)⁻¹ := by
    have := norm_exp_neg_log (y := 1+s+r) (by linarith)
    rwa [hc₁] at this
  have hnu : ‖Complex.exp e₃‖=s := norm_exp_log hs
  have ht : ‖Complex.exp (-e₁)‖+‖Complex.exp (-e₁)‖*‖Complex.exp e₃‖<1 := by
    rw [hnt,hnu]
    have hpos : 0<1+s+r := by linarith
    rw [← mul_one_add, inv_mul_lt_iff₀ hpos]
    linarith
  have hu : ‖Complex.exp e₃‖<1 := by rw [hnu]; linarith [hD.2.2]
  have hG := summable_fullLog_mid_double
    (tensorObject hC2 N (tensorObject hC2 (tensorObject hC2 P Q) R)).act N.act R.act P.act Q.act
    (tensorObject hC2 P Q).act (tensorObject hC2 (tensorObject hC2 P Q) R).act hC2
    (tensorObject hC2 N (tensorObject hC2 (tensorObject hC2 P Q) R)).finiteGeneration
    N.finiteGeneration R.finiteGeneration P.finiteGeneration Q.finiteGeneration
    (tensorObject hC2 P Q).finiteGeneration
    (tensorObject hC2 (tensorObject hC2 P Q) R).finiteGeneration
    (tensorIntertwiner hC2 N.act (tensorObject hC2 (tensorObject hC2 P Q) R).act
      N.finiteGeneration (tensorObject hC2 (tensorObject hC2 P Q) R).finiteGeneration)
    (tensorIntertwiner hC2 (tensorObject hC2 P Q).act R.act
      (tensorObject hC2 P Q).finiteGeneration R.finiteGeneration)
    (tensorIntertwiner hC2 P.act Q.act P.finiteGeneration Q.finiteGeneration)
    x.2 w.2 y.2 z.2 f (a+h'-β-1) (d+h-h'-1) (b+c-h-1) e₁ 0 e₃ ht hu
  refine summable_row_of_reindex
    (F := fun γ δ => fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s f γ δ) h h'
    (Complex.exp (e₁*(β-a-h'))*Complex.exp (e₃*(h-b-c))) Prod.swap Prod.swap_injective hG ?_
  intro p
  simp only []
  rw [fivePointTerm_middle_eq, midPointProfile_eq_polynomial _ _ _ _ _ _ _
    (tensorObject hC2 N (tensorObject hC2 (tensorObject hC2 P Q) R)).finiteGeneration
    N.finiteGeneration R.finiteGeneration P.finiteGeneration Q.finiteGeneration
    (tensorObject hC2 P Q).finiteGeneration
    (tensorObject hC2 (tensorObject hC2 P Q) R).finiteGeneration,
    Prod.fst_swap, Prod.snd_swap, fullLogMidProductCoefficient_eq]
  have h1 : a+(h'+(p.2 : ℂ))-β-1=a+h'-β-1+(p.2 : ℂ) := by ring
  have h2 : d+(h+(p.1 : ℂ))-(h'+(p.2 : ℂ))-1=d+h-h'-1-(p.2 : ℂ)+(p.1 : ℂ) := by ring
  have h3 : b+c-(h+(p.1 : ℂ))-1=b+c-h-1-(p.1 : ℂ) := by ring
  rw [h1,h2,h3]
  have hexp : Complex.exp (e₁*(β-a-(h'+(p.2 : ℂ))))*
      Complex.exp (0*((h'+(p.2 : ℂ))-(h+(p.1 : ℂ))-d))*
      Complex.exp (e₃*((h+(p.1 : ℂ))-b-c))=
      (Complex.exp (e₁*(β-a-h'))*Complex.exp (e₃*(h-b-c)))*
        (Complex.exp (-e₁)^p.2*Complex.exp e₃^p.1) := by
    rw [← exp_mul_nat, ← exp_mul_nat]
    simp only [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- Absolute convergence of the literal pair vertex of the logarithmic pentagon. -/
theorem fivePointTerm_pair_summable_norm (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .pair →ₗ[ℂ] ℂ) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R .pair a b c d β x y z w r s f p.1 p.2‖) := by
  apply fivePoint_summable_norm_of_rows
  intro h h'
  have hr : 0<r := hD.1
  have hs : 0<s := hD.1.trans hD.2.1
  set e₁ : ℂ := Complex.log (1+s) with he₁
  set e₃ : ℂ := Complex.log r with he₃
  have hc₁ : ((1+s : ℝ) : ℂ)=1+s := by push_cast; ring
  have hnt : ‖Complex.exp (-e₁)‖=(1+s)⁻¹ := by
    have := norm_exp_neg_log (y := 1+s) (by linarith)
    rwa [hc₁] at this
  have hnu : ‖Complex.exp e₃‖=r := norm_exp_log hr
  have ht : ‖Complex.exp (-e₁)‖+‖Complex.exp (-e₁)‖*‖Complex.exp e₃‖<1 := by
    rw [hnt,hnu]
    have hpos : 0<1+s := by linarith
    rw [← mul_one_add, inv_mul_lt_iff₀ hpos]
    linarith [hD.2.1]
  have hu : ‖Complex.exp e₃‖<1 := by rw [hnu]; linarith [hD.2.2, hD.2.1]
  have hG := summable_fullLog_pair_double
    (tensorObject hC2 (tensorObject hC2 N P) (tensorObject hC2 Q R)).act R.act Q.act N.act P.act
    (tensorObject hC2 N P).act (tensorObject hC2 Q R).act hC2
    (tensorObject hC2 (tensorObject hC2 N P) (tensorObject hC2 Q R)).finiteGeneration
    R.finiteGeneration Q.finiteGeneration N.finiteGeneration P.finiteGeneration
    (tensorObject hC2 N P).finiteGeneration (tensorObject hC2 Q R).finiteGeneration
    (tensorIntertwiner hC2 (tensorObject hC2 N P).act (tensorObject hC2 Q R).act
      (tensorObject hC2 N P).finiteGeneration (tensorObject hC2 Q R).finiteGeneration)
    (tensorIntertwiner hC2 Q.act R.act Q.finiteGeneration R.finiteGeneration)
    (tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration)
    w.2 z.2 x.2 y.2 f (h+h'-β-1) (c+d-h'-1) (a+b-h-1) e₁ 0 e₃ ht hu
  have hσ : Function.Injective (fun p : ℕ × ℕ => (p.1+p.2,p.1)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    apply Prod.ext <;> omega
  refine summable_row_of_reindex
    (F := fun γ δ => fivePointTerm hC2 N P Q R .pair a b c d β x y z w r s f γ δ) h h'
    (Complex.exp (e₁*(β-h-h'))*Complex.exp (e₃*(h-a-b))) _ hσ hG ?_
  intro p
  simp only []
  rw [fivePointTerm_pair_eq, pairPointProfile_eq_polynomial _ _ _ _ _ _ _
    (tensorObject hC2 (tensorObject hC2 N P) (tensorObject hC2 Q R)).finiteGeneration
    R.finiteGeneration Q.finiteGeneration N.finiteGeneration P.finiteGeneration
    (tensorObject hC2 N P).finiteGeneration (tensorObject hC2 Q R).finiteGeneration,
    fullLogPairCoefficient_eq]
  have h1 : (h+(p.1 : ℂ))+(h'+(p.2 : ℂ))-β-1=h+h'-β-1+((p.1+p.2 : ℕ) : ℂ) := by push_cast; ring
  have h2 : c+d-(h'+(p.2 : ℂ))-1=c+d-h'-1-((p.1+p.2 : ℕ) : ℂ)+(p.1 : ℂ) := by push_cast; ring
  have h3 : a+b-(h+(p.1 : ℂ))-1=a+b-h-1-(p.1 : ℂ) := by ring
  rw [h1,h2,h3]
  have hexp : Complex.exp (e₁*(β-(h+(p.1 : ℂ))-(h'+(p.2 : ℂ))))*
      Complex.exp (0*((h'+(p.2 : ℂ))-c-d))*
      Complex.exp (e₃*((h+(p.1 : ℂ))-a-b))=
      (Complex.exp (e₁*(β-h-h'))*Complex.exp (e₃*(h-a-b)))*
        (Complex.exp (-e₁)^(p.1+p.2)*Complex.exp e₃^p.1) := by
    rw [← exp_mul_nat, ← exp_mul_nat]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

end VOA.Huang.LogAssocFivePoint
