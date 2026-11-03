import VOA.Huang.GenusTwoPointSepInsertion
import VOA.Huang.GenusTwoPointSepHuangU
import VOA.Huang.GenusOneSquareModes

/-!
# Square-bracket insertion into both slots of actual two-point mode traces

These are finite coefficient identities. Both normal-order orientations are
retained. No elliptic-kernel collection or equality between one mode trace
and the full geometrically modified two-point series is presumed.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module GenusOne
open scoped BigOperators
universe u
variable {V E₁ E₂ M K : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E₁] [Module ℂ E₁] [AddCommGroup E₂] [Module ℂ E₂]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W E₁} {A₂ : OrdVModule W E₂}
  {N : OrdVModule W M} {Q : OrdVModule W K}

/-- The right-slot iterate formula inside the actual traced weight space. -/
theorem trace_product_mode_iterate_right
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    {α₂ : ℂ} (w₁ : E₁) {w₂ : E₂} (h₂ : w₂ ∈ A₂.weight α₂)
    (a : V) (ell : ℤ) (n₁ n₂ e : ℂ) :
    ∃ I : ℕ, productModeTrace Y₁ Y₂ w₁ (mode (A₂.YM a) ell w₂) n₁ n₂ e =
      ∑ i ∈ Finset.range I, (negOnePow i * cbz ell i) *
        (gradedTraceOp N
            ((Y₁.val n₁ w₁).comp ((mode (Q.YM a) (ell - i)).comp
              (Y₂.val (n₂ + i) w₂))) e -
          negOnePow ell * gradedTraceOp N
            ((Y₁.val n₁ w₁).comp ((Y₂.val (ell + n₂ - i) w₂).comp
              (mode (N.YM a) i))) e) := by
  obtain ⟨I₀, hI₀⟩ := rectangular_eventually_zero_on_weight Y₂ h₂
    (e + W.centralCharge / 24) n₂
  obtain ⟨I₁, hI₁⟩ := mode_eventually_zero_on_weight N a (e + W.centralCharge / 24)
  let I := (max I₀ I₁).toNat
  let T : ℕ → Module.End ℂ M := fun i =>
    (negOnePow i * cbz ell i) •
      ((Y₁.val n₁ w₁).comp ((mode (Q.YM a) (ell - i)).comp (Y₂.val (n₂ + i) w₂)) -
        negOnePow ell • (Y₁.val n₁ w₁).comp
          ((Y₂.val (ell + n₂ - i) w₂).comp (mode (N.YM a) i)))
  have he : gradedTraceOp N
      ((Y₁.val n₁ w₁).comp (Y₂.val n₂ (mode (A₂.YM a) ell w₂))) e =
        gradedTraceOp N (∑ i ∈ Finset.range I, T i) e := by
    apply gradedTraceOp_congr_on_weight
    intro x hx
    have h := HuangODEModes.iterate_range Y₂.property a w₂ x ell n₂ I
      (fun i hi => ⟨hI₀ i (by dsimp [I] at hi; omega) x hx,
        hI₁ i (by dsimp [I] at hi; omega) x hx⟩)
    change Y₁.val n₁ w₁ (Y₂.val n₂ (mode (A₂.YM a) ell w₂) x) = _
    rw [h, map_sum]
    simp only [T, map_smul, map_sub, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.sub_apply]
  refine ⟨I, ?_⟩
  change gradedTraceOp N _ e = _
  rw [he, ← gradedTraceAt_apply, map_sum]
  simp only [T, map_smul, map_sub, gradedTraceAt_apply, smul_eq_mul]

/-- Zhu's coefficient transform uses a finite interval at any fixed insertion. -/
theorem sqAct_eq_range (A : OrdVModule W E₁) (a : V) (k : ℕ) (m : ℤ) (w : E₁)
    (J : ℤ) (hJ : ∀ i : ℤ, J ≤ i → mode (A.YM a) i w = 0) :
    sqAct A a k m w =
      ∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i • mode (A.YM a) i w := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support, Finset.mem_coe, Finset.mem_Ico] at *
  constructor
  · by_contra hn
    exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
  · by_contra hn
    exact hi (by rw [hJ i (by omega), smul_zero])

/-- The exact square-bracket transform in the first slot of the actual trace. -/
theorem trace_product_sqAct_left
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    (a : V) (k : ℕ) (m : ℤ) (w₁ : E₁) (w₂ : E₂) (n₁ n₂ e : ℂ)
    (J : ℤ) (hJ : ∀ i : ℤ, J ≤ i → mode (A₁.YM a) i w₁ = 0) :
    productModeTrace Y₁ Y₂ (sqAct A₁ a k m w₁) w₂ n₁ n₂ e =
      ∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i *
        productModeTrace Y₁ Y₂ (mode (A₁.YM a) i w₁) w₂ n₁ n₂ e := by
  rw [sqAct_eq_range A₁ a k m w₁ J hJ]
  have hc : (∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i •
      Y₁.val n₁ (mode (A₁.YM a) i w₁)).comp (Y₂.val n₂ w₂) =
      ∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i •
        (Y₁.val n₁ (mode (A₁.YM a) i w₁)).comp (Y₂.val n₂ w₂) := by
    ext x
    simp
  simp only [productModeTrace, map_sum, map_smul, hc,
    ← gradedTraceAt_apply, smul_eq_mul]

/-- The same finite transform, with the orientation of the product unchanged. -/
theorem trace_product_sqAct_right
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    (a : V) (k : ℕ) (m : ℤ) (w₁ : E₁) (w₂ : E₂) (n₁ n₂ e : ℂ)
    (J : ℤ) (hJ : ∀ i : ℤ, J ≤ i → mode (A₂.YM a) i w₂ = 0) :
    productModeTrace Y₁ Y₂ w₁ (sqAct A₂ a k m w₂) n₁ n₂ e =
      ∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i *
        productModeTrace Y₁ Y₂ w₁ (mode (A₂.YM a) i w₂) n₁ n₂ e := by
  rw [sqAct_eq_range A₂ a k m w₂ J hJ]
  have hc : (Y₁.val n₁ w₁).comp (∑ i ∈ Finset.Ico m J,
      sqBracketCoeffZ k m i • Y₂.val n₂ (mode (A₂.YM a) i w₂)) =
      ∑ i ∈ Finset.Ico m J, sqBracketCoeffZ k m i •
        (Y₁.val n₁ w₁).comp (Y₂.val n₂ (mode (A₂.YM a) i w₂)) := by
    ext x
    simp
  simp only [productModeTrace, map_sum, map_smul, hc,
    ← gradedTraceAt_apply, smul_eq_mul]

/-- Square-bracket normal ordering, explicitly including m=-2.
Each inner cutoff is proved by the Jacobi identity on the traced weight space. -/
theorem trace_product_sqAct_iterate_left
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    {α₁ α₂ : ℂ} {w₁ : E₁} {w₂ : E₂}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (a : V) (k : ℕ) (m : ℤ) (n₁ n₂ e : ℂ) :
    ∃ (J : ℤ) (I : ℤ → ℕ),
      (∀ i : ℤ, J ≤ i → mode (A₁.YM a) i w₁ = 0) ∧
      productModeTrace Y₁ Y₂ (sqAct A₁ a k m w₁) w₂ n₁ n₂ e =
        ∑ ell ∈ Finset.Ico m J, sqBracketCoeffZ k m ell *
          ∑ i ∈ Finset.range (I ell), (negOnePow i * cbz ell i) *
            (gradedTraceOp N
                (mode (N.YM a) (ell - i) *
                  ((Y₁.val (n₁ + i) w₁).comp (Y₂.val n₂ w₂))) e -
              negOnePow ell * gradedTraceOp N
                ((Y₁.val (ell + n₁ - i) w₁).comp
                  ((mode (Q.YM a) i).comp (Y₂.val n₂ w₂))) e) := by
  obtain ⟨J, hJ⟩ := A₁.truncation a w₁
  choose I hI using fun ell => trace_product_mode_iterate Y₁ Y₂ h₁ h₂ a ell n₁ n₂ e
  refine ⟨J, I, hJ, ?_⟩
  rw [trace_product_sqAct_left Y₁ Y₂ a k m w₁ w₂ n₁ n₂ e J hJ]
  simp only [hI]

/-- Right-slot square-bracket normal ordering, without dropping its second term. -/
theorem trace_product_sqAct_iterate_right
    (Y₁ : IntertwiningOperator A₁ Q N) (Y₂ : IntertwiningOperator A₂ N Q)
    {α₂ : ℂ} (w₁ : E₁) {w₂ : E₂} (h₂ : w₂ ∈ A₂.weight α₂)
    (a : V) (k : ℕ) (m : ℤ) (n₁ n₂ e : ℂ) :
    ∃ (J : ℤ) (I : ℤ → ℕ),
      (∀ i : ℤ, J ≤ i → mode (A₂.YM a) i w₂ = 0) ∧
      productModeTrace Y₁ Y₂ w₁ (sqAct A₂ a k m w₂) n₁ n₂ e =
        ∑ ell ∈ Finset.Ico m J, sqBracketCoeffZ k m ell *
          ∑ i ∈ Finset.range (I ell), (negOnePow i * cbz ell i) *
            (gradedTraceOp N
                ((Y₁.val n₁ w₁).comp ((mode (Q.YM a) (ell - i)).comp
                  (Y₂.val (n₂ + i) w₂))) e -
              negOnePow ell * gradedTraceOp N
                ((Y₁.val n₁ w₁).comp ((Y₂.val (ell + n₂ - i) w₂).comp
                  (mode (N.YM a) i))) e) := by
  obtain ⟨J, hJ⟩ := A₂.truncation a w₂
  choose I hI using fun ell => trace_product_mode_iterate_right Y₁ Y₂ w₁ h₂ a ell n₁ n₂ e
  refine ⟨J, I, hJ, ?_⟩
  rw [trace_product_sqAct_right Y₁ Y₂ a k m w₁ w₂ n₁ n₂ e J hJ]
  simp only [hI]

end VOA.Huang.GenusTwoPoint.Separate
