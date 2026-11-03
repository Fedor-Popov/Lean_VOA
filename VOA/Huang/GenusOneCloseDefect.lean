import VOA.Huang.GenusOneCuspSupport

/-!
# Formal insertion blocks with an omega defect

The logarithmic pair of Miyamoto, math/0010180, Proposition 4.14, in its
smallest form: if `F(τ+1) = λF(τ) + G(τ)` with `G(τ+1) = λG(τ)`, then
`H = F − (τ/λ)G` is `λ`-periodic and satisfies the first two block relations,
while the omega relation acquires the inhomogeneous term `(2πiλ)⁻¹G`.

This file proves the formal half: such a defect pair, supported at a common
exponent `b`, has `G = 0`, and `H` is a finite sum of intertwiner traces. It
uses the quotient bimodule and the Li lifting input as explicit hypotheses.
No analytic expansion is asserted here.
-/
namespace VOA.Huang.GenusOne.Close
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-! ## Linearity of the convolution on a common base -/

theorem qConv_add_of_mem (f : ℕ → ℂ) {b : ℂ} {g₁ g₂ : FormalQSeries}
    (h₁ : g₁ ∈ QSeriesAt b) (h₂ : g₂ ∈ QSeriesAt b) :
    qConv f (g₁ + g₂) = qConv f g₁ + qConv f g₂ := by
  have h₁₂ := (QSeriesAt b).add_mem h₁ h₂
  apply QSeriesAt.ext (qConv_mem_QSeriesAt f h₁₂)
    ((QSeriesAt b).add_mem (qConv_mem_QSeriesAt f h₁) (qConv_mem_QSeriesAt f h₂))
  intro m
  rw [Pi.add_apply, qConv_apply_of_support f _ b (QSeriesAt.support_neg h₁₂) m,
    qConv_apply_of_support f _ b (QSeriesAt.support_neg h₁) m,
    qConv_apply_of_support f _ b (QSeriesAt.support_neg h₂) m, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pi.add_apply, mul_add]

theorem qDeriv_add (χ ψ : FormalQSeries) : qDeriv (χ + ψ) = qDeriv χ + qDeriv ψ := by
  funext e
  simp only [qDeriv, Pi.add_apply, mul_add]

theorem qDeriv_smul (c : ℂ) (χ : FormalQSeries) : qDeriv (c • χ) = c • qDeriv χ := by
  funext e
  simp only [qDeriv, Pi.smul_apply, smul_eq_mul]
  ring

theorem tail_finite (S : M →ₗ[ℂ] FormalQSeries) (y : ℕ → M)
    (hy : ∃ K : ℕ, ∀ m, K ≤ m → y m = 0) (c : ℕ → FormalQSeries → FormalQSeries)
    (hc : ∀ m, c m 0 = 0) : (Function.support fun m => c m (S (y m))).Finite := by
  obtain ⟨K, hK⟩ := hy
  refine (Set.finite_Iio K).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  exact hm (by rw [hK m (by omega), map_zero, hc])

/-! ## Defect blocks -/

/-- The three formal block relations, with an additional term `E` in the omega
relation. `E = 0` is exactly `IsInsertionFormalBlock`. -/
structure IsDefectBlock (A : OrdVModule W M) (S E : M →ₗ[ℂ] FormalQSeries) : Prop where
  vanish : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ W.grading (k : ℤ), ∀ w,
    S (sqAct A a k 0 w) = 0
  negTwo : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ W.grading (k : ℤ), ∀ w,
    S (sqAct A a k (-2) w) + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ) •
      qConv (zhuG (m + 1)) (S (sqAct A a k (2 * (m + 1) - 2 : ℤ) w)) = 0
  omega : ∀ w, S (sqL A (-2) w) = qDeriv (S w) +
    ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (sqL A (2 * (m + 1) - 2 : ℤ) w)) + E w

theorem isDefectBlock_zero_iff {S : M →ₗ[ℂ] FormalQSeries} :
    IsDefectBlock A S 0 ↔ IsInsertionFormalBlock A S := by
  constructor
  · intro h
    exact ⟨h.vanish, h.negTwo, fun w => by simpa using h.omega w⟩
  · intro h
    exact ⟨h.vanish, h.negTwo, fun w => by simpa using h.omega w⟩

theorem IsDefectBlock.add {S T E F : M →ₗ[ℂ] FormalQSeries} {b : ℂ}
    (hSb : ∀ w, S w ∈ QSeriesAt b) (hTb : ∀ w, T w ∈ QSeriesAt b)
    (hS : IsDefectBlock A S E) (hT : IsDefectBlock A T F) :
    IsDefectBlock A (S + T) (E + F) where
  vanish k hk a ha w := by
    simp only [LinearMap.add_apply, hS.vanish k hk a ha w, hT.vanish k hk a ha w, add_zero]
  negTwo k hk a ha w := by
    have hy := sqAct_tail_eventually_zero A a k w
    let c : ℕ → FormalQSeries → FormalQSeries := fun m χ =>
      ((2 * (m + 1) - 1 : ℕ) : ℂ) • qConv (zhuG (m + 1)) χ
    have hc : ∀ m, c m 0 = 0 := fun m => by simp [c]
    have hfS := tail_finite S _ hy c hc
    have hfT := tail_finite T _ hy c hc
    have h1 := hS.negTwo k hk a ha w
    have h2 := hT.negTwo k hk a ha w
    simp only [LinearMap.add_apply]
    rw [finsum_congr (fun m => by rw [qConv_add_of_mem _ (hSb _) (hTb _), smul_add]),
      finsum_add_distrib hfS hfT]
    have : S (sqAct A a k (-2) w) + T (sqAct A a k (-2) w) +
        ((∑ᶠ m : ℕ, c m (S (sqAct A a k (2 * (m + 1) - 2 : ℤ) w))) +
          ∑ᶠ m : ℕ, c m (T (sqAct A a k (2 * (m + 1) - 2 : ℤ) w))) =
        (S (sqAct A a k (-2) w) + ∑ᶠ m : ℕ, c m (S (sqAct A a k (2 * (m + 1) - 2 : ℤ) w))) +
        (T (sqAct A a k (-2) w) + ∑ᶠ m : ℕ, c m (T (sqAct A a k (2 * (m + 1) - 2 : ℤ) w))) := by
      abel
    exact this.trans (by rw [h1, h2, add_zero])
  omega w := by
    have hy := sqL_tail_eventually_zero A w
    let c : ℕ → FormalQSeries → FormalQSeries := fun m χ => qConv (zhuG (m + 1)) χ
    have hc : ∀ m, c m 0 = 0 := fun m => by simp [c]
    have hfS := tail_finite S _ hy c hc
    have hfT := tail_finite T _ hy c hc
    have h1 := hS.omega w
    have h2 := hT.omega w
    simp only [LinearMap.add_apply]
    rw [finsum_congr (fun m => qConv_add_of_mem _ (hSb _) (hTb _)),
      finsum_add_distrib hfS hfT, qDeriv_add, h1, h2]
    abel

theorem IsDefectBlock.smul {S E : M →ₗ[ℂ] FormalQSeries} (hS : IsDefectBlock A S E) (c : ℂ) :
    IsDefectBlock A (c • S) (c • E) where
  vanish k hk a ha w := by
    simp only [LinearMap.smul_apply, hS.vanish k hk a ha w, smul_zero]
  negTwo k hk a ha w := by
    have h1 := hS.negTwo k hk a ha w
    simp only [LinearMap.smul_apply, qConv_smul_right, smul_comm _ c]
    rw [← smul_finsum, ← smul_add, h1, smul_zero]
  omega w := by
    have h1 := hS.omega w
    simp only [LinearMap.smul_apply, qConv_smul_right]
    rw [← smul_finsum, qDeriv_smul, h1]
    simp only [smul_add]

theorem IsDefectBlock.sub_formal {S T E : M →ₗ[ℂ] FormalQSeries} {b : ℂ}
    (hSb : ∀ w, S w ∈ QSeriesAt b) (hTb : ∀ w, T w ∈ QSeriesAt b)
    (hS : IsDefectBlock A S E) (hT : IsInsertionFormalBlock A T) :
    IsDefectBlock A (S - T) E := by
  have hT' := (isDefectBlock_zero_iff.mpr hT).smul (-1)
  have h := hS.add hSb (fun w => (QSeriesAt b).smul_mem (-1) (hTb w)) hT'
  simpa only [smul_zero, add_zero, neg_one_smul, ← sub_eq_add_neg] using h

theorem isInsertionFormalBlock_sum {κ : Type*} (s : Finset κ)
    (T : κ → M →ₗ[ℂ] FormalQSeries) {b : ℂ} (hTb : ∀ i ∈ s, ∀ w, T i w ∈ QSeriesAt b)
    (hT : ∀ i ∈ s, IsInsertionFormalBlock A (T i)) :
    IsInsertionFormalBlock A (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ← isDefectBlock_zero_iff]
    exact ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => by simp,
      fun _ => by
        simp only [LinearMap.zero_apply, qConv_zero_right, finsum_zero, add_zero]
        funext e; simp [qDeriv]⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, ← isDefectBlock_zero_iff]
    have hih := ih (fun i hi => hTb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    have h := (isDefectBlock_zero_iff.mpr (hT j (Finset.mem_insert_self j s))).add
      (hTb j (Finset.mem_insert_self j s))
      (fun w => by
        rw [LinearMap.coe_sum, Finset.sum_apply]
        exact Submodule.sum_mem _ fun i hi => hTb i (Finset.mem_insert_of_mem hi) w)
      (isDefectBlock_zero_iff.mpr hih)
    simpa only [add_zero] using h

/-! ## Leading coefficients of defect blocks -/

variable {S E : M →ₗ[ℂ] FormalQSeries} {b : ℂ}

theorem leading_fzRes_pos (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsDefectBlock A S E) {p : ℕ} (hp : 1 ≤ p)
    {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    Cusp.leading S b (fzRes A.toWeakModule p 0 a w) = 0 := by
  have hr := hS.negTwo p hp a ha w
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a p w
  have hfin : (Function.support fun m : ℕ => ((2 * (m + 1) - 1 : ℕ) : ℂ) •
      qConv (zhuG (m + 1)) (S (sqAct A a p (2 * (m + 1) - 2 : ℤ) w))).Finite := by
    refine (Set.finite_Iio K).subset fun m hm => ?_
    simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hK m (by omega), map_zero, qConv_zero_right, smul_zero])
  have hev := congrArg (fun f : FormalQSeries => f b) hr
  dsimp only at hev
  rw [Pi.add_apply, finsum_apply hfin] at hev
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Cusp.qConv_leading hsupp] at hev
  rw [← Cusp.fullNegTwo_cusp A hp a w, map_add,
    map_finsum _ (Cusp.cusp_tail_support A a p w)]
  simp only [map_smul, smul_eq_mul, mul_assoc]
  exact hev

theorem leading_kills_fzO (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsDefectBlock A S E) : fzO A.toWeakModule ≤ LinearMap.ker (Cusp.leading S b) := by
  apply Submodule.span_le.mpr
  rintro x ⟨p, n, a, ha, w, rfl⟩
  apply Cusp.fzRes_mem_of_base A (LinearMap.ker (Cusp.leading S b)) _ ha w n
  intro k a ha w
  change Cusp.leading S b (fzRes A.toWeakModule k 0 a w) = 0
  by_cases hk : k = 0
  · subst k
    rw [Cusp.fzRes_zero_weight ha, map_zero]
  · exact leading_fzRes_pos hsupp hS (by omega) ha w

theorem leading_balanced (hS : IsDefectBlock A S E)
    (p : ℕ) {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    Cusp.leading S b (fzLeft A.toWeakModule p a w) =
      Cusp.leading S b (fzRight A.toWeakModule p a w) := by
  by_cases hp : p = 0
  · subst p
    simp [fzLeft, fzRight]
  · have hv := congrArg (fun f : FormalQSeries => f b) (hS.vanish p (by omega) a ha w)
    change Cusp.leading S b (sqAct A a p 0 w) = 0 at hv
    rw [Cusp.sqAct_zero_eq_actions A (by omega), map_sub, sub_eq_zero] at hv
    exact hv

/-- The leading conformal relation acquires the leading coefficient of the defect. -/
theorem leading_conformal (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsDefectBlock A S E) (w : M) :
    Cusp.leading S b (fzLeft A.toWeakModule 2 W.conformalVector w) =
      (b + W.centralCharge / 24) * Cusp.leading S b w + E w b := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  have hfin : (Function.support fun m : ℕ => qConv (zhuG (m + 1))
      (S (sqL A (2 * (m + 1) - 2 : ℤ) w))).Finite := by
    refine (Set.finite_Iio K).subset fun m hm => ?_
    simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hK m (by omega), map_zero, qConv_zero_right])
  have hv := congrArg (fun f : FormalQSeries => f b) (hS.omega w)
  dsimp only at hv
  rw [Pi.add_apply, Pi.add_apply, finsum_apply hfin] at hv
  simp only [Cusp.qConv_leading hsupp, qDeriv] at hv
  have htail : (Function.support fun m : ℕ =>
      zhuG (m + 1) 0 • sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w).Finite := by
    obtain ⟨L, hL⟩ := sqAct_eventually_zero A W.conformalVector 2 w
    refine (Set.finite_Iio L.toNat).subset fun m hm => ?_
    simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hL _ (by omega), smul_zero])
  have hc := congrArg (Cusp.leading S b) (Cusp.negOneFamily_cusp A (by norm_num : 1 ≤ 2)
    W.conformalVector w)
  rw [map_sub, map_add, map_smul, map_finsum _ htail] at hc
  simp only [map_smul, smul_eq_mul] at hc
  have hz : Cusp.leading S b (sqAct A W.conformalVector 2 0 w) = 0 := by
    exact congrArg (fun f : FormalQSeries => f b)
      (hS.vanish 2 (by norm_num) W.conformalVector W.conformalVector_mem_grading_two w)
  rw [hz, mul_zero, add_zero] at hc
  rw [leading_balanced hS 2 W.conformalVector_mem_grading_two w]
  have hl : ∀ m : ℕ, sqL A (2 * (m + 1) - 2 : ℤ) w =
      sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w := by
    intro m
    simp [sqL, show (2 * (m + 1) - 2 : ℤ) ≠ -2 by omega,
      show (2 * (m + 1) - 2 + 1 : ℤ) = 2 * (m + 1) - 1 by ring]
  simp only [hl] at hv
  change Cusp.leading S b (sqL A (-2) w) = _ at hv
  simp only [sqL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    show (-2 + 1 : ℤ) = -1 by norm_num, map_sub, map_smul, smul_eq_mul] at hv
  change Cusp.leading S b (sqAct A W.conformalVector 2 (-1) w) -
      W.centralCharge / 24 * Cusp.leading S b w =
      b * Cusp.leading S b w + (∑ᶠ m : ℕ, zhuG (m + 1) 0 *
        Cusp.leading S b (sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w)) + E w b at hv
  linear_combination hv - hc

end VOA.Huang.GenusOne.Close
