import VOA.Huang.GenusOneCuspAlgebra

/-! # Leading functionals of supported insertion blocks

The leading coefficient of a log-free formal block descends to the actual
Frenkel–Zhu quotient and is balanced for its two actions. This is the algebraic
part of Miyamoto, math/0010180, Lemmas 4.11–4.12; no assertion that every analytic
block has such an expansion is made here.
-/
namespace VOA.Huang.GenusOne.Cusp
open VOA VOA.FZ
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ}

/-- Evaluation at the lowest permitted exponent. -/
noncomputable def leading (S : M →ₗ[ℂ] FormalQSeries) (b : ℂ) : M →ₗ[ℂ] ℂ :=
  (LinearMap.proj b).comp S

@[simp] theorem leading_apply (w : M) : leading S b w = S w b := rfl

theorem qConv_leading (hsupp : ∀ w, S w ∈ QSeriesAt b) (f : ℕ → ℂ) (w : M) :
    qConv f (S w) b = f 0 * leading S b w := by
  simpa using qConv_apply_of_support f (S w) b (QSeriesAt.support_neg (hsupp w)) 0

theorem cusp_tail_support (A : OrdVModule W M) (a : V) (k : ℕ) (w : M) :
    (Function.support fun m : ℕ =>
      (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuG (m + 1) 0) •
        sqAct A a k (2 * (m + 1) - 2 : ℤ) w).Finite := by
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a k w
  refine (Set.finite_Iio K).subset fun m hm => ?_
  simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
  by_contra hn
  exact hm (by rw [hK m (by omega), smul_zero])

theorem leading_fzRes_pos (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) {p : ℕ} (hp : 1 ≤ p)
    {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    leading S b (fzRes A.toWeakModule p 0 a w) = 0 := by
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
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, qConv_leading hsupp] at hev
  rw [← fullNegTwo_cusp A hp a w, map_add,
    map_finsum _ (cusp_tail_support A a p w)]
  simp only [map_smul, smul_eq_mul, mul_assoc]
  exact hev

/-- The weight-zero state contributes no Zhu residue. -/
theorem fzRes_zero_weight {a : V} (ha : a ∈ W.grading 0) (w : M) :
    fzRes A.toWeakModule 0 0 a w = 0 := by
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  simp only [fzRes, zero_add, Nat.cast_zero, Finset.sum_range_one,
    cbz_zero, one_smul, sub_zero, zero_sub, map_smul]
  change c • A.toWeakModule.act W.vacuum (-2) w = 0
  rw [A.toWeakModule.act_vacuum]
  norm_num

/-- All poles, not just depth zero, are killed by the leading coefficient. -/
theorem leading_kills_fzO (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) : fzO A.toWeakModule ≤ LinearMap.ker (leading S b) := by
  apply Submodule.span_le.mpr
  rintro x ⟨p, n, a, ha, w, rfl⟩
  apply fzRes_mem_of_base A (LinearMap.ker (leading S b)) _ ha w n
  intro k a ha w
  change leading S b (fzRes A.toWeakModule k 0 a w) = 0
  by_cases hk : k = 0
  · subst k
    rw [fzRes_zero_weight ha, map_zero]
  · exact leading_fzRes_pos hsupp hS (by omega) ha w

/-- The leading coefficient as an actual linear functional on `A(M) = M/O(M)`. -/
noncomputable def leadingOnZhu (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) : (M ⧸ fzO A.toWeakModule) →ₗ[ℂ] ℂ :=
  (fzO A.toWeakModule).liftQ (leading S b) (leading_kills_fzO hsupp hS)

@[simp] theorem leadingOnZhu_mk (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) (w : M) :
    leadingOnZhu hsupp hS ((fzO A.toWeakModule).mkQ w) = S w b := rfl

/-- Symmetry means equality of the two Zhu actions; `A(M)` need not be an algebra. -/
theorem leading_balanced (hS : IsInsertionFormalBlock A S)
    (p : ℕ) {a : V} (ha : a ∈ W.grading (p : ℤ)) (w : M) :
    leading S b (fzLeft A.toWeakModule p a w) =
      leading S b (fzRight A.toWeakModule p a w) := by
  by_cases hp : p = 0
  · subst p
    simp [fzLeft, fzRight]
  · have hv := congrArg (fun f : FormalQSeries => f b) (hS.vanish p (by omega) a ha w)
    change leading S b (sqAct A a p 0 w) = 0 at hv
    rw [sqAct_zero_eq_actions A (by omega), map_sub, sub_eq_zero] at hv
    exact hv

end VOA.Huang.GenusOne.Cusp
