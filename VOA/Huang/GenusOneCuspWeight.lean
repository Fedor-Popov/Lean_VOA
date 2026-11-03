import VOA.Huang.GenusOneWeightRealization

/-! # The conformal central character of a leading insertion coefficient

This is the log-free case of Miyamoto, math/0010180, Lemma 4.12 (4.23).
The Bernoulli constant-term identity is used on actual module modes.
-/
namespace VOA.Huang.GenusOne.Cusp
open VOA VOA.FZ
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The right Zhu product on a common truncation window. -/
theorem fzRight_eq_sum_Ico (A : OrdVModule W M) {k : ℕ} (hk : 1 ≤ k)
    (a : V) (w : M) {P : ℕ} (hkP : k ≤ P) :
    fzRight A.toWeakModule k a w =
      ∑ i ∈ Finset.Ico (-1 : ℤ) (P : ℤ),
        cbz ((k : ℤ) - 1) (i + 1) • A.toWeakModule.act a i w := by
  classical
  have hs : Finset.Ico (-1 : ℤ) (P : ℤ) =
      (Finset.range (P + 1)).map ⟨fun j : ℕ => (j : ℤ) - 1, fun x y h => by simpa using h⟩ := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(i + 1).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega
  rw [hs, Finset.sum_map, fzRight]
  simp only [Function.Embedding.coeFn_mk, sub_add_cancel]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  rw [Finset.mem_range, not_lt] at hj
  rw [cbz_lt (by omega) (by omega : (k : ℤ) - 1 < (j : ℤ)), zero_smul]

/-- The minus-one cusp kernel is the average of the two raw Zhu actions. -/
theorem negOneFamily_cusp (A : OrdVModule W M) {k : ℕ} (hk : 1 ≤ k)
    (a : V) (w : M) :
    sqAct A a k (-1) w - ∑ᶠ m : ℕ,
      zhuG (m + 1) 0 • sqAct A a k (2 * (m + 1) - 1 : ℤ) w =
      fzRight A.toWeakModule k a w + (1 / 2 : ℂ) • sqAct A a k 0 w := by
  classical
  obtain ⟨N, hN⟩ := A.truncation a w
  let P := (max N (k : ℤ)).toNat
  have hP : ∀ i : ℤ, (P : ℤ) ≤ i → A.toWeakModule.act a i w = 0 := by
    intro i hi
    exact hN i (by dsimp [P] at hi; omega)
  have hkP : k ≤ P := by dsimp [P]; omega
  let S := Finset.Ico (-1 : ℤ) (P : ℤ)
  have hmode (j : ℤ) (hj : -1 ≤ j) : sqAct A a k j w =
      ∑ i ∈ S, sqBracketCoeffZ k j i • A.toWeakModule.act a i w := by
    rw [sqAct_apply]
    apply finsum_eq_finsetSum_of_support_subset
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [S, Finset.mem_coe, Finset.mem_Ico]
    constructor
    · by_contra hn
      exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
    · by_contra hn
      exact hi (by rw [show mode (A.YM a) i w = A.toWeakModule.act a i w from rfl,
        hP i (by omega), smul_zero])
  have hzero (m : ℕ) (hm : P ≤ m) : sqAct A a k (2 * (m + 1) - 1 : ℤ) w = 0 := by
    rw [hmode _ (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [S, Finset.mem_Ico] at hi
    rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul]
  have hfin : (∑ᶠ m : ℕ, zhuG (m + 1) 0 • sqAct A a k (2 * (m + 1) - 1 : ℤ) w) =
      ∑ m ∈ Finset.range P, zhuG (m + 1) 0 • sqAct A a k (2 * (m + 1) - 1 : ℤ) w := by
    apply finsum_eq_finsetSum_of_support_subset
    intro m hm
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hzero m (by omega), smul_zero])
  have hswap : (∑ m ∈ Finset.range P,
      zhuG (m + 1) 0 • sqAct A a k (2 * (m + 1) - 1 : ℤ) w) =
      ∑ i ∈ S, (∑ m ∈ Finset.range P,
        zhuG (m + 1) 0 * sqBracketCoeffZ k (2 * (m + 1) - 1 : ℤ) i) •
          A.toWeakModule.act a i w := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hmode _ (by omega), Finset.smul_sum]),
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  have hscalar (i : ℤ) (hi : i ∈ S) :
      sqBracketCoeffZ k (-1) i - (∑ m ∈ Finset.range P,
        zhuG (m + 1) 0 * sqBracketCoeffZ k (2 * (m + 1) - 1 : ℤ) i) =
      cbz ((k : ℤ) - 1) (i + 1) + (1 / 2 : ℂ) * sqBracketCoeffZ k 0 i := by
    simp only [S, Finset.mem_Ico] at hi
    by_cases hin : i = -1
    · subst i
      rw [sqBracketCoeffZ_neg_one_diag, sqBracketCoeffZ_of_lt k (by norm_num)]
      have hz : ∀ m ∈ Finset.range P,
          zhuG (m + 1) 0 * sqBracketCoeffZ k (2 * (m + 1) - 1 : ℤ) (-1) = 0 := by
        intro m _
        rw [sqBracketCoeffZ_of_lt k (by omega), mul_zero]
      rw [Finset.sum_eq_zero hz]
      simp [cbz_zero]
    · have hi0 : 0 ≤ i := by omega
      have he : ∑ m ∈ Finset.range P,
          zhuG (m + 1) 0 * sqBracketCoeffZ k (2 * (m + 1) - 1 : ℤ) i =
          ∑ᶠ m : ℕ, zhuG (m + 1) 0 * sqBracketCoeff k (2 * m + 1) i.toNat := by
        rw [Finset.sum_congr rfl (fun m _ => by
          rw [show i = (i.toNat : ℤ) from (Int.toNat_of_nonneg hi0).symm,
            sqBracketCoeffZ_odd_eq])]
        simp only [Nat.cast_nonneg, if_true, Int.toNat_natCast]
        apply (finsum_eq_finsetSum_of_support_subset _ _).symm
        intro m hm
        simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hm ⊢
        by_contra hn
        exact hm (by rw [sqBracketCoeff_eq_zero_of_lt k (by omega), mul_zero])
      rw [he]
      have key := sqBracketCoeffZ_neg_one_eq hk i.toNat
      rw [Int.toNat_of_nonneg hi0] at key
      rw [← cbz_eq_sqBracketCoeffZ_zero k hk]
      linear_combination key
  rw [hfin, hswap, hmode _ (by omega), hmode 0 (by omega),
    fzRight_eq_sum_Ico A hk a w hkP, Finset.smul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← add_smul, ← sub_smul, hscalar i hi]

variable {A : OrdVModule W M} {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ}

/-- The leading functional has conformal central character `b + c/24`. -/
theorem leading_conformal (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) (w : M) :
    leading S b (fzLeft A.toWeakModule 2 W.conformalVector w) =
      (b + W.centralCharge / 24) * leading S b w := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A w
  have hfin : (Function.support fun m : ℕ => qConv (zhuG (m + 1))
      (S (sqL A (2 * (m + 1) - 2 : ℤ) w))).Finite := by
    refine (Set.finite_Iio K).subset fun m hm => ?_
    simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hK m (by omega), map_zero, qConv_zero_right])
  have hv := congrArg (fun f : FormalQSeries => f b) (hS.omega w)
  dsimp only at hv
  rw [Pi.add_apply, finsum_apply hfin] at hv
  simp only [qConv_leading hsupp, qDeriv] at hv
  have htail : (Function.support fun m : ℕ =>
      zhuG (m + 1) 0 • sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w).Finite := by
    obtain ⟨L, hL⟩ := sqAct_eventually_zero A W.conformalVector 2 w
    refine (Set.finite_Iio L.toNat).subset fun m hm => ?_
    simp only [Function.mem_support, Set.mem_Iio] at hm ⊢
    by_contra hn
    exact hm (by rw [hL _ (by omega), smul_zero])
  have hc := congrArg (leading S b) (negOneFamily_cusp A (by norm_num : 1 ≤ 2)
    W.conformalVector w)
  rw [map_sub, map_add, map_smul, map_finsum _ htail] at hc
  simp only [map_smul, smul_eq_mul] at hc
  have hz : leading S b (sqAct A W.conformalVector 2 0 w) = 0 := by
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
  change leading S b (sqL A (-2) w) = _ at hv
  simp only [sqL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    show (-2 + 1 : ℤ) = -1 by norm_num, map_sub, map_smul, smul_eq_mul] at hv
  change leading S b (sqAct A W.conformalVector 2 (-1) w) -
      W.centralCharge / 24 * leading S b w =
      b * leading S b w + ∑ᶠ m : ℕ, zhuG (m + 1) 0 *
        leading S b (sqAct A W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) w) at hv
  linear_combination hv - hc

end VOA.Huang.GenusOne.Cusp

namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u} [Fintype ι]

/-- Correct-weight realization of a supported formal block's leading term.
Only quotient bimodule existence and the converse top correspondence remain
algebraic inputs; the central-character condition is proved, not assumed. -/
theorem leading_realized_at_weight (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (hlift : InsertionTopSurjectivity A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, S w b = ∑ i, trace (Y i) w b := by
  obtain ⟨B⟩ := hB
  exact functional_realized_at_weight P B hlift b (Cusp.leading S b)
    (Cusp.leading_kills_fzO hsupp hS)
    (fun p _ ha w => Cusp.leading_balanced hS p ha w)
    (Cusp.leading_conformal hsupp hS)

end VOA.Huang.GenusOne
