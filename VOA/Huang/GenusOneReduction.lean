import VOA.Huang.GenusOneDifferential
import VOA.Huang.FusionC2

/-! # The square-mode minus-two relation for insertion modules -/
namespace VOA.Huang.GenusOne
open VOA Module
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

/-- Translation in the cylinder coordinate on the insertion module. -/
noncomputable def cylT (A : OrdVModule W M₁) : Module.End ℂ M₁ :=
  mode (A.YM W.conformalVector) 0 + mode (A.YM W.conformalVector) 1

/-- The cylinder translation operator is exactly L[-1] in the square coordinate. -/
theorem sqL_negOne (A : OrdVModule W M₁) : sqL A (-1) = cylT A := by
  ext w
  simp only [sqL,
    show (-1 : ℤ) ≠ -2 by norm_num, if_false, zero_smul, sub_zero,
    show (-1 : ℤ) + 1 = 0 by norm_num, sqAct_apply]
  simp_rw [← cbz_eq_sqBracketCoeffZ_zero 2 (by norm_num)]
  change (∑ᶠ i : ℤ, cbz (1 : ℤ) i • mode (A.YM W.conformalVector) i w) = _
  have hs : (Function.support fun i : ℤ => cbz (1 : ℤ) i • mode (A.YM W.conformalVector) i w)
      ⊆ ({0, 1} : Finset ℤ) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    apply hi
    by_cases hn0 : i < 0
    · rw [cbz_apply_neg _ hn0, zero_smul]
    · rw [cbz_eq_zero_of_lt (by norm_num) (by omega), zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair (by norm_num)]
  have hc : cbz (1 : ℤ) 1 = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num)]
    simpa using gBinom_natCast 1 1
  rw [cbz_zero, hc, one_smul, one_smul]
  rfl

theorem zeroMode_cylT (Y : IntertwiningOperator A N N) (w : M₁) :
    zeroMode A Y.val (cylT A w) = 0 := by
  refine FusionTop.induction_weight A w (by simp) (fun x y hx hy => by
    simp only [map_add, hx, hy, add_zero]) ?_
  intro α x hx
  change zeroMode A Y.val (A.Lm1 x + mode (A.YM W.conformalVector) 1 x) = 0
  rw [map_add, A.L0_weight α x hx, map_smul, zeroMode_of_mem _ _ hx,
    zeroMode_of_mem _ _ (mode_mem_weight A W.conformalVector_mem_grading_two hx 0)]
  rw [show α + (2 : ℤ) - (0 : ℤ) - 1 - 1 = α by push_cast; ring,
    Y.property.L_neg_one]
  simp

theorem trace_cylT (Y : IntertwiningOperator A N N) (w : M₁) : trace Y (cylT A w) = 0 := by
  change gradedTraceOp N (zeroMode A Y.val (cylT A w)) = 0
  rw [zeroMode_cylT]
  funext e
  exact map_zero (gradedTraceAt N e)

theorem module_Lm1_comm (a : V) (w : M₁) (i : ℤ) :
    mode (A.YM W.conformalVector) 0 (mode (A.YM a) i w) -
      mode (A.YM a) i (mode (A.YM W.conformalVector) 0 w) =
        (-i : ℂ) • mode (A.YM a) (i - 1) w := by
  have h := mode_commutator A.toWeakModule W.conformalVector a w 0 i
  rw [finsum_eq_single _ (0 : ℤ) (fun j hj => by
    rw [cbz_zero_left, if_neg hj, zero_smul]), cbz_zero_left, if_pos rfl,
    one_smul, zero_add, sub_zero] at h
  change _ = mode (A.YM (W.L (-1) a)) i w at h
  rw [h]
  exact act_T_covariance A.toWeakModule a i w

theorem module_L0_comm {k : ℤ} {a : V} (ha : a ∈ W.grading k) (w : M₁) (i : ℤ) :
    mode (A.YM W.conformalVector) 1 (mode (A.YM a) i w) -
      mode (A.YM a) i (mode (A.YM W.conformalVector) 1 w) =
        ((k : ℂ) - i - 1) • mode (A.YM a) i w := by
  refine FusionTop.induction_weight A w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, smul_add]
    rw [← hx, ← hy]
    abel
  · intro α x hx
    rw [A.L0_weight _ _ (mode_mem_weight A ha hx i), A.L0_weight _ _ hx,
      map_smul, ← sub_smul]
    congr 1
    ring

theorem cylT_sqAct_comm {k : ℕ} (hk : 1 ≤ k) {a : V} (ha : a ∈ W.grading (k : ℤ)) (m : ℤ)
    (v : M₁) :
    cylT A (sqAct A a k m v) - sqAct A a k m (cylT A v)
      = (-(m : ℂ)) • sqAct A a k (m - 1) v := by
  obtain ⟨R, hR⟩ := A.truncation a v
  -- pointwise commutator with `a₍ᵢ₎`
  have hcomm : ∀ i : ℤ, (cylT A) (mode (A.YM a) i v) - mode (A.YM a) i ((cylT A) v)
      = (-i : ℂ) • mode (A.YM a) (i - 1) v + ((k : ℂ) - i - 1) • mode (A.YM a) i v := by
    intro i
    have h1 := module_Lm1_comm (A := A) a v i
    have h2 := module_L0_comm (A := A) ha v i
    rw [Int.cast_natCast] at h2
    simp only [cylT, LinearMap.add_apply, map_add]
    rw [← h1, ← h2]
    abel
  -- expand `a[m]` and distribute
  have hfinL : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • mode (A.YM a) i v).Finite := sqAct_support_finite A a k m v
  have hexp : cylT A (sqAct A a k m v) - sqAct A a k m (cylT A v)
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i •
          ((cylT A) (mode (A.YM a) i v) - mode (A.YM a) i ((cylT A) v)) := by
    rw [sqAct_apply, sqAct_apply, map_finsum _ hfinL]
    have hfin2 : (Function.support fun i : ℤ =>
        sqBracketCoeffZ k m i • mode (A.YM a) i ((cylT A) v)).Finite :=
      sqAct_support_finite A a k m ((cylT A) v)
    rw [← finsum_sub_distrib (by
        refine hfinL.subset (fun i hi => ?_)
        simp only [Function.mem_support, ne_eq] at hi ⊢
        intro h0; exact hi (by rw [h0, map_zero])) hfin2]
    refine finsum_congr (fun i => ?_)
    rw [map_smul, smul_sub]
  rw [hexp]
  simp_rw [hcomm]
  -- split into the two families and reindex the shifted one
  have hfinA : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • ((-i : ℂ) • mode (A.YM a) (i - 1) v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k hc, zero_smul])
    · by_contra hc; push Not at hc
      exact hi (by rw [hR (i - 1) (by omega), smul_zero, smul_zero])
  have hfinB : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • (((k : ℂ) - i - 1) • mode (A.YM a) i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k hc, zero_smul])
    · by_contra hc; push Not at hc
      exact hi (by rw [hR i (by omega), smul_zero, smul_zero])
  simp_rw [smul_add]
  rw [finsum_add_distrib hfinA hfinB]
  -- reindex `i ↦ i + 1` in the first family
  have hshift : (∑ᶠ i : ℤ, sqBracketCoeffZ k m i • ((-i : ℂ) • mode (A.YM a) (i - 1) v))
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m (i + 1) • ((-(i + 1) : ℂ) • mode (A.YM a) i v) := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr (fun i => ?_)
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    push_cast
    ring_nf
  rw [hshift, ← finsum_add_distrib]
  · rw [sqAct_apply, smul_finsum' _ (sqAct_support_finite A a k (m - 1) v)]
    refine finsum_congr (fun i => ?_)
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    have := sqBracketCoeffZ_derivation hk m i
    push_cast at this ⊢
    linear_combination this
  · refine Set.Finite.subset (Set.finite_Icc (m - 1) R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
    · by_contra hc; push Not at hc
      exact hi (by rw [hR i (by omega), smul_zero, smul_zero])
  · exact hfinB
theorem trace_sqAct_negTwo (Y : IntertwiningOperator A N N) {ka : ℕ} (hk : 1 ≤ ka)
    {a : V} (ha : a ∈ W.grading (ka : ℤ))
    (v : M₁) :
    trace Y (sqAct A a ka (-2) v)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (trace Y (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v)) = 0 := by
  set w : M₁ := cylT A v with hw
  have hrec := trace_sqAct_negOne Y hk ha w
  -- left side: `a[−1]w = L[−1](a[−1]v) − a[−2]v`
  have hL : sqAct A a ka (-1) w = cylT A (sqAct A a ka (-1) v) - sqAct A a ka (-2) v := by
    have h := cylT_sqAct_comm (A := A) hk ha (-1) v
    rw [show (-1 : ℤ) - 1 = -2 from by norm_num, show (-((-1 : ℤ) : ℂ)) = 1 from by push_cast; ring,
      one_smul] at h
    rw [hw, ← h]
    abel
  -- two-point term vanishes: `o(w) = 0`
  have htwo : traceTwo Y a w = 0 := by
    rw [traceTwo, hw, zeroMode_cylT, mul_zero]
    funext e
    exact map_zero (gradedTraceAt N e)
  -- `𝒵(a[−1]w) = −𝒵(a[−2]v)`
  have hLZ : trace Y (sqAct A a ka (-1) w) = -trace Y (sqAct A a ka (-2) v) := by
    rw [hL, map_sub, trace_cylT, zero_sub]
  -- tail terms: `a[2k−1]w = L[−1](a[2k−1]v) + (2k−1)·a[2k−2]v`
  have htail : ∀ m : ℕ, trace Y (sqAct A a ka (2 * (m + 1) - 1 : ℤ) w)
      = ((2 * (m + 1) - 1 : ℕ) : ℂ) • trace Y (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) := by
    intro m
    have h := cylT_sqAct_comm (A := A) hk ha (2 * (m + 1) - 1 : ℤ) v
    rw [show (2 * (m + 1) - 1 - 1 : ℤ) = 2 * (m + 1) - 2 from by ring, ← hw,
      sub_eq_iff_eq_add] at h
    have hc : (((2 * (m + 1) - 1 : ℕ) : ℂ)) = ((2 * (m + 1) - 1 : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (m + 1))]; ring
    have hidx : sqAct A a ka (2 * (m + 1) - 1 : ℤ) w
        = cylT A (sqAct A a ka (2 * (m + 1) - 1 : ℤ) v)
          + ((2 * (m + 1) - 1 : ℕ) : ℂ) • sqAct A a ka (2 * (m + 1) - 2 : ℤ) v := by
      rw [hc, h, neg_smul]
      abel
    rw [hidx, map_add, map_smul, trace_cylT, zero_add]
  rw [hLZ, htwo, zero_add] at hrec
  simp_rw [htail, qConv_smul_right] at hrec
  rw [neg_eq_iff_eq_neg] at hrec
  rw [hrec, neg_add_cancel]


end VOA.Huang.GenusOne
