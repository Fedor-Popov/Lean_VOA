import VOA.Huang.GenusOneRelationCovariance
import VOA.Modularity.CuspDegeneration

/-! # The module cusp relation and higher Zhu residues

The scalar Bernoulli identity from `CuspDegeneration` is applied to module modes.
Higher poles are reduced by the translation recursion of Frenkel–Zhu Lemma 2.1.2.
These are algebraic statements, without a Frobenius expansion assumption.
-/
namespace VOA.Huang.GenusOne.Cusp
open VOA VOA.FZ
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Every square-bracket mode with `−2 ≤ j` is a finite sum over a common window. -/
theorem vSqZ_eq_sum_Ico (A : OrdVModule W M) {k : ℕ} {j : ℤ} (hM : -2 ≤ j) (a : V) (v : M) {P : ℕ}
    (hP : ∀ i : ℤ, (P : ℤ) ≤ i → A.toWeakModule.act a i v = 0) :
    sqAct A a k j v
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), sqBracketCoeffZ k j i • A.toWeakModule.act a i v := by
  classical
  rw [sqAct_apply]
  refine finsum_eq_finsetSum_of_support_subset _ (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra hc
    push Not at hc
    exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
  · by_contra hc
    push Not at hc
    exact hi (by rw [show mode (A.YM a) i v = A.toWeakModule.act a i v from rfl,
      hP i hc, smul_zero])

/-- Zhu's `a ∘ v = fzRes A.toWeakModule k 0 a v` on the same window. -/
theorem pres_zero_eq_sum_Ico (A : OrdVModule W M) {k : ℕ} (a : V) (v : M) {P : ℕ}
    (hkP : k ≤ P) :
    fzRes A.toWeakModule k 0 a v
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), cbz (k : ℤ) (i + 2) • A.toWeakModule.act a i v := by
  classical
  have hmapset : Finset.Ico (-2 : ℤ) (P : ℤ)
      = (Finset.range (P + 2)).map ⟨fun j : ℕ => (j : ℤ) - 2, fun x y h => by simpa using h⟩ := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(i + 2).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hmapset, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ j ∈ Finset.range (P + 2),
      cbz (k : ℤ) (((j : ℤ) - 2) + 2) • A.toWeakModule.act a ((j : ℤ) - 2) v
        = cbz ((k : ℤ) + ((0 : ℕ) : ℤ)) (j : ℤ) •
            A.toWeakModule.act a ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) v := by
    intro j _
    rw [show (((j : ℤ) - 2) + 2) = (j : ℤ) from by ring,
      show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
      show ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) = (j : ℤ) - 2 from by push_cast; ring]
  rw [Finset.sum_congr rfl hterm, fzRes]
  have hsub : Finset.range (k + 0 + 1) ⊆ Finset.range (P + 2) :=
    Finset.range_mono (by omega)
  refine Finset.sum_subset hsub (fun j _ hj => ?_)
  rw [Finset.mem_range, not_lt] at hj
  rw [show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
    cbz_lt (by omega) (by omega : (k : ℤ) < (j : ℤ)), zero_smul]

/-- **DLM Lemma 9.2(c)** — the `q → 0` limit of the (`G₂`-free) `[−2]`-family:

`a[−2]v + Σ_{m} (2(m+2)−1)·G_{2(m+2)}(∞)·a[2(m+2)−2]v = a ∘ v + (1/12)·a[0]v`. -/
theorem negTwoFamily_cusp (A : OrdVModule W M) {k : ℕ} (hk : 1 ≤ k) (a : V) (v : M) :
    sqAct A a k (-2) v
        + ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
            • sqAct A a k (2 * ((m : ℤ) + 2) - 2) v
      = fzRes A.toWeakModule k 0 a v + (1 / 12 : ℂ) • sqAct A a k 0 v := by
  classical
  obtain ⟨N, hN⟩ := A.truncation a v
  set P : ℕ := (max N (k : ℤ)).toNat with hPdef
  have hP : ∀ i : ℤ, (P : ℤ) ≤ i → A.toWeakModule.act a i v = 0 := by
    intro i hi
    exact hN i (by omega)
  have hkP : k ≤ P := by omega
  set S : Finset ℤ := Finset.Ico (-2 : ℤ) (P : ℤ) with hS
  -- every mode in sight, on the common window
  have hmode : ∀ j : ℤ, -2 ≤ j → sqAct A a k j v
      = ∑ i ∈ S, sqBracketCoeffZ k j i • A.toWeakModule.act a i v :=
    fun M hM => vSqZ_eq_sum_Ico A hM a v hP
  -- the `m`-family dies past `P`
  have hzero : ∀ m : ℕ, P ≤ m → sqAct A a k (2 * ((m : ℤ) + 2) - 2) v = 0 := by
    intro m hm
    rw [hmode _ (by omega)]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul]
  have hfin : ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • sqAct A a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ m ∈ Finset.range P, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • sqAct A a k (2 * ((m : ℤ) + 2) - 2) v := by
    refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    exact hm (by rw [hzero m hc, smul_zero])
  -- collect everything on the window
  have hswap : ∑ m ∈ Finset.range P, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • sqAct A a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ i ∈ S, (∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
          * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i) • A.toWeakModule.act a i v := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hmode _ (by omega), Finset.smul_sum]),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun m _ => by rw [smul_smul])
  have hmfin : ∀ i ∈ S, ∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
        * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i
      = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
        * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    refine (finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)).symm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    exact hm (by rw [sqBracketCoeffZ_of_lt k (by omega), mul_zero])
  rw [hfin, hswap, Finset.sum_congr rfl (fun i hi => by rw [hmfin i hi]),
    hmode _ (by omega), hmode (0 : ℤ) (by omega),
    pres_zero_eq_sum_Ico A a v hkP, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  have hkey := sqBracketCoeffZ_neg_two_cusp hk (i + 2).toNat
  rw [show (((i + 2).toNat : ℤ) - 2) = i from by omega,
    show (((i + 2).toNat : ℤ)) = i + 2 from by omega] at hkey
  linear_combination hkey

/-- All higher-pole residues lie in any submodule containing the depth-zero residues. -/
theorem fzRes_mem_of_base (A : OrdVModule W M) (P : Submodule ℂ M)
    (hbase : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ b : M,
      fzRes A.toWeakModule p 0 a b ∈ P)
    {p : ℕ} {a : V} (ha : a ∈ W.grading (p : ℤ)) (b : M) (n : ℕ) :
    fzRes A.toWeakModule p n a b ∈ P := by
  induction n generalizing p a with
  | zero => exact hbase p a ha b
  | succ n ih =>
    have haL : W.L (-1) a ∈ W.grading ((p : ℤ) + 1) := L_neg_one_mem_grading_succ W ha
    have hG : fzRes A.toWeakModule (p + 1) n (W.L (-1) a) b ∈ P := by
      have := ih (p := p + 1) (a := W.L (-1) a) (by
        rwa [show (((p + 1 : ℕ)) : ℤ) = (p : ℤ) + 1 from by push_cast; ring])
      exact this
    have hP : fzRes A.toWeakModule p n a b ∈ P := ih ha
    have hGeq : fzRes A.toWeakModule (p + 1) n (W.L (-1) a) b
        = ∑ i ∈ Finset.range (p + n + 2),
            (cbz ((p : ℤ) + n + 1) (i : ℤ) * (-((i : ℂ) - 2 - n)))
              • A.toWeakModule.act a ((i : ℤ) - 3 - n) b := by
      unfold fzRes
      rw [show p + 1 + n + 1 = p + n + 2 from by ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcast1 : (((p + 1 : ℕ) : ℤ)) + (n : ℤ) = (p : ℤ) + n + 1 := by push_cast; ring
      change cbz _ _ • A.toWeakModule.act (W.L (-1) a) _ b = _
      rw [hcast1, act_T_covariance A.toWeakModule a ((i : ℤ) - 2 - n) b,
        show ((i : ℤ) - 2 - n - 1) = (i : ℤ) - 3 - n from by ring,
        smul_smul]
      congr 2
      push_cast
      ring
    have hsum : ((n : ℂ) + 2) • fzRes A.toWeakModule p (n + 1) a b
        = fzRes A.toWeakModule (p + 1) n (W.L (-1) a) b +
          ((p : ℂ) + n + 1) • fzRes A.toWeakModule p n a b := by
      rw [hGeq]
      have hLHS : ((n : ℂ) + 2) • fzRes A.toWeakModule p (n + 1) a b
          = ∑ i ∈ Finset.range (p + n + 2),
              (((n : ℂ) + 2) * cbz ((p : ℤ) + (n + 1)) (i : ℤ))
                • A.toWeakModule.act a ((i : ℤ) - 2 - (n + 1)) b := by
        unfold fzRes
        rw [show p + (n + 1) + 1 = p + n + 2 from by ring, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul]
        congr 2
      have hPn : ((p : ℂ) + n + 1) • fzRes A.toWeakModule p n a b
          = ∑ i ∈ Finset.range (p + n + 2),
              (((p : ℂ) + n + 1) * cbz ((p : ℤ) + n) ((i : ℤ) - 1))
                • A.toWeakModule.act a ((i : ℤ) - 3 - n) b := by
        unfold fzRes
        rw [Finset.smul_sum]
        rw [Finset.sum_range_succ' (fun i => (((p : ℂ) + n + 1) * cbz ((p : ℤ) + n) ((i : ℤ) - 1))
            • A.toWeakModule.act a ((i : ℤ) - 3 - n) b) (p + n + 1)]
        rw [show cbz ((p : ℤ) + n) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
          mul_zero, zero_smul, add_zero]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [smul_smul]
        congr 2
        · push_cast; ring_nf
        · push_cast; ring_nf
      rw [hLHS, hPn, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hmode : ((i : ℤ) - 2 - ((n : ℤ) + 1)) = (i : ℤ) - 3 - n := by ring
      rw [show ((p : ℤ) + ((n : ℤ) + 1)) = (p : ℤ) + n + 1 from by ring, hmode,
        ← add_smul]
      congr 1
      have := pres_coeff_identity p n (i : ℤ)
      push_cast at this ⊢
      linear_combination this
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero (n + 1)
    have : fzRes A.toWeakModule p (n + 1) a b
        = (((n : ℂ) + 2)⁻¹) • (fzRes A.toWeakModule (p + 1) n (W.L (-1) a) b +
          ((p : ℂ) + n + 1) • fzRes A.toWeakModule p n a b) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP))


/-- The library's all-poles definition of `O(M)` equals its depth-zero definition. -/
theorem fzO_eq_span_base (A : OrdVModule W M) :
    fzO A.toWeakModule = Submodule.span ℂ {x | ∃ (p : ℕ) (a : V),
      a ∈ W.grading (p : ℤ) ∧ ∃ w : M, x = fzRes A.toWeakModule p 0 a w} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨p, n, a, ha, w, rfl⟩
    apply fzRes_mem_of_base A _ ?_ ha w n
    intro k a ha w
    exact Submodule.subset_span ⟨k, a, ha, w, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨p, a, ha, w, rfl⟩
    exact fzRes_mem_fzO A.toWeakModule 0 ha w

/-- The full cusp relation, including the constant term of G₂, is the Zhu residue. -/
theorem fullNegTwo_cusp (A : OrdVModule W M) {k : ℕ} (hk : 1 ≤ k) (a : V) (v : M) :
    sqAct A a k (-2) v + ∑ᶠ m : ℕ,
      (((2 * (m + 1) - 1 : ℕ) : ℂ) * zhuG (m + 1) 0) •
        sqAct A a k (2 * (m + 1) - 2 : ℤ) v = fzRes A.toWeakModule k 0 a v := by
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a k v
  rw [finsum_nat_peel_module (K := K) (fun m hm => by rw [hK m hm, smul_zero])]
  have hg : zhuG 1 0 = -(1 / 12 : ℂ) := by norm_num [zhuG_zero, bernoulli_two]
  simp only [Nat.cast_zero, zero_add, mul_one, Nat.reduceSubDiff, Nat.cast_one,
    one_mul, Int.reduceNeg, hg]
  have ht := negTwoFamily_cusp A hk a v
  rw [← sub_eq_iff_eq_add] at ht
  rw [← ht]
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  simp only [add_assoc, one_add_one_eq_two]
  module

/-- The square zero mode is precisely the difference of the two Zhu actions. -/
theorem sqAct_zero_eq_actions (A : OrdVModule W M) {p : ℕ} (hp : 1 ≤ p)
    (a : V) (w : M) :
    sqAct A a p 0 w = fzLeft A.toWeakModule p a w - fzRight A.toWeakModule p a w := by
  classical
  rw [fzLeft_sub_fzRight, sqAct_apply]
  simp only [← cbz_eq_sqBracketCoeffZ_zero p hp]
  rw [finsum_int_ge_eq_nat_shift (j := 0) _ (fun i hi => by
    rw [cbz_apply_neg _ hi, zero_smul])]
  simp only [zero_add]
  apply finsum_eq_finsetSum_of_support_subset
  intro i hi
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hi ⊢
  by_contra hn
  exact hi (by rw [cbz_lt (by omega) (by omega : (p : ℤ) - 1 < (i : ℤ)), zero_smul])

end VOA.Huang.GenusOne.Cusp
