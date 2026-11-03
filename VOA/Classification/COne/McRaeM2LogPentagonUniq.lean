import VOA.Huang.LogAssocFivePointLogUniqScale
import VOA.Huang.LogAssocFivePointEvaluation

/-! Two-scale uniqueness of genuine power-log double series on the common
pentagon chart `0<r<s, r+s<1`. A double array with uniformly bounded log
degrees, support in finitely many natural progressions in each weight, and
absolutely convergent fixed-log arrays is zero as soon as its full power-log
sum vanishes on the chart. The proof applies the proved one-variable
real-ray uniqueness `loggps_coeff_zero` first in `r` (for fixed `s`) and then
in `s`. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open scoped BigOperators

/-- The polynomial with the first `K` prescribed coefficients. -/
def finPoly (K : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range K, Polynomial.C (c k)*Polynomial.X^k

theorem finPoly_natDegree (K : ℕ) (c : ℕ → ℂ) : (finPoly K c).natDegree ≤ K := by
  unfold finPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.mp hk).le

theorem finPoly_coeff (K : ℕ) (c : ℕ → ℂ) (k : ℕ) :
    (finPoly K c).coeff k=if k<K then c k else 0 := by
  unfold finPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

theorem finPoly_eval (K : ℕ) (c : ℕ → ℂ) (x : ℂ) :
    (finPoly K c).eval x=∑ k ∈ Finset.range K, c k*x^k := by
  unfold finPoly
  simp [Polynomial.eval_finset_sum]

theorem exists_ne_zero_of_finPoly_ne_zero {K : ℕ} {c : ℕ → ℂ} (h : finPoly K c≠0) :
    ∃ k<K, c k≠0 := by
  by_contra hn
  push_neg at hn
  apply h
  unfold finPoly
  apply Finset.sum_eq_zero
  intro k hk
  rw [hn k (Finset.mem_range.mp hk), map_zero, zero_mul]

/-- A complex power of a positive real number is nonzero. -/
theorem ofReal_cpow_ne_zero {r : ℝ} (hr : 0<r) (z : ℂ) : (r : ℂ)^z≠0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  exact hr.ne' (by exact_mod_cast h.1)

/-- A tsum with a nonzero value has a nonzero term. -/
theorem exists_ne_zero_of_tsum_ne_zero {f : ℂ → ℂ} (h : ∑' x, f x≠0) : ∃ x, f x≠0 := by
  by_contra hn
  push_neg at hn
  apply h
  rw [show f=fun _ => 0 from funext hn, tsum_zero]

/-- Two-scale uniqueness of genuine power-log double series on the
pentagon chart. -/
theorem twoScale_loggps_zero (S T : Finset ℂ) (α₀ c₁ : ℂ) (C : ℂ → ℂ → ℕ → ℕ → ℂ)
    (K L : ℕ)
    (hS : ∀ γ δ k l, C γ δ k l≠0 → ∃ h∈S, ∃ n : ℕ, γ=h+n)
    (hT : ∀ γ δ k l, C γ δ k l≠0 → ∃ h∈T, ∃ n : ℕ, δ=h+n)
    (hsum : ∀ r s : ℝ, FivePointDomain r s → ∀ k l,
      Summable (fun p : ℂ × ℂ => (r : ℂ)^(p.1-α₀)*((s : ℂ)^(p.2-p.1-c₁)*C p.1 p.2 k l)))
    (hz : ∀ r s : ℝ, FivePointDomain r s →
      ∑' p : ℂ × ℂ, (r : ℂ)^(p.1-α₀)*((s : ℂ)^(p.2-p.1-c₁)*
        ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range L,
          (Real.log r : ℂ)^k*(Real.log s : ℂ)^l*C p.1 p.2 k l)=0) :
    ∀ γ δ, ∀ k<K, ∀ l<L, C γ δ k l=0 := by
  -- the inner coefficient functions in the second scale
  let c : ℝ → ℂ → ℕ → ℂ := fun s γ k =>
    ∑' δ : ℂ, (s : ℂ)^(δ-γ-c₁)*∑ l ∈ Finset.range L, (Real.log s : ℂ)^l*C γ δ k l
  -- the fixed-log arrays of the first step
  let F : ℝ → ℝ → ℕ → ℂ × ℂ → ℂ := fun r s k p =>
    (r : ℂ)^(p.1-α₀)*((s : ℂ)^(p.2-p.1-c₁)*
      ∑ l ∈ Finset.range L, (Real.log s : ℂ)^l*C p.1 p.2 k l)
  have hF : ∀ r s, FivePointDomain r s → ∀ k, Summable (F r s k) := by
    intro r s hD k
    have hh : Summable (fun p : ℂ × ℂ => ∑ l ∈ Finset.range L, (Real.log s : ℂ)^l*
        ((r : ℂ)^(p.1-α₀)*((s : ℂ)^(p.2-p.1-c₁)*C p.1 p.2 k l))) :=
      summable_sum fun l _ => (hsum r s hD k l).mul_left _
    refine hh.congr fun p => ?_
    simp only [F, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hFrow : ∀ r s, FivePointDomain r s → ∀ k γ,
      ∑' δ : ℂ, F r s k (γ,δ)=(r : ℂ)^(γ-α₀)*c s γ k := by
    intro r s hD k γ
    simp only [F, c]
    rw [tsum_mul_left]
  -- Step 1: for each `s`, all coefficient functions vanish.
  have step1 : ∀ s : ℝ, 0<s → s<1 → ∀ γ, ∀ k<K, c s γ k=0 := by
    intro s hs hs1
    let R : ℝ := min s (1-s)
    have hR : 0<R := lt_min hs (by linarith)
    have hdom : ∀ r : ℝ, 0<r → r<R → FivePointDomain r s := by
      intro r hr hrR
      refine ⟨hr, lt_of_lt_of_le hrR (min_le_left _ _), ?_⟩
      have := lt_of_lt_of_le hrR (min_le_right _ _)
      linarith
    let A : ℂ → Polynomial ℂ := fun γ => finPoly K (c s γ)
    have hcoeffA : ∀ γ k, (A γ).coeff k=if k<K then c s γ k else 0 := fun γ k =>
      finPoly_coeff K (c s γ) k
    have hdeg : ∀ γ, (A γ).natDegree ≤ K := fun γ => finPoly_natDegree K (c s γ)
    have hsupp : ∀ γ, A γ≠0 → ∃ h∈S, ∃ n : ℕ, γ=h+n := by
      intro γ hA
      obtain ⟨k,-,hk⟩ := exists_ne_zero_of_finPoly_ne_zero hA
      obtain ⟨δ,hδ⟩ := exists_ne_zero_of_tsum_ne_zero hk
      have hδ' : ∑ l ∈ Finset.range L, (Real.log s : ℂ)^l*C γ δ k l≠0 :=
        right_ne_zero_of_mul hδ
      obtain ⟨l,-,hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hδ'
      exact hS γ δ k l (right_ne_zero_of_mul hl)
    have hcoeff : ∀ r : ℝ, 0<r → r<R → ∀ k : ℕ,
        Summable (fun γ : ℂ => (A γ).coeff k*(r : ℂ)^(γ-α₀)) := by
      intro r hr hrR k
      by_cases hk : k<K
      · have hh := (hF r s (hdom r hr hrR) k).prod
        refine hh.congr fun γ => ?_
        rw [hFrow r s (hdom r hr hrR) k γ, hcoeffA, if_pos hk, mul_comm]
      · simp only [hcoeffA, if_neg hk, zero_mul]
        exact summable_zero
    have hevalA : ∀ (r : ℝ) γ, (A γ).eval (Real.log r : ℂ)*(r : ℂ)^(γ-α₀)=
        ∑ k ∈ Finset.range K, (Real.log r : ℂ)^k*((r : ℂ)^(γ-α₀)*c s γ k) := by
      intro r γ
      simp only [A, finPoly_eval, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have hsumA : ∀ r : ℝ, 0<r → r<R →
        Summable (fun γ => (A γ).eval (Real.log r : ℂ)*(r : ℂ)^(γ-α₀)) := by
      intro r hr hrR
      have hh : Summable (fun γ : ℂ => ∑ k ∈ Finset.range K,
          (Real.log r : ℂ)^k*((r : ℂ)^(γ-α₀)*c s γ k)) := by
        refine summable_sum fun k hk => Summable.mul_left _ ?_
        have := hcoeff r hr hrR k
        refine this.congr fun γ => ?_
        rw [hcoeffA, if_pos (Finset.mem_range.mp hk), mul_comm]
      exact hh.congr fun γ => (hevalA r γ).symm
    have hzA : ∀ r : ℝ, 0<r → r<R →
        ∑' γ, (A γ).eval (Real.log r : ℂ)*(r : ℂ)^(γ-α₀)=0 := by
      intro r hr hrR
      have hD := hdom r hr hrR
      have hG : ∀ p : ℂ × ℂ, (r : ℂ)^(p.1-α₀)*((s : ℂ)^(p.2-p.1-c₁)*
          ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range L,
            (Real.log r : ℂ)^k*(Real.log s : ℂ)^l*C p.1 p.2 k l)=
          ∑ k ∈ Finset.range K, (Real.log r : ℂ)^k*F r s k p := by
        intro p
        simp only [F, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      have hz' := hz r s hD
      simp only [hG] at hz'
      have hGs : Summable (fun p : ℂ × ℂ => ∑ k ∈ Finset.range K,
          (Real.log r : ℂ)^k*F r s k p) :=
        summable_sum fun k _ => (hF r s hD k).mul_left _
      rw [hGs.tsum_prod' (fun γ => summable_sum fun k _ =>
        ((hF r s hD k).prod_factor γ).mul_left _)] at hz'
      rw [← hz']
      apply tsum_congr
      intro γ
      rw [Summable.tsum_finsetSum (fun k _ => ((hF r s hD k).prod_factor γ).mul_left _),
        hevalA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [tsum_mul_left, hFrow r s hD k γ]
    have hz0 := loggps_coeff_zero S α₀ A K hdeg hsupp hR hcoeff hsumA hzA
    intro γ k hk
    have := hz0 γ k
    rwa [hcoeffA, if_pos hk] at this
  -- Step 2: uniqueness in the second scale.
  intro γ δ k hk l hl
  let B : ℂ → Polynomial ℂ := fun δ => finPoly L (fun l => C γ δ k l)
  have hcoeffB : ∀ δ l, (B δ).coeff l=if l<L then C γ δ k l else 0 := fun δ l =>
    finPoly_coeff L _ l
  have hdegB : ∀ δ, (B δ).natDegree ≤ L := fun δ => finPoly_natDegree L _
  have hsuppB : ∀ δ, B δ≠0 → ∃ h∈T, ∃ n : ℕ, δ=h+n := by
    intro δ hB
    obtain ⟨l,-,hl⟩ := exists_ne_zero_of_finPoly_ne_zero hB
    exact hT γ δ k l hl
  have hrow : ∀ s : ℝ, 0<s → s<1 → ∀ l,
      Summable (fun δ : ℂ => C γ δ k l*(s : ℂ)^(δ-(γ+c₁))) := by
    intro s hs hs1 l
    let r : ℝ := min s (1-s)/2
    have hm : 0 < min s (1-s) := lt_min hs (by linarith)
    have hr : 0<r := by positivity
    have hD : FivePointDomain r s := by
      refine ⟨hr, ?_, ?_⟩
      · have := min_le_left s (1-s)
        simp only [r]
        linarith
      · have := min_le_right s (1-s)
        simp only [r]
        linarith
    have hh := ((hsum r s hD k l).prod_factor γ).mul_left ((r : ℂ)^(γ-α₀))⁻¹
    refine hh.congr fun δ => ?_
    simp only []
    rw [← mul_assoc, inv_mul_cancel₀ (ofReal_cpow_ne_zero hr _), one_mul, mul_comm]
    congr 2
    ring
  have hcoeffB' : ∀ s : ℝ, 0<s → s<1 → ∀ l : ℕ,
      Summable (fun δ : ℂ => (B δ).coeff l*(s : ℂ)^(δ-(γ+c₁))) := by
    intro s hs hs1 l
    by_cases hl : l<L
    · refine (hrow s hs hs1 l).congr fun δ => ?_
      rw [hcoeffB, if_pos hl]
    · simp only [hcoeffB, if_neg hl, zero_mul]
      exact summable_zero
  have hevalB : ∀ (s : ℝ) δ, (B δ).eval (Real.log s : ℂ)*(s : ℂ)^(δ-(γ+c₁))=
      (s : ℂ)^(δ-γ-c₁)*∑ l ∈ Finset.range L, (Real.log s : ℂ)^l*C γ δ k l := by
    intro s δ
    simp only [B, finPoly_eval, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show δ-(γ+c₁)=δ-γ-c₁ by ring]
    ring
  have hsumB : ∀ s : ℝ, 0<s → s<1 →
      Summable (fun δ => (B δ).eval (Real.log s : ℂ)*(s : ℂ)^(δ-(γ+c₁))) := by
    intro s hs hs1
    have hh : Summable (fun δ : ℂ => ∑ l ∈ Finset.range L,
        (Real.log s : ℂ)^l*(C γ δ k l*(s : ℂ)^(δ-(γ+c₁)))) :=
      summable_sum fun l _ => (hrow s hs hs1 l).mul_left _
    refine hh.congr fun δ => ?_
    simp only [B, finPoly_eval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hzB : ∀ s : ℝ, 0<s → s<1 →
      ∑' δ, (B δ).eval (Real.log s : ℂ)*(s : ℂ)^(δ-(γ+c₁))=0 := by
    intro s hs hs1
    simp only [hevalB]
    exact step1 s hs hs1 γ k hk
  have h0 := loggps_coeff_zero T (γ+c₁) B L hdegB hsuppB one_pos hcoeffB' hsumB hzB δ l
  rwa [hcoeffB, if_pos hl] at h0

end VOA.Huang.LogAssocFivePoint
