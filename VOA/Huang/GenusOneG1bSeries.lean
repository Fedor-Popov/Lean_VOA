import VOA.Huang.GenusOneG1bRational

/-!
# One-variable power series: evaluation, the real identity theorem, weighted norms

Analytic tools for transporting the product Euler system to the iterate channel.

* `evS F x = Σ' k, coeff k F * x^k`; polynomial × series evaluates multiplicatively
  (`evS_pc_mul`) — only polynomial factors are ever evaluated, so no Cauchy product of
  two infinite series is needed on the analytic side.
* `eq_zero_of_evS_real`: a power series absolutely convergent at radius `ρ > 0` whose
  sum vanishes on the REAL segment `0 < x < ρ` is zero (elementary: the lowest
  coefficient is bounded by `S x / ρ^{m+1}` for every small `x > 0`).
* `NormLe r F A`: the weighted `ℓ¹` partial sums `Σ_{i<N} ‖F_i‖ r^i` are `≤ A`;
  submultiplicative (`NormLe.mul`), with `(1+X)^e ↦ (1+r)^e` and
  `(1+X)⁻¹ ↦ (1−r)⁻¹`.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open scoped BigOperators
open VOA.Huang.GenusOneWard (pc coeff_pc)

/-- Evaluation of a power series at a complex point. -/
def evS (F : PowerSeries ℂ) (x : ℂ) : ℂ := ∑' k, PowerSeries.coeff k F * x ^ k

/-- Summability at a point. -/
def SumAt (F : PowerSeries ℂ) (x : ℂ) : Prop :=
  Summable fun k => PowerSeries.coeff k F * x ^ k

theorem SumAt.add {F G : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (hG : SumAt G x) :
    SumAt (F + G) x := by
  unfold SumAt at *
  simpa only [map_add, add_mul] using hF.add hG

theorem evS_add {F G : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (hG : SumAt G x) :
    evS (F + G) x = evS F x + evS G x := by
  unfold evS
  simp only [map_add, add_mul]
  exact hF.tsum_add hG

theorem SumAt.smul {F : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (c : ℂ) :
    SumAt (c • F) x := by
  unfold SumAt at *
  simpa only [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc] using hF.mul_left c

theorem evS_smul (F : PowerSeries ℂ) (x c : ℂ) : evS (c • F) x = c * evS F x := by
  unfold evS
  simp only [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem SumAt.sum {κ : Type*} (s : Finset κ) {F : κ → PowerSeries ℂ} {x : ℂ}
    (h : ∀ i ∈ s, SumAt (F i) x) : SumAt (∑ i ∈ s, F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SumAt, summable_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem evS_sum {κ : Type*} (s : Finset κ) {F : κ → PowerSeries ℂ} {x : ℂ}
    (h : ∀ i ∈ s, SumAt (F i) x) : evS (∑ i ∈ s, F i) x = ∑ i ∈ s, evS (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evS]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evS_add (h a (Finset.mem_insert_self a s))
        (SumAt.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem shift_fun (F : PowerSeries ℂ) (x : ℂ) (s k : ℕ) :
    PowerSeries.coeff (k + s) (PowerSeries.X ^ s * F) * x ^ (k + s) =
      x ^ s * (PowerSeries.coeff k F * x ^ k) := by
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel, pow_add]
  ring

theorem SumAt.X_pow_mul {F : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (s : ℕ) :
    SumAt (PowerSeries.X ^ s * F) x := by
  unfold SumAt at *
  rw [← summable_nat_add_iff s]
  simpa only [shift_fun] using hF.mul_left (x ^ s)

theorem evS_X_pow_mul {F : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (s : ℕ) :
    evS (PowerSeries.X ^ s * F) x = x ^ s * evS F x := by
  unfold evS
  rw [← (hF.X_pow_mul s).sum_add_tsum_nat_add s]
  have h0 : ∑ i ∈ Finset.range s, PowerSeries.coeff i (PowerSeries.X ^ s * F) * x ^ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_mul]
  rw [h0, zero_add]
  simp only [shift_fun]
  exact tsum_mul_left

theorem pc_eq_sum (P : Polynomial ℂ) :
    pc P = ∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i • PowerSeries.X ^ i := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, PowerSeries.smul_eq_C_mul]
  simp [pc]

theorem SumAt.pc_mul {F : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (P : Polynomial ℂ) :
    SumAt (pc P * F) x := by
  rw [pc_eq_sum, Finset.sum_mul]
  refine SumAt.sum _ fun i _ => ?_
  rw [smul_mul_assoc]
  exact (hF.X_pow_mul i).smul _

/-- Polynomial × series evaluates multiplicatively. -/
theorem evS_pc_mul {F : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (P : Polynomial ℂ) :
    evS (pc P * F) x = P.eval x * evS F x := by
  rw [pc_eq_sum, Finset.sum_mul,
    evS_sum _ fun i _ => by rw [smul_mul_assoc]; exact (hF.X_pow_mul i).smul _]
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [Polynomial.eval_finset_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, evS_smul, evS_X_pow_mul hF]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem SumAt.of_bound {F : PowerSeries ℂ} {x : ℂ} {r B : ℝ} (hr : ‖x‖ < r)
    (hB : ∀ k, ‖PowerSeries.coeff k F‖ * r ^ k ≤ B) : SumAt F x := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hr
  have hq : ‖x‖ / r < 1 := (div_lt_one hr0).2 hr
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity) hq).mul_left B)
    fun k => ?_
  rw [norm_mul, norm_pow, div_pow]
  have hrk : 0 < r ^ k := pow_pos hr0 k
  calc ‖PowerSeries.coeff k F‖ * ‖x‖ ^ k
      = (‖PowerSeries.coeff k F‖ * r ^ k) * (‖x‖ ^ k / r ^ k) := by
        field_simp
    _ ≤ B * (‖x‖ ^ k / r ^ k) := mul_le_mul_of_nonneg_right (hB k) (by positivity)

/-! ## The identity theorem on a real segment -/

/-- Tail estimate for an absolutely convergent series. -/
theorem tail_bound {F : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : Summable fun k => ‖PowerSeries.coeff k F‖ * ρ ^ k) (m : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hxρ : x < ρ) :
    ‖∑' i, PowerSeries.coeff (i + m) F * (x : ℂ) ^ (i + m)‖ ≤
      (∑' k, ‖PowerSeries.coeff k F‖ * ρ ^ k) * (x / ρ) ^ m := by
  set q := x / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := (div_le_one hρ).2 hxρ.le
  set a : ℕ → ℝ := fun i => ‖PowerSeries.coeff (i + m) F‖ * ρ ^ (i + m) with ha
  have hsh : Summable a := (summable_nat_add_iff m).2 hF
  have hbd : ∀ i, ‖PowerSeries.coeff (i + m) F * (x : ℂ) ^ (i + m)‖ ≤ a i * q ^ m := by
    intro i
    have hx : x = ρ * q := by rw [hq]; field_simp
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le, hx, mul_pow,
      pow_add q i m]
    have h1 : q ^ i ≤ 1 := pow_le_one₀ hq0 hq1
    have h2 : 0 ≤ a i := by simp only [ha]; positivity
    have h3 : 0 ≤ q ^ m := pow_nonneg hq0 m
    calc ‖PowerSeries.coeff (i + m) F‖ * (ρ ^ (i + m) * (q ^ i * q ^ m))
        = a i * q ^ m * q ^ i := by simp only [ha]; ring
      _ ≤ a i * q ^ m * 1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
      _ = a i * q ^ m := mul_one _
  have hle : ∑' i, a i ≤ ∑' k, ‖PowerSeries.coeff k F‖ * ρ ^ k := by
    rw [← hF.sum_add_tsum_nat_add m]
    have : 0 ≤ ∑ i ∈ Finset.range m, ‖PowerSeries.coeff i F‖ * ρ ^ i :=
      Finset.sum_nonneg fun i _ => by positivity
    simp only [ha]
    linarith
  calc _ ≤ ∑' i, a i * q ^ m := tsum_of_norm_bounded (hsh.mul_right _).hasSum hbd
    _ = (∑' i, a i) * q ^ m := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (pow_nonneg hq0 m)

/-- The lowest coefficient of a series vanishing at `x` is `O(x)`. -/
theorem lowest_coeff_bound {F : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : Summable fun k => ‖PowerSeries.coeff k F‖ * ρ ^ k) {m : ℕ}
    (hlow : ∀ i < m, PowerSeries.coeff i F = 0) {x : ℝ} (hx0 : 0 < x) (hxρ : x < ρ)
    (h0 : evS F x = 0) :
    ‖PowerSeries.coeff m F‖ ≤
      (∑' k, ‖PowerSeries.coeff k F‖ * ρ ^ k) / ρ ^ (m + 1) * x := by
  set S := ∑' k, ‖PowerSeries.coeff k F‖ * ρ ^ k with hS
  have hsum : SumAt F (x : ℂ) := SumAt.of_bound (r := ρ) (B := S)
    (by rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]; exact hxρ)
    (fun k => hF.le_tsum k fun j _ => by positivity)
  unfold evS at h0
  rw [← hsum.sum_add_tsum_nat_add (m + 1), Finset.sum_range_succ] at h0
  have hlow' : ∑ i ∈ Finset.range m, PowerSeries.coeff i F * (x : ℂ) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hlow i (Finset.mem_range.mp hi), zero_mul]
  rw [hlow', zero_add] at h0
  have heq : PowerSeries.coeff m F * (x : ℂ) ^ m =
      -∑' i, PowerSeries.coeff (i + (m + 1)) F * (x : ℂ) ^ (i + (m + 1)) := by
    linear_combination h0
  have hn : ‖PowerSeries.coeff m F‖ * x ^ m ≤ S * (x / ρ) ^ (m + 1) := by
    have h1 := congrArg norm heq
    rw [norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le] at h1
    rw [h1]
    exact tail_bound hρ hF (m + 1) hx0 hxρ
  have hxm : 0 < x ^ m := pow_pos hx0 m
  have hr : S * (x / ρ) ^ (m + 1) = (S / ρ ^ (m + 1) * x) * x ^ m := by
    rw [div_pow, pow_succ x m]; ring
  rw [hr] at hn
  exact le_of_mul_le_mul_right hn hxm

/-- **Identity theorem on a real segment.** -/
theorem eq_zero_of_evS_real {F : PowerSeries ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hF : Summable fun k => ‖PowerSeries.coeff k F‖ * ρ ^ k)
    (h : ∀ x : ℝ, 0 < x → x < ρ → evS F x = 0) : F = 0 := by
  have key : ∀ m, PowerSeries.coeff m F = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    set c := (∑' k, ‖PowerSeries.coeff k F‖ * ρ ^ k) / ρ ^ (m + 1) with hc
    have hlim : Filter.Tendsto (fun x : ℝ => c * x) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    rw [mul_zero] at hlim
    have h1 : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < ρ :=
      nhdsWithin_le_nhds (Iio_mem_nhds hρ)
    have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖PowerSeries.coeff m F‖ ≤ c * x := by
      filter_upwards [self_mem_nhdsWithin, h1] with x hx hxρ
      exact lowest_coeff_bound hρ hF ih hx hxρ (h x hx hxρ)
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim hev)
  ext m
  rw [key m, map_zero]

/-! ## Weighted `ℓ¹` norms -/

/-- All weighted partial sums `Σ_{i<N} ‖F_i‖ r^i` are `≤ A`. -/
def NormLe (r : ℝ) (F : PowerSeries ℂ) (A : ℝ) : Prop :=
  ∀ N, ∑ i ∈ Finset.range N, ‖PowerSeries.coeff i F‖ * r ^ i ≤ A

theorem NormLe.nonneg {r A : ℝ} {F : PowerSeries ℂ} (h : NormLe r F A) : 0 ≤ A := by
  simpa using h 0

theorem NormLe.mono {r A B : ℝ} {F : PowerSeries ℂ} (h : NormLe r F A) (hAB : A ≤ B) :
    NormLe r F B := fun N => (h N).trans hAB

theorem NormLe.summable {r A : ℝ} {F : PowerSeries ℂ} (hr : 0 ≤ r) (h : NormLe r F A) :
    Summable fun i => ‖PowerSeries.coeff i F‖ * r ^ i :=
  summable_of_sum_range_le (fun i => by positivity) h

theorem NormLe.tsum_le {r A : ℝ} {F : PowerSeries ℂ} (hr : 0 ≤ r) (h : NormLe r F A) :
    ∑' i, ‖PowerSeries.coeff i F‖ * r ^ i ≤ A :=
  Real.tsum_le_of_sum_range_le (fun i => by positivity) h

theorem NormLe.add {r A B : ℝ} {F G : PowerSeries ℂ} (hF : NormLe r F A) (hG : NormLe r G B)
    (hr : 0 ≤ r) : NormLe r (F + G) (A + B) := fun N => by
  calc ∑ i ∈ Finset.range N, ‖PowerSeries.coeff i (F + G)‖ * r ^ i
      ≤ ∑ i ∈ Finset.range N, (‖PowerSeries.coeff i F‖ * r ^ i +
          ‖PowerSeries.coeff i G‖ * r ^ i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_add, ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ ≤ A + B := by rw [Finset.sum_add_distrib]; exact add_le_add (hF N) (hG N)

theorem NormLe.smul {r A : ℝ} {F : PowerSeries ℂ} (hF : NormLe r F A) (c : ℂ) :
    NormLe r (c • F) (‖c‖ * A) := fun N => by
  simp only [PowerSeries.coeff_smul, smul_eq_mul, norm_mul, mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hF N) (norm_nonneg c)

theorem NormLe.sum {κ : Type*} (s : Finset κ) {r : ℝ} (hr : 0 ≤ r) {F : κ → PowerSeries ℂ}
    {A : κ → ℝ} (h : ∀ i ∈ s, NormLe r (F i) (A i)) :
    NormLe r (∑ i ∈ s, F i) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro N; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) hr

/-- Submultiplicativity of the weighted `ℓ¹` norm. -/
theorem NormLe.mul {r A B : ℝ} {F G : PowerSeries ℂ} (hr : 0 ≤ r) (hF : NormLe r F A)
    (hG : NormLe r G B) : NormLe r (F * G) (A * B) := by
  set f : ℕ → ℝ := fun i => ‖PowerSeries.coeff i F‖ * r ^ i
  set g : ℕ → ℝ := fun i => ‖PowerSeries.coeff i G‖ * r ^ i
  have hf : Summable fun i => ‖f i‖ := by
    simpa [f, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ _)] using hF.summable hr
  have hg : Summable fun i => ‖g i‖ := by
    simpa [g, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ _)] using hG.summable hr
  have hfg := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hterm : ∀ n, ‖PowerSeries.coeff n (F * G)‖ * r ^ n ≤
      ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
    intro n
    rw [PowerSeries.coeff_mul]
    calc ‖∑ kl ∈ Finset.antidiagonal n, PowerSeries.coeff kl.1 F * PowerSeries.coeff kl.2 G‖ *
          r ^ n
        ≤ (∑ kl ∈ Finset.antidiagonal n,
            ‖PowerSeries.coeff kl.1 F‖ * ‖PowerSeries.coeff kl.2 G‖) * r ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ = ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun kl hkl => ?_
          rw [Finset.mem_antidiagonal] at hkl
          simp only [f, g]
          rw [← hkl, pow_add]; ring
  intro N
  have hnn : ∀ n, 0 ≤ ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 :=
    fun n => Finset.sum_nonneg fun kl _ => by simp only [f, g]; positivity
  have hfg' : Summable fun n => ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
    refine hfg.congr fun n => ?_
    exact Real.norm_of_nonneg (hnn n)
  calc ∑ i ∈ Finset.range N, ‖PowerSeries.coeff i (F * G)‖ * r ^ i
      ≤ ∑ i ∈ Finset.range N, ∑ kl ∈ Finset.antidiagonal i, f kl.1 * g kl.2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ ∑' n, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 :=
        hfg'.sum_le_tsum _ fun n _ => hnn n
    _ = (∑' n, f n) * ∑' n, g n := htsum.symm
    _ ≤ A * B := mul_le_mul (hF.tsum_le hr) (hG.tsum_le hr)
          (tsum_nonneg fun n => by simp only [g]; positivity) hF.nonneg

theorem NormLe.pow {r A : ℝ} {F : PowerSeries ℂ} (hr : 0 ≤ r) (hF : NormLe r F A) (e : ℕ) :
    NormLe r (F ^ e) (A ^ e) := by
  induction e with
  | zero =>
    intro N
    rw [pow_zero, pow_zero]
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [PowerSeries.coeff_one, pow_zero, mul_one]
      rw [Finset.sum_eq_zero fun i _ => by simp]
      simp
  | succ e ih => rw [pow_succ, pow_succ]; exact ih.mul hr hF

theorem normLe_one_add_X {r : ℝ} (hr : 0 ≤ r) : NormLe r (1 + PowerSeries.X) (1 + r) := by
  intro N
  calc ∑ i ∈ Finset.range N, ‖PowerSeries.coeff i (1 + PowerSeries.X)‖ * r ^ i
      ≤ ∑ i ∈ Finset.range (N + 2), ‖PowerSeries.coeff i (1 + PowerSeries.X : PowerSeries ℂ)‖ *
          r ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun i _ _ => by positivity
    _ = 1 + r := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        rw [Finset.sum_eq_zero fun i _ => by
          simp [PowerSeries.coeff_one, PowerSeries.coeff_X]]
        simp [PowerSeries.coeff_one, PowerSeries.coeff_X]
        ring

/-- The inverse series `Σ (−1)^i X^i` of `1 + X`. -/
def invOnePlusX : PowerSeries ℂ := PowerSeries.mk fun i => (-1 : ℂ) ^ i

theorem one_add_X_mul_inv : (1 + PowerSeries.X) * invOnePlusX = 1 := by
  ext k
  rw [add_mul, one_mul, map_add]
  cases k with
  | zero => simp [invOnePlusX]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [invOnePlusX, pow_succ]

theorem normLe_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : NormLe r invOnePlusX (1 - r)⁻¹ := by
  intro N
  have h := Summable.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hr0 i)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [tsum_geometric_of_lt_one hr0 hr1] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [invOnePlusX]

end VOA.Huang.GenusOneG1b
