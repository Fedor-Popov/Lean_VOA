import VOA.Moonshine.MoonshineCNReplicationFormal
import VOA.Moonshine.MoonshineCNGenusZeroAnalytic

/-!
# Analytic replication from the twisted denominator identity

For an automorphism `g` of `V♮` of finite order, the coefficients of every McKay–Thompson series
`T_{g^a}` are dominated by those of `J` (`isJDominated_mckayThompson`), so all the series involved
converge absolutely on `ℍ`.  Two expansions are compared:

* the Hecke side: `Σ_{a ∣ m} Σ_{b < m/a} T_{g^a}((aτ+b)/(m/a))`
  `= q^{−m} + Σ_N [p^m q^N] P̃ · q^{N−m}`,
  by the character sum `Σ_{b < d} e^{2πinb/d} = d·[d ∣ n]` (`hasSum_heckeSum`);
* the Faber side: `q^m F_m(T_g(τ))` is the value at `q` of the power series `q^m F_m(f)`, which the
  formal replication identity computes as `1 + [p^m] P̃` (`hasSum_faberPoly_eval`).

Hence the twisted denominator identity of the family `k ↦ T_{g^k}` gives the replication formula of
`g` for every `m` (`faberPoly_eval_mckayThompsonFun`), and identities for all finite-order `g` give
`CompletelyReplicableOfFinOrder` (`completelyReplicableOfFinOrder_of_twistedDenominator`).
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Polynomial AutMonster
open scoped Real

/-! ### Absolutely convergent evaluation of power series -/

/-- `Σ aₙ qⁿ` converges absolutely, with sum `α`. -/
def HasAbsEvalAt (A : PowerSeries ℂ) (q α : ℂ) : Prop :=
  Summable (fun n => ‖PowerSeries.coeff n A * q ^ n‖) ∧
    HasSum (fun n => PowerSeries.coeff n A * q ^ n) α

namespace HasAbsEvalAt

variable {A B : PowerSeries ℂ} {q α β : ℂ}

theorem add (hA : HasAbsEvalAt A q α) (hB : HasAbsEvalAt B q β) :
    HasAbsEvalAt (A + B) q (α + β) := by
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hA.1.add hB.1)
    rw [map_add, add_mul]
    exact norm_add_le _ _
  · simpa only [map_add, add_mul] using hA.2.add hB.2

theorem mul (hA : HasAbsEvalAt A q α) (hB : HasAbsEvalAt B q β) :
    HasAbsEvalAt (A * B) q (α * β) := by
  have hterm : ∀ n, PowerSeries.coeff n (A * B) * q ^ n =
      ∑ kl ∈ Finset.antidiagonal n,
        (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hA.1 hB.1
  refine ⟨?_, ?_⟩
  · simpa only [hterm] using hs
  · have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA.1 hB.1
    rw [hA.2.tsum_eq, hB.2.tsum_eq] at h
    rw [h]
    simp only [hterm]
    exact hs.of_norm.hasSum

theorem const (a : ℂ) : HasAbsEvalAt (PowerSeries.C a) q a := by
  have h0 : ∀ n, n ≠ 0 → PowerSeries.coeff n (PowerSeries.C a) * q ^ n = 0 := fun n hn => by
    simp [PowerSeries.coeff_C, hn]
  refine ⟨(hasSum_single 0 fun n hn => by rw [h0 n hn, norm_zero]).summable, ?_⟩
  convert hasSum_single 0 h0 using 1
  simp

theorem one : HasAbsEvalAt 1 q 1 := by
  simpa using const (q := q) 1

theorem zero : HasAbsEvalAt 0 q 0 := by
  simpa using const (q := q) 0

theorem X : HasAbsEvalAt PowerSeries.X q q := by
  have h0 : ∀ n, n ≠ 1 → PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * q ^ n = 0 :=
    fun n hn => by simp [PowerSeries.coeff_X, hn]
  refine ⟨(hasSum_single 1 fun n hn => by rw [h0 n hn, norm_zero]).summable, ?_⟩
  convert hasSum_single 1 h0 using 1
  simp

theorem pow (hA : HasAbsEvalAt A q α) (n : ℕ) : HasAbsEvalAt (A ^ n) q (α ^ n) := by
  induction n with
  | zero => simpa using one (q := q)
  | succ n ih => simpa [pow_succ] using ih.mul hA

theorem sum {ι : Type*} (s : Finset ι) {A : ι → PowerSeries ℂ} {α : ι → ℂ}
    (h : ∀ i ∈ s, HasAbsEvalAt (A i) q (α i)) :
    HasAbsEvalAt (∑ i ∈ s, A i) q (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (q := q)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end HasAbsEvalAt

/-! ### `J`-dominated `q`-series with a simple pole -/

/-- `q⁻¹ + Σ_{n ≥ 0} c(n) qⁿ` on `ℍ`; for the McKay–Thompson coefficients this is
`mckayThompsonFun`. -/
def poleQSeriesFun (c : ℕ → ℂ) (τ : ℍ) : ℂ :=
  (qPar τ)⁻¹ + ∑' n : ℕ, c n * qPar τ ^ n

theorem mckayThompsonFun_eq_poleQSeriesFun (g : AutVnat) :
    mckayThompsonFun g = poleQSeriesFun fun n => PowerSeries.coeff n (mckayThompson g) :=
  rfl

theorem qPar_ne_zero (τ : ℍ) : qPar τ ≠ 0 := by
  simp [qPar, Function.Periodic.qParam, Complex.exp_ne_zero]

/-- Finite-order McKay–Thompson coefficients are dominated by those of `J`. -/
theorem isJDominated_mckayThompson (h : AutVnat) (hh : IsOfFinOrder h) :
    IsJDominated (fun n => PowerSeries.coeff n (mckayThompson h)) := fun n => by
  have := mckayThompson_coeff_norm_le h hh (n + 1)
  rw [mckayThompson_one, PowerSeries.coeff_mk] at this
  exact this

theorem summable_norm_coeff_mul_qPar {c : ℕ → ℂ} (hc : IsJDominated c) (τ : ℍ) :
    Summable fun n => ‖c n * qPar τ ^ n‖ := by
  rw [← summable_nat_add_iff 1]
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (norm_qTail_term_le hc (norm_qPar_eq τ).le) (summable_jCoeffMajorant_mul_exp τ.im_pos)

/-- `u = q f` is evaluated at `q` to `q · f(τ)`. -/
theorem hasAbsEvalAt_qSeriesUnit {c : ℕ → ℂ} (hc : IsJDominated c) (hc0 : c 0 = 0) (τ : ℍ) :
    HasAbsEvalAt (M8.qSeriesUnit c) (qPar τ) (qPar τ * poleQSeriesFun c τ) := by
  have hs := summable_norm_coeff_mul_qPar hc τ
  have hcoeff : ∀ n, PowerSeries.coeff (n + 1) (M8.qSeriesUnit c) * qPar τ ^ (n + 1) =
      qPar τ * (c n * qPar τ ^ n) := by
    intro n
    rcases n with _ | n
    · simp [M8.qSeriesUnit, hc0]
    · simp only [M8.qSeriesUnit, PowerSeries.coeff_mk, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, add_eq_right, Nat.add_sub_cancel]
      ring
  refine ⟨?_, ?_⟩
  · rw [← summable_nat_add_iff 1]
    simp only [hcoeff]
    simpa only [norm_mul] using hs.mul_left ‖qPar τ‖
  · rw [← hasSum_nat_add_iff' 1]
    simp only [hcoeff, Finset.range_one, Finset.sum_singleton]
    have h0 : PowerSeries.coeff 0 (M8.qSeriesUnit c) * qPar τ ^ 0 = 1 := by
      simp [M8.qSeriesUnit]
    rw [h0, poleQSeriesFun, mul_add, mul_inv_cancel₀ (qPar_ne_zero τ), add_sub_cancel_left]
    exact hs.of_norm.hasSum.mul_left (qPar τ)

/-- The homogenized evaluation of `P` (`deg P ≤ m`) is evaluated at `q` to `q^m P(f(τ))`. -/
theorem hasAbsEvalAt_homogenizedEval {c : ℕ → ℂ} (hc : IsJDominated c) (hc0 : c 0 = 0)
    (τ : ℍ) (m : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ m) :
    HasAbsEvalAt (homogenizedEval c m P) (qPar τ) (qPar τ ^ m * P.eval (poleQSeriesFun c τ)) := by
  have hu := hasAbsEvalAt_qSeriesUnit hc hc0 τ
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum, homogenizedEval]
  refine HasAbsEvalAt.sum _ fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h := ((HasAbsEvalAt.const (q := qPar τ) (P.coeff j)).mul
    (HasAbsEvalAt.X.pow (m - j))).mul (hu.pow j)
  convert h using 1
  have hpow : qPar τ ^ m = qPar τ ^ (m - j) * qPar τ ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjm]
  rw [hpow, mul_pow]
  ring

/-! ### The Hecke side -/

theorem qPar_heckePoint_eq_exp_mul (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    qPar (heckePoint a d b ha hd τ) =
      Complex.exp (2 * π * Complex.I * (a * τ) / d) * Complex.exp (2 * π * Complex.I / d) ^ b := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [qPar, Function.Periodic.qParam, coe_heckePoint, Complex.ofReal_one, div_one,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  field_simp

theorem exp_heckeShift_pow (a d : ℕ) (hd : 0 < d) (τ : ℍ) :
    Complex.exp (2 * π * Complex.I * (a * τ) / d) ^ d = qPar τ ^ a := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [qPar, Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  field_simp

/-- The character sum `Σ_{b < d} (ζ^b)ⁿ = d·[d ∣ n]`, `ζ = e^{2πi/d}`. -/
theorem sum_range_exp_pow (d : ℕ) (hd : 0 < d) (n : ℕ) :
    ∑ b ∈ Finset.range d, (Complex.exp (2 * π * Complex.I / d) ^ b) ^ n =
      if d ∣ n then (d : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / d)) d :=
    Complex.isPrimitiveRoot_exp d hd.ne'
  have hswap : ∀ b, (Complex.exp (2 * π * Complex.I / d) ^ b) ^ n =
      (Complex.exp (2 * π * Complex.I / d) ^ n) ^ b := fun b => pow_right_comm _ _ _
  simp_rw [hswap]
  split_ifs with hdn
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr hdn]
    simp
  · have hne : Complex.exp (2 * π * Complex.I / d) ^ n ≠ 1 :=
      fun h => hdn ((hζ.pow_eq_one_iff_dvd n).mp h)
    rw [geom_sum_eq hne, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

/-- The regular parts of the Hecke cosets with fixed `a`:
`Σ_{b<d} Σ_n c(n) q_bⁿ = Σ_k d c(dk) q^{ak}`. -/
theorem hasSum_heckeCosetSum_regular {c : ℕ → ℂ} (hc : IsJDominated c) {a d : ℕ} (ha : 0 < a)
    (hd : 0 < d)
    (τ : ℍ) :
    HasSum (fun k => (d : ℂ) * c (d * k) * qPar τ ^ (a * k))
      (∑ b ∈ Finset.range d, ∑' n : ℕ, c n * qPar (heckePoint a d b ha hd τ) ^ n) := by
  set w := Complex.exp (2 * π * Complex.I * (a * τ) / d) with hw
  have h1 : HasSum (fun n => ∑ b ∈ Finset.range d, c n * qPar (heckePoint a d b ha hd τ) ^ n)
      (∑ b ∈ Finset.range d, ∑' n : ℕ, c n * qPar (heckePoint a d b ha hd τ) ^ n) :=
    hasSum_sum fun b _ => (summable_norm_coeff_mul_qPar hc _).of_norm.hasSum
  have h2 : ∀ n, ∑ b ∈ Finset.range d, c n * qPar (heckePoint a d b ha hd τ) ^ n =
      if d ∣ n then (d : ℂ) * c n * w ^ n else 0 := by
    intro n
    simp only [qPar_heckePoint_eq_exp_mul, ← hw, mul_pow, ← Finset.mul_sum,
      sum_range_exp_pow d hd n]
    split_ifs <;> ring
  simp only [h2] at h1
  have hinj : Function.Injective (fun k : ℕ => d * k) :=
    fun k l h => Nat.eq_of_mul_eq_mul_left hd h
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => d * k),
      (if d ∣ n then (d : ℂ) * c n * w ^ n else 0) = 0 := by
    intro n hn
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hn ⟨k, rfl⟩
  have h3 := (hinj.hasSum_iff hzero).mpr h1
  refine h3.congr_fun fun k => ?_
  simp only [Function.comp_apply, dvd_mul_right, ↓reduceIte, pow_mul, hw,
    exp_heckeShift_pow a d hd τ]

/-- `Σ_{b < d} (q_b)⁻¹` is `(q^a)⁻¹` for `d = 1` and `0` for `d > 1`. -/
theorem sum_inv_qPar_heckePoint {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ∑ b ∈ Finset.range d, (qPar (heckePoint a d b ha hd τ))⁻¹ =
      if d = 1 then (qPar τ ^ a)⁻¹ else 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / d)) d :=
    Complex.isPrimitiveRoot_exp d hd.ne'
  simp only [qPar_heckePoint_eq_exp_mul]
  split_ifs with h1
  · subst h1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one]
    rw [← exp_heckeShift_pow a 1 one_pos τ, pow_one]
  · have hinv : ∀ b, (Complex.exp (2 * π * Complex.I * (a * τ) / d) *
        Complex.exp (2 * π * Complex.I / d) ^ b)⁻¹ =
        (Complex.exp (2 * π * Complex.I * (a * τ) / d))⁻¹ *
          (Complex.exp (2 * π * Complex.I / d) ^ b) ^ (d - 1) := by
      intro b
      have h : (Complex.exp (2 * π * Complex.I / d) ^ b) ^ (d - 1) *
          Complex.exp (2 * π * Complex.I / d) ^ b = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hd, pow_right_comm, hζ.pow_eq_one, one_pow]
      rw [mul_inv, inv_eq_of_mul_eq_one_left h]
    simp only [hinv, ← Finset.mul_sum]
    rw [sum_range_exp_pow d hd (d - 1),
      if_neg (Nat.not_dvd_of_pos_of_lt (show 0 < d - 1 by omega) (show d - 1 < d by omega)),
      mul_zero]

/-- The Hecke sum of a family of `J`-dominated series with simple poles:
`q^m Σ_{a ∣ m} Σ_{b < m/a} T_a((aτ+b)/(m/a)) − 1 = Σ_N [p^m q^N] P̃ · q^N`. -/
theorem hasSum_heckeSum (c : ℕ → ℕ → ℂ) (hc : ∀ a, IsJDominated (c a)) (hc0 : ∀ a, c a 0 = 0)
    (m : ℕ) (hm : 0 < m) (τ : ℍ) :
    HasSum (fun N => PowerSeries.coeff N (PowerSeries.coeff m (twistedPowerSum c)) * qPar τ ^ N)
      (qPar τ ^ m * (∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
        poleQSeriesFun (c a) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)) - 1) := by
  set q := qPar τ with hq
  -- each block
  have hblock : ∀ a ∈ m.divisors.attach, HasSum
      (fun N => (if (a : ℕ) ∣ N ∧ m < N then
          ((m / a : ℕ) : ℂ) * c a (m / a * ((N - m) / a)) else 0) * q ^ N)
      (q ^ m * ∑ b ∈ Finset.range (m / a), ∑' n : ℕ, c a n *
        qPar (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) ^ n) := by
    intro a _
    have ha : 0 < (a : ℕ) := Nat.pos_of_mem_divisors a.2
    have ham : (a : ℕ) ∣ m := Nat.dvd_of_mem_divisors a.2
    have hd : 0 < m / a := Nat.div_pos (Nat.divisor_le a.2) ha
    have h := (hasSum_heckeCosetSum_regular (hc a) ha hd τ).mul_left (q ^ m)
    rw [← (show Function.Injective (fun k => (a : ℕ) * k + m) from fun k l hkl => by
      simpa [ha.ne'] using hkl).hasSum_iff]
    · refine h.congr_fun fun k => ?_
      simp only [Function.comp_apply]
      rcases k with _ | k
      · simp [hc0]
      · rw [if_pos ⟨dvd_add (dvd_mul_right _ _) ham, by nlinarith⟩, Nat.add_sub_cancel,
          Nat.mul_div_cancel_left _ ha, pow_add, pow_mul]
        ring
    · intro N hN
      rw [if_neg, zero_mul]
      rintro ⟨hdvd, hlt⟩
      have h' : (a : ℕ) ∣ N - m :=
        (Nat.dvd_add_right ham).mp (by rwa [Nat.add_sub_cancel' hlt.le])
      obtain ⟨k, hk⟩ := h'
      refine hN ⟨k, ?_⟩
      simp only
      rw [← hk]
      omega
  have hsum := hasSum_sum hblock
  have hcoeff : ∀ N, ∑ a ∈ m.divisors.attach, (if (a : ℕ) ∣ N ∧ m < N then
        ((m / a : ℕ) : ℂ) * c a (m / a * ((N - m) / a)) else 0) * q ^ N =
      PowerSeries.coeff N (PowerSeries.coeff m (twistedPowerSum c)) * q ^ N := by
    intro N
    rw [← Finset.sum_mul, Finset.sum_attach m.divisors
      (fun a => if a ∣ N ∧ m < N then ((m / a : ℕ) : ℂ) * c a (m / a * ((N - m) / a)) else 0)]
    simp [twistedPowerSum]
  simp only [hcoeff] at hsum
  convert hsum using 1
  -- the polar parts
  have hpole : ∀ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
      poleQSeriesFun (c a) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
        (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) =
      (if m / a = 1 then (q ^ (a : ℕ))⁻¹ else 0) +
        ∑ b ∈ Finset.range (m / a), ∑' n : ℕ, c a n *
          qPar (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
            (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) ^ n := by
    intro a _
    simp only [poleQSeriesFun, Finset.sum_add_distrib]
    rw [sum_inv_qPar_heckePoint]
  have hpolar : ∑ a ∈ m.divisors.attach, (if m / (a : ℕ) = 1 then (q ^ (a : ℕ))⁻¹ else 0) =
      (q ^ m)⁻¹ := by
    rw [Finset.sum_eq_single ⟨m, Nat.mem_divisors_self m hm.ne'⟩]
    · simp [Nat.div_self hm]
    · intro a _ hne
      rw [if_neg]
      intro h1
      apply hne
      apply Subtype.ext
      have h2 := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors a.2)
      rw [h1, one_mul] at h2
      exact h2
    · intro h
      exact absurd (Finset.mem_attach _ _) h
  rw [Finset.sum_congr rfl hpole, Finset.sum_add_distrib, hpolar, mul_add,
    mul_inv_cancel₀ (pow_ne_zero _ (qPar_ne_zero τ)), add_sub_cancel_left, Finset.mul_sum]

/-! ### The Faber side and the replication formula -/

/-- The McKay–Thompson coefficient family of the powers of `g`: `c k n = tr(g^k | V♮_{n+1})`. -/
def mckayThompsonFamily (g : AutVnat) : ℕ → ℕ → ℂ :=
  fun k n => PowerSeries.coeff n (mckayThompson (g ^ k))

theorem mckayThompsonFamily_one (g : AutVnat) :
    mckayThompsonFamily g 1 = fun n => PowerSeries.coeff n (mckayThompson g) := by
  funext n
  simp [mckayThompsonFamily]

/-- The Faber side: `q^m F_m(f(τ)) − 1 = Σ_N [p^m q^N] P̃ · q^N`. -/
theorem hasSum_faberPoly_eval (c : ℕ → ℕ → ℂ) (hTD : TwistedDenominatorIdentity c)
    (hc : IsJDominated (c 1)) (hc0 : c 1 0 = 0) (m : ℕ) (hm : 0 < m) (τ : ℍ) :
    HasSum (fun N => PowerSeries.coeff N (PowerSeries.coeff m (twistedPowerSum c)) * qPar τ ^ N)
      (qPar τ ^ m * (M8.faberPoly (c 1) m).eval (poleQSeriesFun (c 1) τ) - 1) := by
  have h := hasAbsEvalAt_homogenizedEval hc hc0 τ m (M8.faberPoly (c 1) m)
    (M8.faberPoly_natDegree _ _).le
  rw [homogenizedEval_faberPoly c hTD m hm] at h
  have h1 := (HasAbsEvalAt.one (q := qPar τ)).2
  convert h.2.sub h1 using 1
  funext N
  rw [map_add, add_mul]
  ring

/-- **Replication formula** for one automorphism of finite order, given the twisted denominator
identity of its power family: `F_m(T_g(τ)) = Σ_{a ∣ m} Σ_{b < m/a} T_{g^a}((aτ+b)/(m/a))`. -/
theorem faberPoly_eval_mckayThompsonFun (g : AutVnat) (hg : IsOfFinOrder g)
    (hTD : TwistedDenominatorIdentity (mckayThompsonFamily g)) (m : ℕ) (hm : 0 < m) (τ : ℍ) :
    (M8.faberPoly (mckayThompsonFamily g 1) m).eval (mckayThompsonFun g τ) =
      ∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) := by
  have hc : ∀ a, IsJDominated (mckayThompsonFamily g a) :=
    fun a => isJDominated_mckayThompson (g ^ a) hg.pow
  have hc0 : ∀ a, mckayThompsonFamily g a 0 = 0 := fun a => mckayThompson_coeff_zero (g ^ a)
  have hF := hasSum_faberPoly_eval _ hTD (hc 1) (hc0 1) m hm τ
  have hH := hasSum_heckeSum _ hc hc0 m hm τ
  have heq := hF.unique hH
  rw [sub_left_inj] at heq
  have hfun : mckayThompsonFun g = poleQSeriesFun (mckayThompsonFamily g 1) := by
    rw [mckayThompsonFamily_one]
    rfl
  rw [hfun]
  exact mul_left_cancel₀ (pow_ne_zero _ (qPar_ne_zero τ)) heq

/-- **Complete replicability for finite order, from the twisted denominator identities.** -/
theorem completelyReplicableOfFinOrder_of_twistedDenominator
    (hTD : ∀ g : AutVnat, IsOfFinOrder g → TwistedDenominatorIdentity (mckayThompsonFamily g)) :
    CompletelyReplicableOfFinOrder := by
  intro g hg m hm
  refine ⟨M8.faberPoly (mckayThompsonFamily g 1) m, M8.faberPoly_monic _ _,
    M8.faberPoly_natDegree _ _, fun τ => ?_⟩
  exact faberPoly_eval_mckayThompsonFun g hg (hTD g hg) m hm τ

/-- **Complete replicability**, when every automorphism has finite order. -/
theorem completelyReplicable_of_twistedDenominator (hfin : ∀ g : AutVnat, IsOfFinOrder g)
    (hTD : ∀ g : AutVnat, TwistedDenominatorIdentity (mckayThompsonFamily g)) :
    CompletelyReplicable := fun g m hm =>
  completelyReplicableOfFinOrder_of_twistedDenominator (fun g _ => hTD g) g (hfin g) m hm

end VOA.Moonshine.ConwayNorton
