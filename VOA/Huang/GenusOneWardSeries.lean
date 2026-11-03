import VOA.Modularity.ZhuCoefficientIdentity
import VOA.Modularity.ZhuNormalization

/-!
# Two-variable formal series for genus-one two-point traces

The ring `R2 = ℂ⟦u⟧⟦t⟧` (outer variable `u`, inner variable `t`). In the trace
application the coefficient of `u^n t^k` is the trace over the level-`n`
weight space of the traced module whose middle module is at level `k`. Then
`q = u t` is the modular variable and `t = x₂/x₁` the spatial ratio.

`lsum` is a coefficientwise-finite sum over `ℕ`. No topology is used.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open PowerSeries
open scoped BigOperators

/-- `ℂ⟦u⟧⟦t⟧`, written as power series in `u` with coefficients in `ℂ⟦t⟧`. -/
abbrev R2 := PowerSeries (PowerSeries ℂ)

/-- The coefficient of `u^n t^k`. -/
def c2 (f : R2) (n k : ℕ) : ℂ := coeff k (coeff n f)

/-- Build a series from its coefficients. -/
def mk2 (f : ℕ → ℕ → ℂ) : R2 := PowerSeries.mk fun n => PowerSeries.mk fun k => f n k

@[simp] theorem c2_mk2 (f : ℕ → ℕ → ℂ) (n k : ℕ) : c2 (mk2 f) n k = f n k := by
  simp [c2, mk2]

theorem ext2 {f g : R2} (h : ∀ n k, c2 f n k = c2 g n k) : f = g := by
  ext n k
  exact h n k

@[simp] theorem c2_add (f g : R2) (n k : ℕ) : c2 (f + g) n k = c2 f n k + c2 g n k := by
  simp [c2]

@[simp] theorem c2_sub (f g : R2) (n k : ℕ) : c2 (f - g) n k = c2 f n k - c2 g n k := by
  simp [c2]

@[simp] theorem c2_neg (f : R2) (n k : ℕ) : c2 (-f) n k = -c2 f n k := by
  simp [c2]

@[simp] theorem c2_zero (n k : ℕ) : c2 0 n k = 0 := by
  simp [c2]

@[simp] theorem c2_smul (a : ℂ) (f : R2) (n k : ℕ) : c2 (a • f) n k = a * c2 f n k := by
  simp [c2]

theorem c2_sum {ι : Type*} (s : Finset ι) (f : ι → R2) (n k : ℕ) :
    c2 (∑ i ∈ s, f i) n k = ∑ i ∈ s, c2 (f i) n k := by
  simp [c2, map_sum]

theorem c2_mul (f g : R2) (n k : ℕ) :
    c2 (f * g) n k = ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k,
      c2 f p.1 r.1 * c2 g p.2 r.2 := by
  simp only [c2, coeff_mul, map_sum]

/-- The outer variable `u`. -/
def uu : R2 := X

/-- The inner variable `t`. -/
def tt : R2 := PowerSeries.C (X : PowerSeries ℂ)

/-- The modular variable `q = u t`. -/
def qq : R2 := uu * tt

theorem c2_uu_pow_mul (a : ℕ) (f : R2) (n k : ℕ) :
    c2 (uu ^ a * f) n k = if a ≤ n then c2 f (n - a) k else 0 := by
  simp only [c2, uu, coeff_X_pow_mul']
  split_ifs <;> simp

theorem c2_tt_pow_mul (b : ℕ) (f : R2) (n k : ℕ) :
    c2 (tt ^ b * f) n k = if b ≤ k then c2 f n (k - b) else 0 := by
  simp only [c2, tt, ← map_pow, PowerSeries.coeff_C_mul, coeff_X_pow_mul']

theorem qq_pow (d : ℕ) : qq ^ d = uu ^ d * tt ^ d := by
  rw [qq, mul_pow]

theorem c2_qq_pow_mul (d : ℕ) (f : R2) (n k : ℕ) :
    c2 (qq ^ d * f) n k = if d ≤ n ∧ d ≤ k then c2 f (n - d) (k - d) else 0 := by
  rw [qq_pow, mul_assoc, c2_uu_pow_mul]
  by_cases hn : d ≤ n
  · rw [if_pos hn, c2_tt_pow_mul]
    by_cases hk : d ≤ k
    · rw [if_pos hk, if_pos ⟨hn, hk⟩]
    · rw [if_neg hk, if_neg (fun h => hk h.2)]
  · rw [if_neg hn, if_neg (fun h => hn h.1)]

@[simp] theorem c2_one (n k : ℕ) : c2 1 n k = if n = 0 ∧ k = 0 then 1 else 0 := by
  simp only [c2, coeff_one]
  split_ifs with h1 h2 h2 <;> simp_all

/-- Scalars embedded in `R2`. -/
theorem c2_algebraMap (a : ℂ) (n k : ℕ) :
    c2 (algebraMap ℂ R2 a) n k = if n = 0 ∧ k = 0 then a else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, c2_smul, c2_one]
  split_ifs <;> simp

/-! ## The geometric kernel `1 / (1 - q^d)` -/

/-- `Σ_l q^{d l}`. -/
def geo (d : ℕ) : R2 := mk2 fun n k => if n = k ∧ d ∣ n then 1 else 0

theorem c2_geo (d n k : ℕ) : c2 (geo d) n k = if n = k ∧ d ∣ n then 1 else 0 := by
  simp [geo]

theorem one_sub_qq_pow_mul_geo {d : ℕ} (hd : 1 ≤ d) : (1 - qq ^ d) * geo d = 1 := by
  apply ext2
  intro n k
  rw [sub_mul, one_mul, c2_sub, c2_qq_pow_mul, c2_geo, c2_one]
  by_cases hdn : d ≤ n ∧ d ≤ k
  · rw [if_pos hdn, c2_geo]
    have hn0 : n ≠ 0 := by omega
    have h1 : (n - d = k - d) ↔ n = k := by omega
    have h2 : d ∣ n - d ↔ d ∣ n := Nat.dvd_sub_iff_left hdn.1 (dvd_refl d)
    simp only [h1, h2, hn0, false_and, if_false]
    split_ifs <;> simp
  · rw [if_neg hdn]
    by_cases hnk : n = k ∧ d ∣ n
    · obtain ⟨rfl, hdv⟩ := hnk
      have : n = 0 := by
        by_contra h0
        exact hdn ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdv, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdv⟩
      subst this
      simp
    · rw [if_neg hnk]
      have : ¬(n = 0 ∧ k = 0) := fun h => hnk ⟨by omega, by rw [h.1]; exact dvd_zero d⟩
      rw [if_neg this]
      ring

theorem geo_mul_one_sub {d : ℕ} (hd : 1 ≤ d) : geo d * (1 - qq ^ d) = 1 := by
  rw [mul_comm, one_sub_qq_pow_mul_geo hd]

/-- Solving `(1 - q^d) a = b`. -/
theorem eq_geo_mul_of {d : ℕ} (hd : 1 ≤ d) {a b : R2} (h : (1 - qq ^ d) * a = b) :
    a = geo d * b := by
  rw [← h, ← mul_assoc, geo_mul_one_sub hd, one_mul]

theorem geo_sub_one {d : ℕ} (hd : 1 ≤ d) : geo d - 1 = qq ^ d * geo d := by
  have h := one_sub_qq_pow_mul_geo hd
  linear_combination h

/-! ## Coefficientwise-finite sums over `ℕ` -/

/-- Every coefficient is eventually zero along the family. -/
def LocFin (T : ℕ → R2) : Prop := ∀ n k, ∃ B, ∀ i, B ≤ i → c2 (T i) n k = 0

/-- The coefficientwise sum. -/
def lsum (T : ℕ → R2) : R2 := mk2 fun n k => ∑ᶠ i, c2 (T i) n k

theorem c2_lsum_eq_sum {T : ℕ → R2} {n k B : ℕ} (hB : ∀ i, B ≤ i → c2 (T i) n k = 0) :
    c2 (lsum T) n k = ∑ i ∈ Finset.range B, c2 (T i) n k := by
  rw [lsum, c2_mk2]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hi (hB i (by omega))

theorem LocFin.exists_bound {T : ℕ → R2} (hT : LocFin T) (n k : ℕ) (B₀ : ℕ) :
    ∃ B, B₀ ≤ B ∧ ∀ i, B ≤ i → c2 (T i) n k = 0 := by
  obtain ⟨B, hB⟩ := hT n k
  exact ⟨max B B₀, le_max_right _ _, fun i hi => hB i (le_trans (le_max_left _ _) hi)⟩

theorem LocFin.add {T T' : ℕ → R2} (h : LocFin T) (h' : LocFin T') :
    LocFin (fun i => T i + T' i) := by
  intro n k
  obtain ⟨B, hB⟩ := h n k
  obtain ⟨B', hB'⟩ := h' n k
  exact ⟨max B B', fun i hi => by
    rw [c2_add, hB i (le_trans (le_max_left _ _) hi), hB' i (le_trans (le_max_right _ _) hi),
      add_zero]⟩

theorem LocFin.neg {T : ℕ → R2} (h : LocFin T) : LocFin (fun i => -T i) := by
  intro n k
  obtain ⟨B, hB⟩ := h n k
  exact ⟨B, fun i hi => by rw [c2_neg, hB i hi, neg_zero]⟩

theorem LocFin.sub {T T' : ℕ → R2} (h : LocFin T) (h' : LocFin T') :
    LocFin (fun i => T i - T' i) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem LocFin.smul {T : ℕ → R2} (h : LocFin T) (a : ℕ → ℂ) :
    LocFin (fun i => a i • T i) := by
  intro n k
  obtain ⟨B, hB⟩ := h n k
  exact ⟨B, fun i hi => by rw [c2_smul, hB i hi, mul_zero]⟩

theorem LocFin.mul_left {T : ℕ → R2} (h : LocFin T) (r : R2) :
    LocFin (fun i => r * T i) := by
  intro n k
  choose B hB using h
  refine ⟨∑ p ∈ Finset.antidiagonal n, ∑ s ∈ Finset.antidiagonal k, B p.2 s.2, fun i hi => ?_⟩
  rw [c2_mul]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro s hs
  rw [hB p.2 s.2 i, mul_zero]
  refine le_trans ?_ hi
  exact le_trans (Finset.single_le_sum (f := fun s => B p.2 s.2) (fun _ _ => Nat.zero_le _) hs)
    (Finset.single_le_sum (f := fun p => ∑ s ∈ Finset.antidiagonal k, B p.2 s.2)
      (fun _ _ => Nat.zero_le _) hp)

theorem LocFin.mul_right {T : ℕ → R2} (h : LocFin T) (r : R2) :
    LocFin (fun i => T i * r) := by
  simpa only [mul_comm] using h.mul_left r

theorem LocFin.finset_sum {ι : Type*} (s : Finset ι) {T : ι → ℕ → R2}
    (h : ∀ j ∈ s, LocFin (T j)) : LocFin (fun i => ∑ j ∈ s, T j i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n k; exact ⟨0, fun i _ => by simp⟩
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert ha] using h1.add h2

theorem locFin_of_eventually_zero {T : ℕ → R2} (B : ℕ) (h : ∀ i, B ≤ i → T i = 0) :
    LocFin T := fun n k => ⟨B, fun i hi => by rw [h i hi, c2_zero]⟩

/-- Families divisible by growing powers of `u`. -/
theorem locFin_uu_pow (T : ℕ → R2) (o : ℕ → ℕ) (ho : ∀ i, i ≤ o i) :
    LocFin (fun i => uu ^ o i * T i) := by
  intro n k
  refine ⟨n + 1, fun i hi => ?_⟩
  rw [c2_uu_pow_mul, if_neg (by have := ho i; omega)]

/-- Families divisible by growing powers of `t`. -/
theorem locFin_tt_pow (T : ℕ → R2) (o : ℕ → ℕ) (ho : ∀ i, i ≤ o i) :
    LocFin (fun i => tt ^ o i * T i) := by
  intro n k
  refine ⟨k + 1, fun i hi => ?_⟩
  rw [c2_tt_pow_mul, if_neg (by have := ho i; omega)]

theorem lsum_add {T T' : ℕ → R2} (h : LocFin T) (h' : LocFin T') :
    lsum (fun i => T i + T' i) = lsum T + lsum T' := by
  apply ext2
  intro n k
  obtain ⟨B, hB⟩ := (h.add h') n k
  obtain ⟨B₁, hB₁⟩ := h n k
  obtain ⟨B₂, hB₂⟩ := h' n k
  set C := max B (max B₁ B₂)
  rw [c2_add, c2_lsum_eq_sum (B := C) (fun i hi => hB i (le_trans (le_max_left _ _) hi)),
    c2_lsum_eq_sum (B := C) (fun i hi => hB₁ i (le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) hi)),
    c2_lsum_eq_sum (B := C) (fun i hi => hB₂ i (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) hi)), ← Finset.sum_add_distrib]
  simp only [c2_add]

theorem lsum_neg {T : ℕ → R2} (h : LocFin T) : lsum (fun i => -T i) = -lsum T := by
  apply ext2
  intro n k
  obtain ⟨B, hB⟩ := h n k
  rw [c2_neg, c2_lsum_eq_sum (B := B) (fun i hi => by rw [c2_neg, hB i hi, neg_zero]),
    c2_lsum_eq_sum hB, ← Finset.sum_neg_distrib]
  simp only [c2_neg]

theorem lsum_sub {T T' : ℕ → R2} (h : LocFin T) (h' : LocFin T') :
    lsum (fun i => T i - T' i) = lsum T - lsum T' := by
  simp only [sub_eq_add_neg]
  rw [lsum_add h h'.neg, lsum_neg h']

theorem lsum_mul_left {T : ℕ → R2} (h : LocFin T) (r : R2) :
    lsum (fun i => r * T i) = r * lsum T := by
  apply ext2
  intro n k
  choose B hB using h
  set D := ∑ p ∈ Finset.antidiagonal n, ∑ s ∈ Finset.antidiagonal k, B p.2 s.2
  have hle : ∀ p ∈ Finset.antidiagonal n, ∀ s ∈ Finset.antidiagonal k, B p.2 s.2 ≤ D := by
    intro p hp s hs
    exact le_trans (Finset.single_le_sum (f := fun s => B p.2 s.2) (fun _ _ => Nat.zero_le _) hs)
      (Finset.single_le_sum (f := fun p => ∑ s ∈ Finset.antidiagonal k, B p.2 s.2)
        (fun _ _ => Nat.zero_le _) hp)
  have hz : ∀ i, D ≤ i → c2 (r * T i) n k = 0 := by
    intro i hi
    rw [c2_mul]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro s hs
    rw [hB p.2 s.2 i (le_trans (hle p hp s hs) hi), mul_zero]
  rw [c2_lsum_eq_sum hz, c2_mul]
  simp_rw [c2_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [c2_lsum_eq_sum (B := D) (fun i hi => hB p.2 s.2 i (le_trans (hle p hp s hs) hi)),
    Finset.mul_sum]

theorem lsum_mul_right {T : ℕ → R2} (h : LocFin T) (r : R2) :
    lsum (fun i => T i * r) = lsum T * r := by
  simp only [mul_comm _ r]
  exact lsum_mul_left h r

theorem lsum_smul_const {T : ℕ → R2} (h : LocFin T) (a : ℂ) :
    lsum (fun i => a • T i) = a • lsum T := by
  apply ext2
  intro n k
  obtain ⟨B, hB⟩ := h n k
  rw [c2_smul, c2_lsum_eq_sum (B := B) (fun i hi => by rw [c2_smul, hB i hi, mul_zero]),
    c2_lsum_eq_sum hB, Finset.mul_sum]
  simp only [c2_smul]

theorem lsum_finset_sum {ι : Type*} (s : Finset ι) {T : ι → ℕ → R2}
    (h : ∀ j ∈ s, LocFin (T j)) : lsum (fun i => ∑ j ∈ s, T j i) = ∑ j ∈ s, lsum (T j) := by
  classical
  induction s using Finset.induction_on with
  | empty => apply ext2; intro n k; simp [lsum]
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 : ∀ j ∈ s, LocFin (T j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert ha]
    rw [lsum_add h1 (LocFin.finset_sum s h2), ih h2]

theorem lsum_congr {T T' : ℕ → R2} (h : ∀ i, T i = T' i) : lsum T = lsum T' := by
  rw [show T = T' from funext h]

/-- Split off the first `m` terms. -/
theorem lsum_split (T : ℕ → R2) (hT : LocFin T) (m : ℕ) :
    lsum T = ∑ i ∈ Finset.range m, T i + lsum (fun i => T (i + m)) := by
  apply ext2
  intro n k
  obtain ⟨B, hB⟩ := hT n k
  rw [c2_add, c2_sum, c2_lsum_eq_sum (B := m + B) (fun i hi => hB i (by omega)),
    c2_lsum_eq_sum (B := B) (fun i hi => hB (i + m) (by omega)), Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm m i]

theorem lsum_eq_of_eventually_zero {T : ℕ → R2} (m : ℕ) (h : ∀ i, m ≤ i → T i = 0) :
    lsum T = ∑ i ∈ Finset.range m, T i := by
  have hL := locFin_of_eventually_zero m h
  rw [lsum_split T hL m]
  have : lsum (fun i => T (i + m)) = 0 := by
    apply ext2; intro n k
    rw [c2_lsum_eq_sum (B := 0) (fun i _ => by rw [h (i + m) (by omega), c2_zero])]
    simp
  rw [this, add_zero]

end VOA.Huang.GenusOneWard
