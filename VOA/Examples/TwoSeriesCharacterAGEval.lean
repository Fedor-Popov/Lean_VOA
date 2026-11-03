/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterAGSeries
import VOA.Examples.RRLowerQBinomial

/-!
# Evaluation at `x = 1`, the partition series, and the value of `A_i(1)`

A series `F ∈ ℚ⟦q⟧⟦x⟧` is **admissible** (`Adm F`) if `q^m ∣ [x^m] F` for every `m`.  On
admissible series the evaluation `x = 1`, `ev F = Σ_m [x^m] F` (coefficientwise finite), is
multiplicative (`ev_mul`).

* `FF` — the series `1/(xq)_∞ = Σ_m x^m q^m/(q)_m`, with coefficients `pc m (N - m)`
  (partitions of `N` with largest part exactly `m`); `FF_functional : (1 - xq) FF(x) = FF(xq)`,
  and `ev FF = Σ_N p(N) q^N` (`coeff_ev_FF`).
* `coeff_ev_AA` — `[q^N] A_i(1) = Σ_{s ≤ N} [q^N] (-1)^s q^{K s² + (K-i) s + s(s+1)/2}(1 - q^{(2s+1)i})`.

All proved.
-/

namespace VOA.TwoSeriesCharacter.AG

open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## §1  Admissible series -/

/-- `q^m ∣ [x^m] F` for all `m`. -/
def Adm (F : PowerSeries R) : Prop := ∀ m, qq ^ m ∣ coeff m F

theorem coeff_eq_zero_of_dvd {M N : ℕ} {f : R} (h : qq ^ M ∣ f) (hN : N < M) : coeff N f = 0 :=
  (X_pow_dvd_iff.mp (by simpa [qq] using h)) N hN

theorem Adm.coeff_eq_zero {F : PowerSeries R} (hF : Adm F) {m N : ℕ} (h : N < m) :
    coeff N (coeff m F) = 0 :=
  coeff_eq_zero_of_dvd (hF m) h

theorem Adm.add {F G : PowerSeries R} (hF : Adm F) (hG : Adm G) : Adm (F + G) :=
  fun m => by rw [map_add]; exact dvd_add (hF m) (hG m)

theorem Adm.sub {F G : PowerSeries R} (hF : Adm F) (hG : Adm G) : Adm (F - G) :=
  fun m => by rw [map_sub]; exact dvd_sub (hF m) (hG m)

theorem Adm.mul {F G : PowerSeries R} (hF : Adm F) (hG : Adm G) : Adm (F * G) := by
  intro m
  rw [coeff_mul]
  refine Finset.dvd_sum fun p hp => ?_
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  exact mul_dvd_mul (hF p.1) (hG p.2)

theorem Adm_CC (r : R) : Adm (CC r) := by
  intro m
  rw [CC, coeff_C]
  split_ifs with h
  · subst h; simp
  · exact dvd_zero _

theorem Adm_one : Adm 1 := by
  have := Adm_CC 1
  rwa [map_one] at this

theorem Adm_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (h : ∀ i ∈ s, Adm (f i)) :
    Adm (∏ i ∈ s, f i) :=
  Finset.prod_induction _ Adm (fun _ _ ha hb => ha.mul hb) Adm_one h

theorem Adm_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries R) (h : ∀ i ∈ s, Adm (f i)) :
    Adm (∑ i ∈ s, f i) := by
  intro m
  rw [map_sum]
  exact Finset.dvd_sum fun i hi => h i hi m

theorem coeff_CC_mul_xx_pow (r : R) (k m : ℕ) :
    coeff m (CC r * xx ^ k) = if m = k then r else 0 := by
  rw [CC, coeff_C_mul, xx, coeff_X_pow]
  split_ifs <;> simp

theorem Adm_monomial (r : R) (k : ℕ) (h : qq ^ k ∣ r) : Adm (CC r * xx ^ k) := by
  intro m
  rw [coeff_CC_mul_xx_pow]
  split_ifs with hm
  · subst hm; exact h
  · exact dvd_zero _

/-! ## §2  Evaluation at `x = 1` -/

/-- Partial sum `Σ_{m ≤ M} [x^m] F`. -/
def SS (M : ℕ) (F : PowerSeries R) : R := ∑ m ∈ Finset.range (M + 1), coeff m F

/-- Evaluation at `x = 1`. -/
def ev (F : PowerSeries R) : R := mk fun N => coeff N (SS N F)

theorem coeff_ev (F : PowerSeries R) (N : ℕ) : coeff N (ev F) = coeff N (SS N F) := coeff_mk _ _

theorem coeff_ev_eq {F : PowerSeries R} (hF : Adm F) {N M : ℕ} (h : N ≤ M) :
    coeff N (ev F) = coeff N (SS M F) := by
  rw [coeff_ev]
  obtain ⟨d, rfl⟩ : ∃ d, M = N + d := ⟨M - N, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [ih (by omega), SS, SS, show N + (d + 1) + 1 = (N + d + 1) + 1 by ring,
        Finset.sum_range_succ _ (N + d + 1), map_add, hF.coeff_eq_zero (by omega), add_zero]

theorem SS_mul_dvd (M : ℕ) {F G : PowerSeries R} (hF : Adm F) (hG : Adm G) :
    qq ^ (M + 1) ∣ (SS M F * SS M G - SS M (F * G)) := by
  classical
  set B := Finset.range (M + 1) ×ˢ Finset.range (M + 1) with hB
  set T := (Finset.range (M + 1)).biUnion Finset.antidiagonal with hT
  set g : ℕ × ℕ → R := fun p => coeff p.1 F * coeff p.2 G with hg
  have h1 : SS M F * SS M G = ∑ p ∈ B, g p := by
    rw [SS, SS, Finset.sum_mul_sum, hB, Finset.sum_product]
  have h2 : SS M (F * G) = ∑ p ∈ T, g p := by
    rw [SS, hT, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun m _ => coeff_mul m F G
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hpa hpb
      exact hab ((Finset.mem_antidiagonal.mp hpa).symm.trans (Finset.mem_antidiagonal.mp hpb))
  have hsub : T ⊆ B := by
    intro p hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hp
    have := Finset.mem_antidiagonal.mp hpm
    rw [Finset.mem_range] at hm
    rw [hB, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  rw [h1, h2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.dvd_sum fun p hp => ?_
  rw [Finset.mem_sdiff] at hp
  have hbig : M + 1 ≤ p.1 + p.2 := by
    by_contra hc
    apply hp.2
    exact Finset.mem_biUnion.mpr ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
      Finset.mem_antidiagonal.mpr rfl⟩
  have : qq ^ (p.1 + p.2) ∣ g p := by rw [pow_add]; exact mul_dvd_mul (hF p.1) (hG p.2)
  exact (pow_dvd_pow qq hbig).trans this

/-- **Evaluation at `x = 1` is multiplicative on admissible series.** -/
theorem ev_mul {F G : PowerSeries R} (hF : Adm F) (hG : Adm G) : ev (F * G) = ev F * ev G := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ev]
  have h0 := coeff_eq_zero_of_dvd (SS_mul_dvd N hF hG) (show N < N + 1 by omega)
  rw [map_sub, sub_eq_zero] at h0
  rw [← h0, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' := Finset.mem_antidiagonal.mp hu
  rw [coeff_ev_eq hF (show u.1 ≤ N by omega), coeff_ev_eq hG (show u.2 ≤ N by omega)]

theorem ev_add (F G : PowerSeries R) : ev (F + G) = ev F + ev G := by
  refine PowerSeries.ext fun N => ?_
  simp only [coeff_ev, SS, map_add, Finset.sum_add_distrib]

theorem ev_sub (F G : PowerSeries R) : ev (F - G) = ev F - ev G := by
  refine PowerSeries.ext fun N => ?_
  simp only [coeff_ev, SS, map_sub, Finset.sum_sub_distrib]

theorem ev_monomial (r : R) (k : ℕ) (h : qq ^ k ∣ r) : ev (CC r * xx ^ k) = r := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ev, SS]
  simp only [coeff_CC_mul_xx_pow]
  rw [Finset.sum_ite_eq' (Finset.range (N + 1)) k (fun _ => r)]
  split_ifs with hk
  · rfl
  · rw [Finset.mem_range] at hk
    rw [map_zero, coeff_eq_zero_of_dvd h (by omega)]

theorem ev_one : ev 1 = 1 := by
  have := ev_monomial 1 0 (by simp)
  simpa using this

/-! ## §3  The terms of `A_i` at `x = 1` -/

theorem Adm_PP (s : ℕ) : Adm (PP s) := by
  unfold PP
  refine Adm_prod _ _ fun j _ => Adm_one.sub ?_
  have := Adm_monomial (qq ^ (j + 1)) 1 (pow_dvd_pow qq (by omega))
  simpa using this

theorem ev_PP : ∀ s, ev (PP s) = poch s
  | 0 => by simp [PP, poch, ev_one]
  | s + 1 => by
      rw [PP_succ, ev_mul (Adm_PP s), ev_PP s, ev_sub, ev_one, poch_succ]
      · have := ev_monomial (qq ^ (s + 1)) 1 (pow_dvd_pow qq (by omega))
        rw [pow_one] at this
        rw [this]
      · refine Adm_one.sub ?_
        have := Adm_monomial (qq ^ (s + 1)) 1 (pow_dvd_pow qq (by omega))
        simpa using this

variable (K : ℕ)

theorem dvd_coef (d i s : ℕ) :
    qq ^ (K * s) ∣ (-1) ^ s * qq ^ (K * s * s + d * s + tri s) * ipoch s := by
  have h : K * s ≤ K * s * s + d * s + tri s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; simp
    · have : K * s ≤ K * s * s := Nat.le_mul_of_pos_right _ hpos
      omega
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow qq h) _) _

theorem Adm_factor (i s : ℕ) : Adm (1 - CC (qq ^ ((2 * s + 1) * i)) * xx ^ i) :=
  Adm_one.sub (Adm_monomial _ _ (pow_dvd_pow qq (by nlinarith)))

theorem ev_factor (i s : ℕ) :
    ev (1 - CC (qq ^ ((2 * s + 1) * i)) * xx ^ i) = 1 - qq ^ ((2 * s + 1) * i) := by
  rw [ev_sub, ev_one, ev_monomial _ _ (pow_dvd_pow qq (by nlinarith))]

theorem Adm_term (d i s : ℕ) : Adm (term K d i s) := by
  unfold term
  exact ((Adm_monomial _ _ (dvd_coef K d i s)).mul (Adm_factor i s)).mul (Adm_PP s)

theorem ev_term (d i s : ℕ) :
    ev (term K d i s) = (-1) ^ s * qq ^ (K * s * s + d * s + tri s) * (1 - qq ^ ((2 * s + 1) * i)) := by
  unfold term
  rw [ev_mul ((Adm_monomial _ _ (dvd_coef K d i s)).mul (Adm_factor i s)) (Adm_PP s),
    ev_mul (Adm_monomial _ _ (dvd_coef K d i s)) (Adm_factor i s),
    ev_monomial _ _ (dvd_coef K d i s), ev_factor, ev_PP]
  have := poch_mul_ipoch s
  linear_combination ((-1) ^ s * qq ^ (K * s * s + d * s + tri s) *
    (1 - qq ^ ((2 * s + 1) * i))) * this

theorem Adm_AA (i : ℕ) : Adm (AA K i) := by
  intro m
  rw [coeff_AA]
  exact Finset.dvd_sum fun s _ => Adm_term K _ _ _ m

/-- **The value of `A_i` at `x = 1`.** -/
theorem coeff_ev_AA (hK : 1 ≤ K) (i N : ℕ) :
    coeff N (ev (AA K i)) = ∑ s ∈ Finset.range (N + 1),
      coeff N ((-1) ^ s * qq ^ (K * s * s + (K - i) * s + tri s) * (1 - qq ^ ((2 * s + 1) * i))) := by
  rw [coeff_ev, SS]
  have h : ∀ m ∈ Finset.range (N + 1), coeff m (AA K i) =
      ∑ s ∈ Finset.range (N + 1), coeff m (term K (K - i) i s) := fun m hm =>
    coeff_AA_eq K hK i m N (by rw [Finset.mem_range] at hm; omega)
  rw [Finset.sum_congr rfl h, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← ev_term, coeff_ev, SS]

/-! ## §4  The partition series `1/(xq)_∞` -/

/-- `FF = Σ_m x^m q^m/(q)_m`: `[x^m q^N] FF = pc m (N - m)`. -/
def FF : PowerSeries R :=
  mk fun m => mk fun N => ((VOA.RRLower.pc m ((N : ℤ) - m) : ℤ) : ℚ)

theorem coeff_FF (m N : ℕ) :
    coeff N (coeff m FF) = ((VOA.RRLower.pc m ((N : ℤ) - m) : ℤ) : ℚ) := by
  rw [FF, coeff_mk, coeff_mk]

theorem Adm_FF : Adm FF := by
  intro m
  have : (X : R) ^ m ∣ coeff m FF := by
    rw [X_pow_dvd_iff]
    intro N hN
    rw [coeff_FF, VOA.RRLower.pc_of_neg _ (by omega), Int.cast_zero]
  simpa [qq] using this

theorem coeff_qq_mul (f : R) (N : ℕ) :
    coeff N (qq * f) = if N = 0 then 0 else coeff (N - 1) f := by
  rcases N with _ | N
  · simp [qq]
  · simp [qq, coeff_succ_X_mul]

theorem coeff_qq_pow_mul (f : R) (k N : ℕ) :
    coeff N (qq ^ k * f) = if k ≤ N then coeff (N - k) f else 0 := by
  rw [qq, coeff_X_pow_mul']

/-- **`(1 - xq) FF(x) = FF(xq)`.** -/
theorem FF_functional : (1 - CC qq * xx) * FF = resc FF := by
  refine PowerSeries.ext fun m => ?_
  refine PowerSeries.ext fun N => ?_
  rw [coeff_resc, sub_mul, one_mul, map_sub, mul_assoc, CC, coeff_C_mul]
  rcases m with _ | m
  · rw [show xx * FF = X * FF from rfl, coeff_zero_X_mul, mul_zero, sub_zero, pow_zero, one_mul]
  · rw [show xx * FF = X * FF from rfl, coeff_succ_X_mul, map_sub, coeff_qq_mul,
      coeff_qq_pow_mul, coeff_FF]
    have hrec := VOA.RRLower.pc_succ_eq m ((N : ℤ) - ((m + 1 : ℕ) : ℤ))
    split_ifs with h1 h2 h2
    · subst h1; omega
    · subst h1
      rw [VOA.RRLower.pc_of_neg _ (by push_cast; omega)]; simp
    · rw [coeff_FF, coeff_FF, hrec]
      push_cast
      rw [show (N : ℤ) - ((m : ℤ) + 1) - ((m : ℤ) + 1) = ((N - (m + 1) : ℕ) : ℤ) - ((m : ℤ) + 1) by
        push_cast [show m + 1 ≤ N from h2]; ring]
      rw [show ((N - 1 : ℕ) : ℤ) - (m : ℤ) = (N : ℤ) - ((m : ℤ) + 1) by
        push_cast [show 1 ≤ N by omega]; ring]
      ring
    · rw [coeff_FF, hrec, VOA.RRLower.pc_of_neg (m + 1) (by push_cast; omega)]
      push_cast
      rw [show ((N - 1 : ℕ) : ℤ) - (m : ℤ) = (N : ℤ) - ((m : ℤ) + 1) by
        push_cast [show 1 ≤ N by omega]; ring]
      ring

theorem constantCoeff_FF : constantCoeff FF = 1 := by
  refine PowerSeries.ext fun N => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_FF, coeff_one, VOA.RRLower.pc_zero]
  rcases N with _ | N
  · simp
  · simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem sum_pc_largest (N : ℤ) : ∀ J : ℕ,
    ∑ m ∈ Finset.range (J + 1), VOA.RRLower.pc m (N - m) = VOA.RRLower.pc J N
  | 0 => by simp
  | J + 1 => by
      rw [Finset.sum_range_succ, sum_pc_largest N J, VOA.RRLower.pc_succ_eq J N]
      push_cast; ring_nf

/-- **`FF(1) = Σ_N p(N) q^N`.** -/
theorem coeff_ev_FF (N : ℕ) : coeff N (ev FF) = ((VOA.RRLower.pp (N : ℤ) : ℤ) : ℚ) := by
  rw [coeff_ev, SS, map_sum]
  simp only [coeff_FF]
  rw [← Int.cast_sum, sum_pc_largest, VOA.RRLower.pc_eq_pp N (le_refl _)]

end

end VOA.TwoSeriesCharacter.AG
