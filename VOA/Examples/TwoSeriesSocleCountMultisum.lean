/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterAGIdentity
import VOA.Examples.TwoSeriesCharacterGU

/-!
# The Andrews–Gordon multisum, refined by the number of parts

Formal power series in `x` over `ℚ⟦q⟧`, as in `VOA.TwoSeriesCharacter.AG`.  For `n` levels
`N_1 ≥ ⋯ ≥ N_n ≥ 0` (`n_j = N_j - N_{j+1}`) and `1 ≤ i ≤ n + 1` the multisum is

`F_{n,i}(x) = Σ x^{N_1+⋯+N_n} q^{N_1²+⋯+N_n² + N_i+⋯+N_n} / ((q)_{n_1} ⋯ (q)_{n_n})`.

Peeling off the smallest level `t = N_n` (substituting `N_j = N_j' + t` for `j < n`) gives

`F_{n,i}(x) = Σ_t x^{n t} q^{n t² + (n+1-i) t} / (q)_t · F_{n-1, min(i,n)}(x q^{2t})`,

and this is taken as the **definition** (`F`), by recursion on `n`.  The main theorem:

* `F_rec` — Andrews' recursion `F_{a+1} = F_a + x^a q^a F_{n+1-a}(xq)` for `a ≤ n`, by
  induction on `n` through the peeling formula (`peel_shift`, `peel_xmul`, `resc_peel`); the
  inductive step uses the recursion for `n - 1` at **both** `a` and `n + 1 - a`.
* `F_eq_GG` — hence `F_{n,i} = GG n i` (uniqueness of the solution of the recursion), and
  `coeff_F_one` — `[x^r q^N] F_{n,1} = gordonCoeff n N r`: the fixed-number-of-parts
  Andrews–Gordon multisum identity.

Everything is proved; no hypothesis is introduced.
-/

namespace VOA.SocleCount

open PowerSeries VOA.TwoSeriesCharacter VOA.TwoSeriesCharacter.AG
open scoped BigOperators

noncomputable section

/-! ## §1  Rescalings `x ↦ q^k x` -/

/-- `x ↦ q^k x`. -/
def rs (k : ℕ) : PowerSeries R →+* PowerSeries R := rescale (qq ^ k)

theorem coeff_rs (k m : ℕ) (f : PowerSeries R) :
    coeff m (rs k f) = qq ^ (k * m) * coeff m f := by
  rw [rs, coeff_rescale, pow_mul]

theorem rs_rs (j k : ℕ) (f : PowerSeries R) : rs j (rs k f) = rs (j + k) f := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_rs, coeff_rs, coeff_rs, ← mul_assoc, ← pow_add, add_mul]

theorem resc_eq_rs (f : PowerSeries R) : resc f = rs 1 f := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_resc, coeff_rs, one_mul]

theorem rs_zero (f : PowerSeries R) : rs 0 f = f := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_rs, zero_mul, pow_zero, one_mul]

theorem rs_CC (k : ℕ) (r : R) : rs k (CC r) = CC r := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_rs, CC, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem rs_xx_pow (k a : ℕ) : rs k (xx ^ a) = CC (qq ^ (k * a)) * xx ^ a := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_rs, xx, coeff_X_pow, CC, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h; simp
  · simp

theorem resc_xx_pow (a : ℕ) : resc (xx ^ a) = CC (qq ^ a) * xx ^ a := by
  rw [resc_eq_rs, rs_xx_pow, one_mul]

/-! ## §2  Coefficientwise sums -/

/-- `Σ_t A_t`, defined coefficientwise in `x` (only `t ≤ m` contributes to `x^m`). -/
def tsumx (A : ℕ → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun m => ∑ t ∈ Finset.range (m + 1), coeff m (A t)

theorem coeff_tsumx (A : ℕ → PowerSeries R) (m : ℕ) :
    coeff m (tsumx A) = ∑ t ∈ Finset.range (m + 1), coeff m (A t) := coeff_mk _ _

/-- `A_t` has no `x^m` for `m < t`. -/
def Vanish (A : ℕ → PowerSeries R) : Prop := ∀ t m, m < t → coeff m (A t) = 0

theorem coeff_tsumx_eq {A : ℕ → PowerSeries R} (hA : Vanish A) {m M : ℕ} (h : m ≤ M) :
    coeff m (tsumx A) = ∑ t ∈ Finset.range (M + 1), coeff m (A t) := by
  rw [coeff_tsumx]
  obtain ⟨d, rfl⟩ : ∃ d, M = m + d := ⟨M - m, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [ih (by omega), show m + (d + 1) + 1 = (m + d + 1) + 1 by ring,
        Finset.sum_range_succ _ (m + d + 1), hA _ _ (by omega), add_zero]

theorem tsumx_add (A B : ℕ → PowerSeries R) :
    tsumx (fun t => A t + B t) = tsumx A + tsumx B := by
  refine PowerSeries.ext fun m => ?_
  simp only [map_add, coeff_tsumx, Finset.sum_add_distrib]

theorem tsumx_sub (A B : ℕ → PowerSeries R) :
    tsumx (fun t => A t - B t) = tsumx A - tsumx B := by
  refine PowerSeries.ext fun m => ?_
  simp only [map_sub, coeff_tsumx, Finset.sum_sub_distrib]

theorem tsumx_congr {A B : ℕ → PowerSeries R} (h : ∀ t, A t = B t) : tsumx A = tsumx B := by
  rw [show A = B from funext h]

theorem resc_tsumx (A : ℕ → PowerSeries R) : resc (tsumx A) = tsumx fun t => resc (A t) := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_resc, coeff_tsumx, coeff_tsumx, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => (coeff_resc (A t) m).symm

theorem coeff_xmul (a : ℕ) (c : R) (G : PowerSeries R) (m : ℕ) :
    coeff m (xx ^ a * CC c * G) = if a ≤ m then c * coeff (m - a) G else 0 := by
  rw [show xx ^ a * CC c * G = xx ^ a * (CC c * G) by ring, xx, coeff_X_pow_mul']
  split_ifs
  · rw [CC, coeff_C_mul]
  · rfl

theorem Vanish.xmul {A : ℕ → PowerSeries R} (hA : Vanish A) (a : ℕ) (c : R) :
    Vanish fun t => xx ^ a * CC c * A t := by
  intro t m h
  rw [coeff_xmul]
  split_ifs
  · rw [hA t (m - a) (by omega), mul_zero]
  · rfl

theorem Vanish.sub {A B : ℕ → PowerSeries R} (hA : Vanish A) (hB : Vanish B) :
    Vanish fun t => A t - B t := by
  intro t m h
  rw [map_sub, hA t m h, hB t m h, sub_zero]

theorem tsumx_xmul {A : ℕ → PowerSeries R} (hA : Vanish A) (a : ℕ) (c : R) :
    xx ^ a * CC c * tsumx A = tsumx fun t => xx ^ a * CC c * A t := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_xmul, coeff_tsumx (fun t => xx ^ a * CC c * A t)]
  simp only [coeff_xmul]
  split_ifs with h
  · rw [coeff_tsumx_eq hA (show m - a ≤ m by omega), Finset.mul_sum]
  · simp

/-- Reindexing `t = s + 1` when the `t = 0` term vanishes. -/
theorem tsumx_shift {A B : ℕ → PowerSeries R} (hA : Vanish A) (h0 : A 0 = 0)
    (hs : ∀ s, A (s + 1) = B s) : tsumx A = tsumx B := by
  refine PowerSeries.ext fun m => ?_
  rw [coeff_tsumx, coeff_tsumx, Finset.sum_range_succ', h0, map_zero, add_zero,
    Finset.sum_range_succ, ← hs m, hA (m + 1) m (by omega), add_zero]
  exact Finset.sum_congr rfl fun s _ => by rw [← hs s]

/-! ## §3  The peeling sum -/

theorem ipoch_zero : ipoch 0 = 1 := by
  have := poch_mul_ipoch 0
  simpa [poch] using this

/-- The `t`-th peeling term `x^{K t} q^{K t² + e t}/(q)_t · f(x q^{2t})`. -/
def pterm (K e t : ℕ) (f : PowerSeries R) : PowerSeries R :=
  CC (qq ^ (K * t * t + e * t) * ipoch t) * xx ^ (K * t) * rs (2 * t) f

/-- The peeling sum `Σ_t x^{K t} q^{K t² + e t}/(q)_t · f(x q^{2t})`. -/
def peel (K e : ℕ) (f : PowerSeries R) : PowerSeries R := tsumx fun t => pterm K e t f

theorem pterm_vanish {K : ℕ} (hK : 1 ≤ K) (e : ℕ) (f : PowerSeries R) :
    Vanish fun t => pterm K e t f := by
  intro t m h
  change coeff m (pterm K e t f) = 0
  have : pterm K e t f =
      xx ^ (K * t) * (CC (qq ^ (K * t * t + e * t) * ipoch t) * rs (2 * t) f) := by
    unfold pterm; ring
  rw [this, xx, coeff_X_pow_mul', if_neg]
  have : t ≤ K * t := Nat.le_mul_of_pos_left t hK
  omega

theorem peel_add (K e : ℕ) (f g : PowerSeries R) :
    peel K e (f + g) = peel K e f + peel K e g := by
  unfold peel
  rw [← tsumx_add]
  refine tsumx_congr fun t => ?_
  unfold pterm
  rw [map_add]; ring

theorem resc_rs (k : ℕ) (f : PowerSeries R) : resc (rs k f) = rs k (resc f) := by
  rw [resc_eq_rs, resc_eq_rs, rs_rs, rs_rs, add_comm]

theorem resc_pterm (K e t : ℕ) (f : PowerSeries R) :
    resc (pterm K e t f) = pterm K (e + K) t (resc f) := by
  unfold pterm
  rw [map_mul, map_mul, resc_CC, resc_xx_pow, resc_rs,
    show K * t * t + (e + K) * t = K * t * t + e * t + K * t by ring]
  simp only [pow_add, map_mul]
  ring

/-- `resc` passes through the peeling sum. -/
theorem resc_peel (K e : ℕ) (f : PowerSeries R) :
    resc (peel K e f) = peel K (e + K) (resc f) := by
  unfold peel
  rw [resc_tsumx]
  exact tsumx_congr fun t => resc_pterm K e t f

theorem pterm_xmul (K e t a : ℕ) (c : R) (f : PowerSeries R) :
    pterm K e t (xx ^ a * CC c * f) = xx ^ a * CC c * pterm K (e + 2 * a) t f := by
  unfold pterm
  rw [show K * t * t + (e + 2 * a) * t = K * t * t + e * t + 2 * t * a by ring]
  simp only [map_mul, rs_xx_pow, rs_CC, pow_add]
  ring

/-- Factors `x^a c` pass through the peeling sum, at the cost of `e ↦ e + 2a`. -/
theorem peel_xmul {K : ℕ} (hK : 1 ≤ K) (e a : ℕ) (c : R) (f : PowerSeries R) :
    peel K e (xx ^ a * CC c * f) = xx ^ a * CC c * peel K (e + 2 * a) f := by
  unfold peel
  rw [tsumx_xmul (pterm_vanish hK _ f)]
  exact tsumx_congr fun t => pterm_xmul K e t a c f

/-- **The shift identity** `(1 - q^t)/(q)_t = 1/(q)_{t-1}` in peeled form. -/
theorem peel_shift {K : ℕ} (hK : 1 ≤ K) (e : ℕ) (f : PowerSeries R) :
    peel K e f - peel K (e + 1) f = xx ^ K * CC (qq ^ (K + e)) * peel K (e + 2 * K) (rs 2 f) := by
  unfold peel
  rw [← tsumx_sub, tsumx_xmul (pterm_vanish hK _ _)]
  refine tsumx_shift ((pterm_vanish hK e f).sub (pterm_vanish hK (e + 1) f)) ?_ ?_
  · simp [pterm]
  · intro s
    unfold pterm
    rw [rs_rs, show 2 * s + 2 = 2 * (s + 1) by ring, ← ipoch_succ s,
      show K * (s + 1) * (s + 1) + (e + 1) * (s + 1) = K * (s + 1) * (s + 1) + e * (s + 1) + (s + 1)
        by ring,
      show K * (s + 1) * (s + 1) + e * (s + 1) = (K + e) + (K * s * s + (e + 2 * K) * s) by ring,
      show K * (s + 1) = K + K * s by ring]
    simp only [pow_add, map_mul, map_sub, map_one, map_pow]
    ring

theorem coeff_zero_peel (K e : ℕ) (f : PowerSeries R) :
    constantCoeff (peel K e f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, peel, coeff_tsumx, Finset.sum_range_one, pterm]
  simp only [mul_zero, add_zero, pow_zero, ipoch_zero, mul_one, map_one, one_mul,
    rs_zero]
  exact coeff_zero_eq_constantCoeff_apply f

/-! ## §4  The multisum and its recursion -/

/-- The Andrews–Gordon multisum `F_{n,i}` with `x` counting the number of parts, defined by
peeling off the smallest level (`F n 0 = 0`). -/
def F : ℕ → ℕ → PowerSeries R
  | 0, i => if i = 0 then 0 else 1
  | n + 1, i => if i = 0 then 0 else peel (n + 1) (n + 2 - i) (F n (min i (n + 1)))

theorem F_zero (n : ℕ) : F n 0 = 0 := by
  cases n <;> simp [F]

theorem F_succ (n i : ℕ) (hi : i ≠ 0) :
    F (n + 1) i = peel (n + 1) (n + 2 - i) (F n (min i (n + 1))) := by
  simp [F, hi]

theorem constantCoeff_F : ∀ (n i : ℕ), 1 ≤ i → constantCoeff (F n i) = 1
  | 0, i, hi => by simp [F, show i ≠ 0 by omega]
  | n + 1, i, hi => by
      rw [F_succ n i (by omega), coeff_zero_peel]
      exact constantCoeff_F n _ (by omega)

/-- **Andrews' recursion for the multisum**: `F_{a+1} = F_a + x^a q^a F_{n+1-a}(xq)`. -/
theorem F_rec : ∀ (n a : ℕ), a ≤ n →
    F n (a + 1) = F n a + xx ^ a * CC (qq ^ a) * resc (F n (n + 1 - a))
  | 0, a, ha => by
      obtain rfl : a = 0 := by omega
      simp [F]
  | n + 1, a, ha => by
      have IH := F_rec n
      have hK : 1 ≤ n + 1 := by omega
      -- the case `a = 0` of the recursion for `n`
      have h0 : F n 1 = resc (F n (n + 1)) := by
        have := IH 0 (by omega)
        simpa [F_zero] using this
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · -- a = 0
        rw [F_zero, zero_add, pow_zero, pow_zero, map_one, one_mul, one_mul,
          F_succ n 1 (by omega), F_succ n (n + 1 + 1 - 0) (by omega), resc_peel,
          show min 1 (n + 1) = 1 by omega, show min (n + 1 + 1 - 0) (n + 1) = n + 1 by omega,
          show n + 2 - 1 = n + 1 by omega, show n + 2 - (n + 1 + 1 - 0) = 0 by omega,
          h0, Nat.zero_add, zero_add]
      rcases eq_or_lt_of_le ha with rfl | halt
      · -- a = n + 1
        rw [show n + 1 + 1 - (n + 1) = 1 by omega, F_succ n (n + 1 + 1) (by omega),
          F_succ n (n + 1) (by omega), F_succ n 1 (by omega),
          show min (n + 1 + 1) (n + 1) = n + 1 by omega, show min (n + 1) (n + 1) = n + 1 by omega,
          show min 1 (n + 1) = 1 by omega, show n + 2 - (n + 1 + 1) = 0 by omega,
          show n + 2 - (n + 1) = 1 by omega, show n + 2 - 1 = n + 1 by omega,
          resc_peel, h0, ← sub_eq_iff_eq_add', peel_shift hK, resc_eq_rs (resc _),
          resc_eq_rs (F n (n + 1)), rs_rs, show 0 + 2 * (n + 1) = n + 1 + (n + 1) by ring,
          Nat.add_zero]
      · -- 1 ≤ a ≤ n
        have han : a ≤ n := by omega
        obtain ⟨b, hb⟩ : ∃ b, b = n + 1 - a := ⟨_, rfl⟩
        have hab : n + 1 = a + b := by omega
        have hb1 : 1 ≤ b := by omega
        have IHa := IH a han
        have IHb := IH b (by omega)
        rw [show n + 1 - b = a by omega] at IHb
        rw [← hb] at IHa
        rw [show n + 1 + 1 - a = n + 2 - a by omega, F_succ n (a + 1) (by omega),
          F_succ n a (by omega), F_succ n (n + 2 - a) (by omega),
          show min (a + 1) (n + 1) = a + 1 by omega, show min a (n + 1) = a by omega,
          show min (n + 2 - a) (n + 1) = n + 2 - a by omega,
          show n + 2 - (a + 1) = b by omega, show n + 2 - (n + 2 - a) = a by omega,
          show n + 2 - a = b + 1 by omega, IHa, IHb, peel_add, peel_xmul hK, resc_peel,
          map_add, peel_add, map_mul, map_mul, resc_xx_pow, resc_CC, resc_eq_rs (resc _),
          resc_eq_rs (F n a), rs_rs,
          show CC (qq ^ b) * xx ^ b * CC (qq ^ b) * rs (1 + 1) (F n a) =
            xx ^ b * CC (qq ^ b * qq ^ b) * rs 2 (F n a) by rw [map_mul]; ring,
          peel_xmul hK]
        have hs := peel_shift hK b (F n a)
        rw [show peel (n + 1) b (F n a) =
          peel (n + 1) (b + 1) (F n a) + (peel (n + 1) b (F n a) - peel (n + 1) (b + 1) (F n a))
          by ring, hs, hab,
          show b + 2 * a = a + (a + b) by ring,
          show a + (a + b) + 2 * b = b + 2 * (a + b) by ring]
        simp only [pow_add, map_mul]
        ring

/-! ## §5  Uniqueness: the multisum is the Gordon series -/

/-- The multisum equals the Gordon generating series. -/
theorem F_eq_GG (n : ℕ) : ∀ i ≤ n + 1, F n i = GG n i := by
  set D : ℕ → PowerSeries R := fun i => GG n i - F n i with hD
  have hrec : ∀ a ≤ n, D (a + 1) = D a + xx ^ a * CC (qq ^ a) * resc (D (n + 1 - a)) := by
    intro a ha
    simp only [hD]
    rw [GG_rec n a ha, F_rec n a ha, map_sub]
    ring
  have h0 : D 0 = 0 := by simp only [hD]; rw [GG_zero, F_zero, sub_zero]
  have hc : ∀ i, 1 ≤ i → constantCoeff (D i) = 0 := by
    intro i hi
    simp only [hD]
    rw [map_sub, constantCoeff_GG n i hi, constantCoeff_F n i hi, sub_self]
  have key : ∀ N i, i ≤ n + 1 → ∀ m, coeff N (coeff m (D i)) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
    intro i
    induction i with
    | zero => intro _ m; rw [h0]; simp
    | succ a iha =>
      intro hi m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [coeff_zero_eq_constantCoeff_apply, hc (a + 1) (by omega), map_zero]
      · rw [hrec a (by omega), map_add, map_add, iha (by omega) m, zero_add, coeff_shift]
        split_ifs with h
        · exact ihN (N - m) (by omega) (n + 1 - a) (by omega) (m - a)
        · rfl
  intro i hi
  have : D i = 0 :=
    PowerSeries.ext fun m => PowerSeries.ext fun N => by rw [key N i hi m]; simp
  exact (sub_eq_zero.mp (by simpa only [hD] using this)).symm

/-- **The fixed-number-of-parts Andrews–Gordon multisum identity**:
`[x^r q^N] F_{n,1} = gordonCoeff n N r`. -/
theorem coeff_F_one (n N r : ℕ) :
    coeff N (coeff r (F n 1)) = ((gordonCoeff n (N : ℤ) r : ℕ) : ℚ) := by
  rw [F_eq_GG n 1 (by omega), coeff_GG, gordonCoeff_eq_gC]

end

end VOA.SocleCount
