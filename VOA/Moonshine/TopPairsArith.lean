/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaAssemble

/-!
# `TopPairs`, part 1: the sign arithmetic of two odd norm-4 Leech vectors

For `n, m ∈ Λ ∖ Λ₀` of norm `4` (shape `(∓3, ±1²³)` in the coordinates `lv`), with blocks
`i = blk n`, `j = blk m`, this file proves the two scalar identities that the top-pair identity
`Θ₀(o(x_n)Φ₀x_m) = o(x_m)Φ₀x_n` reduces to (`TopPairsCore.lean`).

* The vector `e_n e_m t₀` is a joint eigenvector of the `Z_{0k}` with character
  `u_k = (−1)^{⟨γ⁻_{0k},n⟩+⟨γ⁻_{0k},m⟩}`, i.e. `uN (NS n m)` (`uN_NS`).
* `betaN_NS` — **the `B`-eigenvalue**: `ω^{|N|} = (−1)^{⟨m,n⟩} · s(n_i m_i) · s(n_j m_j)`.
  Proof: `2|N| = 24 − χ(n₀)χ(m₀) Σ_k χ(n_k)χ(m_k)` (`two_card_NS`, `χ(x) = ±1` for
  `x ≡ ±1 (4)`), and `36 Σ_k χ(n_k)χ(m_k) = 36·8⟨n,m⟩ − 48(n_im_i + n_jm_j) + 64[i=j]n_im_i`
  (`sum_chi`, from `6χ(x) = x(7 − x²)`), so `|N| ≡ 0 (4)` and its quarter has the parity of
  `⟨m,n⟩` corrected by the block signs.  No Golay-code input is needed beyond `⟨n,m⟩ ∈ ℤ`.
* `coef_local` — **the coefficient identity**, local in the coordinates `i, j, l`:
  `(m_j/3)(δ_{jl} − n_jn_l/4) χ(n_l)χ(m_l) s(n_im_i)s(n_jm_j) = (n_i/3)(δ_{il} − m_im_l/4)`.
* `coef_identity` — the combination used downstream, for every `l : Fin 24`:
  `c⋆(m)(δ_{jl} − n_jn_l/4) · u_l ω^{|N|} = c⋆(n)(−1)^{⟨m,n⟩}(δ_{il} − m_im_l/4)`.

## Status
`sorry`-free.  Pure integer/complex arithmetic; unconditional.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.TopPairs

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.Moonshine.SigmaTop
open Module (End)

/-! ## §1  The characters `χ` and `s` -/

/-- `χ(x) = 1` for `x ≡ 1 (mod 4)`, `−1` otherwise (integer version). -/
def chiI (x : ℤ) : ℤ := if x % 4 = 1 then 1 else -1

/-- `χ(x)` in `ℂ`. -/
def chiZ (x : ℤ) : ℂ := if x % 4 = 1 then 1 else -1

/-- The sign `s(x) = ±1` of a nonzero integer. -/
def sgnZ (x : ℤ) : ℂ := if 0 < x then 1 else -1

theorem chiZ_eq (x : ℤ) : chiZ x = ((chiI x : ℤ) : ℂ) := by
  unfold chiZ chiI; split_ifs <;> simp

theorem chiI_cases (x : ℤ) : chiI x = 1 ∨ chiI x = -1 := by
  unfold chiI; split_ifs <;> simp

/-- `(−1)^{⟨γ⁻,·⟩}`-type halves: `(−1)^{(x−y)/2} = χ(x)χ(y)` for odd `x, y`. -/
theorem negOne_zpow_half {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    (-1 : ℂ) ^ ((4 * (x - y)) / 8) = chiZ x * chiZ y := by
  have hx' := Int.odd_iff.mp hx
  have hy' := Int.odd_iff.mp hy
  rcases Int.even_or_odd ((4 * (x - y)) / 8) with h | h
  · rw [h.neg_one_zpow]
    have h2 := Int.even_iff.mp h
    unfold chiZ; split_ifs <;> first | omega | norm_num
  · rw [h.neg_one_zpow]
    have h2 := Int.odd_iff.mp h
    unfold chiZ; split_ifs <;> first | omega | norm_num

/-- `χ(x) = i^{x−1}` for odd `x`. -/
theorem chiZ_eq_I {x : ℤ} (hx : Odd x) : chiZ x = Complex.I ^ (x - 1) := by
  have hx' := Int.odd_iff.mp hx
  unfold chiZ
  split_ifs with h
  · obtain ⟨q, hq⟩ : ∃ q, x - 1 = 0 + 4 * q := ⟨(x - 1) / 4, by omega⟩
    rw [hq, I_zpow_add_four]; simp
  · obtain ⟨q, hq⟩ : ∃ q, x - 1 = 2 + 4 * q := ⟨(x - 3) / 4, by omega⟩
    rw [hq, I_zpow_add_four]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]

/-- `i^{m₀} χ(n₀) χ(m₀) = i^{n₀}` for odd `n₀, m₀`. -/
theorem I_chi_chi {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    Complex.I ^ y * (chiZ x * chiZ y) = Complex.I ^ x := by
  rw [chiZ_eq_I hx, chiZ_eq_I hy, ← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ Complex.I_ne_zero]
  have hy' := Int.odd_iff.mp hy
  obtain ⟨q, hq⟩ : ∃ q, y + (x - 1 + (y - 1)) = x + 4 * q := ⟨(y - 1) / 2, by omega⟩
  rw [hq, I_zpow_add_four]

/-! ## §2  The character `N` of `e_n e_m t₀` -/

open Classical in
/-- `N = {k : ⟨γ⁻_{0k}, n⟩ + ⟨γ⁻_{0k}, m⟩ odd}` (never contains `0`). -/
noncomputable def NS (n m : leech.carrier) : Finset (Fin 24) :=
  Finset.univ.filter fun k => ¬ Even (leech.form (gM 0 k) n + leech.form (gM 0 k) m)

theorem lv_gM_self (k : Fin 24) (i : Fin 24) : lv (gM k k) i = 0 := by
  rw [lv_gM_apply]; ring

theorem form_gM_self_left (k : Fin 24) (n : leech.carrier) : leech.form (gM k k) n = 0 := by
  rw [form_gM_left]; simp

theorem zero_not_mem_NS (n m : leech.carrier) : (0 : Fin 24) ∉ NS n m := by
  classical
  simp only [NS, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
  rw [form_gM_self_left, form_gM_self_left]
  exact ⟨0, rfl⟩

theorem uN_NS (n m : leech.carrier) (k : Fin 24) :
    uN (NS n m) k = (-1 : ℂ) ^ (leech.form (gM 0 k) n + leech.form (gM 0 k) m) := by
  classical
  unfold uN NS
  rcases Int.even_or_odd (leech.form (gM 0 k) n + leech.form (gM 0 k) m) with h | h
  · rw [h.neg_one_zpow, if_neg]
    rw [Finset.mem_filter]
    exact fun h' => h'.2 h
  · rw [h.neg_one_zpow, if_pos]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Int.not_even_iff_odd.mpr h⟩

/-- `u_k = χ(n₀)χ(n_k)χ(m₀)χ(m_k)`. -/
theorem uN_NS_chi {n m : leech.carrier} (hn : n ∉ lambda0) (hm : m ∉ lambda0) (k : Fin 24) :
    uN (NS n m) k = (chiZ (lv n 0) * chiZ (lv n k)) * (chiZ (lv m 0) * chiZ (lv m k)) := by
  rw [uN_NS, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), form_gM_left, form_gM_left,
    negOne_zpow_half (lv_odd_of_not_mem hn 0) (lv_odd_of_not_mem hn k),
    negOne_zpow_half (lv_odd_of_not_mem hm 0) (lv_odd_of_not_mem hm k)]

/-! ## §3  Counting `|N|` -/

theorem two_card_NS {n m : leech.carrier} (hn : n ∉ lambda0) (hm : m ∉ lambda0) :
    2 * ((NS n m).card : ℤ)
      = ∑ k, (1 - chiI (lv n 0) * chiI (lv m 0) * (chiI (lv n k) * chiI (lv m k))) := by
  classical
  rw [NS, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [form_gM_left, form_gM_left]
  have h1 := Int.odd_iff.mp (lv_odd_of_not_mem hn 0)
  have h2 := Int.odd_iff.mp (lv_odd_of_not_mem hn k)
  have h3 := Int.odd_iff.mp (lv_odd_of_not_mem hm 0)
  have h4 := Int.odd_iff.mp (lv_odd_of_not_mem hm k)
  simp only [Int.even_iff]
  unfold chiI
  split_ifs <;> omega

/-- `6 χ(x) = x(7 − x²)` on the four odd values of a norm-4 coordinate. -/
theorem chiI_poly {x : ℤ} (h : x ^ 2 = 1 ∨ x ^ 2 = 9) : 6 * chiI x = x * (7 - x ^ 2) := by
  rcases h with h | h
  · rcases int_sq_one h with rfl | rfl <;> decide
  · rcases int_sq_nine h with rfl | rfl <;> decide

theorem sq_cases {a : Fin 24 → ℤ} {i : Fin 24} (ha : ∀ k, a k ^ 2 = if k = i then 9 else 1)
    (k : Fin 24) : a k ^ 2 = 1 ∨ a k ^ 2 = 9 := by
  rw [ha k]; split_ifs <;> simp

/-- The local form of `36 Σ χ(n_k)χ(m_k)`. -/
theorem sum_chi {a b : Fin 24 → ℤ} {i j : Fin 24} (ha : ∀ k, a k ^ 2 = if k = i then 9 else 1)
    (hb : ∀ k, b k ^ 2 = if k = j then 9 else 1) :
    36 * ∑ k, chiI (a k) * chiI (b k)
      = 36 * ∑ k, a k * b k - 48 * (a i * b i) - 48 * (a j * b j)
          + (if i = j then 64 * (a i * b i) else 0) := by
  have hloc : ∀ k, 36 * (chiI (a k) * chiI (b k))
      = 36 * (a k * b k) - (if k = i then 48 * (a k * b k) else 0)
        - (if k = j then 48 * (a k * b k) else 0)
        + (if k = i ∧ k = j then 64 * (a k * b k) else 0) := by
    intro k
    have e : 36 * (chiI (a k) * chiI (b k)) = (6 * chiI (a k)) * (6 * chiI (b k)) := by ring
    rw [e, chiI_poly (sq_cases ha k), chiI_poly (sq_cases hb k), ha k, hb k]
    by_cases hki : k = i
    · subst hki
      by_cases hkj : k = j
      · subst hkj; simp; ring
      · simp [hkj]; ring
    · by_cases hkj : k = j
      · subst hkj; simp [hki]; ring
      · simp [hki, hkj]; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => hloc k, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  congr 1
  by_cases hij : i = j
  · subst hij
    simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

theorem ωB_pow_four_mul (N : ℕ) (r : ℤ) (h : (N : ℤ) = 4 * r) : ωB ^ N = (-1 : ℂ) ^ r := by
  rw [← zpow_natCast, h, zpow_mul]
  congr 1
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, ωB_four]

/-- Parity bookkeeping for `(−1)^r`. -/
theorem negOne_zpow_eq {r q : ℤ} (s : ℂ) (hs : s = 1 ∨ s = -1)
    (h : (Even (r - q) ∧ s = 1) ∨ (Odd (r - q) ∧ s = -1)) :
    (-1 : ℂ) ^ r = (-1 : ℂ) ^ q * s := by
  rcases Int.even_or_odd q with hq | hq <;> rcases Int.even_or_odd r with hr | hr <;>
    rw [hq.neg_one_zpow, hr.neg_one_zpow] <;>
    rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> norm_num <;>
    · simp only [Int.even_iff, Int.odd_iff] at hq hr h1; omega

/-- **The `B`-eigenvalue of `e_n e_m t₀`**: `ω^{|N|} = (−1)^{⟨m,n⟩} s(n_im_i) s(n_jm_j)`. -/
theorem betaN_NS {n m : leech.carrier} (hn : n ∉ lambda0) (hn4 : leech.form n n = 4)
    (hm : m ∉ lambda0) (hm4 : leech.form m m = 4) :
    betaN (NS n m) = (-1 : ℂ) ^ (leech.form m n)
      * (sgnZ (lv n (blk n) * lv m (blk n)) * sgnZ (lv n (blk m) * lv m (blk m))) := by
  rw [SigmaAssemble.betaN_eq]
  have h2 := two_card_NS hn hm
  have hsn := lv_sq hn hn4
  have hsm := lv_sq hm hm4
  have h36 := sum_chi hsn hsm
  have hdot : ∑ k, lv n k * lv m k = 8 * leech.form m n := by
    rw [← lv_dot, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
  push_cast at h2
  rw [hdot] at h36
  generalize hS : ∑ k, chiI (lv n k) * chiI (lv m k) = S at h2 h36
  generalize hc : chiI (lv n 0) * chiI (lv m 0) = c at h2
  have hc' : c = 1 ∨ c = -1 := by
    rw [← hc]
    rcases chiI_cases (lv n 0) with h | h <;> rcases chiI_cases (lv m 0) with h' | h' <;>
      rw [h, h'] <;> norm_num
  generalize hq : leech.form m n = q at h36 ⊢
  generalize hN : (NS n m).card = N at h2 ⊢
  generalize hi : blk n = i at hsn hsm h36 ⊢
  generalize hj : blk m = j at hsn hsm h36 ⊢
  have hni := hsn i; rw [if_pos rfl] at hni
  have hmj := hsm j; rw [if_pos rfl] at hmj
  by_cases hij : i = j
  · rw [if_pos hij] at h36
    subst hij
    have hmi : lv m i ^ 2 = 9 := by rw [hsm i, if_pos rfl]
    obtain ⟨r, hr⟩ : ∃ r, (N : ℤ) = 4 * r := ⟨(N : ℤ) / 4, by
      rcases int_sq_nine hni with h1 | h1 <;> rcases int_sq_nine hmi with h3 | h3 <;>
        rw [h1, h3] at h36 <;> rcases hc' with rfl | rfl <;> omega⟩
    rw [ωB_pow_four_mul N r hr]
    rcases int_sq_nine hni with h1 | h1 <;> rcases int_sq_nine hmi with h3 | h3 <;>
      rw [h1, h3] at h36 ⊢ <;>
      refine negOne_zpow_eq _ (by norm_num [sgnZ]) ?_ <;> norm_num [sgnZ] <;>
      simp only [Int.even_iff] <;> rcases hc' with rfl | rfl <;> omega
  · rw [if_neg hij] at h36
    have hmi : lv m i ^ 2 = 1 := by rw [hsm i, if_neg hij]
    have hnj : lv n j ^ 2 = 1 := by rw [hsn j, if_neg (Ne.symm hij)]
    obtain ⟨r, hr⟩ : ∃ r, (N : ℤ) = 4 * r := ⟨(N : ℤ) / 4, by
      rcases int_sq_nine hni with h1 | h1 <;> rcases int_sq_one hmi with h3 | h3 <;>
        rcases int_sq_one hnj with h5 | h5 <;> rcases int_sq_nine hmj with h7 | h7 <;>
        rw [h1, h3, h5, h7] at h36 <;> rcases hc' with rfl | rfl <;> omega⟩
    rw [ωB_pow_four_mul N r hr]
    rcases int_sq_nine hni with h1 | h1 <;> rcases int_sq_one hmi with h3 | h3 <;>
      rcases int_sq_one hnj with h5 | h5 <;> rcases int_sq_nine hmj with h7 | h7 <;>
      rw [h1, h3, h5, h7] at h36 ⊢ <;>
      refine negOne_zpow_eq _ (by norm_num [sgnZ]) ?_ <;> norm_num [sgnZ] <;>
      simp only [Int.even_iff, Int.odd_iff] <;> rcases hc' with rfl | rfl <;> omega

/-! ## §4  The local coefficient identity -/

/-- **The coefficient identity** (local in the coordinates `i = blk n`, `j = blk m`, `l`). -/
theorem coef_local {a b : Fin 24 → ℤ} {i j : Fin 24} (ha : ∀ k, a k ^ 2 = if k = i then 9 else 1)
    (hb : ∀ k, b k ^ 2 = if k = j then 9 else 1) (l : Fin 24) :
    ((b j : ℂ) / 3) * ((if j = l then 1 else 0) - ((2 * a j * a l : ℤ) : ℂ) / 8)
        * (chiZ (a l) * chiZ (b l)) * (sgnZ (a i * b i) * sgnZ (a j * b j))
      = ((a i : ℂ) / 3) * ((if i = l then 1 else 0) - ((2 * b i * b l : ℤ) : ℂ) / 8) := by
  have hai := ha i; rw [if_pos rfl] at hai
  have hbj := hb j; rw [if_pos rfl] at hbj
  by_cases hij : i = j
  · subst hij
    by_cases hl : l = i
    · subst hl
      rcases int_sq_nine hai with h1 | h1 <;> rcases int_sq_nine hbj with h2 | h2 <;>
        rw [h1, h2] <;> norm_num [chiZ, sgnZ]
    · have hal := ha l; rw [if_neg hl] at hal
      have hbl := hb l; rw [if_neg hl] at hbl
      rw [if_neg (Ne.symm hl)]
      rcases int_sq_nine hai with h1 | h1 <;> rcases int_sq_nine hbj with h2 | h2 <;>
        rcases int_sq_one hal with h3 | h3 <;> rcases int_sq_one hbl with h4 | h4 <;>
        rw [h1, h2, h3, h4] <;> norm_num [chiZ, sgnZ]
  · have hbi := hb i; rw [if_neg hij] at hbi
    have haj := ha j; rw [if_neg (Ne.symm hij)] at haj
    by_cases hli : l = i
    · subst hli
      rw [if_neg (Ne.symm hij)]
      rcases int_sq_nine hai with h1 | h1 <;> rcases int_sq_nine hbj with h2 | h2 <;>
        rcases int_sq_one hbi with h3 | h3 <;> rcases int_sq_one haj with h4 | h4 <;>
        rw [h1, h2, h3, h4] <;> norm_num [chiZ, sgnZ]
    · by_cases hlj : l = j
      · subst hlj
        rw [if_neg hij]
        rcases int_sq_nine hai with h1 | h1 <;> rcases int_sq_nine hbj with h2 | h2 <;>
          rcases int_sq_one hbi with h3 | h3 <;> rcases int_sq_one haj with h4 | h4 <;>
          rw [h1, h2, h3, h4] <;> norm_num [chiZ, sgnZ]
      · have hal := ha l; rw [if_neg hli] at hal
        have hbl := hb l; rw [if_neg hlj] at hbl
        rw [if_neg (Ne.symm hli), if_neg (Ne.symm hlj)]
        rcases int_sq_nine hai with h1 | h1 <;> rcases int_sq_nine hbj with h2 | h2 <;>
          rcases int_sq_one hbi with h3 | h3 <;> rcases int_sq_one haj with h4 | h4 <;>
          rcases int_sq_one hal with h5 | h5 <;> rcases int_sq_one hbl with h6 | h6 <;>
          rw [h1, h2, h3, h4, h5, h6] <;> norm_num [chiZ, sgnZ]

/-- **The combined coefficient identity** behind `TopPairs`, for odd norm-4 `n, m` and every
`l`: `c⋆(m)(δ_{jl} − n_jn_l/4) u_l ω^{|N|} = c⋆(n)(−1)^{⟨m,n⟩}(δ_{il} − m_im_l/4)`. -/
theorem coef_identity {n m : leech.carrier} (hn : n ∉ lambda0) (hn4 : leech.form n n = 4)
    (hm : m ∉ lambda0) (hm4 : leech.form m m = 4) (l : Fin 24) :
    cStar m * ((if blk m = l then 1 else 0) - ((2 * lv n (blk m) * lv n l : ℤ) : ℂ) / 8)
        * (uN (NS n m) l * betaN (NS n m))
      = cStar n * (-1 : ℂ) ^ (leech.form m n)
        * ((if blk n = l then 1 else 0) - ((2 * lv m (blk n) * lv m l : ℤ) : ℂ) / 8) := by
  have hloc := coef_local (lv_sq hn hn4) (lv_sq hm hm4) l
  rw [betaN_NS hn hn4 hm hm4, uN_NS_chi hn hm]
  have hI := I_chi_chi (lv_odd_of_not_mem hn 0) (lv_odd_of_not_mem hm 0)
  unfold cStar sgnBlk
  linear_combination (Complex.I ^ (lv n 0) * (-1 : ℂ) ^ (leech.form m n)) * hloc
    + ((lv m (blk m) : ℂ) / 3 * ((if blk m = l then 1 else 0) - ((2 * lv n (blk m) * lv n l : ℤ) : ℂ) / 8)
        * (chiZ (lv n l) * chiZ (lv m l)) * (-1 : ℂ) ^ (leech.form m n)
        * (sgnZ (lv n (blk n) * lv m (blk n)) * sgnZ (lv n (blk m) * lv m (blk m)))) * hI

end VOA.Moonshine.TopPairs
