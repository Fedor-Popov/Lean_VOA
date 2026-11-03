/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Codes.Golay
import VOA.LatticesAndCodes.Codes.MacWilliams

/-!
# The weight distribution of the extended binary Golay code

`W_G̃(X,Y) = X²⁴ + 759 X¹⁶Y⁸ + 2576 X¹²Y¹² + 759 X⁸Y¹⁶ + Y²⁴`  (Ebeling §2.8).

The `759` weight-eight codewords are the **octads**; they are what the Steiner system `S(5,8,24)`
is built from, what the `759 · 2⁷` count of Leech minimal vectors of one type uses, and half of
the input to the uniqueness of the Golay code.

## The route

Nothing is brute-forced: `decide` over the `2¹²` codewords is out of reach (recorded on the
ledger row `Thm-2.6a`).  Four inputs cut the twenty-five unknowns `A₀, …, A₂₄` down to one:

* **double evenness** kills every `Aⱼ` with `4 ∤ j` (`Code.golay_isDoublyEven`);
* **minimum distance `8`** kills `A₄` (`Code.golay_minDist`);
* **the complement involution** `c ↦ c + 1`.  The all-ones word lies in every binary self-dual
  even code (`Code.one_mem_of_isSelfDual_of_isEven`), so `c ↦ c + 1` is a weight-reversing
  bijection of the code and `Aⱼ = A_{n−j}` (`Code.weightCount_compl`).  This gives `A₂₄ = 1`,
  `A₁₆ = A₈` and `A₂₀ = A₄ = 0` for free;
* **MacWilliams** (M13) at the single point `(X, Y) = (1, 2)`, which together with the count
  `∑ Aⱼ = 2¹²` is one linear equation for the one remaining unknown.

The last step is where the arithmetic lives: at `(1,2)` the identity reads
`4096 · W(1,2) = W(3,−1)`, i.e. `226430750·A₈ + 16245775·A₁₂ = 213710055650`, which with
`2A₈ + A₁₂ = 4094` gives `193939200·A₈ = 147199852800`, so `A₈ = 759`.

Evaluating rather than extracting coefficients is what keeps this short: the coefficient-wise
form of MacWilliams would need the binomial expansion of `(X ± Y)^24` inside `MvPolynomial`.

## Main results

* `Code.one_mem_of_isSelfDual_of_isEven`, `Code.weight_add_one`, `Code.weightCount_compl` —
  the complement involution, for a general binary code.
* `Code.golay_weightCount_eight`, `Code.golay_weightCount_twelve` — `759` and `2576`.
* `Code.golay_hammingEnumerator` — the enumerator itself.

## References

Ebeling, *Lattices and Codes*, §2.8.
-/

open MvPolynomial

namespace Code

variable {n : ℕ}

/-! ### The complement involution of a binary self-dual even code -/

theorem sum_eq_weight (c : Fin n → ZMod 2) : ∑ i, c i = (weight c : ZMod 2) := by
  classical
  have h1 : ∑ i ∈ support c, c i = ∑ i, c i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simpa using not_not.1 (mem_support.not.1 hi)
  have h2 : ∑ i ∈ support c, c i = ∑ _i ∈ support c, (1 : ZMod 2) :=
    Finset.sum_congr rfl fun i hi => by
      have := mem_support.1 hi
      revert this
      generalize c i = x
      revert x
      decide
  rw [← h1, h2, Finset.sum_const, weight_eq_card_support, nsmul_eq_mul, mul_one]

/-- The all-ones word lies in every binary self-dual **even** code: it pairs to
`∑ cᵢ = wt(c) mod 2 = 0` with every codeword. -/
theorem one_mem_of_isSelfDual_of_isEven {C : Code 2 n} (hsd : C.IsSelfDual) (he : C.IsEven) :
    (1 : Fin n → ZMod 2) ∈ C := by
  rw [← hsd, mem_dual]
  intro y hy
  rw [show y ⬝ᵥ (1 : Fin n → ZMod 2) = ∑ i, y i from by simp [dotProduct], sum_eq_weight]
  obtain ⟨k, hk⟩ := he y hy
  rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem weight_add_one (c : Fin n → ZMod 2) : weight (c + 1) = n - weight c := by
  classical
  have hsupp : support (c + 1) = (support c)ᶜ := by
    ext i
    simp only [mem_support, Finset.mem_compl, not_not, Pi.add_apply, Pi.one_apply]
    generalize c i = x
    revert x
    decide
  rw [weight_eq_card_support, weight_eq_card_support, hsupp, Finset.card_compl]
  simp

/-- The complement involution `c ↦ c + 1` reverses weights, so a binary code containing the
all-ones word has a symmetric weight distribution. -/
theorem add_one_add_one (c : Fin n → ZMod 2) : c + 1 + 1 = c := by
  funext j
  show c j + 1 + 1 = c j
  generalize c j = x
  revert x
  decide

theorem weightCount_compl {C : Code 2 n} (h1 : (1 : Fin n → ZMod 2) ∈ C) {i : ℕ} (hi : i ≤ n) :
    C.weightCount (n - i) = C.weightCount i := by
  classical
  refine Finset.card_bij' (fun c _ => c + 1) (fun c _ => c + 1) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, mem_toFinset] at hc ⊢
    refine ⟨C.add_mem hc.1 h1, ?_⟩
    rw [weight_add_one, hc.2]
    omega
  · intro c hc
    rw [Finset.mem_filter, mem_toFinset] at hc ⊢
    refine ⟨C.add_mem hc.1 h1, ?_⟩
    rw [weight_add_one, hc.2]
  · exact fun c _ => add_one_add_one c
  · exact fun c _ => add_one_add_one c

/-! ### The vanishing coefficients of the Golay weight distribution -/

theorem golay_weightCount_of_not_dvd {i : ℕ} (h : ¬ (4 ∣ i)) : golay.weightCount i = 0 := by
  classical
  rw [weightCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc hwc
  exact h (hwc ▸ golay_isDoublyEven c (mem_toFinset.1 hc))

theorem golay_weightCount_four : golay.weightCount 4 = 0 := by
  classical
  rw [weightCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc hwc
  have hcC : c ∈ golay := mem_toFinset.1 hc
  have hne : c ≠ 0 := by
    intro h
    rw [h, weight_zero] at hwc
    exact absurd hwc (by norm_num)
  have := minDist_le_weight hcC hne
  rw [golay_minDist, hwc] at this
  omega

theorem golay_one_mem : (1 : Fin 24 → ZMod 2) ∈ golay :=
  one_mem_of_isSelfDual_of_isEven golay_isSelfDual golay_isDoublyEven.isEven

theorem golay_weightCount_zero : golay.weightCount 0 = 1 := weightCount_zero _

theorem golay_weightCount_twentyfour : golay.weightCount 24 = 1 := by
  have := weightCount_compl golay_one_mem (i := 0) (by norm_num)
  simpa [golay_weightCount_zero] using this

theorem golay_weightCount_sixteen : golay.weightCount 16 = golay.weightCount 8 := by
  have := weightCount_compl golay_one_mem (i := 8) (by norm_num)
  simpa using this

theorem golay_weightCount_twenty : golay.weightCount 20 = 0 := by
  have := weightCount_compl golay_one_mem (i := 4) (by norm_num)
  rw [show (24 : ℕ) - 4 = 20 from rfl, golay_weightCount_four] at this
  exact this

/-! ### The enumerator, in terms of the one remaining unknown -/

theorem golay_enum_eval (f : Fin 2 → ℂ) :
    eval f golay.hammingEnumerator
      = f 0 ^ 24 + (golay.weightCount 8 : ℂ) * (f 0 ^ 16 * f 1 ^ 8)
        + (golay.weightCount 12 : ℂ) * (f 0 ^ 12 * f 1 ^ 12)
        + (golay.weightCount 8 : ℂ) * (f 0 ^ 8 * f 1 ^ 16) + f 1 ^ 24 := by
  have hnd : ∀ i : ℕ, ¬ (4 ∣ i) → golay.weightCount i = 0 := fun i h =>
    golay_weightCount_of_not_dvd h
  rw [hammingEnumerator_eq_sum_weightCount, map_sum]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    nsmul_eq_mul, Finset.sum_range_succ, Finset.sum_range_zero,
    golay_weightCount_zero, golay_weightCount_four, golay_weightCount_sixteen,
    golay_weightCount_twenty, golay_weightCount_twentyfour,
    hnd 1 (by norm_num), hnd 2 (by norm_num), hnd 3 (by norm_num), hnd 5 (by norm_num),
    hnd 6 (by norm_num), hnd 7 (by norm_num), hnd 9 (by norm_num), hnd 10 (by norm_num),
    hnd 11 (by norm_num), hnd 13 (by norm_num), hnd 14 (by norm_num), hnd 15 (by norm_num),
    hnd 17 (by norm_num), hnd 18 (by norm_num), hnd 19 (by norm_num), hnd 21 (by norm_num),
    hnd 22 (by norm_num), hnd 23 (by norm_num)]
  simp only [map_natCast, zero_add]
  push_cast
  ring

/-! ### The two equations -/

theorem golay_card : golay.toFinset.card = 4096 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_toFinset, golay_rank]
  norm_num

theorem golay_count_eq :
    (2 : ℂ) * (golay.weightCount 8 : ℂ) + (golay.weightCount 12 : ℂ) = 4094 := by
  have h := hammingEnumerator_eval_one golay
  rw [golay_enum_eval, golay_card] at h
  norm_num at h
  linear_combination h

theorem golay_macWilliams_eq :
    (4096 : ℂ) * (1 + (golay.weightCount 8 : ℂ) * 2 ^ 8 + (golay.weightCount 12 : ℂ) * 2 ^ 12
        + (golay.weightCount 8 : ℂ) * 2 ^ 16 + 2 ^ 24)
      = 3 ^ 24 + (golay.weightCount 8 : ℂ) * 3 ^ 16 + (golay.weightCount 12 : ℂ) * 3 ^ 12
        + (golay.weightCount 8 : ℂ) * 3 ^ 8 + 1 := by
  have h := macWilliams_eval golay 1 2
  rw [golay_isSelfDual, golay_card] at h
  rw [golay_enum_eval, golay_enum_eval] at h
  norm_num at h
  linear_combination h

/-! ### The weight distribution -/

/-- **Ebeling §2.8: the extended Golay code has `759` octads.** -/
theorem golay_weightCount_eight : golay.weightCount 8 = 759 := by
  have hc := golay_count_eq
  have hm := golay_macWilliams_eq
  have h : (golay.weightCount 8 : ℂ) = 759 := by
    linear_combination (-16245775 / 193939200 : ℂ) * hc + (1 / 193939200 : ℂ) * hm
  exact_mod_cast h

theorem golay_weightCount_twelve : golay.weightCount 12 = 2576 := by
  have hc := golay_count_eq
  rw [golay_weightCount_eight] at hc
  have h : (golay.weightCount 12 : ℂ) = 2576 := by linear_combination hc
  exact_mod_cast h

theorem golay_weightCount_sixteen_eq : golay.weightCount 16 = 759 := by
  rw [golay_weightCount_sixteen, golay_weightCount_eight]

/-- **The Hamming weight enumerator of the extended binary Golay code.** -/
theorem golay_hammingEnumerator :
    golay.hammingEnumerator
      = X 0 ^ 24 + MvPolynomial.C 759 * (X 0 ^ 16 * X 1 ^ 8)
        + MvPolynomial.C 2576 * (X 0 ^ 12 * X 1 ^ 12)
        + MvPolynomial.C 759 * (X 0 ^ 8 * X 1 ^ 16) + X 1 ^ 24 := by
  refine hammingEnumerator_ext fun f => ?_
  rw [golay_enum_eval, golay_weightCount_eight, golay_weightCount_twelve]
  simp

end Code
