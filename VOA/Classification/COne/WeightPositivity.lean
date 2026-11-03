/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# B4. Non-negativity of the theta weights `w_t` (Gannon–Rayhaun, Lemma 3.11)

T. Gannon and B. C. Rayhaun, *Classification of rational `c = 1` vertex operator algebras and
vertex operator superalgebras*, arXiv:2609.00122, §3.2.

This file formalizes the argument of GR Lemma 3.11 as a statement about formal `q`-series.
Nothing here mentions vertex algebras: the VOA-theoretic inputs are explicit hypotheses.

## The objects

All series are formal power series in `q` with integer exponents. This is faithful: for a
`c = 1` VOA of CFT type with integer conformal weights, `F_V = η · ch_V = q^{1/24} ∏(1-qⁿ) ·
q^{-1/24} Σ dim V_n qⁿ` has only integer exponents.

* `etaVirasoroChar h` is `η χ_h^{Vir}` for the `c = 1` Virasoro irreducible of integer weight
  `h ≥ 0`, GR (3.4) (Kac determinant / Feigin–Fuchs): `q^{μ²} - q^{(μ+1)²}` if `h = μ²` is
  degenerate, `q^h` otherwise. GR (3.4) allows `μ ∈ ½ℤ_{≥0}`; for *integer* `h` only integer `μ`
  occur (`exists_nat_of_half_sq_eq`), so degenerate integer weights are exactly perfect squares.
* `etaVirasoroSum A = Σ_h A_h η χ_h`; the sum is formally convergent since `η χ_h = O(q^h)`
  (`coeff_etaVirasoroChar_of_lt`), so its `N`-th coefficient is the finite sum over `h ≤ N`.
* `thetaCoeff r j t N = #{m ∈ ℤ : m ≡ j (mod r), t m² = N}` and `thetaSeries r j t` is the
  `q`-expansion of `θ_{n₀,r,t}` (GR (3.12)) for any `n₀` with `n₀ ≡ j (mod r)`; compare
  `tsum_residueClass_eq_rankOneTheta` in `RankOneTheta.lean`. (For `t ≥ 1`, every `m` with
  `t m² = N` lies in `[-N, N]`, so the finite count in the definition is the full count.)

## The hypotheses (VOA input)

* (GR (3.5)) `F = Σ_h A_h η χ_h` with `A_h ∈ ℤ_{≥0}` the Jordan–Hölder multiplicities of the
  `c = 1` Virasoro irreducibles in `V` and `A_0 = 1` (the vacuum `χ_0` occurs once).
* (GR Lemma 3.9, (3.22), from Serre–Stark) `F = Σ_{t ∈ T} Σ_{n₀ mod r_t} a_t(n₀) θ_{n₀,r_t,t}`
  with `T` a finite set of square-free positive integers, `r_t ≥ 1`, `a_t(n₀) ∈ ℂ`.
  We do **not** assume the symmetry `a_t(n₀) = a_t(-n₀)`; the argument does not need it.

## Main results

* `coeff_etaVirasoroSum_sq`, `coeff_etaVirasoroSum_of_not_sq`: GR (3.7),
  `[q^{(n+1)²}] F = A_{(n+1)²} - A_{n²}` and `[q^ℓ] F = A_ℓ` for non-square `ℓ`.
* `coeff_theta_decomposition`: `[q^{t n²}] F = a_t(n) + a_t(-n)` for `t ∈ T`, `n ≥ 1` (the
  uniqueness observation in the proof of GR Lemma 3.9; uses `t n² = t' m²`, `t, t'` square-free
  `⟹ t = t'`, `squarefree_mul_sq_inj`).
* `theta_weight_sum_nonneg` (**GR Lemma 3.11**, the `s_t` form): for every `t ∈ T`,
  `s_t := Σ_{n₀ mod r_t} a_t(n₀)` is a non-negative real number.
* `theta_weight_nonneg`: the same for `w_t = s_t / (r_t √(2t))`, GR (3.25).
-/

open PowerSeries Finset

noncomputable section

namespace VOA.Classification.COne

/-! ### Arithmetic preliminaries -/

/-- If `t m² = t' n²` with `t, t'` square-free and `n ≠ 0`, then `t = t'`. -/
theorem squarefree_mul_sq_inj {t t' m n : ℕ} (ht : Squarefree t) (ht' : Squarefree t')
    (hn : n ≠ 0) (h : t * m ^ 2 = t' * n ^ 2) : t = t' := by
  have ht0 : t ≠ 0 := ht.ne_zero
  have ht0' : t' ≠ 0 := ht'.ne_zero
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h
    exact (mul_ne_zero ht0' (pow_ne_zero 2 hn)) h.symm
  refine Nat.eq_of_factorization_eq ht0 ht0' fun p => ?_
  have hf := congrArg (fun x => x.factorization p) h
  simp only [Nat.factorization_mul ht0 (pow_ne_zero 2 hm),
    Nat.factorization_mul ht0' (pow_ne_zero 2 hn), Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at hf
  have h1 := ht.natFactorization_le_one p
  have h2 := ht'.natFactorization_le_one p
  omega

/-- A square-free `t ≠ 1` times a nonzero square is not a perfect square. -/
theorem not_isSq_squarefree_mul_sq {t n : ℕ} (ht : Squarefree t) (ht1 : t ≠ 1) (hn : n ≠ 0) :
    Nat.sqrt (t * n ^ 2) ^ 2 ≠ t * n ^ 2 := by
  intro h
  exact ht1 (squarefree_mul_sq_inj squarefree_one ht hn (by rw [one_mul, h])).symm

/-- GR (3.4) allows `h = μ²` with `μ ∈ ½ℤ_{≥0}`. If such an `h` is an integer then `μ` is an
integer: `(k/2)² = h ∈ ℕ` forces `k = 2μ` and `h = μ²`. -/
theorem exists_nat_of_half_sq_eq {k h : ℕ} (hk : ((k : ℚ) / 2) ^ 2 = h) :
    ∃ μ : ℕ, k = 2 * μ ∧ h = μ ^ 2 := by
  have h4 : k ^ 2 = 4 * h := by
    have : ((k ^ 2 : ℕ) : ℚ) = ((4 * h : ℕ) : ℚ) := by
      push_cast; rw [← hk]; ring
    exact_mod_cast this
  have hev : Even k := by
    have : Even (k ^ 2) := ⟨2 * h, by omega⟩
    exact (Nat.even_pow' two_ne_zero).mp this
  obtain ⟨μ, rfl⟩ := hev
  refine ⟨μ, by ring, ?_⟩
  nlinarith

/-! ### Virasoro characters at `c = 1` -/

/-- `h` is a degenerate integer weight of the `c = 1` Virasoro algebra iff it is a perfect
square (see `exists_nat_of_half_sq_eq` for why half-integer `μ` do not contribute). -/
def IsDegenerateWeight (h : ℕ) : Prop := Nat.sqrt h ^ 2 = h

instance : DecidablePred IsDegenerateWeight := fun h =>
  inferInstanceAs (Decidable (Nat.sqrt h ^ 2 = h))

theorem isDegenerateWeight_sq (μ : ℕ) : IsDegenerateWeight (μ ^ 2) := by
  simp [IsDegenerateWeight, Nat.sqrt_eq']

/-- `η χ_h^{Vir}` for the irreducible `c = 1` Virasoro module of integer weight `h`, GR (3.4):
`q^{μ²} - q^{(μ+1)²}` for `h = μ²`, and `q^h` otherwise. -/
def etaVirasoroChar (h : ℕ) : PowerSeries ℤ :=
  X ^ h - if IsDegenerateWeight h then X ^ ((Nat.sqrt h + 1) ^ 2) else 0

theorem etaVirasoroChar_sq (μ : ℕ) :
    etaVirasoroChar (μ ^ 2) = X ^ (μ ^ 2) - X ^ ((μ + 1) ^ 2) := by
  simp [etaVirasoroChar, isDegenerateWeight_sq, Nat.sqrt_eq']

theorem etaVirasoroChar_of_not_sq {h : ℕ} (hh : ¬ IsDegenerateWeight h) :
    etaVirasoroChar h = X ^ h := by
  simp [etaVirasoroChar, hh]

theorem coeff_etaVirasoroChar (N h : ℕ) :
    coeff N (etaVirasoroChar h) =
      (if N = h then 1 else 0) -
        (if IsDegenerateWeight h ∧ N = (Nat.sqrt h + 1) ^ 2 then 1 else 0) := by
  unfold etaVirasoroChar
  split_ifs <;> simp_all [coeff_X_pow]

/-- `η χ_h = O(q^h)`, so the formal sum `Σ_h A_h η χ_h` converges coefficientwise. -/
theorem coeff_etaVirasoroChar_of_lt {N h : ℕ} (hN : N < h) : coeff N (etaVirasoroChar h) = 0 := by
  rw [coeff_etaVirasoroChar]
  have h1 : N ≠ h := hN.ne
  have h2 : N ≠ (Nat.sqrt h + 1) ^ 2 := by
    intro e
    have := Nat.lt_succ_sqrt' h
    simp only [Nat.succ_eq_add_one] at this
    omega
  simp [h1, h2]

/-- `Σ_h A_h η χ_h^{Vir}`. By `coeff_etaVirasoroChar_of_lt` the `N`-th coefficient of the formal
infinite sum is the finite sum over `h ≤ N` used here. -/
def etaVirasoroSum (A : ℕ → ℕ) : PowerSeries ℤ :=
  mk fun N => ∑ h ∈ range (N + 1), (A h : ℤ) * coeff N (etaVirasoroChar h)

/-- GR (3.7), square exponents: `[q^{(n+1)²}] Σ_h A_h η χ_h = A_{(n+1)²} - A_{n²}`. -/
theorem coeff_etaVirasoroSum_sq (A : ℕ → ℕ) (n : ℕ) :
    coeff ((n + 1) ^ 2) (etaVirasoroSum A) = (A ((n + 1) ^ 2) : ℤ) - A (n ^ 2) := by
  rw [etaVirasoroSum, coeff_mk]
  simp only [coeff_etaVirasoroChar, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · rw [sum_ite_eq]; simp
  · rw [sum_eq_single (n ^ 2)]
    · simp [isDegenerateWeight_sq, Nat.sqrt_eq']
    · intro h _ hne
      rw [if_neg]
      rintro ⟨hdeg, he⟩
      apply hne
      have : Nat.sqrt h = n := by
        have := (Nat.pow_left_injective two_ne_zero) he
        omega
      rw [← hdeg, this]
    · intro hn
      exfalso; apply hn
      rw [mem_range]
      exact Nat.lt_succ_of_le (Nat.pow_le_pow_left (Nat.le_succ n) 2)

/-- GR (3.7), non-square exponents: `[q^ℓ] Σ_h A_h η χ_h = A_ℓ`. -/
theorem coeff_etaVirasoroSum_of_not_sq (A : ℕ → ℕ) {N : ℕ} (hN : ¬ IsDegenerateWeight N) :
    coeff N (etaVirasoroSum A) = A N := by
  rw [etaVirasoroSum, coeff_mk]
  simp only [coeff_etaVirasoroChar, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq, if_pos (by simp), sum_eq_zero, sub_zero]
  intro h _
  rw [if_neg]
  rintro ⟨-, rfl⟩
  exact hN (isDegenerateWeight_sq _)

/-- Telescoping GR (3.7) with `A_0 = 1`: `A_{N²} = 1 + Σ_{n=1}^{N} [q^{n²}] F`. -/
theorem sum_coeff_etaVirasoroSum_sq (A : ℕ → ℕ) (hA0 : A 0 = 1) (N : ℕ) :
    ∑ i ∈ range N, coeff ((i + 1) ^ 2) (etaVirasoroSum A) = (A (N ^ 2) : ℤ) - 1 := by
  induction N with
  | zero => simp [hA0]
  | succ N ih => rw [sum_range_succ, ih, coeff_etaVirasoroSum_sq]; ring

/-! ### Theta series -/

/-- `#{m ∈ ℤ : m ≡ j (mod r), t m² = N}`, the coefficient of `q^N` in `θ_{j,r,t}`. The range
`[-N, N]` is no restriction when `t ≥ 1`. -/
def thetaCoeff (r : ℕ) (j : ZMod r) (t N : ℕ) : ℕ :=
  ((Icc (-(N : ℤ)) N).filter fun m : ℤ => (m : ZMod r) = j ∧ (t : ℤ) * m ^ 2 = N).card

/-- The `q`-expansion of `θ_{n₀,r,t} = Σ_{n ≡ n₀ (r)} q^{t n²}` (GR (3.12)), `j = n₀ mod r`. -/
def thetaSeries (r : ℕ) (j : ZMod r) (t : ℕ) : PowerSeries ℤ :=
  mk fun N => thetaCoeff r j t N

/-- The coefficient of `q^{t n²}` (`n ≥ 1`, `t` square-free) in `θ_{j,r,t'}` (`t'` square-free):
it vanishes unless `t' = t`, and then counts `m ∈ {n, -n}` with `m ≡ j`. -/
theorem thetaCoeff_mul_sq {r : ℕ} (j : ZMod r) {t t' n : ℕ} (ht : Squarefree t)
    (ht' : Squarefree t') (hn : n ≠ 0) :
    thetaCoeff r j t' (t * n ^ 2) =
      (if t' = t ∧ ((n : ℤ) : ZMod r) = j then 1 else 0) +
        (if t' = t ∧ ((-(n : ℤ) : ℤ) : ZMod r) = j then 1 else 0) := by
  have key : ∀ m : ℤ, (t' : ℤ) * m ^ 2 = ((t * n ^ 2 : ℕ) : ℤ) ↔
      t' = t ∧ (m = n ∨ m = -n) := by
    intro m
    constructor
    · intro hm
      have hnat : t' * m.natAbs ^ 2 = t * n ^ 2 := by
        have : ((t' * m.natAbs ^ 2 : ℕ) : ℤ) = ((t * n ^ 2 : ℕ) : ℤ) := by
          push_cast; rw [sq_abs]; exact_mod_cast hm
        exact_mod_cast this
      have htt := squarefree_mul_sq_inj ht' ht hn hnat
      subst htt
      refine ⟨rfl, ?_⟩
      have : m.natAbs ^ 2 = n ^ 2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ht'.ne_zero) hnat
      have := (Nat.pow_left_injective two_ne_zero) this
      omega
    · rintro ⟨rfl, hm | hm⟩ <;> subst hm <;> push_cast <;> ring
  rw [thetaCoeff, card_filter]
  have hpt : ∀ m ∈ Icc (-((t * n ^ 2 : ℕ) : ℤ)) ((t * n ^ 2 : ℕ) : ℤ),
      (if (m : ZMod r) = j ∧ (t' : ℤ) * m ^ 2 = ((t * n ^ 2 : ℕ) : ℤ) then 1 else 0) =
        (if (n : ℤ) = m then (if t' = t ∧ ((n : ℤ) : ZMod r) = j then 1 else 0) else 0) +
          (if -(n : ℤ) = m then (if t' = t ∧ ((-(n : ℤ) : ℤ) : ZMod r) = j then 1 else 0)
            else 0) := by
    intro m _
    have hne : (n : ℤ) ≠ -(n : ℤ) := by omega
    simp only [key]
    by_cases h1 : (n : ℤ) = m
    · subst h1
      simp only [true_or, and_true, if_true, if_neg (Ne.symm hne), add_zero]
      split_ifs <;> simp_all
    · by_cases h2 : -(n : ℤ) = m
      · subst h2
        simp only [if_neg h1, or_true, and_true, if_true, zero_add]
        split_ifs <;> simp_all
      · simp only [if_neg h1, if_neg h2, add_zero]
        rw [if_neg]
        rintro ⟨-, -, h | h⟩
        · exact h1 h.symm
        · exact h2 h.symm
  rw [sum_congr rfl hpt, sum_add_distrib, sum_ite_eq, sum_ite_eq]
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ht.ne_zero
  have hle : (n : ℤ) ≤ ((t * n ^ 2 : ℕ) : ℤ) := by push_cast; nlinarith
  have hm1 : (n : ℤ) ∈ Icc (-((t * n ^ 2 : ℕ) : ℤ)) ((t * n ^ 2 : ℕ) : ℤ) := by
    rw [mem_Icc]; constructor <;> omega
  have hm2 : -(n : ℤ) ∈ Icc (-((t * n ^ 2 : ℕ) : ℤ)) ((t * n ^ 2 : ℕ) : ℤ) := by
    rw [mem_Icc]; constructor <;> omega
  simp only [hm1, hm2, if_true]

/-! ### The `q^{t n²}` coefficients of a theta decomposition -/

/-- The `N`-th coefficient of `Σ_{t ∈ T} Σ_j a_t(j) θ_{j,r_t,t}`. -/
theorem coeff_theta_sum (T : Finset ℕ) (r : ℕ → ℕ) [∀ t, NeZero (r t)]
    (a : (t : ℕ) → ZMod (r t) → ℂ) (N : ℕ) :
    coeff N (∑ t ∈ T, ∑ j : ZMod (r t), a t j • map (Int.castRingHom ℂ) (thetaSeries (r t) j t)) =
      ∑ t ∈ T, ∑ j : ZMod (r t), a t j * (thetaCoeff (r t) j t N : ℂ) := by
  simp [map_sum, coeff_map, thetaSeries]

/-- The uniqueness observation in the proof of GR Lemma 3.9: for `t ∈ T`, `n ≥ 1`, the
coefficient of `q^{t n²}` in `Σ_{t'} Σ_j a_{t'}(j) θ_{j,r_{t'},t'}` is `a_t(n) + a_t(-n)`. -/
theorem coeff_theta_decomposition (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t) (r : ℕ → ℕ)
    [∀ t, NeZero (r t)] (a : (t : ℕ) → ZMod (r t) → ℂ) {t : ℕ} (ht : t ∈ T) {n : ℕ}
    (hn : n ≠ 0) :
    coeff (t * n ^ 2)
        (∑ t ∈ T, ∑ j : ZMod (r t), a t j • map (Int.castRingHom ℂ) (thetaSeries (r t) j t)) =
      a t (n : ZMod (r t)) + a t (-(n : ZMod (r t))) := by
  rw [coeff_theta_sum, sum_eq_single t]
  · simp_rw [thetaCoeff_mul_sq _ (hT t ht) (hT t ht) hn]
    simp only [true_and, Int.cast_natCast, Int.cast_neg, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib,
      sum_ite_eq, mem_univ, if_true]
  · intro t' ht' hne
    refine sum_eq_zero fun j _ => ?_
    rw [thetaCoeff_mul_sq _ (hT t ht) (hT t' ht') hn]
    simp [hne]
  · intro h; exact absurd ht h

/-! ### Periodic sums -/

/-- `Σ_{i<r} g(i+1) = Σ_{x ∈ ℤ/r} g(x)`. -/
theorem sum_range_succ_zmod (r : ℕ) [NeZero r] (g : ZMod r → ℂ) :
    ∑ i ∈ range r, g ((i + 1 : ℕ) : ZMod r) = ∑ x : ZMod r, g x := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => g ((i + 1 : ℕ) : ZMod r))]
  have hinj : Function.Injective fun i : Fin r => ((i : ℕ) : ZMod r) := by
    intro i j hij
    simp only [ZMod.natCast_eq_natCast_iff'] at hij
    rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hij
    exact Fin.ext hij
  have hbij : Function.Bijective fun i : Fin r => ((i : ℕ) : ZMod r) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp [ZMod.card]⟩
  have hsh : ∑ x : ZMod r, g (x + 1) = ∑ x : ZMod r, g x :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod r)) g
  rw [← hsh]
  exact Fintype.sum_bijective _ hbij _ _ fun i => by simp

/-- `Σ_{i < k r} g(i+1) = k Σ_{x ∈ ℤ/r} g(x)`. -/
theorem sum_range_mul_succ_zmod (r : ℕ) [NeZero r] (g : ZMod r → ℂ) (k : ℕ) :
    ∑ i ∈ range (k * r), g ((i + 1 : ℕ) : ZMod r) = k * ∑ x : ZMod r, g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, ← sum_range_succ_zmod r g]
    have : ∀ i, (((k * r + i + 1 : ℕ)) : ZMod r) = ((i + 1 : ℕ) : ZMod r) := by
      intro i; push_cast; simp
    simp only [this]
    push_cast; ring

/-! ### GR Lemma 3.11 -/

/-- **GR Lemma 3.11** (`s_t` form). Let `F = η ch_V` satisfy

* (GR (3.5), composition series of `V` as a `c = 1` Virasoro module, characters (3.4) by
  Kac / Feigin–Fuchs) `F = Σ_h A_h η χ_h^{Vir}` with `A_h ∈ ℕ`, `A_0 = 1`;
* (GR Lemma 3.9, (3.22), Serre–Stark) `F = Σ_{t ∈ T} Σ_{j mod r_t} a_t(j) θ_{j,r_t,t}` with every
  `t ∈ T` square-free.

Then for every `t ∈ T`, `s_t = Σ_{j mod r_t} a_t(j)` is a non-negative real number. -/
theorem theta_weight_sum_nonneg (F : PowerSeries ℂ) (A : ℕ → ℕ) (hA0 : A 0 = 1)
    (hVir : F = map (Int.castRingHom ℂ) (etaVirasoroSum A))
    (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t) (r : ℕ → ℕ) [∀ t, NeZero (r t)]
    (a : (t : ℕ) → ZMod (r t) → ℂ)
    (hθ : F = ∑ t ∈ T, ∑ j : ZMod (r t), a t j • map (Int.castRingHom ℂ) (thetaSeries (r t) j t))
    {t : ℕ} (ht : t ∈ T) :
    ∃ x : ℝ, 0 ≤ x ∧ ∑ j : ZMod (r t), a t j = x := by
  set R := r t
  -- `p x = a_t(x) + a_t(-x)`; then `2 s_t = Σ_x p x`.
  set p : ZMod R → ℂ := fun x => a t x + a t (-x) with hp
  have h2s : 2 * ∑ j : ZMod R, a t j = ∑ x : ZMod R, p x := by
    have hneg : ∑ x : ZMod R, a t (-x) = ∑ x : ZMod R, a t x :=
      Equiv.sum_comp (Equiv.neg (ZMod R)) (a t)
    rw [hp, sum_add_distrib, hneg]; ring
  -- `p n = [q^{t n²}] F` for `n ≥ 1`.
  have hpF : ∀ n : ℕ, n ≠ 0 → p (n : ZMod R) = coeff (t * n ^ 2) F := by
    intro n hn
    rw [hθ, coeff_theta_decomposition T hT r a ht hn]
  by_cases ht1 : t = 1
  · -- `t = 1`: telescoping, `A_{(k r)²} = 1 + 2 k s_1`.
    subst ht1
    have htel : ∀ k : ℕ, ((A ((k * R) ^ 2) : ℤ) : ℂ) - 1 = k * (2 * ∑ j : ZMod R, a 1 j) := by
      intro k
      rw [h2s, ← sum_range_mul_succ_zmod R p k]
      have := sum_coeff_etaVirasoroSum_sq A hA0 (k * R)
      have hc := congrArg (fun z : ℤ => (z : ℂ)) this
      simp only [Int.cast_sum, Int.cast_sub, Int.cast_one] at hc
      rw [← hc]
      refine sum_congr rfl fun i _ => ?_
      rw [hpF (i + 1) (Nat.succ_ne_zero i), one_mul, hVir, coeff_map]
      simp
    -- `s_1` is real: `s_1 = (A_{R²} - 1)/2`.
    set x : ℝ := (((A ((1 * R) ^ 2) : ℤ) : ℝ) - 1) / 2 with hx
    have hsx : ∑ j : ZMod R, a 1 j = x := by
      have := htel 1
      rw [hx]; push_cast at this ⊢
      linear_combination (-1 / 2 : ℂ) * this
    refine ⟨x, ?_, hsx⟩
    by_contra hneg
    push Not at hneg
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (-(2 * x)))
    have hk' := htel k
    rw [hsx] at hk'
    have hre : ((A ((k * R) ^ 2) : ℤ) : ℝ) - 1 = k * (2 * x) := by
      have := congrArg Complex.re hk'
      simpa using this
    have hpos : (0 : ℝ) < -(2 * x) := by linarith
    have : (1 : ℝ) < k * (-(2 * x)) := by
      rw [div_lt_iff₀ hpos] at hk; linarith
    have hA : (0 : ℝ) ≤ ((A ((k * R) ^ 2) : ℤ) : ℝ) := by positivity
    nlinarith
  · -- `t > 1`: `t n²` is never a square, so `p n = A_{t n²} ≥ 0`.
    have hpA : ∀ y : ZMod R, p y = ((A (t * (y.val + R) ^ 2) : ℕ) : ℂ) := by
      intro y
      have hn : y.val + R ≠ 0 := by have := NeZero.ne R; omega
      have hy : (((y.val + R : ℕ)) : ZMod R) = y := by simp
      rw [← hy, hpF _ hn, hy, hVir, coeff_map,
        coeff_etaVirasoroSum_of_not_sq A (not_isSq_squarefree_mul_sq (hT t ht) ht1 hn)]
      simp
    refine ⟨(∑ y : ZMod R, (A (t * (y.val + R) ^ 2) : ℝ)) / 2, by positivity, ?_⟩
    have : ∑ j : ZMod R, a t j = (∑ x : ZMod R, p x) / 2 := by rw [← h2s]; ring
    rw [this]
    simp only [hpA]
    push_cast; rfl

/-- **GR Lemma 3.11.** Under the hypotheses of `theta_weight_sum_nonneg`, the weights
`w_t = (r_t √(2t))⁻¹ Σ_{n₀ mod r_t} a_t(n₀)` of GR (3.25) are non-negative reals. -/
theorem theta_weight_nonneg (F : PowerSeries ℂ) (A : ℕ → ℕ) (hA0 : A 0 = 1)
    (hVir : F = map (Int.castRingHom ℂ) (etaVirasoroSum A))
    (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t) (r : ℕ → ℕ) [∀ t, NeZero (r t)]
    (a : (t : ℕ) → ZMod (r t) → ℂ)
    (hθ : F = ∑ t ∈ T, ∑ j : ZMod (r t), a t j • map (Int.castRingHom ℂ) (thetaSeries (r t) j t))
    {t : ℕ} (ht : t ∈ T) :
    ∃ x : ℝ, 0 ≤ x ∧
      (1 / ((r t : ℂ) * (Real.sqrt (2 * t) : ℂ))) * ∑ j : ZMod (r t), a t j = x := by
  obtain ⟨x, hx, hs⟩ := theta_weight_sum_nonneg F A hA0 hVir T hT r a hθ ht
  refine ⟨1 / ((r t : ℝ) * Real.sqrt (2 * t)) * x, by positivity, ?_⟩
  rw [hs]; push_cast; rfl

end VOA.Classification.COne
