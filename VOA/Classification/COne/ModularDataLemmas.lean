/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Finite / matrix-analytic lemmas behind the `c = 1` classification (Gannon–Rayhaun)

This file isolates two purely finite arguments of T. Gannon and B. C. Rayhaun, *Classification of
rational `c = 1` vertex operator algebras and vertex operator superalgebras*, arXiv:2609.00122.
Nothing here mentions vertex algebras; the VOA-theoretic inputs appear as explicit hypotheses.

## B3. The squeeze in the proof of Theorem 2.18

The index type `ι` is `Rep(V)_{h∈ℤ}` (simple modules of integer conformal weight), `i₀` is the
vacuum, `S` the modular S-matrix restricted to `ι`, `d a = S_{a0}/S₀₀` the quantum dimensions,
and `ch b t` the real number `ch_{V_b}(it)` for `t > 0`. The hypotheses are

* `|S_ab| ≤ S₀₀ d_a d_b` (GR (2.35), citing [89, (4.2a)]);
* the identity (2.33) `Σ_b (D S₀₀ d_b − Σ_a d_a S_ab) ch_b(it) = 0` for `t > 0`;
* positivity `ch_b(it) > 0`;
* the leading-term behaviour used to read off the `q^{−c/24}` coefficient: with
  `q = e^{−2πt}`, `q^{c/24} ch_0(it) → 1` and `q^{c/24} ch_b(it) → 0` for `b ≠ 0` as `t → ∞`
  (pseudo-unitarity: `h_b > 0` for `b ≠ 0`).

`tannakian_squeeze` concludes `D = Σ_a d_a²` (GR (2.34)) and `S_ab = S₀₀ d_a d_b` for all
`a, b ∈ ι` (GR (2.37) and the squeeze after it). `vacuum_identity_of_factorized` is the algebra
of the converse direction (GR (2.38)).

## B2. The arithmetic core of Proposition 3.12

`T` is the finite set of square-free `t` with `4t ∣ C` (`C` the conductor), `w t ≥ 0` the
coefficients of Lemma 3.10/3.11 with `Σ_t w_t = S₀₀`, and the Galois bound (3.35)
`|Σ_t (2t/ℓ) w_t| ≥ S₀₀` is assumed for every positive `ℓ` coprime to `C`. For such `ℓ` (odd,
since `C` is even) the Kronecker symbol `(2t/ℓ)` is the Jacobi symbol `J(2t | ℓ)`.
`exists_jacobi_sign_flip` is the CRT construction of `ℓ⋆` with `(2t₁/ℓ⋆) = −(2t₂/ℓ⋆)` (GR (3.37));
it needs only `ℓ⋆` coprime to `C`, not prime, so no Dirichlet theorem is used.
`existsUnique_weight_ne_zero` concludes that exactly one `w_t` is nonzero.
-/

namespace VOA.Classification.COne

open Finset Filter Topology

/-! ### B3: the squeeze of Theorem 2.18 -/

/-- Leading-coefficient extraction: if `Σ_b C_b g_b(t) = 0` eventually, `g_{i₀} → 1` and
`g_b → 0` for `b ≠ i₀`, then `C_{i₀} = 0`. -/
theorem coeff_eq_zero_of_tendsto {ι : Type*} [Fintype ι] (i₀ : ι) (C : ι → ℂ)
    (g : ι → ℝ → ℝ) (h₀ : Tendsto (g i₀) atTop (𝓝 1))
    (h : ∀ b, b ≠ i₀ → Tendsto (g b) atTop (𝓝 0))
    (hid : ∀ᶠ t in atTop, ∑ b, C b * (g b t : ℂ) = 0) : C i₀ = 0 := by
  classical
  have hT : Tendsto (fun t => ∑ b, C b * (g b t : ℂ)) atTop
      (𝓝 (∑ b, C b * (((if b = i₀ then 1 else 0 : ℝ)) : ℂ))) := by
    apply tendsto_finsetSum
    intro b _
    apply Tendsto.const_mul
    apply (Complex.continuous_ofReal.tendsto _).comp
    by_cases hb : b = i₀
    · subst hb; simpa using h₀
    · simpa [hb] using h b hb
  have hT0 : Tendsto (fun t => ∑ b, C b * (g b t : ℂ)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hid.mono fun t ht => ht.symm)
  have := tendsto_nhds_unique hT hT0
  rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)] at this
  simpa using this

/-- **The squeeze in GR Theorem 2.18.** Abstract form: from the bound `‖S_ab‖ ≤ S₀₀ d_a d_b`,
the identity (2.33) evaluated at `τ = it`, positivity of characters, and the leading-term
behaviour of the characters as `t → ∞`, conclude `D = Σ d_a²` and `S_ab = S₀₀ d_a d_b`. -/
theorem tannakian_squeeze {ι : Type*} [Fintype ι] (i₀ : ι) (S : ι → ι → ℂ)
    (d : ι → ℝ) (S₀₀ c : ℝ) (D : ℂ) (ch : ι → ℝ → ℝ)
    (hd : ∀ a, 0 < d a) (hd₀ : d i₀ = 1) (hS₀₀ : 0 < S₀₀)
    (hSa0 : ∀ a, S a i₀ = S₀₀ * d a)
    (hbound : ∀ a b, ‖S a b‖ ≤ S₀₀ * d a * d b)
    (hch : ∀ b, ∀ t, 0 < t → 0 < ch b t)
    (hlead₀ : Tendsto (fun t => Real.exp (-(2 * Real.pi * t * c / 24)) * ch i₀ t) atTop (𝓝 1))
    (hlead : ∀ b, b ≠ i₀ →
      Tendsto (fun t => Real.exp (-(2 * Real.pi * t * c / 24)) * ch b t) atTop (𝓝 0))
    (hid : ∀ t, 0 < t →
      ∑ b, (D * S₀₀ * d b - ∑ a, d a * S a b) * (ch b t : ℂ) = 0) :
    D = ((∑ a, d a ^ 2 : ℝ) : ℂ) ∧ ∀ a b, S a b = S₀₀ * d a * d b := by
  set Cf : ι → ℂ := fun b => D * S₀₀ * d b - ∑ a, d a * S a b with hCf
  -- Step 1: the `q^{-c/24}` coefficient gives `C_{i₀} = 0`, i.e. `D = Σ d_a²`.
  have hC0 : Cf i₀ = 0 := by
    refine coeff_eq_zero_of_tendsto i₀ Cf
      (fun b t => Real.exp (-(2 * Real.pi * t * c / 24)) * ch b t) hlead₀ hlead ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have := hid t ht
    calc ∑ b, Cf b * ((Real.exp (-(2 * Real.pi * t * c / 24)) * ch b t : ℝ) : ℂ)
        = (Real.exp (-(2 * Real.pi * t * c / 24)) : ℂ) *
            ∑ b, (D * S₀₀ * d b - ∑ a, d a * S a b) * (ch b t : ℂ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hCf]; push_cast; ring
      _ = 0 := by rw [this, mul_zero]
  have hD : D = ((∑ a, d a ^ 2 : ℝ) : ℂ) := by
    have h1 : Cf i₀ = (D - ((∑ a, d a ^ 2 : ℝ) : ℂ)) * S₀₀ := by
      simp only [hCf, hd₀, hSa0]; push_cast
      rw [sub_mul, Finset.sum_mul, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_; ring
    rw [hC0] at h1
    have hS : (S₀₀ : ℂ) ≠ 0 := by exact_mod_cast hS₀₀.ne'
    have := (mul_eq_zero.1 h1.symm).resolve_right hS
    exact sub_eq_zero.1 this
  refine ⟨hD, ?_⟩
  -- Step 2: real parts. `Re C_b = Σ_a d_a (S₀₀ d_a d_b - Re S_ab)`.
  have hre : ∀ b, (Cf b).re = ∑ a, d a * (S₀₀ * d a * d b - (S a b).re) := by
    intro b
    simp only [hCf, hD]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_sum, mul_zero, sub_zero, zero_mul]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hterm : ∀ a b, 0 ≤ S₀₀ * d a * d b - (S a b).re := fun a b =>
    sub_nonneg.2 ((Complex.re_le_norm _).trans (hbound a b))
  have hre_nonneg : ∀ b, 0 ≤ (Cf b).re := fun b => by
    rw [hre]; exact Finset.sum_nonneg fun a _ => mul_nonneg (hd a).le (hterm a b)
  -- Step 3: evaluate the real part at `t = 1`.
  have hsum1 : ∑ b, (Cf b).re * ch b 1 = 0 := by
    have := congrArg Complex.re (hid 1 one_pos)
    simpa [hCf, Complex.re_sum, Complex.mul_re] using this
  have hCre : ∀ b, (Cf b).re = 0 := by
    intro b
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
      mul_nonneg (hre_nonneg b) (hch b 1 one_pos).le).1 hsum1 b (Finset.mem_univ _)
    exact (mul_eq_zero.1 h).resolve_right (hch b 1 one_pos).ne'
  have hReS : ∀ a b, (S a b).re = S₀₀ * d a * d b := by
    intro a b
    have h := hCre b
    rw [hre] at h
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      mul_nonneg (hd a).le (hterm a b)).1 h a (Finset.mem_univ _)
    have := (mul_eq_zero.1 h2).resolve_left (hd a).ne'
    linarith
  -- Step 4: `‖S_ab‖ ≤ Re S_ab` forces `S_ab` real.
  intro a b
  have hnn : 0 ≤ (S a b).re := by
    rw [hReS]; exact mul_nonneg (mul_nonneg hS₀₀.le (hd a).le) (hd b).le
  have hnorm : |(S a b).re| = ‖S a b‖ := by
    rw [abs_of_nonneg hnn]
    exact le_antisymm (Complex.re_le_norm _) (by rw [hReS]; exact hbound a b)
  have him : (S a b).im = 0 := Complex.abs_re_eq_norm.1 hnorm
  apply Complex.ext
  · simp [hReS a b]
  · simp [him]

/-- The converse direction of GR Theorem 2.18 (algebra of (2.38)): if `S_ab = S₀₀ d_a d_b`,
then `Σ_a d_a S_ab = S₀₀ (Σ_a d_a²) d_b`. -/
theorem vacuum_identity_of_factorized {ι : Type*} [Fintype ι] (S : ι → ι → ℂ) (d : ι → ℝ)
    (S₀₀ : ℝ) (h : ∀ a b, S a b = S₀₀ * d a * d b) (b : ι) :
    ∑ a, (d a : ℂ) * S a b = S₀₀ * ((∑ a, d a ^ 2 : ℝ) : ℂ) * d b := by
  simp only [h]; push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### B2: the arithmetic core of Proposition 3.12 -/

/-- For `u` odd,, `ℓ ≡ 1 (mod 4)` and `ℓ ≡ 1 (mod u)`, `J(u | ℓ) = 1`. -/
theorem jacobiSym_odd_eq_one {u ℓ : ℕ} (hu : Odd u) (hℓ4 : ℓ % 4 = 1) (hℓu : ℓ ≡ 1 [MOD u]) :
    jacobiSym u ℓ = 1 := by
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' hu hℓ4]
  have : ((ℓ : ℤ)) % (u : ℤ) = (1 : ℤ) % (u : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hℓu
    simpa [Nat.ModEq, Int.natCast_mod] using this
  rw [jacobiSym.mod_left' this, jacobiSym.one_left]

/-- For any `u ≠ 0` with `ℓ ≡ 1 (mod 4u)`, `J(u | ℓ) = 1`. -/
theorem jacobiSym_eq_one_of_modEq {u ℓ : ℕ} (hu : u ≠ 0) (hℓ : ℓ ≡ 1 [MOD 4 * u]) :
    jacobiSym u ℓ = 1 := by
  have hodd : Odd ℓ := by
    have h4 : ℓ ≡ 1 [MOD 2] := hℓ.of_dvd (Dvd.intro (2 * u) (by ring))
    exact Nat.odd_iff.2 h4
  rw [jacobiSym.mod_right _ hodd]
  have : ℓ % (4 * (u : ℤ).natAbs) = 1 := by
    rw [Int.natAbs_natCast]
    have : ℓ % (4 * u) = 1 % (4 * u) := hℓ
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [this, jacobiSym.one_right]

theorem jacobiSym_two_of_mod_eight {ℓ : ℕ} (hℓ : Odd ℓ) :
    jacobiSym 2 ℓ = if ℓ % 8 = 1 ∨ ℓ % 8 = 7 then 1 else -1 := by
  rw [jacobiSym.at_two hℓ, ZMod.χ₈_nat_eq_if_mod_eight]
  have : ℓ % 2 ≠ 0 := by rw [Nat.odd_iff] at hℓ; omega
  simp [this]

/-- Squarefree, `p ∣ t` ⇒ `t = p * u` with `p ∤ u`. -/
theorem squarefree_split {t p : ℕ} (ht : Squarefree t) (hp : p.Prime) (hpt : p ∣ t) :
    ∃ u, t = p * u ∧ ¬ p ∣ u := by
  obtain ⟨u, rfl⟩ := hpt
  refine ⟨u, rfl, fun hpu => ?_⟩
  obtain ⟨v, rfl⟩ := hpu
  have := ht p ⟨v, by ring⟩
  exact hp.not_isUnit (by simpa using this)

/-- Case of an odd prime `p ∣ t₁`, `p ∤ t₂`. -/
theorem exists_flip_odd {C t₁ t₂ p : ℕ} (hC0 : C ≠ 0) (hC8 : 8 ∣ C)
    (h₁ : Squarefree t₁) (h₁C : 4 * t₁ ∣ C) (h₂C : 4 * t₂ ∣ C) (h₂0 : t₂ ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp₁ : p ∣ t₁) (hp₂ : ¬ p ∣ t₂) :
    ∃ ℓ : ℕ, ℓ.Coprime C ∧ jacobiSym (2 * (t₁ : ℤ)) ℓ = -1 ∧ jacobiSym (2 * (t₂ : ℤ)) ℓ = 1 := by
  haveI := Fact.mk hp
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set M := ordCompl[p] C with hM
  have hcop : p.Coprime M := Nat.coprime_ordCompl hp hC0
  have hp_not_dvd_4 : ∀ x, ¬ p ∣ x → ¬ p ∣ 4 * x := by
    intro x hx h
    rcases (Nat.Prime.dvd_mul hp).1 h with h4 | h4
    · have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    · exact hx h4
  have h8M : 8 ∣ M := by
    apply Nat.dvd_ordCompl_of_dvd_not_dvd hC8
    intro h
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
    rw [ZMod.ringChar_zmod_n]; exact hp2)
  set n := a.val
  have hn : (n : ZMod p) = a := ZMod.natCast_zmod_val a
  have hpn : ¬ p ∣ n := by
    intro h
    apply ha
    rw [← hn, (ZMod.natCast_eq_zero_iff n p).2 h]
    exact ⟨0, by simp⟩
  obtain ⟨ℓ, hℓp, hℓM⟩ := Nat.chineseRemainder hcop n 1
  have hℓ8 : ℓ ≡ 1 [MOD 8] := hℓM.of_dvd h8M
  have hℓ8' : ℓ % 8 = 1 := hℓ8
  have hℓ4 : ℓ % 4 = 1 := by omega
  have hℓodd : Odd ℓ := Nat.odd_iff.2 (by omega)
  have hJ2 : jacobiSym 2 ℓ = 1 := by rw [jacobiSym_two_of_mod_eight hℓodd]; simp [hℓ8']
  -- `J(u | ℓ) = 1` for `u` with `4u ∣ C`, `p ∤ u`.
  have hJu : ∀ u, u ≠ 0 → 4 * u ∣ C → ¬ p ∣ u → jacobiSym u ℓ = 1 := by
    intro u hu0 huC hpu
    apply jacobiSym_eq_one_of_modEq hu0
    exact hℓM.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd huC (hp_not_dvd_4 u hpu))
  have hJp : jacobiSym p ℓ = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hpodd hℓ4]
    have : ((ℓ : ℤ)) % (p : ℤ) = (n : ℤ) % (p : ℤ) := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hℓp
      simpa [Nat.ModEq, Int.natCast_mod] using this
    rw [jacobiSym.mod_left' this, ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
    simpa [hn] using ha
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · -- coprimality: `C = p^k * M`
    rw [← Nat.ordProj_mul_ordCompl_eq_self C p]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      apply hpn
      have h1 : ℓ % p = n % p := hℓp
      rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
      omega
    · have := hℓM.gcd_eq
      simpa [Nat.Coprime] using this
  · obtain ⟨u, rfl, hpu⟩ := squarefree_split h₁ hp hp₁
    have hu0 : u ≠ 0 := by rintro rfl; simp at h₁
    have huC : 4 * u ∣ C := (Dvd.intro p (by ring) : 4 * u ∣ 4 * (p * u)).trans h₁C
    push_cast
    rw [show (2 : ℤ) * (p * u) = 2 * p * u by ring, jacobiSym.mul_left, jacobiSym.mul_left,
      hJ2, hJp, hJu u hu0 huC hpu]
    norm_num
  · rw [jacobiSym.mul_left, hJ2, hJu t₂ h₂0 h₂C hp₂, one_mul]

/-- Case `p = 2`: `t₁` even, `t₂` odd. -/
theorem exists_flip_two {C t₁ t₂ : ℕ} (hC0 : C ≠ 0)
    (h₁ : Squarefree t₁) (h₁C : 4 * t₁ ∣ C) (h₂C : 4 * t₂ ∣ C)
    (hp₁ : 2 ∣ t₁) (hp₂ : ¬ 2 ∣ t₂) :
    ∃ ℓ : ℕ, ℓ.Coprime C ∧ jacobiSym (2 * (t₁ : ℤ)) ℓ = 1 ∧ jacobiSym (2 * (t₂ : ℤ)) ℓ = -1 := by
  set M := ordCompl[2] C with hM
  have hcop : (8 : ℕ).Coprime M := by
    have := Nat.coprime_ordCompl Nat.prime_two hC0
    simpa using Nat.Coprime.pow_left 3 this
  obtain ⟨ℓ, hℓ8, hℓM⟩ := Nat.chineseRemainder hcop 5 1
  have hℓ8' : ℓ % 8 = 5 := hℓ8
  have hℓ4 : ℓ % 4 = 1 := by omega
  have hℓodd : Odd ℓ := Nat.odd_iff.2 (by omega)
  have hJ2 : jacobiSym 2 ℓ = -1 := by rw [jacobiSym_two_of_mod_eight hℓodd]; simp [hℓ8']
  have hJu : ∀ u, u ∣ C → ¬ 2 ∣ u → jacobiSym u ℓ = 1 := by
    intro u huC h2u
    apply jacobiSym_odd_eq_one (Nat.odd_iff.2 (by omega)) hℓ4
    exact hℓM.of_dvd (Nat.dvd_ordCompl_of_dvd_not_dvd huC h2u)
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · rw [← Nat.ordProj_mul_ordCompl_eq_self C 2]
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    · have := hℓM.gcd_eq
      simpa [Nat.Coprime] using this
  · obtain ⟨u, rfl, h2u⟩ := squarefree_split h₁ Nat.prime_two hp₁
    have huC : u ∣ C := (Dvd.intro 8 (by ring) : u ∣ 4 * (2 * u)).trans h₁C
    push_cast
    rw [show (2 : ℤ) * (2 * u) = 2 * 2 * u by ring, jacobiSym.mul_left, jacobiSym.mul_left,
      hJ2, hJu u huC h2u]
    norm_num
  · have huC : t₂ ∣ C := (Dvd.intro_left _ rfl : t₂ ∣ 4 * t₂).trans h₂C
    rw [jacobiSym.mul_left, hJ2, hJu t₂ huC hp₂, mul_one]

/-- **The CRT construction of `ℓ⋆` (GR (3.36)–(3.37)).** For distinct square-free `t₁, t₂` with
`4t_i ∣ C` and `8 ∣ C`, there is `ℓ` coprime to `C` with `(2t₁/ℓ) = −(2t₂/ℓ) = ±1`. -/
theorem exists_jacobi_sign_flip {C t₁ t₂ : ℕ} (hC0 : C ≠ 0) (hC8 : 8 ∣ C)
    (h₁ : Squarefree t₁) (h₁C : 4 * t₁ ∣ C) (h₂ : Squarefree t₂) (h₂C : 4 * t₂ ∣ C)
    (hne : t₁ ≠ t₂) :
    ∃ ℓ : ℕ, ℓ.Coprime C ∧
      ((jacobiSym (2 * (t₁ : ℤ)) ℓ = -1 ∧ jacobiSym (2 * (t₂ : ℤ)) ℓ = 1) ∨
       (jacobiSym (2 * (t₁ : ℤ)) ℓ = 1 ∧ jacobiSym (2 * (t₂ : ℤ)) ℓ = -1)) := by
  have hex : ∃ p, p.Prime ∧ ¬ (p ∣ t₁ ↔ p ∣ t₂) := by
    by_contra hcon
    push Not at hcon
    exact hne ((Nat.Squarefree.ext_iff h₁ h₂).2 fun p hp => hcon p hp)
  obtain ⟨p, hp, hpt⟩ := hex
  have h₁0 : t₁ ≠ 0 := h₁.ne_zero
  have h₂0 : t₂ ≠ 0 := h₂.ne_zero
  by_cases h1 : p ∣ t₁
  · have h2 : ¬ p ∣ t₂ := fun h => hpt ⟨fun _ => h, fun _ => h1⟩
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨ℓ, hc, ha, hb⟩ := exists_flip_two hC0 h₁ h₁C h₂C h1 h2
      exact ⟨ℓ, hc, Or.inr ⟨ha, hb⟩⟩
    · obtain ⟨ℓ, hc, ha, hb⟩ := exists_flip_odd hC0 hC8 h₁ h₁C h₂C h₂0 hp hp2 h1 h2
      exact ⟨ℓ, hc, Or.inl ⟨ha, hb⟩⟩
  · have h2 : p ∣ t₂ := by by_contra h2; exact hpt ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨ℓ, hc, ha, hb⟩ := exists_flip_two hC0 h₂ h₂C h₁C h2 h1
      exact ⟨ℓ, hc, Or.inl ⟨hb, ha⟩⟩
    · obtain ⟨ℓ, hc, ha, hb⟩ := exists_flip_odd hC0 hC8 h₂ h₂C h₁C h₁0 hp hp2 h2 h1
      exact ⟨ℓ, hc, Or.inr ⟨hb, ha⟩⟩

theorem abs_jacobiSym_cast_le_one (a : ℤ) (b : ℕ) : |(jacobiSym a b : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

/-- **GR Proposition 3.12, arithmetic core (at most one).** -/
theorem weight_ne_zero_unique {C : ℕ} (hC0 : C ≠ 0) (hC8 : 8 ∣ C) (T : Finset ℕ)
    (hT : ∀ t ∈ T, Squarefree t ∧ 4 * t ∣ C) (w : ℕ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t) {S₀₀ : ℝ}
    (hsum : ∑ t ∈ T, w t = S₀₀)
    (hbound : ∀ ℓ : ℕ, ℓ.Coprime C →
      S₀₀ ≤ |∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℝ) * w t|) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, w t₁ ≠ 0 → w t₂ ≠ 0 → t₁ = t₂ := by
  intro t₁ ht₁ t₂ ht₂ hw₁ hw₂
  by_contra hne
  obtain ⟨h₁, h₁C⟩ := hT t₁ ht₁
  obtain ⟨h₂, h₂C⟩ := hT t₂ ht₂
  obtain ⟨ℓ, hcop, hJ⟩ := exists_jacobi_sign_flip hC0 hC8 h₁ h₁C h₂ h₂C hne
  set J : ℕ → ℝ := fun t => (jacobiSym (2 * (t : ℤ)) ℓ : ℝ) with hJdef
  have hw₁p : 0 < w t₁ := lt_of_le_of_ne (hw t₁ ht₁) (Ne.symm hw₁)
  have hw₂p : 0 < w t₂ := lt_of_le_of_ne (hw t₂ ht₂) (Ne.symm hw₂)
  have ht₂' : t₂ ∈ T.erase t₁ := Finset.mem_erase.2 ⟨Ne.symm hne, ht₂⟩
  set R := (T.erase t₁).erase t₂
  have hsplit : ∀ f : ℕ → ℝ, ∑ t ∈ T, f t = f t₁ + f t₂ + ∑ t ∈ R, f t := by
    intro f
    rw [← Finset.add_sum_erase T f ht₁, ← Finset.add_sum_erase _ f ht₂', add_assoc]
  have hpair : |J t₁ * w t₁ + J t₂ * w t₂| < w t₁ + w t₂ := by
    rcases hJ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [hJdef, ha, hb]; push_cast
      rw [abs_lt]; constructor <;> linarith
    · simp only [hJdef, ha, hb]; push_cast
      rw [abs_lt]; constructor <;> linarith
  have hrest : |∑ t ∈ R, J t * w t| ≤ ∑ t ∈ R, w t := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t ht => ?_)
    have htT : t ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
    rw [abs_mul, abs_of_nonneg (hw t htT)]
    exact mul_le_of_le_one_left (hw t htT) (abs_jacobiSym_cast_le_one _ _)
  have key : |∑ t ∈ T, J t * w t| < S₀₀ := by
    rw [hsplit, ← hsum, hsplit]
    calc |J t₁ * w t₁ + J t₂ * w t₂ + ∑ t ∈ R, J t * w t|
        ≤ |J t₁ * w t₁ + J t₂ * w t₂| + |∑ t ∈ R, J t * w t| := abs_add_le _ _
      _ < w t₁ + w t₂ + ∑ t ∈ R, w t := add_lt_add_of_lt_of_le hpair hrest
  exact absurd (hbound ℓ hcop) (not_le.2 key)

/-- **GR Proposition 3.12, arithmetic core.** Given finitely many square-free `t` with `4t ∣ C`
(`8 ∣ C`; in GR `24 ∣ C`), weights `w_t ≥ 0` summing to `S₀₀ > 0`, and the Galois bound
`|Σ_t (2t/ℓ) w_t| ≥ S₀₀` for every positive `ℓ` coprime to `C`, exactly one `w_t` is nonzero. -/
theorem existsUnique_weight_ne_zero {C : ℕ} (hC0 : C ≠ 0) (hC8 : 8 ∣ C) (T : Finset ℕ)
    (hT : ∀ t ∈ T, Squarefree t ∧ 4 * t ∣ C) (w : ℕ → ℝ) (hw : ∀ t ∈ T, 0 ≤ w t) {S₀₀ : ℝ}
    (hS₀₀ : 0 < S₀₀) (hsum : ∑ t ∈ T, w t = S₀₀)
    (hbound : ∀ ℓ : ℕ, ℓ.Coprime C →
      S₀₀ ≤ |∑ t ∈ T, (jacobiSym (2 * (t : ℤ)) ℓ : ℝ) * w t|) :
    ∃! t, t ∈ T ∧ w t ≠ 0 := by
  obtain ⟨t, ht, hwt⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne hS₀₀.ne')
  exact ⟨t, ⟨ht, hwt⟩, fun t' ⟨ht', hwt'⟩ =>
    weight_ne_zero_unique hC0 hC8 T hT w hw hsum hbound t' ht' t ht hwt' hwt⟩

end VOA.Classification.COne
