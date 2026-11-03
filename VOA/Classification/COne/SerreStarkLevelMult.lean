/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkIntegral

/-!
# Serre–Stark S4-1: multiplicativity of eigenforms on one square class

This is Serre–Stark's "easy" structure theorem for eigenforms (Serre–Stark, LNM 627, §3;
Achimescu–Saha, arXiv:0803.3788, Lemma 3.3(a) and Theorem 3.1), proved from the bounded-coefficient
residual `SerreStarkBoundedCoeff24` alone:

* `eigen_pow_of_fg`: for a `T(p²)`-eigensequence with coefficients in a finitely generated
  subgroup of `ℂ`, and `p² ∤ m`, `a(p^{2j} m) = (χ(p)(m/p))^j a(m)`;
* `exists_squarefree_class`: the positive support of a form all of whose nonzero coefficients
  pairwise multiply to squares lies in `t·□` for a squarefree `t`;
* `squarefree_dvd_of_eigen`: for a simultaneous eigenform, this `t` divides `N`;
* `mCoeff_mul_sq_of_coprime`: `a(n v²) = χ(v) (t/v) a(n)` for every `n > 0` and every `v`
  prime to `N`.
-/

open Complex

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## The recurrence along `m p^{2j}`, solved -/

section Pow

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]

/-- **Lemma 3.3(a) of Achimescu–Saha.** For a `T(p²)`-eigensequence with coefficients in a
finitely generated subgroup of `ℂ` and `p² ∤ m`, `a(p^{2j} m) = (χ(p)(m/p))^j a(m)`. -/
theorem eigen_pow_of_fg (hpN : Nat.Coprime p N) {a : ℕ → ℂ} {L : Submodule ℤ ℂ} (hL : L.FG)
    (haL : ∀ n, a n ∈ L) {c : ℂ} (hc : ∀ n, heckeCoeff χ p a n = c * a n) {m : ℕ}
    (hm : ¬ p ^ 2 ∣ m) (j : ℕ) :
    a (p ^ (2 * j) * m) = (χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ)) ^ j * a m := by
  set x := χ (p : ZMod N) with hx
  set ε := x * (legendreSym p (m : ℤ) : ℂ) with hε
  set A : ℕ → ℂ := fun k => a (p ^ (2 * k) * m) with hA
  have hA0 : A 0 = a m := by simp [hA]
  have r0 : A 1 + ε / p * A 0 = c * A 0 := by
    have := hc m
    rw [heckeCoeff_base χ p a hm] at this
    change a (p ^ (2 * 1) * m) + ε / p * a (p ^ (2 * 0) * m) = c * a (p ^ (2 * 0) * m)
    simp only [Nat.mul_zero, pow_zero, one_mul, Nat.mul_one]
    rw [hε]; linear_combination this
  have rk : ∀ k, A (k + 2) + x ^ 2 / p * A k = c * A (k + 1) := by
    intro k
    have := hc (p ^ (2 * (k + 1)) * m)
    rw [heckeCoeff_step χ p a m k] at this
    simpa [hA] using this
  suffices H : ∀ k, A k = ε ^ k * A 0 ∧ A (k + 1) = ε ^ (k + 1) * A 0 by
    have := (H j).1
    rw [hA0] at this
    simpa [hA] using this
  by_cases ham : a m = 0
  · have h0 : A 0 = 0 := by rw [hA0]; exact ham
    have h1 : A 1 = 0 := by rw [h0, mul_zero, mul_zero, add_zero] at r0; exact r0
    have Z : ∀ k, A k = 0 ∧ A (k + 1) = 0 := by
      intro k
      induction k with
      | zero => exact ⟨h0, h1⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have := rk k
        rw [ih.1, ih.2, mul_zero, mul_zero, add_zero] at this
        exact this
    intro k
    rw [(Z k).1, (Z k).2, h0]
    simp
  · have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpf.out.ne_zero
    obtain ⟨hpm, hcval⟩ := eigenvalue_of_fg χ p hpN hL haL hc ham hm
    have hleg0 : legendreSym p (m : ℤ) ≠ 0 := by
      intro h0
      rw [legendreSym.eq_zero_iff] at h0
      exact hpm ((ZMod.natCast_eq_zero_iff m p).1 (by exact_mod_cast h0))
    have hl2 : (legendreSym p (m : ℤ) : ℂ) ^ 2 = 1 := by
      have := legendreSym.sq_one p (a := (m : ℤ)) (by
        intro h0; exact hleg0 ((legendreSym.eq_zero_iff p _).2 h0))
      exact_mod_cast this
    have hx2 : x ^ 2 = ε ^ 2 := by rw [hε, mul_pow, hl2, mul_one]
    have hc' : c = ε * (1 + 1 / (p : ℂ)) := by rw [hcval, hε]
    have h1 : A 1 = ε * A 0 := by
      rw [hc'] at r0
      linear_combination r0
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e := rk k
      rw [ih.1, ih.2, hc', hx2] at e
      linear_combination e

end Pow

/-! ## Square classes -/

/-- If `n · s² t` is a square with `t` squarefree, then `n ∈ t·□`. -/
theorem exists_eq_mul_sq_of_isSquare {n s t : ℕ} (hs : 0 < s) (ht : Squarefree t)
    (h : IsSquare (n * (s ^ 2 * t))) : ∃ x, n = t * x ^ 2 := by
  obtain ⟨k, hk⟩ := h
  have ht0 : 0 < t := Nat.pos_of_ne_zero ht.ne_zero
  have hsk : s ∣ k := by
    rw [← Nat.pow_dvd_pow_iff two_ne_zero]
    exact ⟨n * t, by rw [sq k, ← hk]; ring⟩
  obtain ⟨k', rfl⟩ := hsk
  have e1 : k' ^ 2 = n * t := by
    have : s ^ 2 * (k' ^ 2) = s ^ 2 * (n * t) := by
      calc s ^ 2 * (k' ^ 2) = s * k' * (s * k') := by ring
        _ = n * (s ^ 2 * t) := hk.symm
        _ = s ^ 2 * (n * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have htk : t ∣ k' := (ht.dvd_pow_iff_dvd two_ne_zero).1 ⟨n, by rw [e1]; ring⟩
  obtain ⟨x, rfl⟩ := htk
  refine ⟨x, ?_⟩
  have : t * (t * x ^ 2) = t * n := by
    calc t * (t * x ^ 2) = (t * x) ^ 2 := by ring
      _ = n * t := e1
      _ = t * n := by ring
  exact (Nat.eq_of_mul_eq_mul_left ht0 this).symm

/-- The positive support of a form whose nonzero coefficients pairwise multiply to squares lies
in one class `t·□`, `t` squarefree; `t·s₀²` is in the support. -/
theorem exists_squarefree_class {a : ℕ → ℂ}
    (hsq : ∀ m₁ m₂ : ℕ, 0 < m₁ → 0 < m₂ → a m₁ ≠ 0 → a m₂ ≠ 0 → IsSquare (m₁ * m₂))
    {n₀ : ℕ} (hn₀ : 0 < n₀) (ha₀ : a n₀ ≠ 0) :
    ∃ t s₀ : ℕ, Squarefree t ∧ 0 < s₀ ∧ n₀ = s₀ ^ 2 * t ∧
      ∀ n, 0 < n → a n ≠ 0 → ∃ x, n = t * x ^ 2 := by
  obtain ⟨t, s₀, ht0, hs0, he, ht⟩ := Nat.sq_mul_squarefree_of_pos hn₀
  refine ⟨t, s₀, ht, hs0, he.symm, fun n hn han => ?_⟩
  have := hsq n n₀ hn hn₀ han ha₀
  rw [← he] at this
  exact exists_eq_mul_sq_of_isSquare hs0 ht this

/-- A squarefree number all of whose prime factors divide `N` divides `N`. -/
theorem squarefree_dvd_of_primes {t N : ℕ} (hN : N ≠ 0) (ht : Squarefree t)
    (h : ∀ q, q.Prime → q ∣ t → q ∣ N) : t ∣ N := by
  rw [← Nat.factorization_le_iff_dvd ht.ne_zero hN]
  intro q
  by_cases hq : q.Prime ∧ q ∣ t
  · have h1 := ht.natFactorization_le_one q
    have h2 := (hq.1.dvd_iff_one_le_factorization hN).1 (h q hq.1 hq.2)
    exact h1.trans h2
  · have : t.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      tauto
    rw [this]; exact Nat.zero_le _

/-! ## Eigenforms on `M_{1/2}(N, χ)` -/

/-- A prime prime to `N`, `24 ∣ N`, is admissible for `T(p²)`. -/
def hPrimeOfCoprime {N p : ℕ} (h24 : 24 ∣ N) (hp : p.Prime) (hpN : p.Coprime N) : HPrime N :=
  ⟨p, hp, by
    rintro rfl
    have h2 : 2 ∣ N := (show 2 ∣ 24 by norm_num).trans h24
    exact absurd (Nat.Coprime.coprime_dvd_right h2 hpN) (by norm_num), hpN⟩

/-- `a(n p²) = ε a(n)` with `ε = χ(p)(m/p)`, `n = p^{2k} m`, `p² ∤ m`, and in addition
`a(n) = ε^k a(m)` (sequence form). -/
theorem seq_mul_sq_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (p : ℕ) [hpf : Fact p.Prime]
    (hpN : Nat.Coprime p N) {a : ℕ → ℂ} {L : Submodule ℤ ℂ} (hL : L.FG)
    (haL : ∀ n, a n ∈ L) {c : ℂ} (hc : ∀ n, heckeCoeff χ p a n = c * a n) {n : ℕ} (hn : 0 < n) :
    ∃ m k : ℕ, ¬ p ^ 2 ∣ m ∧ n = p ^ (2 * k) * m ∧
      a (n * p ^ 2) = χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ) * a n ∧
      a n = (χ (p : ZMod N) * (legendreSym p (m : ℤ) : ℂ)) ^ k * a m ∧
      (a m ≠ 0 → ¬ p ∣ m) := by
  have hpp := hpf.out
  have hndvd : ∀ m, ¬ p ^ 2 ∣ m → a m ≠ 0 → ¬ p ∣ m := fun m hm ham =>
    (eigenvalue_of_fg χ p hpN hL haL hc ham hm).1
  obtain ⟨e, n', hpn', hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hpp.one_lt.ne'
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' e
  · have hm : ¬ p ^ 2 ∣ n' := fun h => hpn' ((dvd_pow_self p two_ne_zero).trans h)
    refine ⟨n', k, hm, by rw [hne, hk], ?_⟩
    have E := eigen_pow_of_fg χ p hpN hL haL hc hm
    have e1 : n * p ^ 2 = p ^ (2 * (k + 1)) * n' := by rw [hne, hk]; ring
    have e2 : n = p ^ (2 * k) * n' := by rw [hne, hk]
    refine ⟨?_, ?_, hndvd _ hm⟩
    · rw [e1, E (k + 1), e2, E k]; ring
    · rw [e2, E k]
  · have hm : ¬ p ^ 2 ∣ p * n' := by
      rintro ⟨u, hu⟩
      apply hpn'
      refine ⟨u, ?_⟩
      have : p * n' = p * (p * u) := by rw [hu]; ring
      exact Nat.eq_of_mul_eq_mul_left hpp.pos this
    refine ⟨p * n', k, hm, by rw [hne, hk]; ring, ?_⟩
    have E := eigen_pow_of_fg χ p hpN hL haL hc hm
    have e1 : n * p ^ 2 = p ^ (2 * (k + 1)) * (p * n') := by rw [hne, hk]; ring
    have e2 : n = p ^ (2 * k) * (p * n') := by rw [hne, hk]; ring
    refine ⟨?_, ?_, hndvd _ hm⟩
    · rw [e1, E (k + 1), e2, E k]; ring
    · rw [e2, E k]

/-- `a(n p²) = ε a(n)` with `ε = χ(p)(m/p)`, `n = p^{2k} m`, `p² ∤ m`, and in addition
`a(n) = ε^k a(m)`. -/
theorem mCoeff_mul_sq_prime_aux (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ) (P : HPrime N) {c : ℂ}
    (hc : heckeEnd χ h24 P g = c • g) {n : ℕ} (hn : 0 < n) :
    ∃ m k : ℕ, ¬ P.1 ^ 2 ∣ m ∧ n = P.1 ^ (2 * k) * m ∧
      mCoeff g (n * P.1 ^ 2) =
        χ (P.1 : ZMod N) * (jacobiSym (m : ℤ) P.1 : ℂ) * mCoeff g n ∧
      mCoeff g n = (χ (P.1 : ZMod N) * (jacobiSym (m : ℤ) P.1 : ℂ)) ^ k * mCoeff g m ∧
      (mCoeff g m ≠ 0 → ¬ P.1 ∣ m) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨L, hL, haL⟩ := hB N hN h24 χ g
  have hc' : ∀ n, heckeCoeff χ P.1 (mCoeff g) n = c * mCoeff g n := fun n => by
    rw [← mCoeff_heckeEnd χ h24 P g n, hc, mCoeff_smul]
  obtain ⟨m, k, h1, h2, h3, h4, h5⟩ := seq_mul_sq_aux χ P.1 P.2.2.2 hL haL hc' hn
  refine ⟨m, k, h1, h2, ?_, ?_, h5⟩
  · rw [h3, jacobiSym.legendreSym.to_jacobiSym]
  · rw [h4, jacobiSym.legendreSym.to_jacobiSym]

/-- For `x` prime to `p`, `(t x² / p) = (t / p)`. -/
theorem jacobiSym_mul_sq {t x p : ℕ} (hxp : Nat.Coprime x p) :
    jacobiSym ((t * x ^ 2 : ℕ) : ℤ) p = jacobiSym (t : ℤ) p := by
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.sq_one' (by rw [Int.gcd_natCast_natCast]; exact hxp),
    mul_one]

/-- **Prime step.** For an eigenform supported on `t·□`, `a(n p²) = χ(p)(t/p) a(n)`. -/
theorem mCoeff_mul_sq_prime (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ) (P : HPrime N) {c : ℂ}
    (hc : heckeEnd χ h24 P g = c • g) {t : ℕ}
    (hsupp : ∀ n, 0 < n → mCoeff g n ≠ 0 → ∃ x, n = t * x ^ 2) {n : ℕ} (hn : 0 < n) :
    mCoeff g (n * P.1 ^ 2) = χ (P.1 : ZMod N) * (jacobiSym (t : ℤ) P.1 : ℂ) * mCoeff g n := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  obtain ⟨m, k, hm, hnm, h1, h2, h5⟩ := mCoeff_mul_sq_prime_aux hB hN h24 χ g P hc hn
  by_cases han : mCoeff g n = 0
  · rw [h1, han, mul_zero, mul_zero]
  have ham : mCoeff g m ≠ 0 := by
    intro h0; apply han; rw [h2, h0, mul_zero]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hnm; omega
    · exact h
  have hpm := h5 ham
  obtain ⟨x, rfl⟩ := hsupp m hm0 ham
  have hxp : Nat.Coprime x P.1 := by
    refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd P.2.1).2 fun hd => hpm ?_))
    exact Dvd.dvd.mul_left (Dvd.dvd.pow hd two_ne_zero) t
  rw [h1, jacobiSym_mul_sq hxp]

/-- **Multiplicativity** (Serre–Stark; Achimescu–Saha Theorem 3.1(3)). For a simultaneous
`T(p²)`-eigenform supported on `t·□` and `v` prime to `N`, `a(n v²) = χ(v)(t/v) a(n)`. -/
theorem mCoeff_mul_sq_of_coprime (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ)
    (hE : ∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) {t : ℕ}
    (hsupp : ∀ n, 0 < n → mCoeff g n ≠ 0 → ∃ x, n = t * x ^ 2) :
    ∀ v : ℕ, v.Coprime N → ∀ n, 0 < n →
      mCoeff g (n * v ^ 2) = χ (v : ZMod N) * (jacobiSym (t : ℤ) v : ℂ) * mCoeff g n := by
  intro v
  induction v using Nat.recOnMul with
  | zero =>
    intro h
    rw [Nat.coprime_zero_left] at h
    subst h
    exact absurd h24 (by norm_num)
  | one => intro _ n _; simp
  | prime p hp =>
    intro hpN n hn
    obtain ⟨c, hc⟩ := hE (hPrimeOfCoprime h24 hp hpN)
    exact mCoeff_mul_sq_prime hB hN h24 χ g (hPrimeOfCoprime h24 hp hpN) hc hsupp hn
  | mul a b iha ihb =>
    intro hab n hn
    have ha : a.Coprime N := Nat.Coprime.coprime_mul_right hab
    have hb : b.Coprime N := Nat.Coprime.coprime_mul_left hab
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha; subst ha; exact absurd h24 (by norm_num)
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb; subst hb; exact absurd h24 (by norm_num)
    have hna : 0 < n * a ^ 2 := Nat.mul_pos hn (by positivity)
    rw [show n * (a * b) ^ 2 = n * a ^ 2 * b ^ 2 by ring, ihb hb _ hna, iha ha n hn,
      Nat.cast_mul, map_mul, jacobiSym.mul_right' _ ha0 hb0]
    push_cast
    ring

/-- For a simultaneous eigenform supported on `t·□` (`t` squarefree) with `a(t s₀²) ≠ 0`, every
prime factor of `t` divides `N`; hence `t ∣ N`. -/
theorem squarefree_dvd_of_eigen (hB : SerreStarkBoundedCoeff24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ)
    (hE : ∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) {t s₀ : ℕ} (ht : Squarefree t)
    (hs₀ : 0 < s₀) (ha : mCoeff g (s₀ ^ 2 * t) ≠ 0) : t ∣ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  refine squarefree_dvd_of_primes hN.ne' ht fun q hq hqt => ?_
  by_contra hqN
  have hqN' : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 hqN
  let P := hPrimeOfCoprime h24 hq hqN'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨c, hc⟩ := hE P
  have hn : 0 < s₀ ^ 2 * t := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero ht.ne_zero)
  obtain ⟨m, k, hm, hnm, -, h2, h5⟩ := mCoeff_mul_sq_prime_aux hB hN h24 χ g P hc hn
  have ham : mCoeff g m ≠ 0 := by intro h0; apply ha; rw [h2, h0, mul_zero]
  have hqm : ¬ q ∣ m := h5 ham
  -- the `q`-adic valuation of `s₀² t` is odd, so `q ∣ m`
  apply hqm
  have hv : (s₀ ^ 2 * t).factorization q = 2 * s₀.factorization q + 1 := by
    rw [Nat.factorization_mul (pow_pos hs₀ 2).ne' ht.ne_zero, Nat.factorization_pow]
    have h1 : t.factorization q = 1 := by
      have := ht.natFactorization_le_one q
      have := (hq.dvd_iff_one_le_factorization ht.ne_zero).1 hqt
      omega
    simp [h1]
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; omega
  change s₀ ^ 2 * t = q ^ (2 * k) * m at hnm
  have hv' : (s₀ ^ 2 * t).factorization q = 2 * k + m.factorization q := by
    rw [hnm, Nat.factorization_mul (pow_pos hq.pos _).ne' hm0, Nat.factorization_pow]
    simp [hq.factorization_self]
  have : 1 ≤ m.factorization q := by omega
  exact (hq.dvd_iff_one_le_factorization hm0).2 this

end SSHecke

end VOA.Classification.COne
