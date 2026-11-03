/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkProof
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Serre–Stark S3-5: eigenforms are supported on one square class (given the eigenvalue lemma)

* `exists_prime_legendre_neg_one`: a positive integer which is not a square is a quadratic
  non-residue modulo arbitrarily large primes (Dirichlet's theorem + quadratic reciprocity);
* the eigenvalue lemma `SerreStarkEigenvalueLemma24` (Serre–Stark; Achimescu–Saha Lemma 3.3), stated
  as a residual: for a `T(p²)`-eigenform with eigenvalue `c` and `a(m) ≠ 0`, `p² ∤ m`, one has
  `p ∤ m` and `c = χ(p) (m/p) (1 + 1/p)` (it is *proved* from bounded coefficients in
  `SerreStarkIntegral.lean`);
* `isSquare_mul_of_eigenvalueLemma`: under the eigenvalue lemma, the positive support of a
  simultaneous eigenform lies in one square class;
* `eigenform_of_eigenvalueLemma_of_squareClass`: the eigenform residual follows from the
  eigenvalue lemma and the residual `SerreStarkSquareClass24`, which only concerns simultaneous
  eigenforms supported on a single square class `t·□`; `squareClass_of_theoremA`.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Non-residues -/

theorem jacobi_eq_neg_one_of_class {m q m₁ v : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hm₁ : Odd m₁) (hv : Odd v) (hm : m = q ^ v * m₁) {g : ℤ}
    (hg : jacobiSym g q = -1) {p : ℕ} (hp8 : (p : ℤ) ≡ 1 [ZMOD 8])
    (hpq : (p : ℤ) ≡ g [ZMOD q]) (hpm : (p : ℤ) ≡ 1 [ZMOD m₁]) :
    jacobiSym (m : ℤ) p = -1 := by
  have hp4 : p % 4 = 1 := by
    have := Int.ModEq.of_dvd (by norm_num : (4 : ℤ) ∣ 8) hp8
    have h : ((p : ℤ) % 4) = 1 := by simpa [Int.ModEq] using this
    omega
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  rw [hm]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left]
  have h1 : jacobiSym (q : ℤ) p = -1 := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four hp4 hqodd
    rw [← this, jacobiSym.mod_left, show ((p : ℕ) : ℤ) % q = g % q from hpq,
      ← jacobiSym.mod_left]
    exact hg
  have h2 : jacobiSym (m₁ : ℤ) p = 1 := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four hp4 hm₁
    rw [← this, jacobiSym.mod_left, show ((p : ℕ) : ℤ) % m₁ = 1 % m₁ from hpm,
      ← jacobiSym.mod_left, jacobiSym.one_left]
  rw [h1, h2, mul_one, hv.neg_one_pow]

theorem chi8_of_mod {p : ℕ} (hp : (p : ℤ) ≡ 1 [ZMOD 8]) : jacobiSym 2 p = 1 := by
  have h8 : p % 8 = 1 := by
    have h : ((p : ℤ) % 8) = 1 := by simpa [Int.ModEq] using hp
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [h8, show p % 2 = 1 by omega]

theorem chi8_of_mod3 {p : ℕ} (hp : (p : ℤ) ≡ 3 [ZMOD 8]) : jacobiSym 2 p = -1 := by
  have h8 : p % 8 = 3 := by
    have h : ((p : ℤ) % 8) = 3 := by simpa [Int.ModEq] using hp
    omega
  have hodd : Odd p := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [h8, show p % 2 = 1 by omega]

/-- A prime with odd exponent in a non-square. -/
theorem exists_prime_odd_factorization {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ Odd (m.factorization q) := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hm
  have ha1 : a ≠ 1 := by
    rintro rfl; apply hsq; exact ⟨b, by rw [← hab]; ring⟩
  set q := a.minFac
  have hq : q.Prime := Nat.minFac_prime ha1
  have hqa : q ∣ a := Nat.minFac_dvd a
  refine ⟨q, hq, hqa.trans ⟨b ^ 2, by rw [← hab]; ring⟩, ?_⟩
  rw [← hab, Nat.factorization_mul (by positivity) ha.ne', Nat.factorization_pow]
  have h1 : a.factorization q = 1 := by
    have hle := hsf.natFactorization_le_one q
    have hge : 1 ≤ a.factorization q := (hq.dvd_iff_one_le_factorization ha.ne').1 hqa
    omega
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, h1]
  exact ⟨b.factorization q, by ring⟩

/-- **Non-residues.** A positive integer which is not a square is a quadratic non-residue
modulo arbitrarily large primes. -/
theorem exists_prime_legendre_neg_one {n : ℕ} (hn : 0 < n) (hsq : ¬ IsSquare n) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ jacobiSym (n : ℤ) p = -1 := by
  obtain ⟨e, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm0 : 0 < m := hmodd.pos
  by_cases hm : IsSquare m
  · -- `m = r²`, so `e` is odd; take `p ≡ 3 (mod 8)`
    obtain ⟨r, hr⟩ := hm
    have he : Odd e := by
      by_contra he
      rw [Nat.not_odd_iff_even] at he
      obtain ⟨k, hk⟩ := he
      apply hsq
      exact ⟨2 ^ k * r, by rw [hnm, hr, hk, pow_add]; ring⟩
    obtain ⟨p, hpB, hp, hp8⟩ := Nat.forall_exists_prime_gt_and_zmodEq (max B n) (q := 8)
      (a := 3) (by norm_num) (by
        rw [show ((8 : ℕ) : ℤ) = 8 by norm_num]
        exact ⟨3, -1, by norm_num⟩)
    refine ⟨p, lt_of_le_of_lt (le_max_left _ _) hpB, hp, ?_⟩
    have hnp : n < p := lt_of_le_of_lt (le_max_right _ _) hpB
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0] at hr; omega
      · exact h0
    have hrn : r ≤ n := by
      rw [hnm, hr]
      calc r ≤ r * r := Nat.le_mul_self r
        _ ≤ 2 ^ e * (r * r) := Nat.le_mul_of_pos_left _ (by positivity)
    have hcop : Nat.Coprime r p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
        have := Nat.le_of_dvd hr0 h; omega).symm
    have hgcd : (r : ℤ).gcd (p : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]; exact hcop
    rw [hnm, hr]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, chi8_of_mod3 hp8, he.neg_one_pow,
      ← pow_two, jacobiSym.sq_one' hgcd]
    ring
  · -- a prime `q` with odd exponent in `m`; take `p ≡ 1 (mod 8)`, `p` a non-residue mod `q`
    obtain ⟨q, hq, hqm, hodd⟩ := exists_prime_odd_factorization hm0 hm
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 hqm)
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    set v := m.factorization q with hv
    set m₁ := m / q ^ v with hm₁def
    have hm₁ : m = q ^ v * m₁ := (Nat.ordProj_mul_ordCompl_eq_self m q).symm
    have hm₁odd : Odd m₁ := by
      have h := hmodd; rw [hm₁] at h; exact Nat.Odd.of_mul_right h
    have hcopq : Nat.Coprime q m₁ := Nat.coprime_ordCompl hq hm0.ne'
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨g₀, hg₀⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by
      rw [ZMod.ringChar_zmod_n]; exact hq2)
    set g : ℤ := (g₀.val : ℤ) with hgdef
    have hgcast : ((g : ℤ) : ZMod q) = g₀ := by simp [hgdef]
    have hg : jacobiSym g q = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff, hgcast]
      exact hg₀
    have hgq : IsCoprime g (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      by_contra hne
      have := jacobiSym.eq_zero_iff.2 ⟨hq.ne_zero, hne⟩
      rw [hg] at this; norm_num at this
    have h8q : Nat.Coprime (8 * m₁) q := by
      refine Nat.Coprime.mul_left ?_ hcopq.symm
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hqodd)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 h8q
    set a : ℤ := 1 + 8 * m₁ * u * (g - 1) with hadef
    have ha8 : a ≡ 1 [ZMOD 8] :=
      Int.modEq_iff_dvd.2 ⟨-(m₁ * u * (g - 1)), by rw [hadef]; ring⟩
    have ham : a ≡ 1 [ZMOD m₁] :=
      Int.modEq_iff_dvd.2 ⟨-(8 * u * (g - 1)), by rw [hadef]; ring⟩
    have haq : a ≡ g [ZMOD q] := by
      refine Int.modEq_iff_dvd.2 ⟨(g - 1) * w, ?_⟩
      push_cast at huw
      rw [hadef]; linear_combination (1 - g) * huw
    have hcopa : IsCoprime a ((8 * q * m₁ : ℕ) : ℤ) := by
      push_cast
      refine IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_
      · exact ⟨1, -(m₁ * u * (g - 1)), by rw [hadef]; ring⟩
      · have : a = g + (-(g - 1) * w) * q := by
          push_cast at huw; rw [hadef]; linear_combination (g - 1) * huw
        rw [this]; exact hgq.add_mul_right_left _
      · exact ⟨1, -(8 * u * (g - 1)), by rw [hadef]; ring⟩
    obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq B
      (q := 8 * q * m₁) (a := a)
      (Nat.mul_pos (Nat.mul_pos (by norm_num) hq.pos) hm₁odd.pos).ne' hcopa
    refine ⟨p, hpB, hp, ?_⟩
    have hpa' : (p : ℤ) ≡ a [ZMOD 8 * q * m₁] := by exact_mod_cast hpa
    have hp8 : (p : ℤ) ≡ 1 [ZMOD 8] :=
      ((hpa'.of_mul_right _).of_mul_right _).trans ha8
    have hpq : (p : ℤ) ≡ g [ZMOD q] :=
      ((hpa'.of_mul_right _).of_mul_left _).trans haq
    have hpm : (p : ℤ) ≡ 1 [ZMOD m₁] := (hpa'.of_mul_left _).trans ham
    have hm' := jacobi_eq_neg_one_of_class hq hq2 hm₁odd hodd hm₁ hg hp8 hpq hpm
    rw [hnm]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, chi8_of_mod hp8, one_pow, one_mul]
    exact_mod_cast hm'

/-! ## The eigenvalue lemma and the square-class residual -/

/-- **Residual (Serre–Stark's eigenvalue lemma).** Let `24 ∣ N`, `p` an odd prime not dividing
`N`, and `g ∈ M_{1/2}(N, χ)` an eigenform of `T(p²)` with eigenvalue `c`. If `a(m) ≠ 0` and
`p² ∤ m`, then `p ∤ m` and `c = χ(p) (m/p) (1 + 1/p)`.

TRUE: Serre–Stark (LNM 627, 1977) §3; Achimescu–Saha (arXiv:0803.3788) Lemma 3.3. Its proof is
`p`-adic: the generating series `Σ_k a(m p^{2k}) X^k = a(m)(1 − εX/p)/(1 − cX + χ(p)²X²/p)`
(`ε = χ(p)(m/p)`) must have `p`-adically bounded coefficients, because `M_{1/2}(N, χ)` has a basis
with algebraic coefficients of bounded denominators; that forces the numerator to cancel a pole,
i.e. `c = ε(1 + 1/p)`. Equivalently (using the linear independence half of Theorem A): every
`g` is a combination of `θ_{ψ,t}` with `p ∤ t`, each a `T(p²)`-eigenform of eigenvalue
`ψ(p)(1 + 1/p) = χ(p)(t n²/p)(1 + 1/p)`, supported on `t n²`. (Conventions checked numerically
against `heckeCoeff` for `θ_{ψ,t}`, `(ψ, t) ∈ {(1,1), ((·/5),3), (1,2)}`, `p ∈ {7, 11, 13}`.) -/
def SerreStarkEigenvalueLemma24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (P : HPrime N)
    (g : mSpace N χ) (c : ℂ) (m : ℕ),
    heckeEnd χ h24 P g = c • g → mCoeff g m ≠ 0 → ¬ P.1 ^ 2 ∣ m →
      ¬ P.1 ∣ m ∧ c = χ (P.1 : ZMod N) * (jacobiSym (m : ℤ) P.1 : ℂ) * (1 + 1 / (P.1 : ℂ))

/-- **Residual (eigenforms on one square class).** Every simultaneous `T(p²)`-eigenform in
`M_{1/2}(N, χ)` (`24 ∣ N`) whose nonzero positive-index coefficients `a(m₁), a(m₂)` always have
`m₁ m₂` a square is a finite combination of the `θ_{ψ,t}`.

TRUE: a special case of `SerreStarkEigenform24`, hence of Theorem A (`squareClass_of_theoremA`).
What remains in it is Serre–Stark's level analysis (operators `U(p)`, `V(p)`, twists, newforms
at `p ∣ N`). -/
def SerreStarkSquareClass24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ),
    (∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) →
    (∀ m₁ m₂ : ℕ, 0 < m₁ → 0 < m₂ → mCoeff g m₁ ≠ 0 → mCoeff g m₂ ≠ 0 → IsSquare (m₁ * m₂)) →
      ((g : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N)

/-- A large prime is admissible. -/
def hPrimeOfLt {N p : ℕ} (hN : 0 < N) (hp : p.Prime) (hNp : N + 2 < p) : HPrime N :=
  ⟨p, hp, by omega, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd hN h; omega⟩

/-- **Square classes.** Under the eigenvalue lemma, the positive support of a simultaneous
`T(p²)`-eigenform lies in a single square class. -/
theorem isSquare_mul_of_eigenvalueLemma (hL : SerreStarkEigenvalueLemma24) {N : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ)
    (hE : ∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) {m₁ m₂ : ℕ} (h1 : 0 < m₁)
    (h2 : 0 < m₂) (a1 : mCoeff g m₁ ≠ 0) (a2 : mCoeff g m₂ ≠ 0) : IsSquare (m₁ * m₂) := by
  by_contra hsq
  obtain ⟨p, hpB, hp, hJ⟩ :=
    exists_prime_legendre_neg_one (Nat.mul_pos h1 h2) hsq (N + m₁ + m₂ + 2)
  let P : HPrime N := hPrimeOfLt hN hp (by omega)
  obtain ⟨c, hc⟩ := hE P
  have hnd : ∀ m : ℕ, 0 < m → m < p → ¬ p ^ 2 ∣ m := fun m hm hmp h => by
    have := Nat.le_of_dvd hm ((dvd_pow_self p two_ne_zero).trans h); omega
  have e1 := (hL N hN h24 χ P g c m₁ hc a1 (hnd m₁ h1 (by omega))).2
  have e2 := (hL N hN h24 χ P g c m₂ hc a2 (hnd m₂ h2 (by omega))).2
  have hχ : χ (p : ZMod N) ≠ 0 :=
    chi_ne_zero_of_isUnit χ ((ZMod.isUnit_iff_coprime p N).2 P.2.2.2)
  have hpos : (1 + 1 / (p : ℂ)) ≠ 0 := by
    have h0 : (0 : ℝ) < 1 + 1 / (p : ℝ) := by positivity
    have : (1 + 1 / (p : ℂ)) = ((1 + 1 / (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact Complex.ofReal_ne_zero.2 h0.ne'
  have hJJ : (jacobiSym (m₁ : ℤ) p : ℂ) = (jacobiSym (m₂ : ℤ) p : ℂ) := by
    have := e1.symm.trans e2
    rw [mul_assoc, mul_assoc] at this
    exact mul_right_cancel₀ hpos (mul_left_cancel₀ hχ this)
  have hJJ' : jacobiSym (m₁ : ℤ) p = jacobiSym (m₂ : ℤ) p := by exact_mod_cast hJJ
  have : jacobiSym ((m₁ * m₂ : ℕ) : ℤ) p = jacobiSym (m₁ : ℤ) p ^ 2 := by
    push_cast; rw [jacobiSym.mul_left, hJJ', sq]
  rw [hJ] at this
  nlinarith [sq_nonneg (jacobiSym (m₁ : ℤ) p)]

/-- **Reduction.** The eigenvalue lemma and the square-class residual give Serre–Stark's
eigenform residual. -/
theorem eigenform_of_eigenvalueLemma_of_squareClass (hL : SerreStarkEigenvalueLemma24)
    (hQ : SerreStarkSquareClass24) : SerreStarkEigenform24 :=
  fun N hN h24 χ g hE => hQ N hN h24 χ g hE fun _ _ h1 h2 a1 a2 =>
    isSquare_mul_of_eigenvalueLemma hL hN h24 χ g hE h1 h2 a1 a2

/-- **Reduction.** Petersson semisimplicity, the eigenvalue lemma, and the square-class
residual give `ISerreStark` at every level divisible by `24`. -/
theorem iSerreStark24_of_semisimple_of_eigenvalueLemma_of_squareClass (hS : HeckeSemisimple24)
    (hL : SerreStarkEigenvalueLemma24) (hQ : SerreStarkSquareClass24) : ISerreStark24 :=
  iSerreStark24_of_semisimple_of_eigenform hS (eigenform_of_eigenvalueLemma_of_squareClass hL hQ)

/-- The square-class residual is no stronger than Serre–Stark's Theorem A. -/
theorem squareClass_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkSquareClass24 :=
  fun _ hN h24 χ g _ _ => mem_span_of_theoremA hA hN h24 χ g

end SSHecke

end VOA.Classification.COne
