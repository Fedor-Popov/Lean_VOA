/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2StarRiccati
import VOA.DeligneAudit.DeligneMLDECubic
import VOA.Commutative.JacobiTripleQuintuple

/-!
# Lorenz's formula `θ_{A₂} = 1 + 6 ∑ χ₋₃(d) qⁿ`

We prove `AQ = 1 + 6 L₀` (`aq_eq_one_add_six_L0`; `L₀` is the `Heat.L0`), hence `LorenzA2`.
Write `E₃ = (q³;q³)_∞`, `φ = ∑ q^{m²}`, `Ψ = ∑ q^{m(m+1)}`.  The bilinear lattice sum

  `S = ∑_{i,j} (-1)^{i+j} (i-j) χ₋₃(i-j) q^{i(i-1)/2 + j(j-1)/2}`

is evaluated twice:

1. **Wronskian at a cube root of unity** (`S_eq_wronskian`): `S = -2 E₃² (1 + 6L₀)`.  This is the
   `x⁰`-part of `DΘ(ωeˣ)·Θ(ω⁻¹eˣ) - Θ(ωeˣ)·DΘ(ω⁻¹eˣ)` for the Jacobi triple product `Θ` over `ℂ⟦x⟧`
   (the `HeatK`): on the product side `D log P = R` gives `R(ω) - R(ω⁻¹) = -2(ω - ω⁻¹)L₀`.
2. **Lattice side** (`S_eq_lattice`): `S = -2 E₃² θ_{A₂}`.  Splitting `i - j` by parity,
   `S = -U φ + W Ψ` with weight-3/2 theta series `U`, `W`, which the `z`-derivatives of the
   quintuple product identity (`quintuple_deriv₀`, `quintuple_deriv₁`) evaluate as
   `U = 2E₃² φ(q³)`, `W = -2q E₃² Ψ(q³)`; and `θ_{A₂} = φ(q)φ(q³) + qΨ(q)Ψ(q³)` (`AQ_split`).
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## Characters and exponents -/

/-- `χ₋₃` on `ℤ`. -/
def chiZ (s : ℤ) : ℚ := if s % 3 = 1 then 1 else if s % 3 = 2 then -1 else 0

theorem chiZ_of_one {s : ℤ} (h : s % 3 = 1) : chiZ s = 1 := by rw [chiZ, if_pos h]
theorem chiZ_of_two {s : ℤ} (h : s % 3 = 2) : chiZ s = -1 := by
  rw [chiZ, if_neg (by omega), if_pos h]
theorem chiZ_of_zero {s : ℤ} (h : s % 3 = 0) : chiZ s = 0 := by
  rw [chiZ, if_neg (by omega), if_neg (by omega)]

/-- `m² - mn + n²`. -/
def qA2 (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2).toNat

theorem cast_qA2 (p : ℤ × ℤ) : ((qA2 p : ℕ) : ℤ) = p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 := by
  rw [qA2, Int.toNat_of_nonneg]
  nlinarith [sq_nonneg (p.1 - p.2), sq_nonneg p.1, sq_nonneg p.2]

theorem abs_le_qA2_form (a b : ℤ) : |a| ≤ a ^ 2 - a * b + b ^ 2 := by
  rcases le_or_gt 2 |a| with h | h
  · nlinarith [abs_nonneg a, sq_abs a, sq_nonneg (2 * b - a)]
  · have h1 : a = -1 ∨ a = 0 ∨ a = 1 := by
      rcases abs_lt.mp (show |a| < 2 from h) with ⟨h1, h2⟩; omega
    rcases h1 with rfl | rfl | rfl
    · rcases le_or_gt 0 b with hb | hb <;> norm_num <;> nlinarith
    · norm_num; positivity
    · rcases le_or_gt 1 b with hb | hb <;> norm_num <;> nlinarith

theorem finFib_qA2 : FinFib qA2 := by
  intro d
  apply ((Set.finite_Icc (-(d : ℤ)) d).prod (Set.finite_Icc (-(d : ℤ)) d)).subset
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hc := cast_qA2 p
  rw [hp] at hc
  have h1 := abs_le_qA2_form p.1 p.2
  have h2 := abs_le_qA2_form p.2 p.1
  simp only [Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    [have := neg_abs_le p.1; have := le_abs_self p.1; have := neg_abs_le p.2;
      have := le_abs_self p.2] <;> nlinarith

/-- `θ_{A₂}` as a lattice `fsr`. -/
theorem AQ_eq_fsr : AQ = fsr (fun _ : ℤ × ℤ => (1 : ℚ)) qA2 := by
  ext N
  rw [AQ, coeff_map, thetaA2, coeff_mk,
    coeff_fsr_of_subset _ _ N (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N) (fun p hp _ => by
      have hc := cast_qA2 p
      rw [hp] at hc
      have h1 := abs_le_qA2_form p.1 p.2
      have h2 := abs_le_qA2_form p.2 p.1
      simp only [Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
        [have := neg_abs_le p.1; have := le_abs_self p.1; have := neg_abs_le p.2;
          have := le_abs_self p.2] <;> nlinarith)]
  rw [eq_intCast, Int.cast_natCast, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hc := cast_qA2 p
  by_cases h : qA2 p = N
  · rw [if_pos h, if_pos (by rw [← hc, h])]; simp
  · rw [if_neg h, if_neg (by intro h'; apply h; exact_mod_cast hc.trans h')]; simp

/-! ## The lattice split of `θ_{A₂}` -/

/-- `(c, b) ↦ (c + b, 2b)`. -/
def latE (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + x.2, 2 * x.2)
/-- `(c, b) ↦ (b - c, 2b + 1)`. -/
def latO (x : ℤ × ℤ) : ℤ × ℤ := (x.2 - x.1, 2 * x.2 + 1)

theorem latE_injective : Function.Injective latE := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [latE, Prod.mk.injEq] at h; ext <;> simp <;> omega
theorem latO_injective : Function.Injective latO := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [latO, Prod.mk.injEq] at h; ext <;> simp <;> omega
theorem lat_cover (p : ℤ × ℤ) : p ∈ Set.range latE ∨ p ∈ Set.range latO := by
  obtain ⟨m, n⟩ := p
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; exact ⟨(m - n / 2, n / 2), by simp only [latE, Prod.mk.injEq]; omega⟩
  · right; exact ⟨(n / 2 - m, n / 2), by simp only [latO, Prod.mk.injEq]; omega⟩
theorem lat_disj (x y : ℤ × ℤ) : latE x ≠ latO y := by
  simp only [latE, latO, ne_eq, Prod.mk.injEq]; omega

theorem psiF_eq' : psiF = fsr (fun _ : ℤ => (1 : ℚ)) (fun m => 2 * pentExp m) := by
  rw [psiF]
  symm
  exact fsr_reindex (Equiv.neg ℤ) (fun _ => rfl) (fun n => by simp)

/-- `θ_{A₂}(q) = φ(q)φ(q³) + qΨ(q)Ψ(q³)`. -/
theorem AQ_split :
    AQ = phiF * expand 3 (by norm_num) phiF + X * (psiF * expand 3 (by norm_num) psiF) := by
  rw [AQ_eq_fsr, fsr_split latE latO latE_injective latO_injective lat_cover lat_disj _ finFib_qA2]
  congr 1
  · rw [phiF, expand_fsr 3 (by norm_num) _ finFib_sqExp,
      fsr_mul _ _ finFib_sqExp (finFib_sqExp.mul_const (by norm_num))]
    refine fsr_congr (fun _ => by ring) (fun x => ?_)
    obtain ⟨c, b⟩ := x
    simp only [latE]
    have h := cast_qA2 (c + b, 2 * b)
    zify; rw [h, cast_sqExp, cast_sqExp]; ring
  · rw [psiF, expand_fsr 3 (by norm_num) _ finFib_two_pentExp_neg,
      fsr_mul _ _ finFib_two_pentExp_neg (finFib_two_pentExp_neg.mul_const
        (by norm_num)), show (X : PowerSeries ℚ) = X ^ 1 by rw [pow_one], X_pow_mul_fsr]
    refine fsr_congr (fun _ => by ring) (fun x => ?_)
    obtain ⟨c, b⟩ := x
    simp only [latO]
    apply VOA.QSeries.JTP.nat_eq_of_two_mul
    have h := cast_qA2 (b - c, 2 * b + 1)
    have h1 := two_mul_cast_pentExp (-c)
    have h2 := two_mul_cast_pentExp (-b)
    push_cast
    rw [h]
    linear_combination -2 * h1 - 6 * h2

/-! ## The bilinear sum `S` on the lattice side -/

/-- `S = ∑_{i,j} (-1)^{i+j} (i-j) χ₋₃(i-j) q^{i(i-1)/2 + j(j-1)/2}`. -/
def Sser : PowerSeries ℚ :=
  fsr (fun p : ℤ × ℤ =>
      (negSign p.1 : ℚ) * negSign p.2 * (((p.1 - p.2 : ℤ) : ℚ) * chiZ (p.1 - p.2)))
    (fun p => pentExp p.1 + pentExp p.2)

/-- `U = ∑_a (2a+1) χ₋₃(2a+1) q^{a(a+1)}`. -/
def Uo : PowerSeries ℚ :=
  fsr (fun a : ℤ => ((2 * a + 1 : ℤ) : ℚ) * chiZ (2 * a + 1)) (fun a => 2 * pentExp (-a))

/-- `W = ∑_a 2a χ₋₃(2a) q^{a²}`. -/
def Wp : PowerSeries ℚ := fsr (fun a : ℤ => ((2 * a : ℤ) : ℚ) * chiZ (2 * a)) sqExp

/-- `s = i - j` odd: `(a, n) ↦ (n + a + 1, n - a)`. -/
def wO (x : ℤ × ℤ) : ℤ × ℤ := (x.2 + x.1 + 1, x.2 - x.1)
/-- `s = i - j` even: `(a, n) ↦ (n + a, n - a)`. -/
def wE (x : ℤ × ℤ) : ℤ × ℤ := (x.2 + x.1, x.2 - x.1)

theorem wO_injective : Function.Injective wO := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [wO, Prod.mk.injEq] at h; ext <;> simp <;> omega
theorem wE_injective : Function.Injective wE := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [wE, Prod.mk.injEq] at h; ext <;> simp <;> omega
theorem w_cover (p : ℤ × ℤ) : p ∈ Set.range wO ∨ p ∈ Set.range wE := by
  obtain ⟨i, j⟩ := p
  rcases Int.emod_two_eq_zero_or_one (i - j) with h | h
  · right; exact ⟨((i - j) / 2, j + (i - j) / 2), by simp only [wE, Prod.mk.injEq]; omega⟩
  · left; exact ⟨((i - j) / 2, j + (i - j) / 2), by simp only [wO, Prod.mk.injEq]; omega⟩
theorem w_disj (x y : ℤ × ℤ) : wO x ≠ wE y := by
  simp only [wO, wE, ne_eq, Prod.mk.injEq]; omega

theorem negSign_mul_negSign_odd (n a : ℤ) :
    (negSign (n + a + 1) : ℚ) * negSign (n - a) = -1 := by
  rw [← negSign_add, show n + a + 1 + (n - a) = 0 + 2 * n + 1 by ring,
    negSign_add_two_mul_add_one]
  simp [negSign]

theorem negSign_mul_negSign_even (n a : ℤ) : (negSign (n + a) : ℚ) * negSign (n - a) = 1 := by
  rw [← negSign_add, show n + a + (n - a) = 0 + 2 * n by ring, negSign_add_two_mul]
  simp [negSign]

theorem finFib_S : FinFib fun p : ℤ × ℤ => pentExp p.1 + pentExp p.2 :=
  finFib_pentExp.prod finFib_pentExp

/-- `S = -U φ + W Ψ`. -/
theorem Sser_split : Sser = -(Uo * phiF) + Wp * psiF := by
  rw [Sser, fsr_split wO wE wO_injective wE_injective w_cover w_disj _ finFib_S]
  congr 1
  · rw [Uo, phiF, fsr_mul _ _ finFib_two_pentExp_neg finFib_sqExp,
      ← fsr_neg _ (finFib_two_pentExp_neg.prod finFib_sqExp)]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨a, n⟩ := x
      simp only [wO]
      rw [negSign_mul_negSign_odd, show n + a + 1 - (n - a) = 2 * a + 1 by ring]
      ring
    · obtain ⟨a, n⟩ := x
      simp only [wO]
      apply VOA.QSeries.JTP.nat_eq_of_two_mul
      have h1 := two_mul_cast_pentExp (n + a + 1)
      have h2 := two_mul_cast_pentExp (n - a)
      have h3 := two_mul_cast_pentExp (-a)
      push_cast
      rw [cast_sqExp]
      linear_combination h1 + h2 - 2 * h3
  · rw [Wp, psiF_eq', fsr_mul _ _ finFib_sqExp (finFib_pentExp.mul_const two_pos)]
    refine fsr_congr (fun x => ?_) (fun x => ?_)
    · obtain ⟨a, n⟩ := x
      simp only [wE]
      rw [negSign_mul_negSign_even, show n + a - (n - a) = 2 * a by ring]
      ring
    · obtain ⟨a, n⟩ := x
      simp only [wE]
      apply VOA.QSeries.JTP.nat_eq_of_two_mul
      have h1 := two_mul_cast_pentExp (n + a)
      have h2 := two_mul_cast_pentExp (n - a)
      have h3 := two_mul_cast_pentExp n
      push_cast
      rw [cast_sqExp]
      linear_combination h1 + h2 - 2 * h3

/-! ### Residues mod 3 -/

def m3a (j : ℤ) : ℤ := 3 * j
def m3b (j : ℤ) : ℤ := 3 * j + 1
def m3c (j : ℤ) : ℤ := 3 * j + 2

theorem m3a_inj : Function.Injective m3a := fun a b h => by simp only [m3a] at h; omega
theorem m3b_inj : Function.Injective m3b := fun a b h => by simp only [m3b] at h; omega
theorem m3c_inj : Function.Injective m3c := fun a b h => by simp only [m3c] at h; omega
theorem m3_cover (a : ℤ) : a ∈ Set.range m3a ∨ a ∈ Set.range m3b ∨ a ∈ Set.range m3c := by
  have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl ⟨a / 3, by simp only [m3a]; omega⟩
  · exact Or.inr (Or.inl ⟨a / 3, by simp only [m3b]; omega⟩)
  · exact Or.inr (Or.inr ⟨a / 3, by simp only [m3c]; omega⟩)
theorem m3ab (x y : ℤ) : m3a x ≠ m3b y := by simp only [m3a, m3b]; omega
theorem m3ac (x y : ℤ) : m3a x ≠ m3c y := by simp only [m3a, m3c]; omega
theorem m3bc (x y : ℤ) : m3b x ≠ m3c y := by simp only [m3b, m3c]; omega

/-- `U = 2 · (∑_j (6j+1) p^{j(3j+1)})|_{p = q³}`. -/
theorem Uo_eq :
    Uo = 2 * expand 3 (by norm_num)
      (fsr (fun j : ℤ => 6 * (j : ℚ) + 1) (fun j => 2 * pentagonal (-j))) := by
  have hF : FinFib fun j : ℤ => 2 * pentagonal (-j) := finFib_pentagonal_neg.mul_const two_pos
  rw [expand_fsr 3 (by norm_num) _ hF, show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
    rw [map_ofNat], ← fsr_const_mul _ _ (hF.mul_const (by norm_num)), Uo,
    fsr_split3 m3a m3b m3c m3a_inj m3b_inj m3c_inj m3_cover m3ab m3ac m3bc _
      finFib_two_pentExp_neg]
  have h1 : fsr (fun j => ((2 * m3b j + 1 : ℤ) : ℚ) * chiZ (2 * m3b j + 1))
      (fun j => 2 * pentExp (-m3b j)) = 0 := by
    rw [← fsr_zero (R := ℚ) (fun j => 2 * pentExp (-m3b j))]
    exact fsr_congr (fun j => by simp only [m3b]; rw [chiZ_of_zero (by omega)]; ring)
      (fun _ => rfl)
  have h0 : fsr (fun j => ((2 * m3a j + 1 : ℤ) : ℚ) * chiZ (2 * m3a j + 1))
      (fun j => 2 * pentExp (-m3a j)) =
      fsr (fun j : ℤ => 6 * (j : ℚ) + 1) (fun j => 3 * (2 * pentagonal (-j))) := by
    refine fsr_congr (fun j => ?_) (fun j => ?_)
    · simp only [m3a]; rw [chiZ_of_one (by omega)]; push_cast; ring
    · simp only [m3a]
      apply VOA.QSeries.JTP.nat_eq_of_two_mul
      have h1 := two_mul_cast_pentExp (-(3 * j))
      have h2 := two_mul_natCast_pentagonal_neg j
      push_cast
      linear_combination 2 * h1 - 6 * h2
  have h2 : fsr (fun j => ((2 * m3c j + 1 : ℤ) : ℚ) * chiZ (2 * m3c j + 1))
      (fun j => 2 * pentExp (-m3c j)) =
      fsr (fun j : ℤ => 6 * (j : ℚ) + 1) (fun j => 3 * (2 * pentagonal (-j))) := by
    refine fsr_reindex (Equiv.subLeft (-1)) (fun j => ?_) (fun j => ?_)
    · simp only [m3c, Equiv.subLeft_apply]; rw [chiZ_of_two (by omega)]; push_cast; ring
    · simp only [m3c, Equiv.subLeft_apply]
      apply VOA.QSeries.JTP.nat_eq_of_two_mul
      have h1 := two_mul_cast_pentExp (-(3 * j + 2))
      have h2 := two_mul_natCast_pentagonal_neg (-1 - j)
      push_cast
      linear_combination 2 * h1 - 6 * h2
  rw [h0, h1, h2, add_zero, ← two_mul, show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
    rw [map_ofNat], ← fsr_const_mul _ _ (hF.mul_const (by norm_num))]

/-- `W = -2q · (2∑_j (3j+1) p^{j(3j+2)})|_{p = q³}`. -/
theorem Wp_eq :
    Wp = -2 * X * expand 3 (by norm_num) (2 * fsr (fun j : ℤ => 3 * (j : ℚ) + 1) qe2) := by
  have hF : FinFib fun j : ℤ => 3 * qe2 j + 1 := (finFib_qe2.mul_const (by norm_num)).add_const 1
  rw [map_mul, map_ofNat, expand_fsr 3 (by norm_num) _ finFib_qe2,
    show (X : PowerSeries ℚ) = X ^ 1 by rw [pow_one]]
  rw [show (-2 * X ^ 1 * (2 * fsr (fun j : ℤ => 3 * (j : ℚ) + 1) fun j => 3 * qe2 j) :
      PowerSeries ℚ) = PowerSeries.C (-4) * (X ^ 1 * fsr (fun j : ℤ => 3 * (j : ℚ) + 1)
        fun j => 3 * qe2 j) by rw [map_neg, map_ofNat]; ring,
    X_pow_mul_fsr, ← fsr_const_mul _ _ hF, Wp,
    fsr_split3 m3a m3b m3c m3a_inj m3b_inj m3c_inj m3_cover m3ab m3ac m3bc _ finFib_sqExp]
  have h0 : fsr (fun j => ((2 * m3a j : ℤ) : ℚ) * chiZ (2 * m3a j))
      (fun j => sqExp (m3a j)) = 0 := by
    rw [← fsr_zero (R := ℚ) (fun j => sqExp (m3a j))]
    exact fsr_congr (fun j => by simp only [m3a]; rw [chiZ_of_zero (by omega)]; ring)
      (fun _ => rfl)
  have h1 : fsr (fun j => ((2 * m3b j : ℤ) : ℚ) * chiZ (2 * m3b j)) (fun j => sqExp (m3b j)) =
      fsr (fun j : ℤ => -2 * (3 * (j : ℚ) + 1)) (fun j => 3 * qe2 j + 1) := by
    refine fsr_congr (fun j => ?_) (fun j => ?_)
    · simp only [m3b]; rw [chiZ_of_two (by omega)]; push_cast; ring
    · simp only [m3b]
      zify
      rw [cast_sqExp, cast_qe2]; ring
  have h2 : fsr (fun j => ((2 * m3c j : ℤ) : ℚ) * chiZ (2 * m3c j)) (fun j => sqExp (m3c j)) =
      fsr (fun j : ℤ => -2 * (3 * (j : ℚ) + 1)) (fun j => 3 * qe2 j + 1) := by
    refine fsr_reindex (Equiv.subLeft (-1)) (fun j => ?_) (fun j => ?_)
    · simp only [m3c, Equiv.subLeft_apply]; rw [chiZ_of_one (by omega)]; push_cast; ring
    · simp only [m3c, Equiv.subLeft_apply]
      zify
      rw [cast_sqExp, cast_qe2]; ring
  rw [h0, h1, h2, zero_add, ← fsr_add _ _ hF]
  exact fsr_congr (fun _ => by ring) (fun _ => rfl)

/-- **The lattice side**: `S = -2 (q³;q³)²_∞ θ_{A₂}`. -/
theorem S_eq_lattice : Sser = -2 * expand 3 (by norm_num) euler ^ 2 * AQ := by
  rw [Sser_split, Uo_eq, Wp_eq, quintuple_deriv₀, quintuple_deriv₁, AQ_split]
  simp only [map_mul, map_pow]
  ring

/-! ## The Wronskian at a cube root of unity -/

section Wronskian

open VOA.DeligneAudit.DeligneMLDE.HeatK

/-- Evaluation at `x = 0` of the coefficients. -/
abbrev evx : PowerSeries (PowerSeries ℂ) →+* PowerSeries ℂ :=
  PowerSeries.map (PowerSeries.constantCoeff (R := ℂ))

theorem map_infProd' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {u : ℕ → PowerSeries R} (hu : ProdFactors u) :
    PowerSeries.map φ (infProd u) = infProd fun k => PowerSeries.map φ (u k) := by
  have hdvd : ∀ K, (X : PowerSeries S) ^ K ∣ PowerSeries.map φ (X ^ K) := fun K => by
    rw [map_pow, PowerSeries.map_X]
  have hφu : ProdFactors fun k => PowerSeries.map φ (u k) := fun k => by
    simpa using (hu k).map (PowerSeries.map φ) (hdvd (k + 1))
  apply eq_infProd_of_agree hφu
  intro N
  rw [← map_prod]
  exact (agreeTo_infProd hu N).map _ (hdvd (N + 1))

theorem map_euler' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    PowerSeries.map φ (euler : PowerSeries R) = euler := by
  rw [euler_eq_infProd, map_infProd' φ prodFactors_euler, euler_eq_infProd]
  apply infProd_congr; intro k; simp

theorem map_expand' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ) (hp : p ≠ 0)
    (f : PowerSeries R) :
    PowerSeries.map φ (expand p hp f) = expand p hp (PowerSeries.map φ f) := by
  ext n; rw [coeff_map, coeff_expand, coeff_expand]; split_ifs <;> simp [coeff_map]

theorem expand3_euler_eq {R : Type*} [CommRing R] :
    expand 3 (by norm_num) (euler : PowerSeries R) =
      infProd fun m => (1 - X ^ (3 * m + 3) : PowerSeries R) := by
  rw [euler_eq_infProd, expand_infProd 3 (by norm_num) (prodFactors_euler (R := R))]
  apply infProd_congr
  intro m
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]
  congr 2

theorem ω3_ne_inv : ω3 - ω3⁻¹ ≠ 0 := by
  intro h
  have h1 : ω3 = ω3 ^ 2 := by rw [← ω3_inv]; linear_combination h
  have h2 := ω3_sq_add
  have h3 : ω3 * (ω3 - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact ω3_ne_zero h4
  · exact ω3_ne_one (by linear_combination h4)

theorem ω3_add_inv' : ω3 + ω3⁻¹ = -1 := by rw [ω3_inv]; linear_combination ω3_sq_add

theorem ω3_zpow_mod (s : ℤ) : ω3 ^ s = ω3 ^ (s % 3) := by
  conv_lhs => rw [← Int.mul_ediv_add_emod s 3]
  rw [zpow_add₀ ω3_ne_zero, zpow_mul, show ω3 ^ (3 : ℤ) = 1 by
    rw [zpow_ofNat]; exact ω3_cube, one_zpow, one_mul]

/-- `ω^s - ω^{-s} = (ω - ω⁻¹) χ₋₃(s)`. -/
theorem ω3_zpow_sub (s : ℤ) : ω3 ^ s - ω3 ^ (-s) = (ω3 - ω3⁻¹) * (chiZ s : ℂ) := by
  rw [ω3_zpow_mod s, ω3_zpow_mod (-s), chiZ]
  have hc := ω3_cube
  have hinv := ω3_inv
  have : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [h, show -s % 3 = 0 by omega]; simp
  · rw [h, show -s % 3 = 2 by omega, if_pos rfl]
    simp only [zpow_one, Rat.cast_one, mul_one]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, hinv]
  · rw [h, show -s % 3 = 1 by omega, if_neg (by norm_num), if_pos rfl]
    simp only [zpow_one, Rat.cast_neg, Rat.cast_one, mul_neg, mul_one]
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, hinv]
    ring

section Units

variable (ω : ℂ) (hω : ω ≠ 0)

theorem constantCoeff_uW_zpow (j : ℤ) :
    PowerSeries.constantCoeff (((uW ω hω) ^ j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = ω ^ j := by
  have h1 : PowerSeries.constantCoeff (((uW ω hω) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = ω := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_uW]; simp
  have : PowerSeries.constantCoeff (((uW ω hω) ^ j : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
      ((Units.map (PowerSeries.constantCoeff (R := ℂ)).toMonoidHom ((uW ω hω) ^ j) : ℂˣ) : ℂ) :=
    rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [h1]

theorem constantCoeff_negSign (j : ℤ) :
    PowerSeries.constantCoeff (negSign j : PowerSeries ℂ) = negSign j := by
  simp [negSign]

theorem evx_tripleSum :
    evx (tripleSum (uW ω hω)) = zSeries (fun j => (negSign j : ℂ) * ω ^ j) pentExp := by
  ext n
  rw [coeff_map, tripleSum, coeff_zSeries, coeff_zSeries, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [tripleCoeff, map_mul, constantCoeff_negSign, constantCoeff_uW_zpow]

theorem evx_liftD_tripleSum :
    evx (liftD (tripleSum (uW ω hω))) =
      zSeries (fun j => (negSign j : ℂ) * (j : ℂ) * ω ^ j) pentExp := by
  ext n
  rw [coeff_map, coeff_liftD, tripleSum, coeff_zSeries, coeff_zSeries, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [tripleCoeff, Derivation.leibniz, dx_negSign, dx_zpow_of_fixed _ (dx_uW ω hω), smul_eq_mul,
    smul_eq_mul, mul_zero, add_zero, map_mul, map_mul, constantCoeff_negSign,
    constantCoeff_uW_zpow]
  simp only [map_intCast]
  ring

end Units

theorem pjK0_eq_evx (F : PowerSeries (PowerSeries ℂ)) : pjK 0 F = evx F := by
  ext n; simp [pjK, coeff_map, coeff_zero_eq_constantCoeff]

theorem evx_C_uW (ω : ℂ) (hω : ω ≠ 0) :
    evx (PowerSeries.C ((uW ω hω : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = PowerSeries.C ω := by
  rw [PowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply, coeff_uW]; simp

theorem evx_R1 : evx (Rser (uW ω3 ω3_ne_zero)) =
    PowerSeries.C (-(ω3 - ω3⁻¹)) * toC VOA.DeligneAudit.DeligneMLDE.Heat.L0 := by
  rw [← pjK0_eq_evx, pj0R]

theorem evx_R2 : evx (Rser (uW ω3⁻¹ (inv_ne_zero ω3_ne_zero))) =
    PowerSeries.C (ω3 - ω3⁻¹) * toC VOA.DeligneAudit.DeligneMLDE.Heat.L0 := by
  rw [← pjK0_eq_evx, pjK_R, VOA.DeligneAudit.DeligneMLDE.Heat.L0, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, inv_inv]
  linear_combination -(ω3_sub_inv k)

theorem evx_P (ω : ℂ) (hω : ω ≠ 0) :
    evx (Pser (uW ω hω)) = infProd fun m =>
      (1 - PowerSeries.C ω * X ^ (m + 1)) * (1 - PowerSeries.C ω⁻¹ * X ^ (m + 1)) *
        (1 - X ^ (m + 1) : PowerSeries ℂ) := by
  rw [Pser, map_infProd' _ (prodFactors_tripleFactor _)]
  apply infProd_congr
  intro m
  have hinv : PowerSeries.constantCoeff (((uW ω hω)⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
      ω⁻¹ := by
    have := constantCoeff_uW_zpow ω hω (-1)
    rwa [zpow_neg_one, zpow_neg_one] at this
  have h1 : PowerSeries.constantCoeff (((uW ω hω) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = ω := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_uW]; simp
  simp only [tripleFactor, map_mul, map_sub, map_one, map_pow, PowerSeries.map_X,
    PowerSeries.map_C, hinv, h1]

theorem evx_P1P2 : evx (Pser (uW ω3 ω3_ne_zero) * Pser (uW ω3⁻¹ (inv_ne_zero ω3_ne_zero))) =
    expand 3 (by norm_num) (euler : PowerSeries ℂ) ^ 2 := by
  have hf : ∀ (a b : ℂ), ProdFactors fun m =>
      (1 - PowerSeries.C a * X ^ (m + 1)) * (1 - PowerSeries.C b * X ^ (m + 1)) *
        (1 - X ^ (m + 1) : PowerSeries ℂ) := fun a b m => by
    have h1 := prodFactors_one_add (R := ℂ) (-a) (fun m => m + 1) (fun m => Nat.lt_succ_self m) m
    have h2 := prodFactors_one_add (R := ℂ) (-b) (fun m => m + 1) (fun m => Nat.lt_succ_self m) m
    have h3 := prodFactors_one_add (R := ℂ) (-1) (fun m => m + 1) (fun m => Nat.lt_succ_self m) m
    simpa [sub_eq_add_neg] using (h1.mul h2).mul h3
  rw [map_mul, evx_P, evx_P, inv_inv, infProd_mul (hf _ _) (hf _ _), expand3_euler_eq,
    infProd_pow (prodFactors_one_sub_X_pow _ fun k => by omega)]
  apply infProd_congr
  intro m
  have hs : PowerSeries.C ω3 + PowerSeries.C ω3⁻¹ = (-1 : PowerSeries ℂ) := by
    rw [← map_add, ω3_add_inv', map_neg, map_one]
  have hp : PowerSeries.C ω3 * PowerSeries.C ω3⁻¹ = (1 : PowerSeries ℂ) := by
    rw [← map_mul, mul_inv_cancel₀ ω3_ne_zero, map_one]
  set t : PowerSeries ℂ := X ^ (m + 1)
  have ht : (X : PowerSeries ℂ) ^ (3 * m + 3) = t ^ 3 := by rw [← pow_mul]; congr 1; ring
  rw [ht]
  set a := PowerSeries.C ω3
  set b := PowerSeries.C ω3⁻¹
  have hA : (1 - a * t) * (1 - b * t) = 1 + t + t ^ 2 := by
    linear_combination (-t) * hs + t ^ 2 * hp
  calc (1 - a * t) * (1 - b * t) * (1 - t) * ((1 - b * t) * (1 - a * t) * (1 - t))
      = ((1 - a * t) * (1 - b * t)) ^ 2 * (1 - t) ^ 2 := by ring
    _ = (1 - t ^ 3) ^ 2 := by rw [hA]; ring

theorem finFib_pentExp' : FinFib pentExp := finFib_of_natAbs_le _ natAbs_le_pentExp

theorem fsr_swap {R : Type*} [CommRing R] (c : ℤ × ℤ → R) (e1 : ℤ → ℕ) :
    fsr c (fun p => e1 p.1 + e1 p.2) =
      fsr (fun p : ℤ × ℤ => c p.swap) (fun p => e1 p.1 + e1 p.2) := by
  rw [← fsr_equiv (Equiv.prodComm ℤ ℤ)]
  exact fsr_congr (fun _ => rfl) (fun p => by simp [add_comm])

/-- The sum side of the Wronskian: `2(Z'(ω)Z(ω⁻¹) - Z(ω)Z'(ω⁻¹)) = (ω - ω⁻¹) S`. -/
theorem wronskian_sum_side :
    2 * (zSeries (fun j => (negSign j : ℂ) * (j : ℂ) * ω3 ^ j) pentExp *
          zSeries (fun j => (negSign j : ℂ) * ω3⁻¹ ^ j) pentExp -
        zSeries (fun j => (negSign j : ℂ) * ω3 ^ j) pentExp *
          zSeries (fun j => (negSign j : ℂ) * (j : ℂ) * ω3⁻¹ ^ j) pentExp) =
      PowerSeries.C (ω3 - ω3⁻¹) * toC Sser := by
  have hF := finFib_pentExp'.prod finFib_pentExp'
  simp only [zSeries_eq_fsr _ _ natAbs_le_pentExp]
  rw [fsr_mul _ _ finFib_pentExp' finFib_pentExp', fsr_mul _ _ finFib_pentExp' finFib_pentExp',
    ← fsr_sub _ _ hF, Sser, toC, map_fsr _ _ hF, ← fsr_const_mul _ _ hF, two_mul]
  conv_lhs => arg 2; rw [fsr_swap]
  rw [← fsr_add _ _ hF]
  refine fsr_congr (fun p => ?_) (fun p => rfl)
  · obtain ⟨i, j⟩ := p
    simp only [Prod.swap_prod_mk]
    have hz := ω3_zpow_sub (i - j)
    have e1 : ω3⁻¹ ^ j = ω3 ^ (-j) := by rw [inv_zpow', ]
    have e2 : ω3⁻¹ ^ i = ω3 ^ (-i) := by rw [inv_zpow']
    have e3 : ω3 ^ i * ω3 ^ (-j) = ω3 ^ (i - j) := by rw [← zpow_add₀ ω3_ne_zero]; ring_nf
    have e4 : ω3 ^ j * ω3 ^ (-i) = ω3 ^ (-(i - j)) := by rw [← zpow_add₀ ω3_ne_zero]; ring_nf
    rw [e1, e2]
    simp only [negSign, map_mul, map_pow, map_neg, map_one, eq_ratCast,
      Rat.cast_intCast]
    push_cast
    linear_combination ((-1 : ℂ) ^ i.natAbs * (-1) ^ j.natAbs * ((i : ℂ) - j)) * hz +
      ((-1 : ℂ) ^ i.natAbs * (-1) ^ j.natAbs * (i : ℂ)) * e3 -
      ((-1 : ℂ) ^ i.natAbs * (-1) ^ j.natAbs * (j : ℂ)) * e3 +
      ((-1 : ℂ) ^ i.natAbs * (-1) ^ j.natAbs * (j : ℂ)) * e4 -
      ((-1 : ℂ) ^ i.natAbs * (-1) ^ j.natAbs * (i : ℂ)) * e4

/-- **The Wronskian side**: `S = -2 (q³;q³)²_∞ (1 + 6L₀)`. -/
theorem S_eq_wronskian :
    Sser = -2 * expand 3 (by norm_num) euler ^ 2 *
      (1 + 6 * VOA.DeligneAudit.DeligneMLDE.Heat.L0) := by
  set w1 := uW ω3 ω3_ne_zero
  set w2 := uW ω3⁻¹ (inv_ne_zero ω3_ne_zero)
  set A := PowerSeries ℂ
  have hw1 : PowerSeries.derivative ℂ (w1 : A) = w1 := dx_uW _ _
  have hw2 : PowerSeries.derivative ℂ (w2 : A) = w2 := dx_uW _ _
  have hT1 := jacobiTriple w1
  have hT2 := jacobiTriple w2
  rw [← Pser] at hT1 hT2
  have hD : ∀ (w : (PowerSeries ℂ)ˣ), PowerSeries.derivative ℂ (w : A) = w →
      liftD ((1 - PowerSeries.C (w : A)) * Pser w) =
        -PowerSeries.C (w : A) * Pser w + (1 - PowerSeries.C (w : A)) * (Pser w * Rser w) := by
    intro w hw
    rw [liftD_mul, liftD_P w hw, liftD_sub, liftD_one, liftD_C, hw]
    ring
  -- the Wronskian at the level of `ℂ⟦x⟧⟦q⟧`
  have hW : liftD (tripleSum w1) * tripleSum w2 - tripleSum w1 * liftD (tripleSum w2) =
      Pser w1 * Pser w2 * (-PowerSeries.C (w1 : A) * (1 - PowerSeries.C (w2 : A)) +
        PowerSeries.C (w2 : A) * (1 - PowerSeries.C (w1 : A)) +
        (1 - PowerSeries.C (w1 : A)) * (1 - PowerSeries.C (w2 : A)) * (Rser w1 - Rser w2)) := by
    rw [← hT1, ← hT2, hD w1 hw1, hD w2 hw2]
    ring
  have hE := congrArg evx hW
  simp only [map_sub, map_mul, map_add, map_neg, map_one] at hE
  rw [evx_liftD_tripleSum, evx_liftD_tripleSum, evx_tripleSum, evx_tripleSum, evx_C_uW, evx_C_uW,
    evx_R1, evx_R2, ← map_mul evx, evx_P1P2] at hE
  have hsum := wronskian_sum_side
  rw [hE] at hsum
  set L := toC VOA.DeligneAudit.DeligneMLDE.Heat.L0
  set E := expand 3 (by norm_num) (euler : PowerSeries ℂ)
  have hs : PowerSeries.C ω3 + PowerSeries.C ω3⁻¹ = (-1 : PowerSeries ℂ) := by
    rw [← map_add, ω3_add_inv', map_neg, map_one]
  have hp : PowerSeries.C ω3 * PowerSeries.C ω3⁻¹ = (1 : PowerSeries ℂ) := by
    rw [← map_mul, mul_inv_cancel₀ ω3_ne_zero, map_one]
  simp only [map_neg, map_sub] at hsum
  set a := PowerSeries.C ω3
  set b := PowerSeries.C ω3⁻¹
  have key : (a - b) * (toC Sser + 2 * E ^ 2 * (1 + 6 * L)) = 0 := by
    linear_combination (-1 : PowerSeries ℂ) * hsum + (4 * E ^ 2 * (a - b) * L) * hs -
      (4 * E ^ 2 * (a - b) * L) * hp
  have hab : a - b ≠ 0 := by
    rw [← map_sub]
    intro h
    exact ω3_ne_inv (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hS := (mul_eq_zero.mp key).resolve_left hab
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  change toC Sser = toC _
  rw [map_mul, map_mul, map_pow, map_add, map_mul, map_one, map_neg, map_ofNat, map_ofNat,
    map_expand', map_euler']
  linear_combination hS

end Wronskian

/-! ## Lorenz's formula -/

/-- **Lorenz's formula** `θ_{A₂} = 1 + 6 L₀`, `L₀ = ∑_{dk=n} χ₋₃(k) qⁿ`. -/
theorem aq_eq_one_add_six_L0 : AQ = 1 + 6 * VOA.DeligneAudit.DeligneMLDE.Heat.L0 := by
  have h := S_eq_lattice.symm.trans S_eq_wronskian
  have hE : (-2 * expand 3 (by norm_num) (euler : PowerSeries ℚ) ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [map_mul, map_pow, map_neg, map_ofNat, constantCoeff_expand, constantCoeff_euler,
      map_zero] at this
    norm_num at this
  exact mul_left_cancel₀ hE h

theorem lambertA2_eq_L0 : lambertA2 = 1 + 6 * VOA.DeligneAudit.DeligneMLDE.Heat.L0 := by
  ext n
  rw [lambertA2, coeff_mk, map_add, show (6 : PowerSeries ℚ) = PowerSeries.C 6 by
    rw [map_ofNat], coeff_C_mul, VOA.DeligneAudit.DeligneMLDE.Heat.coeff_L0, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', if_neg hn.ne', zero_add]
    congr 1

/-- **`LorenzA2` holds.** -/
theorem lorenzA2 : LorenzA2 := aq_eq_one_add_six_L0.trans lambertA2_eq_L0.symm

/-- The level-3 core from the Lambert-form Eisenstein relations alone. -/
theorem g2Level3Core_of_eisLambert (hE : G2Level3EisLambert) : G2Level3Core :=
  g2Level3Core_of_lambert lorenzA2 hE

/-- `G2KWEqMLDE` from the Lambert-form Eisenstein relations alone. -/
theorem g2KWEqMLDE_of_eisLambert (hE : G2Level3EisLambert) : G2KWEqMLDE :=
  g2KWEqMLDE_of_core ramanujanFormal (g2Level3Core_of_eisLambert hE)

end

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.S_eq_lattice
#print axioms VOA.DeligneAudit.G2Star.S_eq_wronskian
#print axioms VOA.DeligneAudit.G2Star.aq_eq_one_add_six_L0
#print axioms VOA.DeligneAudit.G2Star.lorenzA2
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE_of_eisLambert
end AxiomAudit
