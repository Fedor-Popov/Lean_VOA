/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Eis

/-!
# Separating cusps by weight-one Eisenstein binomials, away from a prime `p ∤ N`

For a prime `p ∤ N` put `M = sepModulus N p = 2N · Π_{1 ≤ j ≤ 4N², p ∤ j} j`, so `p ∤ M`, and
`A = ℤ[1/M][ζ_N]`. A value is *good* if it is a unit of `A`.

* `exists_sep_bin`: for `g ∈ SL₂ℤ` whose first column is not `±e₁ (mod N)` there is a binomial
  `c₁E_v − c₂E_w` (`c_i ∈ A`) with constant term `0` at `∞` and a good constant term at the cusp
  of `g`. Two cases: `g₁₀ ≢ 0` (an arithmetic progression of step `2 gcd(g₁₀, N)`, or a cotangent
  value) and `g₁₀ ≡ 0` (a wrap/no-wrap argument for `r ↦ r g₀₀ mod N`).
-/

open UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne.SSHecke

variable {N : ℕ}

/-- The modulus inverted at the prime `p`. -/
def sepModulus (N p : ℕ) : ℕ :=
  2 * N * ∏ j ∈ (Finset.Icc 1 (4 * N ^ 2)).filter (fun j => ¬ p ∣ j), j

theorem sepModulus_ne_zero {p : ℕ} (hN : 0 < N) : sepModulus N p ≠ 0 := by
  unfold sepModulus
  refine mul_ne_zero (by omega) (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_Icc] at hj
  omega

theorem two_mul_dvd_sepModulus (N p : ℕ) : 2 * N ∣ sepModulus N p := Dvd.intro _ rfl

theorem dvd_sepModulus {p j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 4 * N ^ 2) (hpj : ¬ p ∣ j) :
    j ∣ sepModulus N p := by
  have hmem : j ∈ (Finset.Icc 1 (4 * N ^ 2)).filter (fun j => ¬ p ∣ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hj⟩, hpj⟩
  exact (Finset.dvd_prod_of_mem (fun j : ℕ => j) hmem).trans (Dvd.intro_left _ rfl)

theorem not_dvd_sepModulus {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (h2N : 2 ∣ N) :
    ¬ p ∣ sepModulus N p := by
  unfold sepModulus
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      subst this
      exact hpN h2N
    · exact hpN h
  · obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    simp only [Finset.mem_filter] at hj
    exact hj.2 hpj

/-- A good value: a unit of the coefficient ring. -/
def GoodVal (A : Subalgebra (zInv M) ℂ) (x : ℂ) : Prop := x ∈ A ∧ x⁻¹ ∈ A ∧ x ≠ 0

theorem GoodVal.mul {M : ℕ} {A : Subalgebra (zInv M) ℂ} {x y : ℂ} (hx : GoodVal A x)
    (hy : GoodVal A y) : GoodVal A (x * y) :=
  ⟨A.mul_mem hx.1 hy.1, by rw [mul_inv]; exact A.mul_mem hx.2.1 hy.2.1,
    mul_ne_zero hx.2.2 hy.2.2⟩

theorem GoodVal.pow {M : ℕ} {A : Subalgebra (zInv M) ℂ} {x : ℂ} (hx : GoodVal A x) (n : ℕ) :
    GoodVal A (x ^ n) :=
  ⟨A.pow_mem hx.1 n, by rw [← inv_pow]; exact A.pow_mem hx.2.1 n, pow_ne_zero n hx.2.2⟩

theorem GoodVal.isUnit {M : ℕ} {A : Subalgebra (zInv M) ℂ} {x : ℂ} (hx : GoodVal A x) :
    IsUnit (⟨x, hx.1⟩ : A) :=
  isUnit_of_inv_mem hx.1 hx.2.1 hx.2.2

/-- Integer ratios with a bounded, `p`-prime numerator are good. -/
theorem goodVal_int_div {p : ℕ} (hN : 0 < N) {m : ℤ} {K : ℕ} (hm : ¬ (p : ℤ) ∣ m)
    (hmle : m.natAbs ≤ 4 * N ^ 2) (hK : K ∣ sepModulus N p) (hK0 : K ≠ 0) :
    GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N)) ((m : ℂ) / K) := by
  set A := frameRing (sepModulus N p) (weightOneStandardRoot N)
  have hM := sepModulus_ne_zero (p := p) hN
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hpm : ¬ p ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
  have hmM : m.natAbs ∣ sepModulus N p :=
    dvd_sepModulus (Int.natAbs_pos.mpr hm0) hmle hpm
  have hKC : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK0
  have hmC : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm0
  refine ⟨?_, ?_, div_ne_zero hmC hKC⟩
  · rw [div_eq_mul_inv]
    exact A.mul_mem (intCast_mem_frameRing _ _ m) (inv_natCast_mem_frameRing _ hM hK)
  · have habs : ((m.natAbs : ℕ) : ℂ) = (m : ℂ) ∨ ((m.natAbs : ℕ) : ℂ) = -(m : ℂ) := by
      rcases abs_choice m with h | h
      · left
        rw [← Int.cast_natCast, Int.natCast_natAbs, h]
      · right
        rw [← Int.cast_natCast, Int.natCast_natAbs, h, Int.cast_neg]
    have hinv := inv_natCast_mem_frameRing (weightOneStandardRoot N) hM hmM
    rw [inv_div, div_eq_mul_inv]
    refine A.mul_mem (natCast_mem_frameRing _ _ K) ?_
    rcases habs with h | h
    · rwa [h] at hinv
    · rw [h, inv_neg] at hinv
      simpa using A.neg_mem hinv

/-! ## Good constant terms -/

section Good

variable [NeZero N] {p : ℕ}

/-- `Cval x = (N - 2 x₀)/(2N)` is good when `p ∤ N - 2x₀`. -/
theorem goodVal_Cval_rat (x : Fin 2 → ZMod N) (hx0 : x 0 ≠ 0)
    (hp : ¬ (p : ℤ) ∣ ((N : ℤ) - 2 * (x 0).val)) :
    GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N)) (Cval x) := by
  have hN := NeZero.pos N
  have hlt := ZMod.val_lt (x 0)
  have hC : Cval x = (((N : ℤ) - 2 * (x 0).val : ℤ) : ℂ) / ((2 * N : ℕ) : ℂ) := by
    simp only [Cval, hx0, if_false]
    push_cast
    ring
  rw [hC]
  refine goodVal_int_div hN hp ?_ (two_mul_dvd_sepModulus N p) (by omega)
  have : ((N : ℤ) - 2 * (x 0).val).natAbs ≤ N := by omega
  nlinarith

/-- The cotangent constant term is good when `2 x₁ ≠ 0`. -/
theorem goodVal_Cval_cot (x : Fin 2 → ZMod N) (hx0 : x 0 = 0) (h2 : 2 * x 1 ≠ 0) :
    GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N)) (Cval x) := by
  have hN := NeZero.pos N
  set A := frameRing (sepModulus N p) (weightOneStandardRoot N)
  set ζ := weightOneStandardRoot N
  have hM := sepModulus_ne_zero (p := p) hN
  have hNM : N ∣ sepModulus N p := (Dvd.intro_left 2 rfl).trans (two_mul_dvd_sepModulus N p)
  have h2M : 2 ∣ sepModulus N p := (Dvd.intro _ rfl).trans (two_mul_dvd_sepModulus N p)
  have hzN : ζ ^ N = 1 := (stdRoot_isPrimitiveRoot N).pow_eq_one
  have hx1 : x 1 ≠ 0 := by rintro h; exact h2 (by rw [h, mul_zero])
  set b := (x 1).val
  have hb1 : ζ ^ b ≠ 1 := (stdRoot_isPrimitiveRoot N).pow_ne_one_of_pos_of_lt
    ((ZMod.val_ne_zero _).mpr hx1) (ZMod.val_lt _)
  have hb2 : ζ ^ (2 * b) ≠ 1 := by
    intro h
    rw [(stdRoot_isPrimitiveRoot N).pow_eq_one_iff_dvd] at h
    apply h2
    have : ((2 * b : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    simpa [b, ZMod.natCast_zmod_val] using this
  have hC : Cval x = (1 + ζ ^ b) / (2 * (1 - ζ ^ b)) := by simp [Cval, hx0, hx1, ζ, b]
  have hs1 : (1 : ℂ) - ζ ^ b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb1)
  have hs2 : (1 : ℂ) - ζ ^ (2 * b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb2)
  have hprod : (1 - ζ ^ b) * (1 + ζ ^ b) = 1 - ζ ^ (2 * b) := by rw [pow_mul']; ring
  have hp1 : (1 : ℂ) + ζ ^ b ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact hs2 hprod.symm
  have hi2 : ((2 : ℕ) : ℂ)⁻¹ ∈ A := inv_natCast_mem_frameRing _ hM h2M
  have hinvb := inv_one_sub_mem_frameRing hM hNM hN hzN b hb1
  have hinv2b := inv_one_sub_mem_frameRing hM hNM hN hzN (2 * b) hb2
  refine ⟨Cval_mem_frameRing hM (two_mul_dvd_sepModulus N p) x, ?_, ?_⟩
  · rw [hC, inv_div]
    have : 2 * (1 - ζ ^ b) / (1 + ζ ^ b) = 2 * (1 - ζ ^ b) * (1 - ζ ^ b) *
        (1 - ζ ^ (2 * b))⁻¹ := by
      rw [← hprod]; field_simp
    rw [this]
    refine A.mul_mem (A.mul_mem (A.mul_mem (natCast_mem_frameRing _ _ 2) ?_) ?_) hinv2b
    all_goals exact A.sub_mem A.one_mem (zeta_pow_mem_frameRing _ _ _)
  · rw [hC]
    exact div_ne_zero hp1 (mul_ne_zero two_ne_zero hs1)

end Good

/-! ## Case `g₁₀ ≢ 0 (mod N)` -/

section CaseA

variable [NeZero N] {p : ℕ}

theorem two_mul_le_of_dvd_of_lt {d N : ℕ} (hdN : d ∣ N) (hdlt : d < N) (hN : 0 < N) :
    2 * d ≤ N ∧ (2 * d = N ∨ 3 * d ≤ N) := by
  obtain ⟨e, rfl⟩ := hdN
  rcases e with _ | _ | _ | e
  · simp at hN
  · simp at hdlt
  · constructor <;> [omega; (left; ring)]
  · constructor
    · nlinarith
    · right; nlinarith

/-- The cotangent subcase `gcd(g₁₀, N) = N/2`. -/
theorem sep_caseA_cot (h24 : 24 ∣ N) (g : SL(2, ℤ))
    (hγ : ((g 1 0 : ℤ) : ZMod N) ≠ 0)
    (h2d : 2 * Nat.gcd (((g 1 0 : ℤ) : ZMod N)).val N = N) :
    ∃ v : Fin 2 → ZMod N, Cval v = 0 ∧
      GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
        (Cval (weightOneResidueAction v g)) := by
  have hN := NeZero.pos N
  have h2 : 2 ∣ N := dvd_trans (by norm_num) h24
  obtain ⟨q4, hq4⟩ : 4 ∣ N := dvd_trans (by norm_num) h24
  set h := N / 2 with hh
  have hhN : 2 * h = N := Nat.mul_div_cancel' h2
  have hhlt : h < N := by omega
  have hvalh : ((h : ℕ) : ZMod N).val = h := ZMod.val_natCast_of_lt hhlt
  have hh0 : ((h : ℕ) : ZMod N) ≠ 0 := by
    intro e; rw [e, ZMod.val_zero] at hvalh; omega
  set γc : ZMod N := ((g 1 0 : ℤ) : ZMod N) with hγc
  set d := Nat.gcd γc.val N with hd
  have hdh : d = h := by omega
  have hγv : 0 < γc.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr hγ)
  have hγlt : γc.val < N := ZMod.val_lt _
  have hγh : γc.val = h := by
    obtain ⟨k, hk⟩ : d ∣ γc.val := Nat.gcd_dvd_left _ _
    rw [hdh] at hk
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  -- integer entries
  set a00 := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set a01 := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set a10 := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set a11 := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hdet : a00 * a11 - a01 * a10 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hmod : a10 % (N : ℤ) = h := by
    have := ZMod.val_intCast (n := N) a10
    rw [← hγc, hγh] at this
    exact this.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a10 = h + N * k := by
    refine ⟨a10 / N, ?_⟩
    have hdecomp := Int.emod_add_mul_ediv a10 N
    rw [hmod] at hdecomp
    exact hdecomp.symm
  have e1 : (h : ℤ) = 2 * q4 := by omega
  have e2 : (N : ℤ) = 4 * q4 := by exact_mod_cast hq4
  have hev : Even a10 := ⟨q4 * k * 2 + q4, by rw [hk, e1, e2]; ring⟩
  have hodd : Odd (a00 * a11) := by
    have : a00 * a11 = 1 + a01 * a10 := by linarith
    rw [this]
    exact Even.one_add (hev.mul_left a01)
  obtain ⟨hodd0, hodd1⟩ := Int.odd_mul.mp hodd
  refine ⟨![((h : ℕ) : ZMod N), 1], ?_, ?_⟩
  · simp only [Cval, Matrix.cons_val_zero, hh0, if_false, hvalh]
    rw [div_eq_zero_iff]; left
    have : ((N : ℕ) : ℂ) = 2 * (h : ℂ) := by exact_mod_cast hhN.symm
    rw [this]; ring
  · have r0 : weightOneResidueAction ![((h : ℕ) : ZMod N), 1] g 0 =
        ((h : ℕ) : ZMod N) * (a00 : ZMod N) + (a10 : ZMod N) := by
      change ((h : ℕ) : ZMod N) * (a00 : ZMod N) + 1 * (a10 : ZMod N) = _
      ring
    have r1 : weightOneResidueAction ![((h : ℕ) : ZMod N), 1] g 1 =
        ((h : ℕ) : ZMod N) * (a01 : ZMod N) + (a11 : ZMod N) := by
      change ((h : ℕ) : ZMod N) * (a01 : ZMod N) + 1 * (a11 : ZMod N) = _
      ring
    apply goodVal_Cval_cot
    · rw [r0]
      have : ((h : ℕ) : ZMod N) * (a00 : ZMod N) + (a10 : ZMod N) =
          (((h : ℤ) * a00 + a10 : ℤ) : ZMod N) := by push_cast; ring
      rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨m, hm⟩ := hodd0
      refine ⟨m + 1 + k, ?_⟩
      rw [hm, hk, e2, e1]; ring
    · rw [r1]
      have : 2 * (((h : ℕ) : ZMod N) * (a01 : ZMod N) + (a11 : ZMod N)) =
          (((N : ℤ) * a01 + 2 * a11 : ℤ) : ZMod N) := by
        rw [← hhN]; push_cast; ring
      rw [this, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdiv
      have h4 : (4 : ℤ) ∣ (N : ℤ) * a01 + 2 * a11 :=
        dvd_trans ⟨q4, by rw [hq4]; push_cast; ring⟩ hdiv
      have h4' : (4 : ℤ) ∣ 2 * a11 := by
        have : (4 : ℤ) ∣ (N : ℤ) * a01 := ⟨q4 * a01, by rw [hq4]; push_cast; ring⟩
        have := dvd_sub h4 this
        simpa using this
      obtain ⟨m, hm⟩ := hodd1
      omega

theorem sep_caseA (hp : p.Prime) (hpN : ¬ p ∣ N) (h24 : 24 ∣ N) (g : SL(2, ℤ))
    (hγ : ((g 1 0 : ℤ) : ZMod N) ≠ 0) :
    ∃ v : Fin 2 → ZMod N, Cval v = 0 ∧
      GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
        (Cval (weightOneResidueAction v g)) := by
  have hN := NeZero.pos N
  have h2 : 2 ∣ N := dvd_trans (by norm_num) h24
  obtain ⟨q4, hq4⟩ : 4 ∣ N := dvd_trans (by norm_num) h24
  set h := N / 2 with hh
  have hhN : 2 * h = N := Nat.mul_div_cancel' h2
  have hhlt : h < N := by omega
  have hvalh : ((h : ℕ) : ZMod N).val = h := ZMod.val_natCast_of_lt hhlt
  have hh0 : ((h : ℕ) : ZMod N) ≠ 0 := by
    intro e; rw [e, ZMod.val_zero] at hvalh; omega
  have hCv : ∀ t : ZMod N, Cval ![((h : ℕ) : ZMod N), t] = 0 := by
    intro t
    simp only [Cval, Matrix.cons_val_zero, hh0, if_false, hvalh]
    rw [div_eq_zero_iff]; left
    have : ((N : ℕ) : ℂ) = 2 * (h : ℂ) := by exact_mod_cast hhN.symm
    rw [this]; ring
  set α : ZMod N := ((g 0 0 : ℤ) : ZMod N) with hα
  set γc : ZMod N := ((g 1 0 : ℤ) : ZMod N) with hγc
  have hact0 : ∀ t : ZMod N,
      weightOneResidueAction ![((h : ℕ) : ZMod N), t] g 0 = (h : ZMod N) * α + t * γc :=
    fun t => rfl
  -- the target values `s` with a good rational constant term suffice
  have hgood : ∀ s : ℕ, 0 < s → s < N → ¬ (p : ℤ) ∣ ((N : ℤ) - 2 * s) →
      (∃ t : ZMod N, (h : ZMod N) * α + t * γc = (s : ZMod N)) →
      ∃ v : Fin 2 → ZMod N, Cval v = 0 ∧
        GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
          (Cval (weightOneResidueAction v g)) := by
    rintro s hs0 hsN hps ⟨t, ht⟩
    refine ⟨![((h : ℕ) : ZMod N), t], hCv t, ?_⟩
    have hv0 : weightOneResidueAction ![((h : ℕ) : ZMod N), t] g 0 = (s : ZMod N) := by
      rw [hact0, ht]
    have hvs : ((s : ℕ) : ZMod N).val = s := ZMod.val_natCast_of_lt hsN
    refine goodVal_Cval_rat _ ?_ ?_
    · rw [hv0]; intro e; rw [e, ZMod.val_zero] at hvs; omega
    · rw [hv0, hvs]; exact hps
  -- gcd and Bezout
  set d := Nat.gcd γc.val N with hd
  have hγv : 0 < γc.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr hγ)
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hN
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hdle : d ≤ γc.val := Nat.gcd_le_left _ hγv
  have hdlt : d < N := lt_of_le_of_lt hdle (ZMod.val_lt _)
  have hpd : ¬ (p : ℤ) ∣ 2 * d := by
    intro hdiv
    have hdiv' : p ∣ 2 * d := by exact_mod_cast hdiv
    rcases (Nat.Prime.dvd_mul hp).mp hdiv' with h' | h'
    · exact hpN (dvd_trans h' h2)
    · exact hpN (dvd_trans h' hdN)
  have hbez : ((d : ℕ) : ZMod N) = γc * ((Nat.gcdA γc.val N : ℤ) : ZMod N) := by
    have h' := congrArg (fun z : ℤ => (z : ZMod N)) (Nat.gcd_eq_gcd_ab γc.val N)
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
      add_zero, ZMod.natCast_zmod_val] at h'
    exact h'
  set w0 : ZMod N := (h : ZMod N) * α with hw0
  set ρ := w0.val % d with hρ
  have hreach : ∀ j : ℕ, ∃ t : ZMod N, (h : ZMod N) * α + t * γc = ((ρ + d * j : ℕ) : ZMod N) := by
    intro j
    refine ⟨((Nat.gcdA γc.val N : ℤ) : ZMod N) * ((j : ZMod N) - ((w0.val / d : ℕ) : ZMod N)), ?_⟩
    have hcast : ((ρ : ℕ) : ZMod N) + (d : ZMod N) * ((w0.val / d : ℕ) : ZMod N) = w0 := by
      have e := congrArg (fun n : ℕ => (n : ZMod N)) (Nat.mod_add_div w0.val d)
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at e
      exact e
    push_cast
    linear_combination -hcast - ((j : ZMod N) - ((w0.val / d : ℕ) : ZMod N)) * hbez
  -- two consecutive values cannot both be bad
  have hpair : ∀ s : ℕ, (p : ℤ) ∣ ((N : ℤ) - 2 * s) →
      (p : ℤ) ∣ ((N : ℤ) - 2 * (s + d)) → False := by
    intro s h1 h2'
    apply hpd
    have := dvd_sub h1 h2'
    convert this using 1
    ring
  obtain ⟨h2d, h2d'⟩ := two_mul_le_of_dvd_of_lt hdN hdlt hN
  have hρd : ρ < d := Nat.mod_lt _ hd0
  by_cases hρ0 : ρ ≠ 0
  · -- `ρ` and `ρ + d`
    by_cases hb : (p : ℤ) ∣ ((N : ℤ) - 2 * ρ)
    · refine hgood (ρ + d * 1) (by omega) (by omega) ?_ (hreach 1)
      intro hb'
      exact hpair ρ hb (by simpa using hb')
    · exact hgood (ρ + d * 0) (by omega) (by omega) (by simpa using hb) (hreach 0)
  · push Not at hρ0
    rcases h2d' with h2d' | h3d
    · -- cotangent case: `g₁₀ ≡ N/2`
      exact sep_caseA_cot h24 g hγ h2d'
    · by_cases hb : (p : ℤ) ∣ ((N : ℤ) - 2 * d)
      · refine hgood (ρ + d * 2) (by omega) (by omega) ?_ (hreach 2)
        intro hb'
        exact hpair d hb (by rw [hρ0] at hb'; convert hb' using 3; push_cast; ring)
      · exact hgood (ρ + d * 1) (by omega) (by omega) (by rw [hρ0]; simpa using hb) (hreach 1)

end CaseA

/-! ## Case `g₁₀ ≡ 0 (mod N)` -/

theorem mul_succ_mod (N r a : ℕ) (ha : a < N) :
    ((r + 1) * a) % N = ((r * a) % N + a) % N := by
  rw [Nat.succ_mul, Nat.add_mod, Nat.mod_eq_of_lt ha]

/-- Some step of `r ↦ r a mod N` does not wrap around. -/
theorem exists_noWrap (N a : ℕ) (hN : 3 ≤ N) (ha2 : 2 ≤ a) (ha : a ≤ N - 2) :
    ∃ r, 1 ≤ r ∧ r ≤ N - 2 ∧ (r * a) % N + a < N := by
  by_contra H
  push Not at H
  have key : ∀ r, 1 ≤ r → r ≤ N - 1 → (r * a) % N + 2 * (r - 1) ≤ a := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => intro _; rw [one_mul, Nat.mod_eq_of_lt (by omega)]; omega
    | succ r hr ih =>
      intro hr'
      have hw := H r hr (by omega)
      have hlt : (r * a) % N < N := Nat.mod_lt _ (by omega)
      rw [mul_succ_mod N r a (by omega), Nat.mod_eq_sub_mod hw,
        Nat.mod_eq_of_lt (by omega)]
      have := ih (by omega)
      omega
  have := key (N - 1) (by omega) le_rfl
  omega

/-- Some step of `r ↦ r a mod N` wraps around. -/
theorem exists_wrap (N a : ℕ) (hN : 3 ≤ N) (ha2 : 2 ≤ a) (ha : a ≤ N - 2) :
    ∃ r, 1 ≤ r ∧ r ≤ N - 2 ∧ N ≤ (r * a) % N + a := by
  by_contra H
  push Not at H
  have key : ∀ r, 1 ≤ r → r ≤ N - 1 → (r * a) % N = r * a := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => intro _; rw [one_mul, Nat.mod_eq_of_lt (by omega)]
    | succ r hr ih =>
      intro hr'
      have hw := H r hr (by omega)
      rw [mul_succ_mod N r a (by omega), Nat.mod_eq_of_lt hw, ih (by omega), Nat.succ_mul]
  have h1 := key (N - 1) (by omega) le_rfl
  have h2 := Nat.mod_lt ((N - 1) * a) (by omega : 0 < N)
  rw [h1] at h2
  have : (N - 1) * 2 ≤ (N - 1) * a := Nat.mul_le_mul_left _ ha2
  omega

section CaseB

variable [NeZero N] {p : ℕ}

omit [NeZero N] in
theorem val_natCast_mul (r : ℕ) (hr : r < N) (α : ZMod N) :
    ((r : ZMod N) * α).val = (r * α.val) % N := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hr]

omit [NeZero N] in
theorem abs_N_sub_two_le (x : ℕ) (hx : x ≤ N) : |(N : ℤ) - 2 * x| ≤ N := by
  rw [abs_le]; constructor <;> omega

theorem sep_caseB (hp : p.Prime) (hpN : ¬ p ∣ N) (h24 : 24 ∣ N) (g : SL(2, ℤ))
    (hγ0 : ((g 1 0 : ℤ) : ZMod N) = 0) (hα1 : ((g 0 0 : ℤ) : ZMod N) ≠ 1)
    (hαm : ((g 0 0 : ℤ) : ZMod N) ≠ -1) :
    ∃ v w : Fin 2 → ZMod N,
      GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
        (Cval w * Cval (weightOneResidueAction v g) -
          Cval v * Cval (weightOneResidueAction w g)) := by
  have hN := NeZero.pos N
  have h2 : 2 ∣ N := dvd_trans (by norm_num) h24
  have hN24 : 24 ≤ N := Nat.le_of_dvd hN h24
  have hp2 : p ≠ 2 := by rintro rfl; exact hpN h2
  set α : ZMod N := ((g 0 0 : ℤ) : ZMod N) with hα
  set δ : ZMod N := ((g 1 1 : ℤ) : ZMod N) with hδ
  have hdet : α * δ = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) g.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hγ0, mul_zero, sub_zero] at this
    exact this
  have hα0 : α ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet
    have : (1 : ZMod N).val = 1 := ZMod.val_one_eq_one_mod N ▸ Nat.mod_eq_of_lt (by omega)
    rw [← hdet, ZMod.val_zero] at this; omega
  set a := α.val with ha
  have ha0 : a ≠ 0 := (ZMod.val_ne_zero _).mpr hα0
  have ha1 : a ≠ 1 := by
    intro h; apply hα1
    rw [← ZMod.natCast_zmod_val α, ← ha, h, Nat.cast_one]
  have haN : a ≠ N - 1 := by
    intro h; apply hαm
    rw [← ZMod.natCast_zmod_val α, ← ha, h, Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  have halt : a < N := ZMod.val_lt α
  have hunit : ∀ r : ZMod N, r * α = 0 → r = 0 := by
    intro r hr
    have := congrArg (· * δ) hr
    simpa [mul_assoc, hdet] using this
  -- the fixed vector `v = (N/2 - 1, 0)`
  set h := N / 2 with hh
  have hhN : 2 * h = N := Nat.mul_div_cancel' h2
  set h1 : ZMod N := ((h - 1 : ℕ) : ZMod N) with hh1
  have hvalh1 : h1.val = h - 1 := ZMod.val_natCast_of_lt (by omega)
  have hh10 : h1 ≠ 0 := by intro e; rw [e, ZMod.val_zero] at hvalh1; omega
  set κ := (h1 * α).val with hκ
  have hκN : κ ≤ N := (ZMod.val_lt _).le
  have hCv : Cval ![h1, 0] = ((2 : ℕ) : ℂ) / (2 * N) := by
    simp only [Cval, Matrix.cons_val_zero, hh10, if_false, hvalh1]
    congr 1
    have : ((h - 1 : ℕ) : ℂ) = (h : ℂ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    have : ((N : ℕ) : ℂ) = 2 * (h : ℂ) := by exact_mod_cast hhN.symm
    rw [this]; push_cast; ring
  have hvg : Cval (weightOneResidueAction ![h1, 0] g) = ((N : ℂ) - 2 * κ) / (2 * N) := by
    have e0 : weightOneResidueAction ![h1, 0] g 0 = h1 * α := by
      change h1 * α + 0 * _ = _; ring
    have hne : h1 * α ≠ 0 := fun e => hh10 (hunit h1 e)
    simp only [Cval, e0, hne, if_false]
    rfl
  have hw : ∀ r : ℕ, 1 ≤ r → r < N → Cval ![(r : ZMod N), 0] = ((N : ℂ) - 2 * r) / (2 * N) := by
    intro r hr1 hrN
    have hv : ((r : ℕ) : ZMod N).val = r := ZMod.val_natCast_of_lt hrN
    have hne : ((r : ℕ) : ZMod N) ≠ 0 := by intro e; rw [e, ZMod.val_zero] at hv; omega
    simp only [Cval, Matrix.cons_val_zero, hne, if_false, hv]
  have hwg : ∀ r : ℕ, 1 ≤ r → r < N →
      Cval (weightOneResidueAction ![(r : ZMod N), 0] g) =
        ((N : ℂ) - 2 * ((r * a) % N : ℕ)) / (2 * N) := by
    intro r hr1 hrN
    have e0 : weightOneResidueAction ![(r : ZMod N), 0] g 0 = (r : ZMod N) * α := by
      change (r : ZMod N) * α + 0 * _ = _; ring
    have hv : ((r : ℕ) : ZMod N).val = r := ZMod.val_natCast_of_lt hrN
    have hne : (r : ZMod N) * α ≠ 0 := by
      intro e; have := hunit _ e; rw [this, ZMod.val_zero] at hv; omega
    simp only [Cval, e0, hne, if_false, val_natCast_mul r hrN α]
    rfl
  -- the integer numerator
  let m : ℕ → ℤ := fun r =>
    ((N : ℤ) - 2 * r) * ((N : ℤ) - 2 * κ) - 2 * ((N : ℤ) - 2 * ((r * a) % N : ℕ))
  have hval : ∀ r : ℕ, 1 ≤ r → r < N →
      Cval ![(r : ZMod N), 0] * Cval (weightOneResidueAction ![h1, 0] g) -
        Cval ![h1, 0] * Cval (weightOneResidueAction ![(r : ZMod N), 0] g) =
          ((m r : ℤ) : ℂ) / ((4 * N ^ 2 : ℕ) : ℂ) := by
    intro r hr1 hrN
    rw [hw r hr1 hrN, hvg, hCv, hwg r hr1 hrN]
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [m]
    generalize (r * a) % N = c
    push_cast
    field_simp
    ring
  -- choose `r` with `p ∤ m r`
  obtain ⟨r1, hr1, hr1', hnw⟩ := exists_noWrap N a (by omega) (by omega) (by omega)
  obtain ⟨r2, hr2, hr2', hwr⟩ := exists_wrap N a (by omega) (by omega) (by omega)
  have hstep1 : (((r1 + 1) * a) % N : ℕ) = (r1 * a) % N + a := by
    rw [mul_succ_mod N r1 a halt, Nat.mod_eq_of_lt hnw]
  have hstep2 : (((r2 + 1) * a) % N : ℕ) + N = (r2 * a) % N + a := by
    rw [mul_succ_mod N r2 a halt, Nat.mod_eq_sub_mod hwr,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (r2 * a) hN; omega)]
    omega
  have hex : ∃ r, 1 ≤ r ∧ r < N ∧ ¬ (p : ℤ) ∣ m r := by
    by_contra H
    push Not at H
    have d1 := dvd_sub (H (r1 + 1) (by omega) (by omega)) (H r1 hr1 (by omega))
    have d2 := dvd_sub (H (r2 + 1) (by omega) (by omega)) (H r2 hr2 (by omega))
    have c1 : ((((r1 + 1) * a) % N : ℕ) : ℤ) = (((r1 * a) % N : ℕ) : ℤ) + a := by
      exact_mod_cast hstep1
    have c2 : ((((r2 + 1) * a) % N : ℕ) : ℤ) = (((r2 * a) % N : ℕ) : ℤ) + a - N := by
      have : ((((r2 + 1) * a) % N : ℕ) : ℤ) + N = (((r2 * a) % N : ℕ) : ℤ) + a := by
        exact_mod_cast hstep2
      linarith
    have e1 : m (r1 + 1) - m r1 = -2 * ((N : ℤ) - 2 * κ) + 4 * a := by
      simp only [m]; rw [c1]; push_cast; ring
    have e2 : m (r2 + 1) - m r2 = -2 * ((N : ℤ) - 2 * κ) + 4 * a - 4 * N := by
      simp only [m]; rw [c2]; push_cast; ring
    rw [e1] at d1
    rw [e2] at d2
    have d3 := dvd_sub d1 d2
    have h4N : (p : ℤ) ∣ 4 * N := by convert d3 using 1; ring
    have h4N' : p ∣ 4 * N := by exact_mod_cast h4N
    rcases (Nat.Prime.dvd_mul hp).mp h4N' with h' | h'
    · have : p ∣ 2 ^ 2 := by simpa using h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    · exact hpN h'
  obtain ⟨r, hr1, hrN, hpr⟩ := hex
  refine ⟨![h1, 0], ![(r : ZMod N), 0], ?_⟩
  rw [hval r hr1 hrN]
  have hp4 : ¬ p ∣ 4 * N ^ 2 := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h' | h'
    · have : p ∣ 2 ^ 2 := by simpa using h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    · exact hpN (hp.dvd_of_dvd_pow h')
  have hN2 : 1 ≤ 4 * N ^ 2 := by nlinarith
  refine goodVal_int_div hN hpr ?_ (dvd_sepModulus hN2 le_rfl hp4) (by omega)
  have b1 := abs_N_sub_two_le (N := N) r hrN.le
  have b2 := abs_N_sub_two_le (N := N) κ hκN
  have b3 := abs_N_sub_two_le (N := N) ((r * a) % N) (Nat.mod_lt _ hN).le
  have hb : |m r| ≤ 4 * (N : ℤ) ^ 2 := by
    simp only [m]
    calc |((N : ℤ) - 2 * r) * ((N : ℤ) - 2 * κ) - 2 * ((N : ℤ) - 2 * ((r * a) % N : ℕ))|
        ≤ |((N : ℤ) - 2 * r)| * |((N : ℤ) - 2 * κ)| + 2 * |(N : ℤ) - 2 * ((r * a) % N : ℕ)| := by
          have := abs_sub (((N : ℤ) - 2 * r) * ((N : ℤ) - 2 * κ))
            (2 * ((N : ℤ) - 2 * ((r * a) % N : ℕ)))
          rw [abs_mul, abs_mul (2 : ℤ), abs_two] at this
          exact this
      _ ≤ (N : ℤ) * N + 2 * N := by
          gcongr
      _ ≤ 4 * (N : ℤ) ^ 2 := by nlinarith
  have : ((m r).natAbs : ℤ) ≤ 4 * (N : ℤ) ^ 2 := by rw [Int.natCast_natAbs]; exact hb
  exact_mod_cast this

end CaseB

/-- **Separation of two cusps.** -/
theorem exists_sep_bin [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (h24 : 24 ∣ N)
    (g : SL(2, ℤ))
    (hg : ¬ ((((g 0 0 : ℤ) : ZMod N) = 1 ∨ ((g 0 0 : ℤ) : ZMod N) = -1) ∧
      ((g 1 0 : ℤ) : ZMod N) = 0)) :
    ∃ b : Bin N, b.c1 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) ∧
      b.c2 ∈ frameRing (sepModulus N p) (weightOneStandardRoot N) ∧
      b.c1 * Cval b.v - b.c2 * Cval b.w = 0 ∧
      GoodVal (frameRing (sepModulus N p) (weightOneStandardRoot N))
        (b.c1 * Cval (b.act g).v - b.c2 * Cval (b.act g).w) := by
  have hN := NeZero.pos N
  have hM := sepModulus_ne_zero (p := p) hN
  set A := frameRing (sepModulus N p) (weightOneStandardRoot N)
  by_cases hγ : ((g 1 0 : ℤ) : ZMod N) = 0
  · have hα : ((g 0 0 : ℤ) : ZMod N) ≠ 1 ∧ ((g 0 0 : ℤ) : ZMod N) ≠ -1 := by
      constructor <;> intro h <;> exact hg ⟨by tauto, hγ⟩
    obtain ⟨v, w, hvw⟩ := sep_caseB hp hpN h24 g hγ hα.1 hα.2
    refine ⟨⟨Cval w, v, Cval v, w⟩, Cval_mem_frameRing hM (two_mul_dvd_sepModulus N p) w,
      Cval_mem_frameRing hM (two_mul_dvd_sepModulus N p) v, by ring, ?_⟩
    exact hvw
  · obtain ⟨v, hv0, hv⟩ := sep_caseA hp hpN h24 g hγ
    refine ⟨⟨1, v, 0, 0⟩, A.one_mem, A.zero_mem, by simp [hv0], ?_⟩
    simpa [Bin.act] using hv

end VOA.Classification.COne.SSHecke
