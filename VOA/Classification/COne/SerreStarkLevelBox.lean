/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelChar

/-!
# Serre–Stark S4-3: reduction of the square-class residual to the level box

Let `g ∈ M_{1/2}(N, χ)` (`24 ∣ N`) be a simultaneous `T(p²)`-eigenform supported on one square
class. Under `SerreStarkBoundedCoeff24`, S4-1/S4-2 show: the class is `t·□` with `t` squarefree,
`t ∣ N`, and `a(n v²) = ψ(v) a(n)` for `v` prime to `N`, with `ψ = eigenChar χ t` primitive of
conductor `r ∣ N`. Then (this file):

* coefficient calculus of `θ_{ψ,T}`: `charThetaCoeff_eq_zero_of_forall_ne`,
  `charThetaCoeff_self`, `charThetaCoeff_mul_sq` (multiplicativity for `v` prime to `T`);
* `IsClassForm N r ψ t f`: `θ`-type of level `N`, support in `t·□`, `a(n v²) = ψ(v) a(n)`;
* `exists_box_sub`: subtracting a finite combination of the `θ_{ψ, t S²}` with `4 t S² r² ∣ N`
  (the "level box"; these are in Serre–Stark's spanning set) makes the coefficients `a(t S²)` on
  the whole box vanish;
* the residual `SerreStarkLevelBox24`: a class form whose coefficients vanish on the box vanishes;
* `squareClass_of_boundedCoeff_of_levelBox :
  SerreStarkBoundedCoeff24 → SerreStarkLevelBox24 → SerreStarkSquareClass24`;
* `iSerreStark24_of_boundedCoeff_of_levelBox`.
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Coefficients of `θ_{ψ,T}` -/

section ThetaCoeff

variable {r : ℕ} (ψ : DirichletCharacter ℂ r)

theorem charThetaCoeff_eq_zero_of_forall_ne {T k : ℕ} (h : ∀ b : ℤ, sqIdx T b ≠ k) :
    charThetaCoeff r ψ T k = 0 := by
  haveI : IsEmpty (sqIdx T ⁻¹' {k}) := ⟨fun b => h b.1 b.2⟩
  simp [charThetaCoeff]

theorem exists_of_charThetaCoeff_ne_zero {T k : ℕ} (h : charThetaCoeff r ψ T k ≠ 0) :
    ∃ b : ℤ, T * b.natAbs ^ 2 = k := by
  by_contra hne
  push_neg at hne
  exact h (charThetaCoeff_eq_zero_of_forall_ne ψ hne)

theorem charThetaCoeff_self {T : ℕ} (hT : 1 ≤ T) :
    charThetaCoeff r ψ T T = ψ (1 : ℤ) + ψ (-1 : ℤ) := by
  have hset : sqIdx T ⁻¹' {T} = ↑({1, -1} : Finset ℤ) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, sqIdx, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff]
    constructor
    · intro hb
      have h1 : b.natAbs ^ 2 = 1 := by
        have : T * b.natAbs ^ 2 = T * 1 := by rw [hb, mul_one]
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      have h2 : b.natAbs = 1 := by
        rcases Nat.lt_trichotomy b.natAbs 1 with h | h | h
        · interval_cases (b.natAbs); simp at h1
        · exact h
        · nlinarith
      rcases Int.natAbs_eq_iff.1 h2 with h | h
      · left; simpa using h
      · right; simpa using h
    · rintro (rfl | rfl) <;> simp
  rw [charThetaCoeff, tsum_congr_set_coe (fun b : ℤ => ψ (b : ZMod r)) hset,
    Finset.tsum_subtype' ({1, -1} : Finset ℤ) (fun b : ℤ => ψ (b : ZMod r)),
    Finset.sum_pair (by decide)]

theorem charThetaCoeff_lt {t K S : ℕ} (ht : 1 ≤ t) (hS : 1 ≤ S) (hSK : S < K) :
    charThetaCoeff r ψ (t * K ^ 2) (t * S ^ 2) = 0 := by
  refine charThetaCoeff_eq_zero_of_forall_ne ψ fun b hb => ?_
  simp only [sqIdx] at hb
  rcases Nat.eq_zero_or_pos b.natAbs with h0 | h0
  · rw [h0] at hb
    simp at hb
    rcases hb with h | h
    · omega
    · omega
  · have h1 : K ^ 2 ≤ K ^ 2 * b.natAbs ^ 2 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h2 : S ^ 2 < K ^ 2 := Nat.pow_lt_pow_left hSK two_ne_zero
    have h3 : t * S ^ 2 < t * (K ^ 2 * b.natAbs ^ 2) :=
      Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le h2 h1) ht
    rw [← mul_assoc] at h3
    omega

/-- **Multiplicativity.** For `v` prime to `T`, `c(k v²) = ψ(v) c(k)`. -/
theorem charThetaCoeff_mul_sq {T v : ℕ} (hv0 : 0 < v) (hvT : v.Coprime T) (k : ℕ) :
    charThetaCoeff r ψ T (k * v ^ 2) = ψ (v : ZMod r) * charThetaCoeff r ψ T k := by
  have hvz : (v : ℤ) ≠ 0 := by exact_mod_cast hv0.ne'
  have hdvd : ∀ b : ℤ, sqIdx T b = k * v ^ 2 → (v : ℤ) ∣ b := by
    intro b hb
    simp only [sqIdx] at hb
    rw [Int.natCast_dvd]
    have h1 : v ^ 2 ∣ T * b.natAbs ^ 2 := ⟨k, by rw [hb]; ring⟩
    have h2 : v ^ 2 ∣ b.natAbs ^ 2 := (Nat.Coprime.pow_left 2 hvT).dvd_of_dvd_mul_left h1
    exact (Nat.pow_dvd_pow_iff two_ne_zero).1 h2
  let e : (sqIdx T ⁻¹' {k}) ≃ (sqIdx T ⁻¹' {k * v ^ 2}) :=
    { toFun := fun c => ⟨(v : ℤ) * c.1, by
        have hc : T * c.1.natAbs ^ 2 = k := c.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff, sqIdx]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        calc T * (v * c.1.natAbs) ^ 2 = (T * c.1.natAbs ^ 2) * v ^ 2 := by ring
          _ = k * v ^ 2 := by rw [hc]⟩
      invFun := fun b => ⟨b.1 / v, by
        have hb := b.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
        obtain ⟨c, hc⟩ := hdvd b.1 hb
        simp only [Set.mem_preimage, Set.mem_singleton_iff, sqIdx] at hb ⊢
        rw [hc, Int.mul_ediv_cancel_left _ hvz]
        rw [hc, Int.natAbs_mul, Int.natAbs_natCast] at hb
        have : v ^ 2 * (T * c.natAbs ^ 2) = v ^ 2 * k := by
          calc v ^ 2 * (T * c.natAbs ^ 2) = T * (v * c.natAbs) ^ 2 := by ring
            _ = k * v ^ 2 := hb
            _ = v ^ 2 * k := by ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this⟩
      left_inv := fun c => by
        apply Subtype.ext
        simp only
        exact Int.mul_ediv_cancel_left _ hvz
      right_inv := fun b => by
        apply Subtype.ext
        simp only
        have hb := b.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
        exact Int.mul_ediv_cancel' (hdvd b.1 hb) }
  rw [charThetaCoeff, charThetaCoeff, ← Equiv.tsum_eq e, ← tsum_mul_left]
  refine tsum_congr fun c => ?_
  change ψ (((v : ℤ) * c.1 : ℤ) : ZMod r) = _
  rw [Int.cast_mul, map_mul, Int.cast_natCast]

end ThetaCoeff

/-! ## Constant θ-type forms vanish -/

/-- A θ-type form of level `N` (`4 ∣ N`) whose positive-index coefficients vanish is zero on `ℍ`. -/
theorem thetaType_eq_zero_of_coeff_pos {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) {f : ℂ → ℂ}
    (hf : IsThetaTypeForm N f) (hg : ∀ n, 0 < n → thetaTypeCoeff f n = 0) :
    ∀ τ : ℂ, 0 < τ.im → f τ = 0 := by
  set a0 := thetaTypeCoeff f 0
  have hconst : ∀ τ : ℂ, 0 < τ.im → f τ = a0 := by
    intro τ hτ
    have hs := hf.hasSum_coeff hτ
    have hs' : HasSum (fun n : ℕ => thetaTypeCoeff f n * cexp (2 * Real.pi * I * n * τ))
        (thetaTypeCoeff f 0 * cexp (2 * Real.pi * I * (0 : ℕ) * τ)) := by
      refine hasSum_single 0 fun n hn => ?_
      rw [hg n (Nat.pos_of_ne_zero hn), zero_mul]
    have := hs.unique hs'
    simpa using this
  have ha0 : a0 = 0 := by
    by_contra h0
    have hI : (0 : ℝ) < (I : ℂ).im := by simp
    have hγ : lowerMat N ∈ CongruenceSubgroup.Gamma1 N := by
      rw [CongruenceSubgroup.Gamma1_mem]; simp [lowerMat]
    have hlaw := hf.multiplier (lowerMat N) hγ I hI
    rw [hconst _ (im_mobius_pos _ hI), hconst _ hI] at hlaw
    have heq : thetaRef I = thetaRef (mobius (lowerMat N) I) := by
      apply mul_left_cancel₀ h0; linear_combination hlaw
    have hc4 : (4 : ℤ) ∣ lowerMat N 1 0 := by
      simp [lowerMat]; exact_mod_cast h4
    have hnorm := norm_thetaRef_mobius hc4 hI
    rw [← heq] at hnorm
    have hθ : ‖thetaRef I‖ ≠ 0 := norm_ne_zero_iff.2 (thetaRef_ne_zero_of_im_pos hI)
    have h1 : ‖((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)‖ ^ (1 / 2 : ℝ) = 1 := by
      have := hnorm
      field_simp at this
      linarith [this]
    have hgt : 1 < ‖((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)‖ := by
      have hz := Complex.abs_im_le_norm
        (((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ))
      have him : (((lowerMat N 1 0 : ℤ) : ℂ) * I + ((lowerMat N 1 1 : ℤ) : ℂ)).im = N := by
        simp [lowerMat]
      rw [him] at hz
      have : (1 : ℝ) < N := by
        have : 4 ≤ N := Nat.le_of_dvd hN h4
        exact_mod_cast (by omega : 1 < N)
      linarith [abs_of_pos (show (0 : ℝ) < N by positivity)]
    have := Real.one_lt_rpow hgt (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  intro τ hτ
  rw [hconst τ hτ, ha0]

/-! ## Class forms -/

/-- A **class form** for `(ψ, t)` at level `N`: a θ-type form of level `N` whose positive
support lies in `t·□` and whose coefficients satisfy `a(n v²) = ψ(v) a(n)` for `n > 0` and `v`
prime to `N`. (By S4-1/S4-2, every simultaneous `T(p²)`-eigenform on one square class is one,
under `SerreStarkBoundedCoeff24`.) -/
def IsClassForm (N r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ) (f : ℂ → ℂ) : Prop :=
  IsThetaTypeForm N f ∧
    (∀ n, 0 < n → thetaTypeCoeff f n ≠ 0 → ∃ x, n = t * x ^ 2) ∧
    ∀ n v, 0 < n → v.Coprime N → thetaTypeCoeff f (n * v ^ 2) = (ψ (v : ZMod r)) *
      thetaTypeCoeff f n

theorem IsClassForm.zero {N r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) :
    IsClassForm N r ψ t (fun _ => 0) := by
  have h0 : ∀ n, thetaTypeCoeff (fun _ : ℂ => (0 : ℂ)) n = 0 := fun n =>
    (IsThetaTypeForm.zero (N := N)).coeff_eq_of_hasSum (c := fun _ => 0)
      (fun τ _ => by simpa using hasSum_zero) n
  exact ⟨IsThetaTypeForm.zero, fun n _ h => absurd (h0 n) h, fun n v _ _ => by simp [h0]⟩

theorem IsClassForm.add_smul {N r : ℕ} {ψ : DirichletCharacter ℂ r} {t : ℕ} {f g : ℂ → ℂ}
    (hf : IsClassForm N r ψ t f) (hg : IsClassForm N r ψ t g) (c : ℂ) :
    IsClassForm N r ψ t (f + c • g) := by
  have hcf : ∀ n, thetaTypeCoeff (f + c • g) n = thetaTypeCoeff f n + c * thetaTypeCoeff g n :=
    fun n => by rw [hf.1.coeff_add (hg.1.smul c), hg.1.coeff_smul]
  refine ⟨hf.1.add (hg.1.smul c), fun n hn h => ?_, fun n v hn hv => ?_⟩
  · rw [hcf] at h
    by_cases h1 : thetaTypeCoeff f n = 0
    · rw [h1, zero_add] at h
      exact hg.2.1 n hn (right_ne_zero_of_mul h)
    · exact hf.2.1 n hn h1
  · rw [hcf, hcf, hf.2.2 n v hn hv, hg.2.2 n v hn hv]; ring

/-- The theta series `θ_{ψ, t S²}` with `4 t S² r² ∣ N` is a class form. -/
theorem isClassForm_charTheta {N r t S : ℕ} (h24 : 24 ∣ N) (hr : 0 < r) (ht : 1 ≤ t)
    (hS : 1 ≤ S) (hdiv : 4 * (t * S ^ 2) * r ^ 2 ∣ N) (ψ : DirichletCharacter ℂ r) :
    IsClassForm N r ψ t (charTheta r ψ (t * S ^ 2 : ℕ)) := by
  have hT : 1 ≤ t * S ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hθ := isThetaTypeForm_charTheta h24 hr hT hdiv ψ
  have hc := fun k => thetaTypeCoeff_charTheta h24 hr hT hdiv ψ k
  have hTN : t * S ^ 2 ∣ N :=
    Dvd.dvd.trans (show t * S ^ 2 ∣ 4 * (t * S ^ 2) * r ^ 2 from ⟨4 * r ^ 2, by ring⟩) hdiv
  refine ⟨hθ, fun n hn h => ?_, fun n v hn hv => ?_⟩
  · rw [hc] at h
    obtain ⟨b, hb⟩ := exists_of_charThetaCoeff_ne_zero ψ h
    exact ⟨S * b.natAbs, by rw [← hb]; ring⟩
  · have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with h | h
      · subst h
        rw [Nat.coprime_zero_left] at hv
        subst hv
        exact absurd h24 (by norm_num)
      · exact h
    rw [hc, hc, charThetaCoeff_mul_sq ψ hv0 (Nat.Coprime.coprime_dvd_right hTN hv)]

/-! ## Subtracting the level box -/

/-- The **level box** condition for `(ψ, t, S)` at level `N`: `ψ` even and `4 t S² r² ∣ N`. -/
def InBox (N r : ℕ) (ψ : DirichletCharacter ℂ r) (t S : ℕ) : Prop :=
  ψ.Even ∧ 4 * t * S ^ 2 * r ^ 2 ∣ N

/-- **Box subtraction.** For a class form `f`, there is a class form `h` in the span of the
`θ_{ψ, t S²}` (`S` in the box) such that `f − h` has `a(t S²) = 0` for every `S ≤ K` in the box. -/
theorem exists_box_sub {N r t : ℕ} (h24 : 24 ∣ N) (hr : 0 < r) (ht : 1 ≤ t)
    {ψ : DirichletCharacter ℂ r} (hprim : ψ.IsPrimitive) {f : ℂ → ℂ}
    (hf : IsClassForm N r ψ t f) (K : ℕ) :
    ∃ h : ℂ → ℂ, IsClassForm N r ψ t h ∧
      restrictUpper h ∈ Submodule.span ℂ (charThetaSet N) ∧
      ∀ S, 1 ≤ S → S ≤ K → InBox N r ψ t S → thetaTypeCoeff (f - h) (t * S ^ 2) = 0 := by
  induction K with
  | zero =>
    refine ⟨fun _ => 0, IsClassForm.zero ψ t, ?_, fun S h1 h2 _ => by omega⟩
    have : restrictUpper (fun _ : ℂ => (0 : ℂ)) = 0 := rfl
    rw [this]; exact Submodule.zero_mem _
  | succ K ih =>
    obtain ⟨h, hh, hspan, hvan⟩ := ih
    have hfh : IsClassForm N r ψ t (f - h) := by
      have := hf.add_smul hh (-1)
      simpa [sub_eq_add_neg] using this
    by_cases hbox : InBox N r ψ t (K + 1)
    · set T := t * (K + 1) ^ 2 with hT
      have hdiv : 4 * T * r ^ 2 ∣ N := by rw [hT]; simpa [mul_assoc] using hbox.2
      have hθ := isClassForm_charTheta h24 hr ht (Nat.succ_pos K) hdiv ψ
      set c := thetaTypeCoeff (f - h) T / 2 with hc
      refine ⟨h + c • charTheta r ψ (T : ℕ), hh.add_smul hθ c, ?_, ?_⟩
      · rw [map_add, map_smul]
        refine Submodule.add_mem _ hspan (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
        exact ⟨r, T, ψ, hprim, hbox.1, Nat.one_le_iff_ne_zero.2 (by positivity), hdiv, rfl⟩
      · intro S hS1 hSK hSbox
        have hθc := fun k => thetaTypeCoeff_charTheta h24 hr
          (Nat.one_le_iff_ne_zero.2 (by positivity) : 1 ≤ T) hdiv ψ k
        have e : f - (h + c • charTheta r ψ (T : ℕ)) = (f - h) + (-c) • charTheta r ψ (T : ℕ) := by
          funext τ; simp; ring
        rw [e, hfh.1.coeff_add (hθ.1.smul _), hθ.1.coeff_smul, hθc]
        rcases Nat.lt_or_ge S (K + 1) with hlt | hge
        · rw [hvan S hS1 (by omega) hSbox, charThetaCoeff_lt ψ ht hS1 hlt]; ring
        · have hSe : S = K + 1 := by omega
          subst hSe
          rw [← hT, charThetaCoeff_self ψ (Nat.one_le_iff_ne_zero.2 (by positivity))]
          have hev : ψ (-1 : ℤ) = 1 := by
            have := hbox.1
            rw [DirichletCharacter.Even] at this
            simpa using this
          rw [show ψ ((1 : ℤ) : ZMod r) = 1 by simp, hev, hc]
          ring
    · refine ⟨h, hh, hspan, fun S hS1 hSK hSbox => ?_⟩
      rcases Nat.lt_or_ge S (K + 1) with hlt | hge
      · exact hvan S hS1 (by omega) hSbox
      · have hSe : S = K + 1 := by omega
        subst hSe
        exact absurd hSbox hbox

/-! ## The residual -/

/-- **Residual (the level box).** Let `24 ∣ N`, `ψ` a primitive character of conductor `r ∣ N`,
`t ∣ N` squarefree, and `f` a class form for `(ψ, t)` at level `N` (θ-type, positive support in
`t·□`, `a(n v²) = ψ(v) a(n)` for `v` prime to `N`). If `a(t S²) = 0` for every `S ≥ 1` in the
level box (`ψ` even and `4 t S² r² ∣ N`), then all positive-index coefficients of `f` vanish.

TRUE (from Serre–Stark's Theorem A *with* linear independence, LNM 627, 1977, Thm A; independence
is the trivial half, cf. Achimescu–Saha arXiv:0803.3788 §6.2 Case 1): write
`f = Σ c_{φ,T} θ_{φ,T}` over even primitive `φ` and `4 T r_φ² ∣ N`. Coefficients of `θ_{φ,T}` at
`n v²` are `φ(v)` times those at `n`; since the restrictions to `(ℤ/N)ˣ` of distinct primitive
characters of conductor dividing `N` are distinct, the hypothesis `a(n v²) = ψ(v) a(n)` kills
(by independence of characters, then of the `θ_{φ,T}`) every component with `φ ≠ ψ`; the support
hypothesis kills every `T ∉ t·□`; so `f = Σ_{S in box} c_S θ_{ψ, t S²}`, and the coefficient of
`q^{t S²}` is `2 Σ_{S' ∣ S} c_{S'} ψ(S/S')`, a unitriangular system: all `c_S = 0`.
(If `ψ` is odd the box is empty and so is the family: `f` has no positive coefficients.)

What it contains: Serre–Stark's level analysis — operators `U(p)`, `V(p)`, `W(N)`, `S(ψ)`,
`K(p)`, the oldform criterion (their Theorem 1), and the newform theorem (`θ_ψ` is the only
newform; Mellin transform / functional equation of `Σ a(n²) n^{-s}` against `L(2s, ψ)`). -/
def SerreStarkLevelBox24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (_h24 : 24 ∣ N) (r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ)
    (f : ℂ → ℂ), ψ.IsPrimitive → r ∣ N → Squarefree t → t ∣ N → IsClassForm N r ψ t f →
    (∀ S, 1 ≤ S → InBox N r ψ t S → thetaTypeCoeff f (t * S ^ 2) = 0) →
    ∀ n, 0 < n → thetaTypeCoeff f n = 0

/-- Under the box residual, every class form lies in the span of Serre–Stark's theta series. -/
theorem mem_span_of_levelBox (hL : SerreStarkLevelBox24) {N r t : ℕ} (hN : 0 < N)
    (h24 : 24 ∣ N) {ψ : DirichletCharacter ℂ r} (hprim : ψ.IsPrimitive) (hrN : r ∣ N)
    (ht : Squarefree t) (htN : t ∣ N) {f : ℂ → ℂ} (hf : IsClassForm N r ψ t f) :
    restrictUpper f ∈ Submodule.span ℂ (charThetaSet N) := by
  have hr : 0 < r := Nat.pos_of_dvd_of_pos hrN hN
  have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.2 ht.ne_zero
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  obtain ⟨h, hh, hspan, hvan⟩ := exists_box_sub h24 hr ht1 hprim hf N
  have hfh : IsClassForm N r ψ t (f - h) := by
    have := hf.add_smul hh (-1)
    simpa [sub_eq_add_neg] using this
  have hbox : ∀ S, 1 ≤ S → InBox N r ψ t S → thetaTypeCoeff (f - h) (t * S ^ 2) = 0 := by
    intro S hS hSb
    refine hvan S hS ?_ hSb
    have hd : S ^ 2 ∣ N := (Dvd.intro_left (4 * t) (by ring) : S ^ 2 ∣ 4 * t * S ^ 2).trans
      ((Dvd.intro _ rfl : 4 * t * S ^ 2 ∣ 4 * t * S ^ 2 * r ^ 2).trans hSb.2)
    calc S ≤ S ^ 2 := Nat.le_self_pow two_ne_zero S
      _ ≤ N := Nat.le_of_dvd hN hd
  have hpos := hL N hN h24 r ψ t (f - h) hprim hrN ht htN hfh hbox
  have hzero := thetaType_eq_zero_of_coeff_pos hN h4 hfh.1 hpos
  have : restrictUpper f = restrictUpper h := by
    funext τ
    have := hzero τ τ.2
    simp only [Pi.sub_apply, sub_eq_zero] at this
    simpa [restrictUpper_apply] using this
  rw [this]
  exact hspan

/-! ## Assembly -/

/-- `4t ∣ N` for squarefree `t ∣ N`, `24 ∣ N`. -/
theorem four_mul_dvd_of_squarefree {t N : ℕ} (h24 : 24 ∣ N) (ht : Squarefree t) (htN : t ∣ N) :
    4 * t ∣ N := by
  rcases Nat.even_or_odd t with he | ho
  · obtain ⟨u, rfl⟩ := he
    have hu : Odd u := by
      by_contra hu
      rw [Nat.not_odd_iff_even] at hu
      obtain ⟨w, rfl⟩ := hu
      have := Nat.isUnit_iff.1 (ht 2 ⟨w, by ring⟩)
      omega
    have h8 : 8 ∣ N := (show 8 ∣ 24 by norm_num).trans h24
    have huN : u ∣ N := (Dvd.intro_left 2 (by ring) : u ∣ u + u).trans htN
    have hc : Nat.Coprime 8 u := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hu)
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h8 huN
    rw [show 4 * (u + u) = 8 * u by ring]
    exact this
  · have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
    have hc : Nat.Coprime 4 t := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 ho)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h4 htN

/-- **Reduction.** Bounded coefficients and the level-box residual give the square-class
residual. -/
theorem squareClass_of_boundedCoeff_of_levelBox (hB : SerreStarkBoundedCoeff24)
    (hL : SerreStarkLevelBox24) : SerreStarkSquareClass24 := by
  intro N hN h24 χ g hE hsq
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  by_cases hall : ∀ n, 0 < n → mCoeff g n = 0
  · have := eq_zero_of_mCoeff_pos hN h4 g hall
    rw [this]
    exact Submodule.zero_mem _
  push Not at hall
  obtain ⟨n₀, hn₀, ha₀⟩ := hall
  obtain ⟨t, s₀, ht, hs₀, hn₀e, hsupp⟩ := exists_squarefree_class hsq hn₀ ha₀
  have htN : t ∣ N := squarefree_dvd_of_eigen hB hN h24 χ g hE ht hs₀ (hn₀e ▸ ha₀)
  have h4t : 4 * t ∣ N := four_mul_dvd_of_squarefree h24 ht htN
  have hN1 : 1 < N := by have := Nat.le_of_dvd hN h24; omega
  set ψ := eigenChar χ h4t hN1
  have hmult := mCoeff_mul_sq_of_coprime hB hN h24 χ g hE hsupp
  have hcls : IsClassForm N _ ψ t (extH (g : ℍ → ℂ)) := by
    refine ⟨(extH_of_mem g.2).thetaType, fun n hn h => hsupp n hn h, fun n v hn hv => ?_⟩
    change mCoeff g (n * v ^ 2) = _ * mCoeff g n
    rw [hmult v hv n hn, eigenChar_natCast χ h4t hN1 hv]
  have := mem_span_of_levelBox hL hN h24 (eigenChar_isPrimitive χ h4t hN1)
    (conductor_eigenChar_dvd χ h4t hN1) ht htN hcls
  rwa [restrictUpper_extH] at this

/-- **Reduction.** Bounded coefficients and the level-box residual give `ISerreStark` at every
level divisible by `24`. -/
theorem iSerreStark24_of_boundedCoeff_of_levelBox (hB : SerreStarkBoundedCoeff24)
    (hL : SerreStarkLevelBox24) : ISerreStark24 :=
  iSerreStark24_of_boundedCoeff_of_squareClass hB (squareClass_of_boundedCoeff_of_levelBox hB hL)

end SSHecke

end VOA.Classification.COne
