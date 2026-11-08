/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Code/Weights.lean
  CFSG/Monster/Code/LatticeShort.lean
  CFSG/Monster/Code/LatticeCount.lean
  CFSG/Monster/Griess/Short.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.GriessTrilinear

/-!
# Axiom's Monster port (triality closure): the three families of minimal Leech vectors, `196560`, `98280`

* `minVecs_eq` — the minimal vectors of `Λ` (norm `32` in `√8`-coordinates) are the union of
  `minFamily₁` (`(±4, ±4, 0²²)`), `minFamily₂` (`(±2⁸, 0¹⁶)` on an octad, even number of `-2`) and
  `minFamily₃` (`oddMin i d = (∓3, ±1²³)`); the families are pairwise disjoint;
* explicit parametrisations `fam₁Param`, `fam₂Vec`, `oddMin` with their injectivity, the finite sets
  `fam₁Fin`, `fam₂Fin`, `fam₃Fin`, `minFin` and the count `card_minFin = 196560`
  (`1104 + 97152 + 98304`; uses `wtCount_eight = 759`, `decide +kernel`);
* `card_classes`, `card_shortIdx : Nat.card ShortIdx = 98280`.

## Port notes
* Namespaces `CFSG.Monster.Code`, `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess.Code`,
  `VOA.Moonshine.MonsterGriess`.  Module-system syntax dropped.  Bodies verbatim except as listed.
* The source's private helpers of `LatticeShort.lean` (`val_zero'`, `odd_sq`, `sq_par`,
  `neg_one_pow_val`, …) are private in our `MinimalVectors.lean`; they are restated here (private,
  verbatim).  `LatticeCount.lean`'s duplicate private `neg_one_pow_val` is the same statement.
* `Code.sgn : Bool → ℤ` is the source's `CFSG.Monster.Code.sgn` (distinct from
  `MonsterGriess.sgn : ZMod 2 → ℚ`).
* `decide +kernel` (kernel-checked): `wtCount_eight`, `card_lt_pairs`, `card_fam₁Dom`.
* Omitted: the summary theorem `mog_lattice_short_vectors`.
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess.Code

open VOA.Moonshine.MonsterGriess
open scoped Finset

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem val_zero' : (0 : ZMod 2).val = 0 := rfl

private theorem val_one' : (1 : ZMod 2).val = 1 := rfl

private theorem bitLift_zero' : bitLift 0 = 0 := rfl

private theorem bitLift_one' : bitLift 1 = 1 := rfl

/-! ### From `CFSG/Monster/Code/Weights.lean` -/

def wtCount (w : ℕ) : ℕ := treeSumN (fun a => if popc 24 a = w then 1 else 0) Bmask 12 0

theorem wtCount_eight : wtCount 8 = 759 := by decide +kernel

theorem card_filter_wt (w : ℕ) :
    #{x ∈ Finset.univ.filter (· ∈ C) | hammingNorm x = w} = wtCount w := by
  rw [Finset.card_filter, sum_C_eq_treeSumN]
  simp only [wtCount, hammingNorm_bvec]

/-! ### From `CFSG/Monster/Code/LatticeShort.lean` -/

def minFamily₁ : Set (Fin 24 → ℤ) :=
  {u | #{i | u i ≠ 0} = 2 ∧ ∀ i, u i ≠ 0 → u i = 4 ∨ u i = -4}

def minFamily₂ : Set (Fin 24 → ℤ) :=
  {u | ∃ d ∈ C, hammingNorm d = 8 ∧ (∀ i, d i ≠ 0 → u i = 2 ∨ u i = -2) ∧
    (∀ i, d i = 0 → u i = 0) ∧ Even #{i | u i = -2}}

private theorem odd_sq (x : ℤ) (hx : x % 2 = 1) : ∃ t, 0 ≤ t ∧ x * x = 1 + 8 * t := by
  obtain ⟨q, rfl⟩ : ∃ q, x = 2 * q + 1 := ⟨x / 2, by omega⟩
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self q
  have hq : 0 ≤ q * (q + 1) := by
    rcases le_or_gt 0 q with h | h
    · positivity
    · nlinarith
  refine ⟨r, by linarith, ?_⟩
  linear_combination 4 * hr

private theorem sign_one (x : ℤ) (t : ZMod 2) (hx : x * x = 1)
    (hc : x ≡ 1 + 2 * bitLift t [ZMOD 4]) : x = (-1) ^ t.val := by
  have h : x = 1 ∨ x = -1 := mul_self_eq_one_iff.1 hx
  unfold Int.ModEq at hc
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', pow_zero]; rw [bitLift_zero'] at hc; omega
  · rw [val_one', pow_one]; rw [bitLift_one'] at hc; omega

private theorem sign_three (x : ℤ) (t : ZMod 2) (hx : x * x = 9)
    (hc : x ≡ 1 + 2 * bitLift t [ZMOD 4]) : x = (-1) ^ t.val * (1 - 4) := by
  have h : x = 3 ∨ x = -3 := mul_self_eq_mul_self_iff.1 (by rw [hx]; norm_num)
  unfold Int.ModEq at hc
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', pow_zero]; rw [bitLift_zero'] at hc; omega
  · rw [val_one', pow_one]; rw [bitLift_one'] at hc; omega

private theorem sq_par (x : ℤ) : (x * x - x) % 2 = 0 := by
  have h := Int.even_mul_pred_self x
  rw [Int.even_iff] at h
  have e : x * x - x = x * (x - 1) := by ring
  rw [e]
  exact h

private theorem exists_eq_one {t : Fin 24 → ℤ} (h0 : ∀ i, 0 ≤ t i) (h1 : ∑ i, t i = 1) :
    ∃ i₀, t i₀ = 1 ∧ ∀ j, j ≠ i₀ → t j = 0 := by
  obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ Finset.univ, t i₀ ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
  have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i₀, t j := Finset.sum_nonneg fun j _ => h0 j
  have hsplit := Finset.add_sum_erase Finset.univ t (Finset.mem_univ i₀)
  rw [h1] at hsplit
  have ht : t i₀ = 1 := by have := h0 i₀; omega
  refine ⟨i₀, ht, fun j hj => ?_⟩
  have hzero : ∑ j ∈ Finset.univ.erase i₀, t j = 0 := by omega
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j).1 hzero j
    (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)

theorem le_normSq (u : Fin 24 → ℤ) (i : Fin 24) : u i * u i ≤ normSq u :=
  Finset.single_le_sum (f := fun i => u i * u i) (fun j _ => mul_self_nonneg (u j))
    (Finset.mem_univ i)

theorem mem_minFamily₃_of_odd {u : Fin 24 → ℤ} {d : Fin 24 → ZMod 2} (hd : d ∈ C)
    (hud : ∀ i, u i ≡ 1 + 2 * bitLift (d i) [ZMOD 4]) (hn : normSq u = 32) :
    u ∈ minFamily₃ := by
  have hodd : ∀ i, u i % 2 = 1 := fun i => by
    have h := hud i
    unfold Int.ModEq at h
    have := bitLift_zero_or_one (d i)
    omega
  choose t ht0 ht using fun i => odd_sq (u i) (hodd i)
  have hsum : ∑ i, t i = 1 := by
    have h : normSq u = ∑ i, (1 + 8 * t i) := Finset.sum_congr rfl fun i _ => ht i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hn] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one] at h
    omega
  obtain ⟨i₀, hi₀, hj⟩ := exists_eq_one ht0 hsum
  refine ⟨i₀, d, hd, funext fun j => ?_⟩
  by_cases hji : j = i₀
  · subst hji
    simp only [oddMin, ite_true, mul_one]
    exact sign_three _ _ (by rw [ht, hi₀]; norm_num) (hud _)
  · simp only [oddMin, hji, ite_false, mul_zero, sub_zero, mul_one]
    exact sign_one _ _ (by rw [ht, hj j hji]; norm_num) (hud j)

theorem mem_minFamily₁_of_four {u : Fin 24 → ℤ} (hu4 : ∀ i, u i % 4 = 0) (hn : normSq u = 32) :
    u ∈ minFamily₁ := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 24 → ℤ, ∀ i, u i = 4 * w i :=
    ⟨fun i => u i / 4, fun i => by have := hu4 i; show u i = 4 * (u i / 4); omega⟩
  have hsum : ∑ i, w i * w i = 2 := by
    have h : normSq u = ∑ i, 16 * (w i * w i) :=
      Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
    rw [← Finset.mul_sum, hn] at h
    omega
  have hbound : ∀ i, w i * w i ≤ 2 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun i => w i * w i) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hval : ∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1 := fun i => by
    have h := hbound i
    have h1 : w i ≤ 1 := by nlinarith
    have h2 : -1 ≤ w i := by nlinarith
    omega
  refine ⟨?_, fun i hi => ?_⟩
  · have hind : ∀ i, (if u i ≠ 0 then (1 : ℤ) else 0) = w i * w i := fun i => by
      rw [hw i]
      rcases hval i with h | h | h <;> rw [h] <;> norm_num
    have : ((#{i | u i ≠ 0} : ℕ) : ℤ) = 2 := by
      rw [Finset.natCast_card_filter, ← hsum]
      exact Finset.sum_congr rfl fun i _ => hind i
    exact_mod_cast this
  · rw [hw i] at hi ⊢
    rcases hval i with h | h | h
    · right; rw [h]; norm_num
    · exact absurd (by rw [h]; norm_num) hi
    · left; rw [h]; norm_num

theorem mem_minFamily₂_of_even {u : Fin 24 → ℤ} {d : Fin 24 → ZMod 2} (hd : d ∈ C) (hd0 : d ≠ 0)
    (hud : ∀ i, u i ≡ 2 * bitLift (d i) [ZMOD 4]) (hus : ∑ i, u i ≡ 0 [ZMOD 8])
    (hn : normSq u = 32) : u ∈ minFamily₂ := by
  have hw8 : 8 ≤ hammingNorm d := eight_le_wt hd hd0
  have hlow : ∀ i, 4 * bitLift (d i) ≤ u i * u i := fun i => by
    have h := hud i
    unfold Int.ModEq at h
    rcases bitLift_zero_or_one (d i) with hb | hb
    · rw [hb]; simpa using mul_self_nonneg (u i)
    · rw [hb] at h ⊢
      have : u i ≥ 2 ∨ u i ≤ -2 := by omega
      rcases this with h' | h' <;> nlinarith
  have hsumb : ∑ i, bitLift (d i) = hammingNorm d := sum_bitLift d
  have hzero : ∑ i, (u i * u i - 4 * bitLift (d i)) = 32 - 4 * hammingNorm d := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumb]
    exact congrArg (· - _) hn
  have hnn : ∀ i, 0 ≤ u i * u i - 4 * bitLift (d i) := fun i => by linarith [hlow i]
  have hnonneg := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hnn i
  have hwt : hammingNorm d = 8 := by
    have : (hammingNorm d : ℤ) ≤ 8 := by linarith
    exact_mod_cast le_antisymm this (by exact_mod_cast hw8)
  have heach : ∀ i, u i * u i = 4 * bitLift (d i) := fun i => by
    have h0 : ∑ i, (u i * u i - 4 * bitLift (d i)) = 0 := by rw [hzero, hwt]; norm_num
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 h0 i (Finset.mem_univ i)
    linarith
  have hon : ∀ i, d i ≠ 0 → u i = 2 ∨ u i = -2 := fun i hi => by
    have hb : bitLift (d i) = 1 := by
      rcases zmod2_cases (d i) with h | h
      · exact absurd h hi
      · rw [h]; rfl
    have h := heach i
    rw [hb] at h
    exact mul_self_eq_mul_self_iff.1 (by rw [h]; norm_num)
  have hoff : ∀ i, d i = 0 → u i = 0 := fun i hi => by
    have h := heach i
    rw [hi, bitLift_zero', mul_zero] at h
    exact mul_self_eq_zero.1 h
  refine ⟨d, hd, hwt, hon, hoff, ?_⟩
  have hcoord : ∀ i, u i = 2 * bitLift (d i) - 4 * (if u i = -2 then 1 else 0) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  have hs : ∑ i, u i = 16 - 4 * (#{i | u i = -2} : ℕ) := by
    rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hsumb, hwt, Finset.natCast_card_filter]
    norm_num
  rw [hs] at hus
  unfold Int.ModEq at hus
  rw [Nat.even_iff]
  omega

theorem mem_families_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    u ∈ minFamily₁ ∪ minFamily₂ ∪ minFamily₃ := by
  obtain ⟨hL, hn⟩ := mem_minVecs_iff.1 hu
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hL
  rcases hm with rfl | rfl
  · by_cases hd0 : d = 0
    · subst hd0
      refine Or.inl (Or.inl (mem_minFamily₁_of_four (fun i => ?_) hn))
      have h := hud i
      unfold Int.ModEq at h
      simpa [bitLift_zero'] using h
    · exact Or.inl (Or.inr (mem_minFamily₂_of_even hd hd0 (fun i => by simpa using hud i)
        (by simpa using hus) hn))
  · exact Or.inr (mem_minFamily₃_of_odd hd hud hn)

theorem minFamily₁_subset : minFamily₁ ⊆ minVecs := by
  rintro u ⟨hcard, hval⟩
  have hv : ∀ i, u i = 4 * (if u i = 4 then 1 else if u i = -4 then -1 else 0) := fun i => by
    by_cases h : u i = 0
    · simp [h]
    · rcases hval i h with h' | h' <;> simp [h']
  have hsq : ∀ i, u i * u i = 16 * (if u i ≠ 0 then 1 else 0) := fun i => by
    by_cases h : u i = 0
    · simp [h]
    · rcases hval i h with h' | h' <;> simp [h']
  have hn : normSq u = 32 := by
    rw [normSq, Finset.sum_congr rfl fun i _ => hsq i, ← Finset.mul_sum, ← Finset.natCast_card_filter,
      hcard]
    norm_num
  refine mem_minVecs_iff.2 ⟨⟨0, .inl rfl, 0, C.zero_mem, fun i => ?_, ?_⟩, hn⟩
  · simp only [Pi.zero_apply, bitLift_zero', mul_zero, add_zero]
    rw [hv i]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
  ·
    set s : Fin 24 → ℤ := fun i => if u i = 4 then 1 else if u i = -4 then -1 else 0
    have hs2 : ∀ i, s i * s i = if u i ≠ 0 then 1 else 0 := fun i => by
      by_cases h : u i = 0
      · simp [s, h]
      · rcases hval i h with h' | h' <;> simp [s, h']
    have hss : ∑ i, s i * s i = 2 := by
      rw [Finset.sum_congr rfl fun i _ => hs2 i, ← Finset.natCast_card_filter, hcard]
      norm_num
    have hpar : Even (∑ i, (s i * s i - s i)) :=
      Finset.even_sum _ fun i _ => Int.even_iff.2 (sq_par (s i))
    rw [Int.even_iff, Finset.sum_sub_distrib, hss] at hpar
    have hsum : ∑ i, u i = 4 * ∑ i, s i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hv i
    rw [hsum]
    unfold Int.ModEq
    omega

theorem minFamily₂_subset : minFamily₂ ⊆ minVecs := by
  rintro u ⟨d, hd, hwt, hon, hoff, heven⟩
  have hsq : ∀ i, u i * u i = 4 * bitLift (d i) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  have hn : normSq u = 32 := by
    rw [normSq, Finset.sum_congr rfl fun i _ => hsq i, ← Finset.mul_sum, sum_bitLift, hwt]
    norm_num
  have hcoord : ∀ i, u i = 2 * bitLift (d i) - 4 * (if u i = -2 then 1 else 0) := fun i => by
    rcases zmod2_cases (d i) with h | h
    · rw [hoff i h, h, bitLift_zero']; norm_num
    · rw [h, bitLift_one']
      rcases hon i (by rw [h]; exact one_ne_zero) with h' | h' <;> rw [h'] <;> norm_num
  refine mem_minVecs_iff.2 ⟨⟨0, .inl rfl, d, hd, fun i => ?_, ?_⟩, hn⟩
  · rw [zero_add]
    unfold Int.ModEq
    rw [hcoord i]
    split_ifs <;> omega
  · have hs : ∑ i, u i = 16 - 4 * (#{i | u i = -2} : ℕ) := by
      rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, sum_bitLift, hwt, Finset.natCast_card_filter]
      norm_num
    rw [hs, mul_zero]
    unfold Int.ModEq
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    push_cast
    omega

private theorem neg_one_pow_val (t : ZMod 2) : ((-1 : ℤ) ^ t.val) = 1 - 2 * bitLift t := by
  rcases zmod2_cases t with rfl | rfl
  · rw [val_zero', bitLift_zero']; norm_num
  · rw [val_one', bitLift_one']; norm_num

theorem minVecs_eq : minVecs = minFamily₁ ∪ minFamily₂ ∪ minFamily₃ := by
  refine Set.Subset.antisymm (fun u hu => mem_families_of_mem_minVecs hu) ?_
  rintro u ((h | h) | h)
  · exact minFamily₁_subset h
  · exact minFamily₂_subset h
  · exact minFamily₃_subset h

theorem minFamily₃_odd {u : Fin 24 → ℤ} (hu : u ∈ minFamily₃) : u 0 % 2 = 1 := by
  obtain ⟨i, d, -, rfl⟩ := hu
  rw [oddMin, neg_one_pow_val]
  rcases bitLift_zero_or_one (d 0) with hb | hb <;> rw [hb] <;> split_ifs <;> norm_num

theorem minFamily₁_even {u : Fin 24 → ℤ} (hu : u ∈ minFamily₁) (i : Fin 24) :
    u i = 0 ∨ u i = 4 ∨ u i = -4 := by
  by_cases h : u i = 0
  · exact Or.inl h
  · exact Or.inr (hu.2 i h)

theorem minFamily₂_even {u : Fin 24 → ℤ} (hu : u ∈ minFamily₂) (i : Fin 24) :
    u i = 0 ∨ u i = 2 ∨ u i = -2 := by
  obtain ⟨d, -, -, hon, hoff, -⟩ := hu
  by_cases h : d i = 0
  · exact Or.inl (hoff i h)
  · exact Or.inr (hon i h)

theorem disjoint_minFamily₁₂ : Disjoint minFamily₁ minFamily₂ := by
  rw [Set.disjoint_left]
  intro u h1 h2
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    have hne : (Finset.univ.filter fun i => u i ≠ 0).Nonempty :=
      Finset.card_pos.1 (by rw [h1.1]; norm_num)
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  rcases h1.2 i hi with h | h <;> rcases minFamily₂_even h2 i with h' | h' | h' <;> omega

theorem disjoint_minFamily₁₃ : Disjoint minFamily₁ minFamily₃ := by
  rw [Set.disjoint_left]
  intro u h1 h3
  have := minFamily₃_odd h3
  rcases minFamily₁_even h1 0 with h | h | h <;> rw [h] at this <;> norm_num at this

theorem disjoint_minFamily₂₃ : Disjoint minFamily₂ minFamily₃ := by
  rw [Set.disjoint_left]
  intro u h2 h3
  have := minFamily₃_odd h3
  rcases minFamily₂_even h2 0 with h | h | h <;> rw [h] at this <;> norm_num at this

/-! ### From `CFSG/Monster/Code/LatticeCount.lean` -/

/-- The sign `Bool → ℤ` of `LatticeCount.lean` (the source's `CFSG.Monster.Code.sgn`). -/
def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> decide

theorem sgn_injective : Function.Injective sgn := by decide

def fam₁Param (p : (Fin 24 × Fin 24) × (Bool × Bool)) : Fin 24 → ℤ :=
  fun k => (if k = p.1.1 then 4 * sgn p.2.1 else 0) + (if k = p.1.2 then 4 * sgn p.2.2 else 0)

@[irreducible] def fam₁Dom : Finset ((Fin 24 × Fin 24) × (Bool × Bool)) :=
  (Finset.univ.filter fun q : Fin 24 × Fin 24 => q.1 < q.2) ×ˢ Finset.univ

theorem mem_fam₁Dom {p : (Fin 24 × Fin 24) × (Bool × Bool)} : p ∈ fam₁Dom ↔ p.1.1 < p.1.2 := by
  unfold fam₁Dom
  simp

private theorem card_lt_pairs :
    (Finset.univ.filter fun q : Fin 24 × Fin 24 => q.1 < q.2).card = 276 := by
  decide +kernel

theorem card_fam₁Dom : fam₁Dom.card = 1104 := by
  unfold fam₁Dom
  rw [Finset.card_product, card_lt_pairs]
  decide +kernel

theorem fam₁Param_ne_zero_iff {p : (Fin 24 × Fin 24) × (Bool × Bool)}
    (hp : p.1.1 < p.1.2) (k : Fin 24) : fam₁Param p k ≠ 0 ↔ k = p.1.1 ∨ k = p.1.2 := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp
  have h1 := sgn_ne_zero p.2.1
  have h2 := sgn_ne_zero p.2.2
  by_cases hk1 : k = p.1.1
  · subst hk1
    simp only [fam₁Param, ite_true, hne, ite_false, add_zero, true_or, iff_true]
    exact mul_ne_zero (by norm_num) h1
  · by_cases hk2 : k = p.1.2
    · subst hk2
      simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, or_true, iff_true]
      exact mul_ne_zero (by norm_num) h2
    · simp [fam₁Param, hk1, hk2]

theorem fam₁Param_injOn : Set.InjOn fam₁Param fam₁Dom := by
  rintro ⟨⟨i, j⟩, s, t⟩ hp ⟨⟨i', j'⟩, s', t'⟩ hq h
  have hp' : i < j := mem_fam₁Dom.1 (Finset.mem_coe.1 hp)
  have hq' : i' < j' := mem_fam₁Dom.1 (Finset.mem_coe.1 hq)
  have hsupp : ∀ k, (k = i ∨ k = j) ↔ (k = i' ∨ k = j') := fun k => by
    rw [← fam₁Param_ne_zero_iff (p := ((i, j), s, t)) hp', ← fam₁Param_ne_zero_iff
      (p := ((i', j'), s', t')) hq', h]
  have hi := (hsupp i).1 (Or.inl rfl)
  have hj := (hsupp j).1 (Or.inr rfl)
  have hi' := (hsupp i').2 (Or.inl rfl)
  have hj' := (hsupp j').2 (Or.inr rfl)
  have hij : i = i' ∧ j = j' := by
    rw [Fin.lt_def] at hp' hq'
    simp only [Fin.ext_iff] at hi hj hi' hj'
    constructor <;> ext <;> omega
  obtain ⟨rfl, rfl⟩ := hij
  have hne : i ≠ j := ne_of_lt hp'
  have hs := congrFun h i
  have ht := congrFun h j
  simp only [fam₁Param, ite_true, hne, ite_false, add_zero, Ne.symm hne, zero_add] at hs ht
  have hs' : s = s' := sgn_injective (by linarith)
  have ht' : t = t' := sgn_injective (by linarith)
  rw [hs', ht']

@[irreducible] noncomputable def fam₁Fin : Finset (Fin 24 → ℤ) := fam₁Dom.image fam₁Param

theorem card_fam₁Fin : fam₁Fin.card = 1104 := by
  unfold fam₁Fin
  rw [Finset.card_image_of_injOn fam₁Param_injOn, card_fam₁Dom]

theorem coe_fam₁Fin : (fam₁Fin : Set (Fin 24 → ℤ)) = minFamily₁ := by
  unfold fam₁Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.1.1 < p.1.2 := mem_fam₁Dom.1 (Finset.mem_coe.1 hp)
    refine ⟨?_, fun k hk => ?_⟩
    · have : (Finset.univ.filter fun k => fam₁Param p k ≠ 0) = {p.1.1, p.1.2} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        exact fam₁Param_ne_zero_iff hp' k
      rw [this, Finset.card_pair (ne_of_lt hp')]
    · have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp'
      rcases (fam₁Param_ne_zero_iff hp' k).1 hk with rfl | rfl
      · simp only [fam₁Param, ite_true, hne, ite_false, add_zero, sgn]
        split_ifs <;> norm_num
      · simp only [fam₁Param, Ne.symm hne, ite_false, ite_true, zero_add, sgn]
        split_ifs <;> norm_num
  · rintro ⟨hcard, hval⟩
    obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.1 hcard
    have hmem : ∀ k, u k ≠ 0 ↔ k = a ∨ k = b := fun k => by
      have := congrArg (k ∈ ·) hS
      simpa using this
    obtain ⟨i, j, hij, hsupp⟩ : ∃ i j : Fin 24, i < j ∧ ∀ k, u k ≠ 0 ↔ k = i ∨ k = j := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, h, hmem⟩
      · exact ⟨b, a, h, fun k => (hmem k).trans or_comm⟩
    refine ⟨((i, j), (decide (u i = -4), decide (u j = -4))), ?_, ?_⟩
    · exact Finset.mem_coe.2 (mem_fam₁Dom.2 hij)
    · funext k
      have hne : i ≠ j := ne_of_lt hij
      by_cases hk1 : k = i
      · subst hk1
        simp only [fam₁Param, ite_true, hne, ite_false, add_zero, sgn]
        rcases hval k ((hsupp k).2 (Or.inl rfl)) with h | h <;> rw [h] <;> norm_num
      · by_cases hk2 : k = j
        · subst hk2
          simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, sgn]
          rcases hval k ((hsupp k).2 (Or.inr rfl)) with h | h <;> rw [h] <;> norm_num
        · simp only [fam₁Param, hk1, hk2, ite_false, add_zero]
          by_contra h
          rcases (hsupp k).1 (Ne.symm h) with h' | h'
          · exact hk1 h'
          · exact hk2 h'

@[irreducible] noncomputable def CFin : Finset (Fin 24 → ZMod 2) := Finset.univ.filter (· ∈ C)

theorem mem_CFin {d : Fin 24 → ZMod 2} : d ∈ CFin ↔ d ∈ C := by
  unfold CFin
  rw [Finset.mem_filter]
  simp

theorem card_CFin : CFin.card = 4096 := by
  unfold CFin
  rw [Finset.card_eq_sum_ones, sum_C]
  simp

@[irreducible] noncomputable def fam₃Dom : Finset (Fin 24 × (Fin 24 → ZMod 2)) :=
  Finset.univ ×ˢ CFin

theorem mem_fam₃Dom {p : Fin 24 × (Fin 24 → ZMod 2)} : p ∈ fam₃Dom ↔ p.2 ∈ C := by
  unfold fam₃Dom
  rw [Finset.mem_product, mem_CFin]
  simp

theorem card_fam₃Dom : fam₃Dom.card = 98304 := by
  unfold fam₃Dom
  rw [Finset.card_product, card_CFin, Finset.card_univ, Fintype.card_fin]

theorem oddMin_injective :
    Function.Injective fun p : Fin 24 × (Fin 24 → ZMod 2) => oddMin p.1 p.2 := by
  rintro ⟨i, d⟩ ⟨i', d'⟩ h
  simp only at h
  have hval : ∀ j, oddMin i d j = (1 - 2 * bitLift (d j)) * (1 - 4 * if j = i then 1 else 0) :=
    fun j => by rw [oddMin, neg_one_pow_val]
  have hval' : ∀ j, oddMin i' d' j =
      (1 - 2 * bitLift (d' j)) * (1 - 4 * if j = i' then 1 else 0) :=
    fun j => by rw [oddMin, neg_one_pow_val]
  have hii : i = i' := by
    by_contra hne
    have h1 := congrFun h i
    rw [hval, hval', if_pos rfl, if_neg hne] at h1
    rcases bitLift_zero_or_one (d i) with ha | ha <;>
      rcases bitLift_zero_or_one (d' i) with hb | hb <;> rw [ha, hb] at h1 <;> norm_num at h1
  subst hii
  have hdd : d = d' := by
    funext j
    have h1 := congrFun h j
    rw [hval, hval'] at h1
    have hb : bitLift (d j) = bitLift (d' j) := by
      rcases bitLift_zero_or_one (d j) with ha | ha <;>
        rcases bitLift_zero_or_one (d' j) with hb | hb <;> rw [ha, hb] at h1 ⊢ <;>
        split_ifs at h1 <;> norm_num at h1
    rcases zmod2_cases (d j) with ha | ha <;> rcases zmod2_cases (d' j) with hb' | hb' <;>
      rw [ha, hb'] at hb ⊢ <;> first | rfl | exact absurd hb (by decide)
  rw [hdd]

@[irreducible] noncomputable def fam₃Fin : Finset (Fin 24 → ℤ) :=
  fam₃Dom.image fun p => oddMin p.1 p.2

theorem card_fam₃Fin : fam₃Fin.card = 98304 := by
  unfold fam₃Fin
  rw [Finset.card_image_of_injective _ oddMin_injective, card_fam₃Dom]

theorem coe_fam₃Fin : (fam₃Fin : Set (Fin 24 → ℤ)) = minFamily₃ := by
  unfold fam₃Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨⟨i, d⟩, hp, rfl⟩
    exact ⟨i, d, mem_fam₃Dom.1 (Finset.mem_coe.1 hp), rfl⟩
  · rintro ⟨i, d, hd, rfl⟩
    exact ⟨(i, d), Finset.mem_coe.2 (mem_fam₃Dom.2 hd), rfl⟩

def suppFin (d : Fin 24 → ZMod 2) : Finset (Fin 24) := Finset.univ.filter (d · ≠ 0)

theorem mem_suppFin {d : Fin 24 → ZMod 2} {i : Fin 24} : i ∈ suppFin d ↔ d i ≠ 0 := by
  simp [suppFin]

def fam₂Vec (d : Fin 24 → ZMod 2) (T : Finset (Fin 24)) : Fin 24 → ℤ :=
  fun i => if d i = 0 then 0 else if i ∈ T then -2 else 2

@[irreducible] noncomputable def octFin : Finset (Fin 24 → ZMod 2) :=
  CFin.filter (hammingNorm · = 8)

theorem mem_octFin {d : Fin 24 → ZMod 2} : d ∈ octFin ↔ d ∈ C ∧ hammingNorm d = 8 := by
  unfold octFin
  rw [Finset.mem_filter, mem_CFin]

theorem card_octFin : octFin.card = 759 := by
  unfold octFin CFin
  rw [card_filter_wt, wtCount_eight]

@[irreducible] noncomputable def fam₂Dom : Finset (Σ _ : Fin 24 → ZMod 2, Finset (Fin 24)) :=
  octFin.sigma fun d => (suppFin d).powerset.filter fun T => Even T.card

theorem mem_fam₂Dom {p : Σ _ : Fin 24 → ZMod 2, Finset (Fin 24)} :
    p ∈ fam₂Dom ↔ (p.1 ∈ C ∧ hammingNorm p.1 = 8) ∧ p.2 ⊆ suppFin p.1 ∧ Even p.2.card := by
  unfold fam₂Dom
  rw [Finset.mem_sigma, mem_octFin, Finset.mem_filter, Finset.mem_powerset]

theorem card_even_subsets {α : Type*} [DecidableEq α] (s : Finset α) (hs : s.card = 8) :
    (s.powerset.filter fun T => Even T.card).card = 128 := by
  have hne : s.Nonempty := Finset.card_pos.1 (by rw [hs]; norm_num)
  have h0 := Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun T => Even T.card)] at h0
  have he : ∑ T ∈ s.powerset.filter (fun T => Even T.card), (-1 : ℤ) ^ T.card =
      (s.powerset.filter fun T => Even T.card).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Finset.mem_filter.1 hT).2.neg_one_pow]; rfl
  have ho : ∑ T ∈ s.powerset.filter (fun T => ¬Even T.card), (-1 : ℤ) ^ T.card =
      -(s.powerset.filter fun T => ¬Even T.card).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun T hT => by
      rw [(Nat.not_even_iff_odd.1 (Finset.mem_filter.1 hT).2).neg_one_pow]; rfl
  rw [he, ho] at h0
  have htot := Finset.card_filter_add_card_filter_not (s := s.powerset) (fun T => Even T.card)
  rw [Finset.card_powerset, hs] at htot
  have : ((s.powerset.filter fun T => Even T.card).card : ℤ) = 128 := by
    have h' : ((s.powerset.filter fun T => Even T.card).card : ℤ) +
        (s.powerset.filter fun T => ¬Even T.card).card = 256 := by exact_mod_cast htot
    linarith
  exact_mod_cast this

theorem card_fam₂Dom : fam₂Dom.card = 97152 := by
  unfold fam₂Dom
  rw [Finset.card_sigma]
  have : ∀ d ∈ octFin, ((suppFin d).powerset.filter fun T => Even T.card).card = 128 := by
    intro d hd
    apply card_even_subsets
    rw [suppFin, ← hammingNorm]
    exact (mem_octFin.1 hd).2
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_octFin, smul_eq_mul]

theorem fam₂Vec_injOn :
    Set.InjOn (fun p : Σ _ : Fin 24 → ZMod 2, Finset (Fin 24) => fam₂Vec p.1 p.2) fam₂Dom := by
  rintro ⟨d, T⟩ hp ⟨d', T'⟩ hq h
  have hp' := mem_fam₂Dom.1 (Finset.mem_coe.1 hp)
  have hq' := mem_fam₂Dom.1 (Finset.mem_coe.1 hq)
  simp only at h hp' hq'
  have hdd : d = d' := by
    funext i
    have h1 := congrFun h i
    simp only [fam₂Vec] at h1
    rcases zmod2_cases (d i) with ha | ha <;> rcases zmod2_cases (d' i) with hb | hb <;>
      rw [ha, hb] at h1 ⊢ <;> first | rfl | (simp at h1; split_ifs at h1; norm_num at h1)
  subst hdd
  have hTT : T = T' := by
    ext i
    have h1 := congrFun h i
    simp only [fam₂Vec] at h1
    have hT : i ∈ T → d i ≠ 0 := fun hi => mem_suppFin.1 (hp'.2.1 hi)
    have hT' : i ∈ T' → d i ≠ 0 := fun hi => mem_suppFin.1 (hq'.2.1 hi)
    by_cases hd : d i = 0
    · exact ⟨fun hi => absurd hd (hT hi), fun hi => absurd hd (hT' hi)⟩
    · simp only [hd, ite_false] at h1
      by_cases h2 : i ∈ T <;> by_cases h3 : i ∈ T' <;>
        simp only [h2, h3, ite_true, ite_false] at h1 <;>
        first | exact iff_of_true h2 h3 | exact iff_of_false h2 h3 | norm_num at h1
  rw [hTT]

@[irreducible] noncomputable def fam₂Fin : Finset (Fin 24 → ℤ) :=
  fam₂Dom.image fun p => fam₂Vec p.1 p.2

theorem card_fam₂Fin : fam₂Fin.card = 97152 := by
  unfold fam₂Fin
  rw [Finset.card_image_of_injOn fam₂Vec_injOn, card_fam₂Dom]

theorem coe_fam₂Fin : (fam₂Fin : Set (Fin 24 → ℤ)) = minFamily₂ := by
  unfold fam₂Fin
  rw [Finset.coe_image]
  ext u
  constructor
  · rintro ⟨⟨d, T⟩, hp, rfl⟩
    obtain ⟨⟨hd, hwt⟩, hTsub, hTeven⟩ := mem_fam₂Dom.1 (Finset.mem_coe.1 hp)
    refine ⟨d, hd, hwt, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simp only [fam₂Vec, hi, ite_false]
      split_ifs <;> norm_num
    · simp [fam₂Vec, hi]
    · have : (Finset.univ.filter fun i => fam₂Vec d T i = -2) = T := by
        ext i
        rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and]
        constructor
        · intro h
          by_contra hiT
          simp only [fam₂Vec, hiT, ite_false] at h
          split_ifs at h
        · intro hi
          have hdi : d i ≠ 0 := mem_suppFin.1 (hTsub hi)
          simp [fam₂Vec, hdi, hi]
      simp only at this ⊢
      rw [this]
      exact hTeven
  · rintro ⟨d, hd, hwt, hon, hoff, heven⟩
    refine ⟨⟨d, Finset.univ.filter fun i => u i = -2⟩, Finset.mem_coe.2 (mem_fam₂Dom.2
      ⟨⟨hd, hwt⟩, fun i hi => ?_, heven⟩), ?_⟩
    · rw [Finset.mem_filter] at hi
      rw [mem_suppFin]
      intro h0
      rw [hoff i h0] at hi
      norm_num at hi
    · funext i
      simp only [fam₂Vec, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h0 : d i = 0
      · simp [h0, hoff i h0]
      · simp only [h0, ite_false]
        rcases hon i h0 with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num

@[irreducible] noncomputable def minFin : Finset (Fin 24 → ℤ) := fam₁Fin ∪ fam₂Fin ∪ fam₃Fin

theorem coe_minFin : (minFin : Set (Fin 24 → ℤ)) = minVecs := by
  unfold minFin
  rw [Finset.coe_union, Finset.coe_union, coe_fam₁Fin, coe_fam₂Fin, coe_fam₃Fin, minVecs_eq]

theorem mem_minFin {u : Fin 24 → ℤ} : u ∈ minFin ↔ u ∈ minVecs := by
  rw [← Finset.mem_coe, coe_minFin]

/-- ⭐ **The Leech lattice has `196560` minimal vectors.** -/
theorem card_minFin : minFin.card = 196560 := by
  unfold minFin
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_fam₁Fin,
    card_fam₂Fin, card_fam₃Fin]
  · rw [← Finset.disjoint_coe, coe_fam₁Fin, coe_fam₂Fin]
    exact disjoint_minFamily₁₂
  · rw [← Finset.disjoint_coe, Finset.coe_union, coe_fam₁Fin, coe_fam₂Fin, coe_fam₃Fin]
    exact Disjoint.union_left disjoint_minFamily₁₃ disjoint_minFamily₂₃

def posFirst (u : Fin 24 → ℤ) : Prop := ∃ i, 0 < u i ∧ ∀ j, j < i → u j = 0

theorem posFirst_xor {u : Fin 24 → ℤ} (h0 : u ≠ 0) : (posFirst u ↔ ¬posFirst (-u)) := by
  classical
  constructor
  · rintro ⟨i, hi, hj⟩ ⟨i', hi', hj'⟩
    simp only [Pi.neg_apply, neg_pos] at hi'
    have hj'' : ∀ j, j < i' → u j = 0 := fun j hj => by
      have := hj' j hj
      simpa using this
    rcases lt_trichotomy i i' with h | h | h
    · have := hj'' i h; omega
    · subst h; omega
    · have := hj i' h; omega
  · intro hn
    have hex : (Finset.univ.filter fun i => u i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
    set i₀ := (Finset.univ.filter fun i => u i ≠ 0).min' hex
    have hi₀ : u i₀ ≠ 0 := (Finset.mem_filter.1 (Finset.min'_mem _ hex)).2
    have hlt : ∀ j, j < i₀ → u j = 0 := fun j hj => by
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hne⟩))
        (not_le.2 hj)
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · exact absurd ⟨i₀, by simp [hneg], fun j hj => by simp [hlt j hj]⟩ hn
    · exact ⟨i₀, hpos, hlt⟩

def minHalf : Set (Fin 24 → ℤ) := {u | u ∈ minVecs ∧ posFirst u}

theorem minVecs_finite : minVecs.Finite := by
  rw [← coe_minFin]
  exact Finset.finite_toSet _

theorem ncard_minVecs : minVecs.ncard = 196560 := by
  rw [← coe_minFin, Set.ncard_coe_finset, card_minFin]

theorem minVecs_eq_half_union : minVecs = minHalf ∪ Neg.neg '' minHalf := by
  ext v
  constructor
  · intro hv
    by_cases hp : posFirst v
    · exact Or.inl ⟨hv, hp⟩
    · refine Or.inr ⟨-v, ⟨neg_mem_minVecs hv, ?_⟩, neg_neg v⟩
      by_contra h
      exact hp ((posFirst_xor (minVecs_ne_zero hv)).2 h)
  · rintro (⟨hv, -⟩ | ⟨u, ⟨hu, -⟩, rfl⟩)
    · exact hv
    · exact neg_mem_minVecs hu

theorem disjoint_minHalf : Disjoint minHalf (Neg.neg '' minHalf) := by
  rw [Set.disjoint_left]
  rintro v ⟨hv, hpv⟩ ⟨u, ⟨hu, hpu⟩, rfl⟩
  exact (posFirst_xor (minVecs_ne_zero hu)).1 hpu hpv

theorem ncard_minHalf : minHalf.ncard = 98280 := by
  have hfin : minHalf.Finite := minVecs_finite.subset fun u hu => hu.1
  have h := Set.ncard_union_eq disjoint_minHalf hfin (hfin.image _)
  rw [← minVecs_eq_half_union, neg_injective.injOn.ncard_image, ncard_minVecs] at h
  generalize minHalf.ncard = a at h ⊢
  omega

theorem card_classes :
    {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c}.ncard = 98280 := by
  have hS : {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c} =
      classOf '' minHalf := by
    ext c
    constructor
    · rintro ⟨u, hu, rfl⟩
      by_cases hp : posFirst u
      · exact ⟨u, ⟨hu, hp⟩, rfl⟩
      · have hn := neg_mem_minVecs hu
        refine ⟨-u, ⟨hn, ?_⟩, ?_⟩
        · by_contra h
          exact hp ((posFirst_xor (minVecs_ne_zero hu)).2 h)
        · exact ((classOf_eq_iff hu hn).2 (Or.inr rfl)).symm
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, rfl⟩
  have hinj : Set.InjOn classOf minHalf := by
    rintro u ⟨hu1, hu2⟩ v ⟨hv1, hv2⟩ huv
    rcases (classOf_eq_iff hu1 hv1).1 huv with h | h
    · exact h.symm
    · subst h
      exact absurd hv2 ((posFirst_xor (minVecs_ne_zero hu1)).1 hu2)
  rw [hS, hinj.ncard_image, ncard_minHalf]

end VOA.Moonshine.MonsterGriess.Code

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.SpinLattice

/-! ### From `CFSG/Monster/Griess/Short.lean` -/

/-- ⭐ **`98280` short coordinates** (`= 196560 / 2`). -/
theorem card_shortIdx : Nat.card ShortIdx = 98280 := by
  have e : ShortIdx ≃ {c : codeLatticeModTwo C allOnes_mem_C | ∃ u ∈ minVecs, classOf u = c} :=
    { toFun := fun p => ⟨phi0 p.1, p.2⟩
      invFun := fun c => ⟨phi0Equiv.symm c.1, by
        obtain ⟨u, hu, h⟩ := c.2
        exact ⟨u, hu, h.trans (phi0Equiv.apply_symm_apply c.1).symm⟩⟩
      left_inv := fun p => Subtype.ext (phi0Equiv.symm_apply_apply p.1)
      right_inv := fun c => Subtype.ext (phi0Equiv.apply_symm_apply c.1) }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, card_classes]

end VOA.Moonshine.MonsterGriess
