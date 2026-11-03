/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.GroundLatticeGolay

/-!
# The ground-state lattice residual in Golay coordinates

`Λ₀ ≅ A = Leech.subA = {x ∈ ℤ²⁴ : x mod 2 ∈ 𝒢, 4 ∣ Σxᵢ}` with `⟨x,y⟩ = x·y/2`.  In these
coordinates the residual `GroundLattice` (`ZhuGenGround.lean`) becomes `groundLatticeA`:

for every `g ∈ A` with `g·g ≥ 12` (`|γ|² ≥ 6`), either
* `Direct g`: `g = a + (g - a)` with `a, g - a ∈ A ∖ 0` and `a·(g-a) = -2` or `≥ 2`
  (`⟨α,β⟩ = -1` or `≥ 1`), or
* `Tri g`: a triangle `g → g' → g'' → g` of `ZeroRel` steps, `ZeroRel u v` meaning
  `u = a + b`, `v = a - b`, `a, b ∈ A ∖ 0`, `a·b = 0` (the `k = 0` relations
  `x_u + x_v`).

## Proof
* `direct_of_pair`: `a = 2(±eᵢ ± eⱼ)` gives `a·g = 2(|gᵢ| + |gⱼ|)`, so `Direct g` as soon as
  `|gᵢ| + |gⱼ| = 3` or `≥ 5` for some `i ≠ j`.
* Otherwise the shape is forced (`shape_of_noPair`): all coordinates odd, or `±4eᵢ`, or all
  `|gⱼ| ∈ {0,2}`, or all `|gⱼ| ≤ 1`.
* **Octad vectors** `octVec O σ` (`±1` on an octad `O`, sign parity fixed at one point `p`):
  `a·g = σ_p g_p + Σ_{O∖p} |gⱼ|`.
* `|gⱼ| ∈ {0,2}`, support `S` (`|S|` even `≥ 4`): an octad meeting `S` in `3` (`|S| = 4`,
  `exists_octad_inter_three`) or in `≥ 5` points (`steiner`).
* `|gⱼ| ≤ 1`, support a codeword of weight `12` or `16`: an octad meeting it in `6` points
  (`exists_octad_inter_six`).
* **All coordinates odd** (this contains the exceptional families `(±1)²⁴` and
  `(±3,±1²³)` uniformly): let `τ = {j : gⱼ ≡ 3 mod 4}`.
  - `τ ∉ 𝒢`: an octad `O` with `|O ∩ τ|` odd (`exists_octad_dot_ne_zero`); then `a·g ≡ 2 mod 4`
    and `a·g ≥ 6`, so `a·g = 6` or `≥ 10` (`odd_direct`).
  - `τ ∈ 𝒢`: flipping the signs of `g` on any codeword `A ∉ {∅, Ω}` is a `ZeroRel` step
    (`zeroRel_flip`); three codewords `A₁, A₂, A₁ Δ A₂` give the triangle.
* `±4eᵢ` (`E1`): the triangle `4eᵢ → 4eⱼ → 4eₖ` with `a, b = 2(eᵢ ± eⱼ)`.

## Status
`sorry`-free, no project axiom; only small kernel `decide`s (on `Fin 24`, `ZMod 2`, and the
values of two encoder rows).
-/

namespace VOA.Moonshine.GroundLat

open Code Finset Leech

/-! ## §1  The statement -/

/-- A **direct** ground relation for `g`: `g = a + (g - a)` with `a·(g-a) = -2` or `≥ 2`. -/
def Direct (g : Fin 24 → ℤ) : Prop :=
  ∃ a ∈ subA, a ≠ 0 ∧ g - a ≠ 0 ∧ (a ⬝ᵥ (g - a) = -2 ∨ 2 ≤ a ⬝ᵥ (g - a))

/-- A `k = 0` relation step: `u = a + b`, `v = a - b`, `a ⊥ b`. -/
def ZeroRel (u v : Fin 24 → ℤ) : Prop :=
  ∃ a ∈ subA, ∃ b ∈ subA, a ≠ 0 ∧ b ≠ 0 ∧ a ⬝ᵥ b = 0 ∧ a + b = u ∧ a - b = v

/-- A triangle of `k = 0` relation steps through `g`. -/
def Tri (g : Fin 24 → ℤ) : Prop :=
  ∃ g' g'', ZeroRel g g' ∧ ZeroRel g' g'' ∧ ZeroRel g'' g

/-! ## §2  Generic constructions -/

theorem direct_of {g a : Fin 24 → ℤ} (ha : a ∈ subA) (haa : a ⬝ᵥ a = 8) (hg : 12 ≤ g ⬝ᵥ g)
    (h : a ⬝ᵥ g = 6 ∨ 10 ≤ a ⬝ᵥ g) : Direct g := by
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · rintro rfl; simp at haa
  · intro h0
    rw [sub_eq_zero] at h0
    subst h0
    omega
  · rw [dotProduct_sub, haa]
    omega

/-- The sign `±1` of an integer (`+1` at `0`). -/
def sg (x : ℤ) : ℤ := if x < 0 then -1 else 1

theorem sg_mul (x : ℤ) : sg x * x = |x| := by
  unfold sg; split_ifs with h
  · rw [abs_of_neg h]; ring
  · rw [abs_of_nonneg (not_lt.1 h)]; ring

theorem sg_cases (x : ℤ) : sg x = 1 ∨ sg x = -1 := by
  unfold sg; split_ifs <;> simp

theorem pairVec_mem {i j : Fin 24} (_hij : i ≠ j) {x y : ℤ} (hx : x = 2 ∨ x = -2)
    (hy : y = 2 ∨ y = -2) : Pi.single i x + Pi.single j y ∈ subA := by
  rw [mem_subA, mem_preG]
  refine ⟨?_, ?_⟩
  · have hev : ∀ k, (2 : ℤ) ∣ (Pi.single i x + Pi.single j y : Fin 24 → ℤ) k := by
      intro k
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs <;> omega
    have : reduceMod 2 24 (Pi.single i x + Pi.single j y) = 0 := by
      funext k
      rw [reduceMod_apply, Pi.zero_apply]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (hev k)
    rw [this]
    exact golay.zero_mem
  · simp only [Pi.add_apply]
    rw [sum_add_distrib, sum_pi_single', sum_pi_single']
    simp only [mem_univ, if_true]
    omega

theorem pairVec_dot (i j : Fin 24) (x y : ℤ) (v : Fin 24 → ℤ) :
    (Pi.single i x + Pi.single j y) ⬝ᵥ v = x * v i + y * v j := by
  rw [add_dotProduct, single_dotProduct, single_dotProduct]

/-- Pair construction: `|gᵢ| + |gⱼ| = 3` or `≥ 5` gives a direct relation. -/
theorem direct_of_pair {g : Fin 24 → ℤ} (hg : 12 ≤ g ⬝ᵥ g) {i j : Fin 24} (hij : i ≠ j)
    (h : |g i| + |g j| = 3 ∨ 5 ≤ |g i| + |g j|) : Direct g := by
  have hx : 2 * sg (g i) = 2 ∨ 2 * sg (g i) = -2 := by rcases sg_cases (g i) with h | h <;> simp [h]
  have hy : 2 * sg (g j) = 2 ∨ 2 * sg (g j) = -2 := by rcases sg_cases (g j) with h | h <;> simp [h]
  refine direct_of (pairVec_mem hij hx hy) ?_ hg ?_
  · rw [pairVec_dot i j]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
    rcases sg_cases (g i) with h1 | h1 <;> rcases sg_cases (g j) with h2 | h2 <;>
      simp [h1, h2]
  · rw [pairVec_dot i j, mul_assoc, mul_assoc, sg_mul, sg_mul]
    omega

/-! ## §3  Sums of signs -/

theorem sum_sign {s : Finset (Fin 24)} {f : Fin 24 → ℤ} (hf : ∀ j ∈ s, f j = 1 ∨ f j = -1) :
    ∑ j ∈ s, f j + 2 * ((s.filter fun j => f j = -1).card : ℤ) = s.card := by
  have : ∀ j ∈ s, f j = 1 - 2 * (if f j = -1 then (1 : ℤ) else 0) := by
    intro j hj
    rcases hf j hj with h | h <;> simp [h]
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, nsmul_eq_mul, mul_one]
  ring

/-! ## §4  Octad vectors -/

/-- The vector `σ` on the octad `O`, `0` off it. -/
def octVec (O : Finset (Fin 24)) (σ : Fin 24 → ℤ) : Fin 24 → ℤ := fun j => if j ∈ O then σ j else 0

theorem octVec_dot (O : Finset (Fin 24)) (σ g : Fin 24 → ℤ) :
    octVec O σ ⬝ᵥ g = ∑ j ∈ O, σ j * g j := by
  simp only [dotProduct, octVec, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter]

theorem octVec_self {O : Finset (Fin 24)} (hO : IsOct O) {σ : Fin 24 → ℤ}
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) : octVec O σ ⬝ᵥ octVec O σ = 8 := by
  rw [octVec_dot]
  have : ∀ j ∈ O, σ j * octVec O σ j = 1 := by
    intro j hj
    simp only [octVec, hj, if_true]
    rcases hσ j with h | h <;> simp [h]
  rw [sum_congr rfl this, sum_const, hO.2]
  rfl

theorem octVec_mem {O : Finset (Fin 24)} (hO : IsOct O) {σ : Fin 24 → ℤ}
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (h4 : 4 ∣ ∑ j ∈ O, σ j) : octVec O σ ∈ subA := by
  rw [mem_subA, mem_preG]
  refine ⟨?_, ?_⟩
  · have : reduceMod 2 24 (octVec O σ) = ind O := by
      funext k
      simp only [reduceMod_apply, octVec, ind]
      split_ifs
      · rcases hσ k with h | h <;> rw [h] <;> decide
      · simp
    rw [this]
    exact hO.1
  · have : ∑ i, octVec O σ i = ∑ j ∈ O, σ j := by
      simp only [octVec]
      rw [sum_ite_mem, univ_inter]
    rw [this]
    exact h4

/-- Fix the sign parity at one point `p ∈ O`. -/
theorem exists_eps {O : Finset (Fin 24)} (hO : O.card = 8) {σ : Fin 24 → ℤ}
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1) {p : Fin 24} (hp : p ∈ O) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ 4 ∣ ∑ j ∈ O, Function.update σ p ε j := by
  have hsplit : ∀ ε : ℤ, ∑ j ∈ O, Function.update σ p ε j = ε + ∑ j ∈ O.erase p, σ j := by
    intro ε
    rw [← add_sum_erase O _ hp, Function.update_self]
    congr 1
    exact sum_congr rfl fun j hj => Function.update_of_ne (ne_of_mem_erase hj) _ _
  have hs := sum_sign (s := O.erase p) (f := σ) (fun j _ => hσ j)
  rw [card_erase_of_mem hp, hO] at hs
  by_cases h : (4 : ℤ) ∣ 1 + ∑ j ∈ O.erase p, σ j
  · exact ⟨1, Or.inl rfl, by rw [hsplit]; exact h⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [hsplit]
    push_cast at hs
    omega

theorem update_sign {σ : Fin 24 → ℤ} (hσ : ∀ j, σ j = 1 ∨ σ j = -1) {p : Fin 24} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : ∀ j, Function.update σ p ε j = 1 ∨ Function.update σ p ε j = -1 := by
  intro j
  by_cases h : j = p
  · subst h; rw [Function.update_self]; exact hε
  · rw [Function.update_of_ne h]; exact hσ j

/-- The octad-vector construction: for an octad `O ∋ p` there is a sign vector `σ`, equal to
`sgn gⱼ` on `O ∖ p`, with `a = octVec O σ ∈ A`, `a·a = 8` and `a·g = σ_p g_p + Σ_{O∖p} |gⱼ|`. -/
theorem exists_octVec {O : Finset (Fin 24)} (hO : IsOct O) (g : Fin 24 → ℤ) {p : Fin 24}
    (hp : p ∈ O) : ∃ σ : Fin 24 → ℤ, (∀ j, σ j = 1 ∨ σ j = -1) ∧ 4 ∣ ∑ j ∈ O, σ j ∧
      octVec O σ ∈ subA ∧ octVec O σ ⬝ᵥ octVec O σ = 8 ∧
      octVec O σ ⬝ᵥ g = σ p * g p + ∑ j ∈ O.erase p, |g j| := by
  obtain ⟨ε, hε, h4⟩ := exists_eps hO.2 (σ := fun k => sg (g k)) (fun k => sg_cases _) hp
  have hσ := update_sign (σ := fun k => sg (g k)) (fun k => sg_cases _) hε (p := p)
  refine ⟨_, hσ, h4, octVec_mem hO hσ h4, octVec_self hO hσ, ?_⟩
  rw [octVec_dot, ← add_sum_erase O _ hp]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hj), sg_mul]

theorem sign_mul_ge (σp x : ℤ) (h : σp = 1 ∨ σp = -1) : -|x| ≤ σp * x := by
  rcases h with rfl | rfl
  · simp [neg_abs_le]
  · simp [le_abs_self]

theorem sum_abs_eq {s S : Finset (Fin 24)} {g : Fin 24 → ℤ} {m : ℤ}
    (hg : ∀ j, |g j| = if j ∈ S then m else 0) : ∑ j ∈ s, |g j| = m * (s ∩ S).card := by
  rw [sum_congr rfl fun j _ => hg j, ← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter]
  ring

theorem exists_mem_not_mem_of_inter_lt {O S : Finset (Fin 24)} (hO : IsOct O)
    (h : (O ∩ S).card < 8) : ∃ p ∈ O, p ∉ S := by
  by_contra hc
  push Not at hc
  have : O ∩ S = O := inter_eq_left.2 hc
  rw [this, hO.2] at h
  omega

/-! ## §5  Even coordinates `0, ±2` -/

theorem direct_even2 {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hg : 12 ≤ g ⬝ᵥ g)
    (h02 : ∀ j, |g j| = 0 ∨ |g j| = 2) : Direct g := by
  classical
  set S := univ.filter (fun j => g j ≠ 0) with hS
  have habs : ∀ j, |g j| = if j ∈ S then 2 else 0 := by
    intro j
    simp only [hS, mem_filter, mem_univ, true_and]
    split_ifs with h
    · rcases h02 j with h' | h'
      · exact absurd (abs_eq_zero.1 h') h
      · exact h'
    · rw [not_not.1 h, abs_zero]
  have hgg : g ⬝ᵥ g = 4 * S.card := by
    have : ∀ j ∈ (univ : Finset (Fin 24)), g j * g j = 2 * |g j| := by
      intro j _
      rw [← abs_mul_abs_self]
      rcases h02 j with h | h <;> rw [h] <;> norm_num
    rw [dotProduct, sum_congr rfl this, ← mul_sum, sum_abs_eq habs, univ_inter]
    ring
  have hsum : ∑ j, g j = 2 * ∑ j ∈ S, sg (g j) := by
    rw [← sum_subset (subset_univ S) (fun j _ hj => by
      simp only [hS, mem_filter, mem_univ, true_and, not_not] at hj; exact hj), mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have h2 : |g j| = 2 := by rw [habs j, if_pos hj]
    unfold sg
    split_ifs with hn
    · rw [abs_of_neg hn] at h2; omega
    · rw [abs_of_nonneg (not_lt.1 hn)] at h2; omega
  have hsg := sum_sign (s := S) (f := fun j => sg (g j)) (fun j _ => sg_cases _)
  simp only at hsg
  have h4 : (4 : ℤ) ∣ ∑ j, g j := hgA.2
  rw [hsum] at h4
  have hS3 : 3 ≤ S.card := by omega
  have hSeven : S.card % 2 = 0 := by omega
  rcases (show S.card = 4 ∨ 5 ≤ S.card by omega) with h4' | h5
  · obtain ⟨O, hO, h3⟩ := exists_octad_inter_three h4'
    obtain ⟨p, hp, hpS⟩ := exists_mem_not_mem_of_inter_lt (S := S) hO (by omega)
    obtain ⟨σ, -, -, ha, haa, hdot⟩ := exists_octVec hO g hp
    refine direct_of ha haa hg (Or.inl ?_)
    have hgp : g p = 0 := abs_eq_zero.1 (by rw [habs p, if_neg hpS])
    rw [hdot, hgp, mul_zero, zero_add, sum_abs_eq habs, erase_inter,
      erase_eq_of_notMem (fun h => hpS (mem_inter.1 h).2), h3]
    norm_num
  · obtain ⟨O, hO, h5'⟩ := exists_octad_inter_ge_five h5
    by_cases hout : ∃ p ∈ O, p ∉ S
    · obtain ⟨p, hp, hpS⟩ := hout
      obtain ⟨σ, -, -, ha, haa, hdot⟩ := exists_octVec hO g hp
      refine direct_of ha haa hg (Or.inr ?_)
      have hgp : g p = 0 := abs_eq_zero.1 (by rw [habs p, if_neg hpS])
      rw [hdot, hgp, mul_zero, zero_add, sum_abs_eq habs, erase_inter,
        erase_eq_of_notMem (fun h => hpS (mem_inter.1 h).2)]
      omega
    · push Not at hout
      obtain ⟨p, hp⟩ : O.Nonempty := by rw [← card_pos, hO.2]; omega
      obtain ⟨σ, hσ, -, ha, haa, hdot⟩ := exists_octVec hO g hp
      refine direct_of ha haa hg (Or.inr ?_)
      have hgp : |g p| = 2 := by rw [habs p, if_pos (hout p hp)]
      have hlow := sign_mul_ge (σ p) (g p) (hσ p)
      have h7 : (O.erase p ∩ S).card = 7 := by
        rw [inter_eq_left.2 (fun j hj => hout j (mem_of_mem_erase hj)), card_erase_of_mem hp, hO.2]
      rw [hdot, sum_abs_eq habs, h7]
      omega

/-! ## §6  Coordinates `0, ±1` -/

theorem direct_le_one {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hg : 12 ≤ g ⬝ᵥ g)
    (h1 : ∀ j, |g j| ≤ 1) {j₀ : Fin 24} (hj₀ : g j₀ = 0) : Direct g := by
  classical
  set S := univ.filter (fun j => g j ≠ 0) with hS
  have hval : ∀ j, g j = -1 ∨ g j = 0 ∨ g j = 1 := by
    intro j
    have := abs_le.1 (h1 j)
    omega
  have habs : ∀ j, |g j| = if j ∈ S then 1 else 0 := by
    intro j
    simp only [hS, mem_filter, mem_univ, true_and]
    rcases hval j with h | h | h <;> simp [h]
  have hind : ind S = reduceMod 2 24 g := by
    funext j
    simp only [ind, reduceMod_apply, hS, mem_filter, mem_univ, true_and]
    rcases hval j with h | h | h <;> simp [h]
  have hSg : ind S ∈ golay := by rw [hind]; exact hgA.1
  have hgg : g ⬝ᵥ g = S.card := by
    have : ∀ j ∈ (univ : Finset (Fin 24)), g j * g j = |g j| := by
      intro j _
      rcases hval j with h | h | h <;> simp [h]
    rw [dotProduct, sum_congr rfl this, sum_abs_eq habs, univ_inter, one_mul]
  have hlt : S.card < 24 := by
    have hj : j₀ ∉ S := by simp [hS, hj₀]
    have := card_lt_univ_of_notMem hj
    rwa [Fintype.card_fin] at this
  have h1216 : S.card = 12 ∨ S.card = 16 := by
    rcases card_cases hSg with h | h | h | h | h <;> omega
  obtain ⟨O, hO, h6⟩ := exists_octad_inter_six hSg h1216
  obtain ⟨p, hp, hpS⟩ := exists_mem_not_mem_of_inter_lt (S := S) hO (by omega)
  obtain ⟨σ, -, -, ha, haa, hdot⟩ := exists_octVec hO g hp
  refine direct_of ha haa hg (Or.inl ?_)
  have hgp : g p = 0 := abs_eq_zero.1 (by rw [habs p, if_neg hpS])
  rw [hdot, hgp, mul_zero, zero_add, sum_abs_eq habs, erase_inter,
    erase_eq_of_notMem (fun h => hpS (mem_inter.1 h).2), h6]
  norm_num

/-! ## §7  All coordinates odd -/

/-- `τ(g) = {j : gⱼ ≡ 3 mod 4}`. -/
def tau (g : Fin 24 → ℤ) : Finset (Fin 24) := univ.filter (fun j => g j % 4 = 3)

theorem mod4_sum {g : Fin 24 → ℤ} (hodd : ∀ j, g j % 2 = 1) (s : Finset (Fin 24)) :
    (4 : ℤ) ∣ ∑ j ∈ s, g j - s.card - 2 * (s ∩ tau g).card := by
  have h : (4 : ℤ) ∣ ∑ j ∈ s, (g j - 1 - 2 * (if j ∈ tau g then (1 : ℤ) else 0)) := by
    refine dvd_sum fun j _ => ?_
    have := hodd j
    by_cases hj : g j % 4 = 3 <;> simp [tau, hj] <;> omega
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, nsmul_eq_mul, mul_one,
    filter_mem_eq_inter] at h
  exact h

theorem even_card_inter_of_mem {A B : Finset (Fin 24)} (hA : ind A ∈ golay) (hB : ind B ∈ golay) :
    Even (A ∩ B).card := by
  have h := (mem_dual.1 (golay_isSelfOrthogonal hB)) _ hA
  rw [ind_dot, ZMod.natCast_eq_zero_iff_even] at h
  exact h

theorem odd_direct {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hodd : ∀ j, g j % 2 = 1)
    (hτ : ind (tau g) ∉ golay) : Direct g := by
  have hone : ∀ j, 1 ≤ |g j| := fun j => Int.one_le_abs (by have := hodd j; omega)
  have hg : 12 ≤ g ⬝ᵥ g := by
    have : ∑ _j : Fin 24, (1 : ℤ) ≤ g ⬝ᵥ g := by
      refine sum_le_sum fun j _ => ?_
      rw [← abs_mul_abs_self]
      nlinarith [hone j]
    simp at this
    omega
  have hw : Even (weight (ind (tau g))) := by
    have h4 := mod4_sum hodd univ
    have h4' : (4 : ℤ) ∣ ∑ j, g j := hgA.2
    rw [weight_ind]
    rw [univ_inter, card_univ, Fintype.card_fin] at h4
    rw [Nat.even_iff]
    omega
  obtain ⟨O, hO, hdotO⟩ := exists_octad_dot_ne_zero hτ hw
  have hodd' : (O ∩ tau g).card % 2 = 1 := by
    rw [ind_dot, Ne, ZMod.natCast_eq_zero_iff_even, Nat.even_iff] at hdotO
    omega
  obtain ⟨p, hp, hmin⟩ := exists_min_image O (fun j => |g j|) (by rw [← card_pos, hO.2]; omega)
  obtain ⟨σ, hσ, hσ4, ha, haa, hdot⟩ := exists_octVec hO g hp
  refine direct_of ha haa hg ?_
  -- lower bound
  have hlow := sign_mul_ge (σ p) (g p) (hσ p)
  have hsum7 : (O.erase p).card • |g p| ≤ ∑ j ∈ O.erase p, |g j| :=
    card_nsmul_le_sum _ _ _ fun j hj => hmin j (mem_of_mem_erase hj)
  rw [card_erase_of_mem hp, hO.2, nsmul_eq_mul] at hsum7
  have hge : 6 ≤ octVec O σ ⬝ᵥ g := by
    rw [hdot]
    have := hone p
    push_cast at hsum7
    linarith
  -- congruence mod 4
  have hterm : (4 : ℤ) ∣ ∑ j ∈ O, (σ j * g j - σ j - g j + 1) := by
    refine dvd_sum fun j _ => ?_
    have := hodd j
    rcases hσ j with h | h <;> rw [h] <;> omega
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← octVec_dot, sum_const, hO.2] at hterm
  have hm := mod4_sum hodd O
  rw [hO.2] at hm
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hterm
  push_cast at hm
  omega

/-- Flip the signs of `g` on `A`. -/
def flip (A : Finset (Fin 24)) (g : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun j => if j ∈ A then -g j else g j

/-- Restrict `g` to `A`. -/
def restr (A : Finset (Fin 24)) (g : Fin 24 → ℤ) : Fin 24 → ℤ := fun j => if j ∈ A then g j else 0

theorem flip_odd {g : Fin 24 → ℤ} (hodd : ∀ j, g j % 2 = 1) (A : Finset (Fin 24)) :
    ∀ j, flip A g j % 2 = 1 := by
  intro j
  have := hodd j
  unfold flip
  split_ifs <;> omega

theorem tau_flip {g : Fin 24 → ℤ} (hodd : ∀ j, g j % 2 = 1) (A : Finset (Fin 24)) :
    tau (flip A g) = symmDiff (tau g) A := by
  ext j
  have := hodd j
  simp only [tau, flip, mem_filter, mem_univ, true_and, Finset.mem_symmDiff]
  by_cases hj : j ∈ A <;> (simp [hj]; try omega)

theorem restr_mem {g : Fin 24 → ℤ} (hodd : ∀ j, g j % 2 = 1) (hτ : ind (tau g) ∈ golay)
    {A : Finset (Fin 24)} (hA : ind A ∈ golay) : restr A g ∈ subA := by
  rw [mem_subA, mem_preG]
  refine ⟨?_, ?_⟩
  · have : reduceMod 2 24 (restr A g) = ind A := by
      funext k
      simp only [reduceMod_apply, restr, ind]
      split_ifs
      · rw [← ZMod.intCast_mod (g k) 2, show ((2 : ℕ) : ℤ) = 2 from rfl, hodd k, Int.cast_one]
      · simp
    rw [this]
    exact hA
  · have hs : ∑ i, restr A g i = ∑ j ∈ A, g j := by
      simp only [restr]
      rw [sum_ite_mem, univ_inter]
    rw [hs]
    have hm := mod4_sum hodd A
    have hev := even_card_inter_of_mem hA hτ
    have h4 : 4 ∣ A.card := by rcases card_cases hA with h | h | h | h | h <;> rw [h] <;> norm_num
    rw [Nat.even_iff] at hev
    omega

theorem flip_eq_sub (A : Finset (Fin 24)) (g : Fin 24 → ℤ) :
    flip A g = (g - restr A g) - restr A g := by
  funext j
  simp only [flip, restr, Pi.sub_apply]
  split_ifs <;> ring

theorem flip_mem {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hodd : ∀ j, g j % 2 = 1)
    (hτ : ind (tau g) ∈ golay) {A : Finset (Fin 24)} (hA : ind A ∈ golay) : flip A g ∈ subA := by
  have hb := restr_mem hodd hτ hA
  rw [flip_eq_sub]
  exact subA.sub_mem (subA.sub_mem hgA hb) hb

theorem tau_flip_mem {g : Fin 24 → ℤ} (hodd : ∀ j, g j % 2 = 1) (hτ : ind (tau g) ∈ golay)
    {A : Finset (Fin 24)} (hA : ind A ∈ golay) : ind (tau (flip A g)) ∈ golay := by
  rw [tau_flip hodd, ← ind_add]
  exact golay.add_mem hτ hA

/-- Flipping the signs on a codeword `A ∉ {∅, Ω}` is a `k = 0` step. -/
theorem zeroRel_flip {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hodd : ∀ j, g j % 2 = 1)
    (hτ : ind (tau g) ∈ golay) {A : Finset (Fin 24)} (hA : ind A ∈ golay) {i k : Fin 24}
    (hi : i ∈ A) (hk : k ∉ A) : ZeroRel g (flip A g) := by
  have hb := restr_mem hodd hτ hA
  refine ⟨g - restr A g, subA.sub_mem hgA hb, restr A g, hb, ?_, ?_, ?_, sub_add_cancel _ _,
    (flip_eq_sub A g).symm⟩
  · intro h
    have := congrFun h k
    simp only [Pi.sub_apply, restr, hk, if_false, sub_zero, Pi.zero_apply] at this
    have := hodd k
    omega
  · intro h
    have := congrFun h i
    simp only [restr, hi, if_true, Pi.zero_apply] at this
    have := hodd i
    omega
  · rw [dotProduct]
    refine sum_eq_zero fun j _ => ?_
    simp only [Pi.sub_apply, restr]
    split_ifs <;> ring

theorem flip_flip_flip (A₁ A₂ : Finset (Fin 24)) (g : Fin 24 → ℤ) :
    flip (symmDiff A₁ A₂) (flip A₂ (flip A₁ g)) = g := by
  funext j
  simp only [flip, Finset.mem_symmDiff]
  by_cases h1 : j ∈ A₁ <;> by_cases h2 : j ∈ A₂ <;> simp [h1, h2]

/-- Two explicit codewords: the first two rows of the generator matrix. -/
def A₁ : Finset (Fin 24) := support (golayEnc (Pi.single 0 1))
def A₂ : Finset (Fin 24) := support (golayEnc (Pi.single 1 1))

theorem ind_A₁ : ind A₁ ∈ golay := by rw [A₁, ind_support]; exact golayEnc_mem _
theorem ind_A₂ : ind A₂ ∈ golay := by rw [A₂, ind_support]; exact golayEnc_mem _

theorem mem_A₁ : (0 : Fin 24) ∈ A₁ ∧ (2 : Fin 24) ∉ A₁ ∧ (0 : Fin 24) ∉ A₂ ∧ (1 : Fin 24) ∈ A₂ ∧
    (2 : Fin 24) ∉ A₂ := by
  simp only [A₁, A₂, mem_support, Ne]
  decide

/-- All coordinates odd and `τ(g) ∈ 𝒢` (this contains `E2`, `E3`): a triangle. -/
theorem odd_tri {g : Fin 24 → ℤ} (hgA : g ∈ subA) (hodd : ∀ j, g j % 2 = 1)
    (hτ : ind (tau g) ∈ golay) : Tri g := by
  obtain ⟨h0, h2, h0', h1, h2'⟩ := mem_A₁
  have hA₃ : ind (symmDiff A₁ A₂) ∈ golay := by rw [← ind_add]; exact golay.add_mem ind_A₁ ind_A₂
  set g₁ := flip A₁ g
  set g₂ := flip A₂ g₁
  have hg₁ : g₁ ∈ subA := flip_mem hgA hodd hτ ind_A₁
  have ho₁ := flip_odd hodd A₁
  have hτ₁ : ind (tau g₁) ∈ golay := tau_flip_mem hodd hτ ind_A₁
  have hg₂ : g₂ ∈ subA := flip_mem hg₁ ho₁ hτ₁ ind_A₂
  have ho₂ := flip_odd ho₁ A₂
  have hτ₂ : ind (tau g₂) ∈ golay := tau_flip_mem ho₁ hτ₁ ind_A₂
  refine ⟨g₁, g₂, zeroRel_flip hgA hodd hτ ind_A₁ h0 h2, zeroRel_flip hg₁ ho₁ hτ₁ ind_A₂ h1 h2', ?_⟩
  have := zeroRel_flip hg₂ ho₂ hτ₂ hA₃ (i := 0) (k := 2)
    (Finset.mem_symmDiff.2 (Or.inl ⟨h0, h0'⟩)) (by
      rw [Finset.mem_symmDiff]; rintro (⟨h, -⟩ | ⟨h, -⟩); exacts [h2 h, h2' h])
  rwa [flip_flip_flip] at this

/-! ## §8  `±4eᵢ` -/

theorem zeroRel_single {i j : Fin 24} (hij : i ≠ j) {s t : ℤ} (hs : s = 4 ∨ s = -4)
    (ht : t = 4 ∨ t = -4) : ZeroRel (Pi.single i s) (Pi.single j t) := by
  have hx : s / 2 = 2 ∨ s / 2 = -2 := by omega
  have hy : t / 2 = 2 ∨ t / 2 = -2 := by omega
  have hy' : -(t / 2) = 2 ∨ -(t / 2) = -2 := by omega
  refine ⟨_, pairVec_mem hij hx hy, _, pairVec_mem hij hx hy', ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h i
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero,
      Pi.zero_apply] at this
    omega
  · intro h
    have := congrFun h i
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero,
      Pi.zero_apply] at this
    omega
  · rw [pairVec_dot]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
  · funext k
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega
  · funext k
    simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega

theorem fin24_ne : ∀ i : Fin 24, i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 2 ≠ i + 1 := by decide

/-- `E1 = {±4eᵢ}`: the triangle `±4eᵢ → 4e_{i+1} → 4e_{i+2} → ±4eᵢ`. -/
theorem e1_tri {g : Fin 24 → ℤ} {i : Fin 24} (hgi : |g i| = 4) (h0 : ∀ j, j ≠ i → g j = 0) :
    Tri g := by
  have hg : g = Pi.single i (g i) := by
    funext j
    by_cases h : j = i
    · subst h; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, h0 j h]
  have hs : g i = 4 ∨ g i = -4 := by
    rcases abs_cases (g i) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨h1, h2, h3⟩ := fin24_ne i
  rw [hg]
  exact ⟨Pi.single (i + 1) 4, Pi.single (i + 2) 4, zeroRel_single h1.symm hs (Or.inl rfl),
    zeroRel_single h3.symm (Or.inl rfl) (Or.inl rfl), zeroRel_single h2 (Or.inl rfl) hs⟩

/-! ## §9  The case analysis -/

/-- **`GroundLattice` in Golay coordinates.** -/
theorem groundLatticeA : ∀ g ∈ subA, 12 ≤ g ⬝ᵥ g → Direct g ∨ Tri g := by
  intro g hgA hg
  by_cases hodd : ∀ j, g j % 2 = 1
  · by_cases hτ : ind (tau g) ∈ golay
    · exact Or.inr (odd_tri hgA hodd hτ)
    · exact Or.inl (odd_direct hgA hodd hτ)
  push Not at hodd
  obtain ⟨j₀, hj₀⟩ := hodd
  by_cases hpair : ∃ i j, i ≠ j ∧ (|g i| + |g j| = 3 ∨ 5 ≤ |g i| + |g j|)
  · obtain ⟨i, j, hij, h⟩ := hpair
    exact Or.inl (direct_of_pair hg hij h)
  push Not at hpair
  have habs : ∀ j, 0 ≤ |g j| := fun j => abs_nonneg _
  by_cases hbig : ∃ i, 3 ≤ |g i|
  · obtain ⟨i, hi⟩ := hbig
    have hother : ∀ j, j ≠ i → |g i| + |g j| ≠ 3 ∧ |g i| + |g j| < 5 := fun j hj => hpair i j hj.symm
    obtain ⟨hn3, hn5⟩ := hother (i + 1) (fin24_ne i).1
    have := habs (i + 1)
    by_cases h3 : |g i| = 3
    · exfalso
      have hj1 : ∀ j, j ≠ i → |g j| = 1 := by
        intro j hj
        obtain ⟨a, b⟩ := hother j hj
        have := habs j
        omega
      by_cases hji : j₀ = i
      · subst hji
        rcases abs_cases (g j₀) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · have := hj1 j₀ hji
        rcases abs_cases (g j₀) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · have h4 : |g i| = 4 := by omega
      refine Or.inr (e1_tri h4 fun j hj => ?_)
      obtain ⟨a, b⟩ := hother j hj
      have := habs j
      exact abs_eq_zero.1 (by omega)
  · push Not at hbig
    by_cases h1 : ∃ i, |g i| = 1
    · obtain ⟨i, hi⟩ := h1
      have hle : ∀ j, |g j| ≤ 1 := by
        intro j
        by_cases hji : j = i
        · rw [hji, hi]
        · obtain ⟨a, b⟩ := hpair i j (Ne.symm hji)
          have := hbig j
          omega
      have hz : g j₀ = 0 := by
        have := abs_le.1 (hle j₀)
        omega
      exact Or.inl (direct_le_one hgA hg hle hz)
    · push Not at h1
      refine Or.inl (direct_even2 hgA hg fun j => ?_)
      have := hbig j
      have := h1 j
      have := habs j
      omega

end VOA.Moonshine.GroundLat
