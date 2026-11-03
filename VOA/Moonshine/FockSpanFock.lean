/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FockSpanCharged

/-!
# `FockSpanned`: the charge-zero sector `M(1)⁺` of `V₀⁺`  (Moonshine step M8g, R-gen)

`fockSpanned : FockSpanned` — machine-checked, unconditional.  Hence
`zhuGenerated_weightTwo_of_groundLattice : GroundLattice → ZhuGenerated weightTwo`:
R-gen rests on the lattice residual `GroundLattice` alone.

For weight `n ≥ 3`:

* **Degree `≥ 3`**: the ascent `Fdw_le_of_ascent` with `step_quad` (the source `m' ⊗ e^0` has
  degree `≥ 1`, hence positive weight).
* **Degree `1`**: `P(X v ⊗ e^0) = 0` (`excitedV0_zero_X`).
* **Degree `2`** (`fock_bilinear`), with the weight-two `0`-modes
  `D_{ab} = (h_ah_b)₍₀₎` (derivations on charge `0`) and `(-1)`-modes:
  - off-diagonal `X(i,c)X(j,f)`, `c ≠ f`, `i ≥ 1`: `D_{ce}(X(i-1,e)X(j,f)) = i·X(i,c)X(j,f)` for a
    third colour `e` (`fock_off`);
  - diagonal `V_c(k) = X(k,c)X(n-2-k,c)`: `D_{ce}(X(k-1,e)X(n-2-k,c)) = k V_c(k) + (n-1-k) V_e(k-1)`
    identifies the colours and gives a recursion; the remaining one-dimensional deficiency (even
    `n`, the rank-one `J` of `A(M(1)⁺)`) is removed by the degree-four cancellation
    `(h_ch_e)₍₋₁₎(X(0,c)X(n-4,e)) − (h_ch_c)₍₋₁₎(X(0,e)X(n-4,e)) = (n-3)V_c(0) + V_e(2)`
    (`quadN0_cancel`); the linear algebra is `diag_algebra` (coefficient `(n-3)n ≠ 0`).
  Rank `≥ 3` (three colours) is used; rank 24 is available.

## Main results
* `diag_algebra`, `quadD0_off`, `quadD0_diag`, `quadN0_cancel`, `fock_off`,
  `fock_bilinear`, `fock_base`.
* `fockSpanned`, `zhuGenerated_weightTwo_of_groundLattice`.

## Status
`sorry`-free; no project axiom (`#print axioms fockSpanned` =
`[propext, Classical.choice, Quot.sound]`).  `GroundLattice` (Golay combinatorics of `Λ₀`) is
still open.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FockSpan

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen LatGen IntegralLattice
  HeisenbergN MvPolynomial
open Submodule

/-! ## §1  The linear algebra of the diagonal bilinears -/

/-- The diagonal linear algebra: the relations `(b)`, the symmetry, and the cancellation `(c)`
force every diagonal bilinear to vanish (`n ≥ 3`, at least three colours). -/
theorem diag_algebra {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} (n : ℕ) (hn : 3 ≤ n)
    (W : ι → ℕ → M) (c0 c1 : ι) (h01 : c0 ≠ c1) (hthird : ∀ c g : ι, ∃ e, e ≠ c ∧ e ≠ g)
    (hb : ∀ c e, c ≠ e → ∀ k, 1 ≤ k → k ≤ n - 2 →
      (k : ℂ) • W c k + ((n - 1 - k : ℕ) : ℂ) • W e (k - 1) = 0)
    (hsym : ∀ c k, k ≤ n - 2 → W c k = W c (n - 2 - k))
    (hc : 4 ≤ n → ∀ c e, c ≠ e → ((n - 3 : ℕ) : ℂ) • W c 0 + W e 2 = 0) :
    ∀ c k, k ≤ n - 2 → W c k = 0 := by
  -- Step 1: the colour does not matter
  have hid1 : ∀ c g k, 1 ≤ k → k ≤ n - 2 → W c k = W g k := by
    intro c g k hk1 hk2
    by_cases hcg : c = g
    · rw [hcg]
    obtain ⟨e, hec, heg⟩ := hthird c g
    have h1 := hb c e (Ne.symm hec) k hk1 hk2
    have h2 := hb g e (Ne.symm heg) k hk1 hk2
    have h3 : (k : ℂ) • (W c k - W g k) = 0 := by
      rw [smul_sub]; linear_combination (norm := module) h1 - h2
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h (by exact_mod_cast (show k ≠ 0 by omega))
    · exact sub_eq_zero.mp h
  have hid : ∀ c g k, k ≤ n - 2 → W c k = W g k := by
    intro c g k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [hsym c 0 (by omega), hsym g 0 (by omega)]
      exact hid1 c g _ (by omega) (by omega)
    · exact hid1 c g k h0 hk
  -- Step 2: one colour
  have hb' : ∀ k, 1 ≤ k → k ≤ n - 2 →
      (k : ℂ) • W c0 k + ((n - 1 - k : ℕ) : ℂ) • W c0 (k - 1) = 0 := by
    intro k hk1 hk2
    have h := hb c0 c1 h01 k hk1 hk2
    rwa [hid c1 c0 (k - 1) (by omega)] at h
  -- Step 3: the bottom vanishes
  have hw0 : W c0 0 = 0 := by
    rcases Nat.lt_or_ge n 4 with h3 | h4
    · have hn3 : n = 3 := by omega
      subst hn3
      have h1 := hb' 1 le_rfl le_rfl
      have hs := hsym c0 0 (by omega)
      simp only [Nat.cast_one, one_smul, show (3 - 1 - 1 : ℕ) = 1 from rfl, Nat.sub_self] at h1 hs
      rw [← hs] at h1
      have h2 : (2 : ℂ) • W c0 0 = 0 := by rw [two_smul]; exact h1
      rcases smul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    · have E1 := hb' 1 le_rfl (by omega)
      have E2 := hb' 2 (by omega) (by omega)
      have E3 := hc h4 c1 c0 (Ne.symm h01)
      rw [hid c1 c0 0 (by omega)] at E3
      simp only [Nat.cast_one, one_smul, Nat.sub_self, show (2 - 1 : ℕ) = 1 from rfl,
        show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega] at E1 E2
      have key : (((n - 3 : ℕ) : ℂ) * ((n - 2 : ℕ) + 2 : ℂ)) • W c0 0 = 0 := by
        linear_combination (norm := module) (2 : ℂ) • E3 - E2 + ((n - 3 : ℕ) : ℂ) • E1
      rcases smul_eq_zero.mp key with h | h
      · exfalso
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (by exact_mod_cast (show n - 3 ≠ 0 by omega))
        · have : ((n - 2 : ℕ) : ℂ) + 2 = ((n - 2 + 2 : ℕ) : ℂ) := by push_cast; ring
          rw [this] at h'
          exact absurd h' (by exact_mod_cast (show n - 2 + 2 ≠ 0 by omega))
      · exact h
  -- Step 4: upward induction
  have hall : ∀ k, k ≤ n - 2 → W c0 k = 0 := by
    intro k
    induction k with
    | zero => intro _; exact hw0
    | succ k ih =>
      intro hk
      have h := hb' (k + 1) (by omega) hk
      rw [Nat.add_sub_cancel, ih (by omega), smul_zero, add_zero] at h
      rcases smul_eq_zero.mp h with h' | h'
      · exact absurd h' (by exact_mod_cast (show k + 1 ≠ 0 by omega))
      · exact h'
  intro c k hk
  rw [hid c c0 k hk]
  exact hall k hk

/-! ## §2  The charge-zero relations -/

/-- The charge-`0` target submodule. -/
noncomputable abbrev T0 (n : ℤ) : Submodule ℂ Fk := Tsub lambda0.zero_mem n

theorem quad0_mem (i j : ℕ) (a b : Fin (rank leech)) {n m : ℤ} (hm : m ≤ 0) {w : ℕ} {p : Fk}
    (hp : p ∈ gradingWN (rank leech) w) (h1 : (i : ℤ) + j + 2 < n) (h2 : (w : ℤ) < n)
    (h3 : ((i : ℤ) + j + 2) + w - m - 1 = n) :
    quadF 0 a i b j (-m - 1) p ∈ T0 n :=
  quadF_mem_Tsub i j a b lambda0.zero_mem hm hp h1 (by rw [SigmaExist.halfNorm_zero]; simpa)
    (by rw [SigmaExist.halfNorm_zero]; simpa)

theorem quadD0_one (a b : Fin (rank leech)) : quadF 0 a 0 b 0 (-1) (1 : Fk) = 0 := by
  rw [quadF_D_one, chargeCoord_zero, chargeCoord_zero, zero_smul, zero_smul, add_zero]

theorem quadN0_one (a b : Fin (rank leech)) :
    quadF 0 a 0 b 0 0 (1 : Fk) = X (0, a) * X (0, b) := by
  rw [quadF_lead_one, chargeCoord_zero, chargeCoord_zero]
  simp

theorem quadD0_X (a b : Fin (rank leech)) (t : ℕ) (c : Fin (rank leech)) :
    quadF 0 a 0 b 0 (-1) (X (t, c) : Fk)
      = (if c = b then ((t : ℂ) + 1) • (X (t + 1, a) : Fk) else 0)
        + (if c = a then ((t : ℂ) + 1) • (X (t + 1, b) : Fk) else 0) := by
  rw [← mul_one (X (t, c) : Fk), quadD_X, quadD0_one, mul_zero, zero_add, mul_one, mul_one]

/-- `(h_ch_e)₍₀₎(X(i,e)X(j,f)) = (i+1) X(i+1,c)X(j,f)` for distinct `c, e, f`. -/
theorem quadD0_off {c e f : Fin (rank leech)} (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (i j : ℕ) :
    quadF 0 c 0 e 0 (-1) (X (i, e) * X (j, f) : Fk)
      = ((i : ℂ) + 1) • (X (i + 1, c) * X (j, f) : Fk) := by
  rw [quadD_X, quadD0_X, if_neg (Ne.symm hef), if_neg (Ne.symm hcf), if_pos rfl,
    if_neg (Ne.symm hce)]
  simp

/-- `(h_ch_e)₍₀₎(X(k,e)X(m,c)) = (k+1) X(k+1,c)X(m,c) + (m+1) X(k,e)X(m+1,e)` (`c ≠ e`). -/
theorem quadD0_diag {c e : Fin (rank leech)} (hce : c ≠ e) (k m : ℕ) :
    quadF 0 c 0 e 0 (-1) (X (k, e) * X (m, c) : Fk)
      = ((k : ℂ) + 1) • (X (k + 1, c) * X (m, c) : Fk)
        + ((m : ℂ) + 1) • (X (k, e) * X (m + 1, e) : Fk) := by
  rw [quadD_X, quadD0_X, if_neg hce, if_pos rfl, if_pos rfl, if_neg (Ne.symm hce)]
  simp only [add_zero, zero_add, mul_smul_comm]
  abel

/-- The degree-four cancellation:
`(h_ch_e)₍₋₁₎(X(0,c)X(L,e)) − (h_ch_c)₍₋₁₎(X(0,e)X(L,e)) = (L+1) X(0,c)X(L+2,c) + X(2,e)X(L,e)`. -/
theorem quadN0_cancel {c e : Fin (rank leech)} (hce : c ≠ e) (L : ℕ) :
    quadF 0 c 0 e 0 0 (X (0, c) * X (L, e) : Fk) - quadF 0 c 0 c 0 0 (X (0, e) * X (L, e) : Fk)
      = ((L : ℂ) + 1) • (X (0, c) * X (L + 2, c) : Fk) + (X (2, e) * X (L, e) : Fk) := by
  rw [← mul_one (X (L, e) : Fk), quadN_X, quadN_X, quadN_X, quadN_X, quadN0_one, quadN0_one]
  simp only [hce, Ne.symm hce, if_true, if_false, add_zero, mul_one, Nat.cast_zero, zero_add,
    one_smul, MvPolynomial.smul_eq_C_mul]
  ring

/-! ## §3  Degree two -/

theorem exists_third (c g : Fin (rank leech)) : ∃ e, e ≠ c ∧ e ≠ g := by
  have h24 : rank leech = 24 := leech_rank
  by_cases h0 : (⟨0, by omega⟩ : Fin (rank leech)) ≠ c ∧ (⟨0, by omega⟩ : Fin (rank leech)) ≠ g
  · exact ⟨_, h0⟩
  by_cases h1 : (⟨1, by omega⟩ : Fin (rank leech)) ≠ c ∧ (⟨1, by omega⟩ : Fin (rank leech)) ≠ g
  · exact ⟨_, h1⟩
  by_cases h2 : (⟨2, by omega⟩ : Fin (rank leech)) ≠ c ∧ (⟨2, by omega⟩ : Fin (rank leech)) ≠ g
  · exact ⟨_, h2⟩
  exfalso
  simp only [not_and_or, not_not, Fin.ext_iff] at h0 h1 h2
  omega

theorem X_mul_X_mem_gradingWN' (i j : ℕ) (a b : Fin (rank leech)) {w : ℕ} (hw : i + j + 2 = w) :
    (X (i, a) * X (j, b) : Fk) ∈ gradingWN (rank leech) w := by
  rw [← hw]; exact X_mul_X_mem_gradingWN i j a b

/-- Off-diagonal bilinears `X(i,c)X(j,f)` (`c ≠ f`, `i ≥ 1`) are `0`-products. -/
theorem fock_off {n : ℕ} {c f : Fin (rank leech)} (hcf : c ≠ f) (i j : ℕ) (hi : 1 ≤ i)
    (hw : i + j + 2 = n) : (X (i, c) * X (j, f) : Fk) ∈ T0 n := by
  obtain ⟨e, hec, hef⟩ := exists_third c f
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have h := quad0_mem 0 0 c e (n := n) (m := 0) le_rfl
    (X_mul_X_mem_gradingWN' i' j e f (w := n - 1) (by omega)) (by push_cast; omega)
    (by omega) (by push_cast; omega)
  rw [show -(0 : ℤ) - 1 = -1 by norm_num, quadD0_off (Ne.symm hec) hef hcf] at h
  have h2 := smul_mem _ (((i' : ℂ) + 1)⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero i'), one_smul] at h2

/-- **The bilinears**: every degree-two charge-`0` state of weight `n ≥ 3` lies in `Tsub`. -/
theorem fock_bilinear {n : ℕ} (hn : 3 ≤ n) (v1 v2 : ℕ × Fin (rank leech))
    (hw : v1.1 + v2.1 + 2 = n) : (X v1 * X v2 : Fk) ∈ T0 n := by
  obtain ⟨i, c⟩ := v1
  obtain ⟨j, f⟩ := v2
  simp only at hw
  by_cases hcf : c = f
  · subst hcf
    -- the diagonal: linear algebra in the quotient
    set W : Fin (rank leech) → ℕ → Fk ⧸ T0 n :=
      fun c k => (T0 n).mkQ (X (k, c) * X (n - 2 - k, c) : Fk) with hW
    have hb : ∀ c e, c ≠ e → ∀ k, 1 ≤ k → k ≤ n - 2 →
        (k : ℂ) • W c k + ((n - 1 - k : ℕ) : ℂ) • W e (k - 1) = 0 := by
      intro c e hce k hk1 hk2
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have h := quad0_mem 0 0 c e (n := n) (m := 0) le_rfl
        (X_mul_X_mem_gradingWN' k' (n - 2 - (k' + 1)) e c (w := n - 1) (by omega))
        (by push_cast; omega) (by omega) (by push_cast; omega)
      rw [show -(0 : ℤ) - 1 = -1 by norm_num, quadD0_diag hce] at h
      have e1 : n - 2 - (k' + 1) + 1 = n - 2 - k' := by omega
      have e2 : ((n - 2 - (k' + 1) : ℕ) : ℂ) + 1 = ((n - 1 - (k' + 1) : ℕ) : ℂ) := by
        rw [show n - 1 - (k' + 1) = n - 2 - (k' + 1) + 1 by omega]; push_cast; ring
      rw [e1, e2, show ((k' : ℂ) + 1) = ((k' + 1 : ℕ) : ℂ) by push_cast; ring] at h
      simp only [hW, Nat.add_sub_cancel]
      rw [← map_smul, ← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
    have hsym : ∀ c k, k ≤ n - 2 → W c k = W c (n - 2 - k) := by
      intro c k hk
      simp only [hW]
      rw [mul_comm, show n - 2 - (n - 2 - k) = k by omega]
    have hc : 4 ≤ n → ∀ c e, c ≠ e → ((n - 3 : ℕ) : ℂ) • W c 0 + W e 2 = 0 := by
      intro h4 c e hce
      have h1 := quad0_mem 0 0 c e (n := n) (m := -1) (by norm_num)
        (X_mul_X_mem_gradingWN' 0 (n - 4) c e (w := n - 2) (by omega))
        (by push_cast; omega) (by omega) (by push_cast; omega)
      have h2 := quad0_mem 0 0 c c (n := n) (m := -1) (by norm_num)
        (X_mul_X_mem_gradingWN' 0 (n - 4) e e (w := n - 2) (by omega))
        (by push_cast; omega) (by omega) (by push_cast; omega)
      have h3 := sub_mem h1 h2
      rw [show -(-1 : ℤ) - 1 = 0 by norm_num, quadN0_cancel hce] at h3
      rw [show n - 4 + 2 = n - 2 by omega, show ((n - 4 : ℕ) : ℂ) + 1 = ((n - 3 : ℕ) : ℂ) by
        rw [show n - 3 = n - 4 + 1 by omega]; push_cast; ring] at h3
      simp only [hW, Nat.sub_zero, show n - 2 - 2 = n - 4 by omega]
      rw [← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h3
    have hall := diag_algebra n hn W ⟨0, by rw [leech_rank]; omega⟩
      ⟨1, by rw [leech_rank]; omega⟩ (by simp [Fin.ext_iff]) exists_third hb hsym hc c i
      (by omega)
    simp only [hW, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hall
    rwa [show n - 2 - i = j by omega] at hall
  · rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [mul_comm]
      exact fock_off (Ne.symm hcf) j i (by omega) (by omega)
    · exact fock_off hcf i j hi hw

/-! ## §4  `FockSpanned` -/

/-- Odd charge-`0` states project to zero: `P(X v ⊗ e^0) = 0`. -/
theorem excitedV0_zero_X (v : ℕ × Fin (rank leech)) :
    excitedV0 lambda0.zero_mem (X v : Fk) = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [excitedV0_coe, plusProj_coe, thetaLat_latStateGen, sigmaN_X, neg_zero]
  simp [latStateGen, TensorProduct.neg_tmul]

/-- Degrees `≤ 2` in the charge-`0` sector (weight `n ≥ 3`). -/
theorem fock_base {n : ℕ} (hn : 3 ≤ n) : Fdw 2 n ≤ T0 n := by
  refine (Fdw_le_span 2 n).trans (span_le.mpr ?_)
  rintro _ ⟨s, hsd, hsw, rfl⟩
  rcases Nat.eq_zero_or_pos s.degree with h0 | h0
  · rw [eq_zero_of_degree_eq_zero h0, wt, map_zero] at hsw
    omega
  obtain ⟨v1, s1, rfl⟩ := exists_single_add (s := s) h0
  rw [degree_single_add] at hsd
  rw [wt_single_add] at hsw
  rcases Nat.eq_zero_or_pos s1.degree with h1 | h1
  · obtain rfl : s1 = 0 := eq_zero_of_degree_eq_zero h1
    rw [SetLike.mem_coe, monomial_single_add_one, monomial_zero', C_1, mul_one]
    change excitedV0 lambda0.zero_mem (X v1 : Fk) ∈ span ℂ (lowerProd V0P (n : ℤ))
    rw [excitedV0_zero_X]
    exact zero_mem _
  obtain ⟨v2, s', rfl⟩ := exists_single_add (s := s1) h1
  rw [degree_single_add] at hsd
  rw [wt_single_add] at hsw
  obtain rfl : s' = 0 := eq_zero_of_degree_eq_zero (by omega)
  rw [wt, map_zero] at hsw
  rw [SetLike.mem_coe, monomial_single_add_one, monomial_single_add_one, monomial_zero', C_1,
    mul_one]
  exact fock_bilinear hn v1 v2 (by push_cast at hsw; omega)

theorem one_le_wt_of_degree {s : (ℕ × Fin (rank leech)) →₀ ℕ} (h : 1 ≤ s.degree) : 1 ≤ wt s := by
  obtain ⟨v, s', rfl⟩ := exists_single_add h
  rw [wt_single_add]
  omega

/-- **`FockSpanned`** (machine-checked): every projected charge-`0` word state of weight `≥ 3`
is a combination of weight-raising products of lower-weight states of `V₀⁺`. -/
theorem fockSpanned : FockSpanned := by
  intro l hl
  rw [← excitedV0_word]
  change wordStateN l ∈ T0 (wordWt l)
  have hn : 3 ≤ wordWt l := by exact_mod_cast hl
  refine gradingWN_le_of_Fdw (fun D => ?_) (wordStateN_mem_gradingWN l)
  refine Fdw_le_of_ascent _ (wordWt l) 2 (by norm_num) (fock_base hn)
    (fun D' hD' IH v1 v2 s' hdeg hwt => step_quad lambda0.zero_mem _ D' (wordWt l)
      (by rw [SigmaExist.halfNorm_zero, add_zero]) IH v1 v2 s' hdeg hwt ?_) D
  have := one_le_wt_of_degree (s := s') (by omega)
  rw [SigmaExist.halfNorm_zero, add_zero]
  exact_mod_cast this

/-- **`V0LowerSpanned` reduced to the ground-state lattice residual alone.** -/
theorem zhuGenerated_weightTwo_of_groundLattice (hL : GroundLattice) :
    ZhuGenerated weightTwo :=
  zhuGenerated_weightTwo_of_residuals fockSpanned excitedSpanned hL

end VOA.Moonshine.FockSpan
