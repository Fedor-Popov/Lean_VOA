/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
/-
Scratch: the Virasoro central term (c = 1) for the free-boson Sugawara modes.
-/
import VOA.Examples.HeisenbergVirasoro

namespace VOA

open scoped BigOperators
open Module (End)

/-! ## The target

  `L_virasoro (k) (hk) (m n) :`
  `  Lvir k m * Lvir k n - Lvir k n * Lvir k m`
  `    = (m-n) • Lvir k (m+n) + (if m+n=0 then ((m:ℂ)^3-m)/12 else 0) • LinearMap.id`
-/

/-- osc_comm acting on a vector: `a_p (a_q x) = a_q (a_p x) + [p+q=0] (p k) x`. -/
theorem osc_swap (k : ℂ) (p q : ℤ) (x : Fock) :
    osc k p (osc k q x) = osc k q (osc k p x)
      + (if p + q = 0 then (p : ℂ) * k else 0) • x := by
  have h := congrArg (fun (T : End ℂ Fock) => T x) (osc_comm k p q)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  -- h : a_p (a_q x) - a_q (a_p x) = [p+q=0](p k) • x
  linear_combination (norm := module) h

/-! ## The reindexed "boundary-gate" Sugawara term and the central window. -/

/-- The shift equivalence `i ↦ i - m` (used to reindex `F_j` by `i = m + j`, `j = i - m`). -/
def shiftIdx (m : ℤ) : ℤ ≃ ℤ where
  toFun i := i - m
  invFun i := i + m
  left_inv i := by dsimp only; ring
  right_inv i := by dsimp only; ring

@[simp] theorem shiftIdx_apply (m i : ℤ) : shiftIdx m i = i - m := rfl

/-- The ordered pair `a_i a_{m+n-i}` (left index `i`), with the *standard* gate `i < 0`
(normal ordering with the `i`-factor on the right when `i ≥ 0`). This is `sugTerm (m+n) i`. -/
theorem sugTerm_sum_apply (k : ℂ) (m n i : ℤ) (x : Fock) :
    sugTerm k (m + n) i x
      = if i < 0 then osc k i (osc k (m + n - i) x) else osc k (m + n - i) (osc k i x) := by
  rw [sugTerm_apply]

/-- The **shifted-gate** ordered pair `tilS_i = a_i a_{m+n-i}` but with gate `i < m`
(the boundary window shifted by `m`). This is what the reindexed `F`-family produces. -/
noncomputable def tilS (k : ℂ) (m n i : ℤ) (x : Fock) : Fock :=
  if i < m then osc k i (osc k (m + n - i) x) else osc k (m + n - i) (osc k i x)

/-- The `F`-family (the `-j·(…)` half of the per-term bracket `R_j`): the pair `(m+j, n-j)`
ordered by the gate `j < 0`. -/
noncomputable def Ffam (k : ℂ) (m n j : ℤ) (x : Fock) : Fock :=
  (-(j : ℂ)) • (if j < 0 then osc k (m + j) (osc k (n - j) x)
                else osc k (n - j) (osc k (m + j) x))

/-- The `G`-family (the `-(n-j)·(…)` half): this is exactly `-(n-j)·sugTerm (m+n) j`. -/
noncomputable def Gfam (k : ℂ) (m n j : ℤ) (x : Fock) : Fock :=
  (-((n - j : ℤ) : ℂ)) • sugTerm k (m + n) j x

/-- `R_j = F_j + G_j`. -/
theorem R_eq_F_add_G (k : ℂ) (hk : k ≠ 0) (m n j : ℤ) (x : Fock) :
    Lvir k m (sugTerm k n j x) - sugTerm k n j (Lvir k m x)
      = Ffam k m n j x + Gfam k m n j x := by
  rw [L_comm_sugTerm_vec k hk m n j x, Ffam, Gfam, sugTerm_apply]
  by_cases hj : j < 0
  · simp only [if_pos hj]
    rw [show m + (n - j) = m + n - j from by ring]
  · simp only [if_neg hj]
    rw [show m + (n - j) = m + n - j from by ring]
    abel

/-- Reindex `F_j` by `i = m + j`: `F_{i-m} = -(i-m)·tilS_i`. -/
theorem Ffam_reindex (k : ℂ) (m n i : ℤ) (x : Fock) :
    Ffam k m n (i - m) x = (-((i - m : ℤ) : ℂ)) • tilS k m n i x := by
  rw [Ffam, tilS]
  congr 1
  by_cases hi : i < m
  · rw [if_pos (by omega), if_pos hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]
  · rw [if_neg (by omega), if_neg hi,
      show m + (i - m) = i from by ring, show n - (i - m) = m + n - i from by ring]

/-- The **per-`i` boundary difference** `S_i − tilS_i`. The two differ only on the boundary
window (where the gates `i < 0` and `i < m` disagree), and there the difference is a single
commutator `[a_i, a_{m+n-i}]`, hence a central scalar that vanishes unless `m+n = 0`. -/
theorem S_sub_tilS (k : ℂ) (m n i : ℤ) (x : Fock) :
    sugTerm k (m + n) i x - tilS k m n i x
      = (if m + n = 0 then
          (if (i < 0 ∧ ¬ i < m) then (i : ℂ) * k
           else if (¬ i < 0 ∧ i < m) then -((i : ℂ) * k) else 0)
        else 0) • x := by
  rw [sugTerm_apply, tilS]
  -- P := a_i (a_{m+n-i} x), Q := a_{m+n-i} (a_i x); P - Q = δ (i k) x
  have hPQ : osc k i (osc k (m + n - i) x) - osc k (m + n - i) (osc k i x)
      = (if m + n = 0 then (i : ℂ) * k else 0) • x := by
    have h := osc_swap k i (m + n - i) x
    rw [show i + (m + n - i) = m + n from by ring] at h
    rw [h]; abel
  by_cases hmn : m + n = 0
  · rw [if_pos hmn] at hPQ ⊢
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
    · rw [if_pos h0, if_neg hm, hPQ, if_pos (show i < 0 ∧ ¬ i < m from ⟨h0, hm⟩)]
    · rw [if_neg h0, if_pos hm, if_neg (show ¬(i < 0 ∧ ¬ i < m) from by tauto),
          if_pos (show ¬ i < 0 ∧ i < m from ⟨h0, hm⟩)]
      rw [show osc k (m + n - i) (osc k i x) - osc k i (osc k (m + n - i) x)
            = -(osc k i (osc k (m + n - i) x) - osc k (m + n - i) (osc k i x)) from by abel,
          hPQ, neg_smul]
    · rw [if_neg h0, if_neg hm, sub_self, if_neg (by tauto), if_neg (by tauto), zero_smul]
  · rw [if_neg hmn, zero_smul]
    by_cases h0 : i < 0 <;> by_cases hm : i < m
    · rw [if_pos h0, if_pos hm, sub_self]
    · rw [if_pos h0, if_neg hm, hPQ, if_neg hmn, zero_smul]
    · rw [if_neg h0, if_pos hm]
      rw [show osc k (m + n - i) (osc k i x) - osc k i (osc k (m + n - i) x)
            = -(osc k i (osc k (m + n - i) x) - osc k (m + n - i) (osc k i x)) from by abel,
          hPQ, if_neg hmn, zero_smul, neg_zero]
    · rw [if_neg h0, if_neg hm, sub_self]

/-! ## Finiteness of the families. -/

/-- `G_j = -(n-j)·sugTerm (m+n) j x` has finite support (transported from `sugTerm`). -/
theorem Gfam_support_finite (k : ℂ) (m n : ℤ) (x : Fock) :
    (Function.support (fun j : ℤ => Gfam k m n j x)).Finite := by
  apply Set.Finite.subset (sugTerm_support_finite k (m + n) x)
  intro j hj
  rw [Function.mem_support] at hj ⊢
  rw [Gfam] at hj
  exact fun h => hj (by rw [h, smul_zero])

/-- `c(i)·sugTerm (m+n) i x` has finite support for any coefficient `c`. -/
theorem weightedS_support_finite (k : ℂ) (s : ℤ) (c : ℤ → ℂ) (x : Fock) :
    (Function.support (fun i : ℤ => c i • sugTerm k s i x)).Finite := by
  apply Set.Finite.subset (sugTerm_support_finite k s x)
  intro i hi
  rw [Function.mem_support] at hi ⊢
  exact fun h => hi (by rw [h, smul_zero])

/-- `R_j` (the per-term bracket) has finite support. -/
theorem R_support_finite (k : ℂ) (m n : ℤ) (x : Fock) :
    (Function.support (fun j : ℤ =>
      Lvir k m (sugTerm k n j x) - sugTerm k n j (Lvir k m x))).Finite := by
  apply Set.Finite.subset
    ((sugTerm_support_finite k n x).union (sugTerm_support_finite k n (Lvir k m x)))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push_neg at h
  apply hj
  rw [h.1, h.2, map_zero, sub_zero]

/-- `F_j` has finite support: `F = R − G`, both finite. -/
theorem Ffam_support_finite (k : ℂ) (hk : k ≠ 0) (m n : ℤ) (x : Fock) :
    (Function.support (fun j : ℤ => Ffam k m n j x)).Finite := by
  apply Set.Finite.subset ((R_support_finite k m n x).union (Gfam_support_finite k m n x))
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra h
  push_neg at h
  apply hj
  have hR := R_eq_F_add_G k hk m n j x
  rw [h.1, h.2] at hR
  -- hR : 0 = Ffam + 0
  rw [add_zero] at hR
  exact hR.symm

/-- Support finiteness of the reindexed `F`-family `i ↦ -(i-m)·tilS_i x`. -/
theorem reindexedF_support_finite (k : ℂ) (hk : k ≠ 0) (m n : ℤ) (x : Fock) :
    (Function.support (fun i : ℤ => (-((i - m : ℤ) : ℂ)) • tilS k m n i x)).Finite := by
  have hF := Ffam_support_finite k hk m n x
  -- transport through i ↦ i - m using Ffam_reindex
  apply Set.Finite.subset (hF.image (fun j => j + m))
  intro i hi
  rw [Function.mem_support, ← Ffam_reindex] at hi
  rw [Set.mem_image]
  exact ⟨i - m, by rw [Function.mem_support]; exact hi, by ring⟩

/-! ## Master identity: the bracket as bulk + boundary window. -/

/-- The Virasoro commutator on a vector, split into the **bulk** `(m−n)L_{m+n}` and the
finite **boundary window** `(1/2k)∑ᵢ (i−m)(Sᵢ − tilSᵢ)`. The window's summand is a central
scalar (from `S_sub_tilS`), nonzero only when `m+n = 0`. -/
theorem L_comm_bulk_window (k : ℂ) (hk : k ≠ 0) (m n : ℤ) (x : Fock) :
    Lvir k m (Lvir k n x) - Lvir k n (Lvir k m x)
      = (((m : ℂ) - n) • Lvir k (m + n) x)
        + (1 / (2 * k)) • ∑ᶠ i : ℤ,
            (((i : ℂ) - m) • (sugTerm k (m + n) i x - tilS k m n i x)) := by
  rw [L_comm_eq_finsum k m n x]
  -- step 1: R_j = F_j + G_j
  rw [show (∑ᶠ j : ℤ, (Lvir k m (sugTerm k n j x) - sugTerm k n j (Lvir k m x)))
        = ∑ᶠ j : ℤ, (Ffam k m n j x + Gfam k m n j x) from
      finsum_congr fun j => R_eq_F_add_G k hk m n j x]
  -- step 2: split F + G
  rw [finsum_add_distrib (Ffam_support_finite k hk m n x) (Gfam_support_finite k m n x)]
  -- step 3: reindex ∑ F_j = ∑_i F_{i-m} = ∑_i -(i-m) tilS_i
  rw [show (∑ᶠ j : ℤ, Ffam k m n j x)
        = ∑ᶠ i : ℤ, (-((i - m : ℤ) : ℂ)) • tilS k m n i x from by
      rw [← finsum_comp_equiv (shiftIdx m) (f := fun j => Ffam k m n j x)]
      exact finsum_congr fun i => by rw [shiftIdx_apply, Ffam_reindex]]
  -- step 4: G_j = -(n-j) • S_j
  rw [show (∑ᶠ j : ℤ, Gfam k m n j x)
        = ∑ᶠ j : ℤ, (-((n - j : ℤ) : ℂ)) • sugTerm k (m + n) j x from
      finsum_congr fun j => by rw [Gfam]]
  -- step 5: merge the two finsums over i
  rw [← finsum_add_distrib (reindexedF_support_finite k hk m n x)
        (weightedS_support_finite k (m + n) (fun i => -((n - i : ℤ) : ℂ)) x)]
  -- summand identity: -(i-m)•tilS + -(n-i)•S = (m-n)•S + (i-m)•(S - tilS)
  rw [show (∑ᶠ i : ℤ, ((-((i - m : ℤ) : ℂ)) • tilS k m n i x
              + (-((n - i : ℤ) : ℂ)) • sugTerm k (m + n) i x))
        = ∑ᶠ i : ℤ, (((m : ℂ) - n) • sugTerm k (m + n) i x
              + ((i : ℂ) - m) • (sugTerm k (m + n) i x - tilS k m n i x)) from
      finsum_congr fun i => by push_cast; module]
  -- step 6: split into bulk + window, identify bulk with (m-n) L_{m+n}
  rw [finsum_add_distrib
      (weightedS_support_finite k (m + n) (fun i => (m : ℂ) - n) x)
      (by
        apply Set.Finite.subset
          ((weightedS_support_finite k (m + n) (fun i => (i : ℂ) - m) x).union
            (reindexedF_support_finite k hk m n x))
        intro i hi
        rw [Function.mem_support] at hi
        rw [Set.mem_union, Function.mem_support, Function.mem_support]
        by_contra h; push_neg at h; apply hi
        obtain ⟨h1, h2⟩ := h
        have h2' : ((i : ℂ) - m) • tilS k m n i x = 0 := by
          have : (-((i - m : ℤ) : ℂ)) • tilS k m n i x = 0 := h2
          rw [neg_smul, neg_eq_zero] at this
          rw [show ((i : ℂ) - m) = ((i - m : ℤ) : ℂ) from by push_cast; ring]
          exact this
        rw [smul_sub, h1, h2', sub_zero])]
  -- the bulk finsum = (m-n) • ∑ S_i and (m-n) L_{m+n} x = (m-n)/(2k) • ∑ S_i
  rw [smul_add]
  congr 1
  · rw [Lvir_apply' k (m + n) x,
      ← smul_finsum' ((m : ℂ) - n) (sugTerm_support_finite k (m + n) x),
      smul_smul, smul_smul]
    congr 1; ring

/-! ## Power sums over ℂ (by induction), and the window scalar `(m³-m)/6`. -/

open Finset in
/-- `∑_{i<N} i = N(N-1)/2` over ℂ. -/
theorem csum_id (N : ℕ) : ∑ i ∈ range N, (i : ℂ) = (N : ℂ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

open Finset in
/-- `∑_{i<N} i² = N(N-1)(2N-1)/6` over ℂ. -/
theorem csum_sq (N : ℕ) : ∑ i ∈ range N, (i : ℂ)^2 = (N : ℂ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

open Finset in
/-- `∑_{i<N} (N-i)·i = (N³-N)/6` over ℂ. -/
theorem csum_window (N : ℕ) :
    ∑ i ∈ range N, ((N : ℂ) - i) * i = ((N : ℂ)^3 - N) / 6 := by
  have : ∑ i ∈ range N, ((N : ℂ) - i) * i
      = (N : ℂ) * (∑ i ∈ range N, (i : ℂ)) - ∑ i ∈ range N, (i : ℂ)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, csum_id, csum_sq]; ring

open Finset in
/-- A `ℤ`-indexed finsum supported on the window `[base, base + N)` equals the shifted
`range`-sum `∑_{j<N} f(base + j)`. -/
theorem finsum_int_window (f : ℤ → ℂ) (base : ℤ) (N : ℕ)
    (hsupp : ∀ i : ℤ, f i ≠ 0 → base ≤ i ∧ i < base + N) :
    ∑ᶠ i : ℤ, f i = ∑ j ∈ range N, f (base + j) := by
  classical
  let emb : ℕ ↪ ℤ := ⟨fun j => base + (j : ℤ), by intro a b hab; simpa using hab⟩
  rw [finsum_eq_finsetSum_of_support_subset f (s := (range N).map emb) ?_]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    rw [Function.mem_support] at hi
    obtain ⟨h1, h2⟩ := hsupp i hi
    rw [Finset.coe_map, Set.mem_image]
    refine ⟨(i - base).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]; omega
    · show base + ((i - base).toNat : ℤ) = i; omega

/-- The boundary-window scalar summand `W(m,n,i)` from `S_sub_tilS`. -/
noncomputable def winScalar (k : ℂ) (m n i : ℤ) : ℂ :=
  if m + n = 0 then
    (if (i < 0 ∧ ¬ i < m) then (i : ℂ) * k
     else if (¬ i < 0 ∧ i < m) then -((i : ℂ) * k) else 0)
  else 0

/-- **The window resums to `(m³−m)/6 · k`** (`δ_{m+n,0}`). The pos branch (`m > 0`) and the
neg branch (`m < 0`) each reindex to the closed form `∑_{j<M}(M-j)j = (M³−M)/6` (`csum_window`),
and `M = |m|` makes both equal to `k(m³−m)/6`. -/
theorem window_sum (k : ℂ) (m n : ℤ) :
    (∑ᶠ i : ℤ, ((i : ℂ) - m) * winScalar k m n i)
      = if m + n = 0 then k * ((m : ℂ)^3 - m) / 6 else 0 := by
  by_cases hmn : m + n = 0
  · rw [if_pos hmn]
    simp only [winScalar, if_pos hmn]
    rcases le_or_gt 0 m with hm | hm
    · -- m ≥ 0 : only the pos branch (0 ≤ i < m) is active; base 0, N = m.toNat
      have hcast : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
        have := Int.toNat_of_nonneg hm
        rw [← this]; push_cast; rw [this]
      rw [finsum_int_window _ 0 m.toNat ?_]
      · rw [show k * ((m : ℂ)^3 - m) / 6
              = k * (((m.toNat : ℂ)^3 - (m.toNat : ℂ)) / 6) from by rw [hcast]; ring]
        rw [← csum_window m.toNat, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hjm : (0 : ℤ) + (j : ℤ) < m := by
          have : (j : ℤ) < (m.toNat : ℤ) := by exact_mod_cast hj
          rw [Int.toNat_of_nonneg hm] at this; omega
        rw [if_neg (show ¬((0 : ℤ) + (j : ℤ) < 0 ∧ ¬ (0 : ℤ) + (j : ℤ) < m) from by rintro ⟨_, _⟩; omega),
            if_pos (show ¬ ((0 : ℤ) + (j : ℤ) < 0) ∧ (0 : ℤ) + (j : ℤ) < m from ⟨by omega, hjm⟩)]
        rw [show ((0 : ℤ) + (j : ℤ)) = (j : ℤ) from by ring, hcast]
        push_cast; ring
      · -- support: nonzero only on 0 ≤ i < m
        intro i hi
        by_contra hc
        push_neg at hc
        rcases lt_or_ge i 0 with hi0 | hi0
        · -- i < 0, but then both branches: i<0∧¬i<m needs i≥m≥0 false; ¬i<0∧i<m needs i≥0 false
          rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
        · -- i ≥ 0 and (since not in [0,m)) i ≥ m
          have : m ≤ i := by have := hc (by omega); omega
          rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
    · -- m < 0 : only the neg branch (m ≤ i < 0) is active; base m, N = (-m).toNat
      have hmM : ((((-m).toNat : ℕ)) : ℂ) = -(m : ℂ) := by
        have h := Int.toNat_of_nonneg (show (0:ℤ) ≤ -m by omega)
        have : (((-m).toNat : ℤ) : ℂ) = ((-m : ℤ) : ℂ) := by rw [h]
        rw [Int.cast_natCast] at this; rw [this]; push_cast; ring
      rw [finsum_int_window _ m (-m).toNat ?_]
      · rw [show k * ((m : ℂ)^3 - m) / 6
              = -(k * ((((-m).toNat : ℂ)^3 - ((-m).toNat : ℂ)) / 6)) from by
              rw [hmM]; ring]
        rw [← csum_window (-m).toNat, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hjlt : m + (j : ℤ) < 0 := by
          have : (j : ℤ) < ((-m).toNat : ℤ) := by exact_mod_cast hj
          rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -m)] at this; omega
        rw [if_pos (show m + (j : ℤ) < 0 ∧ ¬ m + (j : ℤ) < m from ⟨hjlt, by omega⟩)]
        push_cast
        rw [show (((m : ℂ) + j) - m) = (j : ℂ) from by ring]
        rw [show ((((-m).toNat : ℂ)) - j) = -((m : ℂ) + j) from by rw [hmM]; ring]
        ring
      · -- support: nonzero only on m ≤ i < 0
        intro i hi
        by_contra hc
        push_neg at hc
        rcases lt_or_ge i 0 with hi0 | hi0
        · have : i < m := by by_contra h; exact absurd (hc (by omega)) (by omega)
          rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
        · rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
  · rw [if_neg hmn]
    simp only [winScalar, if_neg hmn, mul_zero, finsum_zero]

/-! ## The full Virasoro relation with central charge `c = 1`. -/

/-- **The Virasoro relations for the free-boson Sugawara modes, central charge `c = 1`**
(Gannon 5.2.5d):
`[Lₘ, Lₙ] = (m−n) L_{m+n} + δ_{m+n,0} (m³−m)/12 · id`.
The bulk `(m−n)L_{m+n}` is the anomaly-free reindexing; the central term is the finite
normal-ordering boundary window, which resums to `(m³−m)/12` (`window_sum`). -/
theorem L_virasoro (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    Lvir k m * Lvir k n - Lvir k n * Lvir k m
      = ((m : ℂ) - n) • Lvir k (m + n)
        + (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0) • (LinearMap.id : End ℂ Fock) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [L_comm_bulk_window k hk m n x]
  congr 1
  -- window finsum of vectors = (window scalar finsum) • x
  rw [show (∑ᶠ i : ℤ, (((i : ℂ) - m) • (sugTerm k (m + n) i x - tilS k m n i x)))
        = ∑ᶠ i : ℤ, (((i : ℂ) - m) * winScalar k m n i) • x from
      finsum_congr fun i => by
        rw [S_sub_tilS k m n i x, smul_smul]; rfl]
  rw [← finsum_smul, window_sum k m n]
  -- (1/2k) • ((if m+n=0 then k(m³-m)/6 else 0) • x) = (if m+n=0 then (m³-m)/12 else 0) • x
  rw [smul_smul]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    congr 1
    field_simp
    ring
  · rw [if_neg hmn, if_neg hmn, mul_zero, zero_smul]

end VOA
