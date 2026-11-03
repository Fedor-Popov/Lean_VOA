/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharLowerG

/-!
# Counting the profile functionals: the full fermionic lower bound

* `card_idxP` — the functionals of a profile `P` of weight `N` number
  `[q^N] q^{nb + ts + sq} H_{2 nb}(q) Π_c 1/(q)_{r_c}`;
* `profSum` — summing over the profiles of length `k` with `nb` blocks gives the Bailey chain
  `β^{(k)}_{nb}`;
* `fermSeries_le_model` — **for every `n ≥ 1`, `[q^N] fermSeries n ≤ Σ_{r ≤ N} dim S_{n,r,N}`**:
  the Chern–Tran–Wakhare fermionic lower bound for the model, with all `n` colours.

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct VOA.QSeries
open scoped BigOperators

noncomputable section

/-- `Π_c 1/(q)_{r_c}`. -/
def rqfL : List ℕ → PowerSeries ℚ
  | [] => 1
  | r :: P => reciprocalQFactorial r * rqfL P

theorem mem_boxE_of_awtE : ∀ (P : List ℕ) (x : ExpL P) (B : ℕ), awtE P x ≤ B → x ∈ boxE P B
  | [], x, B, _ => Finset.mem_singleton.mpr rfl
  | r :: P, x, B, h => by
    have h1 : awt x.1 + awtE P x.2 ≤ B := h
    refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_,
      mem_boxE_of_awtE P x.2 B (by omega)⟩
    rw [Finset.mem_range]
    have : ((i : ℕ) + 1) * x.1 i ≤ awt x.1 :=
      Finset.single_le_sum (f := fun j : Fin r => ((j : ℕ) + 1) * x.1 j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have : x.1 i ≤ ((i : ℕ) + 1) * x.1 i := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The weighted count of exponents. -/
theorem card_boxE_awt : ∀ (P : List ℕ) (e B : ℕ), e ≤ B →
    (((boxE P B).filter fun x => awtE P x = e).card : ℚ) = PowerSeries.coeff e (rqfL P)
  | [], e, B, _ => by
    simp only [boxE, rqfL, PowerSeries.coeff_one]
    by_cases he : e = 0
    · subst he
      show ((({()} : Finset Unit).filter fun x => awtE [] x = 0).card : ℚ) = 1
      simp [awtE]
      exact Finset.card_singleton _
    · rw [if_neg he]; simp [awtE, Ne.symm he]
  | r :: P, e, B, hB => by
    classical
    rw [rqfL, PowerSeries.coeff_mul]
    have hc : ∀ p ∈ Finset.antidiagonal e,
        PowerSeries.coeff p.1 (reciprocalQFactorial r : PowerSeries ℚ) *
          PowerSeries.coeff p.2 (rqfL P) =
        ∑ γ ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (B + 1)),
          ∑ x ∈ boxE P B, (if awt γ = p.1 then (1 : ℚ) else 0) *
            (if awtE P x = p.2 then (1 : ℚ) else 0) := by
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [coeff_reciprocalQFactorial_eq_card r p.1 B (by omega),
        ← card_boxE_awt P p.2 B (by omega), Finset.card_filter, Finset.card_filter]
      push_cast
      rw [Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl hc]
    show ((((Fintype.piFinset fun _ : Fin r => Finset.range (B + 1)) ×ˢ boxE P B).filter
      fun x => awt x.1 + awtE P x.2 = e).card : ℚ) = _
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases he : awt γ + awtE P x = e
    · rw [Finset.sum_eq_single (awt γ, awtE P x)]
      · simp [he]
      · intro p _ hne
        split_ifs with h1 h2 <;> try simp
        exact absurd (Prod.ext h1.symm h2.symm) hne
      · intro hn
        exact absurd (Finset.mem_antidiagonal.mpr he) hn
    · rw [if_neg he]
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      split_ifs with h1 h2 <;> try simp
      exact absurd (by rw [h1, h2]; exact hp') he

/-- The weighted count of the functionals of one profile. -/
theorem card_idxP (P : List ℕ) (N : ℕ) :
    ((idxP P N).card : ℚ) = PowerSeries.coeff N
      (PowerSeries.X ^ (nbL P + tsL P + sqL P) *
        (∑ k ∈ Finset.range (2 * nbL P + 1), gaussian PowerSeries.X (2 * nbL P) k) *
          rqfL P) := by
  classical
  rw [Finset.card_eq_sum_ones, sum_idxP, sum_gaussian_eq]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [cntG, Finset.mul_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro ro _
  rw [Finset.sum_const, nsmul_one, ← pow_add, PowerSeries.coeff_X_pow_mul', symSum_eq_msOf]
  split_ifs with hle
  · rw [← card_boxE_awt P _ N (by omega), fibE]
    congr 2
    ext x
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  · rw [fibE, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    omega

theorem idxP_eq_empty {P : List ℕ} {N : ℕ} (h : N < nbL P + tsL P) : idxP P N = ∅ := by
  rw [idxP, Finset.eq_empty_iff_forall_notMem]
  rintro ⟨k, ro, x⟩ hi
  rw [Finset.mem_sigma, Finset.mem_filter] at hi
  have := hi.2.2
  have := tsL_le_sqL P
  omega

/-- **Summing over the profiles gives the Bailey chain.** -/
theorem profSum : ∀ (k B Nb : ℕ), Nb ≤ B →
    ∑ P ∈ (profs k B).filter (fun P => nbL P = Nb),
      (PowerSeries.X ^ (tsL P + sqL P) * rqfL P : PowerSeries ℚ) = bet k Nb
  | 0, B, Nb, _ => by
    by_cases h : Nb = 0
    · subst h
      rw [Finset.sum_eq_single []]
      · simp [tsL, sqL, rqfL, bet]
      · intro P hP hne
        simp [profs] at hP
        exact absurd hP.1 hne
      · intro h; simp [profs, nbL] at h
    · rw [Finset.sum_eq_zero]
      · simp [bet, h]
      · intro P hP
        simp only [profs, Finset.mem_filter, Finset.mem_singleton] at hP
        obtain ⟨rfl, h'⟩ := hP
        exact absurd h'.symm (by simpa [nbL] using h)
  | k + 1, B, Nb, hNb => by
    classical
    rw [bet]
    -- the profiles `r :: P`
    have hinj : Set.InjOn (fun p : ℕ × List ℕ => p.1 :: p.2)
        ((Finset.range (B + 1)) ×ˢ profs k B : Set (ℕ × List ℕ)) := by
      intro p _ q _ h
      simp only [List.cons.injEq] at h
      exact Prod.ext h.1 h.2
    rw [profs, Finset.filter_image, Finset.sum_image (fun p hp q hq h => hinj (by
      simpa using (Finset.mem_filter.mp hp).1) (by simpa using (Finset.mem_filter.mp hq).1) h)]
    rw [Finset.sum_filter, Finset.sum_product]
    -- regroup by `N_1 = nbL P`
    rw [Finset.sum_comm]
    have hin : ∀ P ∈ profs k B, ∑ r ∈ Finset.range (B + 1),
        (if nbL (r :: P) = Nb then
          (PowerSeries.X ^ (tsL (r :: P) + sqL (r :: P)) * rqfL (r :: P) : PowerSeries ℚ)
          else 0) =
        if nbL P ≤ Nb then PowerSeries.X ^ (nbL P * nbL P + nbL P) *
          reciprocalQFactorial (Nb - nbL P) *
            (PowerSeries.X ^ (tsL P + sqL P) * rqfL P) else 0 := by
      intro P _
      split_ifs with hle
      · rw [Finset.sum_eq_single (Nb - nbL P)]
        · rw [if_pos (by simp [nbL]; omega)]
          simp only [tsL, sqL, rqfL]
          rw [show nbL P + tsL P + (nbL P * nbL P + sqL P) =
            (nbL P * nbL P + nbL P) + (tsL P + sqL P) by ring, pow_add]
          ring
        · intro r _ hr
          rw [if_neg]
          simp only [nbL]; omega
        · intro h
          exfalso; apply h
          rw [Finset.mem_range]; omega
      · apply Finset.sum_eq_zero
        intro r _
        rw [if_neg]
        simp only [nbL]; omega
    rw [Finset.sum_congr rfl hin, ← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (g := nbL) (t := Finset.range (Nb + 1)) (fun P hP => by
      rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.mem_filter.mp hP).2)]
    apply Finset.sum_congr rfl
    intro N1 hN1
    have hN1' : N1 ≤ Nb := Nat.lt_succ_iff.mp (Finset.mem_range.mp hN1)
    rw [← profSum k B N1 (hN1'.trans hNb), Finset.mul_sum]
    rw [Finset.filter_filter]
    apply Finset.sum_congr
    · ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hP, _, h2⟩; exact ⟨hP, h2⟩
      · rintro ⟨hP, h2⟩; exact ⟨hP, h2 ▸ hN1', h2⟩
    · intro P hP
      have hPN : nbL P = N1 := by
        simp only [Finset.mem_filter] at hP; tauto
      rw [hPN]

theorem sum_profs_card_eq (n N : ℕ) :
    PowerSeries.coeff N (fermSeries n) = ∑ P ∈ profs n N, ((idxP P N).card : ℚ) := by
  classical
  rw [fermSeries, coeff_indexBounded_sum _ (coeff_fermTerm_eq_zero n) N N le_rfl, map_sum]
  have hterm : ∀ Nb ∈ Finset.range (N + 1), PowerSeries.coeff N (fermTerm n Nb) =
      ∑ P ∈ (profs n N).filter (fun P => nbL P = Nb), ((idxP P N).card : ℚ) := by
    intro Nb hNb
    have hNb' : Nb ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hNb)
    rw [fermTerm, ← profSum n N Nb hNb', Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro P hP
    rw [card_idxP, (Finset.mem_filter.mp hP).2]
    congr 1
    rw [pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm]
  symm
  rw [← Finset.sum_filter_of_ne (p := fun P => nbL P ≤ N) (fun P _ hP => by
    by_contra h
    exact hP (by rw [idxP_eq_empty (by omega)]; simp))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := nbL) (t := Finset.range (N + 1)) (fun P hP => by
    rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.mem_filter.mp hP).2)]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  rw [Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hP, _, h2⟩; exact ⟨hP, h2⟩
  · rintro ⟨hP, h2⟩; exact ⟨hP, h2 ▸ hx', h2⟩

/-- **The full fermionic lower bound for the model, for every `n ≥ 1`**:
`[q^N] fermSeries n ≤ Σ_{r ≤ N} dim S_{n,r,N}`. -/
theorem fermSeries_le_model {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    PowerSeries.coeff N (fermSeries n) ≤
      ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) : ℚ) := by
  classical
  rw [sum_profs_card_eq]
  have hR : ∑ r ∈ Finset.range (N + 1), ((tIdxG n r N).card : ℚ) =
      ∑ P ∈ profs n N, ((idxP P N).card : ℚ) := by
    simp only [tIdxG, Finset.card_sigma, Nat.cast_sum]
    rw [← Finset.sum_filter_of_ne (s := profs n N) (p := fun P => nbL P + tsL P ≤ N)
      (fun P _ hP => by
        by_contra h
        exact hP (by rw [idxP_eq_empty (by omega)]; simp))]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun P => nbL P + tsL P)
      (t := Finset.range (N + 1)) (fun P hP => by
        rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.mem_filter.mp hP).2)]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : x ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    rw [Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP, h2⟩; exact ⟨hP, h2 ▸ hx', h2⟩
    · rintro ⟨hP, _, h2⟩; exact ⟨hP, h2⟩
  rw [← hR]
  exact Finset.sum_le_sum fun r _ => by exact_mod_cast card_tIdxG_le_finrank hn r N

end

end VOA.TwoSeries.ModelChar
