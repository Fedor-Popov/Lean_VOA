import VOA.DeligneAudit.SL4TRelationLineFlag
import VOA.DeligneAudit.SL4TBalanced

/-!
# Site words by number of T-states, and summation by parts

For a site word of a one-adjoint-site block `q`, the number `Y` of roots in `Y = g₁ ⊔ g₂′` is
the weight `r = mixedWeight q`, and the word weight is `3^T 2^(r - 2T)` with `T` its number of
T-states (sites with two roots in `Y`). With the stratum level `L_j = r - min(j, ⌊r/2⌋)` the
balanced cost of level `L_j` is `3^min(j, ⌊r/2⌋) 2^(r - 2 min(j, ⌊r/2⌋))`; it is antitone in `j`
and equals the word weight on words with `j` T-states. Hence the block cost is
`Σ_j (w_j - w_(j+1)) · cost(L_j)` (`adjointSiteBlockBound_eq_strata`). Summation by parts
(`stratumCost_le_of_codimension_le`) then bounds `Σ_j (g_j - g_(j+1)) · c_j` by
`Σ_j (w_j - w_(j+1)) · c_j` whenever `g_0 - g_j ≤ w_0 - w_j` for all `j` and `c` is antitone:
only the upper bounds of the stratum count are used.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.CVsl2 (bal)

/-! ### Summation by parts -/

/-- The summation-by-parts identity comparing two stratum costs. -/
theorem stratumCost_sub_eq (n : ℕ) (G W c : ℕ → ℤ) :
    (∑ j ∈ Finset.range n, (W j - W (j + 1)) * c j) -
        ∑ j ∈ Finset.range n, (G j - G (j + 1)) * c j =
      ((W 0 - W n) - (G 0 - G n)) * c n +
        ∑ j ∈ Finset.range n, ((W 0 - W (j + 1)) - (G 0 - G (j + 1))) * (c j - c (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      linear_combination ih

/-- **Summation by parts.** If the codimensions `g_0 - g_j` are bounded by `w_0 - w_j` and the
costs are antitone, the stratum cost of `g` is at most that of `w`. -/
theorem stratumCost_le_of_codimension_le (n : ℕ) (g w c : ℕ → ℕ)
    (hg : ∀ j < n, g (j + 1) ≤ g j) (hw : ∀ j < n, w (j + 1) ≤ w j)
    (hc : ∀ j, c (j + 1) ≤ c j) (hcod : ∀ j ≤ n, g 0 - g j ≤ w 0 - w j) :
    ∑ j ∈ Finset.range n, (g j - g (j + 1)) * c j ≤
      ∑ j ∈ Finset.range n, (w j - w (j + 1)) * c j := by
  have hg0 : ∀ j ≤ n, g j ≤ g 0 := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hg j (by omega)).trans (ih (by omega))
  have hw0 : ∀ j ≤ n, w j ≤ w 0 := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hw j (by omega)).trans (ih (by omega))
  have hcast (v : ℕ → ℕ) (hv : ∀ j < n, v (j + 1) ≤ v j) :
      ((∑ j ∈ Finset.range n, (v j - v (j + 1)) * c j : ℕ) : ℤ) =
        ∑ j ∈ Finset.range n, ((v j : ℤ) - v (j + 1)) * c j := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_mul, Nat.cast_sub (hv j (Finset.mem_range.mp hj))]
  have key := stratumCost_sub_eq n (fun j => (g j : ℤ)) (fun j => (w j : ℤ))
    (fun j => (c j : ℤ))
  have hnonneg : 0 ≤ (((w 0 : ℤ) - w n) - ((g 0 : ℤ) - g n)) * (c n : ℤ) +
      ∑ j ∈ Finset.range n,
        (((w 0 : ℤ) - w (j + 1)) - ((g 0 : ℤ) - g (j + 1))) * ((c j : ℤ) - c (j + 1)) := by
    apply add_nonneg
    · apply mul_nonneg _ (Nat.cast_nonneg _)
      have h₁ := hcod n le_rfl
      have h₂ := hg0 n le_rfl
      have h₃ := hw0 n le_rfl
      omega
    · apply Finset.sum_nonneg
      intro j hj
      have hjn := Finset.mem_range.mp hj
      apply mul_nonneg
      · have h₁ := hcod (j + 1) hjn
        have h₂ := hg0 (j + 1) hjn
        have h₃ := hw0 (j + 1) hjn
        omega
      · have := hc j
        omega
  have hle : ((∑ j ∈ Finset.range n, (g j - g (j + 1)) * c j : ℕ) : ℤ) ≤
      ((∑ j ∈ Finset.range n, (w j - w (j + 1)) * c j : ℕ) : ℤ) := by
    rw [hcast g hg, hcast w hw]
    linarith
  exact_mod_cast hle

/-! ### Stratum levels and their costs -/

/-- The level `r - min(j, ⌊r/2⌋)` used for the stratum `j`; it is at least `r - j`. -/
def jointStratumLevel (r j : ℕ) : ℕ := r - min j (r / 2)

theorem jointStratumLevel_ge (r j : ℕ) : r - j ≤ jointStratumLevel r j := by
  unfold jointStratumLevel
  have := min_le_left j (r / 2)
  omega

/-- The balanced cost of the stratum level: `3^m 2^(r - 2m)` with `m = min(j, ⌊r/2⌋)`. -/
theorem lineLevelCost_jointStratumLevel (r j : ℕ) :
    lineLevelCost r (jointStratumLevel r j) =
      3 ^ min j (r / 2) * 2 ^ (r - 2 * min j (r / 2)) := by
  unfold lineLevelCost jointStratumLevel
  have h₁ := min_le_right j (r / 2)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [bal_prod_of_weight_le (Nat.zero_le _)]
    simp
  · rw [bal_prod_two (by omega) (by omega) (by omega)]
    congr 2 <;> omega

/-- The stratum costs are antitone. -/
theorem lineLevelCost_jointStratumLevel_succ_le (r j : ℕ) :
    lineLevelCost r (jointStratumLevel r (j + 1)) ≤ lineLevelCost r (jointStratumLevel r j) := by
  rw [lineLevelCost_jointStratumLevel, lineLevelCost_jointStratumLevel]
  by_cases hj : j + 1 ≤ r / 2
  · rw [min_eq_left hj, min_eq_left (by omega : j ≤ r / 2)]
    have hsplit : r - 2 * j = (r - 2 * (j + 1)) + 2 := by omega
    have hx : 3 ^ (j + 1) * 2 ^ (r - 2 * (j + 1)) = (3 ^ j * 2 ^ (r - 2 * (j + 1))) * 3 := by
      ring
    have hy : 3 ^ j * 2 ^ (r - 2 * j) = (3 ^ j * 2 ^ (r - 2 * (j + 1))) * 4 := by
      rw [hsplit]
      ring
    rw [hx, hy]
    exact Nat.mul_le_mul_left _ (by norm_num)
  · rw [min_eq_right (by omega : r / 2 ≤ j + 1), min_eq_right (by omega : r / 2 ≤ j)]

/-! ### Sites and words -/

/-- `1` exactly when a site carries two roots in `Y`. -/
def siteTwoIndicator (n : ℕ) : ℕ := if n = 2 then 1 else 0

theorem siteYWeight_mul_four_pow (n : ℕ) (hn : n ≤ 2) :
    siteYWeight n * 2 ^ (2 * siteTwoIndicator n) = 3 ^ siteTwoIndicator n * 2 ^ n := by
  interval_cases n <;> rfl

theorem two_mul_siteTwoIndicator_le (n : ℕ) : 2 * siteTwoIndicator n ≤ n := by
  unfold siteTwoIndicator
  split_ifs <;> omega

theorem adjointSiteStateYCount_le (a : AdjointSiteState) : adjointSiteStateYCount a ≤ 2 := by
  revert a
  decide

theorem doubledSiteStateYCount_le (s : DoubledSiteState) : doubledSiteStateYCount s ≤ 2 := by
  revert s
  decide

theorem flagColourInY_le (l : Fin 4) : flagColourInY l ≤ 1 := by
  revert l
  decide

theorem adjointSiteStateYCount_eq (a : AdjointSiteState) :
    adjointSiteStateYCount a =
      adjointSiteStateColourCount a 1 + adjointSiteStateColourCount a 3 := by
  revert a
  decide

theorem doubledSiteStateYCount_eq (s : DoubledSiteState) :
    doubledSiteStateYCount s =
      doubledSiteStateColourCount s 1 + doubledSiteStateColourCount s 3 := by
  revert s
  decide

theorem flagColourInY_eq (l : Fin 4) :
    flagColourInY l = (if l = 1 then 1 else 0) + (if l = 3 then 1 else 0) := by
  revert l
  decide

theorem adjointSiteState_colour_total (a : AdjointSiteState) :
    ∑ l, adjointSiteStateColourCount a l =
      (if a.1.isSome then 1 else 0) + (if a.2.isSome then 1 else 0) := by
  revert a
  decide

theorem doubledSiteState_colour_total (s : DoubledSiteState) :
    ∑ l, doubledSiteStateColourCount s l = 2 := by
  revert s
  decide

variable {B k : ℕ}

/-- The number of roots of a word lying in `Y = g₁ ⊔ g₂′`. -/
def adjointSiteWordYCount (u : AdjointSiteWord B k) : ℕ :=
  adjointSiteStateYCount u.1 + ∑ i, doubledSiteStateYCount (u.2.1 i) +
    ∑ i, flagColourInY (u.2.2 i)

theorem adjointSiteWordYCount_eq (u : AdjointSiteWord B k) :
    adjointSiteWordYCount u = adjointSiteWordColourCount u 1 + adjointSiteWordColourCount u 3 := by
  simp only [adjointSiteWordYCount, adjointSiteWordColourCount, adjointSiteStateYCount_eq,
    doubledSiteStateYCount_eq, flagColourInY_eq, Finset.sum_add_distrib]
  ring

/-- Every word has `[U-root] + [V-root] + 2k + (B - 2k)` roots. -/
theorem adjointSiteWord_colour_total (u : AdjointSiteWord B k) :
    ∑ l, adjointSiteWordColourCount u l =
      (if u.1.1.isSome then 1 else 0) + (if u.1.2.isSome then 1 else 0) + 2 * k +
        (B - 2 * k) := by
  have h₁ : ∑ l : Fin 4, ∑ i : Fin k, doubledSiteStateColourCount (u.2.1 i) l = 2 * k := by
    rw [Finset.sum_comm]
    simp [doubledSiteState_colour_total, mul_comm]
  have h₂ : ∑ l : Fin 4, ∑ i : Fin (B - 2 * k), (if u.2.2 i = l then 1 else 0) = B - 2 * k := by
    rw [Finset.sum_comm]
    simp
  simp only [adjointSiteWordColourCount, Finset.sum_add_distrib, h₁, h₂,
    adjointSiteState_colour_total]

/-- The weight `r` of the block of a word is its number of roots in `Y`. -/
theorem adjointSiteWordBlock_weight (hkB : 2 * k ≤ B) (u : AdjointSiteWord B k) :
    (mixedWeight (adjointSiteWordBlock u)).toNat = adjointSiteWordYCount u := by
  have ht := adjointSiteWord_colour_total u
  rw [Fin.sum_univ_four] at ht
  rw [adjointSiteWordYCount_eq]
  simp only [adjointSiteWordBlock, mixedWeight, mixedQ]
  split_ifs at ht ⊢ <;> omega

/-- The weight of a word is `3^T 2^(Y - 2T)`, and `2T ≤ Y`. -/
theorem adjointSiteWordWeight_eq (u : AdjointSiteWord B k) :
    adjointSiteWordWeight u =
        3 ^ adjointSiteWordTCount u * 2 ^ (adjointSiteWordYCount u - 2 * adjointSiteWordTCount u) ∧
      2 * adjointSiteWordTCount u ≤ adjointSiteWordYCount u := by
  set ta := siteTwoIndicator (adjointSiteStateYCount u.1)
  set td : Fin k → ℕ := fun i => siteTwoIndicator (doubledSiteStateYCount (u.2.1 i))
  have hT : adjointSiteWordTCount u = ta + ∑ i, td i := rfl
  have hle : 2 * adjointSiteWordTCount u ≤ adjointSiteWordYCount u := by
    rw [hT, mul_add, Finset.mul_sum]
    unfold adjointSiteWordYCount
    have h₁ := two_mul_siteTwoIndicator_le (adjointSiteStateYCount u.1)
    have h₂ : ∑ i, 2 * td i ≤ ∑ i, doubledSiteStateYCount (u.2.1 i) :=
      Finset.sum_le_sum fun i _ => two_mul_siteTwoIndicator_le _
    omega
  have hd : (∏ i, siteYWeight (doubledSiteStateYCount (u.2.1 i))) * 2 ^ (2 * ∑ i, td i) =
      (∏ i, 3 ^ td i) * ∏ i, 2 ^ doubledSiteStateYCount (u.2.1 i) := by
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ =>
      siteYWeight_mul_four_pow _ (doubledSiteStateYCount_le _)
  have hs : ∏ i, siteYWeight (flagColourInY (u.2.2 i)) = ∏ i, 2 ^ flagColourInY (u.2.2 i) := by
    apply Finset.prod_congr rfl
    intro i _
    have := flagColourInY_le (u.2.2 i)
    interval_cases flagColourInY (u.2.2 i) <;> rfl
  have ha := siteYWeight_mul_four_pow _ (adjointSiteStateYCount_le u.1)
  have hmul : adjointSiteWordWeight u * 2 ^ (2 * adjointSiteWordTCount u) =
      3 ^ adjointSiteWordTCount u * 2 ^ adjointSiteWordYCount u := by
    unfold adjointSiteWordWeight adjointSiteWordYCount
    rw [hT, hs]
    calc _ = (siteYWeight (adjointSiteStateYCount u.1) * 2 ^ (2 * ta)) *
            ((∏ i, siteYWeight (doubledSiteStateYCount (u.2.1 i))) * 2 ^ (2 * ∑ i, td i)) *
              ∏ i, 2 ^ flagColourInY (u.2.2 i) := by
          rw [mul_add, pow_add]
          ring
      _ = (3 ^ ta * 2 ^ adjointSiteStateYCount u.1) *
            ((∏ i, 3 ^ td i) * ∏ i, 2 ^ doubledSiteStateYCount (u.2.1 i)) *
              ∏ i, 2 ^ flagColourInY (u.2.2 i) := by rw [ha, hd]
      _ = _ := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
            Finset.prod_pow_eq_pow_sum]
          ring
  refine ⟨?_, hle⟩
  have hsplit : adjointSiteWordYCount u =
      (adjointSiteWordYCount u - 2 * adjointSiteWordTCount u) + 2 * adjointSiteWordTCount u := by
    omega
  rw [hsplit, pow_add, ← mul_assoc] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

/-- The weight of a word is the cost of the stratum level of its number of T-states. -/
theorem adjointSiteWordWeight_eq_stratumCost (hkB : 2 * k ≤ B) (u : AdjointSiteWord B k) :
    adjointSiteWordWeight u =
      lineLevelCost (mixedWeight (adjointSiteWordBlock u)).toNat
        (jointStratumLevel (mixedWeight (adjointSiteWordBlock u)).toNat
          (adjointSiteWordTCount u)) := by
  obtain ⟨hw, hle⟩ := adjointSiteWordWeight_eq u
  rw [adjointSiteWordBlock_weight hkB, lineLevelCost_jointStratumLevel,
    min_eq_left (by omega : adjointSiteWordTCount u ≤ adjointSiteWordYCount u / 2)]
  exact hw

/-- The block cost, sorted by the number of T-states:
`Σ_words 3^T 2^D = Σ_j (w_j - w_(j+1)) · cost(L_j)`. -/
theorem adjointSiteBlockBound_eq_strata (hkB : 2 * k ≤ B) (q : MixedParams) :
    adjointSiteBlockBound B k q = ∑ j ∈ Finset.range ((mixedWeight q).toNat + 1),
      (adjointSiteWordCount B k q j - adjointSiteWordCount B k q (j + 1)) *
        lineLevelCost (mixedWeight q).toNat (jointStratumLevel (mixedWeight q).toNat j) := by
  set F := Finset.univ.filter (fun u : AdjointSiteWord B k => adjointSiteWordBlock u = q)
  have hcount (j : ℕ) :
      adjointSiteWordCount B k q j = (F.filter (fun u => j ≤ adjointSiteWordTCount u)).card := by
    unfold adjointSiteWordCount
    rw [Finset.filter_filter]
  have hfib (j : ℕ) : (F.filter (fun u => adjointSiteWordTCount u = j)).card =
      adjointSiteWordCount B k q j - adjointSiteWordCount B k q (j + 1) := by
    rw [hcount, hcount]
    have hunion : F.filter (fun u => j ≤ adjointSiteWordTCount u) =
        F.filter (fun u => adjointSiteWordTCount u = j) ∪
          F.filter (fun u => j + 1 ≤ adjointSiteWordTCount u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hu, hj⟩
        rcases Nat.eq_or_lt_of_le hj with h | h
        · exact Or.inl ⟨hu, h.symm⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨hu, h⟩ | ⟨hu, h⟩)
        · exact ⟨hu, h.ge⟩
        · exact ⟨hu, by omega⟩
    have hdisj : Disjoint (F.filter (fun u => adjointSiteWordTCount u = j))
        (F.filter (fun u => j + 1 ≤ adjointSiteWordTCount u)) := by
      rw [Finset.disjoint_filter]
      intro u _ h₁ h₂
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    omega
  have hmaps : ∀ u ∈ F, adjointSiteWordTCount u ∈ Finset.range ((mixedWeight q).toNat + 1) := by
    intro u hu
    have hb := (Finset.mem_filter.mp hu).2
    have hy := adjointSiteWordBlock_weight hkB u
    rw [hb] at hy
    have := (adjointSiteWordWeight_eq u).2
    exact Finset.mem_range.mpr (by omega)
  unfold adjointSiteBlockBound
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hfib j, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨hu₁, hu₂⟩ := Finset.mem_filter.mp hu
  rw [adjointSiteWordWeight_eq_stratumCost hkB u, (Finset.mem_filter.mp hu₁).2, hu₂]

/-- The word counts `w_j` are antitone in `j`. -/
theorem adjointSiteWordCount_succ_le (B k : ℕ) (q : MixedParams) (j : ℕ) :
    adjointSiteWordCount B k q (j + 1) ≤ adjointSiteWordCount B k q j := by
  unfold adjointSiteWordCount
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.1, by omega⟩

end

end VOA.DeligneAudit.SL4T
