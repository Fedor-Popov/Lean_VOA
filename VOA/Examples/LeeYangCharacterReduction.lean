import VOA.Examples.LeeYangCharacterCount

/-!
# Reduction of the refined Lee–Yang PBW character to the classical lower bound

`LeeYangTransferAssembly.LeeYangPBWCharacter` asks for the dimension of **every** length step
`G_p L(-22/5,0)_n` of the PBW flag.  With the proved gap-two spanning
(`goodFil_leeYang_eq_gapSpan`) and the proved count (`card_gapWords`):

* `finrank_pieceIn_le` — **upper bound, proved outright**:
  `dim G_p L_n ≤ Σ_{j ∈ [0,2p]} leadingCoefficient n j`;
* `leeYangPBWCharacter_iff_lowerBound` — the refined statement is **equivalent** to the
  unrefined classical lower bound `LeeYangRRLowerBound`:
  `#{gap-two partitions of N} ≤ dim L(-22/5,0)_N` for every `N`
  (equivalently, by the upper bound, the Rogers–Ramanujan character identity
  `dim L(-22/5,0)_N = #{partitions of N into parts ≥ 2 with difference ≥ 2}`);
* `leeYangGapTwoIndependent_of_lowerBound` — the lower bound makes the gap-two words a basis,
  adapted to the length flag.

The lower bound itself is **not** proved in this file: it is the classical Rocha-Caridi /
Feigin–Fuchs character of `L(c_{2,5},0)` combined with the first Rogers–Ramanujan identity,
and it is stated here as the named proposition `LeeYangRRLowerBound`.  It is proved downstream:
`VOA.RRLower.leeYangRRLowerBound_holds` (`LYGramRank.lean`).
-/

namespace VOA.LeeYangCharacter

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYang VOA.LeeYangTransferAssembly
open scoped BigOperators

noncomputable section

/-- The class of a creation word in `L(-22/5,0)`. -/
def lyWord (u : List ℕ) : VirUniv leeYangC ⧸ maxIdealVir leeYangC :=
  (maxIdealVir leeYangC).mkQ (negWordVir leeYangC u)

/-- The gap-two family of energy `N` and length `≤ p`. -/
def lyFamily (N p : ℕ) : (gapWordsLe N p) → VirUniv leeYangC ⧸ maxIdealVir leeYangC :=
  fun u => lyWord u.1

/-- The length step is the span of the gap-two family. -/
theorem goodFil_eq_span_lyFamily (p N : ℕ) :
    goodFil leeYangC p (N : ℤ) = Submodule.span ℂ (Set.range (lyFamily N p)) := by
  rw [goodFil_leeYang_eq_gapSpan]
  apply le_antisymm
  · rw [gapSpan, Submodule.map_span_le]
    rintro _ ⟨u, hu, hE, hl, rfl⟩
    exact Submodule.subset_span ⟨⟨u, mem_gapWordsLe.mpr ⟨hu, hE, hl⟩⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨hg, hE, hl⟩ := mem_gapWordsLe.mp hu
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, hg, hE, hl, rfl⟩)

theorem finrank_pieceIn_eq (p : ℕ) (n : ℤ) :
    Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) =
      Module.finrank ℂ (goodFil leeYangC p n) :=
  (Submodule.comapSubtypeEquivOfLe (goodFil_le_grading leeYangC p n)).finrank_eq

theorem virFil_neg {p : ℕ} {n : ℤ} (hn : n < 0) : virFil leeYangC p n = ⊥ := by
  rw [virFil, Submodule.span_eq_bot]
  rintro _ ⟨w, -, hen, -, rfl⟩
  have : (0 : ℤ) ≤ (energyVir w : ℤ) := Int.natCast_nonneg _
  omega

theorem finrank_pieceIn_neg {p : ℕ} {n : ℤ} (hn : n < 0) :
    Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) = 0 := by
  rw [finrank_pieceIn_eq, goodFil, virFil_neg hn, Submodule.map_bot, finrank_bot]

theorem sum_leadingCoefficient_neg {n : ℤ} (hn : n < 0) (p : ℕ) :
    ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), leadingCoefficient n j = 0 := by
  rw [sum_leadingCoefficient_eq]
  exact Finset.sum_eq_zero fun r _ => gapTwoCoefficient_neg hn r

/-- **The refined upper bound, proved outright.** -/
theorem finrank_pieceIn_le (n : ℤ) (p : ℕ) :
    Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) ≤
      ∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), leadingCoefficient n j := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [finrank_pieceIn_neg hn]; exact Nat.zero_le _
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [finrank_pieceIn_eq, goodFil_eq_span_lyFamily, sum_leadingCoefficient_eq,
      ← card_gapWordsLe]
    have := finrank_range_le_card (R := ℂ) (lyFamily N p)
    simpa [Set.finrank] using this

/-! ## The named lower bound and the equivalence -/

/-- The Rogers–Ramanujan lower bound for the vacuum Lee–Yang module (proved:
`VOA.RRLower.leeYangRRLowerBound_holds`, `LYGramRank.lean`) — at every weight `N`, the number
of partitions of `N` into parts `≥ 2` with adjacent difference `≥ 2` is at most
`dim L(-22/5,0)_N`.  Mathematically this is the Rocha-Caridi
(Feigin–Fuchs) character of `L(c_{2,5},0)` together with the first Rogers–Ramanujan identity. -/
def LeeYangRRLowerBound : Prop :=
  ∀ N : ℕ, (∑ r ∈ Finset.range (N + 1), gapTwoCoefficient (N : ℤ) r) ≤
    Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ))

/-- The classical character identity `dim L(-22/5,0)_N = #{gap-two partitions of N}`. -/
def LeeYangRRCharacter : Prop :=
  ∀ N : ℕ, Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) =
    ∑ r ∈ Finset.range (N + 1), gapTwoCoefficient (N : ℤ) r

/-- The gap-two words of each weight are linearly independent in `L(-22/5,0)`. -/
def LeeYangGapTwoIndependent : Prop :=
  ∀ N : ℕ, LinearIndependent ℂ (lyFamily N N)

theorem goodFil_top (N : ℕ) :
    goodFil leeYangC N (N : ℤ) = (virasoroSimple leeYangC).grading (N : ℤ) :=
  goodFil_eq_grading_of_le leeYangC le_rfl

theorem finrank_span_lyFamily_top (N : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (lyFamily N N))) =
      Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) := by
  rw [← goodFil_eq_span_lyFamily, goodFil_top]

/-- The lower bound makes the spanning gap-two family independent. -/
theorem leeYangGapTwoIndependent_of_lowerBound (h : LeeYangRRLowerBound) :
    LeeYangGapTwoIndependent := by
  intro N
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply le_antisymm
  · rw [Fintype.card_coe, card_gapWordsLe, Set.finrank, finrank_span_lyFamily_top]
    exact h N
  · have := finrank_range_le_card (R := ℂ) (lyFamily N N)
    exact this

/-- Independence gives the refined character at every weight and length. -/
theorem leeYangPBWCharacter_of_independent (h : LeeYangGapTwoIndependent) :
    LeeYangPBWCharacter := by
  intro n p
  rcases lt_or_ge n 0 with hn | hn
  · rw [finrank_pieceIn_neg hn, sum_leadingCoefficient_neg hn]
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [finrank_pieceIn_eq, goodFil_eq_span_lyFamily, sum_leadingCoefficient_eq,
      ← card_gapWordsLe, ← Fintype.card_coe]
    have hsub := gapWordsLe_subset N p
    let incl : (gapWordsLe N p) → (gapWordsLe N N) := fun u => ⟨u.1, hsub u.2⟩
    have hincl : Function.Injective incl := fun u v huv => by
      have h1 : (incl u).1 = (incl v).1 := congrArg Subtype.val huv
      exact Subtype.ext h1
    have hcomp : lyFamily N p = lyFamily N N ∘ incl := rfl
    have hind : LinearIndependent ℂ (lyFamily N p) := by
      rw [hcomp]; exact (h N).comp incl hincl
    exact finrank_span_eq_card hind

theorem lowerBound_of_leeYangPBWCharacter (h : LeeYangPBWCharacter) : LeeYangRRLowerBound := by
  intro N
  have hc := h (N : ℤ) N
  rw [finrank_pieceIn_eq, goodFil_top, sum_leadingCoefficient_eq] at hc
  exact hc.symm.le

/-- **The refined PBW character is equivalent to the classical lower bound.** -/
theorem leeYangPBWCharacter_iff_lowerBound : LeeYangPBWCharacter ↔ LeeYangRRLowerBound :=
  ⟨lowerBound_of_leeYangPBWCharacter,
    fun h => leeYangPBWCharacter_of_independent (leeYangGapTwoIndependent_of_lowerBound h)⟩

/-- The total-dimension upper bound, proved outright. -/
theorem finrank_grading_le (N : ℕ) :
    Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) ≤
      ∑ r ∈ Finset.range (N + 1), gapTwoCoefficient (N : ℤ) r := by
  have := finrank_pieceIn_le (N : ℤ) N
  rwa [finrank_pieceIn_eq, goodFil_top, sum_leadingCoefficient_eq] at this

theorem leeYangRRCharacter_iff_lowerBound : LeeYangRRCharacter ↔ LeeYangRRLowerBound :=
  ⟨fun h N => (h N).symm.le, fun h N => le_antisymm (finrank_grading_le N) (h N)⟩

theorem leeYangPBWCharacter_iff_rrCharacter : LeeYangPBWCharacter ↔ LeeYangRRCharacter :=
  leeYangPBWCharacter_iff_lowerBound.trans leeYangRRCharacter_iff_lowerBound.symm

end

end VOA.LeeYangCharacter
