import VOA.DeligneAudit.SL4TMixedCellData

/-! # The mixed-site spanning filtration by induction on the number of sites -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- At zero sites every polynomial generator vanishes, so scalars span the ring. -/
theorem mixedRing_zero_algebraMap_surjective (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : q.B = 0) : Function.Surjective (algebraMap ℂ (MixedRing q)) := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have hd1 : q.d1 = 0 := by omega
  have hd2 : q.d2 = 0 := by omega
  have hd3 : q.d3 = 0 := by omega
  have he1 : q.e1 = 0 := by omega
  have he2 : q.e2 = 0 := by omega
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hX (v : Fin 5 × ℕ) :
      Ideal.Quotient.mk (mixedIdeal q) (MvPolynomial.X v) = 0 := by
    rcases v with ⟨i, j⟩
    have hl : mixedLengths q i = 0 := by
      fin_cases i <;> simp [mixedLengths, hd1, hd2, hd3, he1, he2]
    have ht := mixedElementary_tail q hq i (j + 1) (by omega)
    simpa only [mixedE, mixedAlphabet, elementary_succ, MvPolynomial.rename_X] using ht
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨c, rfl⟩
  | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      exact ⟨c + d, by rw [map_add, map_add, hc, hd]⟩
  | mul_X p v hp => exact ⟨0, by rw [map_zero, map_mul, hX, mul_zero]⟩

/-- The terminal mixed ring has the single spanning cell of level zero. -/
theorem mixedCellFlag_zero (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : q.B = 0) :
    SpanningChain (mixedTruncationIdeal q) ⊥ ⊤ [0] := by
  have hspan : (ℂ ∙ (1 : MixedRing q)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨c, rfl⟩ := mixedRing_zero_algebraMap_surjective q hq hA hB x
    exact Submodule.mem_span_singleton.mpr ⟨c, by simp [Algebra.smul_def]⟩
  refine .cons 1 0 ?_ ?_ (.nil ⊤)
  · simp only [Submodule.restrictScalars_top, Submodule.restrictScalars_bot,
      bot_sup_eq, hspan]
  · simp only [map_one, pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    simpa only [hA, hB, add_zero, Int.toNat_zero, pow_zero] using
      mixedTruncationIdeal_power q

/-- The recursively ordered cells give an ideal spanning flag with their prescribed levels. -/
theorem mixedCellFlag_recursive (n : ℕ) (q : MixedParams) (hq : MixedValid q)
    (hn : (q.A + q.B).toNat = n) :
    SpanningChain (mixedTruncationIdeal q) ⊥ ⊤ (mixedCellLevels n q) := by
  induction n generalizing q with
  | zero =>
      have hA : q.A = 0 := by have := hq.1; have := hq.2.1; omega
      have hB : q.B = 0 := by have := hq.1; have := hq.2.1; omega
      simpa [mixedCellLevels, mixedCellData, hq, mixedCellLevel] using
        mixedCellFlag_zero q hq hA hB
  | succ n ih =>
      by_cases hB : 1 ≤ q.B
      · rw [mixedCellLevels_b_step n q hq hB]
        rw [← mixedBChain_zero q, ← mixedBChain_top q]
        apply SpanningChain.join_range
        intro i hi
        rw [dif_pos hi]
        let s := mixedBOrder ⟨i, hi⟩
        by_cases hs : MixedValid (mixedBNext q s)
        · exact mixedBState_flag q hq hB ⟨i, hi⟩ hs
            (ih _ hs (by rw [mixedBNext_sites]; have := hq.1; omega))
        · rw [mixedCellLevels_invalid n _ hs, List.map_nil, mixedBChain_step q ⟨i, hi⟩]
          exact SpanningChain.of_zero_state (mixedBStateIdeal q s) (mixedBChain q i)
            (mixedTruncationIdeal q) (mixedBThom q s) (mixedBState_invalid q hq hB s hs)
            (mixedBThom_stateIdeal q hq hB ⟨i, hi⟩)
      · have hB0 : q.B = 0 := by have := hq.2.1; omega
        have hA : 1 ≤ q.A := by omega
        rw [mixedCellLevels_a_step n q hq hB0]
        rw [← mixedAChain_zero q, ← mixedAChain_top q]
        apply SpanningChain.join_range
        intro i hi
        rw [dif_pos hi]
        let s := mixedAOrder ⟨i, hi⟩
        by_cases hs : MixedValid (mixedANext q s)
        · exact mixedAState_flag q hq hA hB0 ⟨i, hi⟩ hs
            (ih _ hs (by rw [mixedANext_sites]; omega))
        · rw [mixedCellLevels_invalid n _ hs, List.map_nil, mixedAChain_step q ⟨i, hi⟩]
          exact SpanningChain.of_zero_state (mixedAStateIdeal q s) (mixedAChain q i)
            (mixedTruncationIdeal q) (mixedAThom q s)
            (mixedAState_invalid q hq hA hB0 s hs)
            (mixedAThom_stateIdeal q hq hA hB0 ⟨i, hi⟩)

/-- The mixed cell filtration in spanning form, with every prefix an ideal. -/
theorem mixedCell_spanningFiltration (q : MixedParams) (hq : MixedValid q) :
    let ns := mixedCellLevels (q.A + q.B).toNat q
    ∃ (v : ℕ → MixedRing q) (F : ℕ → Ideal (MixedRing q)),
      (∀ k ≤ ns.length, (F k).restrictScalars ℂ = generatorPrefix v k) ∧
      F ns.length = ⊤ ∧
      (∀ i < ns.length,
        Polynomial.C (v i) * X ^ (ns.getD i 0) ∈
          (F i).map Polynomial.C ⊔ mixedTruncationIdeal q) :=
  (mixedCellFlag_recursive (q.A + q.B).toNat q hq rfl).prefix_export


/-- Every cell has the block's weight, with doubles contributing one and triples two. -/
theorem mixedCellData_weight (n : ℕ) (q : MixedParams) (hq : MixedValid q)
    (hn : (q.A + q.B).toNat = n) (c : MixedCellCounts) (hc : c ∈ mixedCellData n q) :
    mixedWeight q = (c.1 : ℤ) + 2 * c.2 := by
  induction n generalizing q c with
  | zero =>
      simp only [mixedCellData, if_pos hq, List.mem_singleton] at hc
      subst c
      have hv := hq
      simp only [MixedValid, mixedP, mixedQ] at hv
      simp only [mixedWeight, mixedQ, Nat.cast_zero, mul_zero, add_zero]
      omega
  | succ n ih =>
      by_cases hB : 1 ≤ q.B
      · simp only [mixedCellData, if_pos hq, if_pos hB, List.mem_flatMap] at hc
        obtain ⟨i, hi, hc⟩ := hc
        have hi' : i < 4 := List.mem_range.mp hi
        rw [dif_pos hi'] at hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        let s := mixedBOrder ⟨i, hi'⟩
        have hs : MixedValid (mixedBNext q s) := by
          by_contra hh
          rw [mixedCellData_invalid n _ hh] at hd
          exact List.not_mem_nil hd
        have hw := ih _ hs (by rw [mixedBNext_sites]; have := hq.1; omega) d hd
        rw [mixedBNext_weight q s, hw]
        simp only [mixedCellShift, Nat.cast_add, Nat.cast_zero, add_zero]
        ring
      · have hB0 : q.B = 0 := by have := hq.2.1; omega
        simp only [mixedCellData, if_pos hq, if_neg hB, List.mem_flatMap] at hc
        obtain ⟨i, hi, hc⟩ := hc
        have hi' : i < 9 := List.mem_range.mp hi
        rw [dif_pos hi'] at hc
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        let s := mixedAOrder ⟨i, hi'⟩
        have hs : MixedValid (mixedANext q s) := by
          by_contra hh
          rw [mixedCellData_invalid n _ hh] at hd
          exact List.not_mem_nil hd
        have hw := ih _ hs (by rw [mixedANext_sites]; have := hq.1; omega) d hd
        have hsweight := mixedA_counts_weight s
        have hcast : (mixedAZeroRoots s : ℤ) =
            mixedADoubleCount s + 2 * mixedATripleCount s := by
          exact_mod_cast hsweight.symm
        rw [mixedANext_weight q s, hw, hcast]
        simp only [mixedCellShift, Nat.cast_add]
        ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedRing_zero_algebraMap_surjective
#print axioms VOA.DeligneAudit.SL4T.mixedCellFlag_zero
#print axioms VOA.DeligneAudit.SL4T.mixedCellFlag_recursive
#print axioms VOA.DeligneAudit.SL4T.mixedCell_spanningFiltration

#print axioms VOA.DeligneAudit.SL4T.mixedCellData_weight
