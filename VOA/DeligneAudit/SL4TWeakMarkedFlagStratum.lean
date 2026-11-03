import VOA.DeligneAudit.SL4TMarkedFlagZeroPointStrata

/-!
# The product stratum of the weak full flag with one double

Let `W` be the weak full flag on `m + 2` roots with common cutoff `m + 1`, a marked group `V`
(`∏ V = 0`, power sums of `V` vanishing from `max m 1` on) and the weak group `U = Vᶜ`. Its
configurations are of two kinds: a zero pair (one root of each group at zero) with one root at
every other point, and a marked root at zero with two marked roots at the double point. For a set
`Y` of roots with complement `Z`, `dim (∏ Z)` is at least the number of configurations with a
point carrying two roots of `Y`:

`a b m! + (b C(b - 1, 2) + c C(b, 2)) (m - 1)!`   with `a = |U ∩ Y|`, `b = |V ∩ Y|`,
`c = |V ∖ Y|`   (`weakMarkedFlag_stratum_finrank_ge`).

With `U = ∅` the weak ring is the unmarked flag with one double
(`weakMarkedFlagIdeal_univ_eq_unmarked`). Otherwise delete a weak root `y`; its layers are the
singly marked flag without doubles (`y` at zero), the weak flag with cutoff lowered by one (`y` at
a simple point) and the doubly marked flag without doubles (`y` alone at the double point).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- With every root marked, the weak ideal is the unmarked ideal with cutoff `h + 1`. -/
theorem weakMarkedFlagIdeal_univ_eq_unmarked (n h : ℕ) (hn : 1 ≤ n) :
    weakMarkedFlagIdeal n Finset.univ h = unmarkedFlagIdeal n (h + 1) := by
  unfold weakMarkedFlagIdeal unmarkedFlagIdeal
  apply le_antisymm
  · refine sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
      (le_sup_right.trans le_sup_left)) ?_
    · apply Ideal.span_le.mpr
      rintro p ⟨S, hS, rfl⟩
      rw [Set.mem_singleton_iff] at hS
      subst hS
      apply (le_sup_left.trans (le_sup_left.trans le_sup_left) :
        fullFlagSymmetricIdeal n ≤ markedFlagIdeal n ∅ (fun _ => h + 1) ∅ 0)
      rw [flagGroupProduct, ← esymm_card_eq_prod]
      exact Ideal.subset_span ⟨n, hn, rfl⟩
    · apply Ideal.span_le.mpr
      rintro p ⟨s, hs, rfl⟩
      apply (le_sup_left.trans (le_sup_left.trans le_sup_left) :
        fullFlagSymmetricIdeal n ≤ markedFlagIdeal n ∅ (fun _ => h + 1) ∅ 0)
      exact psum_mem_fullFlagSymmetricIdeal n s
        (Nat.lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right h 1) hs))
  · refine sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
      (le_sup_right.trans le_sup_left)) ?_
    · rw [Set.image_empty, Ideal.span_empty]
      exact bot_le
    · apply Ideal.span_le.mpr
      rintro p ⟨s, _, rfl⟩
      simp only [flagGroupPowerSum, Finset.sum_empty, SetLike.mem_coe]
      exact Ideal.zero_mem _

/-- The product step with the cutoff written as `N + 1`. -/
theorem productStratum_layers_le_succ {C : Type*} [CommRing C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] {n : ℕ} (r : Fin (n + 1) → C) (y : Fin (n + 1))
    (Z : Finset (Fin (n + 1))) (hy : y ∈ Z) (N : ℕ) (hz : r y ^ (N + 1) = 0) :
    ∑ i ∈ Finset.range N, Module.finrank ℂ ((((Ideal.span
        {∏ j ∈ deletedGroup y Z, r (y.succAbove j)} : Ideal C).restrictScalars ℂ).map
          (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (i + 1))).toLinearMap)) ≤
      Module.finrank ℂ ((Ideal.span {∏ i ∈ Z, r i} : Ideal C).restrictScalars ℂ) := by
  have h := productStratum_layers_le r y Z hy (N + 1) hz
  rwa [Nat.add_sub_cancel] at h

set_option maxHeartbeats 800000 in
-- Three kinds of layer, each transported through a layer isomorphism of a quotient ring.
/-- **The product stratum of the weak flag.** -/
theorem weakMarkedFlag_stratum_finrank_ge (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 2)))
    (hV : V.Nonempty) :
    (Vᶜ ∩ Y).card * (V ∩ Y).card * m.factorial +
        singlyMarkedOneDoubleCount 0 (V ∩ Y).card (V \ Y).card * (m - 1).factorial ≤
      Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
        quotientRoot (weakMarkedFlagIdeal (m + 2) V m) i}).restrictScalars ℂ) := by
  classical
  induction m with
  | zero => omega
  | succ B ih =>
      by_cases hU : V = Finset.univ
      · -- no weak roots: the unmarked flag with one double
        subst hU
        rw [weakMarkedFlagIdeal_univ_eq_unmarked (B + 1 + 2) (B + 1) (by omega)]
        have hprod : (B + 1 + 2 - Yᶜ.card).choose 2 * (B + 1 + 2 - 2).factorial ≤
            Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
              quotientRoot (unmarkedFlagIdeal (B + 1 + 2) (B + 1 + 1)) i}).restrictScalars ℂ) :=
          unmarkedFlag_oneDouble_product_finrank_ge (B + 1 + 2) (by omega) Yᶜ
        refine le_trans (le_of_eq ?_) hprod
        have hy := Finset.card_le_univ Y
        rw [Fintype.card_fin] at hy
        rw [Finset.compl_univ, Finset.empty_inter, Finset.card_empty, zero_mul, zero_mul,
          zero_add, Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, Finset.card_compl,
          Fintype.card_fin, singlyMarkedOneDoubleCount_zero,
          show Y.card + (B + 1 + 2 - Y.card) - 2 = B + 1 by omega,
          show B + 1 + 2 - (B + 1 + 2 - Y.card) = Y.card by omega,
          show B + 1 + 2 - 2 = B + 1 by omega, show B + 1 - 1 = B by omega,
          Nat.factorial_succ]
        ring
      obtain ⟨y₀, hy₀⟩ := exists_notMem_of_ne_univ V hU
      have hk1 : 1 ≤ 1 := le_rfl
      have hk : 2 * 1 ≤ B + 2 := by omega
      change (Vᶜ ∩ Y).card * (V ∩ Y).card * (B + 1).factorial +
          singlyMarkedOneDoubleCount 0 (V ∩ Y).card (V \ Y).card * (B + 1 - 1).factorial ≤
        Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
          quotientRoot (weakMarkedFlagIdeal (B + 3) V (B + 2 - 1)) i}).restrictScalars ℂ)
      set r := quotientRoot (weakMarkedFlagIdeal (B + 3) V (B + 2 - 1)) with hr
      have hcut : ∀ y, r y ^ (B + 2) = 0 := fun y => weakMarkedFlag_cutoff _ _ _ y
      have hcount : ∀ y, y ∉ V →
          (deletedGroup y V)ᶜ ∩ deletedGroup y Y = deletedGroup y (Vᶜ ∩ Y) ∧
            (deletedGroup y V ∩ deletedGroup y Y).card = (V ∩ Y).card ∧
              (deletedGroup y V \ deletedGroup y Y).card = (V \ Y).card ∧
                (deletedGroup y V).Nonempty := by
        intro y hy
        refine ⟨by rw [deletedGroup_inter, deletedGroup_compl], ?_, ?_, ?_⟩
        · rw [← deletedGroup_inter]
          exact deletedGroup_card_of_notMem _ y (fun h => hy (Finset.mem_inter.mp h).1)
        · rw [← deletedGroup_sdiff]
          exact deletedGroup_card_of_notMem _ y (fun h => hy (Finset.mem_sdiff.mp h).1)
        · rw [← Finset.card_pos, deletedGroup_card_of_notMem V y hy]
          exact Finset.card_pos.mpr hV
      -- the lower layers receive the child stratum, the top layer the doubly marked zero pair
      have hlower : ∀ y (hy : y ∉ V) (i : ℕ), i < B →
          Module.finrank ℂ ((Ideal.span {∏ j ∈ (deletedGroup y Y)ᶜ,
              quotientRoot (weakMarkedFlagIdeal (B + 2) (deletedGroup y V) B) j}
              ).restrictScalars ℂ) ≤
            Module.finrank ℂ ((((Ideal.span {∏ j ∈ deletedGroup y Yᶜ, r (y.succAbove j)} :
              Ideal (WeakMarkedFlagRing (B + 3) V (B + 2 - 1))).restrictScalars ℂ).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (i + 1))).toLinearMap)) := by
        intro y hy i hi
        have hl := childProduct_finrank_le_layer r y (i + 1) _ _
          (weakLayerMap_injective_lower B 1 hk1 hk V hV y hy (i + 1) (by omega) (by omega))
          (deletedGroup y Yᶜ)
        rw [← deletedGroup_compl y Y]
        exact hl
      have htop : ∀ y (hy : y ∉ V),
          Module.finrank ℂ ((Ideal.span {∏ j ∈ (deletedGroup y Y)ᶜ,
              quotientRoot (doublyMarkedFlagIdeal (B + 2) (deletedGroup y V) B) j}
              ).restrictScalars ℂ) ≤
            Module.finrank ℂ ((((Ideal.span {∏ j ∈ deletedGroup y Yᶜ, r (y.succAbove j)} :
              Ideal (WeakMarkedFlagRing (B + 3) V (B + 2 - 1))).restrictScalars ℂ).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (B + 1))).toLinearMap)) := by
        intro y hy
        have hl := childProduct_finrank_le_layer r y (B + 2 - 1) _ _
          (weakLayerMap_injective_doubly B 1 hk1 hk V hV y hy) (deletedGroup y Yᶜ)
        rw [← deletedGroup_compl y Y]
        exact hl
      by_cases hcase : ∃ y, y ∉ V ∧ y ∉ Y
      · -- a weak root outside `Y`: the positive layers
        obtain ⟨y, hy, hyY⟩ := hcase
        obtain ⟨haV, hbV, hcV, hV'⟩ := hcount y hy
        have hacard : (deletedGroup y (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ y (fun h => hyY (Finset.mem_inter.mp h).2)
        have hchildCard := stratumCard_sum_le (deletedGroup y V) (deletedGroup y Y)
        rw [haV, hbV, hcV, hacard] at hchildCard
        have hY' : y ∈ Yᶜ := Finset.mem_compl.mpr hyY
        have hsum := productStratum_layers_le_succ r y Yᶜ hY' (B + 1) (hcut y)
        rw [Finset.sum_range_succ] at hsum
        refine le_trans ?_ hsum
        have hpos : ∀ i ∈ Finset.range B,
            (Vᶜ ∩ Y).card * (V ∩ Y).card * B.factorial +
                singlyMarkedOneDoubleCount 0 (V ∩ Y).card (V \ Y).card * (B - 1).factorial ≤
              Module.finrank ℂ ((((Ideal.span {∏ j ∈ deletedGroup y Yᶜ, r (y.succAbove j)} :
                Ideal (WeakMarkedFlagRing (B + 3) V (B + 2 - 1))).restrictScalars ℂ).map
                  (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (i + 1))).toLinearMap)) := by
          intro i hi
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hi; omega
          have hrec := ih hB (deletedGroup y V) (deletedGroup y Y) hV'
          rw [haV, hbV, hcV, hacard] at hrec
          exact hrec.trans (hlower y hy i (Finset.mem_range.mp hi))
        have hz := doublyMarkedFlag_zeroPair_finrank_ge B (deletedGroup y V) (deletedGroup y Y)
        rw [haV, hbV, hacard] at hz
        refine le_trans (le_of_eq ?_) (Nat.add_le_add (Finset.sum_le_sum hpos)
          (hz.trans (htop y hy)))
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, show B + 1 - 1 = B by omega,
          mul_add, factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedOneDoubleCount_eq_zero
            _ _ _ (by omega)), Nat.factorial_succ]
        ring
      · -- every weak root lies in `Y`
        have hUY : ∀ y, y ∉ V → y ∈ Y := fun y hy => by
          by_contra h
          exact hcase ⟨y, hy, h⟩
        set y := y₀
        have hy : y ∉ V := hy₀
        have hyY := hUY y hy
        obtain ⟨haV, hbV, hcV, hV'⟩ := hcount y hy
        have hacard : (deletedGroup y (Vᶜ ∩ Y)).card + 1 = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_mem _ y (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hy, hyY⟩)
        have hchildCard := stratumCard_sum_le (deletedGroup y V) (deletedGroup y Y)
        rw [haV, hbV, hcV] at hchildCard
        have hY' : y ∉ Yᶜ := fun h => (Finset.mem_compl.mp h) hyY
        have hprodeq : ∏ j ∈ deletedGroup y Yᶜ, r (y.succAbove j) = ∏ i ∈ Yᶜ, r i :=
          prod_deletedGroup_of_notMem r Yᶜ y hY'
        have hUY' : (deletedGroup y V)ᶜ ⊆ deletedGroup y Y := by
          intro j hj
          rw [← deletedGroup_compl, mem_deletedGroup] at hj
          rw [mem_deletedGroup]
          exact hUY _ (Finset.mem_compl.mp hj)
        let I : Submodule ℂ (WeakMarkedFlagRing (B + 3) V (B + 2 - 1)) :=
          (Ideal.span {∏ i ∈ Yᶜ, r i}).restrictScalars ℂ
        let W : ℕ → Submodule ℂ (WeakMarkedFlagRing (B + 3) V (B + 2 - 1)) := fun _ => I
        have hW : ∀ j < B + 2, ∀ c ∈ W j, r y ^ j * c ∈
            I ⊔ (Ideal.span {r y ^ (j + 1)}).restrictScalars ℂ := fun j _ c hc =>
          Submodule.mem_sup_left (Ideal.mul_mem_left _ _ hc)
        have hsum := layer_finrank_sum_le (r y) (B + 2) (hcut y) I W hW
        rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hsum
        refine le_trans ?_ hsum
        have h0 : (V ∩ Y).card * (B + 1).factorial ≤ Module.finrank ℂ ((W 0).map
            (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) 0)).toLinearMap) := by
          have hoz := singlyMarkedFlag_omittedZero_finrank_ge (B + 2) (deletedGroup y V)
            (deletedGroup y Y) hV' hUY'
          rw [hbV, ← deletedGroup_compl y Y, show B + 2 - 1 = B + 1 by omega] at hoz
          have hl := childProduct_finrank_le_layer r y (1 - 1) _ _
            (weakLayerMap_injective_singly B 1 hk1 hk V hV y hy) (deletedGroup y Yᶜ)
          rw [hprodeq] at hl
          exact hoz.trans hl
        have hpos : ∀ i ∈ Finset.range B,
            (deletedGroup y (Vᶜ ∩ Y)).card * (V ∩ Y).card * B.factorial +
                singlyMarkedOneDoubleCount 0 (V ∩ Y).card (V \ Y).card * (B - 1).factorial ≤
              Module.finrank ℂ ((W (i + 1)).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (i + 1))).toLinearMap) := by
          intro i hi
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hi; omega
          have hrec := ih hB (deletedGroup y V) (deletedGroup y Y) hV'
          rw [haV, hbV, hcV] at hrec
          have hl := hlower y hy i (Finset.mem_range.mp hi)
          rw [hprodeq] at hl
          exact hrec.trans hl
        have hz : (deletedGroup y (Vᶜ ∩ Y)).card * (V ∩ Y).card * B.factorial ≤
            Module.finrank ℂ ((W (B + 1)).map
              (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r y) (B + 1))).toLinearMap) := by
          have hz := doublyMarkedFlag_zeroPair_finrank_ge B (deletedGroup y V)
            (deletedGroup y Y)
          rw [haV, hbV] at hz
          have hl := htop y hy
          rw [hprodeq] at hl
          exact hz.trans hl
        refine le_trans (le_of_eq ?_) (Nat.add_le_add (Nat.add_le_add
          (Finset.sum_le_sum hpos) h0) hz)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, show B + 1 - 1 = B by omega,
          mul_add, factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedOneDoubleCount_eq_zero
            _ _ _ (by omega)), ← hacard, Nat.factorial_succ]
        ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlagIdeal_univ_eq_unmarked
#print axioms VOA.DeligneAudit.SL4T.productStratum_layers_le_succ
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_stratum_finrank_ge
