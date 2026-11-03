import VOA.DeligneAudit.SL4TSinglyMarkedOneDoubleStratum

/-!
# Strata at the zero point: the omitted zero and the doubly marked zero pair

For a set `Y` of roots with complement `Z`:

* **Omitted zero.** In the singly marked full flag on `n` roots without doubles (cutoff `n - 1`
  on `U = Vᶜ`, `n` on `V`), if `U ⊆ Y` then `dim (∏ Z) ≥ |V ∩ Y| · (n - 1)!`, the number of
  configurations whose marked root at zero lies in `Y`
  (`singlyMarkedFlag_omittedZero_finrank_ge`). Every layer of a root of `U` receives the same
  product; with `U = ∅` it is the product stratum of the unmarked flag without doubles.
* **Doubly marked zero pair.** In the doubly marked full flag on `m + 2` roots without doubles
  (cutoff `m + 1`), `dim (∏ Z) ≥ |U ∩ Y| · |V ∩ Y| · m!`, the number of configurations whose zero
  pair lies in `Y` (`doublyMarkedFlag_zeroPair_finrank_ge`). Delete a first-group root `u`: if
  `u ∉ Y` the positive layers receive the child product; if `U ⊆ Y` the zero layer receives the
  omitted zero and the positive layers the child stratum.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

theorem compl_inter_card_add_inter_card {n : ℕ} (V Y : Finset (Fin n)) :
    (Vᶜ ∩ Y).card + (V ∩ Y).card = Y.card := by
  rw [Finset.inter_comm Vᶜ Y, ← Finset.sdiff_eq_inter_compl, Finset.inter_comm V Y, add_comm]
  exact Finset.card_inter_add_card_sdiff Y V

/-- **The omitted zero.** -/
theorem singlyMarkedFlag_omittedZero_finrank_ge (n : ℕ) (V Y : Finset (Fin n))
    (hV : V.Nonempty) (hUY : Vᶜ ⊆ Y) :
    (V ∩ Y).card * (n - 1).factorial ≤ Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
      quotientRoot (singlyMarkedFlagIdeal n V (n - 1)) i}).restrictScalars ℂ) := by
  classical
  induction n with
  | zero =>
      obtain ⟨a, _⟩ := hV
      exact a.elim0
  | succ n ih =>
      by_cases hU : V = Finset.univ
      · subst hU
        rw [singlyMarkedFlagIdeal_univ_eq (n + 1) (by omega)]
        have hprod := unmarkedFlag_noDouble_product_finrank_ge (n + 1) Yᶜ
        refine le_trans (le_of_eq ?_) hprod
        have hy := Finset.card_le_univ Y
        rw [Fintype.card_fin] at hy
        rw [Finset.univ_inter, Finset.card_compl, Fintype.card_fin,
          show n + 1 - (n + 1 - Y.card) = Y.card by omega]
      obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU
      have huY : u ∈ Y := hUY (Finset.mem_compl.mpr hu)
      obtain ⟨B, rfl⟩ : ∃ B, n = B + 1 := by
        obtain ⟨v, hv⟩ := hV
        refine ⟨n - 1, ?_⟩
        rcases n with _ | n
        · exact absurd ((show u = v from Fin.ext (by omega)) ▸ hv) hu
        · omega
      have hk0 : 2 * 0 ≤ B + 1 := by omega
      change (V ∩ Y).card * (B + 1).factorial ≤ Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
        quotientRoot (singlyMarkedFlagIdeal (B + 2) V (B + 1 - 0)) i}).restrictScalars ℂ)
      set r := quotientRoot (singlyMarkedFlagIdeal (B + 2) V (B + 1 - 0)) with hr
      have hcut : r u ^ (B + 1) = 0 := singlyMarkedFlag_unmarked_cutoff _ _ _ u hu
      have hY' : u ∉ Yᶜ := fun h => (Finset.mem_compl.mp h) huY
      have hprodeq : ∏ j ∈ deletedGroup u Yᶜ, r (u.succAbove j) = ∏ i ∈ Yᶜ, r i :=
        prod_deletedGroup_of_notMem r Yᶜ u hY'
      have hV' : (deletedGroup u V).Nonempty := by
        rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
        exact Finset.card_pos.mpr hV
      have hUY' : (deletedGroup u V)ᶜ ⊆ deletedGroup u Y := by
        intro j hj
        rw [← deletedGroup_compl, mem_deletedGroup] at hj
        rw [mem_deletedGroup]
        exact hUY hj
      have hbV : (deletedGroup u V ∩ deletedGroup u Y).card = (V ∩ Y).card := by
        rw [← deletedGroup_inter]
        exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_inter.mp h).1)
      let I : Submodule ℂ (SinglyMarkedFlagRing (B + 2) V (B + 1 - 0)) :=
        (Ideal.span {∏ i ∈ Yᶜ, r i}).restrictScalars ℂ
      let W : ℕ → Submodule ℂ (SinglyMarkedFlagRing (B + 2) V (B + 1 - 0)) := fun _ => I
      have hW : ∀ j < B + 1, ∀ c ∈ W j, r u ^ j * c ∈
          I ⊔ (Ideal.span {r u ^ (j + 1)}).restrictScalars ℂ := fun j _ c hc =>
        Submodule.mem_sup_left (Ideal.mul_mem_left _ _ hc)
      have hsum := layer_finrank_sum_le (r u) (B + 1) hcut I W hW
      refine le_trans ?_ hsum
      have hterm : ∀ i ∈ Finset.range (B + 1), (V ∩ Y).card * B.factorial ≤
          Module.finrank ℂ ((W i).map
            (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) i)).toLinearMap) := by
        intro i hi
        have hrec := ih (deletedGroup u V) (deletedGroup u Y) hV' hUY'
        rw [hbV, ← deletedGroup_compl u Y, Nat.add_sub_cancel] at hrec
        have hl := childProduct_finrank_le_layer r u i _
          (singlyMarkedLayer_lower_le_ker (B + 1) V (B + 1 - 0) 0 (by omega) (by omega) u hu i
            (Nat.zero_le i))
          (singlyMarkedLayerMap_injective_lower B 0 hk0 V hV u hu i (Nat.zero_le i)
            (by have := Finset.mem_range.mp hi; omega)) (deletedGroup u Yᶜ)
        rw [hprodeq] at hl
        exact hrec.trans hl
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.factorial_succ]
      ring

/-- **The doubly marked zero pair.** -/
theorem doublyMarkedFlag_zeroPair_finrank_ge (m : ℕ) (V Y : Finset (Fin (m + 2))) :
    (Vᶜ ∩ Y).card * (V ∩ Y).card * m.factorial ≤ Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
      quotientRoot (doublyMarkedFlagIdeal (m + 2) V m) i}).restrictScalars ℂ) := by
  classical
  induction m with
  | zero =>
      by_cases hZ : Yᶜ = ∅
      · rw [hZ, Finset.prod_empty, Ideal.span_singleton_one, Submodule.restrictScalars_top,
          finrank_top]
        have hdim := doublyMarkedFlag_finrank_eq 0 0 (le_refl _) V
        rw [fullFlagConfiguration_empty_card, mul_one] at hdim
        refine le_trans ?_ (le_of_eq hdim.symm)
        rw [Nat.factorial_zero, mul_one]
        exact Nat.mul_le_mul (Finset.card_le_card Finset.inter_subset_left)
          (Finset.card_le_card Finset.inter_subset_left)
      · have hY := compl_inter_card_add_inter_card V Y
        have h1 := Finset.card_compl Y
        have h2 : 0 < Yᶜ.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hZ)
        rw [Fintype.card_fin] at h1
        rcases Nat.eq_zero_or_pos (Vᶜ ∩ Y).card with ha | ha
        · rw [ha]
          simp
        · rw [show (V ∩ Y).card = 0 by omega]
          simp
  | succ m ih =>
      change (Vᶜ ∩ Y).card * (V ∩ Y).card * (m + 1).factorial ≤ Module.finrank ℂ
        ((Ideal.span {∏ i ∈ Yᶜ, quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1)) i}
          ).restrictScalars ℂ)
      by_cases hVe : V = ∅
      · subst hVe
        simp
      have hV : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hVe
      by_cases hU : V = Finset.univ
      · subst hU
        simp
      set r := quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1)) with hr
      have hcut : ∀ u, r u ^ (m + 2) = 0 := fun u => doublyMarkedFlag_cutoff _ _ _ u
      have hcount : ∀ u, u ∉ V →
          (deletedGroup u V)ᶜ ∩ deletedGroup u Y = deletedGroup u (Vᶜ ∩ Y) ∧
            (deletedGroup u V ∩ deletedGroup u Y).card = (V ∩ Y).card ∧
              (deletedGroup u V).Nonempty := by
        intro u hu
        refine ⟨by rw [deletedGroup_inter, deletedGroup_compl], ?_, ?_⟩
        · rw [← deletedGroup_inter]
          exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_inter.mp h).1)
        · rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
          exact Finset.card_pos.mpr hV
      by_cases hcase : ∃ u, u ∉ V ∧ u ∉ Y
      · -- a first-group root outside `Y`: the positive layers
        obtain ⟨u, hu, huY⟩ := hcase
        obtain ⟨haV, hbV, hV'⟩ := hcount u hu
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ u (fun h => huY (Finset.mem_inter.mp h).2)
        have hY' : u ∈ Yᶜ := Finset.mem_compl.mpr huY
        have hsum := productStratum_layers_le r u Yᶜ hY' (m + 2) (hcut u)
        rw [show m + 2 - 1 = m + 1 by omega] at hsum
        refine le_trans ?_ hsum
        have hterm : ∀ i ∈ Finset.range (m + 1),
            (Vᶜ ∩ Y).card * (V ∩ Y).card * m.factorial ≤
              Module.finrank ℂ ((((Ideal.span {∏ j ∈ deletedGroup u Yᶜ, r (u.succAbove j)} :
                Ideal (DoublyMarkedFlagRing (m + 3) V (m + 1))).restrictScalars ℂ).map
                  (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap)) := by
          intro i hi
          have hrec := ih (deletedGroup u V) (deletedGroup u Y)
          rw [haV, hbV, hacard, ← deletedGroup_compl u Y] at hrec
          have hl := childProduct_finrank_le_layer r u (i + 1) _ _
            (doublyMarkedZeroLayerMap_injective_lower m V hV u hu (i + 1) (by omega)
              (by have := Finset.mem_range.mp hi; omega)) (deletedGroup u Yᶜ)
          exact hrec.trans hl
        refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.factorial_succ]
        ring
      · -- every first-group root lies in `Y`
        have hUY : ∀ u, u ∉ V → u ∈ Y := fun u hu => by
          by_contra h
          exact hcase ⟨u, hu, h⟩
        obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU
        have huY := hUY u hu
        obtain ⟨haV, hbV, hV'⟩ := hcount u hu
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card + 1 = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_mem _ u (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hu, huY⟩)
        have hY' : u ∉ Yᶜ := fun h => (Finset.mem_compl.mp h) huY
        have hprodeq : ∏ j ∈ deletedGroup u Yᶜ, r (u.succAbove j) = ∏ i ∈ Yᶜ, r i :=
          prod_deletedGroup_of_notMem r Yᶜ u hY'
        have hUY' : (deletedGroup u V)ᶜ ⊆ deletedGroup u Y := by
          intro j hj
          rw [← deletedGroup_compl, mem_deletedGroup] at hj
          rw [mem_deletedGroup]
          exact hUY _ (Finset.mem_compl.mp hj)
        let I : Submodule ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1)) :=
          (Ideal.span {∏ i ∈ Yᶜ, r i}).restrictScalars ℂ
        let W : ℕ → Submodule ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1)) := fun _ => I
        have hW : ∀ j < m + 2, ∀ c ∈ W j, r u ^ j * c ∈
            I ⊔ (Ideal.span {r u ^ (j + 1)}).restrictScalars ℂ := fun j _ c hc =>
          Submodule.mem_sup_left (Ideal.mul_mem_left _ _ hc)
        have hsum := layer_finrank_sum_le (r u) (m + 2) (hcut u) I W hW
        rw [Finset.sum_range_succ'] at hsum
        refine le_trans ?_ hsum
        have h0 : (V ∩ Y).card * (m + 1).factorial ≤ Module.finrank ℂ ((W 0).map
            (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) 0)).toLinearMap) := by
          have hoz := singlyMarkedFlag_omittedZero_finrank_ge (m + 2) (deletedGroup u V)
            (deletedGroup u Y) hV' hUY'
          rw [hbV, ← deletedGroup_compl u Y, show m + 2 - 1 = m + 1 by omega] at hoz
          have hl := childProduct_finrank_le_layer r u 0 _ _
            (doublyMarkedZeroLayerMap_injective_singly m V hV u hu) (deletedGroup u Yᶜ)
          rw [hprodeq] at hl
          exact hoz.trans hl
        have hterm : ∀ i ∈ Finset.range (m + 1),
            (deletedGroup u (Vᶜ ∩ Y)).card * (V ∩ Y).card * m.factorial ≤
              Module.finrank ℂ ((W (i + 1)).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap) := by
          intro i hi
          have hrec := ih (deletedGroup u V) (deletedGroup u Y)
          rw [haV, hbV, ← deletedGroup_compl u Y] at hrec
          have hl := childProduct_finrank_le_layer r u (i + 1) _ _
            (doublyMarkedZeroLayerMap_injective_lower m V hV u hu (i + 1) (by omega)
              (by have := Finset.mem_range.mp hi; omega)) (deletedGroup u Yᶜ)
          rw [hprodeq] at hl
          exact hrec.trans hl
        refine le_trans (le_of_eq ?_) (Nat.add_le_add (Finset.sum_le_sum hterm) h0)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← hacard, Nat.factorial_succ]
        ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.compl_inter_card_add_inter_card
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_omittedZero_finrank_ge
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_zeroPair_finrank_ge
