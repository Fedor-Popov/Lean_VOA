import VOA.DeligneAudit.SL4TSinglyMarkedProductLayers

/-!
# The singly marked stratum modulo the unmarked product

Let `S` be the singly marked full flag on `m + 2` roots with one double and `π = ∏ U`,
`U = Vᶜ`. For a set `Y` of roots with complement `Z`, the image of the stratum ideal
`G = (∏ Z, ∏ (V ∩ Y) · c(Z))` in `S/πS` has dimension at least the number of configurations whose
double point carries two roots of `Y`, at least one of them in `U`:

`(b (C(a, 2) + a (b - 1)) + c (C(a, 2) + a b)) (m - 1)!`   with `a = |U ∩ Y|`, `b = |V ∩ Y|`,
`c = |V ∖ Y|`   (`singlyMarkedProduct_stratum_finrank_ge`).

The proof is the induction of the singly marked stratum, run on `S/πS` with its exact layers
(`singlyProductLayerMap_injective_zero`, `singlyProductLayerMap_injective_lower`): the zero layer
receives the omitted-point stratum, the positive layers the stratum of the child `S'/π'S'`.
The count is the full stratum count minus the configurations whose double lies in `V`
(`singlyMarkedOneDoubleCount_eq_add_mixed`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- `b (C(a, 2) + a (b - 1)) + c (C(a, 2) + a b)`: placements of a marked root at zero and two
roots of `Y`, at least one unmarked, at the double point. -/
def singlyMarkedMixedDoubleCount (a b c : ℕ) : ℕ :=
  b * (a.choose 2 + a * (b - 1)) + c * (a.choose 2 + a * b)

theorem singlyMarkedMixedDoubleCount_zero_left (b c : ℕ) :
    singlyMarkedMixedDoubleCount 0 b c = 0 := by
  unfold singlyMarkedMixedDoubleCount
  rw [Nat.choose_eq_zero_of_lt (by norm_num : (0 : ℕ) < 2)]
  ring

theorem singlyMarkedMixedDoubleCount_succ (a b c : ℕ) :
    singlyMarkedMixedDoubleCount (a + 1) b c =
      singlyMarkedMixedDoubleCount a b c + (a * (b + c) + b * (b + c - 1)) := by
  unfold singlyMarkedMixedDoubleCount
  rw [stratumChoose_two_succ]
  rcases b with _ | b
  · simp only [zero_mul, mul_zero, zero_add, add_zero]
    ring
  · rw [show b + 1 - 1 = b by omega, show b + 1 + c - 1 = b + c by omega]
    ring

theorem singlyMarkedMixedDoubleCount_eq_zero (a b c : ℕ) (h : a + b + c ≤ 2) :
    singlyMarkedMixedDoubleCount a b c = 0 := by
  have ha : a ≤ 2 := by omega
  have hb : b ≤ 2 := by omega
  have hc : c ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first | omega | decide

/-- The stratum count splits by whether the double lies in the marked group. -/
theorem singlyMarkedOneDoubleCount_eq_add_mixed (a b c : ℕ) :
    singlyMarkedOneDoubleCount a b c =
      singlyMarkedOneDoubleCount 0 b c + singlyMarkedMixedDoubleCount a b c := by
  induction a with
  | zero => rw [singlyMarkedMixedDoubleCount_zero_left, add_zero]
  | succ a ih =>
      rw [singlyMarkedOneDoubleCount_succ, singlyMarkedMixedDoubleCount_succ, ih]
      ring

/-- **The singly marked stratum modulo the unmarked product.** -/
theorem singlyMarkedProduct_stratum_finrank_ge (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 2))) (hV : V.Nonempty) :
    singlyMarkedMixedDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card * (m - 1).factorial ≤
      Module.finrank ℂ ((omittedPointStratumIdeal (singlyMarkedProductIdeal (m + 2) V m) V Y
        ).restrictScalars ℂ) := by
  classical
  induction m with
  | zero => omega
  | succ B ih =>
      by_cases hU : V = Finset.univ
      · subst hU
        rw [Finset.compl_univ, Finset.empty_inter, Finset.card_empty,
          singlyMarkedMixedDoubleCount_zero_left, zero_mul]
        exact Nat.zero_le _
      obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU
      change singlyMarkedMixedDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card *
          (B + 1 - 1).factorial ≤
        Module.finrank ℂ ((omittedPointStratumIdeal
          (singlyMarkedProductIdeal (B + 3) V (B + 1)) V Y).restrictScalars ℂ)
      set r := quotientRoot (singlyMarkedProductIdeal (B + 3) V (B + 1)) with hr
      have hVprod : ∏ i ∈ V, r i = 0 := singlyMarkedProduct_product_zero _ _ _
      have hcut : r u ^ (B + 1) = 0 := singlyMarkedProduct_unmarked_cutoff _ _ _ u hu
      have hV' : (deletedGroup u V).Nonempty := by
        rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
        exact Finset.card_pos.mpr hV
      have hbV : (deletedGroup u V ∩ deletedGroup u Y).card = (V ∩ Y).card := by
        rw [← deletedGroup_inter]
        exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_inter.mp h).1)
      have hcV : (deletedGroup u V \ deletedGroup u Y).card = (V \ Y).card := by
        rw [← deletedGroup_sdiff]
        exact deletedGroup_card_of_notMem _ u (fun h => hu (Finset.mem_sdiff.mp h).1)
      have haV : (deletedGroup u V)ᶜ ∩ deletedGroup u Y = deletedGroup u (Vᶜ ∩ Y) := by
        rw [deletedGroup_inter, deletedGroup_compl]
      have hchildCard := stratumCard_sum_le (deletedGroup u V) (deletedGroup u Y)
      -- the positive layers receive the child stratum of `S'/π'S'`
      have hlayer : ∀ i, i < B → Module.finrank ℂ ((omittedPointStratumIdeal
            (singlyMarkedProductIdeal (B + 2) (deletedGroup u V) B) (deletedGroup u V)
              (deletedGroup u Y)).restrictScalars ℂ) ≤
          Module.finrank ℂ (((Ideal.span {∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j),
            (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
              groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ}
              ).restrictScalars ℂ).map
            (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap) :=
        fun i hi => stratumPair_finrank_le_layer r u (i + 1) _
          (singlyProductLayer_lower_le_ker (B + 2) V (B + 1) u hu 1 (by omega) (by omega)
            (i + 1) (by omega) (by omega))
          (singlyProductLayerMap_injective_lower B V hV u hu (i + 1) (by omega) (by omega)) _ _
      by_cases huY : u ∈ Y
      · -- `u ∈ Y`: every layer receives the same two generators
        have hgen := stratumPair_deleted_eq_of_mem r V Y u hu huY
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card + 1 = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_mem _ u (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hu, huY⟩)
        set I := omittedPointStratumIdeal (singlyMarkedProductIdeal (B + 3) V (B + 1)) V Y
          with hI
        let W : ℕ → Submodule ℂ (SinglyMarkedProductRing (B + 3) V (B + 1)) :=
          fun _ => I.restrictScalars ℂ
        have hW : ∀ j < B + 1, ∀ c ∈ W j, r u ^ j * c ∈
            I.restrictScalars ℂ ⊔ (Ideal.span {r u ^ (j + 1)}).restrictScalars ℂ :=
          fun j _ c hc => Submodule.mem_sup_left (I.mul_mem_left _ hc)
        have hsum := layer_finrank_sum_le (r u) (B + 1) hcut _ W hW
        rw [Finset.sum_range_succ'] at hsum
        refine le_trans ?_ hsum
        -- the zero layer: the omitted-point stratum of the child without doubles
        have h0 : ((deletedGroup u (Vᶜ ∩ Y)).card * ((V ∩ Y).card + (V \ Y).card) +
            (V ∩ Y).card * ((V ∩ Y).card + (V \ Y).card - 1)) * B.factorial ≤
            Module.finrank ℂ ((W 0).map
              (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) 0)).toLinearMap) := by
          have hop := singlyMarkedFlag_omittedPoint_finrank_ge (B + 2) (deletedGroup u V)
            (deletedGroup u Y) hV'
          have hl := stratumPair_finrank_le_layer r u 0 _
            (singlyProductLayer_same_le_ker (B + 2) V (B + 1) u hu 0)
            (singlyProductLayerMap_injective_zero B V hV u hu) (deletedGroup u V)
            (deletedGroup u Y)
          rw [hgen] at hl
          have hq : (deletedGroup u V).card = (V ∩ Y).card + (V \ Y).card := by
            rw [deletedGroup_card_of_notMem V u hu, Finset.card_inter_add_card_sdiff]
          rw [haV, hbV, hq, show B + 2 - 2 = B by omega] at hop
          exact hop.trans hl
        have hpos : ∀ i ∈ Finset.range B,
            singlyMarkedMixedDoubleCount (deletedGroup u (Vᶜ ∩ Y)).card (V ∩ Y).card
                (V \ Y).card * (B - 1).factorial ≤
              Module.finrank ℂ ((W (i + 1)).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap) := by
          intro i hi
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hi; omega
          have hrec := ih hB (deletedGroup u V) (deletedGroup u Y) hV'
          rw [haV, hbV, hcV] at hrec
          have hl := hlayer i (Finset.mem_range.mp hi)
          rw [hgen] at hl
          exact hrec.trans hl
        refine le_trans (le_of_eq ?_) (Nat.add_le_add (Finset.sum_le_sum hpos) h0)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedMixedDoubleCount_eq_zero _ _ _
            (by rw [haV, hbV, hcV] at hchildCard; omega)),
          ← hacard, singlyMarkedMixedDoubleCount_succ, show B + 1 - 1 = B by omega]
        ring
      · -- `u ∉ Y`: the stratum lies in `u (S/πS)`
        have hJ := stratumPair_deleted_mul_mem r V Y u hVprod hu huY
        have hsum := pairStratum_layers_le (r u) (B + 1) hcut
          (omittedPointStratumIdeal (singlyMarkedProductIdeal (B + 3) V (B + 1)) V Y) _ hJ
        rw [Nat.add_sub_cancel] at hsum
        refine le_trans ?_ hsum
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ u (fun h => huY (Finset.mem_inter.mp h).2)
        have hpos : ∀ i ∈ Finset.range B,
            singlyMarkedMixedDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card *
                (B - 1).factorial ≤
              Module.finrank ℂ (((Ideal.span {∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j),
                (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
                  groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ}
                  ).restrictScalars ℂ).map
                (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap) := by
          intro i hi
          have hB : 1 ≤ B := by have := Finset.mem_range.mp hi; omega
          have hrec := ih hB (deletedGroup u V) (deletedGroup u Y) hV'
          rw [haV, hbV, hcV, hacard] at hrec
          exact hrec.trans (hlayer i (Finset.mem_range.mp hi))
        refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hpos)
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul,
          factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedMixedDoubleCount_eq_zero _ _ _
            (by rw [haV, hbV, hcV, hacard] at hchildCard; omega)),
          show B + 1 - 1 = B by omega]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_zero_left
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedMixedDoubleCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_eq_add_mixed
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedProduct_stratum_finrank_ge
