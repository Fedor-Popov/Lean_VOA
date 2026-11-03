import VOA.DeligneAudit.SL4TSinglyMarkedOmittedPointBound

/-!
# The singly marked stratum with one double

Let `S` be the singly marked full flag on `m + 2` roots with one double: cutoff `m` on the first
group `U = Vᶜ` and `m + 1` on the marked group `V`. For a set `Y` of roots with complement `Z`,
the stratum ideal is `(∏ Z, ∏ (V ∩ Y) · c(Z))` (`omittedPointStratumIdeal`), `c(Z)` the subleading
coefficient. Its dimension is at least the number of configurations whose double point carries
two roots of `Y`:

`(b · C(a + b - 1, 2) + c · C(a + b, 2)) · (m - 1)!`   with `a = |U ∩ Y|`, `b = |V ∩ Y|`,
`c = |V ∖ Y|`   (`singlyMarkedFlag_oneDouble_stratum_finrank_ge`).

The count: a configuration puts one marked root at zero, two roots at the double point and the
other `m - 1` roots at distinct simple points; the root at zero lies in `V ∩ Y` or in `V ∖ Y`.

The proof is by induction on `m`. With every root marked it is the product stratum of the
unmarked flag with one double. Otherwise delete a first-group root `u`:

* `u ∉ Y`: both generators lie in `u S`, and the positive layers (lowered cutoff) receive the
  child stratum (`stratumPair_deleted_mul_mem`);
* `u ∈ Y`: the generators do not involve `u` (`stratumPair_deleted_eq_of_mem`); the zero layer
  (same cutoff, no double left) receives the omitted-point stratum, and the positive layers the
  child stratum.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- With every root marked, the singly marked ideal is the unmarked ideal with cutoff `h + 1`. -/
theorem singlyMarkedFlagIdeal_univ_eq_unmarked (n h : ℕ) (hn : 1 ≤ n) :
    singlyMarkedFlagIdeal n Finset.univ h = unmarkedFlagIdeal n (h + 1) := by
  have hcut : singlyMarkedCutoff (Finset.univ : Finset (Fin n)) h = fun _ => h + 1 := by
    funext i
    simp [singlyMarkedCutoff]
  unfold singlyMarkedFlagIdeal unmarkedFlagIdeal
  rw [hcut]
  apply le_antisymm
  · refine sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
      (le_sup_right.trans le_sup_left)) le_sup_right
    apply Ideal.span_le.mpr
    rintro p ⟨S, hS, rfl⟩
    rw [Set.mem_singleton_iff] at hS
    subst hS
    apply (le_sup_left.trans (le_sup_left.trans le_sup_left) :
      fullFlagSymmetricIdeal n ≤ markedFlagIdeal n ∅ (fun _ => h + 1) ∅ 0)
    rw [flagGroupProduct, ← esymm_card_eq_prod]
    exact Ideal.subset_span ⟨n, hn, rfl⟩
  · refine sup_le (sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
      (le_sup_right.trans le_sup_left)) le_sup_right
    rw [Set.image_empty, Ideal.span_empty]
    exact bot_le

theorem deletedGroup_sdiff {n : ℕ} (u : Fin (n + 1)) (S T : Finset (Fin (n + 1))) :
    deletedGroup u (S \ T) = deletedGroup u S \ deletedGroup u T := by
  ext j
  simp [deletedGroup]

/-- The three parts `Vᶜ ∩ Y`, `V ∩ Y`, `V ∖ Y` are disjoint. -/
theorem stratumCard_sum_le {n : ℕ} (V Y : Finset (Fin n)) :
    (Vᶜ ∩ Y).card + (V ∩ Y).card + (V \ Y).card ≤ n := by
  have h1 := Finset.card_inter_add_card_sdiff V Y
  have h2 : (Vᶜ ∩ Y).card ≤ Vᶜ.card := Finset.card_le_card Finset.inter_subset_left
  have h3 := Finset.card_compl V
  have h4 := Finset.card_le_univ V
  rw [Fintype.card_fin] at h3 h4
  omega

/-! ### The two generators under a deletion -/

section Generators

variable {C : Type*} [CommRing C] {n : ℕ} (r : Fin (n + 1) → C) (V Y : Finset (Fin (n + 1)))
  (u : Fin (n + 1))

/-- Deleting a first-group root `u ∉ Y` of a group with `∏ V = 0`: `u` times the child generators
lies in the parent stratum ideal. -/
theorem stratumPair_deleted_mul_mem (hVprod : ∏ i ∈ V, r i = 0) (hu : u ∉ V) (huY : u ∉ Y)
    (c : C) (hc : c ∈ Ideal.span {∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j),
      (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
        groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ}) :
    r u * c ∈ Ideal.span {∏ i ∈ Yᶜ, r i,
      (∏ i ∈ V ∩ Y, r i) * groupSubtopCoefficient r Yᶜ} := by
  classical
  set I := Ideal.span {∏ i ∈ Yᶜ, r i, (∏ i ∈ V ∩ Y, r i) * groupSubtopCoefficient r Yᶜ}
    with hIgen
  have hY' : u ∈ Yᶜ := Finset.mem_compl.mpr huY
  have hs : ∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j) =
      ∏ i ∈ V ∩ Y, r i := by
    rw [← deletedGroup_inter]
    exact prod_deletedGroup_of_notMem r (V ∩ Y) u (fun h => hu (Finset.mem_inter.mp h).1)
  have hzero : (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
      ∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j) = 0 := by
    rw [← Finset.prod_union (Finset.disjoint_left.mpr fun j hj hj' =>
      (Finset.mem_compl.mp hj') (Finset.mem_inter.mp hj).2)]
    apply prod_eq_zero_of_subset (fun j => r (u.succAbove j)) _
      ((prod_deletedGroup_of_notMem r V u hu).trans hVprod)
    intro j hj
    by_cases hjY : j ∈ deletedGroup u Y
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hj, hjY⟩)
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hjY)
  obtain ⟨s, t, rfl⟩ := Ideal.mem_span_pair.mp hc
  have hm1 : r u * ∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j) ∈ I := by
    rw [← deletedGroup_compl, ← prod_eq_mul_deletedGroup_of_mem r Yᶜ u hY', hIgen]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hm2 : r u * ((∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
      groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ) ∈ I := by
    by_cases hne : (deletedGroup u Yᶜ).Nonempty
    · have hsub := groupSubtopCoefficient_deleted_of_mem r Yᶜ u hY' hne
      have htop := groupElementaryPolynomial_coeff_card (fun j => r (u.succAbove j))
        (deletedGroup u Y)ᶜ
      rw [deletedGroup_compl] at hsub
      have heq : r u * ((∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
          groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ) =
          -((∏ i ∈ V ∩ Y, r i) * groupSubtopCoefficient r Yᶜ) +
            (-1) ^ ((deletedGroup u Y)ᶜ).card *
              ((∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
                ∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j)) := by
        rw [hsub, htop, ← hs]
        ring
      rw [heq, hzero, mul_zero, add_zero, hIgen]
      exact I.neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    · have hYu : ∏ i ∈ Yᶜ, r i = r u := by
        rw [prod_eq_mul_deletedGroup_of_mem r Yᶜ u hY',
          Finset.not_nonempty_iff_eq_empty.mp hne, Finset.prod_empty, mul_one]
      rw [← hYu, hIgen]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  rw [mul_add, mul_left_comm, mul_left_comm (r u) t]
  exact I.add_mem (I.mul_mem_left _ hm1) (I.mul_mem_left _ hm2)

/-- Deleting a first-group root `u ∈ Y` leaves the two generators unchanged. -/
theorem stratumPair_deleted_eq_of_mem (hu : u ∉ V) (huY : u ∈ Y) :
    Ideal.span {∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j),
      (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
        groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ} =
      Ideal.span {∏ i ∈ Yᶜ, r i, (∏ i ∈ V ∩ Y, r i) * groupSubtopCoefficient r Yᶜ} := by
  have hY' : u ∉ Yᶜ := fun h => (Finset.mem_compl.mp h) huY
  rw [← deletedGroup_compl, prod_deletedGroup_of_notMem r Yᶜ u hY', ← deletedGroup_inter,
    prod_deletedGroup_of_notMem r (V ∩ Y) u (fun h => hu (Finset.mem_inter.mp h).1),
    groupSubtopCoefficient_deleted_of_notMem r Yᶜ u hY']

end Generators

/-- Through an injective layer map, the child stratum ideal is at most as large as the image in
the layer of the ideal generated by the evaluated generators. -/
theorem stratumPair_finrank_le_layer {C : Type*} [CommRing C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] {n : ℕ} (r : Fin (n + 1) → C) (u : Fin (n + 1)) (i : ℕ)
    (I' : Ideal (MvPolynomial (Fin n) ℂ))
    (hI' : I' ≤ RingHom.ker (aeval (deletedLayerRoot r u i)).toRingHom)
    (hinj : Function.Injective (deletedLayerMap r u i I' hI')) (V' Y' : Finset (Fin n)) :
    Module.finrank ℂ ((omittedPointStratumIdeal I' V' Y').restrictScalars ℂ) ≤
      Module.finrank ℂ (((Ideal.span {∏ j ∈ Y'ᶜ, r (u.succAbove j),
        (∏ j ∈ V' ∩ Y', r (u.succAbove j)) *
          groupSubtopCoefficient (fun j => r (u.succAbove j)) Y'ᶜ}).restrictScalars ℂ).map
        (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) i)).toLinearMap) := by
  have hl := childPair_finrank_le_layer r u i I' hI' hinj (∏ j ∈ Y'ᶜ, X j)
    ((∏ j ∈ V' ∩ Y', X j) * groupSubtopCoefficient X Y'ᶜ)
  have hg := aeval_omittedPointGenerators (fun j => r (u.succAbove j)) V' Y'
  rw [hg.1, hg.2, ← omittedPointStratumIdeal_eq_span] at hl
  exact hl

/-! ### The configuration count -/

/-- The number of placements of a marked root at zero and two roots of `Y` at the double point:
`b · C(a + b - 1, 2) + c · C(a + b, 2)`, where `a = |U ∩ Y|`, `b = |V ∩ Y|`, `c = |V ∖ Y|`. -/
def singlyMarkedOneDoubleCount (a b c : ℕ) : ℕ :=
  b * (a + b - 1).choose 2 + c * (a + b).choose 2

theorem stratumChoose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

/-- Without first-group roots in `Y`, the count is `(b + c - 2) · C(b, 2)`. -/
theorem singlyMarkedOneDoubleCount_zero (b c : ℕ) :
    singlyMarkedOneDoubleCount 0 b c = (b + c - 2) * b.choose 2 := by
  unfold singlyMarkedOneDoubleCount
  rw [Nat.zero_add]
  rcases Nat.lt_or_ge b 2 with hb | hb
  · rw [Nat.choose_eq_zero_of_lt hb, Nat.choose_eq_zero_of_lt (by omega : b - 1 < 2)]
    simp
  · obtain ⟨z, rfl⟩ : ∃ z, b = z + 2 := ⟨b - 2, by omega⟩
    have h := Nat.choose_mul_succ_eq (z + 1) 2
    rw [show z + 1 + 1 - 2 = z by omega, show z + 1 + 1 = z + 2 by ring] at h
    rw [show z + 2 - 1 = z + 1 by omega, show z + 2 + c - 2 = z + c by omega]
    calc (z + 2) * (z + 1).choose 2 + c * (z + 2).choose 2
        = (z + 1).choose 2 * (z + 2) + c * (z + 2).choose 2 := by ring
      _ = (z + 2).choose 2 * z + c * (z + 2).choose 2 := by rw [h]
      _ = (z + c) * (z + 2).choose 2 := by ring

/-- Moving one root of `U ∩ Y`: the count grows by `a (b + c) + b (b + c - 1)`, the
omitted-point count of the zero layer. -/
theorem singlyMarkedOneDoubleCount_succ (a b c : ℕ) :
    singlyMarkedOneDoubleCount (a + 1) b c =
      singlyMarkedOneDoubleCount a b c + (a * (b + c) + b * (b + c - 1)) := by
  unfold singlyMarkedOneDoubleCount
  rcases b with _ | b
  · rw [show a + 1 + 0 = a + 1 by ring, show a + 0 = a by ring, stratumChoose_two_succ]
    simp only [zero_mul, zero_add, add_zero]
    ring
  · rw [show a + 1 + (b + 1) - 1 = a + b + 1 by omega, show a + (b + 1) - 1 = a + b by omega,
      show a + 1 + (b + 1) = a + b + 1 + 1 by ring, show a + (b + 1) = a + b + 1 by ring,
      show b + 1 + c - 1 = b + c by omega, stratumChoose_two_succ (a + b + 1),
      stratumChoose_two_succ (a + b)]
    ring

/-- With at most two roots in `Y ∪ V`, no configuration has its double inside `Y`. -/
theorem singlyMarkedOneDoubleCount_eq_zero (a b c : ℕ) (h : a + b + c ≤ 2) :
    singlyMarkedOneDoubleCount a b c = 0 := by
  unfold singlyMarkedOneDoubleCount
  rcases (show a + b ≤ 1 ∨ (a + b = 2 ∧ c = 0) by omega) with h1 | ⟨h1, h2⟩
  · rw [Nat.choose_eq_zero_of_lt (by omega : a + b - 1 < 2),
      Nat.choose_eq_zero_of_lt (by omega : a + b < 2)]
    simp
  · rw [h1, h2, Nat.choose_eq_zero_of_lt (show (2 : ℕ) - 1 < 2 by norm_num)]
    simp

theorem factorial_mul_pred_of_zero (B x : ℕ) (hx : B = 0 → x = 0) :
    B * (x * (B - 1).factorial) = x * B.factorial := by
  rcases B with _ | B
  · simp [hx rfl]
  · rw [Nat.factorial_succ, Nat.add_sub_cancel]
    ring

/-! ### The stratum bound -/

/-- **The singly marked stratum with one double.** -/
theorem singlyMarkedFlag_oneDouble_stratum_finrank_ge (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 2))) (hV : V.Nonempty) :
    singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card * (m - 1).factorial ≤
      Module.finrank ℂ ((omittedPointStratumIdeal (singlyMarkedFlagIdeal (m + 2) V m) V Y
        ).restrictScalars ℂ) := by
  classical
  induction m with
  | zero => omega
  | succ B ih =>
      by_cases hU : V = Finset.univ
      · -- every root marked: the product stratum of the unmarked flag with one double
        subst hU
        rw [singlyMarkedFlagIdeal_univ_eq_unmarked (B + 1 + 2) (B + 1) (by omega)]
        have hprod : (B + 1 + 2 - Yᶜ.card).choose 2 * (B + 1 + 2 - 2).factorial ≤
            Module.finrank ℂ ((Ideal.span {∏ i ∈ Yᶜ,
              quotientRoot (unmarkedFlagIdeal (B + 1 + 2) (B + 1 + 1)) i}).restrictScalars ℂ) :=
          unmarkedFlag_oneDouble_product_finrank_ge (B + 1 + 2) (by omega) Yᶜ
        have hmono : (Ideal.span {∏ i ∈ Yᶜ,
            quotientRoot (unmarkedFlagIdeal (B + 1 + 2) (B + 1 + 1)) i}).restrictScalars ℂ ≤
            (omittedPointStratumIdeal (unmarkedFlagIdeal (B + 1 + 2) (B + 1 + 1))
              Finset.univ Y).restrictScalars ℂ := fun x hx =>
          Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) hx
        refine le_trans (le_of_eq ?_) (hprod.trans (Submodule.finrank_mono hmono))
        have hy := Finset.card_le_univ Y
        rw [Fintype.card_fin] at hy
        rw [Finset.compl_univ, Finset.empty_inter, Finset.card_empty, Finset.univ_inter,
          ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
          singlyMarkedOneDoubleCount_zero,
          show Y.card + (B + 1 + 2 - Y.card) - 2 = B + 1 by omega,
          show B + 1 + 2 - (B + 1 + 2 - Y.card) = Y.card by omega,
          show B + 1 + 2 - 2 = B + 1 by omega, show B + 1 - 1 = B by omega,
          Nat.factorial_succ]
        ring
      obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU
      have hk : 2 * 1 ≤ B + 1 + 1 := by omega
      change singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card *
          (B + 1 - 1).factorial ≤
        Module.finrank ℂ ((omittedPointStratumIdeal
          (singlyMarkedFlagIdeal (B + 1 + 2) V (B + 1 + 1 - 1)) V Y).restrictScalars ℂ)
      set r := quotientRoot (singlyMarkedFlagIdeal (B + 1 + 2) V (B + 1 + 1 - 1)) with hr
      have hVprod : ∏ i ∈ V, r i = 0 := singlyMarkedFlag_product_zero _ _ _
      have hcut : r u ^ (B + 1) = 0 := singlyMarkedFlag_unmarked_cutoff _ _ _ u hu
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
      -- the positive layers receive the child stratum
      have hlayer : ∀ i, i < B → Module.finrank ℂ ((omittedPointStratumIdeal
            (singlyMarkedFlagIdeal (B + 2) (deletedGroup u V) B) (deletedGroup u V)
              (deletedGroup u Y)).restrictScalars ℂ) ≤
          Module.finrank ℂ (((Ideal.span {∏ j ∈ (deletedGroup u Y)ᶜ, r (u.succAbove j),
            (∏ j ∈ deletedGroup u V ∩ deletedGroup u Y, r (u.succAbove j)) *
              groupSubtopCoefficient (fun j => r (u.succAbove j)) (deletedGroup u Y)ᶜ}
              ).restrictScalars ℂ).map
            (Ideal.Quotient.mkₐ ℂ (rootPowerLayerIdeal (r u) (i + 1))).toLinearMap) :=
        fun i hi => stratumPair_finrank_le_layer r u (i + 1) _
          (singlyMarkedLayer_lower_le_ker (B + 1 + 1) V (B + 1 + 1 - 1) 1 (by omega) (by omega)
            u hu (i + 1) (by omega))
          (singlyMarkedLayerMap_injective_lower (B + 1) 1 hk V hV u hu (i + 1) (by omega)
            (by omega)) _ _
      by_cases huY : u ∈ Y
      · -- `u ∈ Y`: every layer receives the same two generators
        have hgen := stratumPair_deleted_eq_of_mem r V Y u hu huY
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card + 1 = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_mem _ u (Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hu, huY⟩)
        set I := omittedPointStratumIdeal (singlyMarkedFlagIdeal (B + 1 + 2) V (B + 1 + 1 - 1))
          V Y with hI
        let W : ℕ → Submodule ℂ (SinglyMarkedFlagRing (B + 1 + 2) V (B + 1 + 1 - 1)) :=
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
            (singlyMarkedLayer_same_le_ker (B + 1 + 1) V (B + 1 + 1 - 1) u hu 0)
            (singlyMarkedLayerMap_injective_same (B + 1) 1 hk V hV u hu 0 (by omega)
              (by omega)) (deletedGroup u V) (deletedGroup u Y)
          rw [hgen] at hl
          have hq : (deletedGroup u V).card = (V ∩ Y).card + (V \ Y).card := by
            rw [deletedGroup_card_of_notMem V u hu, Finset.card_inter_add_card_sdiff]
          rw [haV, hbV, hq, show B + 2 - 2 = B by omega] at hop
          exact hop.trans hl
        have hpos : ∀ i ∈ Finset.range B,
            singlyMarkedOneDoubleCount (deletedGroup u (Vᶜ ∩ Y)).card (V ∩ Y).card
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
          factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedOneDoubleCount_eq_zero _ _ _
            (by rw [haV, hbV, hcV] at hchildCard; omega)),
          ← hacard, singlyMarkedOneDoubleCount_succ, show B + 1 - 1 = B by omega]
        ring
      · -- `u ∉ Y`: the stratum lies in `u S`
        have hJ := stratumPair_deleted_mul_mem r V Y u hVprod hu huY
        have hsum := pairStratum_layers_le (r u) (B + 1) hcut
          (omittedPointStratumIdeal (singlyMarkedFlagIdeal (B + 1 + 2) V (B + 1 + 1 - 1)) V Y)
          _ hJ
        rw [Nat.add_sub_cancel] at hsum
        refine le_trans ?_ hsum
        have hacard : (deletedGroup u (Vᶜ ∩ Y)).card = (Vᶜ ∩ Y).card :=
          deletedGroup_card_of_notMem _ u (fun h => huY (Finset.mem_inter.mp h).2)
        have hpos : ∀ i ∈ Finset.range B,
            singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card *
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
          factorial_mul_pred_of_zero B _ (fun hB => singlyMarkedOneDoubleCount_eq_zero _ _ _
            (by rw [haV, hbV, hcV, hacard] at hchildCard; omega)),
          show B + 1 - 1 = B by omega]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlagIdeal_univ_eq_unmarked
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_sdiff
#print axioms VOA.DeligneAudit.SL4T.stratumCard_sum_le
#print axioms VOA.DeligneAudit.SL4T.stratumPair_deleted_mul_mem
#print axioms VOA.DeligneAudit.SL4T.stratumPair_deleted_eq_of_mem
#print axioms VOA.DeligneAudit.SL4T.stratumPair_finrank_le_layer
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount
#print axioms VOA.DeligneAudit.SL4T.stratumChoose_two_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_succ
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedOneDoubleCount_eq_zero
#print axioms VOA.DeligneAudit.SL4T.factorial_mul_pred_of_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_oneDouble_stratum_finrank_ge
