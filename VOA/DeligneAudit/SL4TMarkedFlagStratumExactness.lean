import VOA.DeligneAudit.SL4TMarkedFlagStratumDeformation

/-!
# The marked full-flag strata with one double are exactly their point algebras

Let `C` be the singly marked full flag on `m + 2` roots (cutoffs `m` on `U`, `m + 1` on the marked
group `V`) or the doubly marked full flag on `m + 3` roots (cutoff `m + 1`), `m ≥ 1`, so that the
configurations have one doubled site. For a set `Y` of roots with complement `Z ≠ ∅`:

* singly marked, `G_1 = (∏ Z, ∏ (V ∩ Y) · c(Z))` (`singlyMarkedSelectedStratumIdeal`);
* doubly marked, `G_1 = (∏ Z, c(Z))` (`doublyMarkedOneSelectedStratumIdeal`) and
  `G_2 = ((∏ Z)²)` (`doublyMarkedTwoSelectedStratumIdeal`).

These are the stratum ideals in complement form (`jointTopIdeal_one_eq_pair`,
`jointTopIdeal_one_eq_pair_of_zero`, `jointTopIdeal_two_eq_sq_of_zero`). The polynomial stratum
ideal (flag relations plus the generators of `G_j`) lies below the leading-relation ideal of the
configurations with fewer than `j` selected doubles (the deformation, `*_le`); the lower bound for
`dim G_j`, the exact dimension of `C` and the configuration count close the gap, so the two ideals
are **equal** (`*_eq`) and `dim C/G_j` is the number of configurations with fewer than `j` selected
doubles (`*_finrank`). This is the identification `C/G_j ≅ gr C[X_{<j}]` of Theorem 5.5, as linear
spaces, for all parameters.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

theorem fullFlagSymmetricIdeal_le_markedFlagIdeal (n : ℕ) (marked : Set (Finset (Fin n)))
    (cut : Fin n → ℕ) (tail : Finset (Fin n)) (L : ℕ) :
    fullFlagSymmetricIdeal n ≤ markedFlagIdeal n marked cut tail L :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

/-- Modulo the coinvariant relations the roots form a coinvariant alphabet. -/
theorem quotientRoot_group_elementary {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : fullFlagSymmetricIdeal n ≤ P) :
    groupElementaryPolynomial (quotientRoot P) Finset.univ = 1 := by
  rw [← ksEPoly_ofFn_eq_group]
  exact quotientRoot_elementaryPolynomial P hP

theorem fullFlagSubalphabet_map_mk {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ))
    (Y : Finset (Fin n)) :
    (fullFlagSubalphabet Y).map (Ideal.Quotient.mk P) = Y.toList.map (quotientRoot P) := by
  simp only [fullFlagSubalphabet, List.map_map]
  rfl

/-- A remainder top ideal of the roots vanishes modulo an ideal containing its polynomial form. -/
theorem remainderTopIdeal_quotientRoot_eq_bot {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ))
    (Y : Finset (Fin n)) (N j : ℕ) (h : remainderTopIdeal (fullFlagSubalphabet Y) N j ≤ P) :
    remainderTopIdeal (Y.toList.map (quotientRoot P)) N j = ⊥ := by
  have hm := Ideal.map_mk_eq_bot_of_le h
  rwa [remainderTopIdeal_map, fullFlagSubalphabet_map_mk] at hm

theorem quotientRoot_list_length {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ))
    (Y : Finset (Fin n)) : (Y.toList.map (quotientRoot P)).length = Y.card := by
  simp

/-! ### The singly marked stratum -/

/-- The polynomial singly marked stratum ideal for `j = 1`: the singly marked flag relations and
`∏ Z`, `∏ (V ∩ Y) · c(Z)`. -/
def singlyMarkedSelectedStratumIdeal (m : ℕ) (V Y : Finset (Fin (m + 2))) :
    Ideal (MvPolynomial (Fin (m + 2)) ℂ) :=
  singlyMarkedFlagIdeal (m + 2) V m ⊔
    Ideal.span {∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin (m + 2)) ℂ),
      (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (m + 2)) ℂ)) * groupSubtopCoefficient X Yᶜ}

/-- **Deformation, singly marked.** The stratum ideal consists of leading relations of the
configurations without a selected double. -/
theorem singlyMarkedSelectedStratumIdeal_le (m : ℕ) (V Y : Finset (Fin (m + 2)))
    (hV : V.Nonempty) (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty) (ζ : Fin (m + 1 - 1) → ℂ) :
    singlyMarkedSelectedStratumIdeal m V Y ≤
      pointInitialIdeal (singlyMarkedStratumPoint (m + 1) 1 1 V Y ζ) := by
  classical
  set P := pointInitialIdeal (singlyMarkedStratumPoint (m + 1) 1 1 V Y ζ) with hPdef
  have h0 : singlyMarkedFlagIdeal (m + 2) V m ≤ P :=
    (singlyMarkedFlagIdeal_le_pointInitialIdeal (m + 1) 1 V hV ζ).trans
      (pointInitialIdeal_le_comp (singlyMarkedPoint (m + 1) 1 V ζ)
        (fun c : {c : SinglyMarkedConfiguration (m + 1) 1 V //
          singlyMarkedSelectedDoubles Y c < 1} => c.val))
  have hE := quotientRoot_group_elementary P
    ((fullFlagSymmetricIdeal_le_markedFlagIdeal _ _ _ _ _).trans h0)
  have hlen := quotientRoot_list_length P Y
  have hYc : Y.card + Yᶜ.card = m + 2 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  have htop : remainderTopIdeal (Y.toList.map (quotientRoot P)) (m + 1) 1 = ⊥ :=
    remainderTopIdeal_quotientRoot_eq_bot P Y (m + 1) 1
      (singlyMarked_remainderTopIdeal_le (m + 1) 1 1 (m + 1) (by omega) V Y ζ)
  have hprod := topIdeal_one_power_eq_prod (quotientRoot P) hE Y hY (m + 1) (by omega)
  rw [← hlen, polynomialSubmoduleTopIdeal_power_eq, htop] at hprod
  have hZprod : ∏ i ∈ Yᶜ, quotientRoot P i = 0 :=
    Ideal.span_singleton_eq_bot.mp hprod.symm
  have hpair := topIdeal_one_power_eq_pair (quotientRoot P) hE Y hY hZ m (by omega)
  rw [← hlen, polynomialSubmoduleTopIdeal_power_eq] at hpair
  have hc : groupSubtopCoefficient (quotientRoot P) Yᶜ ∈
      remainderTopIdeal (Y.toList.map (quotientRoot P)) m 1 := by
    rw [hpair]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hmarked : ∀ y ∈ remainderTopIdeal (Y.toList.map (quotientRoot P)) m 1,
      (∏ i ∈ V ∩ Y, quotientRoot P i) * y = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => (∏ i ∈ V ∩ Y, quotientRoot P i) * y = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨cols, rfl⟩
      have h := singlyMarked_markedRemainderMinor_mem (m + 1) 1 1 m (by omega) V Y ζ cols
      have h' := Ideal.Quotient.eq_zero_iff_mem.mpr h
      rw [map_mul, map_prod, remainderTopMinor_map, fullFlagSubalphabet_map_mk] at h'
      exact h'
    · simp only [mul_zero]
    · intro x y _ _ hx hy
      rw [mul_add, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine sup_le h0 (Ideal.span_le.mpr ?_)
  rintro g (rfl | rfl)
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_prod]
    exact hZprod
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, map_prod, groupSubtopCoefficient_map]
    exact hmarked _ hc

/-- **Exactness, singly marked.** The polynomial stratum ideal is the leading-relation ideal of
the configurations without a selected double. -/
theorem singlyMarkedSelectedStratumIdeal_eq (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 2)))
    (hV : V.Nonempty) (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty) (ζ : Fin (m + 1 - 1) → ℂ)
    (hζ : Function.Injective ζ) (hζ0 : ∀ a, ζ a ≠ 0) :
    singlyMarkedSelectedStratumIdeal m V Y =
      pointInitialIdeal (singlyMarkedStratumPoint (m + 1) 1 1 V Y ζ) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hinj : Function.Injective (singlyMarkedStratumPoint (p + 1 + 1) 1 1 V Y ζ) :=
    fun a b h => Subtype.ext (singlyMarkedPoint_injective _ _ V ζ hζ hζ0 h)
  have hC : Module.finrank ℂ (MvPolynomial (Fin (p + 1 + 2)) ℂ ⧸
      singlyMarkedFlagIdeal (p + 1 + 2) V (p + 1)) =
        V.card * Nat.card (FullFlagConfiguration (p + 2) 1) :=
    singlyMarkedFlag_finrank_eq (p + 2) 1 (by omega) V hV
  have hG := singlyMarkedFlag_oneDouble_stratum_finrank_ge (p + 1) hm V Y hV
  rw [omittedPointStratumIdeal_eq_span, Nat.add_sub_cancel] at hG
  have hcount : 2 * Nat.card {c : SinglyMarkedConfiguration (p + 1 + 1) 1 V //
      singlyMarkedSelectedDoubles Y c < 1} +
      2 * singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card * p.factorial =
        V.card * (p + 2).factorial := singlyMarked_oneDouble_count p V Y
  have hclosed := fullFlagConfiguration_card_closed (p + 2) 1 (by omega)
  rw [pow_one] at hclosed
  unfold singlyMarkedSelectedStratumIdeal
  apply sup_eq_pointInitialIdeal_of_count _ hinj _ _
    (singlyMarkedSelectedStratumIdeal_le (p + 1) V Y hV hY hZ ζ)
    (V.card * Nat.card (FullFlagConfiguration (p + 2) 1))
    (singlyMarkedOneDoubleCount (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card * p.factorial) hC
  · rw [Ideal.map_span, Set.image_pair]
    exact hG
  · rw [Fintype.card_eq_nat_card]
    have h2 : 2 * (V.card * Nat.card (FullFlagConfiguration (p + 2) 1)) =
        V.card * (p + 2).factorial := by
      rw [← hclosed]
      ring
    linarith

/-- The singly marked stratum quotient has dimension the number of configurations without a
selected double. -/
theorem singlyMarkedSelectedStratum_finrank (m : ℕ) (hm : 1 ≤ m) (V Y : Finset (Fin (m + 2)))
    (hV : V.Nonempty) (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty) :
    Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸ singlyMarkedSelectedStratumIdeal m V Y) =
      Nat.card {c : SinglyMarkedConfiguration (m + 1) 1 V //
        singlyMarkedSelectedDoubles Y c < 1} := by
  classical
  let ζ : Fin (m + 1 - 1) → ℂ := fun a => (a.val : ℂ) + 1
  have hζ : Function.Injective ζ := by
    intro a b h
    apply Fin.ext
    have h' : (a.val : ℂ) = b.val := by simpa [ζ] using h
    exact_mod_cast h'
  have hζ0 : ∀ a, ζ a ≠ 0 := by
    intro a h
    have h' : ((a.val + 1 : ℕ) : ℂ) = 0 := by simpa [ζ] using h
    exact Nat.succ_ne_zero a.val (by exact_mod_cast h')
  have hinj : Function.Injective (singlyMarkedStratumPoint (m + 1) 1 1 V Y ζ) :=
    fun a b h => Subtype.ext (singlyMarkedPoint_injective _ _ V ζ hζ hζ0 h)
  rw [singlyMarkedSelectedStratumIdeal_eq m hm V Y hV hY hZ ζ hζ hζ0,
    (pointInitialQuotient_finrank _ hinj).2, Nat.card_eq_fintype_card]

/-! ### The doubly marked strata -/

/-- The polynomial doubly marked stratum ideal for `j = 1`: the doubly marked flag relations and
`∏ Z`, `c(Z)`. -/
def doublyMarkedOneSelectedStratumIdeal (m : ℕ) (V Y : Finset (Fin (m + 3))) :
    Ideal (MvPolynomial (Fin (m + 3)) ℂ) :=
  doublyMarkedFlagIdeal (m + 3) V m ⊔
    Ideal.span {∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin (m + 3)) ℂ),
      groupSubtopCoefficient X Yᶜ}

/-- The polynomial doubly marked stratum ideal for `j = 2`: the doubly marked flag relations and
`(∏ Z)²`. -/
def doublyMarkedTwoSelectedStratumIdeal (m : ℕ) (V Y : Finset (Fin (m + 3))) :
    Ideal (MvPolynomial (Fin (m + 3)) ℂ) :=
  doublyMarkedFlagIdeal (m + 3) V m ⊔
    Ideal.span {(∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin (m + 3)) ℂ)) ^ 2}

theorem doublyMarkedFlagIdeal_le_stratumPoint (m j : ℕ) (V Y : Finset (Fin (m + 3)))
    (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (ζ : Fin (m + 1 - 1) → ℂ)
    (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedFlagIdeal (m + 3) V m ≤
      pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 j V Y ζ) :=
  (doublyMarkedFlagIdeal_le_pointInitialIdeal (m + 1) 1 V hV hU ζ hζ0).trans
    (pointInitialIdeal_le_comp (doublyMarkedPoint (m + 1) 1 V ζ)
      (fun c : {c : DoublyMarkedConfiguration (m + 1) 1 V //
        doublyMarkedSelectedDoubles Y c < j} => c.val))

/-- **Deformation, doubly marked, one selected double.** -/
theorem doublyMarkedOneSelectedStratumIdeal_le (m : ℕ) (V Y : Finset (Fin (m + 3)))
    (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty)
    (ζ : Fin (m + 1 - 1) → ℂ) (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedOneSelectedStratumIdeal m V Y ≤
      pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 1 V Y ζ) := by
  classical
  set P := pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 1 V Y ζ) with hPdef
  have h0 := doublyMarkedFlagIdeal_le_stratumPoint m 1 V Y hV hU ζ hζ0
  have hE := quotientRoot_group_elementary P
    ((fullFlagSymmetricIdeal_le_markedFlagIdeal _ _ _ _ _).trans h0)
  have hlen := quotientRoot_list_length P Y
  have hYc : Y.card + Yᶜ.card = m + 3 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  have htop : remainderTopIdeal (Y.toList.map (quotientRoot P)) (m + 1) 1 = ⊥ :=
    remainderTopIdeal_quotientRoot_eq_bot P Y (m + 1) 1
      (doublyMarked_remainderTopIdeal_le (m + 1) 1 1 (m + 1) (by omega) V Y ζ)
  have hpair := topIdeal_one_power_eq_pair (quotientRoot P) hE Y hY hZ (m + 1) (by omega)
  rw [← hlen, polynomialSubmoduleTopIdeal_power_eq, htop] at hpair
  have hmem : ∀ g ∈ ({∏ i ∈ Yᶜ, quotientRoot P i,
      groupSubtopCoefficient (quotientRoot P) Yᶜ} : Set (MvPolynomial (Fin (m + 3)) ℂ ⧸ P)),
      g = 0 := by
    intro g hg
    have h := Ideal.subset_span hg
    rw [← hpair] at h
    exact (Ideal.mem_bot).mp h
  refine sup_le h0 (Ideal.span_le.mpr ?_)
  rintro g (rfl | rfl)
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_prod]
    exact hmem _ (Set.mem_insert _ _)
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [groupSubtopCoefficient_map]
    exact hmem _ (Set.mem_insert_of_mem _ rfl)

/-- **Deformation, doubly marked, two selected doubles.** -/
theorem doublyMarkedTwoSelectedStratumIdeal_le (m : ℕ) (V Y : Finset (Fin (m + 3)))
    (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY2 : 2 ≤ Y.card) (hZ : Yᶜ.Nonempty)
    (ζ : Fin (m + 1 - 1) → ℂ) (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedTwoSelectedStratumIdeal m V Y ≤
      pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 2 V Y ζ) := by
  classical
  set P := pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 2 V Y ζ) with hPdef
  have h0 := doublyMarkedFlagIdeal_le_stratumPoint m 2 V Y hV hU ζ hζ0
  have hE := quotientRoot_group_elementary P
    ((fullFlagSymmetricIdeal_le_markedFlagIdeal _ _ _ _ _).trans h0)
  have hlen := quotientRoot_list_length P Y
  have hYc : Y.card + Yᶜ.card = m + 3 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  have htop : remainderTopIdeal (Y.toList.map (quotientRoot P)) (m + 1) 2 = ⊥ :=
    remainderTopIdeal_quotientRoot_eq_bot P Y (m + 1) 2
      (doublyMarked_remainderTopIdeal_le (m + 1) 1 2 (m + 1) (by omega) V Y ζ)
  have hsq := topIdeal_two_power_eq_sq (quotientRoot P) hE Y hY2 hZ m (by omega)
  rw [← hlen, polynomialSubmoduleTopIdeal_power_eq, htop] at hsq
  refine sup_le h0 (Ideal.span_le.mpr ?_)
  rintro g rfl
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow, map_prod]
  exact Ideal.span_singleton_eq_bot.mp hsq.symm

theorem doublyMarkedStratumIdeal_map_span {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (Y : Finset (Fin n)) :
    (Ideal.span {∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin n) ℂ),
      groupSubtopCoefficient X Yᶜ}).map
      (Ideal.Quotient.mk I) = doublyMarkedStratumIdeal I Y := by
  rw [Ideal.map_span, Set.image_pair, map_prod, groupSubtopCoefficient_map]
  rfl

/-- **Exactness, doubly marked, one selected double.** -/
theorem doublyMarkedOneSelectedStratumIdeal_eq (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY : Y.Nonempty)
    (hZ : Yᶜ.Nonempty) (ζ : Fin (m + 1 - 1) → ℂ) (hζ : Function.Injective ζ)
    (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedOneSelectedStratumIdeal m V Y =
      pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 1 V Y ζ) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hinj : Function.Injective (doublyMarkedStratumPoint (p + 1 + 1) 1 1 V Y ζ) :=
    fun a b h => Subtype.ext (doublyMarkedPoint_injective _ _ V ζ hζ hζ0 h)
  have hC : Module.finrank ℂ (MvPolynomial (Fin (p + 1 + 3)) ℂ ⧸
      doublyMarkedFlagIdeal (p + 1 + 3) V (p + 1)) =
        Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1) :=
    doublyMarkedFlag_finrank_eq (p + 2) 1 (by omega) V
  have hG := doublyMarkedFlag_oneDouble_stratum_finrank_ge (p + 1) hm V Y
  rw [Nat.add_sub_cancel] at hG
  have hcount : 2 * Nat.card {c : DoublyMarkedConfiguration (p + 1 + 1) 1 V //
      doublyMarkedSelectedDoubles Y c < 1} +
      2 * doublyMarkedOneDoubleCount (p + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
        (Vᶜ \ Y).card * p.factorial = Vᶜ.card * V.card * (p + 2).factorial :=
    doublyMarked_oneDouble_count p V Y
  have hclosed := fullFlagConfiguration_card_closed (p + 2) 1 (by omega)
  rw [pow_one] at hclosed
  unfold doublyMarkedOneSelectedStratumIdeal
  apply sup_eq_pointInitialIdeal_of_count _ hinj _ _
    (doublyMarkedOneSelectedStratumIdeal_le (p + 1) V Y hV hU hY hZ ζ hζ0)
    (Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1))
    (doublyMarkedOneDoubleCount (p + 1) (Vᶜ ∩ Y).card (V ∩ Y).card (V \ Y).card
      (Vᶜ \ Y).card * p.factorial) hC
  · rw [doublyMarkedStratumIdeal_map_span]
    exact hG
  · rw [Fintype.card_eq_nat_card]
    have h2 : 2 * (Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1)) =
        Vᶜ.card * V.card * (p + 2).factorial := by
      rw [← hclosed]
      ring
    linarith

/-- **Exactness, doubly marked, two selected doubles.** -/
theorem doublyMarkedTwoSelectedStratumIdeal_eq (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY2 : 2 ≤ Y.card)
    (hZ : Yᶜ.Nonempty) (ζ : Fin (m + 1 - 1) → ℂ) (hζ : Function.Injective ζ)
    (hζ0 : ∀ a, ζ a ≠ 0) :
    doublyMarkedTwoSelectedStratumIdeal m V Y =
      pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 2 V Y ζ) := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hinj : Function.Injective (doublyMarkedStratumPoint (p + 1 + 1) 1 2 V Y ζ) :=
    fun a b h => Subtype.ext (doublyMarkedPoint_injective _ _ V ζ hζ hζ0 h)
  have hC : Module.finrank ℂ (MvPolynomial (Fin (p + 1 + 3)) ℂ ⧸
      doublyMarkedFlagIdeal (p + 1 + 3) V (p + 1)) =
        Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1) :=
    doublyMarkedFlag_finrank_eq (p + 2) 1 (by omega) V
  have hG := doublyMarkedFlag_twoDouble_stratum_finrank_ge (p + 1) hm V Y
  rw [Nat.add_sub_cancel] at hG
  have hcount : 2 * Nat.card {c : DoublyMarkedConfiguration (p + 1 + 1) 1 V //
      doublyMarkedSelectedDoubles Y c < 2} +
      2 * ((Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2) *
        p.factorial = Vᶜ.card * V.card * (p + 2).factorial :=
    doublyMarked_twoDouble_count p V Y
  have hclosed := fullFlagConfiguration_card_closed (p + 2) 1 (by omega)
  rw [pow_one] at hclosed
  unfold doublyMarkedTwoSelectedStratumIdeal
  apply sup_eq_pointInitialIdeal_of_count _ hinj _ _
    (doublyMarkedTwoSelectedStratumIdeal_le (p + 1) V Y hV hU hY2 hZ ζ hζ0)
    (Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1))
    ((Vᶜ ∩ Y).card * (V ∩ Y).card * ((Vᶜ ∩ Y).card + (V ∩ Y).card - 2).choose 2 *
      p.factorial) hC
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_prod]
    exact hG
  · rw [Fintype.card_eq_nat_card]
    have h2 : 2 * (Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (p + 2) 1)) =
        Vᶜ.card * V.card * (p + 2).factorial := by
      rw [← hclosed]
      ring
    linarith

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_le_markedFlagIdeal
#print axioms VOA.DeligneAudit.SL4T.quotientRoot_group_elementary
#print axioms VOA.DeligneAudit.SL4T.fullFlagSubalphabet_map_mk
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_quotientRoot_eq_bot
#print axioms VOA.DeligneAudit.SL4T.quotientRoot_list_length
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratumIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedSelectedStratum_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlagIdeal_le_stratumPoint
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratumIdeal_map_span
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedOneSelectedStratumIdeal_eq
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedTwoSelectedStratumIdeal_eq
