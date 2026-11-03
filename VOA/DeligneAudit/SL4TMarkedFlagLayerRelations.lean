import VOA.DeligneAudit.SL4TSinglyMarkedFlagRank
import VOA.DeligneAudit.SL4TMarkedFlagExchanges

/-!
# The layers of a first-group root in the weak and doubly marked full flags

For the weak ring `W(U, V; B, k)` on `B + 1` roots and a root `y` of the weak group `U`:

* every layer is a quotient of the weak ring with the same cutoff (`weakLayer_weak_le_ker`);
* from layer `k - 1` on, of the singly marked ring with the same cutoff, by the exchange of two
  weak roots (`weakLayer_singly_le_ker`);
* from layer `k` on, of the weak ring with cutoff lowered by one, by the two-root exchanges and
  the power-sum exchange (`weakLayer_lower_le_ker`);
* the top layer `h` is a quotient of the doubly marked ring with cutoff lowered by one, by the
  power-sum exchange, `x^h y^h = 0` and `y^h ∏(U∖y) = 0` (`weakLayer_doubly_le_ker`).

For the doubly marked ring `C₂(U, V; B, k)` on `B + 2` roots and a root `u` of `U`:

* every layer is a quotient of the weak ring with the same cutoff (`doublyLayer_weak_le_ker`) and
  of the unmarked full flag with cutoff `h + 1` (`doublyLayer_fullFlag_le_ker`);
* every positive layer is a quotient of the doubly marked ring with the same cutoff, since
  `u^i ∏U' = u^(i-1) ∏U` (`doublyLayer_same_le_ker`);
* from layer `k` on, of the singly marked ring with the same cutoff, by the exchange of two
  first-group roots (`doublyLayer_singly_le_ker`), and in positive layers also modulo `∏U'`
  (`doublyLayer_singlyProduct_le_ker`);
* from layer `k + 1` on, of the doubly marked ring with cutoff lowered by one, by the two-root
  exchanges and the power-sum exchange (`doublyLayer_lower_le_ker`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- A vanishing element lies in every ideal. -/
theorem ideal_mem_of_eq_zero {R : Type*} [CommRing R] {x : R} (I : Ideal R) (hx : x = 0) :
    x ∈ I := hx ▸ I.zero_mem

/-! ### Relations of the weak and doubly marked roots -/

section Roots

variable (n : ℕ) (V : Finset (Fin n)) (h : ℕ)

theorem weakMarkedFlag_elementary :
    D4Levi.ksEPoly (List.ofFn (quotientRoot (weakMarkedFlagIdeal n V h))) = 1 :=
  markedFlag_elementary _ _ _ _ _

theorem weakMarkedFlag_group_elementary :
    groupElementaryPolynomial (quotientRoot (weakMarkedFlagIdeal n V h)) Finset.univ = 1 := by
  rw [← ksEPoly_ofFn_eq_group]
  exact weakMarkedFlag_elementary n V h

theorem weakMarkedFlag_product_zero :
    ∏ i ∈ V, quotientRoot (weakMarkedFlagIdeal n V h) i = 0 :=
  markedFlag_product_zero _ _ _ _ _ V rfl

theorem weakMarkedFlag_cutoff (i : Fin n) :
    quotientRoot (weakMarkedFlagIdeal n V h) i ^ (h + 1) = 0 :=
  markedFlag_cutoff _ _ _ _ _ i

theorem weakMarkedFlag_tail_zero (s : ℕ) (hs : max h 1 ≤ s) :
    ∑ i ∈ V, quotientRoot (weakMarkedFlagIdeal n V h) i ^ s = 0 :=
  markedFlag_tail_zero _ _ _ _ _ s hs

theorem doublyMarkedFlag_elementary :
    D4Levi.ksEPoly (List.ofFn (quotientRoot (doublyMarkedFlagIdeal n V h))) = 1 :=
  markedFlag_elementary _ _ _ _ _

theorem doublyMarkedFlag_group_elementary :
    groupElementaryPolynomial (quotientRoot (doublyMarkedFlagIdeal n V h)) Finset.univ = 1 := by
  rw [← ksEPoly_ofFn_eq_group]
  exact doublyMarkedFlag_elementary n V h

theorem doublyMarkedFlag_product_zero :
    ∏ i ∈ V, quotientRoot (doublyMarkedFlagIdeal n V h) i = 0 :=
  markedFlag_product_zero _ _ _ _ _ V (Set.mem_insert_of_mem _ rfl)

theorem doublyMarkedFlag_compl_product_zero :
    ∏ i ∈ Vᶜ, quotientRoot (doublyMarkedFlagIdeal n V h) i = 0 :=
  markedFlag_product_zero _ _ _ _ _ Vᶜ (Set.mem_insert _ _)

theorem doublyMarkedFlag_cutoff (i : Fin n) :
    quotientRoot (doublyMarkedFlagIdeal n V h) i ^ (h + 1) = 0 :=
  markedFlag_cutoff _ _ _ _ _ i

theorem doublyMarkedFlag_tail_zero (s : ℕ) (hs : max h 1 ≤ s) :
    ∑ i ∈ V, quotientRoot (doublyMarkedFlagIdeal n V h) i ^ s = 0 :=
  markedFlag_tail_zero _ _ _ _ _ s hs

end Roots

/-! ### The layers of a weak root -/

section Weak

variable (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ) (u : Fin (n + 1)) (hu : u ∉ V)
include hu

theorem weakLayer_weak_le_ker (i : ℕ) :
    weakMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (weakMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (weakMarkedFlagIdeal (n + 1) V h)
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact weakMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact deletedGroupProduct_mem_of_zero r V u hu (weakMarkedFlag_product_zero _ _ _) i
  · intro j
    exact mul_mem_of_eq_zero _ _ (weakMarkedFlag_cutoff _ _ _ _)
  · intro s hs
    exact deletedGroupPowerSum_mem_of_zero r V u hu s (weakMarkedFlag_tail_zero _ _ _ s hs) i

/-- From layer `K` on, with `n + 1 = h + K + 2` roots, the layers of a weak root carry the
singly marked relations (the exchange of two weak roots with `K = k - 1`). -/
theorem weakLayer_singly_le_ker (K : ℕ) (hn : n + 1 = h + K + 2) (i : ℕ) (hi : K ≤ i) :
    singlyMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (weakMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (weakMarkedFlagIdeal (n + 1) V h)
  have hE : groupElementaryPolynomial r Finset.univ = 1 := weakMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact weakMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact deletedGroupProduct_mem_of_zero r V u hu (weakMarkedFlag_product_zero _ _ _) i
  · intro j
    have hau : u.succAbove j ≠ u := Fin.succAbove_ne u j
    by_cases hj : u.succAbove j ∈ V
    · rw [singlyMarkedCutoff, if_pos ((mem_deletedGroup u V j).mpr hj)]
      exact mul_mem_of_eq_zero _ _ (weakMarkedFlag_cutoff _ _ _ _)
    · rw [singlyMarkedCutoff, if_neg (fun h' => hj ((mem_deletedGroup u V j).mp h'))]
      apply mem_span_pow_succ_of_le _ _ K i hi
      have hb := pair_boundary_mem_of_product r hE V (weakMarkedFlag_product_zero _ _ _)
        (u.succAbove j) u hau hj hu (h + 1) K (by omega) (by omega) (weakMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel] using hb
  · intro s _
    simp

/-- From layer `k` on, with `n + 1 = h + k + 1` roots, the layers of a weak root carry the weak
relations with cutoff lowered by one (two-root exchanges and the power-sum exchange). -/
theorem weakLayer_lower_le_ker (k : ℕ) (hn : n + 1 = h + k + 1) (hk1 : 1 ≤ k) (hh : 1 ≤ h)
    (i : ℕ) (hi : k ≤ i) :
    weakMarkedFlagIdeal n (deletedGroup u V) (h - 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (weakMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (weakMarkedFlagIdeal (n + 1) V h)
  have hE : groupElementaryPolynomial r Finset.univ = 1 := weakMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact weakMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact deletedGroupProduct_mem_of_zero r V u hu (weakMarkedFlag_product_zero _ _ _) i
  · intro j
    have hau : u.succAbove j ≠ u := Fin.succAbove_ne u j
    rw [show h - 1 + 1 = h by omega]
    by_cases hj : u.succAbove j ∈ V
    · apply mem_span_pow_succ_of_le _ _ k i hi
      have hb := pair_boundary_mem_of_card r hE (u.succAbove j) u hau (h + 1) k (by omega)
        (by omega) (weakMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel] using hb
    · apply mem_span_pow_succ_of_le _ _ (k - 1) i (by omega)
      have hb := pair_boundary_mem_of_product r hE V (weakMarkedFlag_product_zero _ _ _)
        (u.succAbove j) u hau hj hu (h + 1) (k - 1) (by omega) (by omega)
        (weakMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hk1] using hb
  · intro s hs
    by_cases hsh : h ≤ s
    · exact deletedGroupPowerSum_mem_of_zero r V u hu s
        (weakMarkedFlag_tail_zero _ _ _ s (by omega)) i
    · obtain rfl : s = h - 1 := by omega
      rw [sum_deletedGroup_of_notMem (fun i => r i ^ (h - 1)) V u hu]
      apply mem_span_pow_succ_of_le _ _ k i hi
      exact firstGroup_powerSum_exchange r V u (weakMarkedFlag_elementary _ _ _)
        (weakMarkedFlag_product_zero _ _ _) hu h k (n - 1) (by omega) (by omega) (by omega)
        (fun e he => weakMarkedFlag_tail_zero _ _ _ e (by omega))

/-- The top layer `h` of a weak root carries the doubly marked relations with cutoff lowered by
one (the power-sum exchange, `x^h y^h = 0` and `y^h ∏(U∖y) = 0`). -/
theorem weakLayer_doubly_le_ker (k : ℕ) (hn : n + 1 = h + k + 1) (hk1 : 1 ≤ k) (hkh : k ≤ h) :
    doublyMarkedFlagIdeal n (deletedGroup u V) (h - 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (weakMarkedFlagIdeal (n + 1) V h)) u h)).toRingHom := by
  set r := quotientRoot (weakMarkedFlagIdeal (n + 1) V h)
  have hE : groupElementaryPolynomial r Finset.univ = 1 := weakMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u h
  · exact weakMarkedFlag_elementary _ _ _
  · intro S hS
    rcases hS with rfl | hS
    · apply ideal_mem_of_eq_zero
      rw [mul_comm]
      exact firstGroup_power_product_zero r V u (weakMarkedFlag_elementary _ _ _) hu h
        (by omega) (weakMarkedFlag_tail_zero _ _ _ h (by omega)) (weakMarkedFlag_cutoff _ _ _)
    · rw [Set.mem_singleton_iff] at hS
      subst hS
      exact deletedGroupProduct_mem_of_zero r V u hu (weakMarkedFlag_product_zero _ _ _) h
  · intro j
    rw [show h - 1 + 1 = h by omega]
    exact ideal_mem_of_eq_zero _ (pair_middle_zero_of_card r hE (u.succAbove j) u
      (Fin.succAbove_ne u j) h (by omega) (weakMarkedFlag_cutoff _ _ _ _)
      (weakMarkedFlag_cutoff _ _ _ _))
  · intro s hs
    by_cases hsh : h ≤ s
    · exact deletedGroupPowerSum_mem_of_zero r V u hu s
        (weakMarkedFlag_tail_zero _ _ _ s (by omega)) h
    · obtain rfl : s = h - 1 := by omega
      rw [sum_deletedGroup_of_notMem (fun i => r i ^ (h - 1)) V u hu]
      apply mem_span_pow_succ_of_le _ _ k h hkh
      exact firstGroup_powerSum_exchange r V u (weakMarkedFlag_elementary _ _ _)
        (weakMarkedFlag_product_zero _ _ _) hu h k (n - 1) (by omega) (by omega) (by omega)
        (fun e he => weakMarkedFlag_tail_zero _ _ _ e (by omega))

end Weak

/-! ### The layers of a first-group root of the doubly marked ring -/

section Doubly

variable (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ) (u : Fin (n + 1)) (hu : u ∉ V)
include hu

theorem doublyLayer_weak_le_ker (i : ℕ) :
    weakMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact doublyMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact deletedGroupProduct_mem_of_zero r V u hu (doublyMarkedFlag_product_zero _ _ _) i
  · intro j
    exact mul_mem_of_eq_zero _ _ (doublyMarkedFlag_cutoff _ _ _ _)
  · intro s hs
    exact deletedGroupPowerSum_mem_of_zero r V u hu s (doublyMarkedFlag_tail_zero _ _ _ s hs) i

theorem doublyLayer_same_le_ker (i : ℕ) (hi : 1 ≤ i) :
    doublyMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact doublyMarkedFlag_elementary _ _ _
  · intro S hS
    rcases hS with rfl | hS
    · exact deletedComplProduct_mem r V u hu (doublyMarkedFlag_compl_product_zero _ _ _) i hi
    · rw [Set.mem_singleton_iff] at hS
      subst hS
      exact deletedGroupProduct_mem_of_zero r V u hu (doublyMarkedFlag_product_zero _ _ _) i
  · intro j
    exact mul_mem_of_eq_zero _ _ (doublyMarkedFlag_cutoff _ _ _ _)
  · intro s hs
    exact deletedGroupPowerSum_mem_of_zero r V u hu s (doublyMarkedFlag_tail_zero _ _ _ s hs) i

/-- From layer `k` on, with `n + 1 = h + k + 2` roots, the layers of `u` carry the singly
marked relations (the exchange of two first-group roots). -/
theorem doublyLayer_singly_le_ker (k : ℕ) (hn : n + 1 = h + k + 2) (i : ℕ) (hi : k ≤ i) :
    singlyMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  have hE : groupElementaryPolynomial r Finset.univ = 1 :=
    doublyMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact doublyMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact deletedGroupProduct_mem_of_zero r V u hu (doublyMarkedFlag_product_zero _ _ _) i
  · intro j
    have hau : u.succAbove j ≠ u := Fin.succAbove_ne u j
    by_cases hj : u.succAbove j ∈ V
    · rw [singlyMarkedCutoff, if_pos ((mem_deletedGroup u V j).mpr hj)]
      exact mul_mem_of_eq_zero _ _ (doublyMarkedFlag_cutoff _ _ _ _)
    · rw [singlyMarkedCutoff, if_neg (fun h' => hj ((mem_deletedGroup u V j).mp h'))]
      apply mem_span_pow_succ_of_le _ _ k i hi
      have hb := pair_boundary_mem_of_product r hE V (doublyMarkedFlag_product_zero _ _ _)
        (u.succAbove j) u hau hj hu (h + 1) k (by omega) (by omega)
        (doublyMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel] using hb
  · intro s _
    simp

/-- In a positive layer from `k` on, the layers of `u` carry the singly marked relations and the
product of the remaining first-group roots. -/
theorem doublyLayer_singlyProduct_le_ker (k : ℕ) (hn : n + 1 = h + k + 2) (i : ℕ) (hi : k ≤ i)
    (hi1 : 1 ≤ i) :
    singlyMarkedFlagIdeal n (deletedGroup u V) h ⊔
        Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ} ≤
      RingHom.ker (aeval (deletedLayerRoot
        (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  refine sup_le (doublyLayer_singly_le_ker n V h u hu k hn i hi) ?_
  apply Ideal.span_le.mpr
  rintro p rfl
  change aeval (deletedLayerRoot r u i) (flagGroupProduct (deletedGroup u V)ᶜ) = 0
  have h0 := layer_mk_eq_zero r u i _
    (deletedComplProduct_mem r V u hu (doublyMarkedFlag_compl_product_zero _ _ _) i hi1)
  simpa [flagGroupProduct, deletedLayerRoot, map_prod] using h0

/-- From layer `k + 1` on, the layers of `u` carry the doubly marked relations with cutoff
lowered by one (two-root exchanges and the power-sum exchange). -/
theorem doublyLayer_lower_le_ker (k : ℕ) (hn : n + 1 = h + k + 2) (hh : 1 ≤ h) (i : ℕ)
    (hi : k + 1 ≤ i) :
    doublyMarkedFlagIdeal n (deletedGroup u V) (h - 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  have hE : groupElementaryPolynomial r Finset.univ = 1 :=
    doublyMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact doublyMarkedFlag_elementary _ _ _
  · intro S hS
    rcases hS with rfl | hS
    · exact deletedComplProduct_mem r V u hu (doublyMarkedFlag_compl_product_zero _ _ _) i
        (by omega)
    · rw [Set.mem_singleton_iff] at hS
      subst hS
      exact deletedGroupProduct_mem_of_zero r V u hu (doublyMarkedFlag_product_zero _ _ _) i
  · intro j
    have hau : u.succAbove j ≠ u := Fin.succAbove_ne u j
    rw [show h - 1 + 1 = h by omega]
    by_cases hj : u.succAbove j ∈ V
    · apply mem_span_pow_succ_of_le _ _ (k + 1) i hi
      have hb := pair_boundary_mem_of_card r hE (u.succAbove j) u hau (h + 1) (k + 1)
        (by omega) (by omega) (doublyMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel] using hb
    · apply mem_span_pow_succ_of_le _ _ k i (by omega)
      have hb := pair_boundary_mem_of_product r hE V (doublyMarkedFlag_product_zero _ _ _)
        (u.succAbove j) u hau hj hu (h + 1) k (by omega) (by omega)
        (doublyMarkedFlag_cutoff _ _ _ _)
      simpa only [Nat.add_sub_cancel] using hb
  · intro s hs
    by_cases hsh : h ≤ s
    · exact deletedGroupPowerSum_mem_of_zero r V u hu s
        (doublyMarkedFlag_tail_zero _ _ _ s (by omega)) i
    · obtain rfl : s = h - 1 := by omega
      rw [sum_deletedGroup_of_notMem (fun i => r i ^ (h - 1)) V u hu]
      apply mem_span_pow_succ_of_le _ _ (k + 1) i hi
      exact firstGroup_powerSum_exchange r V u (doublyMarkedFlag_elementary _ _ _)
        (doublyMarkedFlag_product_zero _ _ _) hu h (k + 1) (n - 1) (by omega) (by omega)
        (by omega) (fun e he => doublyMarkedFlag_tail_zero _ _ _ e (by omega))

end Doubly

/-- Every layer of a root of a ring in which all roots have cutoff `h + 1` carries the relations
of the unmarked full flag on the remaining roots with cutoff `h + 1`. -/
theorem doublyLayer_fullFlag_le_ker (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ)
    (u : Fin (n + 1)) (i : ℕ) :
    fullFlagTruncationIdeal n (h + 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (doublyMarkedFlagIdeal (n + 1) V h)
  refine sup_le (fullFlagSymmetricIdeal_le_ker _ _
    (deletedLayer_elementary r u i (doublyMarkedFlag_elementary _ _ _))) ?_
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  change aeval (deletedLayerRoot r u i) ((X j : MvPolynomial (Fin n) ℂ) ^ (h + 1)) = 0
  rw [map_pow, aeval_X]
  exact deletedLayerRoot_pow_eq_zero r u i j _
    (mul_mem_of_eq_zero _ _ (doublyMarkedFlag_cutoff _ _ _ _))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.ideal_mem_of_eq_zero
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_elementary
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_group_elementary
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_product_zero
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_cutoff
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_tail_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_elementary
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_group_elementary
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_product_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_compl_product_zero
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_cutoff
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_tail_zero
#print axioms VOA.DeligneAudit.SL4T.weakLayer_weak_le_ker
#print axioms VOA.DeligneAudit.SL4T.weakLayer_singly_le_ker
#print axioms VOA.DeligneAudit.SL4T.weakLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.weakLayer_doubly_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_weak_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_same_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_singly_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_singlyProduct_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.doublyLayer_fullFlag_le_ker
