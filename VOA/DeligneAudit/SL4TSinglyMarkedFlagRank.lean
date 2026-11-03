import VOA.DeligneAudit.SL4TMarkedFlagDeletion

/-!
# The upper bound for the singly marked full flag

The singly marked ring on `B + 1` roots, with a nonempty marked group `V` of size `q`, cutoff
`h = B - k` on the unmarked group and `h + 1` on `V`, has dimension at most `q · B!/2^k`, written
as `q` times the number of paired configurations of `B` roots with `k` doubles
(`singlyMarkedFlag_finrank_le`). The proof deletes an unmarked root `u`: the first `k` layers of
`u` are quotients of the singly marked ring with one root fewer and `k - 1` doubles, the later
ones of the ring with `k` doubles and cutoff lowered by one (`singlyMarkedLayer_finrank_le_same`,
`singlyMarkedLayer_finrank_le_lower`). When every root is marked the ring is a quotient of the
unmarked full flag on `B + 1` roots (`singlyMarkedFlag_univ_finrank_le`).

The closed form `2^k · #configurations = B!` is recorded as
`fullFlagConfiguration_card_closed`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- The number of paired configurations times `2^k` is `B!`. -/
theorem fullFlagConfiguration_card_closed (B k : ℕ) (hk : 2 * k ≤ B) :
    2 ^ k * Nat.card (FullFlagConfiguration B k) = B.factorial := by
  induction B generalizing k with
  | zero =>
      obtain rfl : k = 0 := by omega
      rw [fullFlagConfiguration_empty_card]
      rfl
  | succ B ih =>
      rw [fullFlagConfiguration_card_recursion B k hk, Nat.factorial_succ]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have h0 := ih 0 (by omega)
        simp only [pow_zero, one_mul, zero_mul, zero_add, Nat.sub_zero] at h0 ⊢
        rw [h0]
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have h1 := ih k' (by omega)
        rw [show k' + 1 - 1 = k' by omega]
        by_cases h2 : 2 * (k' + 1) ≤ B
        · have h3 := ih (k' + 1) h2
          calc 2 ^ (k' + 1) * ((k' + 1) * Nat.card (FullFlagConfiguration B k') +
                (B + 1 - (k' + 1) - (k' + 1)) * Nat.card (FullFlagConfiguration B (k' + 1)))
              = (k' + 1) * 2 * (2 ^ k' * Nat.card (FullFlagConfiguration B k')) +
                  (B + 1 - (k' + 1) - (k' + 1)) *
                    (2 ^ (k' + 1) * Nat.card (FullFlagConfiguration B (k' + 1))) := by ring
            _ = ((k' + 1) * 2 + (B + 1 - (k' + 1) - (k' + 1))) * B.factorial := by
                rw [h1, h3]; ring
            _ = (B + 1) * B.factorial := by congr 1; omega
        · rw [show B + 1 - (k' + 1) - (k' + 1) = 0 by omega, zero_mul, add_zero]
          calc 2 ^ (k' + 1) * ((k' + 1) * Nat.card (FullFlagConfiguration B k'))
              = (k' + 1) * 2 * (2 ^ k' * Nat.card (FullFlagConfiguration B k')) := by ring
            _ = (B + 1) * B.factorial := by rw [h1]; congr 1; omega

/-- Adding one root to a configuration count with the same number of doubles. -/
theorem fullFlagConfiguration_card_succ (B k : ℕ) (hk : 2 * k ≤ B) :
    Nat.card (FullFlagConfiguration (B + 1) k) =
      (B + 1) * Nat.card (FullFlagConfiguration B k) := by
  have h1 := fullFlagConfiguration_card_closed (B + 1) k (by omega)
  have h2 := fullFlagConfiguration_card_closed B k hk
  rw [Nat.factorial_succ, ← h2] at h1
  have hp : 0 < 2 ^ k := by positivity
  apply Nat.eq_of_mul_eq_mul_left hp
  rw [h1]
  ring

/-- A sum over the first `h` layers with two kinds of layer. -/
theorem sum_range_ite_lt (h k a b : ℕ) (hk : k ≤ h) :
    ∑ i ∈ Finset.range h, (if i < k then a else b) = k * a + (h - k) * b := by
  rw [show h = k + (h - k) by omega, Finset.sum_range_add,
    show k + (h - k) - k = h - k by omega]
  congr 1
  · rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
    simp
  · rw [Finset.sum_congr rfl (fun i _ => if_neg (show ¬ k + i < k by omega))]
    simp

/-! ### Relations of the singly marked roots -/

section Roots

variable (n : ℕ) (V : Finset (Fin n)) (h : ℕ)

theorem singlyMarkedFlag_elementary :
    D4Levi.ksEPoly (List.ofFn (quotientRoot (singlyMarkedFlagIdeal n V h))) = 1 :=
  markedFlag_elementary _ _ _ _ _

theorem singlyMarkedFlag_group_elementary :
    groupElementaryPolynomial (quotientRoot (singlyMarkedFlagIdeal n V h)) Finset.univ = 1 := by
  rw [← ksEPoly_ofFn_eq_group]
  exact singlyMarkedFlag_elementary n V h

theorem singlyMarkedFlag_product_zero :
    ∏ i ∈ V, quotientRoot (singlyMarkedFlagIdeal n V h) i = 0 :=
  markedFlag_product_zero _ _ _ _ _ V rfl

theorem singlyMarkedFlag_cutoff (i : Fin n) :
    quotientRoot (singlyMarkedFlagIdeal n V h) i ^ singlyMarkedCutoff V h i = 0 :=
  markedFlag_cutoff _ _ _ _ _ i

theorem singlyMarkedFlag_unmarked_cutoff (i : Fin n) (hi : i ∉ V) :
    quotientRoot (singlyMarkedFlagIdeal n V h) i ^ h = 0 := by
  have hc := singlyMarkedFlag_cutoff n V h i
  rwa [singlyMarkedCutoff, if_neg hi] at hc

theorem singlyMarkedFlag_marked_cutoff (i : Fin n) (hi : i ∈ V) :
    quotientRoot (singlyMarkedFlagIdeal n V h) i ^ (h + 1) = 0 := by
  have hc := singlyMarkedFlag_cutoff n V h i
  rwa [singlyMarkedCutoff, if_pos hi] at hc

end Roots

/-! ### The layers of an unmarked root -/

/-- The relations of the singly marked ring with one root fewer and the same cutoff hold in
every layer of an unmarked root. -/
theorem singlyMarkedLayer_same_le_ker (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ)
    (u : Fin (n + 1)) (hu : u ∉ V) (i : ℕ) :
    singlyMarkedFlagIdeal n (deletedGroup u V) h ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (singlyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (singlyMarkedFlagIdeal (n + 1) V h) with hr
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact singlyMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact mul_mem_of_eq_zero _ _ ((prod_deletedGroup_of_notMem r V u hu).trans
      (singlyMarkedFlag_product_zero _ _ _))
  · intro j
    have hc : singlyMarkedCutoff (deletedGroup u V) h j =
        singlyMarkedCutoff V h (u.succAbove j) := by
      simp [singlyMarkedCutoff, mem_deletedGroup]
    rw [hc]
    exact mul_mem_of_eq_zero _ _ (singlyMarkedFlag_cutoff _ _ _ _)
  · intro s _
    simp

/-- From the `k`-th layer on, the relations of the singly marked ring with one root fewer and
cutoff lowered by one hold in the layers of an unmarked root. -/
theorem singlyMarkedLayer_lower_le_ker (n : ℕ) (V : Finset (Fin (n + 1))) (h k : ℕ)
    (hn : n = h + k) (hh : 1 ≤ h) (u : Fin (n + 1)) (hu : u ∉ V) (i : ℕ) (hi : k ≤ i) :
    singlyMarkedFlagIdeal n (deletedGroup u V) (h - 1) ≤ RingHom.ker (aeval (deletedLayerRoot
      (quotientRoot (singlyMarkedFlagIdeal (n + 1) V h)) u i)).toRingHom := by
  set r := quotientRoot (singlyMarkedFlagIdeal (n + 1) V h) with hr
  have hE : groupElementaryPolynomial r Finset.univ = 1 :=
    singlyMarkedFlag_group_elementary _ _ _
  apply deletedLayer_markedFlagIdeal_le_ker r u i
  · exact singlyMarkedFlag_elementary _ _ _
  · intro S hS
    rw [Set.mem_singleton_iff] at hS
    subst hS
    exact mul_mem_of_eq_zero _ _ ((prod_deletedGroup_of_notMem r V u hu).trans
      (singlyMarkedFlag_product_zero _ _ _))
  · intro j
    have hau : u.succAbove j ≠ u := Fin.succAbove_ne u j
    apply mem_span_pow_succ_of_le _ _ k i hi
    by_cases hj : u.succAbove j ∈ V
    · have hc : singlyMarkedCutoff (deletedGroup u V) (h - 1) j = h := by
        simp only [singlyMarkedCutoff, mem_deletedGroup, if_pos hj]
        omega
      rw [hc]
      have hb := pair_boundary_mem_of_card r hE (u.succAbove j) u hau (h + 1) k (by omega)
        (by omega) (singlyMarkedFlag_marked_cutoff _ _ _ _ hj)
      simpa only [Nat.add_sub_cancel] using hb
    · have hc : singlyMarkedCutoff (deletedGroup u V) (h - 1) j = h - 1 := by
        simp only [singlyMarkedCutoff, mem_deletedGroup, if_neg hj]
      rw [hc]
      exact pair_boundary_mem_of_product r hE V (singlyMarkedFlag_product_zero _ _ _)
        (u.succAbove j) u hau hj hu h k (by omega) (by omega)
        (singlyMarkedFlag_unmarked_cutoff _ _ _ _ hj)
  · intro s _
    simp

/-- Every layer of an unmarked root is a quotient of the singly marked ring with one root fewer
and the same cutoff. -/
theorem singlyMarkedLayer_finrank_le_same (n : ℕ) (V : Finset (Fin (n + 1))) (h : ℕ)
    (u : Fin (n + 1)) (hu : u ∉ V) (i : ℕ) :
    Module.finrank ℂ (SinglyMarkedFlagRing (n + 1) V h ⧸
      rootPowerLayerIdeal (quotientRoot (singlyMarkedFlagIdeal (n + 1) V h) u) i) ≤
      Module.finrank ℂ (SinglyMarkedFlagRing n (deletedGroup u V) h) :=
  deletedLayer_finrank_le _ (quotientRoot_aeval_surjective _) u i _
    (singlyMarkedLayer_same_le_ker n V h u hu i)

/-- From the `k`-th layer on, a layer of an unmarked root is a quotient of the singly marked
ring with one root fewer and cutoff lowered by one. -/
theorem singlyMarkedLayer_finrank_le_lower (n : ℕ) (V : Finset (Fin (n + 1))) (h k : ℕ)
    (hn : n = h + k) (hh : 1 ≤ h) (u : Fin (n + 1)) (hu : u ∉ V) (i : ℕ) (hi : k ≤ i) :
    Module.finrank ℂ (SinglyMarkedFlagRing (n + 1) V h ⧸
      rootPowerLayerIdeal (quotientRoot (singlyMarkedFlagIdeal (n + 1) V h) u) i) ≤
      Module.finrank ℂ (SinglyMarkedFlagRing n (deletedGroup u V) (h - 1)) :=
  deletedLayer_finrank_le _ (quotientRoot_aeval_surjective _) u i _
    (singlyMarkedLayer_lower_le_ker n V h k hn hh u hu i hi)

/-! ### The marked base and the induction -/

/-- When every root is marked, the singly marked ring is a quotient of the unmarked full flag on
all its roots with cutoff `h + 1`. -/
theorem singlyMarkedFlag_univ_finrank_le (B k : ℕ) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (SinglyMarkedFlagRing (B + 1) Finset.univ (B - k)) ≤
      (B + 1) * Nat.card (FullFlagConfiguration B k) := by
  letI := fullFlag_finite (B + 1) (B + 1 - k)
  have hle := finrank_le_of_aeval_surjective (fullFlagTruncationIdeal (B + 1) (B + 1 - k))
    (quotientRoot (singlyMarkedFlagIdeal (B + 1) Finset.univ (B - k))) (by
      refine sup_le (fullFlagSymmetricIdeal_le_ker _ _ (singlyMarkedFlag_elementary _ _ _)) ?_
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change aeval _ ((X i : MvPolynomial (Fin (B + 1)) ℂ) ^ (B + 1 - k)) = 0
      rw [map_pow, aeval_X, show B + 1 - k = B - k + 1 by omega]
      exact singlyMarkedFlag_marked_cutoff _ _ _ _ (Finset.mem_univ i))
    (quotientRoot_aeval_surjective _)
  apply hle.trans
  rw [fullFlag_finrank_eq_configurations (B + 1) k (by omega),
    fullFlagConfiguration_card_succ B k hk]

/-- **The singly marked upper bound.** The singly marked full flag on `B + 1` roots with a
nonempty marked group `V` and cutoff `B - k` has dimension at most `|V| · B!/2^k`. -/
theorem singlyMarkedFlag_finrank_le (B k : ℕ) (hk : 2 * k ≤ B) (V : Finset (Fin (B + 1)))
    (hV : V.Nonempty) :
    Module.finrank ℂ (SinglyMarkedFlagRing (B + 1) V (B - k)) ≤
      V.card * Nat.card (FullFlagConfiguration B k) := by
  classical
  induction B generalizing k with
  | zero =>
      obtain rfl : k = 0 := by omega
      have hU : V = Finset.univ := by
        obtain ⟨a, ha⟩ := hV
        ext i
        simp only [Finset.mem_univ, iff_true]
        rwa [show i = a from Fin.ext (by have := i.isLt; have := a.isLt; omega)]
      subst hU
      simpa using singlyMarkedFlag_univ_finrank_le 0 0 le_rfl
  | succ B ih =>
      by_cases hU : V = Finset.univ
      · subst hU
        simpa using singlyMarkedFlag_univ_finrank_le (B + 1) k hk
      obtain ⟨u, hu⟩ : ∃ u, u ∉ V := by
        by_contra hn
        apply hU
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩
      set h := B + 1 - k with hh
      have hh1 : 1 ≤ h := by omega
      set r := quotientRoot (singlyMarkedFlagIdeal (B + 2) V h)
      have hV' : (deletedGroup u V).Nonempty := by
        rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
        exact Finset.card_pos.mpr hV
      have hcard := deletedGroup_card_of_notMem V u hu
      rw [rootPowerFiltration_finrank (r u) h (singlyMarkedFlag_unmarked_cutoff _ _ _ _ hu)]
      calc ∑ i ∈ Finset.range h, Module.finrank ℂ (SinglyMarkedFlagRing (B + 2) V h ⧸
              rootPowerLayerIdeal (r u) i)
          ≤ ∑ i ∈ Finset.range h, (if i < k then
              V.card * Nat.card (FullFlagConfiguration B (k - 1))
            else V.card * Nat.card (FullFlagConfiguration B k)) := by
            apply Finset.sum_le_sum
            intro i hi
            split_ifs with hik
            · apply (singlyMarkedLayer_finrank_le_same (B + 1) V h u hu i).trans
              have hrec := ih (k - 1) (by omega) (deletedGroup u V) hV'
              rw [show B - (k - 1) = h by omega, hcard] at hrec
              exact hrec
            · apply (singlyMarkedLayer_finrank_le_lower (B + 1) V h k (by omega) hh1 u hu i
                (by omega)).trans
              have hrec := ih k (by have := Finset.mem_range.mp hi; omega) (deletedGroup u V) hV'
              rw [show B - k = h - 1 by omega, hcard] at hrec
              exact hrec
        _ = V.card * Nat.card (FullFlagConfiguration (B + 1) k) := by
            rw [sum_range_ite_lt h k _ _ (by omega), fullFlagConfiguration_card_recursion B k hk,
              show h - k = B + 1 - k - k by omega]
            ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_card_closed
#print axioms VOA.DeligneAudit.SL4T.fullFlagConfiguration_card_succ
#print axioms VOA.DeligneAudit.SL4T.sum_range_ite_lt
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_elementary
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_group_elementary
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_product_zero
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_cutoff
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_unmarked_cutoff
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_marked_cutoff
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedLayer_same_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedLayer_lower_le_ker
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedLayer_finrank_le_same
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedLayer_finrank_le_lower
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_univ_finrank_le
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_finrank_le
