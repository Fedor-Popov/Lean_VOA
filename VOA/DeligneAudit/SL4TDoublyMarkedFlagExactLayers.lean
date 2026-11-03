import VOA.DeligneAudit.SL4TDoublyMarkedFlagConfiguration

/-!
# Exact layers of the doubly marked full flag and the dimension of the weak ring

Let `u` be a root of the first group of the doubly marked ring `C₂` on `B + 2 = m + 3` roots with
`k ≥ 1` doubles. The layer bounds of the proof of the doubly marked bound (`doublyMarkedLayerBound`,
`doublyMarkedLayer_finrank_le_bound`) add up to the dimension of `C₂`
(`doublyMarkedLayerBound_sum`), which is exact. Hence every layer bound is attained
(`doublyMarkedLayer_finrank_eq_bound`). In particular the layer `C₂/(u)`, a quotient of the weak
ring, has the full weak configuration count, so the weak ring with a nonempty weak group has
exactly its configuration dimension (`weakMarkedFlag_finrank_eq`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- The layer bound of the `i`-th layer of a first-group root in the doubly marked ring on
`m + 3` roots with `k ≥ 1` doubles; `p'` and `q` are the sizes of the remaining groups. -/
def doublyMarkedLayerBound (p' q m k i : ℕ) : ℕ :=
  if i = 0 then weakMarkedCount p' q (m + 1) k
  else if i < k then p' * q * Nat.card (FullFlagConfiguration m (k - 1))
  else if i = k then q * Nat.card (FullFlagConfiguration (m + 1) k) -
    q * (q - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (k - 1))
  else p' * q * Nat.card (FullFlagConfiguration m k)

section Layers

variable (m k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ m + 1) (V : Finset (Fin (m + 3)))
  (hV : V.Nonempty) (u : Fin (m + 3)) (hu : u ∉ V)
include hk1 hk hV hu

/-- The excess of the zero layer is at most the singly marked dimension. -/
theorem doublyMarkedLayer_excess_le :
    V.card * (V.card - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (k - 1)) ≤
      V.card * Nat.card (FullFlagConfiguration (m + 1) k) := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hcard := deletedGroup_card_of_notMem V u hu
  have hS := singlyMarkedFlag_finrank_le (m + 1) k hk (deletedGroup u V) hV'
  have hπ := singlyMarkedFlag_unmarkedProduct_finrank_ge (m + 1) k hk1 hk (deletedGroup u V) hV'
  rw [hcard] at hS hπ
  rw [show m + 1 - 2 = m - 1 by omega] at hπ
  refine hπ.trans (le_trans ?_ hS)
  exact Submodule.finrank_le _

/-- Every layer of a first-group root is bounded by its layer bound. -/
theorem doublyMarkedLayer_finrank_le_bound (i : ℕ) (hi : i < m + 1 - k + 1) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1 - k) ⧸ rootPowerLayerIdeal
        (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k)) u) i) ≤
      doublyMarkedLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  classical
  set h := m + 1 - k with hh
  set r := quotientRoot (doublyMarkedFlagIdeal (m + 3) V h) with hr
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hcard := deletedGroup_card_of_notMem V u hu
  simp only [doublyMarkedLayerBound]
  split_ifs with h0 h1 h2
  · subst h0
    apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
      (doublyLayer_weak_le_ker (m + 2) V h u hu 0)).trans
    have hrec := weakMarkedFlag_finrank_le (m + 1) k hk1 hk (deletedGroup u V) hV'
    rwa [show m + 1 - k = h by omega, hcard] at hrec
  · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (doublyLayer_same_le_ker (m + 2) V h u hu i (by omega))).trans
    have hrec := doublyMarkedFlag_finrank_le m (k - 1) (by omega) (deletedGroup u V)
    rwa [show m - (k - 1) = h by omega, hcard] at hrec
  · subst h2
    haveI : FiniteDimensional ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
        (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h ⊔
          Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ le_sup_left).toLinearMap
        (Ideal.Quotient.factor_surjective le_sup_left)
    apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (doublyLayer_singlyProduct_le_ker (m + 2) V h u hu i (by omega) i le_rfl
        (by omega))).trans
    let πS := ∏ j ∈ (deletedGroup u V)ᶜ,
      quotientRoot (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) j
    have hπS : Ideal.Quotient.mk (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h)
        (flagGroupProduct (deletedGroup u V)ᶜ) = πS := by
      simp [flagGroupProduct, πS, quotientRoot]
    have hS := singlyMarkedFlag_finrank_le (m + 1) i hk (deletedGroup u V) hV'
    have hπ := singlyMarkedFlag_unmarkedProduct_finrank_ge (m + 1) i hk1 hk (deletedGroup u V)
      hV'
    rw [show m + 1 - i = h by omega, hcard] at hS hπ
    rw [show m + 1 - 2 = m - 1 by omega] at hπ
    have hsplit := quotient_sup_span_finrank
      (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h)
      (flagGroupProduct (deletedGroup u V)ᶜ)
    rw [hπS] at hsplit
    have h3 : V.card * (V.card - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (i - 1))
        ≤ Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) := hπ
    have h5 : Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
        singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) ≤
          V.card * Nat.card (FullFlagConfiguration (m + 1) i) := hS
    apply Nat.le_sub_of_add_le
    calc _ ≤ Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
            (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h ⊔
              Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) +
            Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) :=
          Nat.add_le_add_left h3 _
      _ = _ := hsplit
      _ ≤ _ := h5
  · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (doublyLayer_lower_le_ker (m + 2) V h u hu k (by omega) (by omega) i (by omega))).trans
    have hrec := doublyMarkedFlag_finrank_le m k (by omega) (deletedGroup u V)
    rwa [show m - k = h - 1 by omega, hcard] at hrec

/-- The layer bounds add up to the dimension of the doubly marked ring. -/
theorem doublyMarkedLayerBound_sum :
    ∑ i ∈ Finset.range (m + 1 - k + 1),
        doublyMarkedLayerBound (deletedGroup u V)ᶜ.card V.card m k i =
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (m + 1) k) := by
  have hcardc : (deletedGroup u V)ᶜ.card + 1 = Vᶜ.card := by
    rw [← deletedGroup_compl]
    exact deletedGroup_card_of_mem Vᶜ u (Finset.mem_compl.mpr hu)
  have hQX := doublyMarkedLayer_excess_le m k hk1 hk V hV u hu
  set p' := (deletedGroup u V)ᶜ.card
  set q := V.card
  set h := m + 1 - k with hh
  let X := q * Nat.card (FullFlagConfiguration (m + 1) k)
  let Qc := q * (q - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (k - 1))
  let A := p' * q * Nat.card (FullFlagConfiguration m (k - 1))
  let C := p' * q * Nat.card (FullFlagConfiguration m k)
  have hsum : ∑ i ∈ Finset.range (h + 1), doublyMarkedLayerBound p' q m k i =
      weakMarkedCount p' q (m + 1) k + (k - 1) * A + (X - Qc) + (h - k) * C :=
    sum_range_doubly_layers h k _ A (X - Qc) C hk1 (by omega)
  rw [hsum, ← hcardc]
  have hR := fullFlagConfiguration_card_recursion m k hk
  rw [show m + 1 - k - k = h - k by omega] at hR
  have hL0 : weakMarkedCount p' q (m + 1) k = A + Qc := by
    simp only [A, Qc, weakMarkedCount, show m + 1 - 1 = m by omega,
      show m + 1 - 2 = m - 1 by omega]
  rw [hL0]
  have hX : Qc + (X - Qc) = X := Nat.add_sub_cancel' hQX
  calc A + Qc + (k - 1) * A + (X - Qc) + (h - k) * C
      = A + (k - 1) * A + (h - k) * C + (Qc + (X - Qc)) := by ring
    _ = A + (k - 1) * A + (h - k) * C + X := by rw [hX]
    _ = (p' + 1) * q * Nat.card (FullFlagConfiguration (m + 1) k) := by
        simp only [A, C, X]
        rw [hR]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring

/-- **Exact layers.** Every layer bound of a first-group root is attained. -/
theorem doublyMarkedLayer_finrank_eq_bound (i : ℕ) (hi : i < m + 1 - k + 1) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1 - k) ⧸ rootPowerLayerIdeal
        (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k)) u) i) =
      doublyMarkedLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  set r := quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k))
  have htot := rootPowerFiltration_finrank (r u) (m + 1 - k + 1) (doublyMarkedFlag_cutoff _ _ _ u)
  rw [doublyMarkedFlag_finrank_eq (m + 1) k hk V,
    ← doublyMarkedLayerBound_sum m k hk1 hk V hV u hu] at htot
  have hle : ∀ j ∈ Finset.range (m + 1 - k + 1),
      Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1 - k) ⧸
        rootPowerLayerIdeal (r u) j) ≤
      doublyMarkedLayerBound (deletedGroup u V)ᶜ.card V.card m k j :=
    fun j hj => doublyMarkedLayer_finrank_le_bound m k hk1 hk V hV u hu j (Finset.mem_range.mp hj)
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp htot.symm) i (Finset.mem_range.mpr hi)

end Layers

/-- Deleting the first position of a group shifted by one. -/
theorem deletedGroup_zero_map_succ {n : ℕ} (W : Finset (Fin (n + 1))) :
    deletedGroup 0 (W.map (Fin.succEmb (n + 1))) = W := by
  ext j
  rw [mem_deletedGroup, Fin.succAbove_zero, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, haj⟩
    rwa [show a = j from Fin.succ_injective _ haj] at ha
  · intro hj
    exact ⟨j, hj, rfl⟩

/-- **The weak dimension.** The weak full flag on `B + 1` roots with `k ≥ 1` doubles and nonempty
groups has exactly its configuration dimension. -/
theorem weakMarkedFlag_finrank_eq (B k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ B)
    (W : Finset (Fin (B + 1))) (hW : W.Nonempty) (hU : Wᶜ.Nonempty) :
    Module.finrank ℂ (WeakMarkedFlagRing (B + 1) W (B - k)) =
      weakMarkedCount Wᶜ.card W.card B k := by
  classical
  apply le_antisymm (weakMarkedFlag_finrank_le B k hk1 hk W hW)
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
  let V : Finset (Fin (m + 3)) := W.map (Fin.succEmb (m + 2))
  have hu : (0 : Fin (m + 3)) ∉ V := by
    simp only [V, Finset.mem_map, Fin.coe_succEmb, not_exists, not_and]
    intro a _ h
    exact Fin.succ_ne_zero a h
  have hVne : V.Nonempty := hW.map
  have hdel : deletedGroup 0 V = W := deletedGroup_zero_map_succ W
  have hVc : V.card = W.card := Finset.card_map _
  have h0 := doublyMarkedLayer_finrank_eq_bound m k hk1 hk V hVne 0 hu 0 (by omega)
  have hle := deletedLayer_finrank_le _ (quotientRoot_aeval_surjective _) 0 0 _
    (doublyLayer_weak_le_ker (m + 2) V (m + 1 - k) 0 hu 0)
  rw [h0, hdel] at hle
  simp only [doublyMarkedLayerBound, if_pos rfl, hdel, hVc] at hle
  exact hle

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerBound
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayer_excess_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayer_finrank_le_bound
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayerBound_sum
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedLayer_finrank_eq_bound
#print axioms VOA.DeligneAudit.SL4T.deletedGroup_zero_map_succ
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_finrank_eq
