import VOA.DeligneAudit.SL4TDoublyMarkedFlagExactLayers

/-!
# Layer isomorphisms of the weak and doubly marked full flags

A layer map from a presented child onto a layer of a deleted root is surjective; when the child
has at most the dimension of the layer it is an isomorphism
(`deletedLayerMap_injective_of_finrank_le`). The dimension counts of the marked full flags give
this for every layer used by the stratum recursions:

* doubly marked ring with no doubles, a first-group root `u`: the zero layer is the singly marked
  ring and every positive layer is the doubly marked ring with one root fewer and cutoff lowered
  by one (`doublyMarkedZeroLayer_finrank_eq_bound`, `doublyMarkedZeroLayerMap_injective_singly`,
  `doublyMarkedZeroLayerMap_injective_lower`);
* doubly marked ring with doubles: the four kinds of layer of a first-group root
  (`doublyMarkedLayerMap_injective_weak`, `_same`, `_singlyProduct`, `_lower`);
* weak ring with doubles and a weak root `y`: the four kinds of layer of `y`
  (`weakLayer_finrank_eq_bound`, `weakLayerMap_injective_weak`, `_singly`, `_lower`,
  `_doubly`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- A layer map whose child has at most the dimension of the layer is injective. -/
theorem deletedLayerMap_injective_of_finrank_le {C : Type*} [CommRing C] [Algebra ℂ C]
    [FiniteDimensional ℂ C] {n : ℕ} (r : Fin (n + 1) → C)
    (hr : Function.Surjective (aeval r : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] C))
    (u : Fin (n + 1)) (i : ℕ) (I' : Ideal (MvPolynomial (Fin n) ℂ))
    [FiniteDimensional ℂ (MvPolynomial (Fin n) ℂ ⧸ I')]
    (hI' : I' ≤ RingHom.ker (aeval (deletedLayerRoot r u i)).toRingHom)
    (hle : Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ I') ≤
      Module.finrank ℂ (C ⧸ rootPowerLayerIdeal (r u) i)) :
    Function.Injective (deletedLayerMap r u i I' hI') := by
  haveI : FiniteDimensional ℂ (C ⧸ rootPowerLayerIdeal (r u) i) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℂ _)
  have hs := deletedLayerMap_surjective r hr u i I' hI'
  have he : Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ I') =
      Module.finrank ℂ (C ⧸ rootPowerLayerIdeal (r u) i) :=
    le_antisymm hle (deletedLayer_finrank_le r hr u i I' hI')
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (deletedLayerMap r u i I' hI').toLinearMap) he).mpr hs

/-! ### The doubly marked ring without doubles -/

/-- The layer bound of a first-group root of the doubly marked ring on `m + 3` roots without
doubles. -/
def doublyMarkedZeroLayerBound (p' q m i : ℕ) : ℕ :=
  if i = 0 then q * Nat.card (FullFlagConfiguration (m + 1) 0)
  else p' * q * Nat.card (FullFlagConfiguration m 0)

section ZeroDoubles

variable (m : ℕ) (V : Finset (Fin (m + 3))) (hV : V.Nonempty) (u : Fin (m + 3)) (hu : u ∉ V)
include hV hu

theorem doublyMarkedZeroLayer_child_singly_le :
    Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup u V) (m + 1)) ≤
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m 0 := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hrec := singlyMarkedFlag_finrank_le (m + 1) 0 (by omega) (deletedGroup u V) hV'
  rw [Nat.sub_zero, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [doublyMarkedZeroLayerBound, if_pos rfl] using hrec

theorem doublyMarkedZeroLayer_child_lower_le (i : ℕ) (hi : 1 ≤ i) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 2) (deletedGroup u V) m) ≤
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m i := by
  have hrec := doublyMarkedFlag_finrank_le m 0 (by omega) (deletedGroup u V)
  rw [Nat.sub_zero, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [doublyMarkedZeroLayerBound, if_neg (show i ≠ 0 by omega)] using hrec

theorem doublyMarkedZeroLayer_finrank_le_bound (i : ℕ) (hi : i < m + 2) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1) ⧸ rootPowerLayerIdeal
        (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1)) u) i) ≤
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m i := by
  set r := quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1))
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
      (doublyLayer_singly_le_ker (m + 2) V (m + 1) u hu 0 (by omega) 0 le_rfl)).trans
      (doublyMarkedZeroLayer_child_singly_le m V hV u hu)
  · exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (doublyLayer_lower_le_ker (m + 2) V (m + 1) u hu 0 (by omega) (by omega) i
        (by omega))).trans (doublyMarkedZeroLayer_child_lower_le m V hV u hu i hi1)

theorem doublyMarkedZeroLayerBound_sum :
    ∑ i ∈ Finset.range (m + 2), doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m i =
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration (m + 1) 0) := by
  have hcardc : (deletedGroup u V)ᶜ.card + 1 = Vᶜ.card := by
    rw [← deletedGroup_compl]
    exact deletedGroup_card_of_mem Vᶜ u (Finset.mem_compl.mpr hu)
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun i _ => show
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m (i + 1) =
        (deletedGroup u V)ᶜ.card * V.card * Nat.card (FullFlagConfiguration m 0) by
      simp only [doublyMarkedZeroLayerBound, if_neg (Nat.succ_ne_zero i)])]
  simp only [doublyMarkedZeroLayerBound, if_pos rfl, ↓reduceIte, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  rw [← hcardc, fullFlagConfiguration_card_succ m 0 (by omega)]
  ring

/-- **Exact layers without doubles.** -/
theorem doublyMarkedZeroLayer_finrank_eq_bound (i : ℕ) (hi : i < m + 2) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1) ⧸ rootPowerLayerIdeal
        (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1)) u) i) =
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m i := by
  set r := quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1))
  have htot := rootPowerFiltration_finrank (r u) (m + 2) (doublyMarkedFlag_cutoff _ _ _ u)
  have hdim := doublyMarkedFlag_finrank_eq (m + 1) 0 (by omega) V
  rw [Nat.sub_zero] at hdim
  rw [hdim, ← doublyMarkedZeroLayerBound_sum m V hV u hu] at htot
  have hle : ∀ j ∈ Finset.range (m + 2),
      Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1) ⧸
        rootPowerLayerIdeal (r u) j) ≤
      doublyMarkedZeroLayerBound (deletedGroup u V)ᶜ.card V.card m j :=
    fun j hj => doublyMarkedZeroLayer_finrank_le_bound m V hV u hu j (Finset.mem_range.mp hj)
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp htot.symm) i (Finset.mem_range.mpr hi)

theorem doublyMarkedZeroLayerMap_injective_singly :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1))) u 0 _
      (doublyLayer_singly_le_ker (m + 2) V (m + 1) u hu 0 (by omega) 0 le_rfl)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [doublyMarkedZeroLayer_finrank_eq_bound m V hV u hu 0 (by omega)]
  exact doublyMarkedZeroLayer_child_singly_le m V hV u hu

theorem doublyMarkedZeroLayerMap_injective_lower (i : ℕ) (hi1 : 1 ≤ i) (hi : i < m + 2) :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1))) u i _
      (doublyLayer_lower_le_ker (m + 2) V (m + 1) u hu 0 (by omega) (by omega) i
        (by omega))) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [doublyMarkedZeroLayer_finrank_eq_bound m V hV u hu i hi]
  exact doublyMarkedZeroLayer_child_lower_le m V hV u hu i hi1

end ZeroDoubles

/-! ### The doubly marked ring with doubles -/

section Doubles

variable (m k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ m + 1) (V : Finset (Fin (m + 3)))
  (hV : V.Nonempty) (u : Fin (m + 3)) (hu : u ∉ V)
include hk1 hk hV hu

theorem doublyMarkedLayerMap_injective_weak :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k))) u 0 _
      (doublyLayer_weak_le_ker (m + 2) V (m + 1 - k) u hu 0)) := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [doublyMarkedLayer_finrank_eq_bound m k hk1 hk V hV u hu 0 (by omega)]
  have hrec := weakMarkedFlag_finrank_le (m + 1) k hk1 hk (deletedGroup u V) hV'
  rw [deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [doublyMarkedLayerBound, if_pos rfl] using hrec

theorem doublyMarkedLayerMap_injective_same (i : ℕ) (hi1 : 1 ≤ i) (hik : i < k) :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k))) u i _
      (doublyLayer_same_le_ker (m + 2) V (m + 1 - k) u hu i hi1)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [doublyMarkedLayer_finrank_eq_bound m k hk1 hk V hV u hu i (by omega)]
  have hrec := doublyMarkedFlag_finrank_le m (k - 1) (by omega) (deletedGroup u V)
  rw [show m - (k - 1) = m + 1 - k by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [doublyMarkedLayerBound, if_neg (show i ≠ 0 by omega), if_pos hik] using hrec

theorem doublyMarkedLayerMap_injective_lower (i : ℕ) (hik : k + 1 ≤ i) (hi : i < m + 2 - k) :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k))) u i _
      (doublyLayer_lower_le_ker (m + 2) V (m + 1 - k) u hu k (by omega) (by omega) i hik)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [doublyMarkedLayer_finrank_eq_bound m k hk1 hk V hV u hu i (by omega)]
  have hrec := doublyMarkedFlag_finrank_le m k (by omega) (deletedGroup u V)
  rw [show m - k = m + 1 - k - 1 by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [doublyMarkedLayerBound, if_neg (show i ≠ 0 by omega),
    if_neg (show ¬ i < k by omega), if_neg (show i ≠ k by omega)] using hrec

/-- The product of the remaining first-group roots in the singly marked child at the zero point
layer has exactly the configuration count of the unmarked product bound. -/
theorem doublyMarkedLayer_childProduct_finrank_eq :
    Module.finrank ℂ ((Ideal.span {∏ j ∈ (deletedGroup u V)ᶜ,
        quotientRoot (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) (m + 1 - k)) j}
          ).restrictScalars ℂ) =
      V.card * (V.card - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (k - 1)) ∧
    Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
        (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) (m + 1 - k) ⊔
          Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) =
      Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V (m + 1 - k) ⧸ rootPowerLayerIdeal
        (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k)) u) k) := by
  set h := m + 1 - k with hh
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hcard := deletedGroup_card_of_notMem V u hu
  let πS := ∏ j ∈ (deletedGroup u V)ᶜ,
    quotientRoot (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) j
  have hπS : Ideal.Quotient.mk (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h)
      (flagGroupProduct (deletedGroup u V)ᶜ) = πS := by
    simp [flagGroupProduct, πS, quotientRoot]
  have hS := singlyMarkedFlag_finrank_eq (m + 1) k hk (deletedGroup u V) hV'
  have hπ := singlyMarkedFlag_unmarkedProduct_finrank_ge (m + 1) k hk1 hk (deletedGroup u V) hV'
  rw [show m + 1 - k = h by omega, hcard] at hS hπ
  rw [show m + 1 - 2 = m - 1 by omega] at hπ
  have hsplit := quotient_sup_span_finrank
    (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) (flagGroupProduct (deletedGroup u V)ᶜ)
  rw [hπS] at hsplit
  haveI : FiniteDimensional ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
      (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h ⊔
        Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ le_sup_left).toLinearMap
      (Ideal.Quotient.factor_surjective le_sup_left)
  have hlayer := doublyMarkedLayer_finrank_eq_bound m k hk1 hk V hV u hu k (by omega)
  simp only [doublyMarkedLayerBound, if_neg (show k ≠ 0 by omega),
    if_neg (show ¬ k < k by omega), if_pos rfl, ↓reduceIte] at hlayer
  have hmap := deletedLayer_finrank_le _ (quotientRoot_aeval_surjective _) u k _
    (doublyLayer_singlyProduct_le_ker (m + 2) V h u hu k (by omega) k le_rfl (by omega))
  rw [hlayer] at hmap
  have hS' : Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
      singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) =
        V.card * Nat.card (FullFlagConfiguration (m + 1) k) := hS
  have hπ' : V.card * (V.card - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) (k - 1))
      ≤ Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) := hπ
  rw [hS'] at hsplit
  constructor
  · change Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) = _
    omega
  · rw [hlayer]
    omega

theorem doublyMarkedLayerMap_injective_singlyProduct :
    Function.Injective (deletedLayerMap
      (quotientRoot (doublyMarkedFlagIdeal (m + 3) V (m + 1 - k))) u k _
      (doublyLayer_singlyProduct_le_ker (m + 2) V (m + 1 - k) u hu k (by omega) k le_rfl
        (by omega))) := by
  haveI : FiniteDimensional ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
      (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) (m + 1 - k) ⊔
        Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ ℂ le_sup_left).toLinearMap
      (Ideal.Quotient.factor_surjective le_sup_left)
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  exact le_of_eq (doublyMarkedLayer_childProduct_finrank_eq m k hk1 hk V hV u hu).2

end Doubles

/-! ### The weak ring with doubles -/

/-- The layer bound of a weak root of the weak ring on `m + 3` roots with `k ≥ 1` doubles. -/
def weakLayerBound (p' q m k i : ℕ) : ℕ :=
  if i < k - 1 then weakMarkedCount p' q (m + 1) (k - 1)
  else if i = k - 1 then q * Nat.card (FullFlagConfiguration (m + 1) (k - 1))
  else if i < m + 2 - k then weakMarkedCount p' q (m + 1) k
  else p' * q * Nat.card (FullFlagConfiguration m (k - 1))

section WeakLayers

variable (m k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ m + 2) (V : Finset (Fin (m + 3)))
  (hV : V.Nonempty) (u : Fin (m + 3)) (hu : u ∉ V)
include hk1 hk hV hu

theorem weakLayer_child_weak_le (i : ℕ) (hi : i < k - 1) :
    Module.finrank ℂ (WeakMarkedFlagRing (m + 2) (deletedGroup u V) (m + 2 - k)) ≤
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hrec := weakMarkedFlag_finrank_le (m + 1) (k - 1) (by omega) (by omega)
    (deletedGroup u V) hV'
  rw [show m + 1 - (k - 1) = m + 2 - k by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [weakLayerBound, if_pos hi] using hrec

theorem weakLayer_child_singly_le :
    Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) (deletedGroup u V) (m + 2 - k)) ≤
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k (k - 1) := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hrec := singlyMarkedFlag_finrank_le (m + 1) (k - 1) (by omega) (deletedGroup u V) hV'
  rw [show m + 1 - (k - 1) = m + 2 - k by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [weakLayerBound, if_neg (lt_irrefl _), if_pos rfl] using hrec

theorem weakLayer_child_lower_le (i : ℕ) (hik : k ≤ i) (hi : i < m + 2 - k) :
    Module.finrank ℂ (WeakMarkedFlagRing (m + 2) (deletedGroup u V) (m + 2 - k - 1)) ≤
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hrec := weakMarkedFlag_finrank_le (m + 1) k hk1 (by omega) (deletedGroup u V) hV'
  rw [show m + 1 - k = m + 2 - k - 1 by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [weakLayerBound, if_neg (show ¬ i < k - 1 by omega),
    if_neg (show i ≠ k - 1 by omega), if_pos hi] using hrec

theorem weakLayer_child_doubly_le :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 2) (deletedGroup u V) (m + 2 - k - 1)) ≤
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k (m + 2 - k) := by
  have hrec := doublyMarkedFlag_finrank_le m (k - 1) (by omega) (deletedGroup u V)
  rw [show m - (k - 1) = m + 2 - k - 1 by omega, deletedGroup_card_of_notMem V u hu] at hrec
  simpa only [weakLayerBound, if_neg (show ¬ m + 2 - k < k - 1 by omega),
    if_neg (show m + 2 - k ≠ k - 1 by omega), if_neg (lt_irrefl _)] using hrec

theorem weakLayer_finrank_le_bound (i : ℕ) (hi : i < m + 2 - k + 1) :
    Module.finrank ℂ (WeakMarkedFlagRing (m + 3) V (m + 2 - k) ⧸ rootPowerLayerIdeal
        (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k)) u) i) ≤
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  set h := m + 2 - k with hh
  set r := quotientRoot (weakMarkedFlagIdeal (m + 3) V h)
  by_cases h1 : i < k - 1
  · exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (weakLayer_weak_le_ker (m + 2) V h u hu i)).trans
      (weakLayer_child_weak_le m k hk1 hk V hV u hu i h1)
  by_cases h2 : i = k - 1
  · subst h2
    exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u (k - 1) _
      (weakLayer_singly_le_ker (m + 2) V h u hu (k - 1) (by omega) (k - 1) le_rfl)).trans
      (weakLayer_child_singly_le m k hk1 hk V hV u hu)
  by_cases h3 : i < h
  · exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
      (weakLayer_lower_le_ker (m + 2) V h u hu k (by omega) hk1 (by omega) i
        (by omega))).trans (weakLayer_child_lower_le m k hk1 hk V hV u hu i (by omega) h3)
  · obtain rfl : i = h := by omega
    exact (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u h _
      (weakLayer_doubly_le_ker (m + 2) V h u hu k (by omega) hk1 (by omega))).trans
      (weakLayer_child_doubly_le m k hk1 hk V hV u hu)

theorem weakLayerBound_sum :
    ∑ i ∈ Finset.range (m + 2 - k + 1), weakLayerBound (deletedGroup u V)ᶜ.card V.card m k i =
      weakMarkedCount Vᶜ.card V.card (m + 2) k := by
  have hcardc : (deletedGroup u V)ᶜ.card + 1 = Vᶜ.card := by
    rw [← deletedGroup_compl]
    exact deletedGroup_card_of_mem Vᶜ u (Finset.mem_compl.mpr hu)
  have hUne : V ≠ Finset.univ := fun h => hu (h ▸ Finset.mem_univ u)
  set h := m + 2 - k with hh
  set q := V.card
  set p' := (deletedGroup u V)ᶜ.card
  have hsum := sum_range_weak_layers h k (weakMarkedCount p' q (m + 1) (k - 1))
    (q * Nat.card (FullFlagConfiguration (m + 1) (k - 1))) (weakMarkedCount p' q (m + 1) k)
    (p' * q * Nat.card (FullFlagConfiguration m (k - 1))) hk1 (by omega)
  simp only [weakLayerBound]
  rw [hsum, ← hcardc]
  simp only [weakMarkedCount]
  rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega,
    show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show k - 1 - 1 = k - 2 by omega]
  have hR1 := fullFlagConfiguration_card_recursion m (k - 1) (by omega)
  rw [show k - 1 - 1 = k - 2 by omega,
    show m + 1 - (k - 1) - (k - 1) = h - k + 1 by omega] at hR1
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    obtain rfl : k = 1 := by omega
    have hq : q - 1 < 2 := by
      have hlt : q < Finset.univ.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hUne⟩)
      rw [Finset.card_univ, Fintype.card_fin] at hlt
      omega
    rw [Nat.choose_eq_zero_of_lt hq, hR1]
    simp only [mul_zero, zero_mul, add_zero, Nat.sub_self, zero_add]
    ring
  · have hR2 := fullFlagConfiguration_card_recursion (m - 1) (k - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, show k - 1 - 1 = k - 2 by omega,
      show m - (k - 1) - (k - 1) = h - k by omega] at hR2
    rw [hR1, hR2]
    ring

/-- **Exact weak layers.** -/
theorem weakLayer_finrank_eq_bound (i : ℕ) (hi : i < m + 2 - k + 1) :
    Module.finrank ℂ (WeakMarkedFlagRing (m + 3) V (m + 2 - k) ⧸ rootPowerLayerIdeal
        (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k)) u) i) =
      weakLayerBound (deletedGroup u V)ᶜ.card V.card m k i := by
  set r := quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k))
  have htot := rootPowerFiltration_finrank (r u) (m + 2 - k + 1) (weakMarkedFlag_cutoff _ _ _ u)
  rw [weakMarkedFlag_finrank_eq (m + 2) k hk1 hk V hV ⟨u, Finset.mem_compl.mpr hu⟩,
    ← weakLayerBound_sum m k hk1 hk V hV u hu] at htot
  have hle : ∀ j ∈ Finset.range (m + 2 - k + 1),
      Module.finrank ℂ (WeakMarkedFlagRing (m + 3) V (m + 2 - k) ⧸
        rootPowerLayerIdeal (r u) j) ≤ weakLayerBound (deletedGroup u V)ᶜ.card V.card m k j :=
    fun j hj => weakLayer_finrank_le_bound m k hk1 hk V hV u hu j (Finset.mem_range.mp hj)
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp htot.symm) i (Finset.mem_range.mpr hi)

theorem weakLayerMap_injective_weak (i : ℕ) (hi : i < k - 1) :
    Function.Injective (deletedLayerMap
      (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k))) u i _
      (weakLayer_weak_le_ker (m + 2) V (m + 2 - k) u hu i)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [weakLayer_finrank_eq_bound m k hk1 hk V hV u hu i (by omega)]
  exact weakLayer_child_weak_le m k hk1 hk V hV u hu i hi

theorem weakLayerMap_injective_singly :
    Function.Injective (deletedLayerMap
      (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k))) u (k - 1) _
      (weakLayer_singly_le_ker (m + 2) V (m + 2 - k) u hu (k - 1) (by omega) (k - 1)
        le_rfl)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [weakLayer_finrank_eq_bound m k hk1 hk V hV u hu (k - 1) (by omega)]
  exact weakLayer_child_singly_le m k hk1 hk V hV u hu

theorem weakLayerMap_injective_lower (i : ℕ) (hik : k ≤ i) (hi : i < m + 2 - k) :
    Function.Injective (deletedLayerMap
      (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k))) u i _
      (weakLayer_lower_le_ker (m + 2) V (m + 2 - k) u hu k (by omega) hk1 (by omega) i
        hik)) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [weakLayer_finrank_eq_bound m k hk1 hk V hV u hu i (by omega)]
  exact weakLayer_child_lower_le m k hk1 hk V hV u hu i hik hi

theorem weakLayerMap_injective_doubly :
    Function.Injective (deletedLayerMap
      (quotientRoot (weakMarkedFlagIdeal (m + 3) V (m + 2 - k))) u (m + 2 - k) _
      (weakLayer_doubly_le_ker (m + 2) V (m + 2 - k) u hu k (by omega) hk1 (by omega))) := by
  apply deletedLayerMap_injective_of_finrank_le _ (quotientRoot_aeval_surjective _)
  rw [weakLayer_finrank_eq_bound m k hk1 hk V hV u hu (m + 2 - k) (by omega)]
  exact weakLayer_child_doubly_le m k hk1 hk V hV u hu

end WeakLayers

end

end VOA.DeligneAudit.SL4T
