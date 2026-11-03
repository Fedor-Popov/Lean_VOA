import VOA.DeligneAudit.SL4TMarkedFlagLayerRelations
import VOA.DeligneAudit.SL4TSinglyMarkedProductBound

/-!
# The upper bounds for the weak and the doubly marked full flags

* **Weak ring** (`weakMarkedFlag_finrank_le`): on `B + 1` roots, with `k ≥ 1`, a weak group of
  size `p` and a marked group of size `q ≥ 1`,
  `dim W ≤ p q (B-1)!/2^(k-1) + q C(q-1, 2) (B-2)!/2^(k-1)` (`weakMarkedCount`).
* **Doubly marked ring** (`doublyMarkedFlag_finrank_le`): on `B + 2` roots, with groups of sizes
  `p` and `q`, `dim C₂ ≤ p q B!/2^k`.

Both are proved together by strong induction on `B` (`markedFlag_bounds`). At each `B` the weak
bound is proved first, from the weak bound at `B - 1`, the singly marked bound and the doubly
marked bound at `B - 2`; then the doubly marked bound, from the weak bound at `B`, the doubly
marked bound at `B - 1`, the singly marked bound and the unmarked product bound
(`singlyMarkedFlag_unmarkedProduct_finrank_ge`), which cancels the excess of the weak layer.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- The configuration count of the weak ring with groups of sizes `p` and `q`. -/
def weakMarkedCount (p q B k : ℕ) : ℕ :=
  p * q * Nat.card (FullFlagConfiguration (B - 1) (k - 1)) +
    q * (q - 1).choose 2 * Nat.card (FullFlagConfiguration (B - 2) (k - 1))

/-- Quotienting by one more principal ideal removes its dimension. -/
theorem quotient_sup_span_finrank {σ : Type*} (I : Ideal (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ (MvPolynomial σ ℂ ⧸ I)] (p : MvPolynomial σ ℂ) :
    Module.finrank ℂ (MvPolynomial σ ℂ ⧸ (I ⊔ Ideal.span {p})) +
      Module.finrank ℂ ((Ideal.span {Ideal.Quotient.mk I p}).restrictScalars ℂ) =
        Module.finrank ℂ (MvPolynomial σ ℂ ⧸ I) := by
  let K : Ideal (MvPolynomial σ ℂ ⧸ I) := Ideal.span {Ideal.Quotient.mk I p}
  have hK : (Ideal.span {p}).map (Ideal.Quotient.mkₐ ℂ I) = K := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have e1 := (DoubleQuot.quotQuotEquivQuotSupₐ ℂ I (Ideal.span {p})).toLinearEquiv
  rw [← e1.finrank_eq, hK, ← (Submodule.Quotient.restrictScalarsEquiv ℂ K).finrank_eq]
  exact Submodule.finrank_quotient_add_finrank (K.restrictScalars ℂ)

/-- A quotient in which a vanishing product is empty is the zero ring. -/
theorem quotient_finrank_zero_of_empty_product {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (S : Finset (Fin n)) (hS : S = ∅) (h0 : ∏ i ∈ S, quotientRoot I i = 0) :
    Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ I) = 0 := by
  rw [hS, Finset.prod_empty] at h0
  haveI : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ I) := subsingleton_of_zero_eq_one h0.symm
  exact Module.finrank_zero_of_subsingleton

/-! ### Two sums over layers -/

theorem sum_range_weak_layers (h k a b c d : ℕ) (hk1 : 1 ≤ k) (hkh : k ≤ h) :
    ∑ i ∈ Finset.range (h + 1), (if i < k - 1 then a else if i = k - 1 then b
      else if i < h then c else d) = (k - 1) * a + b + (h - k) * c + d := by
  obtain ⟨t, rfl⟩ : ∃ t, h = (k - 1) + (1 + t) := ⟨h - k, by omega⟩
  rw [show k - 1 + (1 + t) - k = t by omega, Finset.sum_range_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_one]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi)),
    if_neg (by omega), if_pos (by omega),
    Finset.sum_congr rfl (fun i hi => show (if k - 1 + (1 + i) < k - 1 then a else
      if k - 1 + (1 + i) = k - 1 then b else if k - 1 + (1 + i) < k - 1 + (1 + t) then c
      else d) = c by
        have := Finset.mem_range.mp hi
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)])]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

theorem sum_range_doubly_layers (h k a b c d : ℕ) (hk1 : 1 ≤ k) (hkh : k ≤ h) :
    ∑ i ∈ Finset.range (h + 1), (if i = 0 then a else if i < k then b
      else if i = k then c else d) = a + (k - 1) * b + c + (h - k) * d := by
  rw [show h + 1 = 1 + ((k - 1) + (1 + (h - k))) by omega, Finset.sum_range_add,
    Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one, Finset.sum_range_one,
    if_pos rfl]
  rw [Finset.sum_congr rfl (fun i hi => show (if 1 + i = 0 then a else if 1 + i < k then b
      else if 1 + i = k then c else d) = b by
        have := Finset.mem_range.mp hi
        rw [if_neg (by omega), if_pos (by omega)]),
    if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Finset.sum_congr rfl (fun i hi => show (if 1 + (k - 1 + (1 + i)) = 0 then a else
      if 1 + (k - 1 + (1 + i)) < k then b else if 1 + (k - 1 + (1 + i)) = k then c else d) = d by
        have := Finset.mem_range.mp hi
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-! ### Bases -/

/-- When every root is marked, the weak ring is a quotient of the unmarked full flag. -/
theorem weakMarkedFlag_univ_finrank_le (B k : ℕ) (hk : 2 * k ≤ B + 1) :
    Module.finrank ℂ (WeakMarkedFlagRing (B + 1) Finset.univ (B - k)) ≤
      Nat.card (FullFlagConfiguration (B + 1) k) := by
  letI := fullFlag_finite (B + 1) (B + 1 - k)
  have hle := finrank_le_of_aeval_surjective (fullFlagTruncationIdeal (B + 1) (B + 1 - k))
    (quotientRoot (weakMarkedFlagIdeal (B + 1) Finset.univ (B - k))) (by
      refine sup_le (fullFlagSymmetricIdeal_le_ker _ _ (weakMarkedFlag_elementary _ _ _)) ?_
      apply Ideal.span_le.mpr
      rintro p ⟨i, rfl⟩
      change aeval _ ((X i : MvPolynomial (Fin (B + 1)) ℂ) ^ (B + 1 - k)) = 0
      rw [map_pow, aeval_X, show B + 1 - k = B - k + 1 by omega]
      exact weakMarkedFlag_cutoff _ _ _ i)
    (quotientRoot_aeval_surjective _)
  exact hle.trans (le_of_eq (fullFlag_finrank_eq_configurations (B + 1) k hk))

/-! ### The induction -/

/-- The weak bound at `B`. -/
def WeakMarkedFlagBound (B : ℕ) : Prop :=
  ∀ k, 1 ≤ k → 2 * k ≤ B → ∀ V : Finset (Fin (B + 1)), V.Nonempty →
    Module.finrank ℂ (WeakMarkedFlagRing (B + 1) V (B - k)) ≤
      weakMarkedCount Vᶜ.card V.card B k

/-- The doubly marked bound at `B`. -/
def DoublyMarkedFlagBound (B : ℕ) : Prop :=
  ∀ k, 2 * k ≤ B → ∀ V : Finset (Fin (B + 2)),
    Module.finrank ℂ (DoublyMarkedFlagRing (B + 2) V (B - k)) ≤
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration B k)

/-- A finset of positions that is not everything misses a position. -/
theorem exists_notMem_of_ne_univ {n : ℕ} (V : Finset (Fin n)) (hV : V ≠ Finset.univ) :
    ∃ u, u ∉ V := by
  by_contra hn
  apply hV
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  by_contra hi
  exact hn ⟨i, hi⟩

/-- **Weak step.** The weak bound at `m + 2` from the weak bound at `m + 1` and the doubly
marked bound at `m`. -/
theorem weakMarkedFlag_step (m : ℕ) (hW : WeakMarkedFlagBound (m + 1))
    (hD : DoublyMarkedFlagBound m) : WeakMarkedFlagBound (m + 2) := by
  intro k hk1 hk V hV
  classical
  by_cases hU : V = Finset.univ
  · subst hU
    have hc : (Finset.univ : Finset (Fin (m + 3)))ᶜ.card = 0 := by simp
    rw [hc, weakMarkedCount, Finset.card_univ, Fintype.card_fin]
    apply (weakMarkedFlag_univ_finrank_le (m + 2) k (by omega)).trans
    rw [fullFlagConfiguration_card_succ (m + 2) k hk,
      fullFlagConfiguration_card_two_less (m + 2) k hk1 hk,
      show m + 3 - 1 = m + 2 by omega]
    simp only [zero_mul, zero_add]
    rw [mul_assoc]
  obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU
  set h := m + 2 - k with hh
  set r := quotientRoot (weakMarkedFlagIdeal (m + 3) V h) with hr
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hV
  have hcard := deletedGroup_card_of_notMem V u hu
  have hcardc : (deletedGroup u V)ᶜ.card + 1 = Vᶜ.card := by
    rw [← deletedGroup_compl]
    exact deletedGroup_card_of_mem Vᶜ u (Finset.mem_compl.mpr hu)
  set q := V.card
  set p' := (deletedGroup u V)ᶜ.card
  let A := weakMarkedCount p' q (m + 1) (k - 1)
  let Bc := q * Nat.card (FullFlagConfiguration (m + 1) (k - 1))
  let Cc := weakMarkedCount p' q (m + 1) k
  let D := p' * q * Nat.card (FullFlagConfiguration m (k - 1))
  rw [rootPowerFiltration_finrank (r u) (h + 1) (weakMarkedFlag_cutoff _ _ _ u)]
  calc ∑ i ∈ Finset.range (h + 1), Module.finrank ℂ (WeakMarkedFlagRing (m + 3) V h ⧸
          rootPowerLayerIdeal (r u) i)
      ≤ ∑ i ∈ Finset.range (h + 1), (if i < k - 1 then A else if i = k - 1 then Bc
          else if i < h then Cc else D) := by
        apply Finset.sum_le_sum
        intro i hi
        have hih := Finset.mem_range.mp hi
        split_ifs with h1 h2 h3
        · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
            (weakLayer_weak_le_ker (m + 2) V h u hu i)).trans
          have hrec := hW (k - 1) (by omega) (by omega) (deletedGroup u V) hV'
          rwa [show m + 1 - (k - 1) = h by omega, hcard] at hrec
        · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
            (weakLayer_singly_le_ker (m + 2) V h u hu (k - 1) (by omega) i (by omega))).trans
          have hrec := singlyMarkedFlag_finrank_le (m + 1) (k - 1) (by omega) (deletedGroup u V)
            hV'
          rwa [show m + 1 - (k - 1) = h by omega, hcard] at hrec
        · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
            (weakLayer_lower_le_ker (m + 2) V h u hu k (by omega) hk1 (by omega) i
              (by omega))).trans
          have hrec := hW k hk1 (by omega) (deletedGroup u V) hV'
          rwa [show m + 1 - k = h - 1 by omega, hcard] at hrec
        · obtain rfl : i = h := by omega
          apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u h _
            (weakLayer_doubly_le_ker (m + 2) V h u hu k (by omega) hk1 (by omega))).trans
          have hrec := hD (k - 1) (by omega) (deletedGroup u V)
          rwa [show m - (k - 1) = h - 1 by omega, hcard] at hrec
    _ = (k - 1) * A + Bc + (h - k) * Cc + D := sum_range_weak_layers h k A Bc Cc D hk1 (by omega)
    _ ≤ weakMarkedCount Vᶜ.card q (m + 2) k := by
        rw [← hcardc]
        simp only [A, Bc, Cc, D, weakMarkedCount]
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
              (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hU⟩)
            rw [Finset.card_univ, Fintype.card_fin] at hlt
            omega
          rw [Nat.choose_eq_zero_of_lt hq, hR1]
          simp only [mul_zero, zero_mul, add_zero, Nat.sub_self, zero_add]
          apply le_of_eq
          ring
        · have hR2 := fullFlagConfiguration_card_recursion (m - 1) (k - 1) (by omega)
          rw [show m - 1 + 1 = m by omega, show k - 1 - 1 = k - 2 by omega,
            show m - (k - 1) - (k - 1) = h - k by omega] at hR2
          rw [hR1, hR2]
          apply le_of_eq
          ring

/-- **Doubly marked step.** The doubly marked bound at `B` from the weak bound at `B` and the doubly
marked bound at `B - 1`. -/
theorem doublyMarkedFlag_step (B : ℕ) (hW : WeakMarkedFlagBound B)
    (hD : ∀ m, B = m + 1 → DoublyMarkedFlagBound m) : DoublyMarkedFlagBound B := by
  intro k hk V
  classical
  by_cases hV0 : V = ∅
  · rw [quotient_finrank_zero_of_empty_product _ V hV0 (doublyMarkedFlag_product_zero _ _ _)]
    exact Nat.zero_le _
  by_cases hU0 : V = Finset.univ
  · rw [quotient_finrank_zero_of_empty_product _ Vᶜ (by rw [hU0, Finset.compl_univ])
      (doublyMarkedFlag_compl_product_zero _ _ _)]
    exact Nat.zero_le _
  have hVne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hV0
  obtain ⟨u, hu⟩ := exists_notMem_of_ne_univ V hU0
  set h := B - k with hh
  set r := quotientRoot (doublyMarkedFlagIdeal (B + 2) V h) with hr
  have hV' : (deletedGroup u V).Nonempty := by
    rw [← Finset.card_pos, deletedGroup_card_of_notMem V u hu]
    exact Finset.card_pos.mpr hVne
  have hcard := deletedGroup_card_of_notMem V u hu
  have hcardc : (deletedGroup u V)ᶜ.card + 1 = Vᶜ.card := by
    rw [← deletedGroup_compl]
    exact deletedGroup_card_of_mem Vᶜ u (Finset.mem_compl.mpr hu)
  have htot : Vᶜ.card + V.card = B + 2 := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ V
    rw [Fintype.card_fin] at this
    omega
  set q := V.card
  set p' := (deletedGroup u V)ᶜ.card
  by_cases hp1 : (deletedGroup u V)ᶜ = ∅
  · -- one root in the first group: it is zero
    have hu0 : r u = 0 := by
      have h0 := doublyMarkedFlag_compl_product_zero (B + 2) V h
      rw [← deletedComplProduct_eq r V u hu, hp1, Finset.prod_empty, mul_one] at h0
      exact h0
    have hp0 : p' = 0 := by simp only [p', hp1, Finset.card_empty]
    letI := fullFlag_finite (B + 1) (h + 1)
    rw [rootPowerFiltration_finrank (r u) 1 (by rw [pow_one]; exact hu0), Finset.sum_range_one]
    apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
      (doublyLayer_fullFlag_le_ker (B + 1) V h u 0)).trans
    rw [show h + 1 = B + 1 - k by omega, fullFlag_finrank_eq_configurations (B + 1) k (by omega),
      fullFlagConfiguration_card_succ B k hk, ← hcardc, hp0]
    rw [show q = B + 1 by omega]
    simp
  have hp'1 : 1 ≤ p' := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp1)
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- no doubles: `u` sits at the zero point or at a simple point
    subst hk0
    rw [rootPowerFiltration_finrank (r u) (h + 1) (doublyMarkedFlag_cutoff _ _ _ u)]
    rcases Nat.eq_zero_or_pos B with hB0 | hB0
    · subst hB0
      rw [Finset.sum_range_one]
      apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
        (doublyLayer_singly_le_ker 1 V h u hu 0 (by omega) 0 le_rfl)).trans
      have hrec := singlyMarkedFlag_finrank_le 0 0 le_rfl (deletedGroup u V) hV'
      rw [hcard] at hrec
      apply hrec.trans
      rw [← hcardc]
      apply Nat.le_of_lt_succ
      nlinarith [Nat.zero_le (q * Nat.card (FullFlagConfiguration 0 0))]
    obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
    calc ∑ i ∈ Finset.range (h + 1), Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V h ⧸
            rootPowerLayerIdeal (r u) i)
        ≤ ∑ i ∈ Finset.range (h + 1), (if i = 0 then
            q * Nat.card (FullFlagConfiguration (m + 1) 0)
            else p' * q * Nat.card (FullFlagConfiguration m 0)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hih := Finset.mem_range.mp hi
          split_ifs with hi0
          · subst hi0
            apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
              (doublyLayer_singly_le_ker (m + 2) V h u hu 0 (by omega) 0 le_rfl)).trans
            have hrec := singlyMarkedFlag_finrank_le (m + 1) 0 (by omega) (deletedGroup u V) hV'
            rwa [hcard] at hrec
          · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
              (doublyLayer_lower_le_ker (m + 2) V h u hu 0 (by omega) (by omega) i
                (by omega))).trans
            have hrec := hD m rfl 0 (by omega) (deletedGroup u V)
            rwa [show m - 0 = h - 1 by omega, hcard] at hrec
      _ = q * Nat.card (FullFlagConfiguration (m + 1) 0) +
            h * (p' * q * Nat.card (FullFlagConfiguration m 0)) := by
          rw [Finset.sum_range_succ', if_pos rfl,
            Finset.sum_congr rfl (fun i _ => if_neg (Nat.succ_ne_zero i))]
          simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
          ring
      _ ≤ Vᶜ.card * q * Nat.card (FullFlagConfiguration (m + 1) 0) := by
          rw [← hcardc, fullFlagConfiguration_card_succ m 0 (by omega),
            show h = m + 1 by omega]
          apply le_of_eq
          ring
  · -- at least one double: `u` at a double, at the zero point, or at a simple point
    obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
    let S := SinglyMarkedFlagRing (m + 2) (deletedGroup u V) h
    let πS : S := ∏ j ∈ (deletedGroup u V)ᶜ,
      quotientRoot (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) j
    have hπS : Ideal.Quotient.mk (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h)
        (flagGroupProduct (deletedGroup u V)ᶜ) = πS := by
      simp [flagGroupProduct, πS, quotientRoot]
    have hS := singlyMarkedFlag_finrank_le (m + 1) k hk (deletedGroup u V) hV'
    have hπ := singlyMarkedFlag_unmarkedProduct_finrank_ge (m + 1) k hk1 hk (deletedGroup u V)
      hV'
    rw [show m + 1 - k = h by omega, hcard] at hS hπ
    have hsplit := quotient_sup_span_finrank
      (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h)
      (flagGroupProduct (deletedGroup u V)ᶜ)
    rw [hπS] at hsplit
    let X := q * Nat.card (FullFlagConfiguration (m + 1) k)
    let Qc := q * (q - 1).choose 2 * Nat.card (FullFlagConfiguration (m - 1) k.pred)
    have hQ : Qc = q * (q - 1).choose 2 * Nat.card (FullFlagConfiguration (m + 1 - 2) (k - 1)) := by
      simp only [Qc, Nat.pred_eq_sub_one, show m + 1 - 2 = m - 1 by omega]
    have hQX : Qc ≤ X := by
      rw [hQ]
      exact hπ.trans ((Nat.le_add_left _ _).trans (hsplit.symm ▸ hS))
    let L0 := weakMarkedCount p' q (m + 1) k
    let A := p' * q * Nat.card (FullFlagConfiguration m (k - 1))
    let Lk := X - Qc
    let C := p' * q * Nat.card (FullFlagConfiguration m k)
    rw [rootPowerFiltration_finrank (r u) (h + 1) (doublyMarkedFlag_cutoff _ _ _ u)]
    calc ∑ i ∈ Finset.range (h + 1), Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V h ⧸
            rootPowerLayerIdeal (r u) i)
        ≤ ∑ i ∈ Finset.range (h + 1), (if i = 0 then L0 else if i < k then A
            else if i = k then Lk else C) := by
          apply Finset.sum_le_sum
          intro i hi
          have hih := Finset.mem_range.mp hi
          split_ifs with h0 h1 h2
          · subst h0
            apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u 0 _
              (doublyLayer_weak_le_ker (m + 2) V h u hu 0)).trans
            have hrec := hW k hk1 hk (deletedGroup u V) hV'
            rwa [show m + 1 - k = h by omega, hcard] at hrec
          · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
              (doublyLayer_same_le_ker (m + 2) V h u hu i (by omega))).trans
            have hrec := hD m rfl (k - 1) (by omega) (deletedGroup u V)
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
            have h3 : Qc ≤ Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) := by
              rw [hQ]
              exact hπ
            have h5 : Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
                singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h) ≤ X := hS
            show _ ≤ X - Qc
            apply Nat.le_sub_of_add_le
            calc _ ≤ Module.finrank ℂ (MvPolynomial (Fin (m + 2)) ℂ ⧸
                    (singlyMarkedFlagIdeal (m + 2) (deletedGroup u V) h ⊔
                      Ideal.span {flagGroupProduct (deletedGroup u V)ᶜ})) +
                    Module.finrank ℂ ((Ideal.span {πS}).restrictScalars ℂ) :=
                  Nat.add_le_add_left h3 _
              _ = _ := hsplit
              _ ≤ X := h5
          · apply (deletedLayer_finrank_le r (quotientRoot_aeval_surjective _) u i _
              (doublyLayer_lower_le_ker (m + 2) V h u hu k (by omega) (by omega) i
                (by omega))).trans
            have hrec := hD m rfl k (by omega) (deletedGroup u V)
            rwa [show m - k = h - 1 by omega, hcard] at hrec
      _ = L0 + (k - 1) * A + Lk + (h - k) * C :=
          sum_range_doubly_layers h k L0 A Lk C hk1 (by omega)
      _ ≤ Vᶜ.card * q * Nat.card (FullFlagConfiguration (m + 1) k) := by
          rw [← hcardc]
          have hR := fullFlagConfiguration_card_recursion m k (by omega)
          rw [show m + 1 - k - k = h - k by omega] at hR
          have hL0 : L0 = A + Qc := by
            simp only [L0, A, Qc, weakMarkedCount, Nat.pred_eq_sub_one,
              show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
          rw [hL0]
          have hX : Qc + Lk = X := Nat.add_sub_cancel' hQX
          calc A + Qc + (k - 1) * A + Lk + (h - k) * C
              = A + (k - 1) * A + (h - k) * C + (Qc + Lk) := by ring
            _ = A + (k - 1) * A + (h - k) * C + X := by rw [hX]
            _ ≤ (p' + 1) * q * Nat.card (FullFlagConfiguration (m + 1) k) := by
                simp only [A, C, X]
                rw [hR]
                apply le_of_eq
                obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
                simp only [Nat.add_sub_cancel]
                ring

/-- **Weak and doubly marked bounds**, by strong induction on `B`. -/
theorem markedFlag_bounds (B : ℕ) : WeakMarkedFlagBound B ∧ DoublyMarkedFlagBound B := by
  induction B using Nat.strong_induction_on with
  | _ B ih =>
      have hW : WeakMarkedFlagBound B := by
        match B, ih with
        | 0, _ => intro k hk1 hk; omega
        | 1, _ => intro k hk1 hk; omega
        | m + 2, ih => exact weakMarkedFlag_step m (ih (m + 1) (by omega)).1 (ih m (by omega)).2
      exact ⟨hW, doublyMarkedFlag_step B hW (fun m hm => (ih m (by omega)).2)⟩

/-- **The weak upper bound.** The weak full flag on `B + 1` roots with `k ≥ 1` doubles has
dimension at most
`p q (B-1)!/2^(k-1) + q C(q-1, 2) (B-2)!/2^(k-1)`. -/
theorem weakMarkedFlag_finrank_le (B k : ℕ) (hk1 : 1 ≤ k) (hk : 2 * k ≤ B)
    (V : Finset (Fin (B + 1))) (hV : V.Nonempty) :
    Module.finrank ℂ (WeakMarkedFlagRing (B + 1) V (B - k)) ≤
      weakMarkedCount Vᶜ.card V.card B k :=
  (markedFlag_bounds B).1 k hk1 hk V hV

/-- **The doubly marked upper bound.** The doubly marked full flag on `B + 2` roots with groups of
sizes `p` and `q` has dimension at most `p q B!/2^k`. -/
theorem doublyMarkedFlag_finrank_le (B k : ℕ) (hk : 2 * k ≤ B) (V : Finset (Fin (B + 2))) :
    Module.finrank ℂ (DoublyMarkedFlagRing (B + 2) V (B - k)) ≤
      Vᶜ.card * V.card * Nat.card (FullFlagConfiguration B k) :=
  (markedFlag_bounds B).2 k hk V

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.weakMarkedCount
#print axioms VOA.DeligneAudit.SL4T.quotient_sup_span_finrank
#print axioms VOA.DeligneAudit.SL4T.quotient_finrank_zero_of_empty_product
#print axioms VOA.DeligneAudit.SL4T.sum_range_weak_layers
#print axioms VOA.DeligneAudit.SL4T.sum_range_doubly_layers
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_univ_finrank_le
#print axioms VOA.DeligneAudit.SL4T.exists_notMem_of_ne_univ
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_step
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_step
#print axioms VOA.DeligneAudit.SL4T.markedFlag_bounds
#print axioms VOA.DeligneAudit.SL4T.weakMarkedFlag_finrank_le
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_finrank_le
