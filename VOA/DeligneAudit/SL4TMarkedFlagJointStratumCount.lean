import VOA.DeligneAudit.SL4TMarkedFlagStratumExactness

/-!
# Dimensions of the joint top-row stratum quotients of the marked full flags

For the marked full flags with one double, the quotient of the flag ring `C` by the joint
top-row minor ideal `G_j` of `(t^(h+1), s t^h)` modulo `P_Y` (the ideal that descends to
`adjointSiteJointTopIdeal`) has dimension exactly the number of configurations with fewer than
`j` selected doubles:

* singly marked, `s = ∏ (V ∩ Y)`, `j = 1` (`singlyMarkedFlag_jointStratum_finrank`);
* doubly marked, `s = 0`, `j = 1, 2` (`doublyMarkedFlag_jointStratum_one_finrank`,
  `doublyMarkedFlag_jointStratum_two_finrank`).

The proofs combine the complement forms of `G_j` with the exactness theorems of
`SL4TMarkedFlagStratumExactness`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

/-- The dimension of `C ⧸ J.map mk` is that of the polynomial quotient by `I ⊔ J`. -/
theorem quotient_map_finrank {n : ℕ} (I J : Ideal (MvPolynomial (Fin n) ℂ)) :
    Module.finrank ℂ ((MvPolynomial (Fin n) ℂ ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) =
      Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ (I ⊔ J)) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ ℂ I J).toLinearEquiv.finrank_eq

/-- **Singly marked joint stratum.** `dim C/G_1 = #{configurations without a selected double}`
for the singly marked flag on `m + 2` roots with joint symbol `s = ∏ (V ∩ Y)`. -/
theorem singlyMarkedFlag_jointStratum_finrank (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 2))) (hV : V.Nonempty) (hY : Y.Nonempty) (hZ : Yᶜ.Nonempty) :
    Module.finrank ℂ (SinglyMarkedFlagRing (m + 2) V m ⧸
      polynomialSubmoduleTopIdeal
        (alphabetCharacteristic (Y.toList.map (quotientRoot (singlyMarkedFlagIdeal (m + 2) V m))))
        Y.card 1
        ((Ideal.span {(Polynomial.X : Polynomial (SinglyMarkedFlagRing (m + 2) V m)) ^ (m + 1),
          Polynomial.C (∏ i ∈ V ∩ Y, quotientRoot (singlyMarkedFlagIdeal (m + 2) V m) i) *
            Polynomial.X ^ m}).restrictScalars (SinglyMarkedFlagRing (m + 2) V m))) =
      Nat.card {c : SinglyMarkedConfiguration (m + 1) 1 V //
        singlyMarkedSelectedDoubles Y c < 1} := by
  classical
  have hYc : Y.card + Yᶜ.card = m + 2 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  rw [jointTopIdeal_one_eq_pair _ (singlyMarkedFlag_group_elementary (m + 2) V m) Y hY hZ m
    (by omega)]
  have hmap : Ideal.span {∏ i ∈ Yᶜ, quotientRoot (singlyMarkedFlagIdeal (m + 2) V m) i,
      (∏ i ∈ V ∩ Y, quotientRoot (singlyMarkedFlagIdeal (m + 2) V m) i) *
        groupSubtopCoefficient (quotientRoot (singlyMarkedFlagIdeal (m + 2) V m)) Yᶜ} =
      (Ideal.span {∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin (m + 2)) ℂ),
        (∏ i ∈ V ∩ Y, (X i : MvPolynomial (Fin (m + 2)) ℂ)) *
          groupSubtopCoefficient X Yᶜ}).map
        (Ideal.Quotient.mk (singlyMarkedFlagIdeal (m + 2) V m)) := by
    rw [Ideal.map_span, Set.image_pair, map_mul, map_prod, map_prod, groupSubtopCoefficient_map]
    rfl
  rw [hmap, quotient_map_finrank]
  exact singlyMarkedSelectedStratum_finrank m hm V Y hV hY hZ

/-- The doubly marked stratum quotient has dimension the number of configurations with fewer
than `j` selected doubles, for an ideal equal to the leading relations. -/
theorem doublyMarkedStratum_finrank_of_eq (m j : ℕ) (V Y : Finset (Fin (m + 3)))
    (I : Ideal (MvPolynomial (Fin (m + 3)) ℂ))
    (hI : ∀ ζ : Fin (m + 1 - 1) → ℂ, Function.Injective ζ → (∀ a, ζ a ≠ 0) →
      I = pointInitialIdeal (doublyMarkedStratumPoint (m + 1) 1 j V Y ζ)) :
    Module.finrank ℂ (MvPolynomial (Fin (m + 3)) ℂ ⧸ I) =
      Nat.card {c : DoublyMarkedConfiguration (m + 1) 1 V //
        doublyMarkedSelectedDoubles Y c < j} := by
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
  have hinj : Function.Injective (doublyMarkedStratumPoint (m + 1) 1 j V Y ζ) :=
    fun a b h => Subtype.ext (doublyMarkedPoint_injective _ _ V ζ hζ hζ0 h)
  rw [hI ζ hζ hζ0, (pointInitialQuotient_finrank _ hinj).2, Nat.card_eq_fintype_card]

/-- **Doubly marked joint stratum, `j = 1`.** -/
theorem doublyMarkedFlag_jointStratum_one_finrank (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY : Y.Nonempty)
    (hZ : Yᶜ.Nonempty) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V m ⧸
      polynomialSubmoduleTopIdeal
        (alphabetCharacteristic (Y.toList.map (quotientRoot (doublyMarkedFlagIdeal (m + 3) V m))))
        Y.card 1
        ((Ideal.span {(Polynomial.X : Polynomial (DoublyMarkedFlagRing (m + 3) V m)) ^ (m + 1),
          Polynomial.C 0 * Polynomial.X ^ m}).restrictScalars
            (DoublyMarkedFlagRing (m + 3) V m))) =
      Nat.card {c : DoublyMarkedConfiguration (m + 1) 1 V //
        doublyMarkedSelectedDoubles Y c < 1} := by
  classical
  have hYc : Y.card + Yᶜ.card = m + 3 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  rw [jointTopIdeal_one_eq_pair_of_zero _ (doublyMarkedFlag_group_elementary (m + 3) V m) Y hY hZ
    m (by omega)]
  have hmap := doublyMarkedStratumIdeal_map_span (doublyMarkedFlagIdeal (m + 3) V m) Y
  rw [doublyMarkedStratumIdeal] at hmap
  rw [← hmap, quotient_map_finrank]
  exact doublyMarkedStratum_finrank_of_eq m 1 V Y _
    (fun ζ hζ hζ0 => doublyMarkedOneSelectedStratumIdeal_eq m hm V Y hV hU hY hZ ζ hζ hζ0)

/-- **Doubly marked joint stratum, `j = 2`.** -/
theorem doublyMarkedFlag_jointStratum_two_finrank (m : ℕ) (hm : 1 ≤ m)
    (V Y : Finset (Fin (m + 3))) (hV : V.Nonempty) (hU : Vᶜ.Nonempty) (hY2 : 2 ≤ Y.card)
    (hZ : Yᶜ.Nonempty) :
    Module.finrank ℂ (DoublyMarkedFlagRing (m + 3) V m ⧸
      polynomialSubmoduleTopIdeal
        (alphabetCharacteristic (Y.toList.map (quotientRoot (doublyMarkedFlagIdeal (m + 3) V m))))
        Y.card 2
        ((Ideal.span {(Polynomial.X : Polynomial (DoublyMarkedFlagRing (m + 3) V m)) ^ (m + 1),
          Polynomial.C 0 * Polynomial.X ^ m}).restrictScalars
            (DoublyMarkedFlagRing (m + 3) V m))) =
      Nat.card {c : DoublyMarkedConfiguration (m + 1) 1 V //
        doublyMarkedSelectedDoubles Y c < 2} := by
  classical
  have hYc : Y.card + Yᶜ.card = m + 3 := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  rw [jointTopIdeal_two_eq_sq_of_zero _ (doublyMarkedFlag_group_elementary (m + 3) V m) Y hY2 hZ
    m (by omega)]
  have hmap :
      Ideal.span {(∏ i ∈ Yᶜ, quotientRoot (doublyMarkedFlagIdeal (m + 3) V m) i) ^ 2} =
      (Ideal.span {(∏ i ∈ Yᶜ, (X i : MvPolynomial (Fin (m + 3)) ℂ)) ^ 2}).map
        (Ideal.Quotient.mk (doublyMarkedFlagIdeal (m + 3) V m)) := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, map_prod]
    rfl
  rw [hmap, quotient_map_finrank]
  exact doublyMarkedStratum_finrank_of_eq m 2 V Y _
    (fun ζ hζ hζ0 => doublyMarkedTwoSelectedStratumIdeal_eq m hm V Y hV hU hY2 hZ ζ hζ hζ0)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.quotient_map_finrank
#print axioms VOA.DeligneAudit.SL4T.singlyMarkedFlag_jointStratum_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedStratum_finrank_of_eq
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_jointStratum_one_finrank
#print axioms VOA.DeligneAudit.SL4T.doublyMarkedFlag_jointStratum_two_finrank
