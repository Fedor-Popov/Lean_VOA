import VOA.DeligneAudit.SL4TMarkedFlagComplementForm

/-!
# The two-minor stratum ideal of the doubly marked flag in complement form

Let `x` be a coinvariant alphabet on `n = h + 3` roots, `Y` with `|Y| = r ≥ 2` and nonempty
complement `Z`, `z = |Z|`, and `H_k` the coefficient of `t^k` in `∏_Z (1 - x t)`. For a column
`t^m` with `r ≤ m + 1` the two top rows of `t^m mod P_Y` are `H_(a+1) + ε H_a` and `H_a`,
`a = m + 1 - r`, `ε` the linear coefficient of `∏_Y (1 - x t)` (`topRow_pair_entries`). A two-minor
of columns `t^m`, `m ≥ h + 1`, is therefore the Hankel minor `H_(a+1) H_b - H_(b+1) H_a` with
`a, b ≥ z - 1`; since `H_k = 0` for `k > z`, it lies in `(H_z²)` (`hankel_two_mem`), and the
columns `t^(h+1)`, `t^(h+2)` give `H_z²` itself (`hankel_two_top`). As `H_z = ± ∏ Z`:

`G_2(t^(h+1)) = ((∏ Z)²)`   (`topIdeal_two_power_eq_sq`),

and the joint two-minor ideal with `s = 0` is the same (`jointTopIdeal_two_eq_sq_of_zero`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- A Hankel two-minor of a sequence vanishing beyond `z`, with indices at least `z - 1`. -/
theorem hankel_two_mem {C : Type*} [CommRing C] (H : ℕ → C) (z : ℕ)
    (hz : ∀ k, z < k → H k = 0) (ε : C) (a b : ℕ) (ha : z ≤ a + 1) (hb : z ≤ b + 1) :
    (H (a + 1) + ε * H a) * H b - (H (b + 1) + ε * H b) * H a ∈ Ideal.span {H z ^ 2} := by
  have hmem : ∀ c : C, c * H z ^ 2 ∈ Ideal.span {H z ^ 2} := fun c =>
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  rw [show (H (a + 1) + ε * H a) * H b - (H (b + 1) + ε * H b) * H a =
    H (a + 1) * H b - H (b + 1) * H a by ring]
  rcases (show a + 1 = z ∨ a = z ∨ z < a by omega) with ha' | ha' | ha'
  · rcases (show b + 1 = z ∨ b = z ∨ z < b by omega) with hb' | hb' | hb'
    · obtain rfl : a = b := by omega
      rw [sub_self]
      exact Ideal.zero_mem _
    · rw [ha', hb', hz (z + 1) (by omega), show H z * H z - 0 * H a = 1 * H z ^ 2 by ring]
      exact hmem 1
    · rw [hz b hb', hz (b + 1) (by omega), show H (a + 1) * 0 - 0 * H a = 0 * H z ^ 2 by ring]
      exact hmem 0
  · rcases (show b + 1 = z ∨ b = z ∨ z < b by omega) with hb' | hb' | hb'
    · rw [hz (a + 1) (by omega), ha', hb', show 0 * H b - H z * H z = (-1) * H z ^ 2 by ring]
      exact hmem (-1)
    · rw [hz (a + 1) (by omega), hz (b + 1) (by omega),
        show 0 * H b - 0 * H a = 0 * H z ^ 2 by ring]
      exact hmem 0
    · rw [hz (a + 1) (by omega), hz (b + 1) (by omega),
        show 0 * H b - 0 * H a = 0 * H z ^ 2 by ring]
      exact hmem 0
  · rw [hz a ha', hz (a + 1) (by omega), show 0 * H b - H (b + 1) * 0 = 0 * H z ^ 2 by ring]
    exact hmem 0

/-- The Hankel minor of the two columns just above the cutoff. -/
theorem hankel_two_top {C : Type*} [CommRing C] (H : ℕ → C) (z : ℕ) (hz1 : 1 ≤ z)
    (hz : ∀ k, z < k → H k = 0) (ε : C) :
    (H (z - 1 + 1) + ε * H (z - 1)) * H z - (H (z + 1) + ε * H z) * H (z - 1) = H z ^ 2 := by
  rw [Nat.sub_add_cancel hz1, hz (z + 1) (by omega)]
  ring

variable {C : Type*} [CommRing C] {n : ℕ} (x : Fin n → C)
  (hE : groupElementaryPolynomial x Finset.univ = 1)
include hE

/-- The two top rows of a remainder in complement form. -/
theorem topRow_pair_entries (Y : Finset (Fin n)) (hY2 : 2 ≤ Y.card) (m : ℕ)
    (hm : Y.card ≤ m + 1) :
    ((X : C[X]) ^ m %ₘ alphabetCharacteristic (Y.toList.map x)).coeff (Y.card - 2) =
        (groupElementaryPolynomial x Yᶜ).coeff (m + 1 - Y.card + 1) +
          (groupElementaryPolynomial x Y).coeff 1 *
            (groupElementaryPolynomial x Yᶜ).coeff (m + 1 - Y.card) ∧
      ((X : C[X]) ^ m %ₘ alphabetCharacteristic (Y.toList.map x)).coeff (Y.card - 2 + 1) =
        (groupElementaryPolynomial x Yᶜ).coeff (m + 1 - Y.card) := by
  have hY : Y.Nonempty := Finset.card_pos.mp (by omega)
  constructor
  · have hlen : (Y.toList.map x).length = Y.card := by simp
    have h := alphabetPowerRemainder_coeff (Y.toList.map x) m (Y.card - 2)
      (by rw [hlen]; omega)
    rw [hlen, show Y.card - (Y.card - 2) = 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_one] at h
    change alphabetPowerRemainder (Y.toList.map x) m (Y.card - 2) = _
    rw [h]
    split_ifs
    · rw [ksEPoly_toList_map, groupElementaryPolynomial_coeff_zero, one_mul, ksHSeries_toList_map,
        groupCompleteSeries_eq_complement x Y hE, Polynomial.coeff_coe, Polynomial.coeff_coe,
        show m - (Y.card - 2) - 0 = m + 1 - Y.card + 1 by omega,
        show m - (Y.card - 2) - 1 = m + 1 - Y.card by omega]
    all_goals omega
  · rw [show Y.card - 2 + 1 = Y.card - 1 by omega, topRemainder_eq_complement x hE Y hY m,
      if_pos hm]

/-- **The two-minor ideal of the doubly marked flag**: `((∏ Z)²)`. -/
theorem topIdeal_two_power_eq_sq (Y : Finset (Fin n)) (hY2 : 2 ≤ Y.card) (hZ : Yᶜ.Nonempty)
    (h : ℕ) (hh : h + 3 - Y.card = Yᶜ.card) :
    polynomialSubmoduleTopIdeal (alphabetCharacteristic (Y.toList.map x)) Y.card 2
        ((Ideal.span {(X : C[X]) ^ (h + 1)}).restrictScalars C) =
      Ideal.span {(∏ i ∈ Yᶜ, x i) ^ 2} := by
  set H : ℕ → C := fun k => (groupElementaryPolynomial x Yᶜ).coeff k with hH
  have hz1 : 1 ≤ Yᶜ.card := Finset.card_pos.mpr hZ
  have hz : ∀ k, Yᶜ.card < k → H k = 0 := fun k hk =>
    groupElementaryPolynomial_coeff_eq_zero _ _ _ hk
  have hHz : H Yᶜ.card ^ 2 = (∏ i ∈ Yᶜ, x i) ^ 2 := by
    simp only [hH]
    rw [groupElementaryPolynomial_coeff_card, mul_pow, ← pow_mul, mul_comm Yᶜ.card 2, pow_mul,
      neg_one_sq, one_pow, one_mul]
  rw [← hHz]
  apply le_antisymm
  · refine topIdeal_le_of_span _ _ _ _ {u | ∃ c, u = X ^ c * X ^ (h + 1)} ?_ _ ?_
    · intro f hf
      rw [Submodule.restrictScalars_mem] at hf
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      exact mul_mem_span_X_pow_mul _ g
    · intro u hu
      obtain ⟨c₀, hc₀⟩ := hu 0
      obtain ⟨c₁, hc₁⟩ := hu 1
      simp only [Matrix.det_fin_two, topRowFunctional_apply, Fin.val_zero, Fin.val_one,
        Nat.add_zero]
      rw [hc₀, hc₁, ← pow_add, ← pow_add,
        (topRow_pair_entries x hE Y hY2 (c₀ + (h + 1)) (by omega)).1,
        (topRow_pair_entries x hE Y hY2 (c₀ + (h + 1)) (by omega)).2,
        (topRow_pair_entries x hE Y hY2 (c₁ + (h + 1)) (by omega)).1,
        (topRow_pair_entries x hE Y hY2 (c₁ + (h + 1)) (by omega)).2]
      exact hankel_two_mem H Yᶜ.card hz _ _ _ (by omega) (by omega)
  · apply Ideal.span_le.mpr
    rintro a rfl
    have hmem := topIdeal_det_mem (alphabetCharacteristic (Y.toList.map x)) Y.card 2
      ((Ideal.span {(X : C[X]) ^ (h + 1)}).restrictScalars C)
      (fun b => (X : C[X]) ^ (h + 1 + b.val))
      (fun b => by
        rw [Submodule.restrictScalars_mem]
        change (X : C[X]) ^ (h + 1 + b.val) ∈ Ideal.span {(X : C[X]) ^ (h + 1)}
        rw [pow_add (X : C[X]) (h + 1) b.val]
        exact Ideal.mul_mem_right ((X : C[X]) ^ b.val) _
          (Ideal.mem_span_singleton_self ((X : C[X]) ^ (h + 1))))
    simp only [Matrix.det_fin_two, topRowFunctional_apply, Fin.val_zero, Fin.val_one,
      Nat.add_zero] at hmem
    rw [(topRow_pair_entries x hE Y hY2 (h + 1) (by omega)).1,
      (topRow_pair_entries x hE Y hY2 (h + 1) (by omega)).2,
      (topRow_pair_entries x hE Y hY2 (h + 1 + 1) (by omega)).1,
      (topRow_pair_entries x hE Y hY2 (h + 1 + 1) (by omega)).2,
      show h + 1 + 1 - Y.card = Yᶜ.card - 1 by omega,
      show h + 1 + 1 + 1 - Y.card = Yᶜ.card by omega] at hmem
    have htop := hankel_two_top H Yᶜ.card hz1 hz ((groupElementaryPolynomial x Y).coeff 1)
    simp only [hH] at htop
    rw [htop] at hmem
    exact hmem

/-- **The joint two-minor ideal of the doubly marked flag** (`s = 0`): `((∏ Z)²)`. -/
theorem jointTopIdeal_two_eq_sq_of_zero (Y : Finset (Fin n)) (hY2 : 2 ≤ Y.card)
    (hZ : Yᶜ.Nonempty) (h : ℕ) (hh : h + 3 - Y.card = Yᶜ.card) :
    polynomialSubmoduleTopIdeal (alphabetCharacteristic (Y.toList.map x)) Y.card 2
        ((Ideal.span {(X : C[X]) ^ (h + 1), Polynomial.C 0 * X ^ h}).restrictScalars C) =
      Ideal.span {(∏ i ∈ Yᶜ, x i) ^ 2} := by
  rw [jointTopIdeal_eq_sup, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul, sup_bot_eq,
    topIdeal_two_power_eq_sq x hE Y hY2 hZ h hh]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.hankel_two_mem
#print axioms VOA.DeligneAudit.SL4T.hankel_two_top
#print axioms VOA.DeligneAudit.SL4T.topRow_pair_entries
#print axioms VOA.DeligneAudit.SL4T.topIdeal_two_power_eq_sq
#print axioms VOA.DeligneAudit.SL4T.jointTopIdeal_two_eq_sq_of_zero
