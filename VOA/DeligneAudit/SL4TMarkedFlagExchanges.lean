import VOA.DeligneAudit.SL4TMarkedFlagDeletion

/-!
# Layer relations after deleting a root of the first group

Let `x : Fin (n + 1) → A` be a coinvariant alphabet, `V` the second group and `u ∉ V` a root of
the first group. This file records the relations of the remaining roots that are used to present
the layers of `u`:

* products and power sums over `V` are unchanged by the deletion
  (`deletedGroupProduct_mem_of_zero`, `deletedGroupPowerSum_mem_of_zero`);
* the product of the remaining first-group roots times a positive power of `u` is the product
  of the whole first group (`deletedComplProduct_mem`);
* the power sums of the remaining first-group roots are `-p_s(V) - u^s`
  (`deletedFirstGroup_powerSum`), which with the vanishing complete functions gives the power-sum
  exchange (`firstGroup_powerSum_exchange`);
* `u^h` kills the product of the other roots of the first group
  (`firstGroup_power_product_zero`).
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

section Delete

variable {n : ℕ} (x : Fin (n + 1) → A) (V : Finset (Fin (n + 1))) (u : Fin (n + 1))

/-- The product over `V` after deleting a root outside `V`. -/
theorem deletedGroupProduct_mem_of_zero (hu : u ∉ V) (hV : ∏ i ∈ V, x i = 0) (i : ℕ) :
    (∏ j ∈ deletedGroup u V, x (u.succAbove j)) * x u ^ i ∈ Ideal.span {x u ^ (i + 1)} :=
  mul_mem_of_eq_zero _ _ ((prod_deletedGroup_of_notMem x V u hu).trans hV)

/-- A power sum over `V` after deleting a root outside `V`. -/
theorem deletedGroupPowerSum_mem_of_zero (hu : u ∉ V) (s : ℕ)
    (hV : ∑ i ∈ V, x i ^ s = 0) (i : ℕ) :
    (∑ j ∈ deletedGroup u V, x (u.succAbove j) ^ s) * x u ^ i ∈ Ideal.span {x u ^ (i + 1)} :=
  mul_mem_of_eq_zero _ _ ((sum_deletedGroup_of_notMem (fun i => x i ^ s) V u hu).trans hV)

/-- The deleted root times the product of the remaining roots of the first group is the product
of the first group. -/
theorem deletedComplProduct_eq (hu : u ∉ V) :
    x u * ∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) = ∏ i ∈ Vᶜ, x i := by
  rw [prod_eq_deletedGroup x Vᶜ u, if_pos (Finset.mem_compl.mpr hu), deletedGroup_compl]

/-- If the first group has vanishing product, its remaining roots have vanishing product in
every positive layer. -/
theorem deletedComplProduct_mem (hu : u ∉ V) (hU : ∏ i ∈ Vᶜ, x i = 0) (i : ℕ) (hi : 1 ≤ i) :
    (∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j)) * x u ^ i ∈
      Ideal.span {x u ^ (i + 1)} := by
  have h0 : (∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j)) * x u ^ i = 0 := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ', ← mul_assoc, mul_comm (∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j)) (x u),
      deletedComplProduct_eq x V u hu, hU, zero_mul]
  rw [h0]
  exact Ideal.zero_mem _

variable [Algebra ℂ A]

/-- The power sums of the remaining roots of the first group. -/
theorem deletedFirstGroup_powerSum (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hu : u ∉ V)
    (s : ℕ) (hs : 0 < s) :
    ∑ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) ^ s = -∑ i ∈ V, x i ^ s - x u ^ s := by
  have h0 := coinvariant_powerSum_zero x he s hs
  have hsplit := sum_eq_deletedGroup (fun i => x i ^ s) Vᶜ u
  rw [if_pos (Finset.mem_compl.mpr hu), deletedGroup_compl] at hsplit
  have hc := Finset.sum_compl_add_sum V (fun i => x i ^ s)
  rw [h0, hsplit] at hc
  linear_combination hc

omit [Algebra ℂ A] in
/-- Summing the vanishing two-root complete functions over the remaining first-group roots. -/
theorem firstGroup_powerSum_relation (hE : groupElementaryPolynomial x Finset.univ = 1)
    (hV : ∏ i ∈ V, x i = 0) (hu : u ∉ V) (M : ℕ) (hn : n + 1 = M + 2) :
    ∑ e ∈ Finset.range (M + 1),
      (∑ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) ^ e) * x u ^ (M - e) = 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hjV : u.succAbove j ∉ V := by
    rw [Finset.mem_compl, mem_deletedGroup] at hj
    exact hj
  apply pairComplete_vanish x hE (u.succAbove j) u (Fin.succAbove_ne u j) M (Or.inr ⟨?_, ?_⟩)
  · rw [pairComplement_card _ _ (Fin.succAbove_ne u j), Fintype.card_fin]
    omega
  · apply prod_eq_zero_of_subset x _ hV
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hjV (h ▸ hi), fun h => hu (h ▸ hi)⟩

/-- **Power-sum exchange**: with `M + 1 = K + h`, `h ≥ 2`, `n + 1 = M + 2`
roots and the power sums of `V` vanishing from `h` on, `p_(h-1)(V) u^K ∈ (u^(K+1))`. -/
theorem firstGroup_powerSum_exchange (he : D4Levi.ksEPoly (List.ofFn x) = 1)
    (hV : ∏ i ∈ V, x i = 0) (hu : u ∉ V) (h K M : ℕ) (hh : 2 ≤ h) (hM : M + 1 = K + h)
    (hn : n + 1 = M + 2) (htail : ∀ e, h ≤ e → ∑ i ∈ V, x i ^ e = 0) :
    (∑ i ∈ V, x i ^ (h - 1)) * x u ^ K ∈ Ideal.span {x u ^ (K + 1)} := by
  have hE : groupElementaryPolynomial x Finset.univ = 1 := by
    rw [← ksEPoly_ofFn_eq_group]
    exact he
  apply powerSum_boundary_mem (fun e => ∑ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) ^ e)
    (fun e => ∑ i ∈ V, x i ^ e) (x u) M K h hh hM
  · exact firstGroup_powerSum_relation x V u hE hV hu M hn
  · exact deletedFirstGroup_powerSum x V u he hu (h - 1) (by omega)
  · intro e he'
    rw [deletedFirstGroup_powerSum x V u he hu e (by omega), htail e he', neg_zero, zero_sub]

/-- If `p_h(V) = 0` and every root has cutoff `h + 1`, then `u^h` kills the product of
the remaining roots of the first group. -/
theorem firstGroup_power_product_zero (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hu : u ∉ V)
    (h : ℕ) (hh : 1 ≤ h) (htail : ∑ i ∈ V, x i ^ h = 0) (hc : ∀ i, x i ^ (h + 1) = 0) :
    x u ^ h * ∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) = 0 := by
  have hs := deletedFirstGroup_powerSum x V u he hu h (by omega)
  rw [htail, neg_zero, zero_sub] at hs
  have hz : (∑ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) ^ h) *
      ∏ j ∈ (deletedGroup u V)ᶜ, x (u.succAbove j) = 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.mul_prod_erase _ (fun j => x (u.succAbove j)) hj, ← mul_assoc, ← pow_succ,
      hc, zero_mul]
  rw [hs, neg_mul, neg_eq_zero] at hz
  exact hz

end Delete

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.deletedGroupProduct_mem_of_zero
#print axioms VOA.DeligneAudit.SL4T.deletedGroupPowerSum_mem_of_zero
#print axioms VOA.DeligneAudit.SL4T.deletedComplProduct_eq
#print axioms VOA.DeligneAudit.SL4T.deletedComplProduct_mem
#print axioms VOA.DeligneAudit.SL4T.deletedFirstGroup_powerSum
#print axioms VOA.DeligneAudit.SL4T.firstGroup_powerSum_relation
#print axioms VOA.DeligneAudit.SL4T.firstGroup_powerSum_exchange
#print axioms VOA.DeligneAudit.SL4T.firstGroup_power_product_zero
