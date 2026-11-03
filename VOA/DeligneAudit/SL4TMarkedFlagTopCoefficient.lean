import VOA.DeligneAudit.SL4TMarkedFlagIdentities

/-!
# The top-coefficient identity of a coinvariant alphabet with a vanishing group product

The identity is stated in the reversed form used by the signed elementary polynomials.

Let `x` be a coinvariant alphabet, `V` a group of roots with `∏ V = 0`, and `u` a root outside
`V`; put `U' = Vᶜ ∖ {u}`. Then

`top(∏_{U'} (1 - x t)) · top(∏_V (1 - x t)) = u^(|U'| + |V| - 1)`,

where `top` is the coefficient of `t^|U'|`, respectively `t^(|V| - 1)`
(`coinvariant_topCoefficient_product`). Indeed `∏_{U'} (1 - x t) · ∏_V (1 - x t)` is the inverse
of `1 - u t`, the first factor has degree at most `|U'|` and the second at most `|V| - 1` because
its coefficient of `t^|V|` is `± ∏ V = 0`. In signed form,
`(-1)^|U'| ∏ U' · c_(|V|-1)(V) = u^(|U'| + |V| - 1)`
(`coinvariant_product_topCoefficient`), where `c_(|V|-1)(V) = (-1)^(|V|-1) e_(|V|-1)(V)`.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A group with vanishing product has signed elementary polynomial of degree below its size. -/
theorem groupElementaryPolynomial_natDegree_le_pred (x : ι → A) (V : Finset ι)
    (hV : ∏ i ∈ V, x i = 0) :
    (groupElementaryPolynomial x V).natDegree ≤ V.card - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases Nat.lt_or_ge V.card N with h | h
  · exact groupElementaryPolynomial_coeff_eq_zero x V N h
  · obtain rfl : N = V.card := by omega
    rw [groupElementaryPolynomial_coeff_card, hV, mul_zero]

/-- **Top-coefficient identity.** -/
theorem coinvariant_topCoefficient_product (x : ι → A)
    (hE : groupElementaryPolynomial x Finset.univ = 1) (V : Finset ι) (hV : ∏ i ∈ V, x i = 0)
    (u : ι) (hu : u ∉ V) :
    (groupElementaryPolynomial x (Vᶜ.erase u)).coeff (Vᶜ.erase u).card *
        (groupElementaryPolynomial x V).coeff (V.card - 1) =
      x u ^ ((Vᶜ.erase u).card + (V.card - 1)) := by
  have hsplit : groupElementaryPolynomial x Finset.univ =
      (1 - Polynomial.C (x u) * Polynomial.X) *
        (groupElementaryPolynomial x (Vᶜ.erase u) * groupElementaryPolynomial x V) := by
    rw [groupElementaryPolynomial, groupElementaryPolynomial, groupElementaryPolynomial,
      ← mul_assoc, Finset.mul_prod_erase _ (fun i => 1 - Polynomial.C (x i) * Polynomial.X)
        (Finset.mem_compl.mpr hu), ← Finset.prod_union disjoint_compl_left,
      Finset.union_comm, Finset.union_compl]
  have hgeo : ((groupElementaryPolynomial x (Vᶜ.erase u) * groupElementaryPolynomial x V :
      Polynomial A) : PowerSeries A) = D4Levi.ksGeometricSeries (x u) := by
    have h1 := congrArg (fun P : Polynomial A => (P : PowerSeries A)) hsplit
    simp only [hE, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_C, Polynomial.coe_X] at h1
    have h2 := congrArg (fun S => D4Levi.ksGeometricSeries (x u) * S) h1
    simp only [mul_one, ← mul_assoc, D4Levi.ksGeometricSeries_mul_linear, one_mul] at h2
    rw [Polynomial.coe_mul]
    exact h2.symm
  have hc := congrArg (PowerSeries.coeff ((Vᶜ.erase u).card + (V.card - 1))) hgeo
  rw [Polynomial.coeff_coe, Polynomial.coeff_mul_add_eq_of_natDegree_le
    (groupElementaryPolynomial_natDegree_le x _)
    (groupElementaryPolynomial_natDegree_le_pred x V hV)] at hc
  rw [hc]
  simp [D4Levi.ksGeometricSeries]

/-- **Top-coefficient identity, signed form.** -/
theorem coinvariant_product_topCoefficient (x : ι → A)
    (hE : groupElementaryPolynomial x Finset.univ = 1) (V : Finset ι) (hV : ∏ i ∈ V, x i = 0)
    (u : ι) (hu : u ∉ V) :
    (-1) ^ (Vᶜ.erase u).card * (∏ i ∈ Vᶜ.erase u, x i) *
        (groupElementaryPolynomial x V).coeff (V.card - 1) =
      x u ^ ((Vᶜ.erase u).card + (V.card - 1)) := by
  rw [← groupElementaryPolynomial_coeff_card]
  exact coinvariant_topCoefficient_product x hE V hV u hu

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_natDegree_le_pred
#print axioms VOA.DeligneAudit.SL4T.coinvariant_topCoefficient_product
#print axioms VOA.DeligneAudit.SL4T.coinvariant_product_topCoefficient
