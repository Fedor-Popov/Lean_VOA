import VOA.DeligneAudit.SL4TMiddleFlagPowerSum

/-! The composite Thom coefficients and vanishing of every wrong-order doubled pair. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {R : Type*} [CommRing R]

/-- An omitted factor can be written as a unit factor in a product over the full index set. -/
theorem product_except_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → R) (i : ι) :
    (∏ k ∈ Finset.univ.erase i, a k) = ∏ k, if k = i then 1 else a k := by
  rw [← Finset.prod_erase (Finset.univ : Finset ι) (f := fun k => if k = i then 1 else a k)
    (show (if i = i then (1 : R) else a i) = 1 by simp)]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [(Finset.mem_erase.mp hk).1, if_false]

/-- The composite coefficient of a forward site and a reverse site, using signed tops. -/
def orderedPairThom (a b : Fin 4 → R) (i j : Fin 4) : R :=
  (∏ k, if i < k then a k else 1) *
    ∏ k, if k < j then (if k = i then b i else a k) else 1

/-- A wrong-order pair contains the differentiated top and every complementary top. -/
theorem orderedPairThom_wrong_order (a b : Fin 4 → R) (i j : Fin 4) (hij : i < j) :
    orderedPairThom a b i j =
      (b i * ∏ k ∈ Finset.univ.erase i, a k) *
        ∏ k, if i < k ∧ k < j then a k else 1 := by
  rw [product_except_eq_ite]
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    simp [orderedPairThom, Fin.prod_univ_succ] <;> ring

/-- A surviving pair contains exactly the top factors outside its closed interval. -/
theorem orderedPairThom_surviving (a b : Fin 4 → R) (i j : Fin 4) (hji : j ≤ i) :
    orderedPairThom a b i j = ∏ k, if k < j ∨ i < k then a k else 1 := by
  change j.val ≤ i.val at hji
  fin_cases i <;> fin_cases j <;> norm_num at hji <;>
    simp [orderedPairThom, Fin.prod_univ_succ] <;> ring

/-- Original flag-block indices in the forward doubled-site order. -/
def doubledSiteFlagIndex (i : Fin 4) : Fin 4 := ![0, 2, 1, 3] i

/-- The signed top coefficient in doubled-site order. -/
def doubledSiteSignedTop (q : MixedParams) (i : Fin 4) : MixedRing q :=
  (middleFlagPolynomial q (doubledSiteFlagIndex i)).coeff 0

/-- The signed next-to-top coefficient in doubled-site order. -/
def doubledSiteSignedLinear (q : MixedParams) (i : Fin 4) : MixedRing q :=
  (middleFlagPolynomial q (doubledSiteFlagIndex i)).coeff 1

/-- Composite Thom classes before passing to the tail quotient. -/
def doubledSiteThomClass (q : MixedParams) (i j : Fin 4) : MixedRing q :=
  orderedPairThom (doubledSiteSignedTop q) (doubledSiteSignedLinear q) i j

set_option maxHeartbeats 800000 in
-- Expanding both four-factor products elaborates the nested mixed-ring instances repeatedly.
/-- The differentiated complementary product is the actual Cartan tail in site order. -/
theorem doubledSiteSignedLinear_tail (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (i : Fin 4) :
    doubledSiteSignedLinear q i * ∏ k ∈ Finset.univ.erase i, doubledSiteSignedTop q k =
      middleFlagTailSymbols q (q.B.toNat - 1) (doubledSiteFlagIndex i) := by
  rw [middleFlagTailSymbols_last_mode q hq hA hB, product_except_eq_ite,
    product_except_eq_ite]
  fin_cases i <;>
    simp [doubledSiteSignedLinear, doubledSiteSignedTop, doubledSiteFlagIndex,
      Fin.prod_univ_succ] <;> ring

/-- Every wrong-order composite Thom class belongs to the last-mode tail ideal. -/
theorem doubledSiteThomClass_wrong_order_mem (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (i j : Fin 4) (hij : i < j) :
    doubledSiteThomClass q i j ∈ middleFlagTailIdeal q (q.B.toNat - 1) := by
  rw [doubledSiteThomClass, orderedPairThom_wrong_order _ _ i j hij,
    doubledSiteSignedLinear_tail q hq hA hB]
  apply Ideal.mul_mem_right
  exact Ideal.subset_span ⟨doubledSiteFlagIndex i, rfl⟩

/-- All wrong-order composite cells vanish in the tail quotient, with arbitrary multipliers. -/
theorem doubledSiteThomClass_wrong_order_zero (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (i j : Fin 4) (hij : i < j) (x : MixedRing q) :
    Ideal.Quotient.mk (middleFlagTailIdeal q (q.B.toNat - 1))
      (doubledSiteThomClass q i j * x) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mul_mem_right _ _ (doubledSiteThomClass_wrong_order_mem q hq hA hB i j hij)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.product_except_eq_ite
#print axioms VOA.DeligneAudit.SL4T.orderedPairThom_wrong_order
#print axioms VOA.DeligneAudit.SL4T.orderedPairThom_surviving
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSignedLinear_tail
#print axioms VOA.DeligneAudit.SL4T.doubledSiteThomClass_wrong_order_mem
#print axioms VOA.DeligneAudit.SL4T.doubledSiteThomClass_wrong_order_zero
