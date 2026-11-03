import VOA.DeligneAudit.D4CharDownGamma

/-! Euler factors with a formal Laurent variable marking the last GL coordinate. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- Reciprocal Pochhammer coefficients commute with every coefficient-ring map. -/
theorem gtInvPoch_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : R) (h : PochhammerUnits q) (k : ℤ) :
    φ (gtInvPoch q h k) = gtInvPoch (φ q) (gtPochhammerUnits_map φ q h) k := by
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    apply (gtPochhammerUnits_map φ q h n).mul_left_cancel
    have hp : φ (CarrierChain.qpochGen q n) = CarrierChain.qpochGen (φ q) n := by
      simp [CarrierChain.qpochGen, map_prod]
    rw [← hp, ← map_mul, gtPoch_mul_invPoch, map_one, hp, gtPoch_mul_invPoch]
  · rw [gtInvPoch_of_neg q h (by omega), map_zero,
      gtInvPoch_of_neg (φ q) (gtPochhammerUnits_map φ q h) (by omega)]

/-- The univariate Laurent coefficient ring for the removed coordinate w. -/
abbrev GTLastLaurent (R : Type*) [CommRing R] := AddMonoidAlgebra R ℤ

def gtLastC : R →+* GTLastLaurent R := AddMonoidAlgebra.singleZeroRingHom

@[simp] theorem gtLastC_apply (r : R) : gtLastC r = AddMonoidAlgebra.single 0 r := rfl

/-- Tag the nth power-series coefficient with w^(n*d). -/
def gtLastTag (d : ℤ) : PowerSeries R →+* PowerSeries (GTLastLaurent R) :=
  (rescale (AddMonoidAlgebra.single d 1)).comp (PowerSeries.map gtLastC)

theorem coeff_gtLastTag (d : ℤ) (F : PowerSeries R) (n : ℕ) :
    coeff n (gtLastTag d F) = AddMonoidAlgebra.single (n • d) (coeff n F) := by
  simp only [gtLastTag, RingHom.comp_apply, coeff_rescale, coeff_map,
    AddMonoidAlgebra.single_pow, one_pow, gtLastC_apply, AddMonoidAlgebra.single_mul_single,
    add_zero, one_mul]

/-- Tagging is the actual Euler substitution x -> x*w^d, including inverse w. -/
theorem gtLastTag_eulerInv (q : R) (h : PochhammerUnits q) (d : ℤ) (x : R) :
    gtLastTag d (gtEulerInv q h x) =
      gtEulerInv (gtLastC q) (gtPochhammerUnits_map gtLastC q h)
        (AddMonoidAlgebra.single d x) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_gtLastTag]
  simp only [gtEulerInv, coeff_mk, AddMonoidAlgebra.single_pow]
  rw [← gtInvPoch_map gtLastC q h, gtLastC_apply,
    AddMonoidAlgebra.single_mul_single, zero_add]

/-- The last-coordinate positive or negative Euler product has one-row coefficients. -/
theorem gtLastEuler_product_coeff (q : R) (h : PochhammerUnits q)
    (x : ℕ → Rˣ) (d : ℤ) (N k : ℕ) :
    coeff k (∏ i ∈ Finset.range N,
      gtEulerInv (gtLastC q) (gtPochhammerUnits_map gtLastC q h)
        (AddMonoidAlgebra.single d (x i : R))) =
      AddMonoidAlgebra.single (k • d) (gtOneRowCoeff q h x N k) := by
  simp_rw [← gtLastTag_eulerInv q h d]
  rw [← map_prod, coeff_gtLastTag, gtEulerInv_product_coeff]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtInvPoch_map
#print axioms VOA.DeligneAudit.D4Char.coeff_gtLastTag
#print axioms VOA.DeligneAudit.D4Char.gtLastTag_eulerInv
#print axioms VOA.DeligneAudit.D4Char.gtLastEuler_product_coeff
