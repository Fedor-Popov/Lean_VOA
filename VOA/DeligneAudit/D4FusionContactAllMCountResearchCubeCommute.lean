import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeOrders
import Mathlib.RingTheory.Derivation.Lie

/-! Whole cube lowerings commute. In particular the cubic polar selected by
the quintic probe is a relabeled sorted orbit, not a differentiated projection. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

theorem orderNext_commute : ∀ (d e : Fin 3) (i : Fin 8),
    (orderNext e i).bind (orderNext d) = (orderNext d i).bind (orderNext e) := by
  decide +kernel

variable (K : Type*) [CommRing K]

def stepValue (t : Option (Fin 8)) : P8 K :=
  match t with
  | none => 0
  | some j => MvPolynomial.X j

theorem orderLower_step (d : Fin 3) (t : Option (Fin 8)) :
    orderLower K d (stepValue K t) = stepValue K (t.bind (orderNext d)) := by
  cases t with
  | none => exact map_zero _
  | some i => exact orderLower_X K d i

theorem orderLower_commute (d e : Fin 3) :
    Function.Commute (orderLower K d : P8 K → P8 K) (orderLower K e : P8 K → P8 K) := by
  have hz : ⁅orderLower K d,orderLower K e⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    change orderLower K d (orderLower K e (MvPolynomial.X i)) -
      orderLower K e (orderLower K d (MvPolynomial.X i)) = 0
    rw [orderLower_X,orderLower_X]
    change orderLower K d (stepValue K (orderNext e i)) -
      orderLower K e (stepValue K (orderNext d i)) = 0
    rw [orderLower_step,orderLower_step,orderNext_commute,sub_self]
  intro p
  apply sub_eq_zero.mp
  change ⁅orderLower K d,orderLower K e⁆ p = 0
  rw [hz]
  rfl

/-- The order 3,1,2 gives the original margins b,c,a. -/
theorem rotate_order_orbit (r a b c : ℕ) :
    orderRename K 4 (orbit K r a b c) = orbit K r b c a := by
  rw [orderRename_orbit]
  change ((orderLower K 1 : _ → _)^[c])
      (((orderLower K 0 : _ → _)^[b])
        (((orderLower K 2 : _ → _)^[a]) (MvPolynomial.X 0^r))) =
    ((orderLower K 2 : _ → _)^[a])
      (((orderLower K 1 : _ → _)^[c])
        (((orderLower K 0 : _ → _)^[b]) (MvPolynomial.X 0^r)))
  rw [(orderLower_commute K 0 2).iterate_iterate b a,
    (orderLower_commute K 1 2).iterate_iterate c a]

theorem rotate_cubic_head : orderRename K 4 (chainTerm K 3 2 1 1) =
    (12 : P8 K) * MvPolynomial.X 0 * MvPolynomial.X 4 * MvPolynomial.X 7 := by
  simp only [chainTerm,orderRename,map_mul,map_pow,map_natCast,MvPolynomial.rename_X]
  change (12 : P8 K) * MvPolynomial.X 0^1 * MvPolynomial.X 4^1 *
    MvPolynomial.X 5^0 * MvPolynomial.X 7^1 = _
  simp only [pow_one,pow_zero,mul_one]

/-- Exact uniform cubic polar head used by the whole quintic source family. -/
theorem cubic_polar_sub_head_mem :
    orbit K 3 1 1 2 - (12 : P8 K) * MvPolynomial.X 0 * MvPolynomial.X 4 *
      MvPolynomial.X 7 ∈ colorLow K 10 := by
  have h := order_orbit_sub_chainTerm_mem K 4 3 2 1 1 (by omega) (by omega) (by omega)
  rw [rotate_order_orbit,rotate_cubic_head] at h
  exact h

end
#print axioms orderLower_commute
#print axioms cubic_polar_sub_head_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
