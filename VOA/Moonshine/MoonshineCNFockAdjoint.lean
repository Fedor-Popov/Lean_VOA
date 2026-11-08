import VOA.Moonshine.NondegLattice
import VOA.Moonshine.MoonshineCNVirasoro

/-! Adjointness of the complex-frame oscillators and Sugawara operators. -/

namespace VOA.Moonshine.ConwayNorton

open Module (End)
open IntegralLattice HeisenbergN Nondeg

theorem uForm_sugawaraTerm_adjoint (r : ℕ) (a : Fin r) (m j : ℤ) (p q : FockN r) :
    uForm r (sugTermN r 1 a m j p) q = uForm r p (sugTermN r 1 a (-m) (-j) q) := by
  by_cases hj : j = 0
  · subst j; simp [sugTermN_apply]
  · by_cases hjn : j < 0
    · rw [sugTermN_apply, if_pos hjn, sugTermN_apply, if_neg (by omega),
        uForm_oscN, uForm_oscN, neg_neg]
      rw [show -m - -j = -(m - j) from by omega]
    · rw [sugTermN_apply, if_neg hjn, sugTermN_apply, if_pos (by omega),
        uForm_oscN, uForm_oscN, neg_neg]
      rw [show -m - -j = -(m - j) from by omega]

/-- The Fock bilinear form makes `Lₙ` adjoint to `L₋ₙ` in every rank. -/
theorem uForm_virasoro_adjoint (r : ℕ) (n : ℤ) (p q : FockN r) :
    uForm r (LvirN r 1 n p) q = uForm r p (LvirN r 1 (-n) q) := by
  have hsingle : ∀ a : Fin r,
      uForm r (LvirNa r 1 a n p) q = uForm r p (LvirNa r 1 a (-n) q) := by
    intro a
    rw [LvirNa_apply', LvirNa_apply', map_smul, LinearMap.smul_apply, map_smul]
    congr 1
    change (uForm r).flip q (∑ᶠ j, sugTermN r 1 a n j p) =
      uForm r p (∑ᶠ j, sugTermN r 1 a (-n) j q)
    rw [map_finsum _ (sugTermN_support_finite r 1 a n p),
      map_finsum _ (sugTermN_support_finite r 1 a (-n) q)]
    calc
      _ = ∑ᶠ j : ℤ, uForm r p (sugTermN r 1 a (-n) (-j) q) :=
        finsum_congr fun j => uForm_sugawaraTerm_adjoint r a n j p q
      _ = _ := finsum_comp_equiv (f := fun j => uForm r p (sugTermN r 1 a (-n) j q))
        (Equiv.neg ℤ)
  simp only [LvirN, LinearMap.coe_sum, Finset.sum_apply, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun a _ => hsingle a

theorem uForm_frameOscillator_adjoint {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (α : L.carrier) (n : ℤ) (p q : FockN (rank L)) :
    uForm (rank L) (frameOscillator F α n p) q =
      -uForm (rank L) p (frameOscillator F α (-n) q) := by
  simp only [frameOscillator_apply_sum, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, uForm_oscN, mul_neg, Finset.sum_neg_distrib]

end VOA.Moonshine.ConwayNorton
