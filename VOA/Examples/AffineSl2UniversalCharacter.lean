/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ChargeDecomposition
import VOA.Commutative.WeightedPolynomialHilbert

/-! # The actual universal affine PBW character -/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA QSeries
noncomputable section

/-- Positive creation-mode weight on actual ordered PBW letters. -/
def currentWeight (q : Fin 3 ×ₗ ℕ) : ℕ := (ofLex q).2+1

theorem currentEnergy_weight (mu : CurrentIndex) :
    (Finsupp.weight currentWeight mu : ℤ) = currentEnergy mu := by
  rw [currentEnergy_sum,Finsupp.weight_apply]
  simp [Finsupp.sum,nsmul_eq_mul,currentWeight]

def cutoffMode (N : ℕ) (q : Fin 3×Fin (N+1)) : Fin 3 ×ₗ ℕ := toLex (q.1,q.2.val)

theorem cutoffMode_injective (N : ℕ) : Function.Injective (cutoffMode N) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ he
  change toLex (a,i.val)=toLex (b,j.val) at he
  have he' : (a,i.val)=(b,j.val) := congrArg ofLex he
  have ha := congrArg Prod.fst he'
  have hi := congrArg Prod.snd he'
  exact Prod.ext ha (Fin.ext hi)

theorem currentWeight_cutoff (N : ℕ) (p : (Fin 3×Fin (N+1)) →₀ ℕ) :
    Finsupp.weight currentWeight (Finsupp.mapDomain (cutoffMode N) p) =
      Finsupp.weight (fun q : Fin 3×Fin (N+1) => q.2.val+1) p := by
  rw [Finsupp.weight_apply,Finsupp.sum_mapDomain_index]
  · rfl
  · intro q; simp
  · intro q a b; simp [add_mul]

/-- An actual energy-N occupation has no current mode beyond the finite cutoff. -/
theorem energy_support_cutoff (N : ℕ) (i : EnergyIndex N) :
    (↑i.val.support : Set (Fin 3 ×ₗ ℕ)) ⊆ Set.range (cutoffMode N) := by
  intro q hq
  have hw : Finsupp.weight currentWeight i.val=N := by
    have h := currentEnergy_weight i.val
    rw [i.property] at h
    exact_mod_cast h
  have hp : (0 : ℕ) < (i.val q : ℕ) := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hb : i.val q * currentWeight q ≤ Finsupp.weight currentWeight i.val := by
    simpa only [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul] using
      (Finset.single_le_sum (fun j (_ : j∈i.val.support) => Nat.zero_le (i.val j * currentWeight j)) hq)
  have hq' : currentWeight q ≤ N := by
    rw [hw] at hb
    exact (Nat.le_mul_of_pos_left _ hp).trans hb
  refine ⟨((ofLex q).1,⟨(ofLex q).2,?_⟩),?_⟩
  · change (ofLex q).2+1≤N at hq'
    omega
  · exact toLex_ofLex q

/-- Literal finite-mode exponent vectors and actual PBW energy indices are equivalent. -/
def cutoffEnergyEquiv (N : ℕ) :
    {p : (Fin 3×Fin (N+1)) →₀ ℕ //
      Finsupp.weight (fun q : Fin 3×Fin (N+1) => q.2.val+1) p=N} ≃ EnergyIndex N where
  toFun p := ⟨Finsupp.mapDomain (cutoffMode N) p.val,by
    rw [← currentEnergy_weight,currentWeight_cutoff,p.property]⟩
  invFun i := ⟨Finsupp.comapDomain (cutoffMode N) i.val (cutoffMode_injective N).injOn,by
    rw [← currentWeight_cutoff,Finsupp.mapDomain_comapDomain _ (cutoffMode_injective N) _
      (energy_support_cutoff N i)]
    have h := currentEnergy_weight i.val
    rw [i.property] at h
    exact_mod_cast h⟩
  left_inv p := Subtype.ext (Finsupp.comapDomain_mapDomain _ (cutoffMode_injective N) p.val)
  right_inv i := Subtype.ext (Finsupp.mapDomain_comapDomain _ (cutoffMode_injective N) i.val
    (energy_support_cutoff N i))

/-- The actual universal conformal dimensions are the three-colour oscillator product coefficients. -/
theorem universal_grading_finrank_eq_reciprocalEuler_cube
    (k : ℂ) (hk : k+2≠0) (N : ℕ) :
    (Module.finrank ℂ ((universal k hk).grading N) : ℚ) =
      PowerSeries.coeff N ((reciprocalEuler : PowerSeries ℚ)^3) := by
  rw [universal_grading_finrank_eq_energy_count,← Nat.card_congr (cutoffEnergyEquiv N)]
  rw [← coeff_prod_weightedGeometric_eq_card _ (fun q : Fin 3×Fin (N+1) => by omega)]
  have hp : (∏ q : Fin 3×Fin (N+1),weightedGeometric (R := ℚ) (q.2.val+1)) =
      (reciprocalQFactorial (N+1) : PowerSeries ℚ)^3 := by
    rw [Fintype.prod_prod_type]
    simp only [prod_weightedGeometric_eq_reciprocalQFactorial,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
  rw [hp]
  have ht : TruncEq N (reciprocalEuler : PowerSeries ℚ) (reciprocalQFactorial (N+1)) := by
    intro j hj
    exact coeff_reciprocalEuler j (N+1) (by omega)
  have h := (ht.mul ht).mul ht
  simpa only [pow_succ,pow_zero,one_mul] using (h N le_rfl).symm

end
end VOA.AffineSl2GeneralRigidity
