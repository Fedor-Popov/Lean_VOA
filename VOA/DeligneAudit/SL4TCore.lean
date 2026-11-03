import VOA.DeligneAudit.SL4TPiTheorem
import VOA.DeligneAudit.SL4TCellCount
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# The two-alphabet pi-form core

Power sums are defined by the inverse Newton recursion on signed elementary
coefficients. The ascending coefficient polynomial is a unit, by the two
Grassmannian inverse-series identities. Its positive coefficients, and hence its
positive power sums, are nilpotent. Thus no ring hypothesis is left to the consumer.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial VOA.DeligneAudit.CVsl2
open scoped symmDiff

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Power sums of a degree `d` alphabet, from its signed elementary coefficients. -/
def powerSumOfCoeff (d : ℕ) (e : ℕ → R) : ℕ → R
  | 0 => d
  | n + 1 => -((n + 1 : ℕ) : ℂ) • e (n + 1) -
      ∑ i : Fin n, powerSumOfCoeff d e (n - i.val) * e (i.val + 1)
termination_by n => n
decreasing_by omega

theorem newtonCoeff_powerSumOfCoeff (d : ℕ) (e : ℕ → R) (h0 : e 0 = 1) :
    ∀ n, newtonCoeff (powerSumOfCoeff d e) n = e n := by
  apply newtonCoeff_unique _ e h0
  intro n
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_add_right, h0, mul_one]
  rw [powerSumOfCoeff]
  module

/-- The inverse Newton convention agrees with the usual power sums in positive degree. -/
theorem powerSumOfCoeff_newtonCoeff (d : ℕ) (p : ℕ → R) :
    ∀ n, 1 ≤ n → powerSumOfCoeff d (newtonCoeff p) n = p n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [powerSumOfCoeff, neg_smul, newtonCoeff_rec, neg_neg]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_add_right,
        show newtonCoeff p 0 = 1 by rw [newtonCoeff], mul_one]
      have he : (∑ i : Fin k, powerSumOfCoeff d (newtonCoeff p) (k - i.val) *
          newtonCoeff p (i.val + 1)) =
          ∑ i : Fin k, p (k - i.val) * newtonCoeff p (i.val + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih _ (by omega) (by have := i.isLt; omega)]
      rw [he]
      abel

theorem powerSumOfCoeff_psum_map (ι : Type*) [Fintype ι]
    (f : MvPolynomial ι ℂ →ₐ[ℂ] R) (d n : ℕ) (hn : 1 ≤ n) :
    powerSumOfCoeff d (fun j => (-1) ^ j * f (MvPolynomial.esymm ι ℂ j)) n =
      f (MvPolynomial.psum ι ℂ n) := by
  have h := powerSumOfCoeff_newtonCoeff d (fun s => f (MvPolynomial.psum ι ℂ s)) n hn
  rw [funext (newtonCoeff_psum_map ι f)] at h
  exact h

theorem powerSumOfCoeff_nilpotent (d : ℕ) (e : ℕ → R)
    (he : ∀ j, 1 ≤ j → IsNilpotent (e j)) (n : ℕ) (hn : 1 ≤ n) :
    IsNilpotent (powerSumOfCoeff d e n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [powerSumOfCoeff]
  apply (Commute.all _ _).isNilpotent_sub
  · exact (he (k + 1) (by omega)).smul (-((k + 1 : ℕ) : ℂ))
  · apply isNilpotent_sum
    intro i _
    simpa only [smul_eq_mul] using
      (he (i.val + 1) (by omega)).smul (powerSumOfCoeff d e (k - i.val))

def grassSeries (d T : ℕ) : (GrassRing d T)[X] :=
  coefficientPoly (fun i => (-1) ^ i * eClass d T i) d

theorem grassSeries_unit (d T : ℕ) : IsUnit (grassSeries d T) :=
  isUnit_iff_exists_inv.mpr ⟨coefficientPoly (hClass d T) T, grass_coefficient_product d T⟩

theorem grassSeries_zero (d T : ℕ) : (grassSeries d T).coeff 0 = 1 := by
  simp [grassSeries, coefficientPoly_coeff, eClass]

def S_series (M a b : ℕ) : (S M a b)[X] :=
  (grassSeries a (M - a)).map (biLeft a (M - a) b (M - b)).toRingHom *
    (grassSeries b (M - b)).map (biRight a (M - a) b (M - b)).toRingHom

theorem S_series_zero (M a b : ℕ) : (S_series M a b).coeff 0 = 1 := by
  simp only [S_series, mul_coeff_zero, coeff_map, grassSeries_zero, map_one, one_mul]

theorem S_series_degree (M a b : ℕ) : (S_series M a b).natDegree ≤ a + b := by
  apply natDegree_mul_le.trans
  apply Nat.add_le_add
  · exact natDegree_map_le.trans (coefficientPoly_degree _ _)
  · exact natDegree_map_le.trans (coefficientPoly_degree _ _)

theorem S_series_unit (M a b : ℕ) : IsUnit (S_series M a b) := by
  apply IsUnit.mul
  · exact (grassSeries_unit a (M - a)).map (Polynomial.mapRingHom _)
  · exact (grassSeries_unit b (M - b)).map (Polynomial.mapRingHom _)

def S_powerSum (M a b : ℕ) : ℕ → S M a b :=
  powerSumOfCoeff (a + b) (S_series M a b).coeff

theorem S_newtonCoeff (M a b n : ℕ) :
    newtonCoeff (S_powerSum M a b) n = (S_series M a b).coeff n :=
  newtonCoeff_powerSumOfCoeff (a + b) _ (S_series_zero M a b) n

theorem S_newtonCoeff_tail (M a b j : ℕ) (hj : a + b < j) :
    newtonCoeff (S_powerSum M a b) j = 0 := by
  rw [S_newtonCoeff]
  exact coeff_eq_zero_of_natDegree_lt ((S_series_degree M a b).trans_lt hj)

theorem S_powerSum_nilpotent (M a b s : ℕ) (hs : 1 ≤ s) :
    IsNilpotent (S_powerSum M a b s) := by
  apply powerSumOfCoeff_nilpotent _ _ _ s hs
  intro j hj
  exact (isUnit_iff_coeff_isUnit_isNilpotent.mp (S_series_unit M a b)).2 j (by omega)

theorem coefficientPoly_coeffs (P : R[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    coefficientPoly P.coeff d = P := by
  ext j
  apply coefficientPoly_coeff_of_tail
  intro k hk
  exact coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk)

theorem S_descending_newton (M a b : ℕ) :
    descendingPoly (newtonCoeff (S_powerSum M a b)) (a + b) =
      leftP M a b * rightP M a b := by
  simp only [funext (S_newtonCoeff M a b), descendingPoly]
  rw [coefficientPoly_coeffs _ _ (S_series_degree M a b)]
  unfold S_series grassSeries
  rw [reflect_mul _ _ (natDegree_map_le.trans (coefficientPoly_degree _ a))
    (natDegree_map_le.trans (coefficientPoly_degree _ b)), reflect_map, reflect_map]
  rfl

theorem bal_sum_cells (M a b : ℕ) :
    (∑ i ∈ Finset.range (cellLevels M a b).length,
      ((bal (a + b) ((cellLevels M a b).getD i 0)).map (· + 1)).prod) = u M a b := by
  rw [list_sum_getD (cellLevels M a b) (fun n => ((bal (a + b) n).map (· + 1)).prod),
    ← cellCatalog_levels, List.map_map, u, ← cellCatalog_toFinset,
    List.sum_toFinset _ (cellCatalog_nodup M a b)]
  congr 1
  apply List.map_congr_left
  intro c hc
  have hv := cellCatalog_valid M a b c hc
  have hb := cellCutoff_bounds hv
  by_cases hz : cellCutoff c = 0
  · have hr : a + b = 0 := by omega
    rw [cellWeight_closed hv]
    simp [hz, hr, bal]
  · rw [cellWeight_closed hv]
    exact bal_prod_two (by omega) hb.1 hb.2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- The all-parameter sl4-T core, with the two-alphabet ring hypotheses discharged. -/
theorem S_pi_bound (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) (hS : SL2 E H F)
    (π : S M a b →ₗ[ℂ] V)
    (hE : ∀ s φ, E s (π φ) = 0)
    (hH0 : ∀ φ, H 0 (π φ) = ((a + b : ℕ) : ℂ) • π φ)
    (hH : ∀ s, 1 ≤ s → ∀ φ, H s (π φ) = π (S_powerSum M a b s * φ))
    (hF0 : ∀ φ, (F 0 ^ (a + b + 1)) (π φ) = 0)
    (hM : ∀ s, M ≤ s → ∀ φ, F s (π φ) = 0) :
    FiniteDimensional ℂ (currentSpan E H F (Set.range π)) ∧
      Module.finrank ℂ (currentSpan E H F (Set.range π)) ≤
        ∑ c ∈ cellSet M a b, 3 ^ (c.1 ∩ c.2).card * 2 ^ (c.1 ∆ c.2).card := by
  have hP := piCharacteristic_of_highest hS π (S_powerSum M a b) hE hH
    (a + b) hF0 (S_newtonCoeff_tail M a b)
  rw [S_descending_newton] at hP
  obtain ⟨fd, hd⟩ := SpanningChain.pi_bound_of_characteristic hS π (S_powerSum M a b)
    (leftP M a b * rightP M a b) (a + b) M (k1_recursive M a b ha hb)
    (S_powerSum_nilpotent M a b) hE hH0 hH hF0 hM hP
  exact ⟨fd, hd.trans_eq (bal_sum_cells M a b)⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_powerSumOfCoeff
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_psum_map
#print axioms VOA.DeligneAudit.SL4T.powerSumOfCoeff_nilpotent
#print axioms VOA.DeligneAudit.SL4T.grassSeries_unit
#print axioms VOA.DeligneAudit.SL4T.grassSeries_zero
#print axioms VOA.DeligneAudit.SL4T.S_series_zero
#print axioms VOA.DeligneAudit.SL4T.S_series_degree
#print axioms VOA.DeligneAudit.SL4T.S_series_unit
#print axioms VOA.DeligneAudit.SL4T.S_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.S_newtonCoeff_tail
#print axioms VOA.DeligneAudit.SL4T.S_powerSum_nilpotent
#print axioms VOA.DeligneAudit.SL4T.coefficientPoly_coeffs
#print axioms VOA.DeligneAudit.SL4T.S_descending_newton
#print axioms VOA.DeligneAudit.SL4T.bal_sum_cells
#print axioms VOA.DeligneAudit.SL4T.S_pi_bound
