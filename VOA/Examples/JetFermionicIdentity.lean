/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetFermionicWZ
import VOA.Examples.JetFermionicMoment
import VOA.Examples.JetProductEndpoint

/-!
# The fermionic jet identity

  `Σ_{r ≥ 0} q^r (Σ_{k=0}^{2r} [2r, k]_q) / (q)_r = ((q³;q³)_∞ / (q;q)_∞)³`

(the `k = 1`, `t = q`, `z = 1` case of Chern–Tran–Wakhare, Theorem 1.2), proved outright by
an elementary route that avoids Bailey pairs:

1. `Σ_k [2r, k] = (q)_{2r} Σ_{a+b=2r} 1/((q)_a (q)_b)`;
2. the moment identity `euler_cube_mul_pairSum` turns `(q)_∞³ · q^r Σ_k [2r,k] / (q)_r` into
   `Σ_t (-1)^t (2r+2t+1) q^{r + C(t+1,2)} (q)_{2r+t} / ((q)_t (q)_r)`;
3. regrouping by `j = r + t`, the terminating WZ identity `wzSum_eq` collapses the inner sum to
   `(-1)^j (2j+1) q^{3 C(j+1,2)}`;
4. Jacobi's cube identity (`jacobi_cube`) dilated by `q ↦ q³` gives `(q³;q³)_∞³`.

* `euler_cube_mul_jetSeries` — `(q;q)_∞³ · jetSeries = (q³;q³)_∞³`;
* `jetFermionicIdentity` — `JetFermionicIdentity`, proved outright;
* `jetFermionicLower` — `JetFermionicLower`, proved outright;
* `leeYang_gradedUnitary_of_affine_wordSymbols_jet` — **Affine GU ⇒ Lee–Yang GU**,
  conditional only on `hA` and the word-symbol descent `desc`.
-/

namespace VOA.JetFermionic

open VOA.QSeries VOA.LocallyFinitePowerSeriesSum VOA.JetProduct
open scoped BigOperators

noncomputable section

/-- The double-sum summand `(-1)^t (2r+2t+1) q^{r + C(t+1,2)} (q)_{2r+t} / ((q)_t (q)_r)`. -/
def jetDouble (r t : ℕ) : PowerSeries ℚ :=
  (-1 : PowerSeries ℚ) ^ t * ((2 * r + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
    PowerSeries.X ^ (r + (t + 1).choose 2) * qFactorial PowerSeries.X (2 * r + t) *
      reciprocalQFactorial t * reciprocalQFactorial r

theorem coeff_jetDouble_eq_zero (r t d : ℕ) (h : d < r + t) :
    PowerSeries.coeff d (jetDouble r t) = 0 := by
  have heq : jetDouble r t = PowerSeries.X ^ (r + (t + 1).choose 2) *
      ((-1 : PowerSeries ℚ) ^ t * ((2 * r + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
        qFactorial PowerSeries.X (2 * r + t) * reciprocalQFactorial t *
          reciprocalQFactorial r) := by
    unfold jetDouble
    ring
  rw [heq]
  exact coeff_X_pow_mul_eq_zero _ _ (by have := le_triangular t; omega) _

/-- `Σ_k [2r, k] = (q)_{2r} Σ_{a+b=2r} 1/((q)_a (q)_b)`. -/
theorem sum_gaussian_eq_pairSum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), gaussian (PowerSeries.X : PowerSeries ℚ) n k =
      qFactorial PowerSeries.X n * pairSum n := by
  rw [pairSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [gaussian_eq_qFactorial_ratio n k hkn]
  dsimp only
  ring

/-- Step 2: the Euler cube times one jet term is a locally finite alternating sum. -/
theorem euler_cube_mul_jetTerm (r : ℕ) :
    (euler : PowerSeries ℚ) ^ 3 * jetTerm r =
      VOA.LocallyFinitePowerSeriesSum.sum (jetDouble r) := by
  have hm := euler_cube_mul_pairSum (K := ℚ) (2 * r)
  calc
    _ = ((euler : PowerSeries ℚ) ^ 3 * pairSum (2 * r)) *
        (PowerSeries.X ^ r * qFactorial PowerSeries.X (2 * r) * reciprocalQFactorial r) := by
      rw [jetTerm, sum_gaussian_eq_pairSum]
      ring
    _ = momentSeries (2 * r) *
        (PowerSeries.X ^ r * qFactorial PowerSeries.X (2 * r) * reciprocalQFactorial r) := by
      rw [hm]
    _ = VOA.LocallyFinitePowerSeriesSum.sum (fun t => momentTerm (2 * r) t *
        (PowerSeries.X ^ r * qFactorial PowerSeries.X (2 * r) * reciprocalQFactorial r)) :=
      (indexBounded_sum_mul _ (coeff_momentTerm_eq_zero (2 * r)) _).symm
    _ = _ := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro t
      rw [momentTerm, jetDouble, gaussian_eq_qFactorial_ratio (2 * r + t) t (by omega),
        show 2 * r + t - t = 2 * r by omega, pow_add]
      have h1 : qFactorial (PowerSeries.X : PowerSeries ℚ) (2 * r) *
          reciprocalQFactorial (2 * r) = 1 := qFactorial_mul_reciprocal _
      rw [show 2 * r + 2 * t + 1 = 2 * r + 2 * t + 1 by rfl]
      linear_combination
        ((-1 : PowerSeries ℚ) ^ t * ((2 * r + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
          PowerSeries.X ^ ((t + 1).choose 2) * qFactorial PowerSeries.X (2 * r + t) *
            reciprocalQFactorial t * PowerSeries.X ^ r * reciprocalQFactorial r) * h1

/-- Step 3: the WZ collapse of each antidiagonal. -/
theorem jetDouble_antidiagonal (j : ℕ) :
    ∑ r ∈ Finset.range (j + 1), jetDouble r (j - r) =
      alternatingTerm j * PowerSeries.X ^ (1 * (j * (j + 1))) := by
  have hw := wzSum_eq (R := ℚ) j
  have hexp : 1 * (j * (j + 1)) + (j + 1).choose 2 = 3 * (j + 1).choose 2 := by
    have h := two_mul_choose_two_add (j + 1)
    nlinarith
  have hA : alternatingTerm j * PowerSeries.X ^ (1 * (j * (j + 1))) =
      (-1 : PowerSeries ℚ) ^ j * ((2 * j + 1 : ℕ) : PowerSeries ℚ) *
        PowerSeries.X ^ (3 * (j + 1).choose 2) := by
    unfold alternatingTerm
    rw [← hexp, pow_add]
    ring
  rw [hA, ← hw, wzSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r ≤ j := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hr
  obtain ⟨t, rfl⟩ : ∃ t, j = r + t := ⟨j - r, by omega⟩
  rw [jetDouble, wzTerm, show r + t - r = t by omega, show 2 * r + t = r + t + r by omega,
    show 2 * r + 2 * t + 1 = 2 * (r + t) + 1 by omega]
  have hsign : (-1 : PowerSeries ℚ) ^ t = (-1) ^ (r + t) * (-1) ^ r := by
    rw [← pow_add, show r + t + r = t + 2 * r by omega, pow_add, pow_mul]
    simp
  rw [hsign]
  ring

/-- `(q;q)_∞³ · jetSeries = (q³;q³)_∞³`, proved outright. -/
theorem euler_cube_mul_jetSeries :
    (euler : PowerSeries ℚ) ^ 3 * jetSeries =
      (PowerSeries.expand (2 * 1 + 1) (by omega) (euler : PowerSeries ℚ)) ^ 3 := by
  have hR : (PowerSeries.expand (2 * 1 + 1) (by omega) (euler : PowerSeries ℚ)) ^ 3 =
      VOA.LocallyFinitePowerSeriesSum.sum
        (fun r => (alternatingTerm r : PowerSeries ℚ) * PowerSeries.X ^ (1 * (r * (r + 1)))) := by
    rw [← map_pow, ← jacobi_cube, sum_alternatingTerm_chain_power 1]
  rw [hR, jetSeries, mul_comm, ← indexBounded_sum_mul _ coeff_jetTerm_eq_zero]
  apply PowerSeries.ext
  intro d
  have hE : ∀ d r, d < r →
      PowerSeries.coeff d (jetTerm r * (euler : PowerSeries ℚ) ^ 3) = 0 := by
    intro d r h
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [coeff_jetTerm_eq_zero ij.1 r (by have := Finset.mem_antidiagonal.mp hij; omega),
      zero_mul]
  rw [coeff_indexBounded_sum _ hE d d le_rfl,
    coeff_indexBounded_sum _ (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _) d d le_rfl,
    map_sum, map_sum]
  simp only [← jetDouble_antidiagonal, map_sum]
  rw [sum_triangle_shift (fun r j => PowerSeries.coeff d (jetDouble r (j - r))) d]
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hr
  rw [mul_comm, euler_cube_mul_jetTerm,
    coeff_indexBounded_sum _ (fun d t h => coeff_jetDouble_eq_zero r t d (by omega)) d d le_rfl,
    map_sum]
  simp only [Nat.add_sub_cancel_left]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro t _ ht
  exact coeff_jetDouble_eq_zero r t d (by simp at ht; omega)

/-- **The fermionic jet identity** `jetSeries = ((q³;q³)_∞/(q;q)_∞)³`, proved outright. -/
theorem jetFermionicIdentity : JetFermionicIdentity := by
  unfold JetFermionicIdentity AffineSl2BoundaryCharacter.product
  have h := congrArg (fun f => f * (reciprocalEuler : PowerSeries ℚ) ^ 3)
    euler_cube_mul_jetSeries
  simp only at h
  have hinv : (euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3 = 1 := by
    rw [← mul_pow, euler_mul_reciprocal, one_pow]
  calc
    jetSeries = ((euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3) * jetSeries := by
      rw [hinv, one_mul]
    _ = _ := by
      rw [show ((euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3) * jetSeries =
        (euler ^ 3 * jetSeries) * reciprocalEuler ^ 3 by ring, h]
      rfl

/-- The coefficientwise inequality used by the endpoint, proved outright. -/
theorem jetFermionicLower : JetFermionicLower :=
  jetFermionicLower_of_identity jetFermionicIdentity

end

end VOA.JetFermionic

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.LeeYangTransferAssembly Sl2CosetConcrete

/-- **Affine GU ⇒ Lee–Yang GU**, with the jet-ring character bound discharged:
conditional only on `hA` and the word-symbol descent `desc`. -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols_jet
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_jetFermionic hA desc VOA.JetFermionic.jetFermionicLower

end VOA.AdamovicSymbol
