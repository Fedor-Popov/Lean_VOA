/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesSocleCountWords
import VOA.Examples.TwoSeriesInvariantsSocle

/-!
# The socle-word count is the Andrews–Gordon count

* `socleWordCount_eq` — `socleWordCount n N r = gordonCoeff n N r` for all `n, N, r`:
  the socle-word count (words in `0, …, n-1` weighted by inversions and tails, times
  bounded-part partitions) equals the number of partitions of `N` into `r` parts `≥ 2` with
  `f_m + f_{m+1} ≤ n`.  Proof: `gapTwoCoefficient` is a coefficient of `1/(q)_{N₁}`
  (`gap_eq`), the word sum is the content sum by MacMahon (`sum_words_eq`), the content sum is
  the peeled multisum `F_{n,1}` (`coeff_F_one_eq`), and `F_{n,1}` is the Gordon series by
  Andrews' recursion (`coeff_F_one`).
* `socleWordGordon` — **`SocleWordGordon n` is proved for every `n`.**
* `VOA.TwoSeries.twoSeries_gradedUnitary_of_socleInput` — Affine GU ⇒ GU of
  `M(2, 2n+3)`, conditional only on `hA` and the affine socle input `TwoSeriesSocleInput n`.
-/

namespace VOA.SocleCount

open PowerSeries VOA.TwoSeriesCharacter VOA.TwoSeriesCharacter.AG VOA.SocleEval
open scoped BigOperators

noncomputable section

theorem inversions_eq_invs {n N : ℕ} (x : Fin N → Fin n) : inversions x = invs x := by
  unfold inversions invs
  rw [Finset.card_filter, Fintype.sum_prod_type]

theorem clusterAtLeast_eq {n N : ℕ} (x : Fin N → Fin n) (t : ℕ) :
    clusterAtLeast x t = Cge (ctt x) t := by
  unfold clusterAtLeast Cge ctt
  rw [Finset.card_filter]
  have h1 : ∀ b : Fin n, (if t ≤ (b : ℕ) then ∑ j, (if x j = b then 1 else 0) else 0) =
      ∑ j, (if x j = b then (if t ≤ (b : ℕ) then 1 else 0) else 0) := by
    intro b
    split_ifs with hb
    · rfl
    · simp
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem Cge_zero {n N : ℕ} (x : Fin N → Fin n) : Cge (ctt x) 0 = N := by
  unfold Cge
  simp only [Nat.zero_le, if_true]
  exact sum_ctt x

/-- The total weight `N₁² + deg x = Qf(content x) + inv x`. -/
theorem wt_eq {n N₁ : ℕ} (x : Fin N₁ → Fin n) :
    N₁ * N₁ + socleDegree x = Qf (ctt x) + invs x := by
  unfold socleDegree Qf
  rw [inversions_eq_invs]
  rcases n with _ | k
  · have hN : N₁ = 0 := by
      rcases Nat.eq_zero_or_pos N₁ with h | h
      · exact h
      · exact (x ⟨0, h⟩).elim0
    subst hN
    simp
  · rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range, Cge_zero,
      show k + 1 - 1 = k by omega]
    simp only [clusterAtLeast_eq, add_comm 1]
    ring

/-- `gapTwoCoefficient` as a coefficient of `q^{s² + d}/(q)_s`. -/
theorem gap_eq (N d s : ℕ) :
    ((VOA.LeeYangTransferAssembly.gapTwoCoefficient ((N : ℤ) - (d : ℤ) + (s : ℤ)) s : ℕ) : ℚ) =
      coeff N (qq ^ (s * s + d) * ipoch s) := by
  rw [qq, coeff_X_pow_mul']
  split_ifs with h
  · have hd : d ≤ N := le_trans (Nat.le_add_left d (s * s)) h
    have e1 : (N : ℤ) - (d : ℤ) + (s : ℤ) = ((N - d + s : ℕ) : ℤ) := by push_cast [hd]; ring
    rw [e1, coeff_ipoch, ← Int.cast_natCast, VOA.RRLower.gapTwoCoefficient_eq_pc]
    congr 2
    push_cast [hd, h]
    ring
  · rw [Nat.cast_eq_zero]
    have h' : (N : ℤ) < (s : ℤ) * s + d := by exact_mod_cast (not_le.mp h)
    rcases lt_or_ge ((N : ℤ) - (d : ℤ) + (s : ℤ)) 0 with hneg | hpos
    · exact VOA.LeeYangCharacter.gapTwoCoefficient_neg hneg s
    · obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = (N : ℤ) - (d : ℤ) + (s : ℤ) :=
        ⟨_, Int.toNat_of_nonneg hpos⟩
      rw [← hM]
      have := VOA.RRLower.gapTwoCoefficient_eq_pc M s
      rw [VOA.RRLower.pc_of_neg _ (by rw [hM]; nlinarith)] at this
      exact_mod_cast this

/-- **The socle-word count is the Andrews–Gordon count.** -/
theorem socleWordCount_eq (n N r : ℕ) :
    socleWordCount n (N : ℤ) r = gordonCoeff n (N : ℤ) r := by
  apply (Nat.cast_injective (R := ℚ))
  rw [← coeff_F_one, coeff_F_one_eq, socleWordCount, Nat.cast_sum, Fintype.sum_sigma]
  simp only [gap_eq]
  trans coeff N (∑ N₁ : Fin (r + 1), ∑ w : SocleWord n r N₁,
    qq ^ ((N₁ : ℕ) * (N₁ : ℕ) + socleDegree w.1) * ipoch N₁)
  · simp only [map_sum]
  congr 1
  have hw : ∀ N₁ : ℕ, (∑ w : SocleWord n r N₁, qq ^ (N₁ * N₁ + socleDegree w.1) * ipoch N₁) =
      ∑ w : Fin N₁ → Fin n, (if ∑ j, ((w j : ℕ) + 1) = r then
        qq ^ (Qf (ctt w) + invs w) * ipoch N₁ else 0) := by
    intro N₁
    rw [← Finset.sum_filter]
    simp only [← wt_eq]
    exact (Finset.sum_subtype (p := fun x : Fin N₁ → Fin n => ∑ j, ((x j : ℕ) + 1) = r)
      (Finset.univ.filter fun x : Fin N₁ → Fin n => ∑ j, ((x j : ℕ) + 1) = r)
      (fun x => by simp) (fun x => qq ^ (N₁ * N₁ + socleDegree x) * ipoch N₁)).symm
  rw [Fin.sum_univ_eq_sum_range (fun N₁ => ∑ w : SocleWord n r N₁,
    qq ^ (N₁ * N₁ + socleDegree w.1) * ipoch N₁) (r + 1)]
  simp only [hw, sum_words_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_ite_eq, if_pos]
  rw [Finset.mem_range]
  have : ∑ b, m b ≤ wsize m := Finset.sum_le_sum fun b _ =>
    Nat.le_mul_of_pos_left _ (by omega)
  have := mem_Mset.mp hm
  omega

/-- **`SocleWordGordon n` holds for every `n`.** -/
theorem socleWordGordon (n : ℕ) : SocleWordGordon n := by
  intro N r
  rcases lt_or_ge N 0 with hN | hN
  · have : socleWordCount n N r = 0 := by
      refine Finset.sum_eq_zero fun i _ => VOA.LeeYangCharacter.gapTwoCoefficient_neg ?_ _
      have : ((i.1 : ℕ) : ℤ) ≤ (socleDegree i.2.1 : ℤ) := by
        exact_mod_cast (show (i.1 : ℕ) ≤ socleDegree i.2.1 by unfold socleDegree; omega)
      omega
    rw [this]; exact Nat.zero_le _
  · obtain ⟨N', rfl⟩ := Int.eq_ofNat_of_zero_le hN
    exact (socleWordCount_eq n N' r).le

end

end VOA.SocleCount

namespace VOA.TwoSeries

open VOA.SocleEval VOA.CyclicEval VOA.InvariantSymbol MvPolynomial Module
open VOA.ConcreteHodge VOA.SymbolModel VOA.GradedUnitaryCohomology VirGradedUnitarity
open Sl2CosetConcrete

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`, with the combinatorial input discharged.**
`#print axioms`-clean, conditional only on `hA` and the affine socle input `S`. -/
theorem twoSeries_gradedUnitary_of_socleInput (n : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (S : TwoSeriesSocleInput n) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_socle n hA S (VOA.SocleCount.socleWordGordon n)

end VOA.TwoSeries
