/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionF
import VOA.DeligneAudit.DeligneFusionSqueeze

/-!
# The squeeze for any type, and its `D₄` instance

Generic versions of `DeligneFusionCount` (F3) and `DeligneFusionSqueeze` (F6) for
`fusionOf Dem` (`D4FusionF.lean`), the unique solution of the mixed recursion for a Demazure series
`Dem`:

* **Count** (`fusionOf_count`): if every `Dem n` is a polynomial with `Dem n (1) = (d+1)ⁿ`, then
  every `fusionOf Dem m` is a polynomial with value `d^m` at `q = 1` (binomial inversion).
* **Squeeze** (`squeezeG`): from the named inputs `FusionSqueezeInputsG Dem d M` (nonnegativity, the
  spanning recursion, `Dem ≤ ch M_{n,0}`, `dim M_{0,m} ≤ d^m`) and the count,
  `ch M_{0,m} = fusionOf Dem m`;
  hence `fusionOf Dem` has nonnegative coefficients (`fusionOf_coeff_nonneg`) and U5 holds in the
  type-generic form (`fusionModuleBoundG_of_squeeze`).
* **`D₄`**: with the named count `D4DemazureCount` (`∑_N d4DemazureHilb n N = 29ⁿ`, checked
  numerically for `n ≤ 7`), `d4_fusionModuleBound_of_squeeze` gives `FusionModuleBoundG D4sector d4FusionF`.
-/

namespace VOA.DeligneAudit.DeligneCarrier

open PowerSeries VOA.DeligneGaussian VOA.DeligneAudit.A2

open scoped BigOperators

noncomputable section

/-! ## The count, generically -/

/-- `fusionOf` on polynomials (same recursion). -/
def fusionPolyOf (P : ℕ → Polynomial ℚ) : ℕ → Polynomial ℚ
  | n => P n -
      ∑ d : Fin n, Polynomial.X ^ ((d.1 + 1) * n) *
        qbinom (Polynomial.X : Polynomial ℚ) n (d.1 + 1) *
        fusionPolyOf P (n - (d.1 + 1))
decreasing_by omega

theorem fusionPolyOf_eq (P : ℕ → Polynomial ℚ) (n : ℕ) : fusionPolyOf P n = P n -
    ∑ d ∈ Finset.range n, Polynomial.X ^ ((d + 1) * n) *
      qbinom (Polynomial.X : Polynomial ℚ) n (d + 1) * fusionPolyOf P (n - (d + 1)) := by
  rw [fusionPolyOf, Fin.sum_univ_eq_sum_range (fun d => Polynomial.X ^ ((d + 1) * n) *
    qbinom (Polynomial.X : Polynomial ℚ) n (d + 1) * fusionPolyOf P (n - (d + 1))) n]

theorem fusionPolyOf_coe (P : ℕ → Polynomial ℚ) (n : ℕ) :
    (fusionPolyOf P n : PowerSeries ℚ) = fusionOf (fun k => (P k : PowerSeries ℚ)) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fusionPolyOf_eq, fusionOf_eq, Polynomial.coe_sub]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_range] at hd
    rw [map_mul, map_mul, map_pow, map_qbinom, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, ih _ (by omega)]

theorem fusionPolyOf_eval_one (P : ℕ → Polynomial ℚ) (d : ℕ)
    (hP : ∀ n, (P n).eval 1 = ((d : ℚ) + 1) ^ n) (n : ℕ) :
    (fusionPolyOf P n).eval 1 = (d : ℚ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fusionPolyOf_eq, Polynomial.eval_sub, hP, Polynomial.eval_finsetSum]
    have h : ∀ k ∈ Finset.range n, (Polynomial.X ^ ((k + 1) * n) *
        qbinom (Polynomial.X : Polynomial ℚ) n (k + 1) * fusionPolyOf P (n - (k + 1))).eval 1 =
          (n.choose (k + 1) : ℚ) * (d : ℚ) ^ (n - (k + 1)) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
        one_mul, eval_one_qbinom, ih _ (by omega)]
    rw [Finset.sum_congr rfl h]
    have hb : ((d : ℚ) + 1) ^ n =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (d : ℚ) ^ (n - k) := by
      rw [add_comm, add_pow]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hb, Finset.sum_range_succ']
    simp

/-- A series supported below `B` is the power series of its truncation. -/
theorem coe_trunc_of_support {f : PowerSeries ℚ} {B : ℕ} (hf : ∀ N, B ≤ N → coeff N f = 0) :
    ((trunc B f : Polynomial ℚ) : PowerSeries ℚ) = f := by
  ext N
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · rfl
  · exact (hf N (by omega)).symm

/-- **The generic count**: polynomial Demazure series with `Dem n (1) = (d+1)ⁿ` give
`fusionOf Dem m (1) = d^m`. -/
theorem fusionOf_count (Dem : ℕ → PowerSeries ℚ) (d : ℕ)
    (hcount : ∀ n, ∃ B, (∀ N, B ≤ N → coeff N (Dem n) = 0) ∧
      ∑ N ∈ Finset.range B, coeff N (Dem n) = ((d : ℚ) + 1) ^ n) (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (fusionOf Dem m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) = (d : ℚ) ^ m := by
  choose B hB hsum using hcount
  set P : ℕ → Polynomial ℚ := fun n => trunc (B n + 1) (Dem n)
  have hDem : (fun k => (P k : PowerSeries ℚ)) = Dem :=
    funext fun k => coe_trunc_of_support (fun N hN => hB k N (by omega))
  have hP : ∀ n, (P n).eval 1 = ((d : ℚ) + 1) ^ n := by
    intro n
    rw [Polynomial.eval_eq_sum_range' (natDegree_trunc_lt (Dem n) (B n))]
    simp only [one_pow, mul_one, coeff_trunc]
    rw [← hsum n, Finset.sum_range_succ, if_pos (by omega), hB n (B n) le_rfl, add_zero]
    exact Finset.sum_congr rfl fun N hN => by
      rw [if_pos (by have := Finset.mem_range.mp hN; omega)]
  refine ⟨(fusionPolyOf P m).natDegree + 1, fun b hb => ?_, ?_⟩
  · rw [← hDem, ← fusionPolyOf_coe, Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · have h := fusionPolyOf_eval_one P d hP m
    rw [Polynomial.eval_eq_sum_range' (by omega : (fusionPolyOf P m).natDegree <
      (fusionPolyOf P m).natDegree + 1)] at h
    simp only [one_pow, mul_one] at h
    rw [← h, ← hDem, ← fusionPolyOf_coe]
    exact Finset.sum_congr rfl fun N _ => Polynomial.coeff_coe _ _

/-! ## The squeeze, generically -/

/-- **Named inputs of the squeeze** for a Demazure series `Dem` and `d = dim 𝔤`. -/
structure FusionSqueezeInputsG (Dem : ℕ → PowerSeries ℚ) (d : ℕ) (M : ℕ → ℕ → PowerSeries ℚ) :
    Prop where
  nonneg : ∀ a b N, 0 ≤ coeff N (M a b)
  rec_le : ∀ a b, CoeffLe (M (a + 1) b) (M a (b + 1) + X ^ (2 * a + b + 1) * M a b)
  dem_le : ∀ n, CoeffLe (Dem n) (M n 0)
  total_le : ∀ m B, ∑ N ∈ Finset.range B, coeff N (M 0 m) ≤ (d : ℚ) ^ m

variable {Dem : ℕ → PowerSeries ℚ} {d : ℕ} {M : ℕ → ℕ → PowerSeries ℚ}

theorem le_mixedG (h : FusionSqueezeInputsG Dem d M) :
    ∀ a b, CoeffLe (M a b) (mixed (X : PowerSeries ℚ) (fun k => M 0 k) a b)
  | 0, b => CoeffLe.refl _
  | a + 1, b => by
      refine (h.rec_le a b).trans ?_
      rw [mixed]
      exact (le_mixedG h a (b + 1)).add ((le_mixedG h a b).X_pow_mul _)

/-- **The generic squeeze**: `ch M_{0,m} = fusionOf Dem m`. -/
theorem squeezeG (h : FusionSqueezeInputsG Dem d M)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (fusionOf Dem m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) = (d : ℚ) ^ m) (m : ℕ) :
    M 0 m = fusionOf Dem m := by
  induction m using Nat.strong_induction_on with
  | _ n ih =>
    have hle : CoeffLe (fusionOf Dem n) (M 0 n) := by
      have h1 := (h.dem_le n).trans (le_mixedG h n 0)
      rw [(mixedFusionRecursion_fusionOf Dem).eq n, mixed_zero_split, mixed_zero_split] at h1
      have hS : ∑ k ∈ Finset.range n, X ^ ((k + 1) * n) * qbinom (X : PowerSeries ℚ) n (k + 1) *
          M 0 (n - (k + 1)) = ∑ k ∈ Finset.range n, X ^ ((k + 1) * n) *
            qbinom (X : PowerSeries ℚ) n (k + 1) * fusionOf Dem (n - (k + 1)) :=
        Finset.sum_congr rfl fun k hk => by
          simp only [Finset.mem_range] at hk
          rw [ih _ (by omega)]
      rw [hS] at h1
      exact h1.add_left_cancel
    obtain ⟨B0, hB0, hsum⟩ := hcount n
    ext N
    set B := max B0 (N + 1)
    have hfB : ∑ k ∈ Finset.range B, coeff k (fusionOf Dem n) = (d : ℚ) ^ n := by
      rw [← hsum]
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _))
      intro k hk hk'
      simp only [Finset.mem_range, not_lt] at hk hk'
      exact hB0 k hk'
    have heq := (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).mp
      (le_antisymm (Finset.sum_le_sum fun k _ => hle k) (by rw [hfB]; exact h.total_le n B))
    exact (heq N (Finset.mem_range.mpr (by omega))).symm

theorem fusionOf_coeff_nonneg (h : FusionSqueezeInputsG Dem d M)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (fusionOf Dem m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) = (d : ℚ) ^ m) (m N : ℕ) :
    0 ≤ coeff N (fusionOf Dem m) := by
  rw [← squeezeG h hcount m]; exact h.nonneg 0 m N

open VOA.DeligneAudit.DeligneSector SectorWeyl in
/-- **Type-generic U5** from the squeeze inputs, the count, and the universal bound at
`a = 0`. -/
theorem fusionModuleBoundG_of_squeeze (S : DeligneSectorData) (hd : S.n = d)
    (h : FusionSqueezeInputsG Dem d M)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → coeff b (fusionOf Dem m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) = (d : ℚ) ^ m)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
      LocalWeylRelG S ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG S (fusionOf Dem) := by
  subst hd
  refine ⟨fun m V _ _ ρ w hw b => ?_, fun m V _ _ ρ w hw B => ?_⟩
  · rw [← squeezeG h hcount m]; exact huniv m V ρ w hw b
  · obtain ⟨B0, hB0, hsum⟩ := hcount m
    have key : (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg ρ w b) : ℚ)) ≤
        (S.n : ℚ) ^ m := by
      calc (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg ρ w b) : ℚ))
          ≤ ∑ b ∈ Finset.range B, coeff b (fusionOf Dem m) := Finset.sum_le_sum fun b _ => by
            rw [← squeezeG h hcount m]; exact huniv m V ρ w hw b
        _ ≤ ∑ b ∈ Finset.range (max B B0), coeff b (fusionOf Dem m) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (le_max_left _ _))
              fun b _ _ => fusionOf_coeff_nonneg h hcount m b
        _ = (S.n : ℚ) ^ m := by
            rw [← hsum]
            symm
            apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _))
            intro k hk hk'
            simp only [Finset.mem_range, not_lt] at hk hk'
            exact hB0 k hk'
    exact_mod_cast key

/-! ## `D₄` -/

/-- **Named input**: `∑_N d4DemazureHilb n N = 29ⁿ` (`dim D(1,nθ) = dim W_loc(nθ) = 29ⁿ`, the
Fourier–Littelmann tensor-product structure of level-one Demazure modules; checked numerically for
`n ≤ 7` outside Lean). -/
def D4DemazureCount : Prop :=
  ∀ n, ∃ B, (∀ N, B ≤ N → VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb n N = 0) ∧
    ∑ N ∈ Finset.range B, VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb n N = 29 ^ n

/-- `d4FusionF m (1) = 28^m` from the `D₄` count. -/
theorem d4FusionF_count (hC : D4DemazureCount) (m : ℕ) :
    ∃ B, (∀ b, B ≤ b → coeff b (d4FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, coeff b (d4FusionF m) = ((28 : ℕ) : ℚ) ^ m := by
  refine fusionOf_count _ 28 (fun n => ?_) m
  obtain ⟨B, hB, hs⟩ := hC n
  refine ⟨B, fun N hN => ?_, ?_⟩
  · rw [hilbSeries, coeff_mk, hB N hN]; simp
  · simp only [hilbSeries, coeff_mk]
    rw [← Nat.cast_sum, hs]
    norm_num

theorem d4sector_n : VOA.DeligneAudit.DeligneSector.D4.D4sector.n = 28 := rfl

open VOA.DeligneAudit.DeligneSector SectorWeyl in
/-- **U5 for `D₄`** (`FusionModuleBoundG D4sector d4FusionF`) from the `D₄` count, the squeeze
inputs and the universal bound. -/
theorem d4_fusionModuleBound_of_squeeze (hC : D4DemazureCount)
    (h : FusionSqueezeInputsG (hilbSeries VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb) 28 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.D4sector.f V) (w : V),
      LocalWeylRelG VOA.DeligneAudit.DeligneSector.D4.D4sector ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBoundG VOA.DeligneAudit.DeligneSector.D4.D4sector d4FusionF :=
  fusionModuleBoundG_of_squeeze _ d4sector_n h (d4FusionF_count hC) huniv

end

end VOA.DeligneAudit.DeligneCarrier

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.fusionOf_count
#print axioms VOA.DeligneAudit.DeligneCarrier.squeezeG
#print axioms VOA.DeligneAudit.DeligneCarrier.fusionOf_coeff_nonneg
#print axioms VOA.DeligneAudit.DeligneCarrier.fusionModuleBoundG_of_squeeze
#print axioms VOA.DeligneAudit.DeligneCarrier.d4FusionF_count
#print axioms VOA.DeligneAudit.DeligneCarrier.d4_fusionModuleBound_of_squeeze
end AxiomAudit
