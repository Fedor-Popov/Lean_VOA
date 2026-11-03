/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionCount

/-!
# U5: the graded squeeze (Ravinder Cor. 1)

Let `M a b` be the graded characters of Ravinder's modules `M_{a,b}` for `sl₃`: `M_{0,m}` is the
universal fusion module `W_loc(mθ)/⟨(f_α ⊗ t^m)w⟩` and `M_{n,0} = W_loc(nθ)`.  The inputs, as named
hypotheses (`FusionSqueezeInputs M`):

* `nonneg` — characters have nonnegative coefficients (they are graded dimensions);
* `rec_le` — the spanning half of Ravinder's exact sequences
  `0 → q^{2a+b+1} M_{a,b} → M_{a+1,b} → M_{a,b+1} → 0`:
  `ch M_{a+1,b} ≤ ch M_{a,b+1} + q^{2a+b+1} ch M_{a,b}` coefficientwise;
* `dem_le` — `Hilb_q D(1,nθ) ≤ ch W_loc(nθ)`, with `Hilb_q D(1,nθ)` read as the Gelfand–Tsetlin
  polynomial `demazureHilbSeries n` (this is where U7 enters: `D(1,nθ)` is a graded quotient of
  `W_loc(nθ)`, and U7 identifies its character);
* `total_le` — F4: `dim M_{0,m} ≤ 8^m`.

**Squeeze** (`squeeze`): then `ch M_{0,m} = fusionF m` for every `m`.
Proof by strong induction:
iterating `rec_le` gives `ch M_{n,0} ≤ ∑_d q^{nd}[n,d] ch M_{0,n-d}` (`le_mixed`); with the
induction hypothesis and U6 (`fusionF` solves `Dem n = ∑_d q^{nd}[n,d] fusionF (n-d)`) this reads
`fusionF n ≤ ch M_{0,n}` coefficientwise; F3 (`fusionF n (1) = 8^n`) and `total_le` force equality.

Consequences: `fusionF` has nonnegative coefficients (`fusionF_coeff_nonneg`), and U5
(`SectorWeyl.FusionModuleBound fusionF`, both fields) follows once every module with the local Weyl
and fusion relations is bounded by the universal one (`fusionModuleBound_of_squeeze`).
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.DeligneGaussian

open scoped BigOperators

noncomputable section

/-- Coefficientwise `≤` of power series over `ℚ`. -/
def CoeffLe (f g : PowerSeries ℚ) : Prop := ∀ N, coeff N f ≤ coeff N g

theorem CoeffLe.refl (f : PowerSeries ℚ) : CoeffLe f f := fun _ => le_rfl

theorem CoeffLe.trans {f g h : PowerSeries ℚ} (h1 : CoeffLe f g) (h2 : CoeffLe g h) :
    CoeffLe f h := fun N => (h1 N).trans (h2 N)

theorem CoeffLe.add {f g f' g' : PowerSeries ℚ} (h1 : CoeffLe f g) (h2 : CoeffLe f' g') :
    CoeffLe (f + f') (g + g') := fun N => by rw [map_add, map_add]; exact add_le_add (h1 N) (h2 N)

theorem CoeffLe.X_pow_mul {f g : PowerSeries ℚ} (h : CoeffLe f g) (k : ℕ) :
    CoeffLe (X ^ k * f) (X ^ k * g) := fun N => by
  rw [coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs
  · exact h _
  · exact le_rfl

theorem CoeffLe.add_left_cancel {f g s : PowerSeries ℚ} (h : CoeffLe (f + s) (g + s)) :
    CoeffLe f g := fun N => by
  have := h N; rw [map_add, map_add] at this; linarith

/-- **The named inputs of the squeeze** (Ravinder's modules `M_{a,b}` for `sl₃`). -/
structure FusionSqueezeInputs (M : ℕ → ℕ → PowerSeries ℚ) : Prop where
  /-- Graded characters have nonnegative coefficients. -/
  nonneg : ∀ a b N, 0 ≤ coeff N (M a b)
  /-- Spanning half of Ravinder's exact sequences. -/
  rec_le : ∀ a b, CoeffLe (M (a + 1) b) (M a (b + 1) + X ^ (2 * a + b + 1) * M a b)
  /-- `Hilb_q D(1,nθ) ≤ ch W_loc(nθ)`, with U7 (Demazure = Gelfand–Tsetlin). -/
  dem_le : ∀ n, CoeffLe (demazureHilbSeries n) (M n 0)
  /-- F4: `dim M_{0,m} ≤ 8^m`. -/
  total_le : ∀ m B, ∑ N ∈ Finset.range B, coeff N (M 0 m) ≤ 8 ^ m

variable {M : ℕ → ℕ → PowerSeries ℚ}

/-- Iterating the spanning inequality: `ch M_{a,b} ≤ mixed (ch M_{0,·}) a b`. -/
theorem le_mixed (h : FusionSqueezeInputs M) :
    ∀ a b, CoeffLe (M a b) (mixed (X : PowerSeries ℚ) (fun k => M 0 k) a b)
  | 0, b => CoeffLe.refl _
  | a + 1, b => by
      refine (h.rec_le a b).trans ?_
      rw [mixed]
      exact (le_mixed h a (b + 1)).add ((le_mixed h a b).X_pow_mul _)

/-- The mixed sum at `(n, 0)` with its `d = 0` term split off. -/
theorem mixed_split (f : ℕ → PowerSeries ℚ) (n : ℕ) :
    mixed (X : PowerSeries ℚ) f n 0 = f n +
      ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
        f (n - (d + 1)) := by
  rw [mixed_eq, Finset.sum_range_succ']
  simp only [zero_mul, pow_zero, qbinom_zero_right, mul_one, one_mul, add_zero, Nat.sub_zero]
  ring

/-- **The squeeze** (Ravinder Cor. 1): `ch M_{0,m} = fusionF m`. -/
theorem squeeze (h : FusionSqueezeInputs M) (m : ℕ) : M 0 m = fusionF m := by
  induction m using Nat.strong_induction_on with
  | _ n ih =>
    -- `fusionF n ≤ ch M_{0,n}` coefficientwise
    have hle : CoeffLe (fusionF n) (M 0 n) := by
      have h1 := (h.dem_le n).trans (le_mixed h n 0)
      rw [mixedFusionRecursion_fusionF.eq n, mixed_split, mixed_split] at h1
      have hS : ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
          M 0 (n - (d + 1)) = ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) *
            qbinom (X : PowerSeries ℚ) n (d + 1) * fusionF (n - (d + 1)) :=
        Finset.sum_congr rfl fun d hd => by
          simp only [Finset.mem_range] at hd
          rw [ih _ (by omega)]
      rw [hS] at h1
      exact h1.add_left_cancel
    -- equality from the totals
    obtain ⟨B0, hB0, hsum⟩ := fusionF_sum n
    ext N
    set B := max B0 (N + 1)
    have hfB : ∑ k ∈ Finset.range B, coeff k (fusionF n) = 8 ^ n := by
      rw [← hsum]
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _))
      intro k hk hk'
      simp only [Finset.mem_range, not_lt] at hk hk'
      exact hB0 k hk'
    have htot := h.total_le n B
    have heq := (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).mp
      (le_antisymm (Finset.sum_le_sum fun k _ => hle k) (by rw [hfB]; exact htot))
    exact (heq N (Finset.mem_range.mpr (by omega))).symm

/-- **`fusionF` has nonnegative coefficients** (from the squeeze inputs). -/
theorem fusionF_coeff_nonneg (h : FusionSqueezeInputs M) (m N : ℕ) :
    0 ≤ coeff N (fusionF m) := by
  rw [← squeeze h m]; exact h.nonneg 0 m N

open SectorWeyl VOA.AffineSl3 in
/-- **U5 for `fusionF`** from the squeeze inputs, given that every module with the local Weyl and
fusion relations is bounded by the universal one (`ch M_{0,m}`). -/
theorem fusionModuleBound_of_squeeze (h : FusionSqueezeInputs M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule (bracketTable) V) (w : V), LocalWeylRel ρ w m →
        ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤ coeff b (M 0 m)) :
    FusionModuleBound fusionF := by
  refine ⟨fun m V _ _ ρ w hw b => ?_, fun m V _ _ ρ w hw B => ?_⟩
  · rw [← squeeze h m]; exact huniv m V ρ w hw b
  · obtain ⟨B0, hB0, hsum⟩ := fusionF_sum m
    have key : (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg ρ w b) : ℚ)) ≤ 8 ^ m := by
      calc (∑ b ∈ Finset.range B, (Module.finrank ℂ (cycDeg ρ w b) : ℚ))
          ≤ ∑ b ∈ Finset.range B, coeff b (fusionF m) := Finset.sum_le_sum fun b _ => by
            rw [← squeeze h m]; exact huniv m V ρ w hw b
        _ ≤ ∑ b ∈ Finset.range (max B B0), coeff b (fusionF m) :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (le_max_left _ _))
              fun b _ _ => fusionF_coeff_nonneg h m b
        _ = 8 ^ m := by
            rw [← hsum]
            symm
            apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _))
            intro k hk hk'
            simp only [Finset.mem_range, not_lt] at hk hk'
            exact hB0 k hk'
    exact_mod_cast key

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.le_mixed
#print axioms VOA.DeligneAudit.A2.squeeze
#print axioms VOA.DeligneAudit.A2.fusionF_coeff_nonneg
#print axioms VOA.DeligneAudit.A2.fusionModuleBound_of_squeeze
end AxiomAudit
