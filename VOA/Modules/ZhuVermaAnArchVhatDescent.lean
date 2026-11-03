/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVhat
import VOA.Modules.ZhuModule

/-!
# `BracketDescends` and `VHatAntisymm` for `V̂`

This file discharges two of the three named obligations of the Frenkel–Zhu loop Lie algebra `V̂`
(`ZhuVermaAnArchVhat.lean`):

* **`VHat.BracketDescends W`** — `Im D` (the derivative relations
  `(L₋₁a)(m) = -m·a(m-1)`) is a two-sided ideal for the Borcherds loop bracket
  `vloopBracket`.  This rests on the VOA fact that `L₋₁` is a derivation of every mode product
  (`Core.Reconstruction.L_neg_one_deriv` / `Modules.ZhuModule.smul_L_neg_one`), packaged through the
  generalized-binomial Pascal/falling-factorial identity
  `(j+1)·C(m,j+1) = (m-j)·C(m,j)` (`Foundations.Substitution.gBinom_mul_factorial`,
  `prod_falling_succ`).  Concretely, bracketing a derivative generator against any `b(k)` produces a
  *finite sum of derivative generators*:
  `[a(m), Dgen(k,b)] = Σᵢ C(m,i) · Dgen(m+k-i, a₍ᵢ₎b)`,  and dually on the left.

* **`VHat.VHatAntisymm W hD`** — `⁅x,y⁆ = -⁅y,x⁆` on `V̂` (given descent).  This file proves the
  *reduction* `vhatAntisymm_of_genSkew`: antisymmetry follows from the single generator identity
  `VHatGenSkew` by bilinearity (`gen_span_top`).  It also proves the translation-tower collapse
  `gen_T_pow` — `(Tʲw)(n) = (-1)ʲ·j!·C(n,j)·w(n-j)` — which is precisely the infra that absorbs the
  skew-mode `e^{zL₋₁}`-tower (`Core.SkewSymmetry.skew_mode`, Gannon 5.1.8) into a binomial.

## Status
`BracketDescends` (T2) is fully **closed** (`bracketDescends`), green & axiom-clean
(`#print axioms = [propext, Classical.choice, Quot.sound]`, not even depending on `pbw`).
For antisymmetry, the bilinearity reduction `vhatAntisymm_of_genSkew` and the tower infra
`gen_T_pow` are closed; the remaining target is the *generator* skew identity `VHatGenSkew`
(see its docstring): substituting `skew_mode` and collapsing the tower via `gen_T_pow` turns it into
the binomial-convolution resummation matching `∑ᵢ C(m,i)·C(m+k-i,j)` against `C(k,·)` — the genuine
deep content (the loop-level analogue of `Core.Skew`).  No `sorry`/axiom anywhere here.

## References
DLM3 §4; H. Li, hep-th/9406211 §2, Lemma 2.1; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## Scalar identities for the generalized binomial coefficients -/

/-- The falling-factorial step `(j+1)·C(m,j+1) = (m-j)·C(m,j)` (clear factorials and peel one
factor via `prod_falling_succ`). -/
theorem gBinom_succ_index (m : ℤ) (j : ℕ) :
    ((j : ℂ) + 1) * gBinom m (j + 1) = ((m : ℂ) - (j : ℂ)) * gBinom m j := by
  have hfac_ne : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  refine mul_left_cancel₀ hfac_ne ?_
  -- Cancel j!.  LHS·j! = (j+1)!·C(m,j+1) = ∏_{i<j+1}(m-i);  RHS·j! = (m-j)·∏_{i<j}(m-i).
  rw [show ((j.factorial : ℂ)) * (((j : ℂ) + 1) * gBinom m (j + 1))
        = ((((j + 1).factorial : ℂ)) * gBinom m (j + 1)) by
        rw [Nat.factorial_succ]; push_cast; ring,
      show ((j.factorial : ℂ)) * (((m : ℂ) - (j : ℂ)) * gBinom m j)
        = ((m : ℂ) - (j : ℂ)) * (((j.factorial : ℂ)) * gBinom m j) by ring,
      gBinom_mul_factorial m (j + 1), gBinom_mul_factorial m j,
      Finset.prod_range_succ (fun i => (m : ℂ) - (i : ℂ)) j]
  ring

/-- The dual step `m·C(m-1,j) = (m-j)·C(m,j)` (same falling-factorial peeling, on `m-1`). -/
theorem gBinom_pred_index (m : ℤ) (j : ℕ) :
    (m : ℂ) * gBinom (m - 1) j = ((m : ℂ) - (j : ℂ)) * gBinom m j := by
  -- m·C(m-1,j) = m·[∏_{i<j}((m-1)-i)/j!];  (m-j)·C(m,j) = (m-j)·[∏_{i<j}(m-i)/j!].
  -- Both equal ∏_{i<j+1 shifted}; clear factorials.
  have hfac_ne : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  refine mul_left_cancel₀ hfac_ne ?_
  rw [show ((j.factorial : ℂ)) * ((m : ℂ) * gBinom (m - 1) j)
        = (m : ℂ) * (((j.factorial : ℂ)) * gBinom (m - 1) j) by ring,
      show ((j.factorial : ℂ)) * (((m : ℂ) - (j : ℂ)) * gBinom m j)
        = ((m : ℂ) - (j : ℂ)) * (((j.factorial : ℂ)) * gBinom m j) by ring,
      gBinom_mul_factorial (m - 1) j, gBinom_mul_factorial m j]
  -- m·∏_{i<j}((m-1)-i) = (m-j)·∏_{i<j}(m-i).  Both equal ∏_{i<j+1}(m-i) (peel top vs bottom).
  have h1 : (m : ℂ) * ∏ i ∈ Finset.range j, (((m - 1 : ℤ) : ℂ) - (i : ℂ))
      = ∏ i ∈ Finset.range (j + 1), ((m : ℂ) - (i : ℂ)) := by
    rw [prod_falling_succ (m : ℂ) j]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  have h2 : ((m : ℂ) - (j : ℂ)) * ∏ i ∈ Finset.range j, ((m : ℂ) - (i : ℂ))
      = ∏ i ∈ Finset.range (j + 1), ((m : ℂ) - (i : ℂ)) := by
    rw [Finset.prod_range_succ (fun i => (m : ℂ) - (i : ℂ)) j]
    ring
  rw [h1, h2]

/-! ## The bracket value on generators as a finite `Finset.range` sum

Convert the OPE finsums to ordinary `Finset.range N` sums over a uniform bound, so the descent
identity becomes finite-sum algebra (`Finset.sum_range_succ'` reindexing + the scalar identities). -/

/-- `[a(m), b(k)] = ∑_{i<N} C(m,i)·(a₍ᵢ₎b)(m+k-i)` for any `N` past the OPE bound. -/
theorem vloopBracket_single_range (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱)
    {N : ℕ} (hN : ∀ i : ℕ, N ≤ i → W.smul a i b = 0) :
    vloopBracket W (single m a) (single k b)
      = ∑ i ∈ Finset.range N, (gBinom m i) • single (m + k - i) (W.smul a i b) := by
  rw [vloopBracket_single]
  refine finsum_eq_sum_of_support_subset _ ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by rw [hN i hcon, Finsupp.single_zero, smul_zero])

/-! ## `BracketDescends` — the ideal property of `Im D`

The generator of `Im D` is `Dgen(n,c) := c(n) ⊗ … = single n (L₋₁c) + n·single (n-1) c`.  We show
both `[Dgen(m,a), single k b]` and `[single m a, Dgen(k,b)]` are finite sums of `Dgen`'s. -/

/-- The derivative generator `Dgen(n,c) = (L₋₁c)(n) + n·c(n-1)`, lying in `Im D`. -/
theorem dgen_mem (W : VertexOperatorAlgebra 𝒱) (c : 𝒱) (n : ℤ) :
    single n (W.L (-1) c) + (n : ℂ) • single (n - 1) c ∈ loopDerivSubmodule W :=
  derivGen_mem W c n

/-- **The shift identity** underlying the right-ideal property.  After substituting
`a₍ᵢ₎(L₋₁b) = L₋₁(a₍ᵢ₎b) + i·a₍ᵢ₋₁₎b` and cancelling the `L₋₁(a₍ᵢ₎b)` pieces, the remainder of
`[a(m), Dgen(k,b)] = ∑ᵢ C(m,i)·Dgen(m+k-i, a₍ᵢ₎b)` is this finite-sum identity in the bare singles.
It collapses by the falling-factorial step `(i+1)·C(m,i+1) = (m-i)·C(m,i)` (`gBinom_succ_index`),
after a `Finset.sum_range_succ'` reindexing of the `a₍ᵢ₋₁₎b` sum. -/
theorem vhatDescent_shift_right (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱) {N : ℕ}
    (hNb : ∀ i : ℕ, N ≤ i → W.smul a i b = 0) :
    (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + k - i) ((i : ℂ) • W.smul a (i - 1) b))
      + (k : ℂ) • (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + (k - 1) - i) (W.smul a i b))
      = ∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • (((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)) := by
  classical
  -- Reindex the first sum (i ↦ i+1; the i=0 term has factor `0`), and trim the other two sums
  -- to range N (the i=N term carries `a₍N₎b = 0`).
  have hfirst : (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + k - i) ((i : ℂ) • W.smul a (i - 1) b))
      = ∑ i ∈ Finset.range N,
        (((i : ℂ) + 1) * gBinom m (i + 1)) • single (m + k - i - 1) (W.smul a i b) := by
    rw [Finset.sum_range_succ' (fun i => (gBinom m i) • single (m + k - i)
          ((i : ℂ) • W.smul a (i - 1) b)) N]
    simp only [Nat.cast_zero, zero_smul, Finsupp.single_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he2 : (m + k - ((i : ℤ) + 1)) = m + k - i - 1 := by ring
    have he3 : ((i : ℤ) + 1 - 1) = (i : ℤ) := by ring
    rw [Finsupp.smul_single, smul_smul, Finsupp.smul_single]
    push_cast
    rw [he2, he3]
    congr 2
    ring
  have hsecond : (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + (k - 1) - i) (W.smul a i b))
      = ∑ i ∈ Finset.range N,
        (gBinom m i) • single (m + (k - 1) - i) (W.smul a i b) := by
    rw [Finset.sum_range_succ, hNb N le_rfl, Finsupp.single_zero, smul_zero, add_zero]
  have hthird : (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • (((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)))
      = ∑ i ∈ Finset.range N,
        (gBinom m i) • (((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)) := by
    rw [Finset.sum_range_succ, hNb N le_rfl, Finsupp.single_zero, smul_zero, smul_zero, add_zero]
  rw [hfirst, hsecond, hthird, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- termwise: same single (degree m+k-i-1, vector a₍ᵢ₎b); match the scalar coefficients
  rw [smul_smul, smul_smul, show m + (k - 1) - i = m + k - i - 1 from by ring, ← add_smul]
  congr 1
  -- ((i+1)·C(m,i+1)) + k·C(m,i) = C(m,i)·(m+k-i)
  rw [gBinom_succ_index m i]
  push_cast; ring

/-- **Right ideal property (generators).**  Bracketing `a(m)` against a derivative generator
`Dgen(k,b)` yields a finite sum of derivative generators:
`[a(m), Dgen(k,b)] = ∑ᵢ C(m,i)·Dgen(m+k-i, a₍ᵢ₎b)` — hence lands in `Im D`. -/
theorem vloopBracket_single_dgen_right (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱) :
    vloopBracket W (single m a) (single k (W.L (-1) b) + (k : ℂ) • single (k - 1) b)
      ∈ loopDerivSubmodule W := by
  classical
  -- pick a uniform bound past which all relevant OPE products vanish
  obtain ⟨N1, hN1⟩ := W.smul_eventually_zero a b
  obtain ⟨N2, hN2⟩ := W.smul_eventually_zero a (W.L (-1) b)
  set N : ℕ := (max N1 N2).toNat with hNdef
  have hNb : ∀ i : ℕ, N ≤ i → W.smul a i b = 0 := fun i hi =>
    hN1 i (le_trans (le_max_left N1 N2) (le_trans (Int.self_le_toNat _) (by exact_mod_cast hi)))
  have hNLb : ∀ i : ℕ, N ≤ i → W.smul a i (W.L (-1) b) = 0 := fun i hi =>
    hN2 i (le_trans (le_max_right N1 N2) (le_trans (Int.self_le_toNat _) (by exact_mod_cast hi)))
  -- expand the bracket bilinearly into two range sums
  rw [map_add, map_smul]
  rw [vloopBracket_single_range W m k a (W.L (-1) b) (N := N + 1) (fun i hi => hNLb i (by omega)),
    vloopBracket_single_range W m (k - 1) a b (N := N + 1) (fun i hi => hNb i (by omega))]
  -- target finite sum of derivative generators
  have htarget : (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + k - i) (W.smul a i (W.L (-1) b)))
      + (k : ℂ) • ∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + (k - 1) - i) (W.smul a i b)
      = ∑ i ∈ Finset.range (N + 1), (gBinom m i) •
          (single (m + k - i) (W.L (-1) (W.smul a i b))
            + ((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)) := by
    -- rewrite a₍ᵢ₎(L₋₁b) = L₋₁(a₍ᵢ₎b) + i·a₍ᵢ₋₁₎b on the left
    have hderiv : ∀ i : ℕ, W.smul a i (W.L (-1) b)
        = W.L (-1) (W.smul a i b) + (i : ℂ) • W.smul a (i - 1) b := by
      intro i
      have h := L_neg_one_deriv W a b i
      have hL : W.smul (W.L (-1) a) (i : ℤ) b = (-(i : ℂ)) • W.smul a ((i : ℤ) - 1) b := by
        rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ]
        push_cast; ring_nf
      have hrw : W.smul a (i : ℤ) (W.L (-1) b)
          = W.L (-1) (W.smul a (i : ℤ) b) - W.smul (W.L (-1) a) (i : ℤ) b := by
        rw [← h]; abel
      rw [hrw, hL, neg_smul, sub_neg_eq_add]
    -- split each big sum into its L₋₁-part + remainder, cancel the L₋₁-parts, apply the shift id
    rw [show (∑ i ∈ Finset.range (N + 1),
            (gBinom m i) • single (m + k - i) (W.smul a i (W.L (-1) b)))
          = (∑ i ∈ Finset.range (N + 1),
              (gBinom m i) • single (m + k - i) (W.L (-1) (W.smul a i b)))
            + (∑ i ∈ Finset.range (N + 1),
              (gBinom m i) • single (m + k - i) ((i : ℂ) • W.smul a (i - 1) b))
          from by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_;
                  rw [hderiv i, Finsupp.single_add, smul_add],
       show (∑ i ∈ Finset.range (N + 1), (gBinom m i) •
            (single (m + k - i) (W.L (-1) (W.smul a i b))
              + ((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)))
          = (∑ i ∈ Finset.range (N + 1),
              (gBinom m i) • single (m + k - i) (W.L (-1) (W.smul a i b)))
            + (∑ i ∈ Finset.range (N + 1),
              (gBinom m i) • (((m + k - i : ℤ) : ℂ) • single (m + k - i - 1) (W.smul a i b)))
          from by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_;
                  rw [smul_add]]
    rw [add_assoc, add_right_inj, vhatDescent_shift_right W m k a b hNb]
  rw [htarget]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ _ (dgen_mem W (W.smul a i b) (m + k - i))

/-- **Left ideal property (generators), strong form.**  Bracketing a derivative generator
`Dgen(m,a)` against any `b(k)` is *identically zero* on the loop space:
`[Dgen(m,a), b(k)] = 0`.  The two binomial families collapse against each other by the dual
falling-factorial steps `(i+1)·C(m,i+1) = (m-i)·C(m,i)` (`gBinom_succ_index`) and
`m·C(m-1,i) = (m-i)·C(m,i)` (`gBinom_pred_index`).  (This is the loop-level statement that
`Im D` is genuinely a null-relation for the bracket from the left.) -/
theorem vloopBracket_dgen_left_eq_zero (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱) :
    vloopBracket W (single m (W.L (-1) a) + (m : ℂ) • single (m - 1) a) (single k b) = 0 := by
  classical
  obtain ⟨N1, hN1⟩ := W.smul_eventually_zero a b
  obtain ⟨N2, hN2⟩ := W.smul_eventually_zero (W.L (-1) a) b
  set N : ℕ := (max N1 N2).toNat with hNdef
  have hNb : ∀ i : ℕ, N ≤ i → W.smul a i b = 0 := fun i hi =>
    hN1 i (le_trans (le_max_left N1 N2) (le_trans (Int.self_le_toNat _) (by exact_mod_cast hi)))
  have hNLa : ∀ i : ℕ, N ≤ i → W.smul (W.L (-1) a) i b = 0 := fun i hi =>
    hN2 i (le_trans (le_max_right N1 N2) (le_trans (Int.self_le_toNat _) (by exact_mod_cast hi)))
  -- expand bilinearly into two range-(N+1) sums
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  rw [vloopBracket_single_range W m k (W.L (-1) a) b (N := N + 1) (fun i hi => hNLa i (by omega)),
    vloopBracket_single_range W (m - 1) k a b (N := N + 1) (fun i hi => hNb i (by omega))]
  -- rewrite (L₋₁a)₍ᵢ₎b = -i·a₍ᵢ₋₁₎b in the first sum
  have hP : (∑ i ∈ Finset.range (N + 1),
        (gBinom m i) • single (m + k - i) (W.smul (W.L (-1) a) i b))
      = ∑ i ∈ Finset.range N,
        (-(((i : ℂ) + 1) * gBinom m (i + 1))) • single (m + k - i - 1) (W.smul a i b) := by
    -- substitute (L₋₁a)₍ᵢ₎b = -i·a₍ᵢ₋₁₎b, then reindex i ↦ i+1
    have hsub : ∀ i : ℕ, W.smul (W.L (-1) a) i b = (-(i : ℂ)) • W.smul a ((i : ℤ) - 1) b := by
      intro i; rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ]; push_cast; ring_nf
    rw [Finset.sum_congr rfl fun i _ => by rw [hsub i]]
    rw [Finset.sum_range_succ' (fun i => (gBinom m i) •
          single (m + k - i) ((-(i : ℂ)) • W.smul a ((i : ℤ) - 1) b)) N]
    simp only [Nat.cast_zero, neg_zero, zero_smul, Finsupp.single_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have he2 : (m + k - ((i : ℤ) + 1)) = m + k - i - 1 := by ring
    have he3 : ((i : ℤ) + 1 - 1) = (i : ℤ) := by ring
    rw [Finsupp.smul_single, smul_smul, Finsupp.smul_single]
    push_cast
    rw [he2, he3]
    congr 2
    ring
  -- trim the second sum to range N (i=N term has a₍N₎b = 0)
  have hQ : (∑ i ∈ Finset.range (N + 1),
        (gBinom (m - 1) i) • single ((m - 1) + k - i) (W.smul a i b))
      = ∑ i ∈ Finset.range N,
        (gBinom (m - 1) i) • single (m + k - i - 1) (W.smul a i b) := by
    rw [Finset.sum_range_succ, hNb N le_rfl, Finsupp.single_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ring
  rw [hP, hQ, Finset.smul_sum, ← Finset.sum_add_distrib]
  -- termwise: coefficients cancel
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_smul, ← add_smul]
  -- -(i+1)·C(m,i+1) + m·C(m-1,i) = 0
  have h1 : ((i : ℂ) + 1) * gBinom m (i + 1) = ((m : ℂ) - (i : ℂ)) * gBinom m i :=
    gBinom_succ_index m i
  have h2 : (m : ℂ) * gBinom (m - 1) i = ((m : ℂ) - (i : ℂ)) * gBinom m i :=
    gBinom_pred_index m i
  rw [h1, h2, neg_add_cancel, zero_smul]

/-! ## Lifting the generator lemmas to all of `Im D` and all `y` -/

/-- A derivative generator brackets to `Im D` against any `y` on the right
(`[y, Dgen(k,b)] ∈ Im D`): reduce `y` to singles by `Finsupp.induction_linear` and apply
`vloopBracket_single_dgen_right`. -/
theorem vloopBracket_dgen_right_mem (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (b : 𝒱) (y : VLoop 𝒱) :
    vloopBracket W y (single k (W.L (-1) b) + (k : ℂ) • single (k - 1) b)
      ∈ loopDerivSubmodule W := by
  classical
  induction y using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add y y' hy hy' =>
    rw [show vloopBracket W (y + y') = vloopBracket W y + vloopBracket W y' from map_add _ _ _,
      LinearMap.add_apply]
    exact Submodule.add_mem _ hy hy'
  | single m a => exact vloopBracket_single_dgen_right W m k a b

/-- A derivative generator brackets to `0` against any `y` on the left (`[Dgen(m,a), y] = 0`):
reduce `y` to singles and apply `vloopBracket_dgen_left_eq_zero`. -/
theorem vloopBracket_dgen_left_eq_zero' (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱)
    (y : VLoop 𝒱) :
    vloopBracket W (single m (W.L (-1) a) + (m : ℂ) • single (m - 1) a) y = 0 := by
  classical
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  | single k b => exact vloopBracket_dgen_left_eq_zero W m k a b

/-- **Target T2 — `BracketDescends`.**  `Im D` is a two-sided ideal for the Borcherds loop bracket.
The left side is the *strong* fact `[Dgen, y] = 0`; the right side is `[y, Dgen] ∈ Im D` as a
finite sum of derivative generators.  Both lift from the generator lemmas by `span`-induction on the
`Im D`-member and `Finsupp` bilinearity on `y`. -/
theorem bracketDescends (W : VertexOperatorAlgebra 𝒱) : VHat.BracketDescends W := by
  classical
  intro x hx y
  -- induct on x ∈ span of derivative generators
  refine Submodule.span_induction (p := fun x _ =>
      vloopBracket W x y ∈ loopDerivSubmodule W ∧ vloopBracket W y x ∈ loopDerivSubmodule W)
    ?gen ?zero ?add ?smul hx
  case gen =>
    rintro z ⟨a, m, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [vloopBracket_dgen_left_eq_zero' W m a y]; exact Submodule.zero_mem _
    · exact vloopBracket_dgen_right_mem W m a y
  case zero =>
    exact ⟨by rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _,
           by rw [map_zero]; exact Submodule.zero_mem _⟩
  case add =>
    rintro z z' - - ⟨hz1, hz2⟩ ⟨hz1', hz2'⟩
    refine ⟨?_, ?_⟩
    · rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hz1 hz1'
    · rw [map_add]; exact Submodule.add_mem _ hz2 hz2'
  case smul =>
    rintro c z - ⟨hz1, hz2⟩
    refine ⟨?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hz1
    · rw [map_smul]; exact Submodule.smul_mem _ _ hz2

/-! ## The translation tower on generators (infra for the skew identity)

The derivative relation `gen_Lneg1` makes `T = L₋₁` act on generators by a *single* falling-factorial
shift; iterating gives the closed `T^j` form used to absorb the skew-mode `e^{zL₋₁}`-tower into the
binomial `C(n,j)`. -/

/-- `T = L₋₁` acts on a generator by one falling-factorial step: `(Tw)(n) = -n·w(n-1)`. -/
theorem gen_T (W : VertexOperatorAlgebra 𝒱) (w : 𝒱) (n : ℤ) :
    gen W (W.toPreVertexAlgebra.T w) n = -(n : ℂ) • gen W w (n - 1) := by
  rw [show W.toPreVertexAlgebra.T w = W.L (-1) w from by rw [T_eq_Lneg1], gen_Lneg1]

/-- The iterated translation tower on a generator:
`(Tʲw)(n) = (-1)ʲ · j! · C(n,j) · w(n-j)`  (the `e^{zL₋₁}` tower collapses to a single binomial). -/
theorem gen_T_pow (W : VertexOperatorAlgebra 𝒱) (w : 𝒱) (n : ℤ) (j : ℕ) :
    gen W ((W.toPreVertexAlgebra.T ^ j) w) n
      = ((-1 : ℂ) ^ j * (j.factorial : ℂ) * gBinom n j) • gen W w (n - j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    -- T^{j+1} w = T (T^j w); peel the outer T, then apply the IH to the inner T^j
    rw [pow_succ', Module.End.mul_apply, gen_T, ih (n - 1), smul_smul,
      show (n - 1 - (j : ℤ)) = n - ((j : ℤ) + 1) from by ring,
      show (n - ((j + 1 : ℕ) : ℤ)) = n - ((j : ℤ) + 1) from by push_cast; ring]
    congr 1
    -- (-n)·((-1)^j·j!·C(n-1,j)) = (-1)^{j+1}·(j+1)!·C(n,j+1)
    have hpd : (n : ℂ) * gBinom (n - 1) j = ((n : ℂ) - (j : ℂ)) * gBinom n j :=
      gBinom_pred_index n j
    have hgb : ((j : ℂ) + 1) * gBinom n (j + 1) = ((n : ℂ) - (j : ℂ)) * gBinom n j :=
      gBinom_succ_index n j
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    rw [show (-(n : ℂ)) * ((-1 : ℂ) ^ j * (j.factorial : ℂ) * gBinom (n - 1) j)
          = (-1 : ℂ) ^ j * (j.factorial : ℂ) * (-((n : ℂ) * gBinom (n - 1) j)) from by ring,
      show (-1 : ℂ) ^ j * -1 * (((j : ℂ) + 1) * (j.factorial : ℂ)) * gBinom n (j + 1)
          = (-1 : ℂ) ^ j * (j.factorial : ℂ) * (-(((j : ℂ) + 1) * gBinom n (j + 1))) from by ring,
      hpd, hgb]

/-! ## `VHatAntisymm` — reduction to the generator-level skew identity

Antisymmetry of the descended bracket is bilinear and generators span `V̂`, so it reduces to the
single statement on generators
`∑ᵢ C(m,i)·(u₍ᵢ₎v)(m+k-i) = -∑ᵢ C(k,i)·(v₍ᵢ₎u)(k+m-i)`  in `V̂`,
which is VOA skew-symmetry `Y(u,z)v = e^{zL₋₁}Y(v,-z)u` (Gannon 5.1.8, `Core.SkewSymmetry.skew_mode`)
absorbed into `Im D` via the derivative relation `(L₋₁c)(n) = -n·c(n-1)` (`gen_Lneg1`). -/

/-- The generator-level skew identity for `V̂` — the precise remaining content for antisymmetry.
Unfolding `vhatBracket_gen` it reads
`∑ᵢ C(m,i)·(u₍ᵢ₎v)(m+k-i) = -∑ᵢ C(k,i)·(v₍ᵢ₎u)(k+m-i)`  in `V̂`.
Substituting `Core.SkewSymmetry.skew_mode` for `u₍ᵢ₎v` and collapsing the resulting `Tʲ`-tower with
`gen_T_pow` turns the LHS into a double sum `∑ᵢ∑ⱼ C(m,i)·(-1)ʲ·sgn(-i-1-j)·C(m+k-i,j)·(v₍-i-1-j₎u)(…)`,
and the identity becomes the Borcherds/skew binomial-convolution resummation against `C(k,·)` — the
loop-level analogue of `Core.Skew`.  `vhatAntisymm_of_genSkew` lifts this to all of `V̂`. -/
def VHatGenSkew (W : VertexOperatorAlgebra 𝒱) (hD : VHat.BracketDescends W) : Prop :=
  ∀ (u v : 𝒱) (m k : ℤ),
    VHat.vhatBracket W hD (VHat.gen W u m) (VHat.gen W v k)
      = - VHat.vhatBracket W hD (VHat.gen W v k) (VHat.gen W u m)

/-- **Reduction T3a.**  The generator-level skew identity `VHatGenSkew` implies full antisymmetry
`VHatAntisymm` on `V̂`.  By `VHat.gen_span_top` the generators span `V̂`, and `vhatBracket` is
bilinear, so the identity propagates from generators to all elements. -/
theorem vhatAntisymm_of_genSkew (W : VertexOperatorAlgebra 𝒱) (hD : VHat.BracketDescends W)
    (hgen : VHatGenSkew W hD) : VHat.VHatAntisymm W hD := by
  classical
  -- `B x y = -B y x` for `x` a generator and `y` arbitrary, by span induction on `y`.
  have keyR : ∀ (a : 𝒱) (m : ℤ) (y : VHat.VHatCarrier W),
      vhatBracket W hD (gen W a m) y = - vhatBracket W hD y (gen W a m) := by
    intro a m y
    have hy : y ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
      rw [gen_span_top]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨⟨b, k⟩, rfl⟩ := hz; exact hgen a b m k
    | zero => rw [map_zero, map_zero, LinearMap.zero_apply, neg_zero]
    | add z z' _ _ hz hz' =>
      rw [map_add,
        show vhatBracket W hD (z + z') (gen W a m)
            = vhatBracket W hD z (gen W a m) + vhatBracket W hD z' (gen W a m) from by
          rw [map_add, LinearMap.add_apply],
        hz, hz', neg_add]
    | smul c z _ hz =>
      rw [map_smul,
        show vhatBracket W hD (c • z) (gen W a m) = c • vhatBracket W hD z (gen W a m) from by
          rw [map_smul, LinearMap.smul_apply],
        hz, smul_neg]
  -- now span induction on `x`
  intro x y
  have hx : x ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
    rw [gen_span_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨⟨a, m⟩, rfl⟩ := hz; exact keyR a m y
  | zero => rw [map_zero, LinearMap.zero_apply, LinearMap.map_zero, neg_zero]
  | add z z' _ _ hz hz' =>
    rw [show vhatBracket W hD (z + z') y = vhatBracket W hD z y + vhatBracket W hD z' y from by
          rw [map_add, LinearMap.add_apply],
      map_add, hz, hz', neg_add]
  | smul c z _ hz =>
    rw [show vhatBracket W hD (c • z) y = c • vhatBracket W hD z y from by
          rw [map_smul, LinearMap.smul_apply],
      map_smul, hz, smul_neg]

end VHat

end VOA
