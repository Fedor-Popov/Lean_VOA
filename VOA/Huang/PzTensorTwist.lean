/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientClose

/-!
# The contragredient twist on an abstract translation-covariant family

The library proves the module FHL identity (`Modules.ContragredientClose.rhs_gen_eq`) for the
family of maps `g ↦ Y_M(g)_k x` attached to an honest module `N` and a vector `x`.  The proof
uses only two properties of that family: it is **linear in the state** and **translation
covariant** (`(L₋₁g)_k = −k g_{k−1}`).  This file is a verbatim generalization of that proof to an
arbitrary family `φ : ℤ → 𝒱 →ₗ[ℂ] X` with these two properties (`TransCov`), so that it can be
applied to the transposed coproduct `ρ` of `PzTensorRho`, which is not the mode family of a
module.

`rhs_gen_eqT`: for homogeneous `u ∈ V_p`, `v ∈ V_q`,

`Σᶠ_i C(m,i) adj(u_{ℓ+i}v, m+n−i) = (−1)^{p+q} Σ_{b,a} (a!b!)⁻¹ Σᶠ_i C(2q−ℓ−n−2−b, i)
  φ_{(2q−ℓ−n−2−b)+(2p−ℓ−m−2−a)−i}((L₁ᵇv)_{ℓ+i}(L₁ᵃu))`,

where `adj(w, k) = (−1)^{wt w} Σ_j (1/j!) φ_{2 wt w − k − 2 − j}(L₁ʲ w)` is the contragredient
twist.

## Status
No `sorry`, no new axioms.  (Proof transcribed from `Modules/ContragredientFHL*`,
`Modules/ContragredientClose`, with `mode (N.YM ·) k xα` replaced by `φ k`.)
-/

namespace VOA.Huang.PzTensorTwist

open VOA VOA.VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {X : Type v} [AddCommGroup X] [Module ℂ X]

set_option linter.unusedVariables false in
/-- A family of linear functionals of the states, indexed by a mode (the VOA is recorded in the
type so that it can be inferred). -/
abbrev Fam (W : VertexOperatorAlgebra 𝒱) (X : Type v) [AddCommGroup X] [Module ℂ X] :=
  ℤ → 𝒱 →ₗ[ℂ] X

/-- **Translation covariance** . -/
def TransCov (φ : Fam W X) : Prop :=
  ∀ (k : ℤ) (g : 𝒱), φ k (W.L (-1) g) = (-(k : ℂ)) • φ (k - 1) g

section Twist

variable (φ : Fam W X)

/-- Iterated translation covariance. -/
theorem fam_Lneg1_pow (hφ : TransCov φ) (w : 𝒱) (j : ℕ) (s : ℤ) :
    φ s (((W.L (-1)) ^ j) w)
      = (-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((s - (l : ℤ) : ℤ) : ℂ)) • φ (s - (j : ℤ)) w := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      have hpow : ((W.L (-1)) ^ (k + 1)) w = W.L (-1) (((W.L (-1)) ^ k) w) := by
        rw [pow_succ']; rfl
      rw [hpow, hφ, ih (s - 1)]
      rw [show (s - 1) - (k : ℤ) = s - ((k + 1 : ℕ) : ℤ) from by push_cast; ring]
      have hprod : (∏ l ∈ Finset.range (k + 1), ((s - (l : ℤ) : ℤ) : ℂ))
          = (s : ℂ) * ∏ l ∈ Finset.range k, (((s - 1) - (l : ℤ) : ℤ) : ℂ) := by
        rw [Finset.prod_range_succ' (fun l => ((s - (l : ℤ) : ℤ) : ℂ)) k]
        rw [Finset.prod_congr rfl
          (fun l _ => show ((s - ((l + 1 : ℕ) : ℤ) : ℤ) : ℂ) = (((s - 1) - (l : ℤ) : ℤ) : ℂ) from by
            push_cast; ring)]
        push_cast; ring
      simp only [smul_smul]
      rw [hprod]
      congr 1
      ring

/-- Skew symmetry transported to the family. -/
theorem fam_skew_reduction (hφ : TransCov φ) (u v : 𝒱) (s k : ℤ) :
    φ k (W.smul v s u)
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ))) •
          ((-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ)) •
            φ (k - (j : ℤ)) (W.smul u (s + (j : ℤ)) v)) := by
  rw [skew_mode W v u s, map_finsum (φ k) (skew_support_finite W v u (-s - 1))]
  refine finsum_congr (fun j => ?_)
  rw [map_smul, map_smul, T_eq_Lneg1]
  have hidx : (W.Y u) (-s - 1 - (j : ℤ)) v = W.smul u (s + (j : ℤ)) v := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show -(s + (j : ℤ)) - 1 = -s - 1 - (j : ℤ) from by ring]
  rw [hidx, fam_Lneg1_pow φ hφ (W.smul u (s + (j : ℤ)) v) j k]

/-- Skew symmetry with the sign collapsed into a `gBinom` tower. -/
theorem mode_skew_gbinom (hφ : TransCov φ) (u v : 𝒱) (s k : ℤ) :
    φ k (W.smul v s u)
      = ∑ᶠ j : ℕ, ((- (-1:ℂ)^s) * gBinom k j) • φ (k - (j:ℤ)) (W.smul u (s + (j:ℤ)) v) := by
  rw [fam_skew_reduction φ hφ u v s k]
  refine finsum_congr (fun j => ?_)
  have hsign : sgn (-s - 1 - (j:ℤ)) * ((-1:ℂ)^j) = - (-1:ℂ)^s := by
    change negOnePow (-s - 1 - (j:ℤ)) * ((-1:ℂ)^j) = - (-1:ℂ)^s
    rw [← negOnePow_natCast j, ← negOnePow_add]
    rw [show (-s - 1 - (j:ℤ)) + (j:ℤ) = -s - 1 from by ring]
    have hr : (-1:ℂ)^(-s-1) = - (-1:ℂ)^s := by
      have h2 : (-1:ℂ)^(-2*s) = 1 := by
        rw [show (-2*s:ℤ)=2*(-s) from by ring]; exact negOne_zpow_even _
      have e : (-1:ℂ)^(-s-1) = (-1:ℂ)^s * (-1:ℂ)^(-2*s-1) := by
        rw [← zpow_add₀ (by norm_num : (-1:ℂ)≠0)]; congr 1; ring
      rw [e, show (-2*s-1:ℤ)=(-2*s)+(-1) from by ring, zpow_add₀ (by norm_num:(-1:ℂ)≠0), h2]
      ring
    rw [negOnePow_eq_zpow, hr]
  rw [show ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j:ℤ))) •
        ((-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ)) •
          φ (k - (j : ℤ)) (W.smul u (s + (j : ℤ)) v))
      = (((j.factorial : ℂ)⁻¹) * sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j *
          (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))) •
          φ (k - (j : ℤ)) (W.smul u (s + (j : ℤ)) v) from by
    rw [smul_smul, smul_smul, smul_smul]]
  congr 1
  rw [show ((j.factorial : ℂ)⁻¹) * sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j *
        (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))
      = (sgn (-s - 1 - (j:ℤ)) * (-1:ℂ)^j) *
          (((j.factorial : ℂ)⁻¹) * (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ))) from by ring]
  rw [hsign, gBinom_scalar]

/-- **The contragredient twist of the family**:
`adj(w, k) = (−1)^{wt} Σ_{j ≤ wt} (1/j!) φ_{2wt−k−2−j}(L₁ʲ w)`. -/
noncomputable def adj (wt : ℤ) (w : 𝒱) (k : ℤ) : X :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    φ (2 * wt - k - 2 - (j : ℤ)) ((W.L 1 ^ j) w)

/-- The antidiagonal bijection `(i,j) ↦ (i+j, j)` on `ℤ × ℕ`. -/
def shiftEquivT : ℤ × ℕ ≃ ℤ × ℕ where
  toFun p := (p.1 + (p.2 : ℤ), p.2)
  invFun p := (p.1 - (p.2 : ℤ), p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- **Antidiagonal reindex.** `∑ᶠ i ∑ᶠ j g(i,j) • V(i+j) = ∑ᶠ r (∑ᶠ j g(r−j,j)) • V(r)`. -/
theorem antidiag_reindexT (g : ℤ → ℕ → ℂ) (V : ℤ → X)
    (hfin : (Function.support (fun p : ℤ × ℕ => g p.1 p.2 • V (p.1 + (p.2 : ℤ)))).Finite)
    (hfin2 : (Function.support (fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1)).Finite)
    (hfinr : ∀ r : ℤ, (Function.support (fun j : ℕ => g (r - (j : ℤ)) j)).Finite) :
    ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), g i j • V (i + (j : ℤ))
      = ∑ᶠ (r : ℤ), (∑ᶠ (j : ℕ), g (r - (j : ℤ)) j) • V r := by
  rw [← finsum_curry (fun p : ℤ × ℕ => g p.1 p.2 • V (p.1 + (p.2 : ℤ))) hfin]
  have hstep : (∑ᶠ p : ℤ × ℕ, g p.1 p.2 • V (p.1 + (p.2 : ℤ)))
      = ∑ᶠ p : ℤ × ℕ, g (p.1 - (p.2 : ℤ)) p.2 • V p.1 := by
    rw [← finsum_comp_equiv shiftEquivT
      (f := fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1)]
    refine finsum_congr (fun p => ?_)
    change g p.1 p.2 • V (p.1 + (p.2 : ℤ))
      = g ((p.1 + (p.2 : ℤ)) - (p.2 : ℤ)) p.2 • V (p.1 + (p.2 : ℤ))
    rw [add_sub_cancel_right]
  rw [hstep, finsum_curry (fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1) hfin2]
  refine finsum_congr (fun r => ?_)
  rw [finsum_smul' (hfinr r)]


/-- The three antidiagonal finiteness side-goals, for `g` vanishing when the first arg `< 0`
and `V` vanishing for `B ≤ r`. -/
theorem antidiag_finsT (g : ℤ → ℕ → ℂ) (V : ℤ → X) (B : ℤ)
    (hg : ∀ i : ℤ, i < 0 → ∀ j : ℕ, g i j = 0)
    (hV : ∀ r : ℤ, B ≤ r → V r = 0) :
    (Function.support (fun pr : ℤ × ℕ => g pr.1 pr.2 • V (pr.1 + (pr.2 : ℤ)))).Finite
    ∧ (Function.support (fun pr : ℤ × ℕ => g (pr.1 - (pr.2 : ℤ)) pr.2 • V pr.1)).Finite
    ∧ (∀ r : ℤ, (Function.support (fun j : ℕ => g (r - (j : ℤ)) j)).Finite) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Finite.subset (Set.finite_Icc (0, 0) (B, B.toNat))
    intro pr hpr
    rw [Function.mem_support] at hpr
    have h1 : ¬ pr.1 < 0 := fun h => hpr (by rw [hg pr.1 h pr.2, zero_smul])
    have h2 : ¬ B ≤ pr.1 + (pr.2 : ℤ) := fun h => hpr (by rw [hV _ h, smul_zero])
    rw [Set.mem_Icc]
    refine ⟨⟨by omega, Nat.zero_le _⟩, by omega, by omega⟩
  · apply Set.Finite.subset (Set.finite_Icc (0, 0) (B, B.toNat))
    intro pr hpr
    rw [Function.mem_support] at hpr
    have h1 : ¬ pr.1 - (pr.2 : ℤ) < 0 := fun h => hpr (by rw [hg _ h pr.2, zero_smul])
    have h2 : ¬ B ≤ pr.1 := fun h => hpr (by rw [hV _ h, smul_zero])
    rw [Set.mem_Icc]
    refine ⟨⟨by omega, Nat.zero_le _⟩, by omega, by omega⟩
  · intro r
    apply Set.Finite.subset (Set.finite_Icc 0 r.toNat)
    intro j hj
    rw [Function.mem_support] at hj
    have h1 : ¬ r - (j : ℤ) < 0 := fun h => hj (hg _ h j)
    rw [Set.mem_Icc]
    refine ⟨Nat.zero_le _, by omega⟩


/-- A single `L₁`-tower term of `dualAdj` (state `u' ∈ 𝒱_wt`).  Vanishes for `t > wt.toNat`. -/
noncomputable def dterm (wt : ℤ) (u' : 𝒱) (k : ℤ) (t : ℕ) : X :=
  ((t.factorial : ℂ)⁻¹) • φ (2 * wt - k - 2 - (t : ℤ)) ((((W.L 1) ^ t) u'))

/-- The `t`-th tower term vanishes once `t > wt` (so `wt − t < 0`), since `L₁ᵗ u' = 0`. -/
theorem dterm_zero {wt : ℤ} {u' : 𝒱} (hu' : u' ∈ W.grading wt)
    (k : ℤ) {t : ℕ} (ht : wt - (t : ℤ) < 0) :
    dterm φ wt u' k t = 0 := by
  rw [dterm, L_one_pow_eq_zero W hu' ht, map_zero, smul_zero]

/-- **`dualAdj` as an infinite `∑ᶠ t` `L₁`-tower.**  The Finset `dualAdj_clean` sum over
`t ∈ range (wt.toNat+1)` extends to a `∑ᶠ t : ℕ` because the surplus terms `t > wt` are zero
vectors (`dterm_zero`).  This frees the comultiplication from any truncation. -/
theorem adj_finsum {wt : ℤ} {u' : 𝒱} (hu' : u' ∈ W.grading wt)
    (k : ℤ) :
    adj φ wt u' k = (-1 : ℂ) ^ wt • ∑ᶠ t : ℕ, dterm φ wt u' k t := by
  unfold adj
  have hfs : (∑ᶠ t : ℕ, dterm φ wt u' k t)
      = ∑ t ∈ Finset.range (wt.toNat + 1), dterm φ wt u' k t := by
    rw [finsum_eq_finsetSum_of_support_subset (dterm φ wt u' k)
        (s := Finset.range (wt.toNat + 1)) ?_]
    intro t ht
    rw [Function.mem_support] at ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    exact ht (dterm_zero φ hu' k (by omega))
  rw [hfs]
  rfl

/-! ## The common u-first `L₁`-tower vector `V` and its per-`r` coefficient. -/

/-- The common **u-first** tower vector
`V = mode (Y_M ((L₁ᵃu)₍ℓ+r₎(L₁ᵇv))) (D − A − B − r) xα`, `D = 2p+2q−2ℓ−m−n−4`. -/
noncomputable def Vtow (u v : 𝒱) (p q ℓ m n : ℤ)
    (A B : ℕ) (r : ℤ) : X :=
  φ ((2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A : ℤ) - (B : ℤ) - r)
    ((W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v)))

/-- The common per-`r` block coefficient `(−1)^{ℓ+1} · gBinom (2p−ℓ−m−2−A) r` (`0` for `r < 0`). -/
noncomputable def fcoeff (p ℓ m : ℤ) (A : ℕ) (r : ℤ) : ℂ :=
  if 0 ≤ r then (-1 : ℂ) ^ (ℓ + 1) * gBinom (2 * p - ℓ - m - 2 - (A : ℤ)) r.toNat else 0

/-- The **RHS_gen** Vandermonde collapse: the skew-transported block coefficient collapses (via
`vand_finsum`) to `fcoeff`.  Parametric copy of `lhs_coeff_eq` (`B`-shift in `cbz`, `A+B`-shift in
`gBinom`) without the global `(−1)^{p+q}`. -/
theorem rhsgen_coeff (p q ℓ m n : ℤ) (A B : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz (2 * q - ℓ - n - 2 - (B:ℤ)) (r - (j:ℤ)) * (- (-1:ℂ)^(ℓ + (r - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - (r - (j:ℤ))) j)
      = fcoeff p ℓ m A (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz (2 * q - ℓ - n - 2 - (B:ℤ)) ((r:ℤ) - (j:ℤ)) * (- (-1:ℂ)^(ℓ + ((r:ℤ) - (j:ℤ))))
        * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - ((r:ℤ) - (j:ℤ))) j
      = (- (-1:ℂ)^(ℓ + (r:ℤ))) *
          ((-1:ℂ)^j * cbz (2 * q - ℓ - n - 2 - (B:ℤ)) ((r:ℤ) - (j:ℤ))
            * gBinom ((2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (ℓ + ((r:ℤ) - (j:ℤ))) = (ℓ + (r:ℤ)) - (j:ℤ) from by ring, signSplit (ℓ + (r:ℤ)) j]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum (2 * q - ℓ - n - 2 - (B:ℤ)) (2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) r]
  rw [fcoeff, if_pos (by positivity), Int.toNat_natCast]
  rw [show (2*p+2*q-2*ℓ-m-n-4 - (A:ℤ) - (B:ℤ)) - (2 * q - ℓ - n - 2 - (B:ℤ))
        = 2 * p - ℓ - m - 2 - (A:ℤ) from by ring]
  rw [← negOne_zpow_natCast r]
  rw [show (- (-1:ℂ)^(ℓ + (r:ℤ))) * ((-1:ℂ)^(r:ℤ) * gBinom (2 * p - ℓ - m - 2 - (A:ℤ)) r)
      = (-((-1:ℂ)^(ℓ + (r:ℤ)) * (-1:ℂ)^(r:ℤ))) * gBinom (2 * p - ℓ - m - 2 - (A:ℤ)) r from by ring]
  congr 1
  rw [← negOne_zpow_add, negOne_neg_zpow]
  exact negOne_zpow_eq _ _ ⟨(r:ℤ), by ring⟩

/-- **RHS_gen block flatten.**  Each `(a,b)` block of the RHS (a v-first `Y_M` product, skewed to
u-first via `mode_skew_gbinom`, then antidiagonal-reindexed) equals `∑ᶠ r, fcoeff … • V a b r`. -/
theorem rhsgen_block (hφ : TransCov φ) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) (a b : ℕ) :
    (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        φ ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i)
          ((W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u))))
      = ∑ᶠ r : ℤ, fcoeff p ℓ m a r • Vtow φ u v p q ℓ m n a b r := by
  have hau : ((W.L 1 ^ a) u) ∈ W.grading (p - (a : ℤ)) := L_one_pow_mem W hu a
  have hbv : ((W.L 1 ^ b) v) ∈ W.grading (q - (b : ℤ)) := L_one_pow_mem W hv b
  set D : ℤ := 2 * p + 2 * q - 2 * ℓ - m - n - 4 with hD
  set V : ℤ → X := fun r => Vtow φ u v p q ℓ m n a b r with hVdef
  -- truncation of the u-first product mode in `r`
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero ((W.L 1 ^ a) u) ((W.L 1 ^ b) v)
  have hVzero : ∀ r : ℤ, (Ns - ℓ) ≤ r → V r = 0 := by
    intro r hr
    change Vtow φ u v p q ℓ m n a b r = 0
    rw [Vtow, show W.smul ((W.L 1 ^ a) u) (ℓ + r) ((W.L 1 ^ b) v) = 0 from hNs (ℓ + r) (by omega),
      map_zero]
  -- skew each summand to the u-first tower
  set g : ℤ → ℕ → ℂ := fun i j =>
    cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i * (- (-1:ℂ)^(ℓ+i))
      * gBinom (D - (a:ℤ) - (b:ℤ) - i) j with hg
  have hskew : (∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
        φ ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i)
          ((W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u))))
      = ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), g i j • V (i + (j : ℤ)) := by
    refine finsum_congr (fun i => ?_)
    rw [show (2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i
          = D - (a:ℤ) - (b:ℤ) - i from by rw [hD]; ring]
    rw [mode_skew_gbinom φ hφ ((W.L 1 ^ a) u) ((W.L 1 ^ b) v) (ℓ + i) (D - (a:ℤ) - (b:ℤ) - i)]
    rw [smul_finsum]
    refine finsum_congr (fun j : ℕ => ?_)
    rw [hg, hVdef]
    change cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
          ((- (-1:ℂ)^(ℓ+i)) * gBinom (D - (a:ℤ) - (b:ℤ) - i) j) •
            φ ((D - (a:ℤ) - (b:ℤ) - i) - (j:ℤ))
              ((W.smul ((W.L 1 ^ a) u) ((ℓ + i) + (j:ℤ)) ((W.L 1 ^ b) v)))
        = (cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i * (- (-1:ℂ)^(ℓ+i))
            * gBinom (D - (a:ℤ) - (b:ℤ) - i) j) •
            Vtow φ u v p q ℓ m n a b (i + (j:ℤ))
    rw [Vtow]
    rw [show (ℓ + (i + (j:ℤ))) = (ℓ + i) + (j:ℤ) from by ring,
        show (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (a:ℤ) - (b:ℤ) - (i + (j:ℤ))
          = (D - (a:ℤ) - (b:ℤ) - i) - (j:ℤ) from by rw [hD]; ring]
    rw [smul_smul]; ring_nf
  rw [hskew]
  obtain ⟨hfin, hfin2, hfinr⟩ := antidiag_finsT g V (Ns - ℓ)
    (fun i hi j => by rw [hg]; simp only []; rw [cbz_apply_neg _ hi]; ring) hVzero
  rw [antidiag_reindexT g V hfin hfin2 hfinr]
  refine finsum_congr (fun r => ?_)
  rcases lt_or_ge r 0 with hr | hr
  · rw [show (∑ᶠ j : ℕ, g (r - (j:ℤ)) j) = (∑ᶠ _j : ℕ, (0:ℂ)) from
        finsum_congr (fun j => by
          rw [hg]; simp only []
          rw [cbz_apply_neg (2 * q - ℓ - n - 2 - (b : ℤ)) (by omega : r - (j:ℤ) < 0)]; ring)]
    rw [finsum_zero, zero_smul, fcoeff, if_neg (by omega), zero_smul]
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    congr 1
    rw [← rhsgen_coeff p q ℓ m n a b rn]

/-! ## The RHS_smul flatten:  reorganizing `dualAdj`-of-product into the u-first tower. -/

/-- The `mode`-of-comultiplication of a single `L₁ᵗ(u₍s₎v)`, reindexed from the comul `(B',A')`
double sum to the u-power/v-power `(A,B)` block with `A = A'`, `B = t − B'`.  Uses the closed form
`K_closed`, so each summand is `(A!B!)⁻¹·gBinom (2p−s−2−A) (t−A−B)` times a u-first tower mode. -/
theorem mode_comul_block {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (v : 𝒱) (s : ℤ) (t : ℕ) (kk : ℤ) :
    φ kk ((((W.L 1) ^ t) (W.smul u s v)))
      = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1),
          ((t.factorial : ℂ) * ((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)
            * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B)) •
            φ kk ((W.smul (((W.L 1) ^ A) u) (s + ((t - A - B : ℕ) : ℤ)) (((W.L 1) ^ B) v))) := by
  -- push `mode (Y_M ·) kk xα` (the linear map `modeAtState`) through the comul double sum
  rw [show φ kk ((((W.L 1) ^ t) (W.smul u s v)))
        = φ kk (((W.L 1) ^ t) (W.smul u s v)) from rfl]
  rw [L1pow_smul_comul W hu v s t]
  -- reflect the outer comul sum `B' ↦ t - B'` (pure Finset identity inside the linear map)
  rw [show (∑ B' ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (B' + 1),
            ((t.choose B' : ℂ) * K p s B' A) •
              W.smul (((W.L 1) ^ A) u) (s + ((B' - A : ℕ) : ℤ)) (((W.L 1) ^ (t - B')) v))
          = ∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range ((t - B) + 1),
            ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
              W.smul (((W.L 1) ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) (((W.L 1) ^ B) v) from by
        rw [← Finset.sum_range_reflect
              (fun B => ∑ A ∈ Finset.range ((t - B) + 1),
                ((t.choose (t - B) : ℂ) * K p s (t - B) A) •
                  W.smul (((W.L 1) ^ A) u) (s + (((t - B) - A : ℕ) : ℤ)) (((W.L 1) ^ B) v)) (t + 1)]
        refine Finset.sum_congr rfl (fun B' hB' => ?_)
        rw [Finset.mem_range] at hB'
        rw [show (t + 1 - 1 - B') = t - B' from by omega,
            show (t - (t - B')) = B' from by omega]]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  rw [Finset.mem_range] at hB
  rw [map_sum]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hA
  rw [map_smul]
  rw [show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega]
  congr 1
  -- coefficient:  C(t, t-B) · K p s (t-B) A  =  (A!⁻¹ B!⁻¹) · gBinom (2p-s-2-A) (t-A-B)
  have hcomb : ((t.choose (t - B) : ℂ))
      = ((t.factorial : ℂ)) * (((t - B).factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹) := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show t - B ≤ t from by omega)
    rw [show t - (t - B) = B from by omega] at h2
    have h2' : ((t.choose (t - B) : ℂ)) * ((((t - B).factorial : ℂ)) * (B.factorial : ℂ))
        = (t.factorial : ℂ) := by push_cast [← h2]; ring
    have htBf : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
    have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
    field_simp
    linear_combination h2'
  rw [hcomb]
  have hKc := K_closed p s (t - B) A (by omega)
  have hAfac : ((A.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero A
  have htBfac : (((t - B).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - B)
  rw [show ((t - B) - A : ℕ) = (t - A - B : ℕ) from by omega] at hKc
  have hKval : K p s (t - B) A
      = (((t - B).factorial : ℂ)) * ((A.factorial : ℂ)⁻¹)
        * gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B) := by
    field_simp at hKc ⊢
    linear_combination hKc
  rw [hKval]
  set G : ℂ := gBinom (2 * p - s - 2 - (A : ℤ)) (t - A - B) with hG
  have hBf : ((B.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero B
  have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  field_simp

omit [Module ℂ X] in
/-- **ℕ-shift of a finsum**: if `H` vanishes below `c`, then `∑ᶠ t, H t = ∑ᶠ j, H (c + j)`. -/
theorem finsum_shift_nat (c : ℕ) (H : ℕ → X) (hH : ∀ t : ℕ, t < c → H t = 0) :
    (∑ᶠ t : ℕ, H t) = ∑ᶠ j : ℕ, H (c + j) := by
  have hsub : Function.support H ⊆ Set.range (fun j : ℕ => c + j) := by
    intro t ht
    rw [Function.mem_support] at ht
    have htc : c ≤ t := by by_contra hlt; exact ht (hH t (by omega))
    exact ⟨t - c, by dsimp only; omega⟩
  have hinj : Function.Injective (fun j : ℕ => c + j) := add_right_injective c
  rw [← finsum_mem_range hinj (f := H)]
  rw [← finsum_mem_inter_support H (Set.range (fun j : ℕ => c + j)),
    ← finsum_mem_univ (f := H), ← finsum_mem_inter_support H Set.univ, Set.univ_inter,
    Set.inter_eq_right.mpr hsub]

/-- The **RHS_smul** Vandermonde collapse: the comul-side block coefficient collapses (via
`vand_finsum`) to `(−1)^{p+q} · fcoeff`.  Parametric copy of `rhs_coeff_eq` (`A`-shift in the
`gBinom`). -/
theorem rhssmul_coeff (p q ℓ m : ℤ) (A : ℕ) (r : ℕ) :
    (∑ᶠ j : ℕ, cbz m (r - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+(r - (j:ℤ)))-1) * gBinom (2*p-(ℓ+(r - (j:ℤ)))-2-(A:ℤ)) j))
      = (-1:ℂ)^(p+q) * fcoeff p ℓ m A (r:ℤ) := by
  have hcongr : ∀ j : ℕ,
      cbz m ((r:ℤ) - (j:ℤ))
        * ((-1:ℂ)^(p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) * gBinom (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2-(A:ℤ)) j)
      = (-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) *
          ((-1:ℂ)^j * cbz m ((r:ℤ) - (j:ℤ)) * gBinom ((2*p-ℓ-2-(A:ℤ)) - ((r:ℤ) - (j:ℤ))) j) := by
    intro j
    rw [show (p+q-(ℓ+((r:ℤ) - (j:ℤ)))-1) = (p+q-ℓ-(r:ℤ)-1) + (j:ℤ) from by ring,
        negOne_zpow_add, negOne_zpow_natCast,
        show (2*p-(ℓ+((r:ℤ) - (j:ℤ)))-2-(A:ℤ)) = (2*p-ℓ-2-(A:ℤ)) - ((r:ℤ) - (j:ℤ)) from by ring]
    ring
  rw [finsum_congr hcongr, ← mul_finsum]
  rw [vand_finsum m (2*p-ℓ-2-(A:ℤ)) r]
  rw [fcoeff, if_pos (by positivity), Int.toNat_natCast]
  rw [show (2*p-ℓ-2-(A:ℤ)) - m = 2*p-ℓ-m-2-(A:ℤ) from by ring]
  rw [← negOne_zpow_natCast r,
      show ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * ((-1:ℂ)^(r:ℤ) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r))
      = ((-1:ℂ)^(p+q-ℓ-(r:ℤ)-1) * (-1:ℂ)^(r:ℤ)) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r from by ring]
  rw [show (-1:ℂ)^(p+q) * ((-1:ℂ)^(ℓ+1) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r)
        = ((-1:ℂ)^(p+q) * (-1:ℂ)^(ℓ+1)) * gBinom (2*p-ℓ-m-2-(A:ℤ)) r from by ring]
  congr 1
  rw [← negOne_zpow_add, ← negOne_zpow_add]
  exact negOne_zpow_eq _ _ ⟨-ℓ - 1, by ring⟩

/-- The comul tower coefficient `cbz m i · (−1)^{P_i} · (A!B!)⁻¹ · gBinom (2p−(ℓ+i)−2−A) j`. -/
noncomputable def gtow (p q ℓ m : ℤ) (A B : ℕ) (i : ℤ) (j : ℕ) : ℂ :=
  cbz m i * (-1:ℂ) ^ (p + q - (ℓ + i) - 1) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))
    * gBinom (2 * p - (ℓ + i) - 2 - (A : ℤ)) j

/-- `Vtow A B r = 0` once `A > p` (then `L₁ᵃu = 0`). -/
theorem Vtow_zero_left {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (v : 𝒱) (q ℓ m n : ℤ) {A : ℕ} (hA : p - (A : ℤ) < 0) (B : ℕ) (r : ℤ) :
    Vtow φ u v p q ℓ m n A B r = 0 := by
  rw [Vtow, L_one_pow_eq_zero W hu hA, W.smul_zero_left, map_zero]

/-- `Vtow A B r = 0` once `B > q` (then `L₁ᵇv = 0`). -/
theorem Vtow_zero_right {p : ℤ} (u : 𝒱) {q : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading q) (ℓ m n : ℤ) (A : ℕ) {B : ℕ} (hB : q - (B : ℤ) < 0) (r : ℤ) :
    Vtow φ u v p q ℓ m n A B r = 0 := by
  rw [Vtow, L_one_pow_eq_zero W hv hB, W.smul_zero_right, map_zero]

omit [Module ℂ X] in
/-- **Triangle → box (with indicator).**  For a summand `G` vanishing whenever `A > P` or `B > Q`,
the comul triangle sum `∑_{B≤t} ∑_{A≤t−B}` equals the fixed box `∑_{B≤Q} ∑_{A≤P}` with an
`[A+B≤t]` indicator. -/
theorem tri_to_box {G : ℕ → ℕ → X} (P Q t : ℕ)
    (hG : ∀ A B, (P < A ∨ Q < B) → G A B = 0) :
    (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range (Q + 1), ∑ A ∈ Finset.range (P + 1),
          (if A + B ≤ t then G A B else 0) := by
  classical
  set R : ℕ := t + Q + P + 1 with hR
  set H : ℕ → ℕ → X := fun B A => if A + B ≤ t ∧ A ≤ P ∧ B ≤ Q then G A B else 0 with hH
  -- inner identity: per B, the LHS triangle row and the RHS box row both equal the
  -- big common row `∑_{A∈range(R+1)} H B A`
  have hrow : ∀ B : ℕ, (∑ A ∈ Finset.range (R + 1), H B A)
      = if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0 := by
    intro B
    by_cases hBt : B ≤ t
    · rw [if_pos hBt]
      have hsub : (∑ A ∈ Finset.range (t - B + 1), H B A)
          = ∑ A ∈ Finset.range (R + 1), H B A :=
        Finset.sum_subset (Finset.range_subset_range.mpr (by omega : t - B + 1 ≤ R + 1))
          (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hH]; rw [if_neg (by omega)])
      rw [← hsub]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hH]
      rcases Nat.lt_or_ge P A with hAP | hAP
      · rw [if_neg (by omega), hG A B (Or.inl hAP)]
      · rcases Nat.lt_or_ge Q B with hBQ | hBQ
        · rw [if_neg (by omega), hG A B (Or.inr hBQ)]
        · rw [if_pos ⟨by omega, hAP, hBQ⟩]
    · rw [if_neg hBt]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hH]; rw [if_neg (by omega)]
  have hrow2 : ∀ B : ℕ, (∑ A ∈ Finset.range (R + 1), H B A)
      = if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0 := by
    intro B
    by_cases hBQ : B ≤ Q
    · rw [if_pos hBQ]
      have hsub : (∑ A ∈ Finset.range (P + 1), H B A)
          = ∑ A ∈ Finset.range (R + 1), H B A :=
        Finset.sum_subset (Finset.range_subset_range.mpr (by omega : P + 1 ≤ R + 1))
          (fun A _ hA => by rw [Finset.mem_range] at hA; simp only [hH]; rw [if_neg (by omega)])
      rw [← hsub]
      refine Finset.sum_congr rfl (fun A hA => ?_)
      rw [Finset.mem_range] at hA; simp only [hH]
      by_cases hc : A + B ≤ t
      · rw [if_pos hc, if_pos ⟨hc, by omega, hBQ⟩]
      · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hBQ]
      refine Finset.sum_eq_zero (fun A _ => ?_)
      simp only [hH]; rw [if_neg (by omega)]
  -- now sum the rows over `range(R+1)` and compare via the `if`-truncations
  have hbig : (∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A)
      = ∑ B ∈ Finset.range (R + 1),
          (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0) :=
    Finset.sum_congr rfl (fun B _ => hrow B)
  have hbig2 : (∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A)
      = ∑ B ∈ Finset.range (R + 1),
          (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0) :=
    Finset.sum_congr rfl (fun B _ => hrow2 B)
  have hLHS : (∑ B ∈ Finset.range (t + 1), ∑ A ∈ Finset.range (t - B + 1), G A B)
      = ∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A := by
    rw [hbig]
    have hsb : (∑ B ∈ Finset.range (t + 1),
              (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0))
        = ∑ B ∈ Finset.range (R + 1),
              (if B ≤ t then (∑ A ∈ Finset.range (t - B + 1), G A B) else 0) :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega : t + 1 ≤ R + 1))
        (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])
    rw [← hsb]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos (by omega)]
  have hRHS : (∑ B ∈ Finset.range (Q + 1), ∑ A ∈ Finset.range (P + 1),
          (if A + B ≤ t then G A B else 0))
      = ∑ B ∈ Finset.range (R + 1), ∑ A ∈ Finset.range (R + 1), H B A := by
    rw [hbig2]
    have hsb : (∑ B ∈ Finset.range (Q + 1),
              (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0)) else 0))
        = ∑ B ∈ Finset.range (R + 1),
              (if B ≤ Q then (∑ A ∈ Finset.range (P + 1), (if A + B ≤ t then G A B else 0))
                else 0) :=
      Finset.sum_subset (Finset.range_subset_range.mpr (by omega : Q + 1 ≤ R + 1))
        (fun B _ hB => by simp only [Finset.mem_range, not_lt] at hB; rw [if_neg (by omega)])
    rw [← hsb]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB; rw [if_pos (by omega)]
  rw [hLHS, hRHS]

/-- **Per-`i` expansion of `cbz m i • dualAdj`** into the fixed `(A,B)`-Finset u-first tower, with a
`∑ᶠ`-depth `j`. -/
theorem dualAdj_block_i {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) (i : ℤ) :
    cbz m i • adj φ (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i)
      = ∑ B ∈ Finset.range (q.toNat + 1), ∑ A ∈ Finset.range (p.toNat + 1),
          ∑ᶠ j : ℕ, gtow p q ℓ m A B i j • Vtow φ u v p q ℓ m n A B (i + (j : ℤ)) := by
  set P : ℤ := p + q - (ℓ + i) - 1 with hP
  have hsmem : W.smul u (ℓ + i) v ∈ W.grading P := W.smul_mem_grading hu hv (ℓ + i)
  -- `Vtow` vanishing data for `tri_to_box`
  have hGzero : ∀ (A B : ℕ) (j : ℕ),
      (p.toNat < A ∨ q.toNat < B) →
      gtow p q ℓ m A B i j • Vtow φ u v p q ℓ m n A B (i + (j : ℤ)) = 0 := by
    rintro A B j (hA | hB)
    · rw [Vtow_zero_left φ hu v q ℓ m n (by omega) B, smul_zero]
    · rw [Vtow_zero_right φ u hv ℓ m n A (by omega), smul_zero]
  -- per-`t` expansion: `cbz m i • (-1)^P • dterm t` = box-with-indicator over (A,B)
  have hterm : ∀ t : ℕ,
      cbz m i • ((-1:ℂ) ^ P • dterm φ P (W.smul u (ℓ + i) v) (m + n - i) t)
        = ∑ B ∈ Finset.range (q.toNat + 1), ∑ A ∈ Finset.range (p.toNat + 1),
            (if A + B ≤ t then
              gtow p q ℓ m A B i (t - A - B) • Vtow φ u v p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ))
             else 0) := by
    intro t
    rw [dterm, mode_comul_block φ hu v (ℓ + i) t (2 * P - (m + n - i) - 2 - (t:ℤ))]
    rw [← tri_to_box p.toNat q.toNat t (G := fun A B =>
          gtow p q ℓ m A B i (t - A - B) • Vtow φ u v p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ)))
        (fun A B h => hGzero A B (t - A - B) h)]
    -- combine the three outer scalars and push into the comul double sum
    rw [smul_smul, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun B hB => ?_)
    rw [Finset.mem_range] at hB
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hA
    have hAB : A + B ≤ t := by omega
    have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
    -- scalars:  (cbz·(-1)^P·(t!)⁻¹) • ((t!·A!⁻¹B!⁻¹·gBinom) • mode) = (gtow) • Vtow
    rw [smul_smul]
    rw [gtow, Vtow]
    have hstate : (ℓ + i) + ((t - A - B : ℕ) : ℤ) = ℓ + (i + ((t - A - B : ℕ) : ℤ)) := by ring
    have hmode : (2 * P - (m + n - i) - 2 - (t:ℤ))
        = (2 * p + 2 * q - 2 * ℓ - m - n - 4) - (A:ℤ) - (B:ℤ) - (i + ((t - A - B : ℕ) : ℤ)) := by
      rw [hP, htAB]; ring
    rw [hstate, hmode]
    congr 1
    -- coefficient identity (t! cancels)
    have htf : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    rw [hP]
    field_simp
  -- assemble: extend dualAdj to ∑ᶠ t, plug `hterm`, swap finite (A,B) sums out, shift t→j
  rw [adj_finsum φ hsmem (m + n - i), smul_finsum, smul_finsum]
  rw [finsum_congr hterm]
  -- finiteness of each per-(A,B) `∑ᶠ t` summand (the indexed `if`-term)
  have hfinAB : ∀ A B : ℕ, Function.HasFiniteSupport (fun t : ℕ =>
      (if A + B ≤ t then
        gtow p q ℓ m A B i (t - A - B) • Vtow φ u v p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ))
       else 0)) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    change (Function.support _).Finite
    apply Set.Finite.subset (Set.finite_Icc 0 ((Ns - ℓ - i + (A:ℤ) + (B:ℤ)).toNat))
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hge
    apply ht
    by_cases hc : A + B ≤ t
    · have htAB : ((t - A - B : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) - (B : ℤ) := by omega
      have hVz : Vtow φ u v p q ℓ m n A B (i + ((t - A - B : ℕ) : ℤ)) = 0 := by
        rw [Vtow,
          show W.smul (((W.L 1) ^ A) u) (ℓ + (i + ((t - A - B : ℕ) : ℤ))) (((W.L 1) ^ B) v) = 0 from
            hNs _ (by rw [htAB]; omega), map_zero]
      rw [if_pos hc, hVz, smul_zero]
    · rw [if_neg hc]
  -- swap the finite (B,A) sums out of `∑ᶠ t`
  rw [finsum_sum_comm (Finset.range (q.toNat + 1)) _ (fun B _ => by
    apply hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1))
    intro A _; exact hfinAB A B)]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [finsum_sum_comm (Finset.range (p.toNat + 1)) _ (fun A _ => hfinAB A B)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  -- per (A,B): shift `t = A + B + j`
  rw [finsum_shift_nat (A + B) _ (fun t htlt => by rw [if_neg (by omega)])]
  refine finsum_congr (fun j => ?_)
  rw [if_pos (by omega)]
  congr 2
  · show ((A + B + j) - A - B : ℕ) = j; omega
  · show i + (((A + B + j) - A - B : ℕ) : ℤ) = i + (j : ℤ)
    congr 1; show (((A + B + j) - A - B : ℕ) : ℤ) = (j : ℤ); congr 1; omega

/-! ## The general module FHL Borcherds RHS reduction. -/

theorem rhs_gen_eqT (hφ : TransCov φ) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) :
    (∑ᶠ i : ℤ, cbz m i •
        adj φ (p + q - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i))
      = (-1 : ℂ) ^ (p + q) •
          ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
            (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
              ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
                φ ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i)
                  ((W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u))) := by
  -- RHS: flatten each block to the u-first tower via `rhsgen_block`, then push the
  -- global `(-1)^{p+q}` into the `(a,b)` double sum, fusing it with `(a!b!)⁻¹`.
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by
    rw [rhsgen_block φ hφ hu hv ℓ m n a b]))]
  simp only [Finset.smul_sum, smul_smul]
  -- LHS: per-`i` expansion, then swap the finite (B,A) sums out of `∑ᶠ i`
  rw [finsum_congr (fun i => dualAdj_block_i φ hu hv ℓ m n i)]
  -- finiteness of the per-(A,B) `∑ᶠ i ∑ᶠ j` summand and the inner `∑ᶠ j`
  have hgfin : ∀ A B : ℕ,
      (Function.support (fun pr : ℤ × ℕ => gtow p q ℓ m A B pr.1 pr.2 •
        Vtow φ u v p q ℓ m n A B (pr.1 + (pr.2 : ℤ)))).Finite
      ∧ (Function.support (fun pr : ℤ × ℕ => gtow p q ℓ m A B (pr.1 - (pr.2 : ℤ)) pr.2 •
          Vtow φ u v p q ℓ m n A B pr.1)).Finite
      ∧ (∀ r : ℤ, (Function.support (fun j : ℕ => gtow p q ℓ m A B (r - (j : ℤ)) j)).Finite) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    refine antidiag_finsT (fun i j => gtow p q ℓ m A B i j) (fun r => Vtow φ u v p q ℓ m n A B r)
      (Ns - ℓ) (fun i hi j => by simp only [gtow]; rw [cbz_apply_neg _ hi]; ring) (fun r hr => ?_)
    change Vtow φ u v p q ℓ m n A B r = 0
    rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v) = 0 from hNs _ (by omega),
      map_zero]
  -- i-support of `fun i => ∑ᶠ j, gtow•Vtow(i+j)` is finite
  have hifin : ∀ A B : ℕ, Function.HasFiniteSupport (fun i : ℤ =>
      ∑ᶠ j : ℕ, gtow p q ℓ m A B i j • Vtow φ u v p q ℓ m n A B (i + (j : ℤ))) := by
    intro A B
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    change (Function.support _).Finite
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      simp only [gtow]; rw [cbz_apply_neg _ h]; simp
    · refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
      have hVz : Vtow φ u v p q ℓ m n A B (i + (j:ℤ)) = 0 := by
        rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + (i + (j:ℤ))) (((W.L 1) ^ B) v) = 0 from
          hNs _ (by omega), map_zero]
      rw [hVz, smul_zero]
  rw [finsum_sum_comm (Finset.range (q.toNat + 1)) _ (fun B _ =>
    hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1)) _ (fun A _ => hifin A B))]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [finsum_sum_comm (Finset.range (p.toNat + 1)) _ (fun A _ => hifin A B)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  -- per (A,B): antidiagonal-reindex then collapse the per-`r` coefficient
  obtain ⟨hfin, hfin2, hfinr⟩ := hgfin A B
  rw [antidiag_reindexT (fun i j => gtow p q ℓ m A B i j) (fun r => Vtow φ u v p q ℓ m n A B r)
        hfin hfin2 hfinr]
  -- finiteness of `r ↦ fcoeff • Vtow`
  have hffin : (Function.support (fun r : ℤ =>
      fcoeff p ℓ m A r • Vtow φ u v p q ℓ m n A B r)).Finite := by
    obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero (((W.L 1) ^ A) u) (((W.L 1) ^ B) v)
    apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
    intro r hr
    rw [Function.mem_support] at hr; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hr ?_, not_lt.mp fun h => hr ?_⟩
    · rw [fcoeff, if_neg (by omega), zero_smul]
    · have hVz : Vtow φ u v p q ℓ m n A B r = 0 := by
        rw [Vtow, show W.smul (((W.L 1) ^ A) u) (ℓ + r) (((W.L 1) ^ B) v) = 0 from hNs _ (by omega),
          map_zero]
      rw [hVz, smul_zero]
  -- pull the constant into the RHS finsum
  rw [smul_finsum' ((-1:ℂ) ^ (p + q) * (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹))) hffin]
  -- match per `r`
  refine finsum_congr (fun r => ?_)
  rw [smul_smul]
  congr 1
  rcases lt_or_ge r 0 with hr | hr
  · rw [fcoeff, if_neg (by omega), mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero (fun j => ?_)
    rw [gtow, cbz_apply_neg _ (by omega : r - (j:ℤ) < 0)]; ring
  · obtain ⟨rn, rfl⟩ : ∃ rn : ℕ, r = (rn : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr).symm⟩
    -- `∑ᶠ j gtow(rn-j) j = (-1)^{p+q} (A!⁻¹B!⁻¹) fcoeff` (via rhssmul_coeff)
    have hpull : (∑ᶠ j : ℕ, gtow p q ℓ m A B ((rn:ℤ) - (j:ℤ)) j)
        = (((A.factorial : ℂ)⁻¹) * ((B.factorial : ℂ)⁻¹)) *
            (∑ᶠ j : ℕ, cbz m ((rn:ℤ) - (j:ℤ))
              * ((-1:ℂ)^(p+q-(ℓ+((rn:ℤ) - (j:ℤ)))-1)
                * gBinom (2*p-(ℓ+((rn:ℤ) - (j:ℤ)))-2-(A:ℤ)) j)) := by
      rw [mul_finsum]
      refine finsum_congr (fun j => ?_)
      rw [gtow]; ring
    rw [hpull, rhssmul_coeff p q ℓ m A rn]
    ring


end Twist

end VOA.Huang.PzTensorTwist
