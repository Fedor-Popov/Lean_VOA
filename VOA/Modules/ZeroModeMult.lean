/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuAlgebra
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Zhu 5.3.9a — zero-mode multiplicativity on a lowest-weight space  (Gannon §5.3.2)

The companion to the zero-mode descent 5.3.9b (`ZhuAlgebra.oMod_L_translation`): the module
zero mode `o(·)` (`Character.oMod`) is **multiplicative** on a lowest-weight space. For
homogeneous `u ∈ 𝒱ₐ`, `v ∈ 𝒱ᵦ` (`a, β ≥ 0`) and `x` in the lowest-weight space `M_h`
(`IsLowestWeight N h`, Gannon's clause that every nonzero weight lies in `h + ℕ`):

  `o(u * v) x = o(u) (o(v) x)`   (`oMod_zhuMul_lowest`, Gannon 5.3.9a).

Together with the descent of `*` to `A(𝒱)` and 5.3.9b, this is what makes `M ↦ M_h` send a
`𝒱`-module to an `A(𝒱)`-module (Theorem 5.3.4(c), the easy direction).

The proof: a module `L₀`-commutator `[L₀, v₍ₙ₎] = (β−n−1) v₍ₙ₎` from the module Jacobi
(`L0_commutator`) ⟹ the weight shift `v₍ₙ₎ : M_α → M_{α+β−n−1}` (`mode_mem_weight`) and the
vanishing of lowering modes on `M_h` (`mode_lowering_vanish`); the module iterate
(`Translation.module_iterate0`) collapses `o(u*v)` on `M_h` to a finite sum whose leading term
is `o(u)∘o(v)` (`S1_collapse`) and whose remainder vanishes by the alternating binomial identity
`∑_{m=0}^{a} (−1)^m C(a,m) C(m−1,i) = 0` for `i < a` (`alt_shiftBinom_vanish`, via Mathlib's
`fwdDiff` finite-difference calculus) (`S2_vanish`).

## Status
`sorry`-free, with no project axioms. **`oMod_zhuMul_lowest`** (5.3.9a) and its
supporting tower are all `[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.2, eq. (5.3.9a); Zhu [574]; Frenkel–Zhu.
-/

/-!
# Zhu 5.3.9a — module zero-mode multiplicativity on the lowest-weight space

Headline: for homogeneous `u ∈ 𝒱ₐ`, `v ∈ 𝒱ᵦ` and `x` in the lowest weight space `M_h`,
`oMod N (zhuMul W u v) x = oMod N u (oMod N v x)`.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {M : Type u} [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra 𝒱}

/-! ## The `L₀`-commutator on a module -/

/-- The boundary (`ℓ = 0`, `m = 1`) module Jacobi commutator with `u = ω`:
`[ω₍₁₎, v₍ₙ₎] x = (ω₍₀₎v)₍₁₊ₙ₎ x + (ω₍₁₎v)₍ₙ₎ x`. -/
theorem L0_commutator_raw (A : WeakModule W M) (v : 𝒱) (x : M) (n : ℤ) :
    mode (A.YM W.conformalVector) 1 (mode (A.YM v) n x)
      - mode (A.YM v) n (mode (A.YM W.conformalVector) 1 x)
      = mode (A.YM (W.smul W.conformalVector 0 v)) (1 + n) x
        + mode (A.YM (W.smul W.conformalVector 1 v)) n x := by
  have hjac := A.jacobi W.conformalVector v x 0 1 n
  -- LHS collapses: cbz 0 i = δ_{i,0}, negOnePow 0 = 1.
  have hlhs : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (A.YM W.conformalVector) (0 + 1 - i) (mode (A.YM v) (n + i) x)
          - negOnePow 0 • mode (A.YM v) (0 + n - i) (mode (A.YM W.conformalVector) (1 + i) x)))
      = mode (A.YM W.conformalVector) 1 (mode (A.YM v) n x)
        - mode (A.YM v) n (mode (A.YM W.conformalVector) 1 x) := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [cbz_zero_left, mul_one, add_zero, zero_add, sub_zero,
      negOnePow, Even.zero, if_true, one_smul]
  -- RHS collapses: cbz 1 i = δ_{i,0}+δ_{i,1}.
  have hcbz1 : ∀ i : ℤ, i ≠ 0 → i ≠ 1 →
      cbz 1 i • mode (A.YM (W.smul W.conformalVector (0 + i) v)) (1 + n - i) x = 0 := by
    intro i hi0 hi1
    rcases lt_trichotomy i 0 with h | h | h
    · rw [cbz_apply_neg 1 h, zero_smul]
    · exact absurd h hi0
    · rw [cbz_lt (by norm_num) (by omega : (1 : ℤ) < i), zero_smul]
  have hrhs : (∑ᶠ i : ℤ, cbz 1 i • mode (A.YM (W.smul W.conformalVector (0 + i) v)) (1 + n - i) x)
      = mode (A.YM (W.smul W.conformalVector 0 v)) (1 + n) x
        + mode (A.YM (W.smul W.conformalVector 1 v)) n x := by
    rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ)) (by
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      by_contra hc
      push_neg at hc
      exact hi (hcbz1 i hc.1 hc.2))]
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    have hc10 : cbz (1 : ℤ) 0 = 1 := cbz_zero 1
    have hc11 : cbz (1 : ℤ) 1 = 1 := by
      rw [cbz_pascal 1 1, show (1 : ℤ) - 1 = 0 by ring, cbz_zero, cbz_lt (le_refl 0) (by norm_num)]
      ring
    rw [hc10, hc11, one_smul, one_smul,
      show (0 + (0 : ℤ)) = 0 by ring, show (0 + (1 : ℤ)) = 1 by ring,
      show (1 + n - (0 : ℤ)) = 1 + n by ring, show (1 + n - (1 : ℤ)) = n by ring]
  rw [hlhs, hrhs] at hjac
  exact hjac

/-! ## `L₀` acts diagonally; eigenvector membership -/

/-- **Eigenvector ⟹ membership.** If `L₀ y = γ • y` then `y ∈ M_γ`. (`L₀` is diagonal w.r.t.
the weight decomposition, so a `γ`-eigenvector has no off-`γ` components.) -/
theorem eigenvector_mem_weight (N : OrdVModule W M) {γ : ℂ} {y : M}
    (hy : mode (N.YM W.conformalVector) 1 y = γ • y) : y ∈ N.weight γ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  set c : ℂ → M := fun j => ((DirectSum.decompose N.weight y j : N.weight j) : M) with hc
  set s : Finset ℂ := (DirectSum.decompose N.weight y).support with hs
  -- `y = ∑_{j ∈ s} c j` (decomposition into weight components).
  have hdecomp : (∑ j ∈ s, c j) = y := DirectSum.sum_support_decompose N.weight y
  -- `L₀` acts as `j` on the `j`-component.
  have hL0comp : ∀ j : ℂ, mode (N.YM W.conformalVector) 1 (c j) = j • c j := fun j =>
    N.L0_weight j _ (DirectSum.decompose N.weight y j).2
  -- `∑_{j ∈ s} (j - γ) • c j = 0`.
  have hzero : (∑ j ∈ s, ((j - γ) • c j)) = 0 := by
    have hLHS : (∑ j ∈ s, ((j - γ) • c j))
        = mode (N.YM W.conformalVector) 1 y - γ • y := by
      rw [← hdecomp, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hL0comp j, sub_smul]
    rw [hLHS, hy, sub_self]
  -- Each `(j - γ) • c j ∈ weight j`. Apply `decompose` and read component `γ`.
  have hmem : ∀ j : ℂ, ((j - γ) • c j) ∈ N.weight j := fun j =>
    (N.weight j).smul_mem _ (DirectSum.decompose N.weight y j).2
  -- For `j ≠ γ`, the `j`-component vanishes, forcing `c j = 0`.
  have hcvanish : ∀ j ∈ s, j ≠ γ → c j = 0 := by
    intro j hjs hjγ
    -- Apply `decompose` to `hzero`, then read slot `j` (as `M`-elements).
    have hdz : (DirectSum.decompose N.weight (∑ k ∈ s, ((k - γ) • c k)) j : N.weight j)
        = (0 : N.weight j) := by
      rw [hzero, DirectSum.decompose_zero, DirectSum.zero_apply]
    have hcomp : ((DirectSum.decompose N.weight (∑ k ∈ s, ((k - γ) • c k)) j : N.weight j) : M)
        = (0 : M) := by rw [hdz, ZeroMemClass.coe_zero]
    rw [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finset_sum,
      Finset.sum_eq_single j (fun k hks hkj => ?_) (fun hjns => ?_)] at hcomp
    · -- diagonal term: ((j-γ)•c j) at slot j is itself.
      rw [DirectSum.decompose_of_mem_same N.weight (hmem j)] at hcomp
      have hne : (j - γ) ≠ 0 := sub_ne_zero.mpr hjγ
      exact (smul_eq_zero.mp hcomp).resolve_left hne
    · have := DirectSum.decompose_of_mem_ne N.weight (hmem k) hkj
      rw [this]
    · exact absurd hjs hjns
  -- Therefore `y = c γ ∈ weight γ`.
  have hyeq : y = c γ := by
    rw [← hdecomp]
    by_cases hγs : γ ∈ s
    · rw [Finset.sum_eq_single γ (fun k hks hkγ => hcvanish k hks hkγ) (fun h => absurd hγs h)]
    · -- if γ ∉ s, all components vanish, and `c γ = 0` too.
      have hcγ0 : c γ = 0 := by
        rw [hc]
        simp only
        have : DirectSum.decompose N.weight y γ = 0 := by
          rw [← DFinsupp.notMem_support_iff]; exact hγs
        rw [this, ZeroMemClass.coe_zero]
      rw [hcγ0, Finset.sum_eq_zero (fun k hks => hcvanish k hks (fun h => hγs (h ▸ hks)))]
  rw [hyeq, hc]
  exact (DirectSum.decompose N.weight y γ).2

/-! ## The `L₀`-commutator on homogeneous `v`, and the weight shift -/

/-- For homogeneous `v ∈ 𝒱ᵦ`, `[L₀, v₍ₙ₎] x = (β − n − 1)·v₍ₙ₎ x`. -/
theorem L0_commutator (N : OrdVModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    (x : M) (n : ℤ) :
    mode (N.YM W.conformalVector) 1 (mode (N.YM v) n x)
      = ((β : ℂ) - n - 1) • mode (N.YM v) n x + mode (N.YM v) n (mode (N.YM W.conformalVector) 1 x) := by
  have hraw := L0_commutator_raw N.toWeakModule v x n
  -- `ω₍₀₎v = L₋₁ v`, `ω₍₁₎v = L₀ v = β v`.
  have h0 : W.smul W.conformalVector 0 v = W.L (-1) v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((-1 : ℤ) + 1) = 0 from by ring]
  have h1 : W.smul W.conformalVector 1 v = W.L 0 v := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((0 : ℤ) + 1) = 1 from by ring]
  rw [h0, h1, W.L_zero_grading v hv] at hraw
  -- `(L₋₁v)₍₁₊ₙ₎ x = −(1+n)·v₍ₙ₎ x`.
  have hcov := act_T_covariance N.toWeakModule v (1 + n) x
  simp only [WeakModule.act_def, show (1 + n - 1 : ℤ) = n from by ring] at hcov
  -- `(β • v)₍ₙ₎ x = β • v₍ₙ₎ x`.
  have hlin : mode (N.YM ((β : ℂ) • v)) n x = (β : ℂ) • mode (N.YM v) n x := by
    rw [map_smul, mode_smul]; rfl
  rw [hcov, hlin] at hraw
  -- Now `hraw : L₀ (v₍ₙ₎ x) - v₍ₙ₎ (L₀ x) = -(1+n)•v₍ₙ₎ x + β•v₍ₙ₎ x`.
  rw [sub_eq_iff_eq_add] at hraw
  rw [hraw]
  have hscal : (-((1 + n : ℤ) : ℂ)) • mode (N.YM v) n x + (β : ℂ) • mode (N.YM v) n x
      = ((β : ℂ) - n - 1) • mode (N.YM v) n x := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [hscal]

/-- **Module weight shift.** For homogeneous `v ∈ 𝒱ᵦ` and `x ∈ M_α`,
`v₍ₙ₎ x ∈ M_{α+β−n−1}`. -/
theorem mode_mem_weight (N : OrdVModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) (n : ℤ) :
    mode (N.YM v) n x ∈ N.weight (α + (β : ℂ) - n - 1) := by
  apply eigenvector_mem_weight N
  rw [L0_commutator N hv x n, N.L0_weight α x hx, map_smul, ← add_smul]
  congr 1
  ring

/-! ## Vanishing of lowering modes on the lowest-weight space -/

/-- **Lowest weight `h`** (Gannon's `HasConformalWeight`, stated universe-polymorphically):
every nonzero weight space lies at `h + ℕ`, so `h` is the minimal weight. -/
def IsLowestWeight (N : OrdVModule W M) (h : ℂ) : Prop :=
  ∀ α : ℂ, N.weight α ≠ ⊥ → ∃ n : ℕ, α = h + n

/-- **Lowering modes annihilate `M_h`.** For `x` in the lowest-weight space `M_h` (with
`IsLowestWeight N h`) and homogeneous `v ∈ 𝒱ᵦ`, `v₍ₙ₎ x = 0` whenever `n ≥ β` (the mode
would push the weight strictly below the lowest weight `h`). -/
theorem mode_lowering_vanish (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) {x : M} (hx : x ∈ N.weight h) {n : ℤ}
    (hn : β ≤ n) : mode (N.YM v) n x = 0 := by
  have hmem := mode_mem_weight N hv hx n
  -- The target weight `h + β - n - 1` is below `h`, hence not of the form `h + k`, k : ℕ.
  have hbot : N.weight (h + (β : ℂ) - n - 1) = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := hcw _ hne
    -- `h + β - n - 1 = h + k` forces `β - n - 1 = k ≥ 0`, contradicting `n ≥ β`.
    have hkeq : ((β : ℂ) - n - 1) = (k : ℂ) := by
      have : h + ((β : ℂ) - n - 1) = h + (k : ℂ) := by rw [← hk]; ring
      exact add_left_cancel this
    have : (β : ℤ) - n - 1 = (k : ℤ) := by exact_mod_cast hkeq
    omega
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- The zero mode `o(v)` preserves the lowest-weight space: for `x ∈ M_h`, `o(v) x ∈ M_h`. -/
theorem oMod_preserves_lowest (N : OrdVModule W M) {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β)
    {h : ℂ} {x : M} (hx : x ∈ N.weight h) : oMod N v x ∈ N.weight h := by
  have he : oMod N v x = mode (N.YM v) (β - 1) x := by rw [oMod_homogeneous N hv]
  rw [he]
  have := mode_mem_weight N hv hx (β - 1)
  rwa [show h + (β : ℂ) - ((β - 1 : ℤ) : ℂ) - 1 = h from by push_cast; ring] at this

/-! ## Unfolding `o(u*v)` on homogeneous `u` -/

/-- For homogeneous `u ∈ 𝒱ₐ`, the Zhu product `u * v` is the single grade-`a` slice
`∑_{m=0}^{a} C(a,m)·u₍ₘ₋₁₎v`. -/
theorem zhuMul_homogeneous (W : VertexOperatorAlgebra 𝒱) {a : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading a) (v : 𝒱) :
    zhuMul W u v = ∑ m ∈ Finset.range (a.toNat + 1), cbz a m • W.smul u ((m : ℤ) - 1) v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : zhuMul W u v = zhuFamily W v a ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (zhuFamily W v)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (zhuFamily W v) a ⟨u, hu⟩
  rw [hcollapse]; rfl

/-! ## The alternating binomial identity (the `S₂ = 0` core)

`∑_{m=0}^{a} (−1)^m C(a,m) C(m−1,i) = 0` for `0 ≤ i < a`: the `a`-th finite difference of the
degree-`i` polynomial `m ↦ C(m−1,i)` vanishes when `i < a`. Realized via Mathlib's
`fwdDiff` calculus. -/

open Polynomial in
/-- The degree-`i` polynomial `P_i(X) = (i!)⁻¹·∏_{j<i}(X − 1 − j)` over `ℂ` with
`P_i(m) = C(m−1,i)` (`= cbz (m−1) i`). -/
noncomputable def shiftBinomPoly (i : ℕ) : ℂ[X] :=
  Polynomial.C ((i.factorial : ℂ)⁻¹) * ∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (1 + (j : ℂ)))

open Polynomial in
theorem shiftBinomPoly_natDegree_le (i : ℕ) : (shiftBinomPoly i).natDegree ≤ i := by
  have hstep : (∏ j ∈ Finset.range i,
      (Polynomial.X - Polynomial.C (1 + (j : ℂ)))).natDegree ≤ i := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hle : ∀ j ∈ Finset.range i,
        (Polynomial.X - Polynomial.C (1 + (j : ℂ))).natDegree ≤ 1 := by
      intro j _; rw [Polynomial.natDegree_X_sub_C (1 + (j : ℂ))]
    refine le_trans (Finset.sum_le_sum hle) ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) hstep

open Polynomial in
theorem shiftBinomPoly_eval (i : ℕ) (m : ℕ) :
    (shiftBinomPoly i).eval (m : ℂ) = cbz ((m : ℤ) - 1) i := by
  rw [cbz_apply_nonneg _ (by positivity), show ((i : ℤ)).toNat = i from by simp]
  rw [shiftBinomPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  rw [gBinom, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    push_cast; ring

/-- Bridge `gBinom (a:ℤ) k = (a.choose k : ℂ)` for `k ≤ a` (ordinary binomial). -/
theorem cbz_natCast_eq_choose {a k : ℕ} (hk : k ≤ a) :
    cbz (a : ℤ) k = (a.choose k : ℂ) := by
  rw [cbz_apply_nonneg _ (by positivity), show ((k : ℤ)).toNat = k from by simp, gBinom]
  have hprod : (∏ i ∈ Finset.range k, (((a : ℤ) : ℂ) - (i : ℂ)))
      = ((a.descFactorial k : ℕ) : ℂ) := by
    rw [Nat.descFactorial_eq_prod_range a k, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hia : (i : ℕ) ≤ a := le_trans (le_of_lt (Finset.mem_range.mp hi)) hk
    rw [Nat.cast_sub hia]; push_cast; ring
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [mul_comm, mul_div_assoc, div_self (by exact_mod_cast Nat.factorial_ne_zero k), mul_one]

/-- **The alternating binomial identity.** For `0 ≤ i < a`,
`∑_{m=0}^{a} (−1)^m C(a,m) C(m−1,i) = 0` (the `S₂`-vanishing core of 5.3.9a). -/
theorem alt_shiftBinom_vanish {a i : ℕ} (hia : i < a) :
    ∑ m ∈ Finset.range (a + 1), negOnePow (m : ℤ) * cbz a m * cbz ((m : ℤ) - 1) i = 0 := by
  -- Relate the sum to the `a`-th forward difference of `shiftBinomPoly i` at `0`.
  have hfd := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := shiftBinomPoly i) (n := a) (lt_of_le_of_lt (shiftBinomPoly_natDegree_le i) hia)
  have hval := congrFun hfd 0
  rw [Pi.zero_apply, fwdDiff_iter_eq_sum_shift (1 : ℂ)] at hval
  -- `hval : ∑ k ∈ range (a+1), ((-1)^(a-k)*C(a,k)) • P(0 + k•1) = 0`.
  -- Rewrite each shifted value and the ℤ-smul into ℂ-multiplication.
  have hval' : ∑ k ∈ Finset.range (a + 1),
      (((-1 : ℂ) ^ (a - k) * (a.choose k : ℂ)) * cbz ((k : ℤ) - 1) i) = 0 := by
    rw [← hval]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [zsmul_eq_mul, show ((0 : ℂ) + k • (1 : ℂ)) = (k : ℂ) from by
      rw [nsmul_eq_mul]; ring, shiftBinomPoly_eval]
    push_cast
    ring
  -- Our target is `(-1)^a` times `hval'` (signs: `(-1)^{a-k} = (-1)^a (-1)^k`; `cbz a k = C(a,k)`).
  have hkey : ∑ m ∈ Finset.range (a + 1),
      negOnePow (m : ℤ) * cbz a m * cbz ((m : ℤ) - 1) i
      = ((-1 : ℂ) ^ a) * ∑ k ∈ Finset.range (a + 1),
          (((-1 : ℂ) ^ (a - k) * (a.choose k : ℂ)) * cbz ((k : ℤ) - 1) i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hma : m ≤ a := by simp only [Finset.mem_range] at hm; omega
    have hcbz : cbz (a : ℤ) m = (a.choose m : ℂ) := cbz_natCast_eq_choose hma
    have hsign : negOnePow (m : ℤ) = (-1 : ℂ) ^ m := negOnePow_natCast m
    have hsplit : ((-1 : ℂ) ^ (a - m)) = (-1 : ℂ) ^ a * (-1 : ℂ) ^ m := by
      have h1 : (-1 : ℂ) ^ (a - m) * (-1 : ℂ) ^ m = (-1 : ℂ) ^ a := by
        rw [← pow_add, show a - m + m = a from by omega]
      have h2 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (-1 : ℂ) ^ (a - m) = (-1 : ℂ) ^ (a - m) * ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) := by
              rw [h2, mul_one]
        _ = ((-1 : ℂ) ^ (a - m) * (-1 : ℂ) ^ m) * (-1 : ℂ) ^ m := by ring
        _ = (-1 : ℂ) ^ a * (-1 : ℂ) ^ m := by rw [h1]
    -- `(-1)^a · (-1)^{a-m} = (-1)^m`.
    have hcombine : (-1 : ℂ) ^ a * (-1 : ℂ) ^ (a - m) = (-1 : ℂ) ^ m := by
      rw [hsplit, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hsign, hcbz]
    rw [show (-1 : ℂ) ^ a * ((-1) ^ (a - m) * (a.choose m : ℂ) * cbz ((m : ℤ) - 1) i)
        = ((-1 : ℂ) ^ a * (-1) ^ (a - m)) * ((a.choose m : ℂ) * cbz ((m : ℤ) - 1) i) from by ring,
      hcombine]
    ring
  rw [hkey, hval', mul_zero]

/-! ## Assembling 5.3.9a -/

section Headline
variable (N : OrdVModule W M) {a β : ℤ} {u v : 𝒱} {h : ℂ} {x : M}

/-- The iterate summand of `module_iterate0` at `ℓ = m-1`, `n = a+β-m-1`. -/
private noncomputable def itG (N : OrdVModule W M) (a β m : ℤ) (u v : 𝒱) (x : M) (i : ℤ) : M :=
  (negOnePow i * cbz (m - 1) i) •
    (mode (N.YM u) (m - 1 - i) (mode (N.YM v) (a + β - m - 1 + i) x)
      - negOnePow (m - 1) • mode (N.YM v) (m - 1 + (a + β - m - 1) - i) (mode (N.YM u) i x))

/-- On `M_h`, the iterate `(u₍ₘ₋₁₎v)₍ₐ₊ᵦ₋ₘ₋₁₎ x` collapses to a finite `Finset.Ico 0 (a+1)`
sum of the iterate summands (its support is `0 ≤ i ≤ a`). -/
theorem iterate_on_lowest (hcw : IsLowestWeight N h)
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading β) (hx : x ∈ N.weight h)
    (ha : 0 ≤ a) {m : ℤ} (hm0 : 0 ≤ m) (hma : m ≤ a) :
    mode (N.YM (W.smul u (m - 1) v)) (a + β - m - 1) x
      = ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itG N a β m u v x i := by
  rw [module_iterate0 N.toWeakModule u v x (m - 1) (a + β - m - 1)]
  have hsupp : (Function.support (itG N a β m u v x)) ⊆ Finset.Ico (0 : ℤ) (a + 1) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hc
    push_neg at hc
    apply hi
    unfold itG
    -- Either `i < 0` (cbz vanishes) or `i ≥ a+1` (both inner products vanish on M_h).
    rcases lt_or_ge i 0 with hineg | hipos
    · rw [cbz_apply_neg (m - 1) hineg, mul_zero, zero_smul]
    · have hia : a + 1 ≤ i := hc hipos
      have hT1 : mode (N.YM v) (a + β - m - 1 + i) x = 0 := by
        apply mode_lowering_vanish N hcw hv hx; omega
      have hT2 : mode (N.YM u) i x = 0 := by
        apply mode_lowering_vanish N hcw hu hx; omega
      rw [hT1, map_zero, hT2, map_zero, smul_zero, sub_zero, smul_zero]
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz (m - 1) i) •
      (mode (N.YM u) (m - 1 - i) (mode (N.YM v) (a + β - m - 1 + i) x)
        - negOnePow (m - 1) • mode (N.YM v) (m - 1 + (a + β - m - 1) - i)
            (mode (N.YM u) i x)))
      = ∑ᶠ i : ℤ, itG N a β m u v x i from rfl]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ico (0 : ℤ) (a + 1)) (by
    intro i hi; exact hsupp hi)]

/-- `o(u*v) x = ∑_{m=0}^{a} C(a,m)·(u₍ₘ₋₁₎v)₍ₐ₊ᵦ₋ₘ₋₁₎ x` on homogeneous `u ∈ 𝒱ₐ`,
`v ∈ 𝒱ᵦ`. -/
theorem oMod_zhuMul_expand (hu : u ∈ W.grading a) (hv : v ∈ W.grading β) (ha : 0 ≤ a) :
    oMod N (zhuMul W u v) x
      = ∑ m ∈ Finset.range (a.toNat + 1),
          cbz a m • mode (N.YM (W.smul u ((m : ℤ) - 1) v)) (a + β - m - 1) x := by
  rw [zhuMul_homogeneous W hu v, map_sum]
  rw [LinearMap.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  -- `u₍ₘ₋₁₎ v ∈ 𝒱_{a+β-m}`, so `oMod` reads its `(a+β-m-1)`-mode.
  have hmem : W.smul u ((m : ℤ) - 1) v ∈ W.grading (a + β - m) := by
    have := W.smul_mem_grading hu hv ((m : ℤ) - 1)
    rwa [show (a + β - ((m : ℤ) - 1) - 1) = a + β - m from by ring] at this
  have he : oMod N (W.smul u ((m : ℤ) - 1) v) = mode (N.YM (W.smul u ((m : ℤ) - 1) v)) (a + β - m - 1) := by
    rw [oMod_homogeneous N hmem]
  rw [he]

/-- The first iterate summand (the `u₍·₎v₍·₎` term). -/
private noncomputable def itT1 (N : OrdVModule W M) (a β m : ℤ) (u v : 𝒱) (x : M) (i : ℤ) : M :=
  (negOnePow i * cbz (m - 1) i) •
    mode (N.YM u) (m - 1 - i) (mode (N.YM v) (a + β - m - 1 + i) x)

/-- The second iterate summand (the `v₍·₎u₍·₎` term, with its sign). -/
private noncomputable def itT2 (N : OrdVModule W M) (a β m : ℤ) (u v : 𝒱) (x : M) (i : ℤ) : M :=
  (negOnePow i * cbz (m - 1) i) •
    (negOnePow (m - 1) • mode (N.YM v) (m - 1 + (a + β - m - 1) - i) (mode (N.YM u) i x))

theorem itG_split (N : OrdVModule W M) (a β m : ℤ) (u v : 𝒱) (x : M) (i : ℤ) :
    itG N a β m u v x i = itT1 N a β m u v x i - itT2 N a β m u v x i := by
  unfold itG itT1 itT2
  rw [smul_sub]

/-- The `S₂` (the `v₍·₎u₍·₎` term) of the iterated double sum **vanishes** on `M_h`,
by the alternating binomial identity `alt_shiftBinom_vanish`. -/
theorem S2_vanish (hcw : IsLowestWeight N h)
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading β) (hx : x ∈ N.weight h) (ha : 0 ≤ a) :
    ∑ m ∈ Finset.range (a.toNat + 1),
        cbz a m • ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itT2 N a β m u v x i = 0 := by
  -- Pull the `cbz a m` scalar inside; the inner `u₍ᵢ₎ x` vanishes for `i ≥ a`.
  have hrw : ∀ m ∈ Finset.range (a.toNat + 1),
      cbz a m • ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itT2 N a β m u v x i
        = ∑ i ∈ Finset.Ico (0 : ℤ) a,
            (cbz a m * (negOnePow i * cbz (m - 1) i) * negOnePow (m - 1)) •
              mode (N.YM v) (a + β - 2 - i) (mode (N.YM u) i x) := by
    intro m hm
    rw [Finset.smul_sum]
    -- The `i = a` term vanishes: `u₍ₐ₎ x = 0` on `M_h`.
    rw [show Finset.Ico (0 : ℤ) (a + 1) = insert a (Finset.Ico (0 : ℤ) a) from by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp)]
    have hua : mode (N.YM u) a x = 0 := mode_lowering_vanish N hcw hu hx (le_refl a)
    have hzero : cbz a m • itT2 N a β m u v x a = 0 := by
      unfold itT2
      rw [hua, map_zero, smul_zero, smul_zero, smul_zero]
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    unfold itT2
    rw [smul_smul, smul_smul, show (m - 1 + (a + β - m - 1) - i) = a + β - 2 - i from by ring]
  rw [Finset.sum_congr rfl hrw]
  -- Swap the order of summation.
  rw [Finset.sum_comm]
  -- Each inner `m`-sum has coefficient `∑_m cbz a m · negOnePow m · cbz(m-1) i = 0` (i < a).
  refine Finset.sum_eq_zero (fun i hi => ?_)
  simp only [Finset.mem_Ico] at hi
  rw [← Finset.sum_smul]
  have hscal : (∑ m ∈ Finset.range (a.toNat + 1),
      cbz a m * (negOnePow i * cbz (m - 1) i) * negOnePow (m - 1))
      = (negOnePow i) * (- ∑ m ∈ Finset.range (a.toNat + 1),
          negOnePow m * cbz a m * cbz (m - 1) i) := by
    rw [mul_neg, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [negOnePow_pred m]
    ring
  rw [hscal]
  -- The bracketed sum is the alternating binomial identity at `(a.toNat, i.toNat)`, `i < a`.
  have hi2 : i < a := hi.2
  have hkey : (∑ m ∈ Finset.range (a.toNat + 1),
      negOnePow (m : ℤ) * cbz a m * cbz ((m : ℤ) - 1) i) = 0 := by
    have hcast : a = (a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
    have hicast : i = (i.toNat : ℤ) := (Int.toNat_of_nonneg hi.1).symm
    have hav := alt_shiftBinom_vanish (a := a.toNat) (i := i.toNat)
      (by rw [hcast, hicast] at hi2; exact_mod_cast hi2)
    rw [← hcast, ← hicast] at hav
    exact hav
  rw [hkey, neg_zero, mul_zero, zero_smul]

/-- The `S₁` (the `u₍·₎v₍·₎` term) of the iterated double sum collapses to the leading term
`u₍ₐ₋₁₎ v₍ᵦ₋₁₎ x` on `M_h` (only the `m = a`, `i = 0` summand survives). -/
theorem S1_collapse (hcw : IsLowestWeight N h)
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading β) (hx : x ∈ N.weight h) (ha : 0 ≤ a) :
    ∑ m ∈ Finset.range (a.toNat + 1),
        cbz a m • ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itT1 N a β m u v x i
      = mode (N.YM u) (a - 1) (mode (N.YM v) (β - 1) x) := by
  rw [Finset.sum_eq_single a.toNat ?_ ?_]
  · -- The `m = a` term: only `i = 0` survives.
    have hcbzaa : cbz a (a.toNat : ℤ) = 1 := by
      rw [cbz_apply_nonneg _ (by positivity),
        show ((a.toNat : ℤ)).toNat = a.toNat from Int.toNat_natCast a.toNat, gBinom]
      have hprod : (∏ j ∈ Finset.range a.toNat, ((a : ℂ) - (j : ℂ)))
          = (a.toNat.factorial : ℂ) := by
        have ha' : (a : ℂ) = (a.toNat : ℂ) := by
          rw [show (a.toNat : ℂ) = ((a.toNat : ℤ) : ℂ) from by push_cast; ring,
            Int.toNat_of_nonneg ha]
        rw [ha', ← Nat.descFactorial_self a.toNat, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Nat.cast_sub (le_of_lt (Finset.mem_range.mp hj))]
      rw [hprod, div_self (by exact_mod_cast Nat.factorial_ne_zero a.toNat)]
    rw [hcbzaa, one_smul, show ((a.toNat : ℤ)) = a from Int.toNat_of_nonneg ha]
    rw [Finset.sum_eq_single (0 : ℤ) ?_ ?_]
    · -- `i = 0`: the leading summand.
      unfold itT1
      rw [show ((0 : ℤ)) = 0 from rfl]
      simp only [cbz_zero, mul_one, negOnePow, Even.zero, if_true, one_smul]
      rw [show (a - 1 - 0 : ℤ) = a - 1 from by ring, show (a + β - a - 1 + 0 : ℤ) = β - 1 from by ring]
    · -- `i ≠ 0` in `Ico 0 (a+1)`: vanishes (inner `v₍·₎ x = 0`).
      intro i hi hine
      simp only [Finset.mem_Ico] at hi
      unfold itT1
      have hvan : mode (N.YM v) (a + β - a - 1 + i) x = 0 := by
        apply mode_lowering_vanish N hcw hv hx; omega
      rw [hvan, map_zero, smul_zero]
    · intro h0
      exact absurd (Finset.mem_Ico.mpr ⟨le_refl 0, by omega⟩) h0
  · -- `m ≠ a` (i.e. `m < a`): the whole inner sum vanishes.
    intro m hm hmne
    simp only [Finset.mem_range] at hm
    have hmltn : m < a.toNat := by omega
    have hmlt : (m : ℤ) < a := by
      have : (m : ℤ) < (a.toNat : ℤ) := by exact_mod_cast hmltn
      rwa [Int.toNat_of_nonneg ha] at this
    rw [Finset.sum_eq_zero (fun i hi => ?_), smul_zero]
    simp only [Finset.mem_Ico] at hi
    unfold itT1
    have hvan : mode (N.YM v) (a + β - m - 1 + i) x = 0 := by
      apply mode_lowering_vanish N hcw hv hx; omega
    rw [hvan, map_zero, smul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

/-- **Zhu 5.3.9a — module zero-mode multiplicativity on the lowest-weight space.**
For homogeneous `u ∈ 𝒱ₐ`, `v ∈ 𝒱ᵦ` (`a, β ≥ 0`) and `x` in the lowest-weight space `M_h`
(`IsLowestWeight N h`):
`o(u * v) x = o(u) (o(v) x)`. -/
theorem oMod_zhuMul_lowest (hcw : IsLowestWeight N h)
    (hu : u ∈ W.grading a) (hv : v ∈ W.grading β) (hx : x ∈ N.weight h)
    (ha : 0 ≤ a) (hβ : 0 ≤ β) :
    oMod N (zhuMul W u v) x = oMod N u (oMod N v x) := by
  -- RHS: `o(u)(o(v)x) = u₍ₐ₋₁₎ (v₍ᵦ₋₁₎ x)`.
  have hRHS : oMod N u (oMod N v x) = mode (N.YM u) (a - 1) (mode (N.YM v) (β - 1) x) := by
    have hv1 : oMod N v x = mode (N.YM v) (β - 1) x := by rw [oMod_homogeneous N hv]
    have hu1 : oMod N u (mode (N.YM v) (β - 1) x)
        = mode (N.YM u) (a - 1) (mode (N.YM v) (β - 1) x) := by rw [oMod_homogeneous N hu]
    rw [hv1, hu1]
  rw [hRHS]
  -- LHS: expand `o(u*v)`, replace each iterate by its `M_h`-collapse, split into S₁ − S₂.
  rw [oMod_zhuMul_expand N hu hv ha]
  have hstep : ∀ m ∈ Finset.range (a.toNat + 1),
      cbz a m • mode (N.YM (W.smul u ((m : ℤ) - 1) v)) (a + β - m - 1) x
        = cbz a m • ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itT1 N a β m u v x i
          - cbz a m • ∑ i ∈ Finset.Ico (0 : ℤ) (a + 1), itT2 N a β m u v x i := by
    intro m hm
    simp only [Finset.mem_range] at hm
    rw [iterate_on_lowest N hcw hu hv hx ha (by positivity) (by omega : (m : ℤ) ≤ a)]
    rw [Finset.sum_congr rfl (fun i _ => itG_split N a β m u v x i)]
    rw [Finset.sum_sub_distrib, smul_sub]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
    S1_collapse N hcw hu hv hx ha, S2_vanish N hcw hu hv hx ha, sub_zero]

end Headline

end VOA
