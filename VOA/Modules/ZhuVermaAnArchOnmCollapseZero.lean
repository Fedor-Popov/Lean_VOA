/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHingeCollapse
import VOA.Modules.ZhuVermaAnArchBottomDefectClose
import VOA.Modules.ZhuVermaAnArchDJ48
import VOA.Modules.ZhuVermaAnArchDWeightPoleShift
import VOA.Modules.ZhuRingInstance

/-!
# The bottom hinge `OnmFull W 0 0` — the pole-`0` reduction of `*^0_{0,p}`

This file proves the **structural reduction of the Dong–Jiang three-index product at the bottom of
the tower**, `(n,m) = (0,0)`, and uses it to isolate exactly what the collapse
`OnmFull W 0 0 = O W` needs.

## The proved reduction (fully proved, axiom-clean)

* `resHom_shift_pascal` — the shift/pole Pascal step
  `resHom W (s+1) q = resHom W s q + resHom W s (q-1)` (`s : ℕ`, `q : ℤ`), i.e.
  `(1+z)^{wt u+s+1}/z^q = (1+z)^{wt u+s}/z^q + (1+z)^{wt u+s}/z^{q-1}`.
* `resHom_shift_expand` — the binomial expansion of the shift
  `∑_{i≤A} C(A,i)·resHom W 0 (i+c) = resHom W A (A+c)`.
* `anmGen_zero_zero_zero` — `u *^0_{0,0} v = zhuMul W u v` (Zhu's product).
* `anmGen_zero_zero_succ` — **`u *^0_{0,p+1} v = resHom W p 0 u v`**: at `(n,m)=(0,0)` the
  general Dong–Jiang product with `p ≥ 1` is a single **pole-order-`0`** residue
  `Res_z (1+z)^{wt u + p - 1} Y(u,z)v` with binomial shift `p-1`.
* `anmGen_zero_zero_pos` — the same statement in the `1 ≤ p` phrasing.

This reduction is reusable and is the reason the two
`OnmCollapses W 0` generator families become concrete:

* `assocDefect_zero_zero_succ_eq` / `assocDefect_zero_zero_zero_eq`,
* `levelMix_zero_zero_succ_eq` / `levelMix_zero_zero_zero_eq`.

## What is discharged unconditionally

* `levelMix_zero_zero_zero_mem` — the `p = 0` level-mixing generator lies in `Onm W 0 0`; pure
  two-sided-ideal bookkeeping off the **unconditional** `zhuRingData_holds` (Zhu Thm 2.1.1/2.1.2).
* `assocDefect_zero_zero_diag_mem` — the `p₁ = p₂ = p₃ = 0` associator-defect generator lies in
  `Onm W 0 0`; the inner difference is literally the Zhu associator, killed by
  `ZhuRingData.assoc`, and the outer wrap by `ZhuRingData.right_ideal`.
* `assocDefect_outer_zero_mem_of_inner` — for `p₃ = 0` and **arbitrary** `p₁ p₂`, the whole
  generator lands in `Onm W 0 0` as soon as its inner difference does (again `right_ideal`).
* `onmFull_zero_zero_eq_O_of_gens` / `onmCollapses_zero_of_gens` — the assembly
  `OnmFull W 0 0 = O W` from the two generator families, via the proved
  `onmFull_eq_Onm_of_gens` and `Onm_zero_zero_eq_O`.

## What is NOT proved, and why

`OnmFull W 0 0 = O W` is **not** proved here.  Two facts pin down the difficulty precisely.

1. **It is the diagonal case `n = 0` of Dong–Jiang Proposition 4.5** (`A_n(V) = A_{n,n}(V)`,
   `math/0601626`, §4).  The off-diagonal statement `O_{n,m} = O'_{n,m}` is explicitly flagged by
   Dong–Jiang as open ("It seems that this is a very difficult problem and we cannot find a proof
   for this in this paper", Remark after Lemma 2.9); the diagonal case is the one they *do* settle
   — but their proof is **representation-theoretic**, not an algebraic identity: they invoke
   Dong–Li–Mason Thm 4.1 to realise an arbitrary `A_n(V)`-module `U` as `M(n)` for an admissible
   `M`, and then read off from DJ Lemma 4.1 that `O''_{n,n} + O'''_{n,n}` acts by `0` on `U`.
   Instantiating at the regular module `U = A_n(V)` converts that into `O'' + O''' ⊆ O'`.  So the
   route suggested by "Zhu associativity + a pole-`0` residue" is **not** sufficient: what is
   really needed is the module-theoretic characterisation of `O(𝒱)` (`x ∈ O(𝒱) ⟺ o(x) = 0` on the
   bottom of every admissible module), which the repo does not have in the required direction.

2. **The pole-`0` residue does not by itself absorb `O(𝒱)` in either slot.**
   `resHom_zeroPole_zhuLgen` (proved below, off the proved `resHom_Lneg1_ibp`) gives, for
   homogeneous `c`, `resHom W s 0 (L(-1)c + L(0)c) w = -(1+s)·resHom W s 0 c w`: the pole-`0`
   residue sends the Zhu grading generator in its **left** slot to a *nonzero multiple of the plain
   residue*, not into `O(𝒱)`.  Dually, the free-boson witness
   `resHom W 0 0 (α₋₁α₋₁𝟙) (α₋₂𝟙+α₋₁𝟙) ↦ 2λ ≠ 0`, shows it does not absorb `O(𝒱)` in its
   **right** slot either.  Hence neither `assocDefect W 0 0 p₁ p₂ (p₃+1) …` nor
   `levelMix W 0 0 (p+1) …` can be closed by "inner factor lies in `O(𝒱)`, outer wrap absorbs it".
   The membership must come from a cancellation *inside* the achievable generator family.

   That cancellation is real, not accidental.  Hand-computing the smallest nontrivial
   `O''`-generator on the rank-1 free boson — `p₁ = p₂ = 0`, `p₃ = 1`, `b = c = 𝟙`,
   `a = α₋₁𝟙` — gives inner difference `Δ = 2(α₋₃𝟙 + α₋₂𝟙)`, and
   `resHom W 0 0 (α₋₁α₋₁𝟙) Δ = 12α₋₄𝟙 + 32α₋₃𝟙 + 28α₋₂𝟙 + 8α₋₁𝟙`, whose Zhu symbol is
   `(-12 + 32 - 28 + 8)λ = 0`.  So this generator *is* in `O(𝒱)`, but only after an exact
   alternating cancellation — matching an engine sweep (`0` violations) and
   confirming that the statement is true-but-not-formal at this level.

Accordingly the two families are carried as explicit hypotheses (NOT axioms, NOT `sorry`), and the
assembly theorem states exactly what they buy.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (`O' + O'' + O'''`, Lemmas 2.6–2.9 and
the Remark after Lemma 2.9), Prop. 4.5; Dong–Li–Mason, J. Algebra 206 (1998) 67–96, Thm 4.1;
Zhu, J. Amer. Math. Soc. 9 (1996), Thm 2.1.1/2.1.2; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Reduction of an identity in the left `resHom` slot to homogeneous inputs. -/

/-- **Homogeneous test for `ℂ`-linear maps.**  Two `ℂ`-linear endomorphisms of `𝒱` that agree on
every homogeneous vector of **nonnegative** grade agree everywhere: decompose along the internal
grading and discard negative grades by `W.positivity`. -/
theorem linear_eq_of_homog (W : VertexOperatorAlgebra 𝒱) (F G : 𝒱 →ₗ[ℂ] 𝒱)
    (h : ∀ (K : ℕ) {a : 𝒱}, a ∈ W.grading (K : ℤ) → F a = G a) (a : 𝒱) : F a = G a := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hdecomp : ∑ k ∈ (DirectSum.decompose W.grading a).support,
      ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) = a :=
    DirectSum.sum_support_decompose W.grading a
  rw [← hdecomp, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading a k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    exact h K hk
  · have hzero : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) = 0 := by
      have hb : ((DirectSum.decompose W.grading a k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using hb
    rw [hzero, map_zero, map_zero]

/-- The generic FZ residue `resHom W s q · v` bundled as a `ℂ`-linear map in its **left** slot
(the slot that carries the grade decomposition). -/
noncomputable def resHomLeft (W : VertexOperatorAlgebra 𝒱) (s q : ℤ) (v : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := resHom W s q u v
  map_add' u₁ u₂ := resHom_add_left W s q u₁ u₂ v
  map_smul' c u := resHom_smul_left W s q c u v

@[simp] theorem resHomLeft_apply (W : VertexOperatorAlgebra 𝒱) (s q : ℤ) (v u : 𝒱) :
    resHomLeft W s q v u = resHom W s q u v := rfl

/-! ## The shift/pole Pascal step and its binomial expansion. -/

/-- **The shift/pole Pascal step for `resHom`.**  For `s : ℕ` and any pole `q : ℤ`,
`resHom W (s+1) q u v = resHom W s q u v + resHom W s (q-1) u v`, i.e.
`(1+z)^{wt u+s+1}/z^q = (1+z)^{wt u+s}/z^q + (1+z)^{wt u+s}/z^{q-1}`.  Proved per grade from
`cbz_pascal_up`, with the two boundary terms killed by `cbz_lt` (top) and `cbz_apply_neg`
(bottom). -/
theorem resHom_shift_pascal (W : VertexOperatorAlgebra 𝒱) (s : ℕ) (q : ℤ) (u v : 𝒱) :
    resHom W ((s : ℤ) + 1) q u v = resHom W (s : ℤ) q u v + resHom W (s : ℤ) (q - 1) u v := by
  have key : ∀ (K : ℕ) {a : 𝒱}, a ∈ W.grading (K : ℤ) →
      resHomLeft W ((s : ℤ) + 1) q v a
        = (resHomLeft W (s : ℤ) q v + resHomLeft W (s : ℤ) (q - 1) v) a := by
    intro K a ha
    simp only [LinearMap.add_apply, resHomLeft_apply]
    rw [resHom_homogeneous W ((s : ℤ) + 1) q ha, resHom_homogeneous W (s : ℤ) q ha,
      resHom_homogeneous W (s : ℤ) (q - 1) ha,
      show ((K : ℤ) + ((s : ℤ) + 1)) = ((K : ℤ) + (s : ℤ)) + 1 from by ring,
      show (((K : ℤ) + (s : ℤ)) + 1).toNat + 1 = ((K + s) + 1) + 1 from by omega,
      show ((K : ℤ) + (s : ℤ)).toNat + 1 = (K + s) + 1 from by omega]
    have hsplit : ∀ i : ℕ,
        cbz (((K : ℤ) + (s : ℤ)) + 1) (i : ℤ) • W.smul a ((i : ℤ) - q) v
          = cbz ((K : ℤ) + (s : ℤ)) (i : ℤ) • W.smul a ((i : ℤ) - q) v
            + cbz ((K : ℤ) + (s : ℤ)) ((i : ℤ) - 1) • W.smul a ((i : ℤ) - q) v := by
      intro i; rw [cbz_pascal_up, add_smul]
    simp only [hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_range_succ,
        cbz_lt (show (0 : ℤ) ≤ (K : ℤ) + (s : ℤ) from by positivity)
          (show ((K : ℤ) + (s : ℤ)) < ((K + s + 1 : ℕ) : ℤ) from by push_cast; omega),
        zero_smul, add_zero]
    · rw [Finset.sum_range_succ' (fun i : ℕ =>
        cbz ((K : ℤ) + (s : ℤ)) ((i : ℤ) - 1) • W.smul a ((i : ℤ) - q) v) (K + s + 1)]
      simp only [Nat.cast_zero, zero_sub]
      rw [cbz_apply_neg ((K : ℤ) + (s : ℤ)) (show (-1 : ℤ) < 0 from by norm_num), zero_smul,
        add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2 <;> push_cast <;> ring
  simpa using linear_eq_of_homog W (resHomLeft W ((s : ℤ) + 1) q v)
    (resHomLeft W (s : ℤ) q v + resHomLeft W (s : ℤ) (q - 1) v) key u

/-- **The binomial expansion of the `resHom` shift.**  For `A : ℕ` and any `c : ℤ`,
`∑_{i=0}^{A} C(A,i)·resHom W 0 (i+c) u v = resHom W A (A+c) u v`, i.e.
`(1+z)^{wt u}·(1+z)^A/z^{A+c} = ∑_i C(A,i)(1+z)^{wt u}·z^i/z^{A+c}`.  Induction on `A` off
`resHom_shift_pascal`. -/
theorem resHom_shift_expand (W : VertexOperatorAlgebra 𝒱) (A : ℕ) (c : ℤ) (u v : 𝒱) :
    (∑ i ∈ Finset.range (A + 1), cbz (A : ℤ) (i : ℤ) • resHom W 0 ((i : ℤ) + c) u v)
      = resHom W (A : ℤ) ((A : ℤ) + c) u v := by
  induction A generalizing c with
  | zero => simp
  | succ A ih =>
    rw [show ((A + 1 : ℕ) : ℤ) = (A : ℤ) + 1 from by push_cast; ring]
    have hsplit : ∀ i : ℕ,
        cbz ((A : ℤ) + 1) (i : ℤ) • resHom W 0 ((i : ℤ) + c) u v
          = cbz (A : ℤ) (i : ℤ) • resHom W 0 ((i : ℤ) + c) u v
            + cbz (A : ℤ) ((i : ℤ) - 1) • resHom W 0 ((i : ℤ) + c) u v := by
      intro i; rw [cbz_pascal_up, add_smul]
    simp only [hsplit, Finset.sum_add_distrib]
    have hfirst : (∑ i ∈ Finset.range (A + 1 + 1),
        cbz (A : ℤ) (i : ℤ) • resHom W 0 ((i : ℤ) + c) u v)
          = resHom W (A : ℤ) ((A : ℤ) + c) u v := by
      rw [Finset.sum_range_succ,
        cbz_lt (show (0 : ℤ) ≤ (A : ℤ) from by positivity)
          (show (A : ℤ) < ((A + 1 : ℕ) : ℤ) from by push_cast; omega),
        zero_smul, add_zero, ih c]
    have hsecond : (∑ i ∈ Finset.range (A + 1 + 1),
        cbz (A : ℤ) ((i : ℤ) - 1) • resHom W 0 ((i : ℤ) + c) u v)
          = resHom W (A : ℤ) ((A : ℤ) + (c + 1)) u v := by
      rw [Finset.sum_range_succ' (fun i : ℕ =>
        cbz (A : ℤ) ((i : ℤ) - 1) • resHom W 0 ((i : ℤ) + c) u v) (A + 1)]
      simp only [Nat.cast_zero, zero_sub]
      rw [cbz_apply_neg (A : ℤ) (show (-1 : ℤ) < 0 from by norm_num), zero_smul, add_zero,
        ← ih (c + 1)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2 <;> push_cast <;> ring
    rw [hfirst, hsecond, resHom_shift_pascal W A ((A : ℤ) + 1 + c),
      show ((A : ℤ) + 1 + c - 1) = (A : ℤ) + c from by ring,
      show ((A : ℤ) + 1 + c) = (A : ℤ) + (c + 1) from by ring]
    exact add_comm _ _

/-! ## The `(n,m) = (0,0)` reduction of the Dong–Jiang three-index product. -/

/-- **`u *^0_{0,0} v = zhuMul W u v`.**  At `p = 0` the general product is the single `i = 0` term
`resHom W 0 1`, which is exactly Zhu's product. -/
theorem anmGen_zero_zero_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    anmGen W 0 0 0 u v = zhuMul W u v := by
  rw [anmGen_eq_anmRight W 0 0 u v, anmRight_zero_zero]

/-- **The bottom reduction: `u *^0_{0,p+1} v = resHom W p 0 u v`.**  At `(n,m) = (0,0)` and
`p ≥ 1` the Dong–Jiang general product is a single **pole-order-`0`** residue
`Res_z (1+z)^{wt u + p} Y(u,z)v`.  The alternating weights `(-1)^i C(i-p-1, i)` are the ordinary
binomials `C(p,i)` (upper-index negation `cbz_neg_upper`), the top term `i = p+1` vanishes
(`cbz_lt`), and the remaining sum is `resHom_shift_expand` at `c = -p`. -/
theorem anmGen_zero_zero_succ (W : VertexOperatorAlgebra 𝒱) (p : ℕ) (u v : 𝒱) :
    anmGen W 0 0 (p + 1) u v = resHom W (p : ℤ) 0 u v := by
  have hterm : ∀ i : ℕ,
      ((-1 : ℂ) ^ i * cbz (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ) + (i : ℤ)) (i : ℤ))
          • resHom W ((0 : ℕ) : ℤ)
              (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ) + (i : ℤ) + 1) u v
        = cbz (p : ℤ) (i : ℤ) • resHom W 0 ((i : ℤ) + (-(p : ℤ))) u v := by
    intro i
    rw [show (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ) + (i : ℤ))
          = (i : ℤ) - (p : ℤ) - 1 from by push_cast; ring,
      show ((i : ℤ) - (p : ℤ) - 1 + 1) = (i : ℤ) + (-(p : ℤ)) from by ring,
      ← cbz_neg_upper (p : ℤ) i, Nat.cast_zero]
  rw [anmGen]
  simp only [hterm]
  rw [Finset.sum_range_succ,
    cbz_lt (show (0 : ℤ) ≤ (p : ℤ) from by positivity)
      (show (p : ℤ) < ((p + 1 : ℕ) : ℤ) from by push_cast; omega),
    zero_smul, add_zero, resHom_shift_expand W p (-(p : ℤ)) u v]
  congr 1
  ring

/-- The bottom reduction in the `1 ≤ p` phrasing: `u *^0_{0,p} v = resHom W (p-1) 0 u v`. -/
theorem anmGen_zero_zero_pos (W : VertexOperatorAlgebra 𝒱) {p : ℕ} (hp : 1 ≤ p) (u v : 𝒱) :
    anmGen W 0 0 p u v = resHom W ((p : ℤ) - 1) 0 u v := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  rw [anmGen_zero_zero_succ]
  congr 1
  push_cast; ring

/-! ## The two `OnmCollapses W 0` generator families, made concrete. -/

/-- The level-mixing generator at `(n,m) = (0,0)`, `p = 0`: `levelMix W 0 0 0 a g v` is the double
Zhu product `(a * g) * v`. -/
theorem levelMix_zero_zero_zero_eq (W : VertexOperatorAlgebra 𝒱) (a g v : 𝒱) :
    levelMix W 0 0 0 a g v = zhuMul W (zhuMul W a g) v := by
  rw [levelMix, anmGen_zero_zero_zero, anmGen_zero_zero_zero]

/-- The level-mixing generator at `(n,m) = (0,0)`, `p = q+1 ≥ 1`: it is the pole-`0` residue
`resHom W q 0` applied to `a *^0_{q+1} g` (the Dong–Jiang right action at level `q+1`). -/
theorem levelMix_zero_zero_succ_eq (W : VertexOperatorAlgebra 𝒱) (q : ℕ) (a g v : 𝒱) :
    levelMix W 0 0 (q + 1) a g v = resHom W (q : ℤ) 0 (anmRight W 0 (q + 1) a g) v := by
  rw [levelMix, anmGen_zero_zero_succ, anmGen_eq_anmRight]

/-- The associator-defect generator at `(n,m) = (0,0)` with outer index `p₃ = 0`: the outer wrap is
Zhu's product. -/
theorem assocDefect_zero_zero_zero_eq (W : VertexOperatorAlgebra 𝒱) (p₁ p₂ : ℕ) (a b c v : 𝒱) :
    assocDefect W 0 0 p₁ p₂ 0 a b c v
      = zhuMul W v (anmGen W 0 0 p₁ (anmGen W 0 p₁ p₂ a b) c
          - anmGen W 0 0 p₂ a (anmGen W p₂ 0 p₁ b c)) := by
  rw [assocDefect, anmGen_zero_zero_zero]

/-- The associator-defect generator at `(n,m) = (0,0)` with outer index `p₃ = r+1 ≥ 1`: the outer
wrap is the pole-`0` residue `resHom W r 0`. -/
theorem assocDefect_zero_zero_succ_eq (W : VertexOperatorAlgebra 𝒱) (p₁ p₂ r : ℕ)
    (a b c v : 𝒱) :
    assocDefect W 0 0 p₁ p₂ (r + 1) a b c v
      = resHom W (r : ℤ) 0 v (anmGen W (r + 1) 0 p₁ (anmGen W (r + 1) p₁ p₂ a b) c
          - anmGen W (r + 1) 0 p₂ a (anmGen W p₂ 0 p₁ b c)) := by
  rw [assocDefect, anmGen_zero_zero_succ]

/-! ## The unconditional discharges at the bottom index. -/

/-- **The `p = 0` level-mixing family lands in `Onm W 0 0`.**  `levelMix W 0 0 0 a g v =
(a * g) * v` with `g ∈ Onm W 0 0 = O(𝒱)`; the right-ideal property gives `a * g ∈ O(𝒱)` and the
left-ideal property gives `(a * g) * v ∈ O(𝒱)`.  Both are fields of the **unconditional**
`zhuRingData_holds` (Zhu Thm 2.1.1/2.1.2). -/
theorem levelMix_zero_zero_zero_mem (W : VertexOperatorAlgebra 𝒱) (a v g : 𝒱)
    (hg : g ∈ Onm W 0 0) : levelMix W 0 0 0 a g v ∈ Onm W 0 0 := by
  rw [Onm_zero_zero_eq_O] at hg ⊢
  rw [levelMix_zero_zero_zero_eq]
  exact (zhuRingData_holds W).left_ideal ((zhuRingData_holds W).right_ideal a hg) v

/-- **The `p₃ = 0` associator-defect family lands in `Onm W 0 0` as soon as its inner difference
does.**  The outer wrap is Zhu multiplication, and `O(𝒱)` is a right ideal
(`zhuRingData_holds`). -/
theorem assocDefect_outer_zero_mem_of_inner (W : VertexOperatorAlgebra 𝒱) (p₁ p₂ : ℕ)
    (a b c v : 𝒱)
    (hin : anmGen W 0 0 p₁ (anmGen W 0 p₁ p₂ a b) c
        - anmGen W 0 0 p₂ a (anmGen W p₂ 0 p₁ b c) ∈ O W) :
    assocDefect W 0 0 p₁ p₂ 0 a b c v ∈ Onm W 0 0 := by
  rw [Onm_zero_zero_eq_O, assocDefect_zero_zero_zero_eq]
  exact (zhuRingData_holds W).right_ideal v hin

/-- **The all-zero associator-defect generator lands in `Onm W 0 0`.**  At `p₁ = p₂ = p₃ = 0` the
inner difference is literally the Zhu associator `(a*b)*c − a*(b*c)`, which lies in `O(𝒱)` by
`ZhuRingData.assoc`; the outer wrap is absorbed by `ZhuRingData.right_ideal`. -/
theorem assocDefect_zero_zero_diag_mem (W : VertexOperatorAlgebra 𝒱) (a b c v : 𝒱) :
    assocDefect W 0 0 0 0 0 a b c v ∈ Onm W 0 0 := by
  refine assocDefect_outer_zero_mem_of_inner W 0 0 a b c v ?_
  rw [anmGen_zero_zero_zero, anmGen_zero_zero_zero, anmGen_zero_zero_zero,
    show anmGen W 0 0 0 b c = zhuMul W b c from anmGen_zero_zero_zero W b c]
  exact (zhuRingData_holds W).assoc a b c

/-! ## The obstruction: the pole-`0` residue does not absorb `O(𝒱)` in its left slot. -/

/-- **The pole-`0` residue on a Zhu grading generator (left slot).**  For homogeneous `c ∈ 𝒱_K`
and `s : ℕ`,
`resHom W s 0 (L(-1)c + L(0)c) w = -(1+s)·resHom W s 0 c w`.
So the pole-`0` residue does **not** send the `O(𝒱)`-generator `L(-1)c + L(0)c` into `O(𝒱)`; it
returns a nonzero multiple of the plain residue.  (Off the proved `resHom_Lneg1_ibp` at pole `0`,
where the `resHom W (s+1) (p+1)` term is killed by its `p = 0` weight, plus `L_zero_grading`.)
This is the precise reason the `p ≥ 1` families of `OnmCollapses W 0` cannot be closed by
"inner factor in `O(𝒱)`, outer wrap absorbs it". -/
theorem resHom_zeroPole_zhuLgen (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (K : ℤ)) (w : 𝒱) (s : ℕ) :
    resHom W (s : ℤ) 0 (W.L (-1) c + W.L 0 c) w
      = (-(1 + (s : ℂ))) • resHom W (s : ℤ) 0 c w := by
  rw [resHom_add_left, resHom_Lneg1_ibp W hc w (s : ℤ) 0 (by positivity),
    W.L_zero_grading c hc, resHom_smul_left]
  push_cast
  rw [zero_smul, add_zero, ← add_smul]
  congr 1
  ring

/-! ## The assembly: `OnmFull W 0 0 = O W` from the two generator families. -/

/-- **`OnmCollapses W 0` from the two generator families.**  Exactly the `(n,m) = (0,0)` instance of
the proved reduction `onmFull_le_Onm_of_gens`. -/
theorem onmCollapses_zero_of_gens (W : VertexOperatorAlgebra 𝒱)
    (hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ Onm W 0 0)
    (hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W 0 0 p a g v ∈ Onm W 0 0) :
    OnmCollapses W 0 :=
  onmFull_le_Onm_of_gens W 0 0 hAssoc hLevel

/-- **`OnmFull W 0 0 = O W` from the two generator families.**  Chains
`onmFull_eq_Onm_of_gens W 0 0` with the proved bottom identification `Onm_zero_zero_eq_O`.
The two hypotheses are the genuine Dong–Jiang Prop. 4.5 (`n = 0`) content and are NOT discharged
here — see the file header for the exact obstruction. -/
theorem onmFull_zero_zero_eq_O_of_gens (W : VertexOperatorAlgebra 𝒱)
    (hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W 0 0 p₁ p₂ p₃ a b c v ∈ Onm W 0 0)
    (hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W 0 0 p a g v ∈ Onm W 0 0) :
    OnmFull W 0 0 = O W := by
  rw [onmFull_eq_Onm_of_gens W 0 0 hAssoc hLevel, Onm_zero_zero_eq_O]

end VOA
