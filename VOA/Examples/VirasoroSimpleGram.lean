/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroGram56
import VOA.Examples.VirasoroSimple
import VOA.Examples.VirasoroSelfDual

/-!
# `dim L(c,0)ₙ` from a Gram rank, and the graded-dimension **jump**

`Core/GradedFormMatrix.finrank_maxQuotient_grading` (**D1**, the bridge) says, for an arbitrary
vertex operator algebra `W`:

  `dim (W / maxGradedIdeal W)ₙ = rank (canGram hne hqp n e)`.

This file instantiates it at the Virasoro family and cashes it in.  For `V(c,0)` both hypotheses
of the canonical form are **free**: `vacVec_ne_zero` gives `𝟙 ≠ 0` (`pbw`-free, via the
linear-dilaton free boson), and `virasoroVOA_qp` gives `L₁𝒱₁ = 0` vacuously because `𝒱₁ = 0`.

## What is new here, and what is imported

* **New**: `finrank_virasoroSimple_grading` — the bridge at `L(c,0)`, in an arbitrary basis of
  `𝒱ₙ`; and `finrank_virasoroSimple_grading_partition`, the same in the partition basis that
  `Examples/VirasoroPartitionBasis` constructs at *every* central charge.
* **New**: the dimension **jump** at the degenerate charges — `L(c,0)ₙ` is strictly smaller at a
  root of the level-`n` determinant than at a non-root.  Levels `4`, `5`, `6`.
* **Imported**: the level-4 matrix from `Examples/VirasoroGram4`, the level-5 and level-6
  matrices from `Examples/VirasoroGram56`.

## The calibration against outside truth

`VirGram4.rank_canGram4_leeYang : rank (canGram4 (-22/5)) = 1` is proved in the repository from
the *independently known* level-4 Lee–Yang radical (`LeeYangKac`).  Feeding it through the bridge
gives `dim L(-22/5,0)₄ = 1`, against `dim V(-22/5,0)₄ = 2`.  That is the classical statement that
the Lee–Yang minimal model has a level-4 singular vector, and it is the one place in this file
where the machine's answer is checked against a number known from outside.

## ⚠ What is **not** claimed

There is **no** uniform-in-`n` statement here that `det (canGram_n c)` is a nonzero polynomial in
`c` (the general form of "D3": `V(c,0)` is simple at generic `c`).  The repository has no
`ℂ[c]`-uniform Shapovalov calculus, and no lemma computing `Lop c m` on a general creation word
with *coefficients* — `VirasoroSpanning.Lop_negWord` is a membership statement only.  What is
available is the statement **level by level**, and it is proved here for `n = 2,3,4,5,6` by
explicit computation.  Every theorem below that needs genericity therefore names the level.

⚠ Note also that "the degenerate locus is discrete" is **false** as a statement about the union
over all levels: the minimal-model charges `1 - 6(p-q)²/(pq)` accumulate at `c = 1`.  The true
and sufficient statement is the **per-level** one: for fixed `n`, `det canGram_n` is a nonzero
polynomial, hence has finitely many roots.  That is the form used below and in
`Examples/VirasoroRigidityStructural`.
-/

set_option linter.style.longLine false

namespace VOA.VirSimpleGram

open VOA VOA.LeeYang VOA.VirModule VOA.VirSimple
open VOA.VirGram56 VOA.VertexOperatorAlgebra
open Module (Basis finrank)

variable (c : ℂ)

/-! ## §1  The bridge at `L(c,0)` -/

/-- **D1 at Virasoro.**  The level-`n` graded dimension of the *simple* Virasoro VOA
`L(c,0)` is the rank of the canonical level-`n` Gram matrix of `V(c,0)`, in any basis of `𝒱ₙ`:

  `dim L(c,0)ₙ = rank (canGram (vacVec_ne_zero c) (virasoroVOA_qp c) n e)`.

Both hypotheses of the canonical form are discharged here once and for all. -/
theorem finrank_virasoroSimple_grading {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℤ)
    (e : Basis ι ℂ ((virasoroVOA c).grading n)) :
    finrank ℂ ((virasoroSimple c).grading n)
      = (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) n e).rank :=
  GramMat.finrank_maxQuotient_grading (vacVec_ne_zero c) (virasoroVOA_qp c) n e

/-- The same, in the **partition basis** — the basis of `𝒱ₙ` indexed by the partitions of `n`
into parts `≥ 2`, which `Examples/VirasoroPartitionBasis` constructs at *every* `c`.  This is the
form in which the statement is uniform in the central charge: the index set does not move. -/
theorem finrank_virasoroSimple_grading_partition (n : ℕ) :
    finrank ℂ ((virasoroSimple c).grading (n : ℤ))
      = (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) (n : ℤ)
          (gradedBasis c n)).rank :=
  finrank_virasoroSimple_grading c (n : ℤ) (gradedBasis c n)

/-! ## §2  The two halves of the jump, at Virasoro -/

/-- **Nondegenerate level**: `dim L(c,0)ₙ = dim V(c,0)ₙ`. -/
theorem finrank_virasoroSimple_eq_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℤ)
    (e : Basis ι ℂ ((virasoroVOA c).grading n))
    (h : (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) n e).det ≠ 0) :
    finrank ℂ ((virasoroSimple c).grading n) = finrank ℂ ((virasoroVOA c).grading n) :=
  GramMat.finrank_maxQuotient_grading_eq_of_det_ne_zero (vacVec_ne_zero c) (virasoroVOA_qp c)
    n e h

/-- **Degenerate level**: `dim L(c,0)ₙ < dim V(c,0)ₙ`. -/
theorem finrank_virasoroSimple_lt_of_det_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℤ)
    (e : Basis ι ℂ ((virasoroVOA c).grading n))
    (h : (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) n e).det = 0) :
    finrank ℂ ((virasoroSimple c).grading n) < finrank ℂ ((virasoroVOA c).grading n) :=
  GramMat.finrank_maxQuotient_grading_lt_of_det_eq_zero (vacVec_ne_zero c) (virasoroVOA_qp c)
    n e h

/-! ## §3  The level-4 Lee–Yang calibration, through the bridge -/

/-- `VirGram4.canGram4` **is** `GramMat.canGram` at level 4 in the basis `VirGram4.basis4`. -/
theorem canGram_basis4 :
    GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 4 (VirGram4.basis4 c)
      = VirGram4.canGram4 c :=
  VirGram4.gramMatrix_basis4 c

/-- **`dim L(-22/5, 0)₄ = 1`.**  The bridge, fed the level-4 rank, returns the classical
Lee–Yang answer: the level-4 space of the *simple* minimal model is one-dimensional, against
`dim V(-22/5,0)₄ = 2`.  The missing dimension is the singular vector `5L₋₂²|0⟩ - 3L₋₄|0⟩`. -/
theorem finrank_virasoroSimple_leeYang_four :
    finrank ℂ ((virasoroSimple leeYangC).grading 4) = 1 := by
  rw [finrank_virasoroSimple_grading leeYangC 4 (VirGram4.basis4 leeYangC), canGram_basis4]
  exact VirGram4.rank_canGram4_leeYang

/-- At a central charge off `{0, -22/5}` the level-4 space of `L(c,0)` is *full*. -/
theorem finrank_virasoroSimple_four_of_generic (h0 : c ≠ 0) (hLY : c ≠ leeYangC) :
    finrank ℂ ((virasoroSimple c).grading 4) = 2 := by
  rw [finrank_virasoroSimple_eq_of_det_ne_zero c 4 (VirGram4.basis4 c)
      (by rw [canGram_basis4]; intro hd
          rcases (VirGram4.det_canGram4_eq_zero_iff c).mp hd with h | h
          · exact h0 h
          · exact hLY h)]
  exact VirDefLow.finrank_gradingVir_four c

/-- **The level-4 jump**: `dim L(-22/5,0)₄ = 1 < 2 = dim L(1,0)₄`. -/
theorem finrank_virasoroSimple_four_leeYang_lt :
    finrank ℂ ((virasoroSimple leeYangC).grading 4)
      < finrank ℂ ((virasoroSimple 1).grading 4) := by
  rw [finrank_virasoroSimple_leeYang_four,
    finrank_virasoroSimple_four_of_generic 1 (by norm_num) (by rw [leeYangC]; norm_num)]
  norm_num

/-! ## §4  Levels 5 and 6: the new instances -/

/-- At a central charge off `{0, -22/5}` the level-5 space of `L(c,0)` is full. -/
theorem finrank_virasoroSimple_five_of_generic (h0 : c ≠ 0) (hLY : c ≠ leeYangC) :
    finrank ℂ ((virasoroSimple c).grading 5) = 2 := by
  rw [finrank_virasoroSimple_eq_of_det_ne_zero c 5 (basis5 c)
      (by rw [canGram_basis5]; intro hd
          rcases (det_canGram5_eq_zero_iff c).mp hd with h | h
          · exact h0 h
          · exact hLY h)]
  exact finrank_gradingVir_five c

/-- At a central charge off `{0, 1/2, -22/5, -68/7}` the level-6 space of `L(c,0)` is full. -/
theorem finrank_virasoroSimple_six_of_generic (h0 : c ≠ 0) (hI : c ≠ isingC)
    (hLY : c ≠ leeYangC) (h27 : c ≠ m27C) :
    finrank ℂ ((virasoroSimple c).grading 6) = 4 := by
  rw [finrank_virasoroSimple_eq_of_det_ne_zero c 6 (basis6 c)
      (by rw [canGram_basis6]; intro hd
          rcases (det_canGram6_eq_zero_iff c).mp hd with h | h | h | h
          · exact h0 h
          · exact hI h
          · exact hLY h
          · exact h27 h)]
  exact finrank_gradingVir_six c

/-- The level-6 space of `L(c,0)` is **strictly** smaller than `4` at each of the four degenerate
charges. -/
theorem finrank_virasoroSimple_six_lt_of_degenerate
    (h : c = 0 ∨ c = isingC ∨ c = leeYangC ∨ c = m27C) :
    finrank ℂ ((virasoroSimple c).grading 6) < 4 := by
  have hd : (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 6 (basis6 c)).det = 0 := by
    rw [canGram_basis6]; exact (det_canGram6_eq_zero_iff c).mpr h
  have h6 : finrank ℂ ((virasoroVOA c).grading 6) = 4 := finrank_gradingVir_six c
  have hlt := finrank_virasoroSimple_lt_of_det_eq_zero c 6 (basis6 c) hd
  rwa [h6] at hlt

/-- **The Ising jump, at level 6.**  `dim L(1/2, 0)₆ < dim L(1,0)₆ = 4`.  This is a
degeneracy that levels `2,3,4,5` do not see at all (`det_canGram5_ising_ne_zero`), so it is a
genuinely new instance of the bridge. -/
theorem finrank_virasoroSimple_six_ising_lt :
    finrank ℂ ((virasoroSimple isingC).grading 6)
      < finrank ℂ ((virasoroSimple 1).grading 6) := by
  rw [finrank_virasoroSimple_six_of_generic 1 (by norm_num)
    (by rw [isingC]; norm_num) (by rw [leeYangC]; norm_num) (by rw [m27C]; norm_num)]
  exact finrank_virasoroSimple_six_lt_of_degenerate isingC (Or.inr (Or.inl rfl))

/-- **The `M(2,7)` jump, at level 6.**  `dim L(-68/7, 0)₆ < 4`.  Also invisible below
level 6. -/
theorem finrank_virasoroSimple_six_m27_lt :
    finrank ℂ ((virasoroSimple m27C).grading 6)
      < finrank ℂ ((virasoroSimple 1).grading 6) := by
  rw [finrank_virasoroSimple_six_of_generic 1 (by norm_num)
    (by rw [isingC]; norm_num) (by rw [leeYangC]; norm_num) (by rw [m27C]; norm_num)]
  exact finrank_virasoroSimple_six_lt_of_degenerate m27C (Or.inr (Or.inr (Or.inr rfl)))

/-! ## §5  **D3, level by level**

For a *fixed* level `n`, `det (canGram_n c)` is a **nonzero** polynomial in `c`.  This is the
input the rigidity argument of `Examples/VirasoroRigidityStructural` needs: it supplies a
comparison charge at which the level-`n` graded dimension is full.  The statements below are the
concrete instances; the polynomial identities are `VirGram4.det_canGram4`,
`VirGram56.det_canGram5`, `VirGram56.det_canGram6`.

⚠ Uniform in `n` this is **open in this repository** — see the ⚠ in the file docstring. -/

/-- **D3 at level 4** (as a `canGram` statement): the level-4 determinant is nonzero at
`c = 1`. -/
theorem det_canGram_four_ne_zero_at_one :
    (GramMat.canGram (vacVec_ne_zero (1 : ℂ)) (virasoroVOA_qp 1) 4
      (VirGram4.basis4 1)).det ≠ 0 := by
  rw [canGram_basis4, VirGram4.det_canGram4]
  norm_num

/-- **D3 at level 5.** -/
theorem det_canGram_five_ne_zero_at_one :
    (GramMat.canGram (vacVec_ne_zero (1 : ℂ)) (virasoroVOA_qp 1) 5 (basis5 1)).det ≠ 0 := by
  rw [canGram_basis5]
  exact det_canGram5_ne_zero_at_one

/-- **D3 at level 6.** -/
theorem det_canGram_six_ne_zero_at_one :
    (GramMat.canGram (vacVec_ne_zero (1 : ℂ)) (virasoroVOA_qp 1) 6 (basis6 1)).det ≠ 0 := by
  rw [canGram_basis6]
  exact det_canGram6_ne_zero_at_one

/-- **`V(1,0)` is simple at levels 4, 5 and 6.**  Not a statement about all levels — see the
⚠ in the docstring — but it is the first time this repository exhibits *any* central charge at
which the maximal graded ideal is proved to vanish on a graded piece above level 3. -/
theorem maxIdealVir_one_inf_grading_six_eq_bot :
    QuotVOA.maxGradedIdeal (virasoroVOA (1 : ℂ)) ⊓ (virasoroVOA (1 : ℂ)).grading 6 = ⊥ :=
  (GramMat.canGram_det_ne_zero_iff (vacVec_ne_zero (1 : ℂ)) (virasoroVOA_qp 1) 6
    (basis6 1)).mp det_canGram_six_ne_zero_at_one

/-- At central charge one, no nonzero weight-five state lies in the maximal
graded ideal. The computed canonical Gram determinant is nonzero there, so
passing to the simple quotient loses no states in this weight. -/
theorem maxIdealVir_one_inf_grading_five_eq_bot :
    QuotVOA.maxGradedIdeal (virasoroVOA (1 : ℂ)) ⊓ (virasoroVOA (1 : ℂ)).grading 5 = ⊥ :=
  (GramMat.canGram_det_ne_zero_iff (vacVec_ne_zero (1 : ℂ)) (virasoroVOA_qp 1) 5
    (basis5 1)).mp det_canGram_five_ne_zero_at_one

end VOA.VirSimpleGram
