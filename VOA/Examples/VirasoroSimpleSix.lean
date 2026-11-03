/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroSimpleGram
import VOA.Examples.VirasoroRigidityStructural

/-!
# `dim L(c,0)₆` **exactly**, at every level-6 degenerate charge

`Examples/VirasoroSimpleGram` gets as far as a strict inequality — `dim L(c₀,0)₆ < 4` at a root
of `det canGram6`.  That is all a *determinant* can give, and the file says so.  This file
computes the **rank** at each of the four roots and therefore the graded dimension itself.

## Why this is the step that matters

The bridge `Core/GradedFormMatrix.finrank_maxQuotient_grading` (D1) equates `dim L(W)ₙ` with a
**rank**, not with a determinant.  Everything upstream of here uses the determinant only as a
*detector* (`det = 0` ⇒ rank not full).  A determinant genuinely does not determine a rank, and
level 6 is the first level in this repository where that gap is visible: `det canGram6` has a
**double** root at `c = -22/5` and simple roots at `c = 1/2` and `c = -68/7`, and the ranks there
are `2`, `3`, `3` respectively.  Only the rank computation separates them.

## The four numbers, and the outside truth they reproduce

| `c` | model | `rank canGram6` | `dim L(c,0)₆` | independent check |
|---|---|---|---|---|
| `0` | `M(2,3)` | `0` | `0` | `L(0,0) = ℂ𝟙`, trivial in every positive degree |
| `1/2` | Ising `M(3,4)` | `3` | `3` | `q⁶` coefficient of the Ising vacuum character |
| `-22/5` | Lee–Yang `M(2,5)` | `2` | `2` | `q⁶` of `∑ qⁿ⁽ⁿ⁺¹⁾/(q)ₙ` (Rogers–Ramanujan) |
| `-68/7` | `M(2,7)` | `3` | `3` | first vacuum singular vector at level `(p-1)(q-1) = 6` |

against `dim V(c,0)₆ = 4` at every `c` (`finrank_gradingVir_six`).  None of these four numbers is
used anywhere in the derivation — they are all *outputs* of the Gram rank, checked afterwards
against characters known from outside the repository.

Level 5 is included for the same reason at `c = -22/5`, where `dim L(-22/5,0)₅ = 1` (the `q⁵`
coefficient of the same Rogers–Ramanujan series), against `dim V(c,0)₅ = 2`.

## The two techniques

* **Lower bound** `r ≤ rank`: exhibit an invertible `r × r` submatrix.  `Matrix.rank_submatrix_le`
  says a submatrix cannot have larger rank, and `Matrix.rank_of_isUnit` computes the rank of an
  invertible square matrix.
* **Upper bound**.  Two different arguments, and the difference is exactly the point of the file:
  * `rank < 4` from `det = 0`, via `GramMat.rank_canGram_lt_of_det_eq_zero` — enough when the
    corank is `1` (Ising, `M(2,7)`);
  * `rank ≤ 2` from an explicit **rank-2 factorisation** `canGram6 = P * Q` with `P` of width `2`
    (`Matrix.rank_mul_le_left`, `Matrix.rank_le_card_width`) — needed at Lee–Yang, where the
    determinant vanishes to order `2` and cannot see the difference between corank `1` and `2`.

## ⚠ Not claimed

Nothing here is uniform in `n`, and nothing here is a Kac determinant formula.  Each charge is a
separate finite computation over an explicit rational matrix.
-/

set_option linter.style.longLine false

namespace VOA.VirSimpleSix

open VOA VOA.LeeYang VOA.VirModule VOA.VirSimple
open VOA.VirGram56 VOA.VirSimpleGram
open VOA.VertexOperatorAlgebra
open Module (Basis finrank)

/-! ## §1  The two bridges from a matrix rank to a graded dimension -/

/-- At a level-6 degenerate charge the rank is below `4 = dim V(c,0)₆`.  This is the determinant
used as a *detector*; it does not say by how much. -/
theorem rank_canGram6_lt_four (c : ℂ) (h : (canGram6 c).det = 0) : (canGram6 c).rank < 4 := by
  have h' : (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 6 (basis6 c)).det = 0 := by
    rw [canGram_basis6]; exact h
  have hlt := GramMat.rank_canGram_lt_of_det_eq_zero (vacVec_ne_zero c) (virasoroVOA_qp c) 6
    (basis6 c) h'
  rw [canGram_basis6] at hlt
  have h6 : finrank ℂ ((virasoroVOA c).grading 6) = 4 := finrank_gradingVir_six c
  rwa [h6] at hlt

/-- The same at level 5, against `dim V(c,0)₅ = 2`. -/
theorem rank_canGram5_lt_two (c : ℂ) (h : (canGram5 c).det = 0) : (canGram5 c).rank < 2 := by
  have h' : (GramMat.canGram (vacVec_ne_zero c) (virasoroVOA_qp c) 5 (basis5 c)).det = 0 := by
    rw [canGram_basis5]; exact h
  have hlt := GramMat.rank_canGram_lt_of_det_eq_zero (vacVec_ne_zero c) (virasoroVOA_qp c) 5
    (basis5 c) h'
  rw [canGram_basis5] at hlt
  have h5 : finrank ℂ ((virasoroVOA c).grading 5) = 2 := finrank_gradingVir_five c
  rwa [h5] at hlt

/-- **D1, level 6, in the usable form**: a level-6 rank *is* the level-6 graded dimension of
the simple quotient. -/
theorem finrank_six_of_rank (c : ℂ) {k : ℕ} (h : (canGram6 c).rank = k) :
    finrank ℂ ((virasoroSimple c).grading 6) = k := by
  rw [finrank_virasoroSimple_grading c 6 (basis6 c), canGram_basis6]
  exact h

/-- The same at level 5. -/
theorem finrank_five_of_rank (c : ℂ) {k : ℕ} (h : (canGram5 c).rank = k) :
    finrank ℂ ((virasoroSimple c).grading 5) = k := by
  rw [finrank_virasoroSimple_grading c 5 (basis5 c), canGram_basis5]
  exact h

/-! ## §2  `c = 0`: the whole level-6 space is radical

`V(0,0)` has `L₀`-graded pieces of dimension `1,0,1,1,2,2,4,…` but its simple quotient is the
trivial vertex operator algebra `ℂ𝟙`.  The Gram matrix sees this at once: it is *identically
zero*, because every entry is a multiple of `c`. -/

/-- At central charge zero every weight-six canonical pairing vanishes.
The entire universal level-six space therefore lies in the pairing radical. -/
theorem canGram6_zero : canGram6 (0 : ℂ) = 0 := by
  rw [canGram6_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The zero pairing has rank zero, so it contributes no weight-six states
to the simple quotient after the radical is removed. -/
theorem rank_canGram6_zero : (canGram6 (0 : ℂ)).rank = 0 := by
  rw [canGram6_zero]
  simp

/-- `dim L(0,0)₆ = 0` — the simple quotient at `c = 0` has nothing in degree 6. -/
theorem finrank_virasoroSimple_six_zero :
    finrank ℂ ((virasoroSimple (0 : ℂ)).grading 6) = 0 :=
  finrank_six_of_rank 0 rank_canGram6_zero

/-! ## §3  Ising, `c = 1/2`: `dim L(1/2,0)₆ = 3` -/

/-- The level-6 matrix at the Ising charge, entrywise. -/
theorem canGram6_ising_eq :
    canGram6 isingC = !![(35/4 : ℂ), 5/2, 9, 12;
                          5/2, 37/8, 7, 105/8;
                          9, 7, 20, 15;
                          12, 105/8, 15, 1683/32] := by
  rw [canGram6_eq, isingC]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The leading `3 × 3` minor is `196 ≠ 0`, so the rank is at least `3`. -/
theorem three_le_rank_canGram6_ising : 3 ≤ (canGram6 isingC).rank := by
  have hsub : ((canGram6 isingC).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
      (![0, 1, 2] : Fin 3 → Fin 4)).rank ≤ (canGram6 isingC).rank :=
    Matrix.rank_submatrix_le _ _ _
  have hunit : IsUnit ((canGram6 isingC).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
      (![0, 1, 2] : Fin 3 → Fin 4)) := by
    have hE : (canGram6 isingC).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
        (![0, 1, 2] : Fin 3 → Fin 4)
        = !![(35/4 : ℂ), 5/2, 9; 5/2, 37/8, 7; 9, 7, 20] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [canGram6_ising_eq]
    rw [Matrix.isUnit_iff_isUnit_det, hE, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- **The Ising level-6 rank is `3`.**  The determinant has a *simple* root at `c = 1/2`, so
here the determinant and the rank agree; the content is the lower bound. -/
theorem rank_canGram6_ising : (canGram6 isingC).rank = 3 := by
  have hlt := rank_canGram6_lt_four isingC
    ((det_canGram6_eq_zero_iff isingC).mpr (Or.inr (Or.inl rfl)))
  have hge := three_le_rank_canGram6_ising
  omega

/-- **`dim L(1/2, 0)₆ = 3`.**  The `q⁶` coefficient of the Ising vacuum character, obtained
from the Gram rank alone — against `dim V(1/2,0)₆ = 4`. -/
theorem finrank_virasoroSimple_six_ising :
    finrank ℂ ((virasoroSimple isingC).grading 6) = 3 :=
  finrank_six_of_rank isingC rank_canGram6_ising

/-! ## §4  `M(2,7)`, `c = -68/7`: `dim L(-68/7,0)₆ = 3` -/

/-- Substituting the M(2,7) charge gives the exact four-by-four weight-six
pairing matrix. These rational entries support the rank calculation below. -/
theorem canGram6_m27_eq :
    canGram6 m27C = !![(-170 : ℂ), -340/7, -1224/7, -1632/7;
                        -340/7, 7752/49, -136, 9384/49;
                        -1224/7, -136, 19856/49, -2040/7;
                        -1632/7, 9384/49, -2040/7, 26928/343] := by
  rw [canGram6_eq, m27C]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The first three partition words have a nondegenerate pairing minor,
so at least three independent directions survive at weight six. -/
theorem three_le_rank_canGram6_m27 : 3 ≤ (canGram6 m27C).rank := by
  have hsub : ((canGram6 m27C).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
      (![0, 1, 2] : Fin 3 → Fin 4)).rank ≤ (canGram6 m27C).rank :=
    Matrix.rank_submatrix_le _ _ _
  have hunit : IsUnit ((canGram6 m27C).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
      (![0, 1, 2] : Fin 3 → Fin 4)) := by
    have hE : (canGram6 m27C).submatrix (![0, 1, 2] : Fin 3 → Fin 4)
        (![0, 1, 2] : Fin 3 → Fin 4)
        = !![(-170 : ℂ), -340/7, -1224/7; -340/7, 7752/49, -136;
              -1224/7, -136, 19856/49] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [canGram6_m27_eq]
    rw [Matrix.isUnit_iff_isUnit_det, hE, Matrix.det_fin_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- **The `M(2,7)` level-6 rank is `3`.** -/
theorem rank_canGram6_m27 : (canGram6 m27C).rank = 3 := by
  have hlt := rank_canGram6_lt_four m27C
    ((det_canGram6_eq_zero_iff m27C).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have hge := three_le_rank_canGram6_m27
  omega

/-- **`dim L(-68/7, 0)₆ = 3`.**  The `M(2,7)` vacuum module's first singular vector sits at
level `(p-1)(q-1) = 6`, and removes exactly one dimension. -/
theorem finrank_virasoroSimple_six_m27 :
    finrank ℂ ((virasoroSimple m27C).grading 6) = 3 :=
  finrank_six_of_rank m27C rank_canGram6_m27

/-! ## §5  Lee–Yang, `c = -22/5`: `dim L(-22/5,0)₆ = 2`

⚠ **This is the case a determinant cannot do.**  `det canGram6` vanishes to order `2` at
`c = -22/5`, but an order-2 vanishing is compatible with corank `1` as well as corank `2`.  The
upper bound `rank ≤ 2` therefore needs an explicit rank-2 factorisation, not the determinant. -/

/-- The exact weight-six pairing matrix at the Lee–Yang charge. Its rank
requires more than determinant vanishing, since there are two null directions. -/
theorem canGram6_leeYang_eq :
    canGram6 leeYangC = !![(-77 : ℂ), -22, -396/5, -528/5;
                            -22, 66/5, -308/5, -462/25;
                            -396/5, -308/5, -88/25, -132;
                            -528/5, -462/25, -132, -17226/125] := by
  rw [canGram6_eq, leeYangC]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The first two columns already span the column space: `canGram6 (-22/5) = P * Q` with `P` the
`4 × 2` matrix of those columns and `Q` the `2 × 4` matrix of coordinates. -/
theorem canGram6_leeYang_factor :
    canGram6 leeYangC
      = (!![(-77 : ℂ), -22; -22, 66/5; -396/5, -308/5; -528/5, -462/25] :
            Matrix (Fin 4) (Fin 2) ℂ)
        * (!![(1 : ℂ), 0, 8/5, 6/5; 0, 1, -2, 3/5] : Matrix (Fin 2) (Fin 4) ℂ) := by
  rw [canGram6_leeYang_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- ⚠ The upper bound that the determinant cannot supply. -/
theorem rank_canGram6_leeYang_le_two : (canGram6 leeYangC).rank ≤ 2 := by
  rw [canGram6_leeYang_factor]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using
    Matrix.rank_le_card_width
      (!![(-77 : ℂ), -22; -22, 66/5; -396/5, -308/5; -528/5, -462/25] :
        Matrix (Fin 4) (Fin 2) ℂ)

/-- The leading `2 × 2` minor is `-7502/5 ≠ 0`. -/
theorem two_le_rank_canGram6_leeYang : 2 ≤ (canGram6 leeYangC).rank := by
  have hsub : ((canGram6 leeYangC).submatrix (![0, 1] : Fin 2 → Fin 4)
      (![0, 1] : Fin 2 → Fin 4)).rank ≤ (canGram6 leeYangC).rank :=
    Matrix.rank_submatrix_le _ _ _
  have hunit : IsUnit ((canGram6 leeYangC).submatrix (![0, 1] : Fin 2 → Fin 4)
      (![0, 1] : Fin 2 → Fin 4)) := by
    have hE : (canGram6 leeYangC).submatrix (![0, 1] : Fin 2 → Fin 4)
        (![0, 1] : Fin 2 → Fin 4) = !![(-77 : ℂ), -22; -22, 66/5] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [canGram6_leeYang_eq]
    rw [Matrix.isUnit_iff_isUnit_det, hE, Matrix.det_fin_two_of]
    norm_num
  rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- **The Lee–Yang level-6 rank is `2`** — corank `2`, matching the order-2 vanishing of the
determinant, but *proved* rather than guessed from it. -/
theorem rank_canGram6_leeYang : (canGram6 leeYangC).rank = 2 :=
  le_antisymm rank_canGram6_leeYang_le_two two_le_rank_canGram6_leeYang

/-- **`dim L(-22/5, 0)₆ = 2`** — the `q⁶` coefficient of the Rogers–Ramanujan series
`∑_{n≥0} q^{n(n+1)}/(q)_n = 1 + q² + q³ + q⁴ + q⁵ + 2q⁶ + …`. -/
theorem finrank_virasoroSimple_six_leeYang :
    finrank ℂ ((virasoroSimple leeYangC).grading 6) = 2 :=
  finrank_six_of_rank leeYangC rank_canGram6_leeYang

/-! ## §6  Level 5 at Lee–Yang: `dim L(-22/5,0)₅ = 1` -/

/-- Substituting the Lee–Yang charge gives this explicit two-by-two
weight-five pairing matrix, whose entries retain their exact rational values. -/
theorem canGram5_leeYang_eq :
    canGram5 leeYangC = !![(-44 : ℂ), -88/5; -88/5, -176/25] := by
  rw [canGram5_eq, leeYangC]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The nonzero top-left pairing supplies an invertible one-by-one minor.
Thus at least one weight-five state survives in the simple quotient. -/
theorem one_le_rank_canGram5_leeYang : 1 ≤ (canGram5 leeYangC).rank := by
  have hsub : ((canGram5 leeYangC).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)).rank
      ≤ (canGram5 leeYangC).rank := Matrix.rank_submatrix_le _ _ _
  have hunit :
      IsUnit ((canGram5 leeYangC).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
    simp only [Matrix.submatrix_apply]
    rw [canGram5_leeYang_eq]
    norm_num
  rwa [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin] at hsub

/-- The determinant vanishes but one entry is nonzero, so the weight-five
pairing has rank exactly one: precisely one independent state survives. -/
theorem rank_canGram5_leeYang : (canGram5 leeYangC).rank = 1 := by
  have hlt := rank_canGram5_lt_two leeYangC
    ((det_canGram5_eq_zero_iff leeYangC).mpr (Or.inr rfl))
  have hge := one_le_rank_canGram5_leeYang
  omega

/-- **`dim L(-22/5, 0)₅ = 1`**, against `dim V(-22/5,0)₅ = 2`.  The `q⁵` coefficient of the
same Rogers–Ramanujan series. -/
theorem finrank_virasoroSimple_five_leeYang :
    finrank ℂ ((virasoroSimple leeYangC).grading 5) = 1 :=
  finrank_five_of_rank leeYangC rank_canGram5_leeYang

/-! ## §7  The jumps, as equalities of numbers

`Examples/VirasoroSimpleGram` proves `dim L(1/2,0)₆ < dim L(1,0)₆`.  With the ranks in hand the
comparison is exact, and the three degenerate charges are *separated from each other*: Lee–Yang
loses two dimensions at level 6, Ising and `M(2,7)` lose one. -/

/-- `dim L(-22/5,0)₆ = 2 < 3 = dim L(1/2,0)₆`.  Two charges, both degenerate at level 6, with
**different** graded dimensions — a distinction the level-6 determinant's zero *set* does not
record, only its rank does. -/
theorem finrank_six_leeYang_lt_ising :
    finrank ℂ ((virasoroSimple leeYangC).grading 6)
      < finrank ℂ ((virasoroSimple isingC).grading 6) := by
  rw [finrank_virasoroSimple_six_leeYang, finrank_virasoroSimple_six_ising]
  norm_num

/-- Ising and `M(2,7)` have the *same* level-6 graded dimension `3`, so level 6 does not
separate them; a genuine separation needs a higher level. -/
theorem finrank_six_ising_eq_m27 :
    finrank ℂ ((virasoroSimple isingC).grading 6)
      = finrank ℂ ((virasoroSimple m27C).grading 6) := by
  rw [finrank_virasoroSimple_six_ising, finrank_virasoroSimple_six_m27]

/-- No graded linear equivalence carries `L(-22/5,0)₆` onto `L(1/2,0)₆`. -/
theorem no_gradedEquiv_leeYang_ising :
    ¬ ∃ e : (VirUniv leeYangC ⧸ maxIdealVir leeYangC) ≃ₗ[ℂ] (VirUniv isingC ⧸ maxIdealVir isingC),
        ∀ x, x ∈ (virasoroSimple leeYangC).grading 6 ↔ e x ∈ (virasoroSimple isingC).grading 6 :=
  VirRigidStruct.no_gradedEquiv_of_finrank_ne _ _ (Nat.ne_of_lt finrank_six_leeYang_lt_ising)

end VOA.VirSimpleSix
