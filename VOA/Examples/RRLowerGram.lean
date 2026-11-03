/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerPartition
import VOA.Examples.LeeYangSingular
import VOA.Examples.VirasoroSimple
import VOA.Examples.VirasoroVermaQuotientDimensions
import VOA.Classification.COne.VirComposition

/-!
# The residual as a Gram-rank statement for the Verma module `M(-22/5, 0)`

The proved local composition series (`Classification.COne.virLocalCompositionSeries`) applied to
the simple VOA `L(-22/5, 0)` gives `dim L_N = Σ_h A_h dim L(c,h)_{N-h}` with `A_0 = 1`, hence
`dim L_N ≥ dim L(c,0)_N = rank G_N`, where `G_N = vermaGramMatrix (-22/5) 0 N` is the explicit
`p(N) × p(N)` Shapovalov matrix of the Verma module (`vermaSimpleLevel_finrank_eq_gramRank`).

* `gramRank_le_finrank` — `rank G_N ≤ dim L(-22/5,0)_N`, proved.

The consequences for the Lee–Yang character (`rochaCaridi_of_gramRank`,
`leeYangRRLowerBound_of_gramRank`, `gramRank_le_rc`, `gramRank_eq_finrank_eq_rc`) are in
`RRLowerGramBound.lean` (they need `RRLowerReduction`, whose import closure
contains the `sl₂` coset / semi-infinite cohomology files, and this file is used by the Virasoro
classical-freeness theorem).

`LeeYangGramRankBound` is the Feigin–Fuchs radical bound for `M(-22/5,0)`: the
contravariant radical at level `N` has dimension `≤ p(N) - rc N`.  It has the same shape as
`Classification.COne.FFLower`'s `c = 1` radical bound, which was proved there by a determinant
comparison along a Kac curve.  It is proved outright downstream:
`VOA.RRLower.leeYangGramRankBound_holds` (`LYGramRank.lean`).
-/

namespace VOA.RRLower

open VOA.InverseDS.VirasoroVerma VOA.Classification.COne VOA.VirSimple VOA.LeeYang
open Finset

noncomputable section

/-- Proved: `leeYangGramRankBound_holds` (`LYGramRank.lean`).  The Feigin–Fuchs radical bound
for the Lee–Yang vacuum Verma module, as a rank bound on the explicit Shapovalov matrix:
`rc N ≤ rank (vermaGramMatrix (-22/5) 0 N)`. -/
def LeeYangGramRankBound : Prop :=
  ∀ N : ℕ, rc N ≤ ((vermaGramMatrix leeYangC 0 N).rank : ℤ)

/-- `dim L(c,0)_N` (the Verma radical quotient) is at most `dim` of the simple VOA's weight
space, at every central charge — by the local composition series with `A_0 = 1`. -/
theorem vermaSimpleLevel_finrank_le (c : ℂ) (N : ℕ) :
    Module.finrank ℂ (vermaSimpleLevel c 0 N) ≤
      Module.finrank ℂ ((virasoroSimple c).grading (N : ℤ)) := by
  let V := virasoroSimple c
  obtain ⟨A, hA⟩ := virLocalCompositionSeries V.centralCharge _ V.grading V.L V.isInternal
    V.finrank V.positivity (fun n v hv => V.L_zero_grading v hv)
    (VertexOperatorAlgebra.L_mem_grading V) V.L_virasoro
  have hc : V.centralCharge = c := virasoroSimple_centralCharge c
  rw [hc] at hA
  have hA0 : A 0 = 1 := by
    have h0 := hA 0
    rw [Nat.cast_zero, V.vacuum_grade, finrank_span_singleton (virasoroSimple_vacuum_ne_zero c)]
      at h0
    simpa [vermaSimpleLevel_zero_finrank] using h0.symm
  rw [hA N, Finset.sum_range_succ']
  simp only [hA0, one_mul, Nat.sub_zero]
  refine le_add_left (le_of_eq ?_)
  rw [Nat.cast_zero]

/-- **The Gram rank bounds the Lee–Yang weight spaces from below.** -/
theorem gramRank_le_finrank (N : ℕ) :
    (vermaGramMatrix leeYangC 0 N).rank ≤
      Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) := by
  rw [← vermaSimpleLevel_finrank_eq_gramRank]
  exact vermaSimpleLevel_finrank_le leeYangC N

end

end VOA.RRLower
