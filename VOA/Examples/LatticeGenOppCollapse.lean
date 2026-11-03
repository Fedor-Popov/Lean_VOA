/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenOppExpand

/-!
# The `Pn`-fold finite-difference collapse for `⟨α,β⟩ < 0`

The two OPE orderings (`hExpand1_gen`, `hExpand2_gen`), summed against the binomial weights
`wt Pn i`, both collapse to the SAME antidiagonal `TvVec α β u v p` (the kernel telescopes via
`wt_kZ_conv`).  For a general even lattice `Pn = -⟨α,β⟩` need NOT be even, so the reindexing
`i ↦ Pn - i` in `collapseR2_gen` picks up a sign `(-1)^{Pn}` (the general weight symmetry
`wt_symm_gen`).  That sign is exactly the cocycle asymmetry `ε(β,α) = (-1)^{Pn} ε(α,β)`, so the
opposite-sign bracket still cancels.  This is the FLM cocycle content the `A₁` lattice (even `Pn`)
never sees.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (kZ kZ_neg kZ_nonneg wt wt_kZ_conv wt_symm_even shear3g)

variable (L : IntegralLattice)

/-! ## The general binomial-weight symmetry `wt Pn (Pn - i) = (-1)^Pn • wt Pn i` -/

/-- **The general weight reflection** `wt P (P - i) = (-1)^P · wt P i` (any parity of `P`).  For
`P` even it reduces to `wt_symm_even`; the odd case carries the extra `-1` cancelled by the
cocycle. -/
theorem wt_symm_gen (P i : ℕ) (hi : i ≤ P) : wt P (P - i) = (-1 : ℂ) ^ P * wt P i := by
  rw [wt, wt, Nat.choose_symm hi, ← mul_assoc, ← pow_add,
    show P + i = (P - i) + 2 * i from by omega, pow_add, pow_mul]
  norm_num

/-! ## Antidiagonal finiteness of the collapsed `TvVec` sums -/

/-- The anti-diagonal `s`-support of `s ↦ kZ (-Pn) (s - c) • TvVec (u+s) (v-s) p` is finite. -/
theorem TvVec_antidiag_shift_finite (Pn : ℕ) (α β : L.carrier) (u v c : ℤ) (p : FockN (rank L)) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) (s - c) • TvVec L α β (u + s) (v - s) p)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusVecField_isField L β p
  apply Set.Finite.subset (Set.finite_Icc c (v - B0))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hs (by rw [kZ_neg _ (by omega), zero_smul])
  · by_contra h
    apply hs
    rw [TvVec, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro pq
    by_cases hq : 0 ≤ pq.2
    · rw [hB0 ((v - s) - pq.2) (by omega), map_zero, map_zero, map_zero]
    · rw [EminusVecField_neg L β (show pq.2 < 0 by omega), LinearMap.zero_apply, map_zero]

/-- `TvVec α β C D p` vanishes when `C` is below the `E⁺(α)`-field lower truncation of `p`:
commute `E⁺(α)_{C-p'}` to the innermost (applied to `p`) — forcing `C - p' ≥ B1(p)` with `p' ≥ 0`,
i.e. `C ≥ B1(p)`. -/
theorem TvVec_eq_zero_of_C_small (hPos : L.PosDef) (α β : L.carrier) (C D : ℤ) (p : FockN (rank L))
    (B1 : ℤ) (hB1 : ∀ n : ℤ, n < B1 → EplusVecField L α n p = 0) (hC : C < B1) :
    TvVec L α β C D p = 0 := by
  rw [TvVec, finsum_eq_zero_of_forall_eq_zero]
  intro pq
  by_cases hp1 : 0 ≤ pq.1
  · rw [← EplusVecField_comm_apply L hPos α β (C - pq.1) (D - pq.2) p,
      hB1 (C - pq.1) (by omega), map_zero, map_zero, map_zero]
  · rw [EminusVecField_neg L α (show pq.1 < 0 by omega), LinearMap.zero_apply]

/-- The reflected anti-diagonal `s`-support of `s ↦ kZ (-Pn) ((-s) - c) • TvVec (u+s) (v-s) p`
is finite. -/
theorem TvVec_antidiag_negshift_finite (hPos : L.PosDef) (Pn : ℕ) (α β : L.carrier) (u v c : ℤ)
    (p : FockN (rank L)) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - c) • TvVec L α β (u + s) (v - s) p)).Finite := by
  obtain ⟨B1, hB1⟩ := EplusVecField_isField L α p
  apply Set.Finite.subset (Set.finite_Icc (B1 - u) (-c))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [TvVec_eq_zero_of_C_small L hPos α β (u + s) (v - s) p B1 hB1 (by omega),
      smul_zero])
  · by_contra h
    exact hs (by rw [kZ_neg _ (by omega), zero_smul])

/-! ## The finite-difference collapses -/

/-- **The `Pn`-fold finite-difference collapse, left ordering** (`hExpand1_gen` + `wt_kZ_conv`). -/
theorem collapseL (hPos : L.PosDef) (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (u v : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • EEVec L α (u + (i : ℤ)) (EEVec L β (v - (i : ℤ)) p))
      = TvVec L α β u v p := by
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      EEVec L α (u + (i : ℤ)) (EEVec L β (v - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • TvVec L α β (u + s) (v - s) p := by
    intro i _
    rw [hExpand1_gen L hPos α β (u + (i : ℤ)) (v - (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.addRight (i : ℤ))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) (s - (i : ℤ)) • TvVec L α β (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.coe_addRight]
    rw [show s + (i : ℤ) - (i : ℤ) = s from by ring,
      show u + (i : ℤ) + s = u + (s + (i : ℤ)) from by ring,
      show v - (i : ℤ) - s = v - (s + (i : ℤ)) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • TvVec L α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • TvVec L α β (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (TvVec_antidiag_shift_finite L Pn α β u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm L (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • TvVec L α β (u + s) (v - s) p)
      (fun i _ => (TvVec_antidiag_shift_finite L Pn α β u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • TvVec L α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • TvVec L α β (u + s) (v - s) p from
      finsum_congr fun s => by rw [← Finset.sum_smul, ← wt_kZ_conv Pn s]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-- **The `Pn`-fold finite-difference collapse, right ordering** (`hExpand2_gen` + `wt_kZ_conv`). -/
theorem collapseR (hPos : L.PosDef) (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (u v : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • EEVec L β (v + (i : ℤ)) (EEVec L α (u - (i : ℤ)) p))
      = TvVec L α β u v p := by
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      EEVec L β (v + (i : ℤ)) (EEVec L α (u - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • TvVec L α β (u + s) (v - s) p := by
    intro i _
    rw [hExpand2_gen L hPos α β (u - (i : ℤ)) (v + (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.subLeft (-(i : ℤ)))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • TvVec L α β (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.subLeft_apply]
    rw [show -(-(i : ℤ) - s) - (i : ℤ) = s from by ring,
      show u - (i : ℤ) - s = u + (-(i : ℤ) - s) from by ring,
      show v + (i : ℤ) + s = v - (-(i : ℤ) - s) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • TvVec L α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • TvVec L α β (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (TvVec_antidiag_negshift_finite L hPos Pn α β u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm L (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • TvVec L α β (u + s) (v - s) p)
      (fun i _ => (TvVec_antidiag_negshift_finite L hPos Pn α β u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • TvVec L α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • TvVec L α β (u + s) (v - s) p from
      finsum_congr fun s => by
        rw [← Finset.sum_smul,
          show (if s = 0 then (1 : ℂ) else 0) = (if (-s) = 0 then (1 : ℂ) else 0) from by
            by_cases hs : s = 0 <;> simp [hs],
          ← wt_kZ_conv Pn (-s)]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-- **The opposite-sign binomial collapse of the second ordering**, GENERAL parity: reindex
`i ↦ Pn - i` via `wt_symm_gen` (the `(-1)^Pn` factor comes out front).  Matches `collapseR`'s
`(v+i, u-i)` shape and collapses to `(-1)^Pn • TvVec (U+Pn) (V-Pn) p`. -/
theorem collapseR2_gen (hPos : L.PosDef) (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (U V : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • EEVec L β (V - (i : ℤ)) (EEVec L α (U + (i : ℤ)) p))
      = (-1 : ℂ) ^ Pn • TvVec L α β (U + (Pn : ℤ)) (V - (Pn : ℤ)) p := by
  have hreindex :
      (∑ i ∈ Finset.range (Pn + 1),
          wt Pn i • EEVec L β (V - (i : ℤ)) (EEVec L α (U + (i : ℤ)) p))
        = ∑ i ∈ Finset.range (Pn + 1),
            (-1 : ℂ) ^ Pn • (wt Pn i • EEVec L β ((V - (Pn : ℤ)) + (i : ℤ))
              (EEVec L α ((U + (Pn : ℤ)) - (i : ℤ)) p)) := by
    refine Finset.sum_nbij' (i := fun i => Pn - i) (j := fun i => Pn - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i hi; simp only [Finset.mem_range] at hi; simp only []; omega
    · intro i hi; simp only [Finset.mem_range] at hi; simp only []; omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      have hcast : ((Pn - i : ℕ) : ℤ) = (Pn : ℤ) - (i : ℤ) := by omega
      rw [show (V - (Pn : ℤ)) + ((Pn - i : ℕ) : ℤ) = V - (i : ℤ) from by rw [hcast]; ring,
        show (U + (Pn : ℤ)) - ((Pn - i : ℕ) : ℤ) = U + (i : ℤ) from by rw [hcast]; ring,
        wt_symm_gen Pn i (by omega), smul_smul,
        show (-1 : ℂ) ^ Pn * ((-1 : ℂ) ^ Pn * wt Pn i) = wt Pn i from by
          rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num]
  rw [hreindex, ← Finset.smul_sum, collapseR L hPos Pn α β hP (U + (Pn : ℤ)) (V - (Pn : ℤ)) p]

end VOA.LatGen
