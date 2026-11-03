/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenContraction

/-!
# The four-fold re-summation `eeMaster_P` of the general lattice VOA

The binomial re-summation `EE(α,c)EE(β,d) = ∑_{i=0}^{P} (-1)^i C(P,i) · T_{α,β}(c+i,d-i)` (`P=⟨α,β⟩`),
the same-sign locality core.  Cross-charge lift of A₁'s `eeMaster_P` (`LatticeSameSignLocality`),
built on the proved `contr_P` (the binomial contraction) and `TvVec` (the four-fold), reusing the
charge-agnostic finsum machinery.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (wC wC_vanish wC_combine wC_symm)

variable (L : IntegralLattice)

/-! ## Support finiteness -/

theorem EplusVecField_pos (α : L.carrier) {t : ℤ} (ht : 0 < t) : EplusVecField L α t = 0 := by
  rw [EplusVecField_apply, if_neg (by omega)]

/-- For fixed `b`, `q ↦ E⁺(α)_{b-q} y` has finite support. -/
theorem EpVec_shift_support_finite (α : L.carrier) (b : ℤ) (y : FockN (rank L)) :
    (Function.support (fun q : ℤ => EplusVecField L α (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusVecField_isField L α y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hq (by rw [EplusVecField_pos L α (show 0 < b - q by omega)]; rfl)
  · by_contra h; exact hq (hB0 (b - q) (by omega))

/-- The double `E⁺E⁺` shift has finite support. -/
theorem EpEpVec_support_finite (α β : L.carrier) (a b : ℤ) (x : FockN (rank L)) :
    (Function.support
      (fun pq : ℤ × ℤ => EplusVecField L α (a - pq.1) (EplusVecField L β (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusVecField L β (b - q) x) with hSq
  have hSqfin : Sq.Finite := EpVec_shift_support_finite L β b x
  set Pr := ⋃ q ∈ Sq, Function.support
    (fun p : ℤ => EplusVecField L α (a - p) (EplusVecField L β (b - q) x)) with hP
  have hPfin : Pr.Finite := hSqfin.biUnion (fun q _ => EpVec_shift_support_finite L α a _)
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h; exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)

/-- The cross four-fold has finite support. -/
theorem TvVec_fourfold_support_finite (α β : L.carrier) (a b : ℤ) (x : FockN (rank L)) :
    (Function.support
      (fun pq : ℤ × ℤ => EminusVecField L α pq.1 (EminusVecField L β pq.2
        (EplusVecField L α (a - pq.1) (EplusVecField L β (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (EpEpVec_support_finite L α β a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h; exact hpq (by rw [h, map_zero, map_zero])

/-- `TvVec` as a nested `q`-then-`p` double sum. -/
theorem TvVec_eq_nestQ (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    TvVec L α β C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusVecField L α p (EminusVecField L β q
        (EplusVecField L α (C - p) (EplusVecField L β (D - q) x))) := by
  rw [TvVec, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ =>
        EminusVecField L α pq.1 (EminusVecField L β pq.2
          (EplusVecField L α (C - pq.1) (EplusVecField L β (D - pq.2) x))))]
  rw [finsum_curry _ ((TvVec_fourfold_support_finite L α β C D x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

/-- The `EEVec`-defining marginal `q ↦ E⁻(α)_q E⁺(α)_{s-q} x` has finite support. -/
theorem EEVecMarg_finite (α : L.carrier) (s : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => EminusVecField L α q (EplusVecField L α (s - q) x))).Finite := by
  apply Set.Finite.subset (EpVec_shift_support_finite L α s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

/-- `EEVec` as the convolution finsum `∑ᶠ m, E⁻(α)_m E⁺(α)_{s-m}`. -/
theorem EEVec_apply_conv (α : L.carrier) (s : ℤ) (x : FockN (rank L)) :
    EEVec L α s x = ∑ᶠ m : ℤ, EminusVecField L α m (EplusVecField L α (s - m) x) := by
  rw [EEVec, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, EminusVecField_neg L α (show m < 0 by omega)]; simp

/-- The cross `EE`-nesting: `EEVec α c (EEVec β d x)` as a nested `q,p` double finsum. -/
theorem EEVec_nest_cross (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    EEVec L α c (EEVec L β d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusVecField L α p (EplusVecField L α (c - p)
        (EminusVecField L β q (EplusVecField L β (d - q) x))) := by
  rw [EEVec_apply_conv L β d x, map_finsum (EEVec L α c) (EEVecMarg_finite L β d x)]
  refine finsum_congr fun q => ?_
  rw [EEVec_apply_conv L α c]

/-! ## The four-fold re-summation -/

/-- Interchange a `finsum` with a `Finset.sum` (each summand finitely supported). -/
theorem finsum_finset_sum_comm {ι : Type*} (s : Finset ι) (g : ι → ℤ → FockN (rank L))
    (hg : ∀ i ∈ s, (Function.support (g i)).Finite) :
    (∑ᶠ q : ℤ, ∑ i ∈ s, g i q) = ∑ i ∈ s, ∑ᶠ q : ℤ, g i q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hga : (Function.support (g a)).Finite := hg a (Finset.mem_insert_self a s)
      have hgs : ∀ i ∈ s, (Function.support (g i)).Finite :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hsum_fin : (Function.support (fun q => ∑ i ∈ s, g i q)).Finite := by
        apply Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet s)
          (fun i _ => hgs i (by simpa using ‹i ∈ s›)))
        intro q hq; rw [Function.mem_support] at hq
        rw [Set.mem_iUnion]
        by_contra h
        exact hq (Finset.sum_eq_zero fun i hi => by
          by_contra hne
          exact h ⟨i, by rw [Set.mem_iUnion]; exact ⟨hi, Function.mem_support.mpr hne⟩⟩)
      rw [Finset.sum_insert ha, ← ih hgs]
      rw [show (fun q => ∑ i ∈ insert a s, g i q)
            = fun q => g a q + ∑ i ∈ s, g i q from
          funext fun q => by rw [Finset.sum_insert ha]]
      rw [finsum_add_distrib hga hsum_fin]

/-- The inner reorder via `contr_P`: swap the middle `E⁺(α)_{c-p} E⁻(β)_q` into the
`(P+1)`-term binomial sum. -/
theorem inner_reorder_P (hPos : L.PosDef) (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (c d p q : ℤ) (x : FockN (rank L)) :
    EminusVecField L α p (EplusVecField L α (c - p)
        (EminusVecField L β q (EplusVecField L β (d - q) x)))
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
            (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))) := by
  have h := DFunLike.congr_fun (contr_P L hPos β α P (by rw [form_symm L β α]; exact hP) (c - p) q)
    (EplusVecField L β (d - q) x)
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- The `i`-th resummed piece equals the shifted cross four-fold `TvVec (c+i) (d-i)`. -/
theorem termX_i (α β : L.carrier) (c d : ℤ) (i : ℕ) (x : FockN (rank L)) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
          (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))))
      = TvVec L α β (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [TvVec_eq_nestQ,
    ← finsum_comp_equiv (Equiv.addRight (i : ℤ))
      (f := fun q : ℤ =>
        ∑ᶠ p : ℤ, EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
          (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  rw [show q + (i : ℤ) - (i : ℤ) = q from by ring,
    show c - p + (i : ℤ) = (c + (i : ℤ)) - p from by ring,
    show d - (q + (i : ℤ)) = (d - (i : ℤ)) - q from by ring]

/-- Per-`i` `p`-support finiteness. -/
theorem eeVec_p_finite (α β : L.carrier) (c d i q : ℤ) (x : FockN (rank L)) :
    (Function.support (fun p : ℤ =>
      EminusVecField L α p (EminusVecField L β (q - i)
        (EplusVecField L α (c - p + i) (EplusVecField L β (d - q) x))))).Finite := by
  apply Set.Finite.subset (EpVec_shift_support_finite L α (c + i) (EplusVecField L β (d - q) x))
  intro p hp; rw [Function.mem_support] at hp ⊢
  intro h
  apply hp
  rw [show c - p + i = c + i - p from by ring, h, map_zero, map_zero]

/-- Per-`i` `q`-support finiteness for the outer sum. -/
theorem eeVec_q_finite (α β : L.carrier) (c d i : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      EminusVecField L α p (EminusVecField L β (q - i)
        (EplusVecField L α (c - p + i) (EplusVecField L β (d - q) x))))).Finite := by
  apply Set.Finite.subset (EpVec_shift_support_finite L β d x)
  intro q hq; rw [Function.mem_support] at hq ⊢
  intro h
  refine hq (finsum_eq_zero_of_forall_eq_zero fun p => ?_)
  rw [h, map_zero, map_zero, map_zero]

/-- **The cross four-fold re-summation** (same-sign): `EEVec α c (EEVec β d x) =
∑_{i=0}^{P} (-1)^i C(P,i) • TvVec α β (c+i) (d-i) x`, `P = ⟨α,β⟩`.  Cross-charge lift of A₁'s
`eeMaster_P`. -/
theorem eeMaster_P (hPos : L.PosDef) (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (c d : ℤ) (x : FockN (rank L)) :
    EEVec L α c (EEVec L β d x)
      = ∑ i ∈ Finset.range (P + 1), wC P i • TvVec L α β (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [EEVec_nest_cross]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            EminusVecField L α p (EplusVecField L α (c - p)
              (EminusVecField L β q (EplusVecField L β (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
              (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))) from
      finsum_congr fun q => finsum_congr fun p => inner_reorder_P L hPos α β P hP c d p q x]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
              (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ i ∈ Finset.range (P + 1), wC P i • ∑ᶠ p : ℤ,
            EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
              (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x))) from
      finsum_congr fun q => by
        rw [finsum_finset_sum_comm L (Finset.range (P + 1))
          (fun i p => wC P i • EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
            (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x)))
            ) (fun i _ => (eeVec_p_finite L α β c d (i : ℤ) q x).subset
              (fun p hp => by
                rw [Function.mem_support] at hp ⊢
                simp only [] at hp ⊢
                exact fun h => hp (by rw [h, smul_zero])))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_finsum' (wC P i) (eeVec_p_finite L α β c d (i : ℤ) q x)]]
  rw [finsum_finset_sum_comm L (Finset.range (P + 1))
      (fun i q => wC P i • ∑ᶠ p : ℤ, EminusVecField L α p (EminusVecField L β (q - (i : ℤ))
        (EplusVecField L α (c - p + (i : ℤ)) (EplusVecField L β (d - q) x)))
        ) (fun i _ => (eeVec_q_finite L α β c d (i : ℤ) x).subset
          (fun q hq => by
            rw [Function.mem_support] at hq ⊢
            simp only [] at hq ⊢
            exact fun h => hq (by rw [h, smul_zero])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_finsum' (wC P i) (eeVec_q_finite L α β c d (i : ℤ) x), termX_i]

/-- **The shifted cross-commutativity with the odd-pairing sign**:
`EEVec α (a-P) (EEVec β b x) = (-1)^P · EEVec β (b-P) (EEVec α a x)` for `P = ⟨α,β⟩`.  Unlike A₁
(where `P = 2mm'` is even, so the sign is `+1`), for a general lattice `P` may be **odd**, giving the
boson reordering sign `(-1)^P` that is cancelled by the cocycle asymmetry `latticeCocycle_swap_sign`
at the vertex-operator level. -/
theorem shift_comm_P (hPos : L.PosDef) (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (a b : ℤ) (x : FockN (rank L)) :
    EEVec L α (a - P) (EEVec L β b x)
      = (-1 : ℂ) ^ P • EEVec L β (b - P) (EEVec L α a x) := by
  rw [eeMaster_P L hPos α β P hP (a - P) b x,
    eeMaster_P L hPos β α P (by rw [form_symm L β α]; exact hP) (b - P) a x, Finset.smul_sum]
  rw [show (∑ i ∈ Finset.range (P + 1),
            (-1 : ℂ) ^ P • wC P i • TvVec L β α (b - P + (i : ℤ)) (a - (i : ℤ)) x)
        = ∑ i ∈ Finset.range (P + 1),
            (-1 : ℂ) ^ P • wC P (P - i) •
              TvVec L β α (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x from
      (Finset.sum_nbij' (i := fun i => P - i) (j := fun i => P - i)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i _ => rfl)).symm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [wC_symm (by omega : i ≤ P),
    TvVec_symm L hPos β α (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x,
    show TvVec L α β (a - ((P - i : ℕ) : ℤ)) (b - P + ((P - i : ℕ) : ℤ)) x
        = TvVec L α β (a - P + (i : ℤ)) (b - (i : ℤ)) x from by
      rw [show a - ((P - i : ℕ) : ℤ) = a - P + (i : ℤ) from by omega,
        show b - P + ((P - i : ℕ) : ℤ) = b - (i : ℤ) from by omega]]
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end VOA.LatGen
