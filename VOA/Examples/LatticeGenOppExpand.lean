/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenOppSign

/-!
# The master OPE expansions `hExpand1_gen`/`hExpand2_gen`

`EEVec α c (EEVec β d x) = ∑ᶠ_m kZ ⟨α,β⟩ m • TvVec α β (c+m) (d-m) x` (and the reflected ordering),
the `ι_z` generalization of the finite `eeMaster_P`, valid for **any** sign of `⟨α,β⟩`.  Cross-charge
lift of A₁'s `hExpand1_gen`/`hExpand2_gen`, built on the proved `EplusVec_EminusVec_geom` and the
four-fold `TvVec` (= `Wgen`), reusing the generic `shear3g`/`finsum_curry₃`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatExp (kZ kZ_neg kZ_nonneg shear3g)

variable (L : IntegralLattice)

/-! ## `TvVec`-nesting and inner finiteness -/

/-- `TvVec` as a nested `p`-then-`q` double sum. -/
theorem TvVec_eq_nestP (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    TvVec L α β C D x = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusVecField L α p (EminusVecField L β q
        (EplusVecField L α (C - p) (EplusVecField L β (D - q) x))) := by
  rw [TvVec, finsum_curry _ (TvVec_fourfold_support_finite L α β C D x)]

/-- The inner `q`-marginal of `TvVec` has finite support. -/
theorem TvVec_inner_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      EminusVecField L α p (EminusVecField L β q
        (EplusVecField L α (C - p) (EplusVecField L β (D - q) x))))).Finite := by
  apply Set.Finite.subset (EpVec_shift_support_finite L β D x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (finsum_eq_zero_of_forall_eq_zero fun p => by rw [h, map_zero, map_zero, map_zero])

/-! ## The first OPE expansion -/

/-- Per-term geometric expansion: contract the middle `E⁺(α)_{c-p} E⁻(β)_q` via
`EplusVec_EminusVec_geom`, pushing `E⁻(α)_p` inside the `m`-sum. -/
theorem term_geom_gen (hPos : L.PosDef) (α β : L.carrier) (c d p q : ℤ) (x : FockN (rank L)) :
    EminusVecField L α p (EplusVecField L α (c - p)
        (EminusVecField L β q (EplusVecField L β (d - q) x)))
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • EminusVecField L α p
          (EminusVecField L β (q - m)
            (EplusVecField L α (c - p + m) (EplusVecField L β (d - q) x))) := by
  rw [show (L.form α β : ℤ) = (L.form β α : ℤ) from form_symm L α β]
  rw [EplusVec_EminusVec_geom L hPos β α (c - p) q (EplusVecField L β (d - q) x)]
  rw [map_finsum (EminusVecField L α p)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (p - c))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusVecField_pos L α (show (0 : ℤ) < c - p + m by omega),
          LinearMap.zero_apply, map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ ((L.form β α : ℤ) : ℂ) m • EminusVecField L β (q - m)
          (EplusVecField L α (c - p + m) (EplusVecField L β (d - q) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul]

/-- The source body `G3gVec (q,p,m)` of the OPE triple sum. -/
noncomputable def G3gVec (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (qpm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) qpm.2.2 • EminusVecField L α qpm.2.1
    (EminusVecField L β (qpm.1 - qpm.2.2)
      (EplusVecField L α (C - qpm.2.1 + qpm.2.2) (EplusVecField L β (D - qpm.1) x)))

theorem G3gVec_support_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (G3gVec L α β C D x)).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusVecField L β (D - q) x) with hSq
  have hSqfin : Sq.Finite := EpVec_shift_support_finite L β D x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ q ∈ Sq, ⋃ m ∈ Set.Icc (0 : ℤ) q,
      (fun p : ℤ => (q, p, m)) ''
        Function.support (fun p : ℤ => EplusVecField L α (C + m - p) (EplusVecField L β (D - q) x))
    with hT
  have hTfin : T.Finite := by
    refine hSqfin.biUnion fun q _ => ?_
    refine (Set.finite_Icc (0 : ℤ) q).biUnion fun m _ => ?_
    exact (EpVec_shift_support_finite L α (C + m) (EplusVecField L β (D - q) x)).image _
  apply Set.Finite.subset hTfin
  intro qpm hqpm
  obtain ⟨q, p, m⟩ := qpm
  rw [Function.mem_support, G3gVec] at hqpm
  simp only at hqpm
  have hqS : q ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hqpm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hqpm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmq : m ≤ q := by
    by_contra h
    exact hqpm (by rw [EminusVecField_neg L β (show q - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hpS : p ∈ Function.support
      (fun p : ℤ => EplusVecField L α (C + m - p) (EplusVecField L β (D - q) x)) := by
    rw [Function.mem_support]; intro h
    apply hqpm
    rw [show C - p + m = C + m - p from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨q, Set.mem_iUnion.mpr ⟨hqS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmq⟩, Set.mem_image_of_mem _ hpS⟩⟩⟩⟩

/-- **The first OPE expansion**: `EEVec α c (EEVec β d x) = ∑ᶠ_m kZ ⟨α,β⟩ m • TvVec α β (c+m) (d-m) x`
(the `z₁`-dominant ordering).  Cross-charge lift of A₁'s `hExpand1_gen`. -/
theorem hExpand1_gen (hPos : L.PosDef) (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    EEVec L α c (EEVec L β d x)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • TvVec L α β (c + m) (d - m) x := by
  rw [EEVec_nest_cross]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        EminusVecField L α p (EplusVecField L α (c - p)
          (EminusVecField L β q (EplusVecField L β (d - q) x))))
      = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ᶠ m : ℤ, G3gVec L α β c d x (q, p, m) from
    finsum_congr fun q => finsum_congr fun p => by rw [term_geom_gen L hPos α β c d p q x]; rfl]
  rw [← finsum_curry₃ (G3gVec L α β c d x) (G3gVec_support_finite L α β c d x),
    ← finsum_comp_equiv shear3g (f := G3gVec L α β c d x),
    finsum_curry₃ _ ((G3gVec_support_finite L α β c d x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, G3gVec L α β c d x (shear3g (m, q', p)))
      = ∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • EminusVecField L α p
          (EminusVecField L β q' (EplusVecField L α (c + m - p) (EplusVecField L β (d - m - q') x)))
      from
    finsum_congr fun q' => finsum_congr fun p => by
      simp only [G3gVec, shear3g, Equiv.coe_fn_mk]
      rw [show q' + m - m = q' from by ring, show c - p + m = c + m - p from by ring,
        show d - (q' + m) = d - m - q' from by ring]]
  rw [TvVec_eq_nestQ]
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m) (TvVec_inner_finite L α β (c + m) (d - m) x)]
  refine finsum_congr fun q' => ?_
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m)
    (by
      apply Set.Finite.subset (EpVec_shift_support_finite L α (c + m)
        (EplusVecField L β (d - m - q') x))
      intro p hp; rw [Function.mem_support] at hp ⊢
      intro h; exact hp (by rw [h, map_zero, map_zero])
    : (Function.support (fun p : ℤ =>
        EminusVecField L α p (EminusVecField L β q'
          (EplusVecField L α (c + m - p) (EplusVecField L β (d - m - q') x))))).Finite)]

/-! ## The second OPE expansion (`z₂`-dominant ordering) -/

/-- Pointwise cross-charge creation-half commutation. -/
theorem EminusVecField_comm_apply (α β : L.carrier) (a b : ℤ) (Y : FockN (rank L)) :
    EminusVecField L β b (EminusVecField L α a Y) = EminusVecField L α a (EminusVecField L β b Y) := by
  have h := DFunLike.congr_fun (EminusVecField_comm L α β a b) Y
  simpa only [LinearMap.comp_apply] using h.symm

/-- Pointwise cross-charge annihilation-half commutation. -/
theorem EplusVecField_comm_apply (hPos : L.PosDef) (α β : L.carrier) (a b : ℤ) (Y : FockN (rank L)) :
    EplusVecField L β b (EplusVecField L α a Y) = EplusVecField L α a (EplusVecField L β b Y) := by
  have h := DFunLike.congr_fun (EplusVecField_comm L hPos α β a b) Y
  simpa only [LinearMap.comp_apply] using h.symm

/-- The inner `q`-marginal of `TvVec` (second, `p`-outer ordering) has finite support. -/
theorem TvVec_inner_finite_P (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (fun p : ℤ => ∑ᶠ q : ℤ,
      EminusVecField L α p (EminusVecField L β q
        (EplusVecField L α (C - p) (EplusVecField L β (D - q) x))))).Finite := by
  apply Set.Finite.subset ((TvVec_fourfold_support_finite L α β C D x).image Prod.fst)
  intro p hp
  rw [Function.mem_support] at hp
  obtain ⟨q, hq⟩ : ∃ q : ℤ,
      EminusVecField L α p (EminusVecField L β q
        (EplusVecField L α (C - p) (EplusVecField L β (D - q) x))) ≠ 0 := by
    by_contra hcon; push_neg at hcon
    exact hp (finsum_eq_zero_of_forall_eq_zero hcon)
  exact ⟨(p, q), Function.mem_support.mpr hq, rfl⟩

/-- `EEVec β d (EEVec α c x)` as a nested `p`-then-`q` double finsum (second ordering). -/
theorem EEVec_nest_cross2 (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    EEVec L β d (EEVec L α c x) = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusVecField L β q (EplusVecField L β (d - q)
        (EminusVecField L α p (EplusVecField L α (c - p) x))) := by
  rw [EEVec_apply_conv L α c x, map_finsum (EEVec L β d) (EEVecMarg_finite L α c x)]
  refine finsum_congr fun p => ?_
  rw [EEVec_apply_conv L β d]

/-- Per-term geometric expansion (second ordering): contract `E⁺(β)_{d-q} E⁻(α)_p` and reorder. -/
theorem term_geom2_gen (hPos : L.PosDef) (α β : L.carrier) (c d p q : ℤ) (x : FockN (rank L)) :
    EminusVecField L β q (EplusVecField L β (d - q)
        (EminusVecField L α p (EplusVecField L α (c - p) x)))
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • EminusVecField L α (p - m)
          (EminusVecField L β q
            (EplusVecField L α (c - p) (EplusVecField L β (d - q + m) x))) := by
  rw [EplusVec_EminusVec_geom L hPos α β (d - q) p (EplusVecField L α (c - p) x)]
  rw [map_finsum (EminusVecField L β q)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (q - d))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusVecField_pos L β (show (0 : ℤ) < d - q + m by omega),
          LinearMap.zero_apply, map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ ((L.form α β : ℤ) : ℂ) m • EminusVecField L α (p - m)
          (EplusVecField L β (d - q + m) (EplusVecField L α (c - p) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul, EminusVecField_comm_apply, EplusVecField_comm_apply L hPos]

/-- The source body `G3gVec' (p,q,m)` of the second OPE triple sum. -/
noncomputable def G3gVec' (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (pqm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) pqm.2.2 • EminusVecField L α (pqm.1 - pqm.2.2)
    (EminusVecField L β pqm.2.1
      (EplusVecField L α (C - pqm.1) (EplusVecField L β (D - pqm.2.1 + pqm.2.2) x)))

/-- The pre-reorder body, pointwise equal to `G3gVec'`. -/
noncomputable def G3gVecpre (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (pqm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) pqm.2.2 • EminusVecField L β pqm.2.1
    (EminusVecField L α (pqm.1 - pqm.2.2)
      (EplusVecField L β (D - pqm.2.1 + pqm.2.2) (EplusVecField L α (C - pqm.1) x)))

theorem G3gVec'_eq_pre (hPos : L.PosDef) (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    G3gVec' L α β C D x = G3gVecpre L α β C D x := by
  funext pqm
  obtain ⟨p, q, m⟩ := pqm
  simp only [G3gVec', G3gVecpre]
  rw [EminusVecField_comm_apply, EplusVecField_comm_apply L hPos]

theorem G3gVec'_support_finite (hPos : L.PosDef) (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (G3gVec' L α β C D x)).Finite := by
  rw [G3gVec'_eq_pre L hPos]
  set Sp := Function.support (fun p : ℤ => EplusVecField L α (C - p) x) with hSp
  have hSpfin : Sp.Finite := EpVec_shift_support_finite L α C x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ p ∈ Sp, ⋃ m ∈ Set.Icc (0 : ℤ) p,
      (fun q : ℤ => (p, q, m)) ''
        Function.support (fun q : ℤ => EplusVecField L β (D + m - q) (EplusVecField L α (C - p) x))
    with hT
  have hTfin : T.Finite := by
    refine hSpfin.biUnion fun p _ => ?_
    refine (Set.finite_Icc (0 : ℤ) p).biUnion fun m _ => ?_
    exact (EpVec_shift_support_finite L β (D + m) (EplusVecField L α (C - p) x)).image _
  apply Set.Finite.subset hTfin
  intro pqm hpqm
  obtain ⟨p, q, m⟩ := pqm
  rw [Function.mem_support, G3gVecpre] at hpqm
  simp only at hpqm
  have hpS : p ∈ Sp := by
    rw [hSp, Function.mem_support]; intro h
    exact hpqm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hpqm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmp : m ≤ p := by
    by_contra h
    exact hpqm (by rw [EminusVecField_neg L α (show p - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hqS : q ∈ Function.support
      (fun q : ℤ => EplusVecField L β (D + m - q) (EplusVecField L α (C - p) x)) := by
    rw [Function.mem_support]; intro h
    apply hpqm
    rw [show D - q + m = D + m - q from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨p, Set.mem_iUnion.mpr ⟨hpS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmp⟩, Set.mem_image_of_mem _ hqS⟩⟩⟩⟩

/-- **The second OPE expansion**: the `z₂`-dominant ordering. -/
theorem hExpand2_gen (hPos : L.PosDef) (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    EEVec L β d (EEVec L α c x)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • TvVec L α β (c - m) (d + m) x := by
  rw [EEVec_nest_cross2]
  rw [show (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
        EminusVecField L β q (EplusVecField L β (d - q)
          (EminusVecField L α p (EplusVecField L α (c - p) x))))
      = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ, ∑ᶠ m : ℤ, G3gVec' L α β c d x (p, q, m) from
    finsum_congr fun p => finsum_congr fun q => by rw [term_geom2_gen L hPos α β c d p q x]; rfl]
  rw [← finsum_curry₃ (G3gVec' L α β c d x) (G3gVec'_support_finite L hPos α β c d x),
    ← finsum_comp_equiv shear3g (f := G3gVec' L α β c d x),
    finsum_curry₃ _ ((G3gVec'_support_finite L hPos α β c d x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, G3gVec' L α β c d x (shear3g (m, p', q)))
      = ∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • EminusVecField L α p'
          (EminusVecField L β q (EplusVecField L α (c - m - p') (EplusVecField L β (d + m - q) x)))
      from
    finsum_congr fun p' => finsum_congr fun q => by
      simp only [G3gVec', shear3g, Equiv.coe_fn_mk]
      rw [show p' + m - m = p' from by ring, show c - (p' + m) = c - m - p' from by ring,
        show d - q + m = d + m - q from by ring]]
  rw [TvVec_eq_nestP]
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m) (TvVec_inner_finite_P L α β (c - m) (d + m) x)]
  refine finsum_congr fun p' => ?_
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m)
    (by
      apply Set.Finite.subset (EpVec_shift_support_finite L β (d + m)
        (EplusVecField L α (c - m - p') x))
      intro q hq; rw [Function.mem_support] at hq ⊢
      intro h; exact hq (by
        rw [← EplusVecField_comm_apply L hPos α β (c - m - p') (d + m - q), h, map_zero, map_zero])
    : (Function.support (fun q : ℤ =>
        EminusVecField L α p' (EminusVecField L β q
          (EplusVecField L α (c - m - p') (EplusVecField L β (d + m - q) x))))).Finite)]

end VOA.LatGen
