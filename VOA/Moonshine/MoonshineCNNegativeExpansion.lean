import VOA.Moonshine.MoonshineCNNegativeContraction

/-!
# Complex-frame lattice fields: NegativeExpansion

Structural adaptation of `LatticeGenOppExpand`.
The real positive frame is replaced by `ComplexLatticeFrame`; every contraction
uses its proved bilinear pairing. All coefficient rearrangements retain their
finite-support hypotheses. This module introduces no positivity assumption.
-/

set_option maxHeartbeats 1200000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen
open VOA.LatExp (kZ kZ_neg kZ_nonneg shear3g)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem normalOrderedFourField_sum_left (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    normalOrderedFourField F α β C D x = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      creationField F α p (creationField F β q
        (annihilationField F α (C - p) (annihilationField F β (D - q) x))) := by
  rw [normalOrderedFourField, finsum_curry _ (normalOrderedFourField_fourfold_support_finite F α β C D x)]


theorem normalOrderedFourField_right_inner_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      creationField F α p (creationField F β q
        (annihilationField F α (C - p) (annihilationField F β (D - q) x))))).Finite := by
  apply Set.Finite.subset (annihilation_shift_support_finite F β D x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (finsum_eq_zero_of_forall_eq_zero fun p => by rw [h, map_zero, map_zero, map_zero])


theorem negativeDressing_right_summand (α β : L.carrier) (c d p q : ℤ) (x : FockN (rank L)) :
    creationField F α p (annihilationField F α (c - p)
        (creationField F β q (annihilationField F β (d - q) x)))
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • creationField F α p
          (creationField F β (q - m)
            (annihilationField F α (c - p + m) (annihilationField F β (d - q) x))) := by
  rw [show (L.form α β : ℤ) = (L.form β α : ℤ) from form_symm L α β]
  rw [negativeFieldContraction F β α (c - p) q (annihilationField F β (d - q) x)]
  rw [map_finsum (creationField F α p)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (p - c))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [annihilationField_pos F α (show (0 : ℤ) < c - p + m by omega),
          LinearMap.zero_apply, map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ ((L.form β α : ℤ) : ℂ) m • creationField F β (q - m)
          (annihilationField F α (c - p + m) (annihilationField F β (d - q) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul]


noncomputable def negativeTripleRight (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (qpm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) qpm.2.2 • creationField F α qpm.2.1
    (creationField F β (qpm.1 - qpm.2.2)
      (annihilationField F α (C - qpm.2.1 + qpm.2.2) (annihilationField F β (D - qpm.1) x)))


theorem negativeTripleRight_support_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (negativeTripleRight F α β C D x)).Finite := by
  set Sq := Function.support (fun q : ℤ => annihilationField F β (D - q) x) with hSq
  have hSqfin : Sq.Finite := annihilation_shift_support_finite F β D x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ q ∈ Sq, ⋃ m ∈ Set.Icc (0 : ℤ) q,
      (fun p : ℤ => (q, p, m)) ''
        Function.support (fun p : ℤ => annihilationField F α (C + m - p) (annihilationField F β (D - q) x))
    with hT
  have hTfin : T.Finite := by
    refine hSqfin.biUnion fun q _ => ?_
    refine (Set.finite_Icc (0 : ℤ) q).biUnion fun m _ => ?_
    exact (annihilation_shift_support_finite F α (C + m) (annihilationField F β (D - q) x)).image _
  apply Set.Finite.subset hTfin
  intro qpm hqpm
  obtain ⟨q, p, m⟩ := qpm
  rw [Function.mem_support, negativeTripleRight] at hqpm
  simp only at hqpm
  have hqS : q ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hqpm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hqpm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmq : m ≤ q := by
    by_contra h
    exact hqpm (by rw [creationField_neg F β (show q - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hpS : p ∈ Function.support
      (fun p : ℤ => annihilationField F α (C + m - p) (annihilationField F β (D - q) x)) := by
    rw [Function.mem_support]; intro h
    apply hqpm
    rw [show C - p + m = C + m - p from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨q, Set.mem_iUnion.mpr ⟨hqS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmq⟩, Set.mem_image_of_mem _ hpS⟩⟩⟩⟩


theorem dressingComposition_negative_right_expansion (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    dressingField F α c (dressingField F β d x)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • normalOrderedFourField F α β (c + m) (d - m) x := by
  rw [dressingComposition_sum_right]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        creationField F α p (annihilationField F α (c - p)
          (creationField F β q (annihilationField F β (d - q) x))))
      = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ᶠ m : ℤ, negativeTripleRight F α β c d x (q, p, m) from
    finsum_congr fun q => finsum_congr fun p => by rw [negativeDressing_right_summand F α β c d p q x]; rfl]
  rw [← finsum_curry₃ (negativeTripleRight F α β c d x) (negativeTripleRight_support_finite F α β c d x),
    ← finsum_comp_equiv shear3g (f := negativeTripleRight F α β c d x),
    finsum_curry₃ _ ((negativeTripleRight_support_finite F α β c d x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, negativeTripleRight F α β c d x (shear3g (m, q', p)))
      = ∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • creationField F α p
          (creationField F β q' (annihilationField F α (c + m - p) (annihilationField F β (d - m - q') x)))
      from
    finsum_congr fun q' => finsum_congr fun p => by
      simp only [negativeTripleRight, shear3g, Equiv.coe_fn_mk]
      rw [show q' + m - m = q' from by ring, show c - p + m = c + m - p from by ring,
        show d - (q' + m) = d - m - q' from by ring]]
  rw [normalOrderedFourField_sum_right]
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m) (normalOrderedFourField_right_inner_finite F α β (c + m) (d - m) x)]
  refine finsum_congr fun q' => ?_
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m)
    (by
      apply Set.Finite.subset (annihilation_shift_support_finite F α (c + m)
        (annihilationField F β (d - m - q') x))
      intro p hp; rw [Function.mem_support] at hp ⊢
      intro h; exact hp (by rw [h, map_zero, map_zero])
    : (Function.support (fun p : ℤ =>
        creationField F α p (creationField F β q'
          (annihilationField F α (c + m - p) (annihilationField F β (d - m - q') x))))).Finite)]


theorem creationField_comm_apply (α β : L.carrier) (a b : ℤ) (Y : FockN (rank L)) :
    creationField F β b (creationField F α a Y) = creationField F α a (creationField F β b Y) := by
  have h := DFunLike.congr_fun (creationField_comm F α β a b) Y
  simpa only [LinearMap.comp_apply] using h.symm


theorem annihilationField_comm_apply (α β : L.carrier) (a b : ℤ) (Y : FockN (rank L)) :
    annihilationField F β b (annihilationField F α a Y) = annihilationField F α a (annihilationField F β b Y) := by
  have h := DFunLike.congr_fun (annihilationField_comm F α β a b) Y
  simpa only [LinearMap.comp_apply] using h.symm


theorem normalOrderedFourField_left_inner_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (fun p : ℤ => ∑ᶠ q : ℤ,
      creationField F α p (creationField F β q
        (annihilationField F α (C - p) (annihilationField F β (D - q) x))))).Finite := by
  apply Set.Finite.subset ((normalOrderedFourField_fourfold_support_finite F α β C D x).image Prod.fst)
  intro p hp
  rw [Function.mem_support] at hp
  obtain ⟨q, hq⟩ : ∃ q : ℤ,
      creationField F α p (creationField F β q
        (annihilationField F α (C - p) (annihilationField F β (D - q) x))) ≠ 0 := by
    by_contra hcon; push_neg at hcon
    exact hp (finsum_eq_zero_of_forall_eq_zero hcon)
  exact ⟨(p, q), Function.mem_support.mpr hq, rfl⟩


theorem dressingComposition_sum_left (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    dressingField F β d (dressingField F α c x) = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      creationField F β q (annihilationField F β (d - q)
        (creationField F α p (annihilationField F α (c - p) x))) := by
  rw [dressingField_apply_conv F α c x, map_finsum (dressingField F β d) (dressingConvolution_support_finite F α c x)]
  refine finsum_congr fun p => ?_
  rw [dressingField_apply_conv F β d]


theorem negativeDressing_left_summand (α β : L.carrier) (c d p q : ℤ) (x : FockN (rank L)) :
    creationField F β q (annihilationField F β (d - q)
        (creationField F α p (annihilationField F α (c - p) x)))
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • creationField F α (p - m)
          (creationField F β q
            (annihilationField F α (c - p) (annihilationField F β (d - q + m) x))) := by
  rw [negativeFieldContraction F α β (d - q) p (annihilationField F α (c - p) x)]
  rw [map_finsum (creationField F β q)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (q - d))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [annihilationField_pos F β (show (0 : ℤ) < d - q + m by omega),
          LinearMap.zero_apply, map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ ((L.form α β : ℤ) : ℂ) m • creationField F α (p - m)
          (annihilationField F β (d - q + m) (annihilationField F α (c - p) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul, creationField_comm_apply, annihilationField_comm_apply F]


noncomputable def negativeTripleLeft (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (pqm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) pqm.2.2 • creationField F α (pqm.1 - pqm.2.2)
    (creationField F β pqm.2.1
      (annihilationField F α (C - pqm.1) (annihilationField F β (D - pqm.2.1 + pqm.2.2) x)))


noncomputable def negativeTripleLeftOrdered (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) (pqm : ℤ × ℤ × ℤ) :
    FockN (rank L) :=
  kZ ((L.form α β : ℤ) : ℂ) pqm.2.2 • creationField F β pqm.2.1
    (creationField F α (pqm.1 - pqm.2.2)
      (annihilationField F β (D - pqm.2.1 + pqm.2.2) (annihilationField F α (C - pqm.1) x)))


theorem negativeTriple_left_reorder (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    negativeTripleLeft F α β C D x = negativeTripleLeftOrdered F α β C D x := by
  funext pqm
  obtain ⟨p, q, m⟩ := pqm
  simp only [negativeTripleLeft, negativeTripleLeftOrdered]
  rw [creationField_comm_apply, annihilationField_comm_apply F]


theorem negativeTriple_left_support_finite (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    (Function.support (negativeTripleLeft F α β C D x)).Finite := by
  rw [negativeTriple_left_reorder F]
  set Sp := Function.support (fun p : ℤ => annihilationField F α (C - p) x) with hSp
  have hSpfin : Sp.Finite := annihilation_shift_support_finite F α C x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ p ∈ Sp, ⋃ m ∈ Set.Icc (0 : ℤ) p,
      (fun q : ℤ => (p, q, m)) ''
        Function.support (fun q : ℤ => annihilationField F β (D + m - q) (annihilationField F α (C - p) x))
    with hT
  have hTfin : T.Finite := by
    refine hSpfin.biUnion fun p _ => ?_
    refine (Set.finite_Icc (0 : ℤ) p).biUnion fun m _ => ?_
    exact (annihilation_shift_support_finite F β (D + m) (annihilationField F α (C - p) x)).image _
  apply Set.Finite.subset hTfin
  intro pqm hpqm
  obtain ⟨p, q, m⟩ := pqm
  rw [Function.mem_support, negativeTripleLeftOrdered] at hpqm
  simp only at hpqm
  have hpS : p ∈ Sp := by
    rw [hSp, Function.mem_support]; intro h
    exact hpqm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hpqm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmp : m ≤ p := by
    by_contra h
    exact hpqm (by rw [creationField_neg F α (show p - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hqS : q ∈ Function.support
      (fun q : ℤ => annihilationField F β (D + m - q) (annihilationField F α (C - p) x)) := by
    rw [Function.mem_support]; intro h
    apply hpqm
    rw [show D - q + m = D + m - q from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨p, Set.mem_iUnion.mpr ⟨hpS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmp⟩, Set.mem_image_of_mem _ hqS⟩⟩⟩⟩


theorem dressingComposition_negative_left_expansion (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    dressingField F β d (dressingField F α c x)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • normalOrderedFourField F α β (c - m) (d + m) x := by
  rw [dressingComposition_sum_left]
  rw [show (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
        creationField F β q (annihilationField F β (d - q)
          (creationField F α p (annihilationField F α (c - p) x))))
      = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ, ∑ᶠ m : ℤ, negativeTripleLeft F α β c d x (p, q, m) from
    finsum_congr fun p => finsum_congr fun q => by rw [negativeDressing_left_summand F α β c d p q x]; rfl]
  rw [← finsum_curry₃ (negativeTripleLeft F α β c d x) (negativeTriple_left_support_finite F α β c d x),
    ← finsum_comp_equiv shear3g (f := negativeTripleLeft F α β c d x),
    finsum_curry₃ _ ((negativeTriple_left_support_finite F α β c d x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, negativeTripleLeft F α β c d x (shear3g (m, p', q)))
      = ∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, kZ ((L.form α β : ℤ) : ℂ) m • creationField F α p'
          (creationField F β q (annihilationField F α (c - m - p') (annihilationField F β (d + m - q) x)))
      from
    finsum_congr fun p' => finsum_congr fun q => by
      simp only [negativeTripleLeft, shear3g, Equiv.coe_fn_mk]
      rw [show p' + m - m = p' from by ring, show c - (p' + m) = c - m - p' from by ring,
        show d - q + m = d + m - q from by ring]]
  rw [normalOrderedFourField_sum_left]
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m) (normalOrderedFourField_left_inner_finite F α β (c - m) (d + m) x)]
  refine finsum_congr fun p' => ?_
  rw [smul_finsum' (kZ ((L.form α β : ℤ) : ℂ) m)
    (by
      apply Set.Finite.subset (annihilation_shift_support_finite F β (d + m)
        (annihilationField F α (c - m - p') x))
      intro q hq; rw [Function.mem_support] at hq ⊢
      intro h; exact hq (by
        rw [← annihilationField_comm_apply F α β (c - m - p') (d + m - q), h, map_zero, map_zero])
    : (Function.support (fun q : ℤ =>
        creationField F α p' (creationField F β q
          (annihilationField F α (c - m - p') (annihilationField F β (d + m - q) x))))).Finite)]


end VOA.Moonshine.ConwayNorton
