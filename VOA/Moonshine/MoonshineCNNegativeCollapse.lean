import VOA.Moonshine.MoonshineCNNegativeExpansion

/-!
# Complex-frame lattice fields: NegativeCollapse

Structural adaptation of `LatticeGenOppCollapse`.
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
open VOA.LatExp (kZ kZ_neg kZ_nonneg wt wt_kZ_conv wt_symm_even shear3g)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem binomialDifference_weight_reflection (P i : ℕ) (hi : i ≤ P) : wt P (P - i) = (-1 : ℂ) ^ P * wt P i := by
  rw [wt, wt, Nat.choose_symm hi, ← mul_assoc, ← pow_add,
    show P + i = (P - i) + 2 * i from by omega, pow_add, pow_mul]
  norm_num


theorem normalOrderedFourField_antidiag_shift_finite (Pn : ℕ) (α β : L.carrier) (u v c : ℤ) (p : FockN (rank L)) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) (s - c) • normalOrderedFourField F α β (u + s) (v - s) p)).Finite := by
  obtain ⟨B0, hB0⟩ := annihilationField_isField F β p
  apply Set.Finite.subset (Set.finite_Icc c (v - B0))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hs (by rw [kZ_neg _ (by omega), zero_smul])
  · by_contra h
    apply hs
    rw [normalOrderedFourField, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro pq
    by_cases hq : 0 ≤ pq.2
    · rw [hB0 ((v - s) - pq.2) (by omega), map_zero, map_zero, map_zero]
    · rw [creationField_neg F β (show pq.2 < 0 by omega), LinearMap.zero_apply, map_zero]


theorem normalOrderedFourField_vanishes_below_cutoff (α β : L.carrier) (C D : ℤ) (p : FockN (rank L))
    (B1 : ℤ) (hB1 : ∀ n : ℤ, n < B1 → annihilationField F α n p = 0) (hC : C < B1) :
    normalOrderedFourField F α β C D p = 0 := by
  rw [normalOrderedFourField, finsum_eq_zero_of_forall_eq_zero]
  intro pq
  by_cases hp1 : 0 ≤ pq.1
  · rw [← annihilationField_comm_apply F α β (C - pq.1) (D - pq.2) p,
      hB1 (C - pq.1) (by omega), map_zero, map_zero, map_zero]
  · rw [creationField_neg F α (show pq.1 < 0 by omega), LinearMap.zero_apply]


theorem normalOrderedFourField_antidiag_negshift_finite (Pn : ℕ) (α β : L.carrier) (u v c : ℤ)
    (p : FockN (rank L)) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - c) • normalOrderedFourField F α β (u + s) (v - s) p)).Finite := by
  obtain ⟨B1, hB1⟩ := annihilationField_isField F α p
  apply Set.Finite.subset (Set.finite_Icc (B1 - u) (-c))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [normalOrderedFourField_vanishes_below_cutoff F α β (u + s) (v - s) p B1 hB1 (by omega),
      smul_zero])
  · by_contra h
    exact hs (by rw [kZ_neg _ (by omega), zero_smul])


theorem negativeDressing_right_difference (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (u v : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • dressingField F α (u + (i : ℤ)) (dressingField F β (v - (i : ℤ)) p))
      = normalOrderedFourField F α β u v p := by
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      dressingField F α (u + (i : ℤ)) (dressingField F β (v - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p := by
    intro i _
    rw [dressingComposition_negative_right_expansion F α β (u + (i : ℤ)) (v - (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.addRight (i : ℤ))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) (s - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.coe_addRight]
    rw [show s + (i : ℤ) - (i : ℤ) = s from by ring,
      show u + (i : ℤ) + s = u + (s + (i : ℤ)) from by ring,
      show v - (i : ℤ) - s = v - (s + (i : ℤ)) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (normalOrderedFourField_antidiag_shift_finite F Pn α β u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm L (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p)
      (fun i _ => (normalOrderedFourField_antidiag_shift_finite F Pn α β u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • normalOrderedFourField F α β (u + s) (v - s) p from
      finsum_congr fun s => by rw [← Finset.sum_smul, ← wt_kZ_conv Pn s]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]


theorem negativeDressing_left_difference (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (u v : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • dressingField F β (v + (i : ℤ)) (dressingField F α (u - (i : ℤ)) p))
      = normalOrderedFourField F α β u v p := by
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      dressingField F β (v + (i : ℤ)) (dressingField F α (u - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p := by
    intro i _
    rw [dressingComposition_negative_left_expansion F α β (u - (i : ℤ)) (v + (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.subLeft (-(i : ℤ)))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.subLeft_apply]
    rw [show -(-(i : ℤ) - s) - (i : ℤ) = s from by ring,
      show u - (i : ℤ) - s = u + (-(i : ℤ) - s) from by ring,
      show v + (i : ℤ) + s = v - (-(i : ℤ) - s) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • normalOrderedFourField F α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (normalOrderedFourField_antidiag_negshift_finite F Pn α β u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm L (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p)
      (fun i _ => (normalOrderedFourField_antidiag_negshift_finite F Pn α β u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • normalOrderedFourField F α β (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • normalOrderedFourField F α β (u + s) (v - s) p from
      finsum_congr fun s => by
        rw [← Finset.sum_smul,
          show (if s = 0 then (1 : ℂ) else 0) = (if (-s) = 0 then (1 : ℂ) else 0) from by
            by_cases hs : s = 0 <;> simp [hs],
          ← wt_kZ_conv Pn (-s)]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]


theorem negativeDressing_reversed_difference (Pn : ℕ) (α β : L.carrier)
    (hP : ((L.form α β : ℤ) : ℂ) = -(Pn : ℂ)) (U V : ℤ) (p : FockN (rank L)) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • dressingField F β (V - (i : ℤ)) (dressingField F α (U + (i : ℤ)) p))
      = (-1 : ℂ) ^ Pn • normalOrderedFourField F α β (U + (Pn : ℤ)) (V - (Pn : ℤ)) p := by
  have hreindex :
      (∑ i ∈ Finset.range (Pn + 1),
          wt Pn i • dressingField F β (V - (i : ℤ)) (dressingField F α (U + (i : ℤ)) p))
        = ∑ i ∈ Finset.range (Pn + 1),
            (-1 : ℂ) ^ Pn • (wt Pn i • dressingField F β ((V - (Pn : ℤ)) + (i : ℤ))
              (dressingField F α ((U + (Pn : ℤ)) - (i : ℤ)) p)) := by
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
        binomialDifference_weight_reflection Pn i (by omega), smul_smul,
        show (-1 : ℂ) ^ Pn * ((-1 : ℂ) ^ Pn * wt Pn i) = wt Pn i from by
          rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num]
  rw [hreindex, ← Finset.smul_sum, negativeDressing_left_difference F Pn α β hP (U + (Pn : ℤ)) (V - (Pn : ℤ)) p]


end VOA.Moonshine.ConwayNorton
