import VOA.Moonshine.MoonshineCNHalfCommutation
import VOA.Examples.LatticeSameSignLocality

/-!
# Complex-frame lattice fields: PositiveContraction

Structural adaptation of `LatticeGenContraction`, `LatticeGenEEMaster`.
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
open VOA.LatExp (wC wC_vanish wC_combine wC_symm)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem endomorphism_sum_comp (L : IntegralLattice) {ι : Type*} (s : Finset ι) (F : ι → End ℂ (FockN (rank L)))
    (g : End ℂ (FockN (rank L))) : (∑ i ∈ s, F i).comp g = ∑ i ∈ s, (F i).comp g := by
  rw [← Module.End.mul_eq_comp, Finset.sum_mul]
  simp only [Module.End.mul_eq_comp]


theorem endomorphism_comp_sum (L : IntegralLattice) {ι : Type*} (s : Finset ι) (g : End ℂ (FockN (rank L)))
    (F : ι → End ℂ (FockN (rank L))) : g.comp (∑ i ∈ s, F i) = ∑ i ∈ s, g.comp (F i) := by
  rw [← Module.End.mul_eq_comp, Finset.mul_sum]
  simp only [Module.End.mul_eq_comp]


noncomputable def positiveContractionSum (α β : L.carrier) (P : ℕ) (N b : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ i ∈ Finset.range (N.toNat + 1),
    wC P i • (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (N - (i : ℤ)))


theorem positiveContractionSum_range (α β : L.carrier) (P : ℕ) (N b : ℤ) (K : ℕ) (hK : N.toNat ≤ K) :
    positiveContractionSum F α β P N b
      = ∑ i ∈ Finset.range (K + 1),
          wC P i • (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (N - (i : ℤ))) := by
  rw [positiveContractionSum]
  refine Finset.sum_subset (by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [annihilationCoefficientZ_neg F β (show N - (i : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]


theorem shiftedRangeSum_reindex (L : IntegralLattice) (P T : ℕ) (g : ℕ → End ℂ (FockN (rank L))) (hg : ∀ j, T < j → g j = 0) :
    (∑ i ∈ Finset.range (T + 1), wC P i • ∑ r ∈ Finset.range T, g (i + r + 1))
      = ∑ j ∈ Finset.range (T + 1), (∑ i ∈ Finset.range j, wC P i) • g j := by
  have hinner : ∀ i ∈ Finset.range (T + 1),
      (∑ r ∈ Finset.range T, g (i + r + 1))
        = ∑ j ∈ Finset.range (T + 1), if i < j then g j else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hdrop : (∑ r ∈ Finset.range T, g (i + r + 1))
        = ∑ r ∈ Finset.range (T - i), g (i + r + 1) := by
      refine (Finset.sum_subset (by
        intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro r _ hr; simp only [Finset.mem_range, not_lt] at hr
      exact hg (i + r + 1) (by omega)
    rw [hdrop, ← Finset.sum_filter]
    refine Finset.sum_nbij' (i := fun r => i + r + 1) (j := fun j => j - i - 1) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_range] at hr
      simp only [Finset.mem_filter, Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_range]; omega
    · intro r hr; simp only [Finset.mem_range] at hr; simp only []; omega
    · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj; simp only []; omega
    · intro r _; rfl
  rw [Finset.sum_congr rfl (fun i hi => by rw [hinner i hi])]
  rw [show (∑ i ∈ Finset.range (T + 1),
            wC P i • ∑ j ∈ Finset.range (T + 1), if i < j then g j else 0)
        = ∑ i ∈ Finset.range (T + 1), ∑ j ∈ Finset.range (T + 1),
            (if i < j then wC P i • g j else 0) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hc : i < j
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc, smul_zero]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [Finset.sum_smul, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega


theorem annihilation_creation_positive_contraction (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (N b : ℤ) : (annihilationCoefficientZ F β N).comp (creationField F α b) = positiveContractionSum F α β P N b := by
  have hPC : ((L.form α β : ℤ) : ℂ) = (P : ℂ) := by rw [← hP]; push_cast; ring
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n →
      (annihilationCoefficientZ F β N).comp (creationField F α b) = positiveContractionSum F α β P N b by
    exact H N.toNat N b le_rfl
  intro n
  induction n with
  | zero =>
    intro N b hN
    rw [positiveContractionSum]
    by_cases h0 : N = 0
    · subst h0
      rw [annihilationCoefficientZ_zero, LinearMap.id_comp, show (0 : ℤ).toNat + 1 = 1 from rfl,
        Finset.sum_range_one, wC, pow_zero, Nat.choose_zero_right]
      simp only [Nat.cast_one, mul_one, one_smul, Nat.cast_zero, sub_zero, annihilationCoefficientZ_zero,
        LinearMap.comp_id]
    · rw [annihilationCoefficientZ_neg F β (by omega : N < 0), LinearMap.zero_comp,
        show N.toNat + 1 = 1 from by omega, Finset.sum_range_one,
        annihilationCoefficientZ_neg F β (show N - ((0 : ℕ) : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]
  | succ n ih =>
    intro N b hN
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      set op : ℤ → End ℂ (FockN (rank L)) :=
        fun j => (creationField F α (b - j)).comp (annihilationCoefficientZ F β (N - j)) with hop
      have hopvanish : ∀ j : ℤ, N.toNat < j → op j = 0 := fun j hj => by
        rw [hop]; dsimp only
        rw [annihilationCoefficientZ_neg F β (show N - j < 0 by omega), LinearMap.comp_zero]
      have hLHS : (annihilationCoefficientZ F β N).comp (creationField F α b)
          = (N : ℂ)⁻¹ • ∑ r ∈ Finset.range N.toNat,
              (-(frameOscillator F β ((r : ℤ) + 1))).comp
                ((annihilationCoefficientZ F β (N - 1 - r)).comp (creationField F α b)) := by
        rw [annihilationCoefficientZ_recursion F β N hN1, LinearMap.smul_comp, endomorphism_sum_comp]
        simp only [LinearMap.comp_assoc]
      have hexp : ∀ r ∈ Finset.range N.toNat,
          (-(frameOscillator F β ((r : ℤ) + 1))).comp
              ((annihilationCoefficientZ F β (N - 1 - r)).comp (creationField F α b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                wC P i • ((creationField F α (b - (i : ℤ))).comp
                    ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                  - (P : ℂ) • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                      (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))) := by
        intro r hr
        simp only [Finset.mem_range] at hr
        rw [ih (N - 1 - r) b (by omega), positiveContractionSum_range F α β P (N - 1 - r) b N.toNat (by omega),
          endomorphism_comp_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.comp_smul,
          frameOscillator_creationField_reorder F α β r (b - (i : ℤ))
            (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))), hPC]
      
      have hMain : ∀ i ∈ Finset.range (N.toNat + 1),
          (creationField F α (b - (i : ℤ))).comp
              (∑ r ∈ Finset.range N.toNat,
                (-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
            = ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [show (∑ r ∈ Finset.range N.toNat,
                (-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
              = ∑ r ∈ Finset.range N.toNat,
                (-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β ((N - i) - 1 - r)) from
            Finset.sum_congr rfl fun r _ => by
              rw [show (N : ℤ) - 1 - r - (i : ℤ) = (N - i) - 1 - r from by ring],
          annihilationCoefficientZ_sum_reassembly F β (N - i) N.toNat (by omega), LinearMap.comp_smul]
      
      rw [hLHS, Finset.sum_congr rfl hexp, Finset.sum_comm]
      have hcollapse : ∀ i ∈ Finset.range (N.toNat + 1),
          (∑ r ∈ Finset.range N.toNat,
              wC P i • ((creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                - (P : ℂ) • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
            = wC P i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ)
              - (P : ℂ) • wC P i • (∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1)) := by
        intro i hi
        rw [show (∑ r ∈ Finset.range N.toNat,
              wC P i • ((creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                - (P : ℂ) • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
            = (∑ r ∈ Finset.range N.toNat,
                wC P i • (creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
              - (∑ r ∈ Finset.range N.toNat,
                  (P : ℂ) • wC P i • op ((i : ℤ) + r + 1)) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_sub, smul_comm (wC P i) (P : ℂ)]
          rw [hop]; dsimp only
          rw [show b - (i : ℤ) - ((r : ℤ) + 1) = b - ((i : ℤ) + r + 1) from by ring,
            show N - 1 - (r : ℤ) - (i : ℤ) = N - ((i : ℤ) + r + 1) from by ring]]
        rw [← Finset.smul_sum, ← endomorphism_comp_sum, hMain i hi, ← Finset.smul_sum, ← Finset.smul_sum]
      rw [Finset.sum_congr rfl hcollapse, Finset.sum_sub_distrib, inv_smul_eq_iff₀ hNne, positiveContractionSum]
      
      rw [show (∑ i ∈ Finset.range (N.toNat + 1), wC P i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ))
            = ∑ j ∈ Finset.range (N.toNat + 1), (wC P j * ((N - (j : ℤ) : ℤ) : ℂ)) • op (j : ℤ) from
          Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                (P : ℂ) • wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((P : ℂ) * ∑ i ∈ Finset.range j, wC P i) • op (j : ℤ)
          from by
          rw [← Finset.smul_sum,
            show (∑ i ∈ Finset.range (N.toNat + 1),
                    wC P i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                = ∑ i ∈ Finset.range (N.toNat + 1),
                    wC P i • ∑ r ∈ Finset.range N.toNat, (fun s : ℕ => op (s : ℤ)) (i + r + 1) from
              Finset.sum_congr rfl fun i _ => congrArg (fun t => wC P i • t)
                (Finset.sum_congr rfl fun r _ => by
                  rw [show (i : ℤ) + (r : ℤ) + 1 = ((i + r + 1 : ℕ) : ℤ) from by push_cast; ring]),
            shiftedRangeSum_reindex L P N.toNat (fun s => op (s : ℤ))
              (fun j hj => hopvanish (j : ℤ) (by exact_mod_cast hj)), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      
      rw [show ((N : ℂ) • ∑ j ∈ Finset.range (N.toNat + 1),
                wC P j • (creationField F α (b - (j : ℤ))).comp (annihilationCoefficientZ F β (N - (j : ℤ))))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((N : ℂ) * wC P j) • op (j : ℤ) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul, hop]]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [← sub_smul]
      congr 1
      have hcomb := wC_combine P j
      push_cast
      push_cast at hcomb
      linear_combination -hcomb


theorem positiveFieldContraction (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β) (a b : ℤ) :
    (annihilationField F β a).comp (creationField F α b)
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • (creationField F α (b - (i : ℤ))).comp (annihilationField F β (a + (i : ℤ))) := by
  rw [annihilationField_eq_annihilationCoefficientZ F β a, annihilation_creation_positive_contraction F α β P hP (-a) b, positiveContractionSum]
  have hEqterm : ∀ i : ℕ, (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (-a - (i : ℤ)))
      = (creationField F α (b - (i : ℤ))).comp (annihilationField F β (a + (i : ℤ))) := fun i => by
    rw [annihilationField_eq_annihilationCoefficientZ F β (a + (i : ℤ)), show -(a + (i : ℤ)) = -a - (i : ℤ) from by ring]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hEqterm i])]
  set term : ℕ → End ℂ (FockN (rank L)) :=
    fun i => wC P i • (creationField F α (b - (i : ℤ))).comp (annihilationField F β (a + (i : ℤ)))
    with hterm
  have hvanA : ∀ i, (-a).toNat < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only
    rw [annihilationField_eq_annihilationCoefficientZ F β (a + (i : ℤ)),
      annihilationCoefficientZ_neg F β (show -(a + (i : ℤ)) < 0 by omega), LinearMap.comp_zero, smul_zero]
  have hvanP : ∀ i, P < i → term i = 0 := fun i hi => by
    rw [hterm]; dsimp only; rw [wC_vanish hi, zero_smul]
  set K := max (P + 1) ((-a).toNat + 1) with hK
  rw [show (∑ i ∈ Finset.range ((-a).toNat + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanA i (by omega))),
    show (∑ i ∈ Finset.range (P + 1), term i) = ∑ i ∈ Finset.range K, term i from
      (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
        (fun i _ hi => by simp only [Finset.mem_range, not_lt] at hi; exact hvanP i (by omega)))]


theorem annihilationField_pos (α : L.carrier) {t : ℤ} (ht : 0 < t) : annihilationField F α t = 0 := by
  rw [annihilationField_apply, if_neg (by omega)]


theorem annihilation_shift_support_finite (α : L.carrier) (b : ℤ) (y : FockN (rank L)) :
    (Function.support (fun q : ℤ => annihilationField F α (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := annihilationField_isField F α y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hq (by rw [annihilationField_pos F α (show 0 < b - q by omega)]; rfl)
  · by_contra h; exact hq (hB0 (b - q) (by omega))


theorem doubleAnnihilation_support_finite (α β : L.carrier) (a b : ℤ) (x : FockN (rank L)) :
    (Function.support
      (fun pq : ℤ × ℤ => annihilationField F α (a - pq.1) (annihilationField F β (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => annihilationField F β (b - q) x) with hSq
  have hSqfin : Sq.Finite := annihilation_shift_support_finite F β b x
  set Pr := ⋃ q ∈ Sq, Function.support
    (fun p : ℤ => annihilationField F α (a - p) (annihilationField F β (b - q) x)) with hP
  have hPfin : Pr.Finite := hSqfin.biUnion (fun q _ => annihilation_shift_support_finite F α a _)
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h; exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)


theorem normalOrderedFourField_fourfold_support_finite (α β : L.carrier) (a b : ℤ) (x : FockN (rank L)) :
    (Function.support
      (fun pq : ℤ × ℤ => creationField F α pq.1 (creationField F β pq.2
        (annihilationField F α (a - pq.1) (annihilationField F β (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (doubleAnnihilation_support_finite F α β a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h; exact hpq (by rw [h, map_zero, map_zero])


theorem normalOrderedFourField_sum_right (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    normalOrderedFourField F α β C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      creationField F α p (creationField F β q
        (annihilationField F α (C - p) (annihilationField F β (D - q) x))) := by
  rw [normalOrderedFourField, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ =>
        creationField F α pq.1 (creationField F β pq.2
          (annihilationField F α (C - pq.1) (annihilationField F β (D - pq.2) x))))]
  rw [finsum_curry _ ((normalOrderedFourField_fourfold_support_finite F α β C D x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]


theorem dressingConvolution_support_finite (α : L.carrier) (s : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => creationField F α q (annihilationField F α (s - q) x))).Finite := by
  apply Set.Finite.subset (annihilation_shift_support_finite F α s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])


theorem dressingField_apply_conv (α : L.carrier) (s : ℤ) (x : FockN (rank L)) :
    dressingField F α s x = ∑ᶠ m : ℤ, creationField F α m (annihilationField F α (s - m) x) := by
  rw [dressingField, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, creationField_neg F α (show m < 0 by omega)]; simp


theorem dressingComposition_sum_right (α β : L.carrier) (c d : ℤ) (x : FockN (rank L)) :
    dressingField F α c (dressingField F β d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      creationField F α p (annihilationField F α (c - p)
        (creationField F β q (annihilationField F β (d - q) x))) := by
  rw [dressingField_apply_conv F β d x, map_finsum (dressingField F α c) (dressingConvolution_support_finite F β d x)]
  refine finsum_congr fun q => ?_
  rw [dressingField_apply_conv F α c]


theorem finsum_finset_sum_comm (L : IntegralLattice) {ι : Type*} (s : Finset ι) (g : ι → ℤ → FockN (rank L))
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


theorem innerDressing_positive_reorder (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (c d p q : ℤ) (x : FockN (rank L)) :
    creationField F α p (annihilationField F α (c - p)
        (creationField F β q (annihilationField F β (d - q) x)))
      = ∑ i ∈ Finset.range (P + 1),
          wC P i • creationField F α p (creationField F β (q - (i : ℤ))
            (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))) := by
  have h := DFunLike.congr_fun (positiveFieldContraction F β α P (by rw [form_symm L β α]; exact hP) (c - p) q)
    (annihilationField F β (d - q) x)
  rw [LinearMap.sum_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]


theorem dressingReorder_summand (α β : L.carrier) (c d : ℤ) (i : ℕ) (x : FockN (rank L)) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        creationField F α p (creationField F β (q - (i : ℤ))
          (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))))
      = normalOrderedFourField F α β (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [normalOrderedFourField_sum_right,
    ← finsum_comp_equiv (Equiv.addRight (i : ℤ))
      (f := fun q : ℤ =>
        ∑ᶠ p : ℤ, creationField F α p (creationField F β (q - (i : ℤ))
          (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  rw [show q + (i : ℤ) - (i : ℤ) = q from by ring,
    show c - p + (i : ℤ) = (c + (i : ℤ)) - p from by ring,
    show d - (q + (i : ℤ)) = (d - (i : ℤ)) - q from by ring]


theorem dressingReorder_left_support_finite (α β : L.carrier) (c d i q : ℤ) (x : FockN (rank L)) :
    (Function.support (fun p : ℤ =>
      creationField F α p (creationField F β (q - i)
        (annihilationField F α (c - p + i) (annihilationField F β (d - q) x))))).Finite := by
  apply Set.Finite.subset (annihilation_shift_support_finite F α (c + i) (annihilationField F β (d - q) x))
  intro p hp; rw [Function.mem_support] at hp ⊢
  intro h
  apply hp
  rw [show c - p + i = c + i - p from by ring, h, map_zero, map_zero]


theorem dressingReorder_right_support_finite (α β : L.carrier) (c d i : ℤ) (x : FockN (rank L)) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      creationField F α p (creationField F β (q - i)
        (annihilationField F α (c - p + i) (annihilationField F β (d - q) x))))).Finite := by
  apply Set.Finite.subset (annihilation_shift_support_finite F β d x)
  intro q hq; rw [Function.mem_support] at hq ⊢
  intro h
  refine hq (finsum_eq_zero_of_forall_eq_zero fun p => ?_)
  rw [h, map_zero, map_zero, map_zero]


theorem dressingComposition_positive_contraction (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (c d : ℤ) (x : FockN (rank L)) :
    dressingField F α c (dressingField F β d x)
      = ∑ i ∈ Finset.range (P + 1), wC P i • normalOrderedFourField F α β (c + (i : ℤ)) (d - (i : ℤ)) x := by
  rw [dressingComposition_sum_right]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            creationField F α p (annihilationField F α (c - p)
              (creationField F β q (annihilationField F β (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • creationField F α p (creationField F β (q - (i : ℤ))
              (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))) from
      finsum_congr fun q => finsum_congr fun p => innerDressing_positive_reorder F α β P hP c d p q x]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ i ∈ Finset.range (P + 1),
            wC P i • creationField F α p (creationField F β (q - (i : ℤ))
              (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ i ∈ Finset.range (P + 1), wC P i • ∑ᶠ p : ℤ,
            creationField F α p (creationField F β (q - (i : ℤ))
              (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x))) from
      finsum_congr fun q => by
        rw [finsum_finset_sum_comm L (Finset.range (P + 1))
          (fun i p => wC P i • creationField F α p (creationField F β (q - (i : ℤ))
            (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x)))
            ) (fun i _ => (dressingReorder_left_support_finite F α β c d (i : ℤ) q x).subset
              (fun p hp => by
                rw [Function.mem_support] at hp ⊢
                simp only [] at hp ⊢
                exact fun h => hp (by rw [h, smul_zero])))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_finsum' (wC P i) (dressingReorder_left_support_finite F α β c d (i : ℤ) q x)]]
  rw [finsum_finset_sum_comm L (Finset.range (P + 1))
      (fun i q => wC P i • ∑ᶠ p : ℤ, creationField F α p (creationField F β (q - (i : ℤ))
        (annihilationField F α (c - p + (i : ℤ)) (annihilationField F β (d - q) x)))
        ) (fun i _ => (dressingReorder_right_support_finite F α β c d (i : ℤ) x).subset
          (fun q hq => by
            rw [Function.mem_support] at hq ⊢
            simp only [] at hq ⊢
            exact fun h => hq (by rw [h, smul_zero])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_finsum' (wC P i) (dressingReorder_right_support_finite F α β c d (i : ℤ) x), dressingReorder_summand]


theorem dressingComposition_positive_swap (α β : L.carrier) (P : ℕ) (hP : (P : ℤ) = L.form α β)
    (a b : ℤ) (x : FockN (rank L)) :
    dressingField F α (a - P) (dressingField F β b x)
      = (-1 : ℂ) ^ P • dressingField F β (b - P) (dressingField F α a x) := by
  rw [dressingComposition_positive_contraction F α β P hP (a - P) b x,
    dressingComposition_positive_contraction F β α P (by rw [form_symm L β α]; exact hP) (b - P) a x, Finset.smul_sum]
  rw [show (∑ i ∈ Finset.range (P + 1),
            (-1 : ℂ) ^ P • wC P i • normalOrderedFourField F β α (b - P + (i : ℤ)) (a - (i : ℤ)) x)
        = ∑ i ∈ Finset.range (P + 1),
            (-1 : ℂ) ^ P • wC P (P - i) •
              normalOrderedFourField F β α (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x from
      (Finset.sum_nbij' (i := fun i => P - i) (j := fun i => P - i)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i hi => by simp only [Finset.mem_range] at hi; simp only []; omega)
        (fun i _ => rfl)).symm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [wC_symm (by omega : i ≤ P),
    normalOrderedFourField_symm F β α (b - P + ((P - i : ℕ) : ℤ)) (a - ((P - i : ℕ) : ℤ)) x,
    show normalOrderedFourField F α β (a - ((P - i : ℕ) : ℤ)) (b - P + ((P - i : ℕ) : ℤ)) x
        = normalOrderedFourField F α β (a - P + (i : ℤ)) (b - (i : ℤ)) x from by
      rw [show a - ((P - i : ℕ) : ℤ) = a - P + (i : ℤ) from by omega,
        show b - P + ((P - i : ℕ) : ℤ) = b - (i : ℤ) from by omega]]
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num


end VOA.Moonshine.ConwayNorton
