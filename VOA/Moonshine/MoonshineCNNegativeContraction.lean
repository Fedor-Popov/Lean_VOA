import VOA.Moonshine.MoonshineCNPositiveContraction
import VOA.Examples.LatticeOppSignLocality

/-!
# Complex-frame lattice fields: NegativeContraction

Structural adaptation of `LatticeGenOppSign`.
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
open VOA.LatExp (kappa kappa_zero kappa_combine partB_reindex_gen kZ kZ_neg kZ_nonneg)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def generalContractionSum (α β : L.carrier) (N b : ℤ) : End ℂ (FockN (rank L)) :=
  ∑ i ∈ Finset.range (N.toNat + 1),
    kappa ((L.form α β : ℤ) : ℂ) i •
      (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (N - (i : ℤ)))


theorem generalContractionSum_range (α β : L.carrier) (N b : ℤ) (K : ℕ) (hK : N.toNat ≤ K) :
    generalContractionSum F α β N b
      = ∑ i ∈ Finset.range (K + 1),
          kappa ((L.form α β : ℤ) : ℂ) i •
            (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (N - (i : ℤ))) := by
  rw [generalContractionSum]
  refine Finset.sum_subset (by
    intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
  intro i _ hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [annihilationCoefficientZ_neg F β (show N - (i : ℤ) < 0 by omega), LinearMap.comp_zero, smul_zero]


theorem annihilation_creation_general_contraction (α β : L.carrier) (N : ℤ) (hN : 0 ≤ N)
    (b : ℤ) : (annihilationCoefficientZ F β N).comp (creationField F α b) = generalContractionSum F α β N b := by
  set PC : ℂ := ((L.form α β : ℤ) : ℂ) with hPCdef
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n → 0 ≤ N →
      (annihilationCoefficientZ F β N).comp (creationField F α b) = generalContractionSum F α β N b by
    exact H N.toNat N b le_rfl hN
  intro n
  induction n with
  | zero =>
    intro N b hN hN0
    have hN0' : N = 0 := by omega
    subst hN0'
    rw [generalContractionSum, annihilationCoefficientZ_zero, LinearMap.id_comp, Int.toNat_zero, Finset.sum_range_one]
    simp only [Nat.cast_zero, sub_zero, kappa_zero, one_smul, annihilationCoefficientZ_zero, LinearMap.comp_id]
  | succ n ih =>
    intro N b hN hN0
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall hN0
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
                kappa PC i • ((creationField F α (b - (i : ℤ))).comp
                    ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                  - PC • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                      (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))) := by
        intro r hr
        simp only [Finset.mem_range] at hr
        rw [ih (N - 1 - r) b (by omega) (by omega),
          generalContractionSum_range F α β (N - 1 - r) b N.toNat (by omega), endomorphism_comp_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.comp_smul,
          frameOscillator_creationField_reorder F α β r (b - (i : ℤ))
            (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))]
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
              kappa PC i • ((creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                - PC • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
            = kappa PC i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ)
              - PC • kappa PC i • (∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1)) := by
        intro i hi
        rw [show (∑ r ∈ Finset.range N.toNat,
              kappa PC i • ((creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ))))
                - PC • (creationField F α (b - (i : ℤ) - ((r : ℤ) + 1))).comp
                    (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
            = (∑ r ∈ Finset.range N.toNat,
                kappa PC i • (creationField F α (b - (i : ℤ))).comp
                  ((-(frameOscillator F β ((r : ℤ) + 1))).comp (annihilationCoefficientZ F β (N - 1 - r - (i : ℤ)))))
              - (∑ r ∈ Finset.range N.toNat,
                  PC • kappa PC i • op ((i : ℤ) + r + 1)) from by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_sub, smul_comm (kappa PC i) PC]
          rw [hop]; dsimp only
          rw [show b - (i : ℤ) - ((r : ℤ) + 1) = b - ((i : ℤ) + r + 1) from by ring,
            show N - 1 - (r : ℤ) - (i : ℤ) = N - ((i : ℤ) + r + 1) from by ring]]
        rw [← Finset.smul_sum, ← endomorphism_comp_sum, hMain i hi, ← Finset.smul_sum, ← Finset.smul_sum]
      rw [Finset.sum_congr rfl hcollapse, Finset.sum_sub_distrib, inv_smul_eq_iff₀ hNne, generalContractionSum]
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
              kappa PC i • ((N - (i : ℤ) : ℤ) : ℂ) • op (i : ℤ))
            = ∑ j ∈ Finset.range (N.toNat + 1),
                (kappa PC j * ((N - (j : ℤ) : ℤ) : ℂ)) • op (j : ℤ) from
          Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                PC • kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
            = ∑ j ∈ Finset.range (N.toNat + 1),
                (PC * ∑ i ∈ Finset.range j, kappa PC i) • op (j : ℤ) from by
          rw [← Finset.smul_sum,
            show (∑ i ∈ Finset.range (N.toNat + 1),
                    kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                = ∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
                    kappa PC i • (fun s : ℕ => op (s : ℤ)) (i + j + 1) from by
              rw [show (∑ i ∈ Finset.range (N.toNat + 1),
                        kappa PC i • ∑ r ∈ Finset.range N.toNat, op ((i : ℤ) + r + 1))
                    = ∑ i ∈ Finset.range (N.toNat + 1), ∑ r ∈ Finset.range N.toNat,
                        kappa PC i • op ((i : ℤ) + r + 1) from by
                  simp only [Finset.smul_sum]]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
              rw [show (i : ℤ) + (r : ℤ) + 1 = ((i + r + 1 : ℕ) : ℤ) from by push_cast; ring],
            partB_reindex_gen (fun s => op (s : ℤ)) N.toNat (kappa PC)
              (fun s hs => hopvanish (s : ℤ) (by exact_mod_cast hs)), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
      rw [show ((N : ℂ) • ∑ i ∈ Finset.range (N.toNat + 1),
                kappa PC i • (creationField F α (b - (i : ℤ))).comp (annihilationCoefficientZ F β (N - (i : ℤ))))
            = ∑ j ∈ Finset.range (N.toNat + 1), ((N : ℂ) * kappa PC j) • op (j : ℤ) from by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [smul_smul, hop]]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [← sub_smul]
      congr 1
      have hcomb := kappa_combine PC j
      push_cast
      push_cast at hcomb
      linear_combination -hcomb


theorem generalFieldContraction (α β : L.carrier) (a b : ℤ) (ha : a ≤ 0) :
    (annihilationField F β a).comp (creationField F α b)
      = ∑ m ∈ Finset.range ((-a).toNat + 1),
          kappa ((L.form α β : ℤ) : ℂ) m •
            (creationField F α (b - (m : ℤ))).comp (annihilationField F β (a + (m : ℤ))) := by
  rw [annihilationField_eq_annihilationCoefficientZ F β a, annihilation_creation_general_contraction F α β (-a) (by omega) b,
    generalContractionSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [annihilationField_eq_annihilationCoefficientZ F β (a + (m : ℤ)), show -(a + (m : ℤ)) = -a - (m : ℤ) from by ring]


theorem negativeFieldContraction (α β : L.carrier) (a q : ℤ)
    (Z : FockN (rank L)) :
    annihilationField F β a (creationField F α q Z)
      = ∑ᶠ m : ℤ, kZ ((L.form α β : ℤ) : ℂ) m •
          creationField F α (q - m) (annihilationField F β (a + m) Z) := by
  set PC : ℂ := ((L.form α β : ℤ) : ℂ) with hPCdef
  have hsub : (Function.support
      (fun m : ℤ => kZ PC m • creationField F α (q - m) (annihilationField F β (a + m) Z)))
      ⊆ (Finset.Icc (0 : ℤ) (-a) : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; exact hm (by rw [kZ_neg PC (by omega), zero_smul])
    · by_contra h
      rw [annihilationField_pos F β (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
        smul_zero] at hm
      exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  by_cases ha : a ≤ 0
  · have happ := DFunLike.congr_fun (generalFieldContraction F α β a q ha) Z
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply] at happ
    rw [happ]
    refine Finset.sum_nbij' (fun (i : ℕ) => (i : ℤ)) (fun (m : ℤ) => m.toNat) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro m hm; simp only [Finset.mem_Icc] at hm; exact Int.toNat_of_nonneg hm.1
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [kZ_nonneg PC (show (0 : ℤ) ≤ (i : ℤ) by positivity), Int.toNat_natCast]
  · push_neg at ha
    rw [annihilationField_pos F β ha, LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    simp only [Finset.mem_Icc] at hm
    rw [annihilationField_pos F β (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
      smul_zero]


end VOA.Moonshine.ConwayNorton
