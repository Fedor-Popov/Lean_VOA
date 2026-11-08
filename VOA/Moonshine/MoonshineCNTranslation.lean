import VOA.Moonshine.MoonshineCNCurrentCharge
import VOA.Examples.HeisenbergNVOA
import VOA.Core.ReconstructionExistence

/-!
# Complex-frame lattice construction: Translation

Structural adaptation of `LatticeGenTranslation` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem scalar_commutator (L : IntegralLattice) (c : ℂ) (M X : End ℂ (LatModuleGen L)) :
    (c • M) * X - X * (c • M) = c • (M * X - X * M) := by
  rw [smul_mul_assoc, mul_smul_comm]; exact (smul_sub c (M * X) (X * M)).symm


noncomputable def momentumCoupling : End ℂ (LatModuleGen L) :=
  ∑ a : Fin (rank L), (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1))) * frameMomentum F a


noncomputable def frameTranslation : End ℂ (LatModuleGen L) :=
  LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) + momentumCoupling F


theorem frameTranslation_vacuum : frameTranslation F (latVacuumGen L) = 0 := by
  rw [frameTranslation, LinearMap.add_apply]
  have h1 : LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1))
      (latVacuumGen L) = 0 := by
    rw [latVacuumGen, latStateGen, LinearMap.rTensor_tmul,
      HeisenbergN.LvirN_vacuum (rank L) 1 (by norm_num : (-1 : ℤ) ≤ -1), TensorProduct.zero_tmul]
  have h2 : momentumCoupling F (latVacuumGen L) = 0 := by
    rw [momentumCoupling, LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Module.End.mul_apply, frameMomentum_vacuum, map_zero]
  rw [h1, h2, add_zero]


theorem rTensor_osc_comm_gen (L : IntegralLattice) (a c : Fin (rank L)) (s : ℤ) :
    (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)))
      = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • (1 : End ℂ (LatModuleGen L)) := by
  rw [currentN_apply, ← tensorEndomorphism_mul, ← tensorEndomorphism_mul, ← LinearMap.rTensor_sub,
    show oscN (rank L) 1 a (-1) * oscN (rank L) 1 c (-s - 1)
          - oscN (rank L) 1 c (-s - 1) * oscN (rank L) 1 a (-1)
        = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • LinearMap.id from by
      rw [oscN_comm]
      by_cases hac : a = c ∧ s = -2
      · rw [if_pos ⟨hac.1, by omega⟩, if_pos hac]; norm_num
      · rw [if_neg (fun h => hac ⟨h.1, by omega⟩), if_neg hac],
    LinearMap.rTensor_smul, LinearMap.rTensor_id]
  rfl


theorem momentumCoupling_comm_rTensor (c : Fin (rank L)) (s : ℤ) :
    momentumCoupling F * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * momentumCoupling F
      = (if s = -2 then (-1 : ℂ) else 0) • frameMomentum F c := by
  have hterm : ∀ a : Fin (rank L),
      (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) * frameMomentum F a)
          * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)
        - LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)
          * (LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) * frameMomentum F a)
      = (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • frameMomentum F a := by
    intro a
    set A := LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) with hA
    set B := LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s) with hB
    set Z := frameMomentum F a with hZ
    have hZB : Z * B = B * Z := frameMomentum_comm_rTensor F a (currentN (rank L) 1 c s)
    have hAB := rTensor_osc_comm_gen L a c s
    rw [← hA, ← hB] at hAB
    have e1 : (A * Z) * B - B * (A * Z) = (A * B - B * A) * Z := by
      rw [mul_assoc, hZB, ← mul_assoc, ← mul_assoc]
      exact (sub_mul (A * B) (B * A) Z).symm
    rw [e1, hAB, smul_mul_assoc, one_mul]
  rw [momentumCoupling, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun a _ => hterm a),
    show (∑ a : Fin (rank L), (if a = c ∧ s = -2 then (-1 : ℂ) else 0) • frameMomentum F a)
        = ∑ a : Fin (rank L),
            (if a = c then (if s = -2 then (-1 : ℂ) else 0) • frameMomentum F a else 0) from
      Finset.sum_congr rfl fun a _ => by
        by_cases hac : a = c
        · by_cases hs : s = -2
          · rw [if_pos ⟨hac, hs⟩, if_pos hac, if_pos hs]
          · rw [if_neg (fun h => hs h.2), if_pos hac, if_neg hs, zero_smul]
        · rw [if_neg (fun h => hac h.1), if_neg hac, zero_smul],
    Finset.sum_ite_eq' Finset.univ c, if_pos (Finset.mem_univ c)]


theorem momentumCoupling_comm_zG (c : Fin (rank L)) :
    momentumCoupling F * frameMomentum F c - frameMomentum F c * momentumCoupling F = 0 := by
  rw [momentumCoupling, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  set A := LinearMap.rTensor (L.carrier →₀ ℂ) (oscN (rank L) 1 a (-1)) with hA
  have hAc : A * frameMomentum F c = frameMomentum F c * A :=
    (frameMomentum_comm_rTensor F c (oscN (rank L) 1 a (-1))).symm
  have hac : frameMomentum F a * frameMomentum F c = frameMomentum F c * frameMomentum F a :=
    frameMomentum_comm F a c
  rw [mul_assoc, hac, ← mul_assoc, hAc, mul_assoc, sub_self]


theorem frameTranslation_frameCurrent_DCovariant (c : Fin (rank L)) :
    Reconstruction.DCovariant (frameTranslation F) (frameCurrent F c) := by
  intro s
  change frameTranslation F * frameCurrent F c s - frameCurrent F c s * frameTranslation F
    = ((s + 1 : ℤ)) • frameCurrent F c (s + 1)
  set Lv := LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) with hLdef
  have hL : Lv * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * Lv
      = ((s + 1 : ℤ)) • LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)) := by
    have hc := HeisenbergN.currentN_DCovariant (rank L) 1 (by norm_num : (1 : ℂ) ≠ 0) c s
    rw [hLdef, ← tensorEndomorphism_mul, ← tensorEndomorphism_mul, ← LinearMap.rTensor_sub,
      show HeisenbergN.LvirN (rank L) 1 (-1) * currentN (rank L) 1 c s
            - currentN (rank L) 1 c s * HeisenbergN.LvirN (rank L) 1 (-1)
          = ((s + 1 : ℤ)) • currentN (rank L) 1 c (s + 1) from hc,
      ← Int.cast_smul_eq_zsmul ℂ (s + 1) (currentN (rank L) 1 c (s + 1)), LinearMap.rTensor_smul]
    exact Int.cast_smul_eq_zsmul ℂ (s + 1)
      (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
  have hLc : Lv * (if s = -1 then frameMomentum F c else 0)
      - (if s = -1 then frameMomentum F c else 0) * Lv = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs, hLdef]
      exact sub_eq_zero_of_eq (frameMomentum_comm_rTensor F c (HeisenbergN.LvirN (rank L) 1 (-1))).symm
    · rw [if_neg hs, mul_zero, zero_mul, sub_zero]
  have hMc : momentumCoupling F * (if s = -1 then frameMomentum F c else 0)
      - (if s = -1 then frameMomentum F c else 0) * momentumCoupling F = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs]; exact momentumCoupling_comm_zG F c
    · rw [if_neg hs, mul_zero, zero_mul, sub_zero]
  have hM := momentumCoupling_comm_rTensor F c s
  have key : frameTranslation F * frameCurrent F c s - frameCurrent F c s * frameTranslation F
      = ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
        + (if s = -2 then (-1 : ℂ) else 0) • frameMomentum F c := by
    have expand : frameTranslation F * frameCurrent F c s - frameCurrent F c s * frameTranslation F
        = (Lv * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
            - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * Lv)
          + (Lv * (if s = -1 then frameMomentum F c else 0)
            - (if s = -1 then frameMomentum F c else 0) * Lv)
          + (momentumCoupling F * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s))
            - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c s)) * momentumCoupling F)
          + (momentumCoupling F * (if s = -1 then frameMomentum F c else 0)
            - (if s = -1 then frameMomentum F c else 0) * momentumCoupling F) := by
      rw [frameTranslation, hLdef, frameCurrent_apply]
      noncomm_ring
    rw [expand, hL, hLc, hM, hMc, add_zero, add_zero]
  rw [key, frameCurrent_apply,
    show ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1))
          + (if s + 1 = -1 then frameMomentum F c else 0))
        = ((s + 1 : ℤ)) • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 c (s + 1)))
          + ((s + 1 : ℤ)) • (if s + 1 = -1 then frameMomentum F c else 0) from smul_add _ _ _]
  congr 1
  by_cases hs : s = -2
  · rw [if_pos hs, if_pos (by omega : s + 1 = -1), hs, show ((-2 : ℤ) + 1) = -1 from by ring]
    exact (neg_one_smul ℂ (frameMomentum F c)).trans (neg_one_smul ℤ (frameMomentum F c)).symm
  · rw [if_neg hs, if_neg (by omega : ¬ s + 1 = -1), zero_smul]
    exact (smul_zero _).symm


theorem frameOscillator_zero (β : L.carrier) : frameOscillator F β 0 = 0 := by
  rw [frameOscillator]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [oscN_zero, smul_zero]


theorem LvirN_comm_frameOscillator_succ (β : L.carrier) (j : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * frameOscillator F β (j + 1)
      - frameOscillator F β (j + 1) * HeisenbergN.LvirN (rank L) 1 (-1)
      = (-((j : ℤ) + 1) : ℂ) • frameOscillator F β j := by
  rw [frameOscillator, frameOscillator, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
    LvirN_comm_oscN (rank L) 1 (by norm_num : (1 : ℂ) ≠ 0) b (-1) (j + 1),
    show (-1 : ℤ) + (j + 1) = j from by ring, smul_comm]
  congr 2
  push_cast; ring


theorem LvirN_comm_annihilationCoefficientZ (β : L.carrier) :
    ∀ N : ℤ, HeisenbergN.LvirN (rank L) 1 (-1) * annihilationCoefficientZ F β N
        - annihilationCoefficientZ F β N * HeisenbergN.LvirN (rank L) 1 (-1)
      = (1 - (N : ℂ)) • annihilationCoefficientZ F β (N - 1) := by
  set Lv : End ℂ (FockN (rank L)) := HeisenbergN.LvirN (rank L) 1 (-1) with hLv
  have hderiv : ∀ X Y : End ℂ (FockN (rank L)), Lv * (X * Y) - (X * Y) * Lv
      = (Lv * X - X * Lv) * Y + X * (Lv * Y - Y * Lv) := by
    intro X Y; simp only [sub_mul, mul_sub, mul_assoc]; abel
  suffices H : ∀ n : ℕ, ∀ N : ℤ, N.toNat ≤ n →
      Lv * annihilationCoefficientZ F β N - annihilationCoefficientZ F β N * Lv = (1 - (N : ℂ)) • annihilationCoefficientZ F β (N - 1) by
    exact fun N => H N.toNat N le_rfl
  intro n
  induction n with
  | zero =>
    intro N hN
    by_cases h0 : N = 0
    · subst h0
      rw [annihilationCoefficientZ_zero, annihilationCoefficientZ_neg F β (show (0 : ℤ) - 1 < 0 by omega), ← Module.End.one_eq_id,
        mul_one, one_mul, sub_self]
      exact (smul_zero _).symm
    · rw [annihilationCoefficientZ_neg F β (by omega : N < 0), annihilationCoefficientZ_neg F β (show N - 1 < 0 by omega),
        mul_zero, zero_mul, sub_self]
      exact (smul_zero _).symm
  | succ n ih =>
    intro N hM
    by_cases hsmall : N.toNat ≤ n
    · exact ih N hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      have hNtoNat : N.toNat = (N - 1).toNat + 1 := by omega
      have pt : ∀ j : ℕ,
          Lv * ((-(frameOscillator F β ((j : ℤ) + 1))) * annihilationCoefficientZ F β (N - 1 - j))
            - ((-(frameOscillator F β ((j : ℤ) + 1))) * annihilationCoefficientZ F β (N - 1 - j)) * Lv
          = ((j : ℂ) + 1) • (frameOscillator F β (j : ℤ) * annihilationCoefficientZ F β (N - 1 - j))
            + ((j : ℂ) + 2 - (N : ℂ)) • ((-(frameOscillator F β ((j : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - j)) := by
        intro j
        rw [hderiv]
        have hfst : Lv * (-(frameOscillator F β ((j : ℤ) + 1))) - (-(frameOscillator F β ((j : ℤ) + 1))) * Lv
            = ((j : ℂ) + 1) • frameOscillator F β (j : ℤ) := by
          have h := LvirN_comm_frameOscillator_succ F β (j : ℤ)
          rw [← hLv] at h
          rw [show (-(frameOscillator F β ((j : ℤ) + 1))) = ((-1 : ℂ)) • frameOscillator F β ((j : ℤ) + 1) from
              (neg_one_smul ℂ _).symm, mul_smul_comm, smul_mul_assoc,
            show ((-1 : ℂ)) • (Lv * frameOscillator F β ((j : ℤ) + 1))
                  - ((-1 : ℂ)) • (frameOscillator F β ((j : ℤ) + 1) * Lv)
                = ((-1 : ℂ)) • (Lv * frameOscillator F β ((j : ℤ) + 1)
                    - frameOscillator F β ((j : ℤ) + 1) * Lv) from (smul_sub _ _ _).symm,
            h, smul_smul]
          congr 1; push_cast; ring
        have hsnd : Lv * annihilationCoefficientZ F β (N - 1 - j) - annihilationCoefficientZ F β (N - 1 - j) * Lv
            = ((j : ℂ) + 2 - (N : ℂ)) • annihilationCoefficientZ F β (N - 2 - j) := by
          have hih := ih (N - 1 - j) (by omega)
          rw [show (N - 1 - (j : ℤ)) - 1 = N - 2 - j from by ring] at hih
          rw [hih]; congr 1; push_cast; ring
        rw [hfst, hsnd, smul_mul_assoc, mul_smul_comm]
      set R := ∑ j ∈ Finset.range N.toNat, (-(frameOscillator F β ((j : ℤ) + 1))) * annihilationCoefficientZ F β (N - 1 - j)
        with hRdef
      have hrecR : annihilationCoefficientZ F β N = (N : ℂ)⁻¹ • R := by
        rw [annihilationCoefficientZ_recursion F β N hN1, hRdef]; simp only [Module.End.mul_eq_comp]
      have hSA : (∑ j ∈ Finset.range N.toNat,
              ((j : ℂ) + 1) • (frameOscillator F β (j : ℤ) * annihilationCoefficientZ F β (N - 1 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2) • (frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ']
        rw [show (frameOscillator F β ((0 : ℕ) : ℤ) * annihilationCoefficientZ F β (N - 1 - ((0 : ℕ) : ℤ))) = 0 from by
          rw [show ((0 : ℕ) : ℤ) = 0 from rfl, frameOscillator_zero, zero_mul], smul_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 from by push_cast; ring,
          show N - 1 - ((i : ℤ) + 1) = N - 2 - i from by ring]
        congr 1; push_cast; ring
      have hSB : (∑ j ∈ Finset.range N.toNat,
              ((j : ℂ) + 2 - (N : ℂ)) • ((-(frameOscillator F β ((j : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - j)))
          = ∑ i ∈ Finset.range (N - 1).toNat,
              ((i : ℂ) + 2 - (N : ℂ)) • ((-(frameOscillator F β ((i : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - i)) := by
        rw [hNtoNat, Finset.sum_range_succ]
        rw [show annihilationCoefficientZ F β (N - 2 - ((N - 1).toNat : ℤ)) = 0 from by
          rw [show ((N - 1).toNat : ℤ) = N - 1 from by omega]
          exact annihilationCoefficientZ_neg F β (by omega), mul_zero, smul_zero, add_zero]
      have hBrR : Lv * R - R * Lv
          = (N : ℂ) • ∑ i ∈ Finset.range (N - 1).toNat,
              frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i) := by
        rw [hRdef, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          Finset.sum_congr rfl (fun j _ => pt j), Finset.sum_add_distrib, hSA, hSB,
          ← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (-(frameOscillator F β ((i : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - i)
            = ((-1 : ℂ)) • (frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i)) from by
              rw [show (-(frameOscillator F β ((i : ℤ) + 1))) = ((-1 : ℂ)) • frameOscillator F β ((i : ℤ) + 1) from
                  (neg_one_smul ℂ _).symm, smul_mul_assoc],
          smul_smul, ← add_smul]
        congr 1; ring
      have hfinal : (∑ i ∈ Finset.range (N - 1).toNat,
              frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i))
          = (1 - (N : ℂ)) • annihilationCoefficientZ F β (N - 1) := by
        have hreass := annihilationCoefficientZ_sum_reassembly F β (N - 1) (N - 1).toNat le_rfl
        simp only [← Module.End.mul_eq_comp] at hreass
        rw [show (N - 1) - 1 = N - 2 from by ring] at hreass
        rw [show (∑ i ∈ Finset.range (N - 1).toNat,
                frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i))
            = -(∑ i ∈ Finset.range (N - 1).toNat,
                (-(frameOscillator F β ((i : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - i)) from by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by
            rw [show (-(frameOscillator F β ((i : ℤ) + 1))) * annihilationCoefficientZ F β (N - 2 - i)
                = ((-1 : ℂ)) • (frameOscillator F β ((i : ℤ) + 1) * annihilationCoefficientZ F β (N - 2 - i)) from by
                  rw [show (-(frameOscillator F β ((i : ℤ) + 1))) = ((-1 : ℂ)) • frameOscillator F β ((i : ℤ) + 1) from
                      (neg_one_smul ℂ _).symm, smul_mul_assoc],
              neg_one_smul, neg_neg]]
        rw [hreass, ← neg_smul]
        congr 1; push_cast; ring
      rw [hrecR, show Lv * ((N : ℂ)⁻¹ • R) - ((N : ℂ)⁻¹ • R) * Lv
          = (N : ℂ)⁻¹ • (Lv * R - R * Lv) from by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]]
      rw [hBrR, smul_smul, inv_mul_cancel₀ hNne, one_smul, hfinal]


end VOA.Moonshine.ConwayNorton
