import VOA.Moonshine.MoonshineCNCurrents

/-!
# Complex-frame lattice construction: CurrentCharge

Structural adaptation of `LatticeGenBosonCharge` using a complex bilinear
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

theorem endomorphism_commutator_leibniz (L : IntegralLattice) (f g h : End ℂ (FockN (rank L))) (x : FockN (rank L)) :
    f (g (h x)) - g (h (f x)) = (f * g - g * f) (h x) + g ((f * h - h * f) x) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]; abel


theorem frameOscillator_eq_sum (α : L.carrier) (m : ℤ) :
    frameOscillator F α m = ∑ b, frameCoordinate F α b • oscN (rank L) 1 b m := rfl


theorem oscN_frameOscillator_commutator (a : Fin (rank L)) (β : L.carrier) (m n : ℤ) :
    oscN (rank L) 1 a m * frameOscillator F β n - frameOscillator F β n * oscN (rank L) 1 a m
      = (if m + n = 0 then frameCoordinate F β a * (m : ℂ) else 0) • LinearMap.id := by
  rw [frameOscillator_eq_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [show (∑ b, (oscN (rank L) 1 a m * (frameCoordinate F β b • oscN (rank L) 1 b n)
          - (frameCoordinate F β b • oscN (rank L) 1 b n) * oscN (rank L) 1 a m))
      = ∑ b, frameCoordinate F β b • (if a = b ∧ m + n = 0 then (m : ℂ) * 1 else 0) • LinearMap.id from
    Finset.sum_congr rfl fun b _ => by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, oscN_comm]]
  rw [Finset.sum_eq_single a]
  · by_cases hmn : m + n = 0
    · rw [if_pos ⟨rfl, hmn⟩, if_pos hmn, mul_one, smul_smul]
    · rw [if_neg (fun h => hmn h.2), if_neg hmn]; simp
  · intro b _ hba
    rw [if_neg (fun h => hba h.1.symm)]; simp
  · intro h; exact absurd (Finset.mem_univ a) h


theorem oscNeg_comp_annihilationCoefficientZ (a : Fin (rank L)) (β : L.carrier) (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℤ, (oscN (rank L) 1 a (-(k : ℤ))).comp (annihilationCoefficientZ F β M)
      = (annihilationCoefficientZ F β M).comp (oscN (rank L) 1 a (-(k : ℤ)))
        + frameCoordinate F β a • annihilationCoefficientZ F β (M - k) := by
  have hmove : ∀ m : ℕ, (oscN (rank L) 1 a (-(k : ℤ))).comp (-(frameOscillator F β ((m : ℤ) + 1)))
      = (-(frameOscillator F β ((m : ℤ) + 1))).comp (oscN (rank L) 1 a (-(k : ℤ)))
        + (if (m : ℤ) + 1 = (k : ℤ) then frameCoordinate F β a * (k : ℂ) else 0) • LinearMap.id := by
    intro m
    have hAB := sub_eq_iff_eq_add'.mp (oscN_frameOscillator_commutator F a β (-(k : ℤ)) ((m : ℤ) + 1))
    rw [LinearMap.comp_neg, LinearMap.neg_comp,
      show (oscN (rank L) 1 a (-(k : ℤ))).comp (frameOscillator F β ((m : ℤ) + 1))
          = oscN (rank L) 1 a (-(k : ℤ)) * frameOscillator F β ((m : ℤ) + 1) from rfl,
      show (frameOscillator F β ((m : ℤ) + 1)).comp (oscN (rank L) 1 a (-(k : ℤ)))
          = frameOscillator F β ((m : ℤ) + 1) * oscN (rank L) 1 a (-(k : ℤ)) from rfl, hAB]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos (show -(k : ℤ) + ((m : ℤ) + 1) = 0 by omega), if_pos hc]
      push_cast; module
    · rw [if_neg (show ¬ (-(k : ℤ) + ((m : ℤ) + 1) = 0) by omega), if_neg hc]; simp
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      (oscN (rank L) 1 a (-(k : ℤ))).comp (annihilationCoefficientZ F β M)
        = (annihilationCoefficientZ F β M).comp (oscN (rank L) 1 a (-(k : ℤ)))
          + frameCoordinate F β a • annihilationCoefficientZ F β (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [annihilationCoefficientZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        annihilationCoefficientZ_neg F β (show (0 : ℤ) - k < 0 by omega), smul_zero, add_zero]
    · rw [annihilationCoefficientZ_neg F β (by omega : M < 0), annihilationCoefficientZ_neg F β (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, smul_zero, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [annihilationCoefficientZ_recursion F β M hM1]
      rw [LinearMap.comp_smul, endomorphism_comp_sum]
      have hterm : ∀ m ∈ Finset.range M.toNat,
          (oscN (rank L) 1 a (-(k : ℤ))).comp
              ((-(frameOscillator F β ((m : ℤ) + 1))).comp (annihilationCoefficientZ F β (M - 1 - m)))
            = (-(frameOscillator F β ((m : ℤ) + 1))).comp
                ((annihilationCoefficientZ F β (M - 1 - m)).comp (oscN (rank L) 1 a (-(k : ℤ))))
              + frameCoordinate F β a • (-(frameOscillator F β ((m : ℤ) + 1))).comp
                  (annihilationCoefficientZ F β ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then frameCoordinate F β a * (k : ℂ) else 0)
                • annihilationCoefficientZ F β (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcol1 : (∑ m ∈ Finset.range M.toNat,
            (-(frameOscillator F β ((m : ℤ) + 1))).comp
              ((annihilationCoefficientZ F β (M - 1 - m)).comp (oscN (rank L) 1 a (-(k : ℤ)))))
          = (M : ℂ) • ((annihilationCoefficientZ F β M).comp (oscN (rank L) 1 a (-(k : ℤ)))) := by
        simp only [← LinearMap.comp_assoc, ← endomorphism_sum_comp,
          annihilationCoefficientZ_sum_reassembly F β M M.toNat le_rfl, LinearMap.smul_comp]
      have hcol2 : (∑ m ∈ Finset.range M.toNat,
            frameCoordinate F β a • (-(frameOscillator F β ((m : ℤ) + 1))).comp
              (annihilationCoefficientZ F β ((M - k) - 1 - m)))
          = frameCoordinate F β a • (((M - k : ℤ) : ℂ) • annihilationCoefficientZ F β (M - k)) := by
        rw [← Finset.smul_sum, annihilationCoefficientZ_sum_reassembly F β (M - k) M.toNat (by omega)]
      have hcol3 : (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then frameCoordinate F β a * (k : ℂ) else 0)
              • annihilationCoefficientZ F β (M - 1 - m))
          = (frameCoordinate F β a * (k : ℂ)) • annihilationCoefficientZ F β (M - k) := by
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [annihilationCoefficientZ_neg F β (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3, inv_smul_eq_iff₀ hMne]
      push_cast
      module


theorem oscN_pos_comp_creationField (a : Fin (rank L)) (α : L.carrier) {m : ℕ} (hm : 1 ≤ m)
    (t : ℤ) :
    (oscN (rank L) 1 a (m : ℤ)).comp (creationField F α t)
      = (creationField F α t).comp (oscN (rank L) 1 a (m : ℤ))
        + frameCoordinate F α a • creationField F α (t - m) := by
  by_cases ht : 0 ≤ t
  · rw [creationField_apply, if_pos ht, directionOscillator_creation_contraction F α a m t.toNat hm]
    congr 1
    by_cases hmN : m ≤ t.toNat
    · rw [if_pos hmN, creationField_apply, if_pos (by omega : (0 : ℤ) ≤ t - m),
        show (t - (m : ℤ)).toNat = t.toNat - m from by omega]
      rfl
    · rw [if_neg hmN, creationField_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ t - m), smul_zero]
  · rw [creationField_apply, if_neg ht, LinearMap.comp_zero, LinearMap.zero_comp,
      creationField_apply, if_neg (by omega : ¬ (0 : ℤ) ≤ t - m), smul_zero, add_zero]


theorem oscN_neg_comp_creationField (a : Fin (rank L)) (α : L.carrier) {m : ℤ} (hm : m < 0)
    (t : ℤ) :
    (oscN (rank L) 1 a m).comp (creationField F α t)
      = (creationField F α t).comp (oscN (rank L) 1 a m) := by
  refine LinearMap.ext fun q => ?_
  rw [creationField_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, creationOperator, LinearMap.mulLeft_apply,
      oscN_apply_neg (rank L) 1 a hm]
    ring
  · simp


theorem bosonCurrent_comm_creationField (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (creationField F α) j t
      = if j ≤ -2 then frameCoordinate F α a • creationField F α (t + j + 1) else 0 := by
  rw [bracketDist_apply, currentN_apply]
  change (oscN (rank L) 1 a (-j - 1)).comp (creationField F α t)
      - (creationField F α t).comp (oscN (rank L) 1 a (-j - 1)) = _
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hmval : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ (-j - 1).toNat := by omega
    rw [show (-j - 1 : ℤ) = ((-j - 1).toNat : ℤ) from hmval.symm,
      oscN_pos_comp_creationField F a α hm1 t,
      show t - ((-j - 1).toNat : ℤ) = t + j + 1 from by rw [hmval]; ring]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 < 0 ∨ -j - 1 = 0 from by omega) with hlt | heq
    · rw [oscN_neg_comp_creationField F a α hlt t, sub_self]
    · rw [heq, oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]


theorem positive_frameOscillators_commute_oscN (β : L.carrier) (a : Fin (rank L)) {m p : ℤ} (hm : 1 ≤ m)
    (hp : 1 ≤ p) : Commute (frameOscillator F β m) (oscN (rank L) 1 a p) := by
  have h := oscN_frameOscillator_commutator F a β p m
  rw [if_neg (by omega : ¬ p + m = 0), zero_smul, sub_eq_zero] at h
  exact h.symm


theorem annihilationCoefficient_commute_oscN (β : L.carrier) (a : Fin (rank L)) (N : ℕ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (annihilationCoefficient F β N) (oscN (rank L) 1 a p) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [annihilationCoefficient_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [annihilationCoefficient_succ]
      refine Commute.smul_left ?_ _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (positive_frameOscillators_commute_oscN F β a (by omega) hp).neg_left


theorem annihilationCoefficientZ_commute_oscPos (β : L.carrier) (a : Fin (rank L)) (M : ℤ) {p : ℤ} (hp : 1 ≤ p) :
    Commute (annihilationCoefficientZ F β M) (oscN (rank L) 1 a p) := by
  by_cases hM : 0 ≤ M
  · rw [annihilationCoefficientZ_nonneg F β hM]; exact annihilationCoefficient_commute_oscN F β a M.toNat hp
  · rw [annihilationCoefficientZ_neg F β (by omega)]; exact Commute.zero_left _


theorem bosonCurrent_comm_annihilationField (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (annihilationField F α) j t
      = if 0 ≤ j then frameCoordinate F α a • annihilationField F α (t + j + 1) else 0 := by
  rw [bracketDist_apply, currentN_apply]
  change (oscN (rank L) 1 a (-j - 1)).comp (annihilationField F α t)
      - (annihilationField F α t).comp (oscN (rank L) 1 a (-j - 1)) = _
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, show -j - 1 = -((j + 1).toNat : ℤ) from by omega,
      annihilationField_eq_annihilationCoefficientZ F α t, annihilationField_eq_annihilationCoefficientZ F α (t + j + 1),
      oscNeg_comp_annihilationCoefficientZ F a α (j + 1).toNat (by omega) (-t),
      show -t - ((j + 1).toNat : ℤ) = -(t + j + 1) from by omega]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 = 0 ∨ 1 ≤ -j - 1 from by omega) with h0 | h1
    · rw [h0, oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
    · rw [annihilationField_eq_annihilationCoefficientZ F α t,
        show (oscN (rank L) 1 a (-j - 1)).comp (annihilationCoefficientZ F α (-t))
            = (annihilationCoefficientZ F α (-t)).comp (oscN (rank L) 1 a (-j - 1)) from
          (annihilationCoefficientZ_commute_oscPos F α a (-t) h1).eq.symm, sub_self]


theorem bosonCurrent_comm_dressingField (a : Fin (rank L)) (α : L.carrier) (j t : ℤ) :
    bracketDist (currentN (rank L) 1 a) (dressingField F α) j t
      = if j = -1 then 0 else frameCoordinate F α a • dressingField F α (t + j + 1) := by
  refine LinearMap.ext fun x => ?_
  have hsupp1 : (Function.support (fun m : ℤ =>
      currentN (rank L) 1 a j (creationField F α m (annihilationField F α (t - m) x)))).Finite := by
    apply Set.Finite.subset (dressingConvolution_support_finite F α t x)
    intro m hm; rw [Function.mem_support] at hm ⊢
    intro h; exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support (fun m : ℤ =>
      creationField F α m (annihilationField F α (t - m) (currentN (rank L) 1 a j x)))).Finite :=
    dressingConvolution_support_finite F α t (currentN (rank L) 1 a j x)
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show dressingField F α t (currentN (rank L) 1 a j x)
        = ∑ᶠ m : ℤ, creationField F α m (annihilationField F α (t - m) (currentN (rank L) 1 a j x)) from
      dressingField_apply_conv F α t (currentN (rank L) 1 a j x),
    show currentN (rank L) 1 a j (dressingField F α t x)
        = ∑ᶠ m : ℤ, currentN (rank L) 1 a j (creationField F α m (annihilationField F α (t - m) x)) from by
      rw [dressingField_apply_conv F α t x, map_finsum (currentN (rank L) 1 a j) (dressingConvolution_support_finite F α t x)],
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (currentN (rank L) 1 a j (creationField F α m (annihilationField F α (t - m) x))
            - creationField F α m (annihilationField F α (t - m) (currentN (rank L) 1 a j x))))
          = ∑ᶠ m : ℤ, ((bracketDist (currentN (rank L) 1 a) (creationField F α) j m)
                (annihilationField F α (t - m) x)
              + creationField F α m
                ((bracketDist (currentN (rank L) 1 a) (annihilationField F α) j (t - m)) x)) from
      finsum_congr fun m => by
        rw [bracketDist_apply, bracketDist_apply]
        exact endomorphism_commutator_leibniz L (currentN (rank L) 1 a j) (creationField F α m)
          (annihilationField F α (t - m)) x]
  simp only [bosonCurrent_comm_creationField, bosonCurrent_comm_annihilationField]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then frameCoordinate F α a • creationField F α (m + j + 1) else 0)
                (annihilationField F α (t - m) x)
              + creationField F α m ((if 0 ≤ j then frameCoordinate F α a • annihilationField F α (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, frameCoordinate F α a • creationField F α (m + j + 1) (annihilationField F α (t - m) x) from
        finsum_congr fun m => by
          rw [if_pos hj, if_neg (by omega : ¬ 0 ≤ j), LinearMap.smul_apply,
            LinearMap.zero_apply, map_zero, add_zero],
      show (frameCoordinate F α a • dressingField F α (t + j + 1)) x
          = frameCoordinate F α a • dressingField F α (t + j + 1) x from rfl,
      dressingField_apply_conv F α (t + j + 1) x, smul_finsum' (frameCoordinate F α a)
        (dressingConvolution_support_finite F α (t + j + 1) x),
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => frameCoordinate F α a • creationField F α m (annihilationField F α (t + j + 1 - m) x))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then frameCoordinate F α a • creationField F α (m + j + 1) else 0)
                (annihilationField F α (t - m) x)
              + creationField F α m ((if 0 ≤ j then frameCoordinate F α a • annihilationField F α (t - m + j + 1)
                else 0) x)))
          = ∑ᶠ m : ℤ, frameCoordinate F α a • creationField F α m (annihilationField F α (t + j + 1 - m) x) from
        finsum_congr fun m => by
          rw [if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            LinearMap.smul_apply, map_smul, show t - m + j + 1 = t + j + 1 - m from by ring],
      show (frameCoordinate F α a • dressingField F α (t + j + 1)) x
          = frameCoordinate F α a • dressingField F α (t + j + 1) x from rfl,
      dressingField_apply_conv F α (t + j + 1) x, smul_finsum' (frameCoordinate F α a)
        (dressingConvolution_support_finite F α (t + j + 1) x)]


theorem frameCoordinate_add (α β : L.carrier) (a : Fin (rank L)) :
    frameCoordinate F (α + β) a = frameCoordinate F α a + frameCoordinate F β a := by
  exact congrFun (F.coordinate.map_add α β) a

theorem frameCurrent_tmul (a : Fin (rank L)) (j : ℤ) (q : FockN (rank L)) (δ : L.carrier) :
    frameCurrent F a j (latStateGen L q δ)
      = latStateGen L (currentN (rank L) 1 a j q) δ
        + (if j = -1 then frameCoordinate F δ a • latStateGen L q δ else 0) := by
  rw [frameCurrent_apply, LinearMap.add_apply]
  have h1 : LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j) (latStateGen L q δ)
      = latStateGen L (currentN (rank L) 1 a j q) δ := by
    show LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j) (q ⊗ₜ[ℂ] eGen L δ)
        = (currentN (rank L) 1 a j q) ⊗ₜ[ℂ] eGen L δ
    rw [LinearMap.rTensor_tmul]
  rw [h1]
  congr 1
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, frameMomentum_latStateGen]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]


theorem frameCurrent_comm_canonicalChargedField_tmul (a : Fin (rank L)) (β : L.carrier) (j t : ℤ)
    (p : FockN (rank L)) (γ : L.carrier) :
    bracketDist (frameCurrent F a) (canonicalChargedField F β) j t (latStateGen L p γ)
      = frameCoordinate F β a • canonicalChargedField F β (t + j + 1) (latStateGen L p γ) := by
  have hcur1 : currentN (rank L) 1 a (-1) = (0 : End ℂ (FockN (rank L))) := by
    rw [currentN_apply, show -(-1 : ℤ) - 1 = 0 from by ring, oscN_zero]
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    canonicalChargedField_tmul, map_smul, frameCurrent_tmul, frameCurrent_tmul]
  by_cases hj : j = -1
  · 
    subst hj
    rw [if_pos rfl, if_pos rfl, hcur1, LinearMap.zero_apply, LinearMap.zero_apply,
      show latStateGen L (0 : FockN (rank L)) (β + γ) = 0 from by
        rw [latStateGen, TensorProduct.zero_tmul],
      show latStateGen L (0 : FockN (rank L)) γ = 0 from by
        rw [latStateGen, TensorProduct.zero_tmul],
      zero_add, zero_add, map_smul, show t + -1 + 1 = t from by ring, canonicalChargedField_tmul,
      frameCoordinate_add]
    module
  · 
    rw [if_neg hj, if_neg hj, add_zero, add_zero, canonicalChargedField_tmul, canonicalChargedField_tmul]
    have hbe : currentN (rank L) 1 a j (dressingField F β (t - L.form β γ) p)
          - dressingField F β (t - L.form β γ) (currentN (rank L) 1 a j p)
        = frameCoordinate F β a • dressingField F β (t - L.form β γ + j + 1) p := by
      have h0 := bosonCurrent_comm_dressingField F a β j (t - L.form β γ)
      rw [if_neg hj] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at hp
      exact hp
    rw [← smul_sub, ← latStateGen_sub_boson, hbe, latStateGen_smul_boson, smul_smul, smul_smul,
      mul_comm (latticeCocycle L β γ) (frameCoordinate F β a),
      show t - L.form β γ + j + 1 = t + j + 1 - L.form β γ from by ring]


theorem frameCurrent_comm_canonicalChargedField (a : Fin (rank L)) (β : L.carrier) (j t : ℤ) :
    bracketDist (frameCurrent F a) (canonicalChargedField F β) j t
      = frameCoordinate F β a • canonicalChargedField F β (t + j + 1) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | single γ a' =>
          rw [show (Finsupp.single γ a' : L.carrier →₀ ℂ) = a' • eGen L γ from
            (Finsupp.smul_single_one γ a').symm]
          erw [TensorProduct.tmul_smul, map_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            frameCurrent_comm_canonicalChargedField_tmul, LinearMap.smul_apply]


theorem frameCurrent_canonicalChargedField_local (a : Fin (rank L)) (β : L.carrier) :
    Local (frameCurrent F a) (canonicalChargedField F β) := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext s t
  rw [mulBySub_apply, frameCurrent_comm_canonicalChargedField, frameCurrent_comm_canonicalChargedField,
    show t + (s - 1) + 1 = (t - 1) + s + 1 from by ring, sub_self]
  rfl


theorem frameDerivativeCurrent_local_canonicalChargedField (a : Fin (rank L)) (i : ℕ) (β : L.carrier) :
    Local (frameDerivativeCurrent F a i) (canonicalChargedField F β) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (frameCurrent F a))) (canonicalChargedField F β)
  exact VertexOperatorAlgebra.Local.smul' _ ((frameCurrent_canonicalChargedField_local F a β).deriv_iterate_left i)


end VOA.Moonshine.ConwayNorton
