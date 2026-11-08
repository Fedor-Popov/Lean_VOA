import VOA.Moonshine.MoonshineCNCreationTranslation

/-!
# Complex-frame lattice construction: ChargeTranslation

Structural adaptation of `LatticeGenVirasoroCharge` using a complex bilinear
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

theorem LvirN_comm_annihilationField (β : L.carrier) (t : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * annihilationField F β t
      - annihilationField F β t * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((t + 1 : ℤ)) • annihilationField F β (t + 1) := by
  rw [annihilationField_eq_annihilationCoefficientZ, annihilationField_eq_annihilationCoefficientZ, show -(t + 1) = -t - 1 from by ring,
    LvirN_comm_annihilationCoefficientZ F β (-t),
    show (1 : ℂ) - ((-t : ℤ) : ℂ) = (((t + 1 : ℤ)) : ℂ) from by push_cast; ring]
  exact Int.cast_smul_eq_zsmul ℂ (t + 1) (annihilationCoefficientZ F β (-t - 1))


theorem frameOscillator_add (α β : L.carrier) (n : ℤ) :
    frameOscillator F (α + β) n = frameOscillator F α n + frameOscillator F β n := by
  rw [frameOscillator_eq_sum, frameOscillator_eq_sum, frameOscillator_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [frameCoordinate_add, add_smul]


theorem frameOscillator_neg1_comm_dressingField  (γ β : L.carrier) (r : ℤ) :
    frameOscillator F γ (-1) * dressingField F β r - dressingField F β r * frameOscillator F γ (-1)
      = ((L.form β γ : ℤ) : ℂ) • dressingField F β (r + 1) := by
  rw [frameOscillator_eq_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ a, ((frameCoordinate F γ a • oscN (rank L) 1 a (-1)) * dressingField F β r
            - dressingField F β r * (frameCoordinate F γ a • oscN (rank L) 1 a (-1))))
        = ∑ a, frameCoordinate F γ a • (frameCoordinate F β a • dressingField F β (r + 1)) from
      Finset.sum_congr rfl fun a _ => by
        rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
        congr 1
        have h := bosonCurrent_comm_dressingField F a β 0 r
        rw [if_neg (by norm_num : ¬ (0 : ℤ) = -1), bracketDist_apply, currentN_apply,
          show -(0 : ℤ) - 1 = -1 from by ring, show r + 0 + 1 = r + 1 from by ring] at h
        exact h]
  rw [show (∑ a, frameCoordinate F γ a • (frameCoordinate F β a • dressingField F β (r + 1)))
        = (∑ a, frameCoordinate F γ a * frameCoordinate F β a) • dressingField F β (r + 1) from by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun a _ => by rw [smul_smul],
    frameCoordinate_pairing F γ β, form_symm L γ β]


theorem LvirN_comm_dressingField (β : L.carrier) (r : ℤ) :
    HeisenbergN.LvirN (rank L) 1 (-1) * dressingField F β r - dressingField F β r * HeisenbergN.LvirN (rank L) 1 (-1)
      = ((r + 1 : ℤ)) • dressingField F β (r + 1) - frameOscillator F β (-1) * dressingField F β r := by
  set Lv : End ℂ (FockN (rank L)) := HeisenbergN.LvirN (rank L) 1 (-1) with hLv
  have ha := creationField_isField F β
  have hb := annihilationField_isField F β
  have NO_term : ∀ k : ℤ,
      Lv * normalOrdered (creationField F β) (annihilationField F β) k (r - k)
        - normalOrdered (creationField F β) (annihilationField F β) k (r - k) * Lv
      = normalOrdered (VOA.deriv (creationField F β)) (annihilationField F β) k (r - k)
        + normalOrdered (creationField F β) (VOA.deriv (annihilationField F β)) k (r - k)
        - frameOscillator F β (-1) * normalOrdered (creationField F β) (annihilationField F β) k (r - k) := by
    intro k
    by_cases hk : 0 ≤ k
    · simp only [normalOrdered_apply, if_pos hk, deriv_apply]
      rw [show Lv * (creationField F β k * annihilationField F β (r - k))
              - creationField F β k * annihilationField F β (r - k) * Lv
            = (Lv * creationField F β k - creationField F β k * Lv) * annihilationField F β (r - k)
              + creationField F β k * (Lv * annihilationField F β (r - k)
                  - annihilationField F β (r - k) * Lv) from by
            simp only [sub_mul, mul_sub, mul_assoc]; abel,
        hLv, LvirN_comm_creationField, LvirN_comm_annihilationField]
      simp only [sub_mul, smul_mul_assoc]
      rw [show frameOscillator F β (-1) * creationField F β k * annihilationField F β (r - k)
          = frameOscillator F β (-1) * (creationField F β k * annihilationField F β (r - k)) from
            mul_assoc _ _ _]
      abel
    · simp only [normalOrdered_apply, if_neg hk]
      have hEm0 : creationField F β k = 0 := creationField_neg F β (by omega)
      have hdEm0 : VOA.deriv (creationField F β) k = 0 := by
        rw [deriv_apply]
        rcases lt_or_eq_of_le (show k + 1 ≤ 0 by omega) with h | h
        · rw [creationField_neg F β h]; exact smul_zero _
        · rw [h, zero_smul]
      rw [hEm0, hdEm0]; simp
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, dressingField, nprod_apply,
    map_finsum Lv (normalOrdered_diag_support_finite ha hb r x), nprod_apply]
  have hfinDL : (Function.support (fun k : ℤ =>
      Lv (normalOrdered (creationField F β) (annihilationField F β) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero])
  have hcleanFin : (Function.support (fun k : ℤ =>
      normalOrdered (VOA.deriv (creationField F β)) (annihilationField F β) k (r - k) x
        + normalOrdered (creationField F β) (VOA.deriv (annihilationField F β)) k (r - k) x)).Finite := by
    apply Set.Finite.subset ((normalOrdered_diag_support_finite ha.deriv hb r x).union
      (normalOrdered_diag_support_finite ha hb.deriv r x))
    intro k hk
    rw [Function.mem_support] at hk
    simp only [Set.mem_union, Function.mem_support]
    by_contra hcon
    push_neg at hcon
    exact hk (by rw [hcon.1, hcon.2, add_zero])
  have hdefectFin : (Function.support (fun k : ℤ =>
      frameOscillator F β (-1) (normalOrdered (creationField F β) (annihilationField F β) k (r - k) x))).Finite := by
    apply Set.Finite.subset (normalOrdered_diag_support_finite ha hb r x)
    intro k hk
    rw [Function.mem_support] at hk ⊢
    exact fun hz => hk (by rw [hz, map_zero])
  have hclean : (∑ᶠ k : ℤ, (normalOrdered (VOA.deriv (creationField F β)) (annihilationField F β) k (r - k) x
        + normalOrdered (creationField F β) (VOA.deriv (annihilationField F β)) k (r - k) x))
      = ((r + 1 : ℤ) • dressingField F β (r + 1)) x := by
    rw [finsum_add_distrib (normalOrdered_diag_support_finite ha.deriv hb r x)
        (normalOrdered_diag_support_finite ha hb.deriv r x),
      show (∑ᶠ k : ℤ, normalOrdered (VOA.deriv (creationField F β)) (annihilationField F β) k (r - k) x)
          = VOA.nprod ha.deriv hb r x from (nprod_apply ha.deriv hb r x).symm,
      show (∑ᶠ k : ℤ, normalOrdered (creationField F β) (VOA.deriv (annihilationField F β)) k (r - k) x)
          = VOA.nprod ha hb.deriv r x from (nprod_apply ha hb.deriv r x).symm]
    have hadd : (VOA.nprod ha.deriv hb r) x + (VOA.nprod ha hb.deriv r) x
        = (VOA.deriv (VOA.nprod ha hb)) r x := by rw [deriv_nprod]; rfl
    rw [hadd, deriv_apply]; rfl
  have hdefect : (∑ᶠ k : ℤ, frameOscillator F β (-1) (normalOrdered (creationField F β) (annihilationField F β) k (r - k) x))
      = (frameOscillator F β (-1) * dressingField F β r) x := by
    rw [Module.End.mul_apply, dressingField, nprod_apply,
      map_finsum (frameOscillator F β (-1)) (normalOrdered_diag_support_finite ha hb r x)]
  rw [← finsum_sub_distrib hfinDL (normalOrdered_diag_support_finite ha hb r (Lv x)),
    finsum_congr (fun k => by
      have := congrArg (fun (T : End ℂ (FockN (rank L))) => T x) (NO_term k)
      simpa only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.smul_apply] using this),
    finsum_sub_distrib hcleanFin hdefectFin, hclean, hdefect]
  exact (LinearMap.sub_apply _ _ x).symm


theorem frameTranslation_tmul (q : FockN (rank L)) (γ : L.carrier) :
    frameTranslation F (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-1) q) γ
        + latStateGen L (frameOscillator F γ (-1) q) γ := by
  have hrt : LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1))
      (latStateGen L q γ) = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-1) q) γ := by
    show LinearMap.rTensor (L.carrier →₀ ℂ) (HeisenbergN.LvirN (rank L) 1 (-1)) (q ⊗ₜ[ℂ] eGen L γ)
        = (HeisenbergN.LvirN (rank L) 1 (-1) q) ⊗ₜ[ℂ] eGen L γ
    rw [LinearMap.rTensor_tmul]
  have hmom : momentumCoupling F (latStateGen L q γ) = latStateGen L (frameOscillator F γ (-1) q) γ := by
    rw [momentumCoupling, LinearMap.coe_sum, Finset.sum_apply,
      show latStateGen L (frameOscillator F γ (-1) q) γ = (frameOscillator F γ (-1) q) ⊗ₜ[ℂ] eGen L γ from rfl,
      frameOscillator_eq_sum, LinearMap.coe_sum, Finset.sum_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Module.End.mul_apply,
      show frameMomentum F a (latStateGen L q γ) = frameCoordinate F γ a • latStateGen L q γ from
        frameMomentum_latStateGen F a q γ,
      show latStateGen L q γ = q ⊗ₜ[ℂ] eGen L γ from rfl,
      map_smul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul', LinearMap.smul_apply]
  rw [frameTranslation, LinearMap.add_apply, hrt, hmom]


theorem frameTranslation_canonicalChargedField_bosonOp  (β : L.carrier) (s : ℤ) (γ : L.carrier) :
    HeisenbergN.LvirN (rank L) 1 (-1) * dressingField F β (s - L.form β γ)
        - dressingField F β (s - L.form β γ) * HeisenbergN.LvirN (rank L) 1 (-1)
      + frameOscillator F (β + γ) (-1) * dressingField F β (s - L.form β γ)
      - dressingField F β (s - L.form β γ) * frameOscillator F γ (-1)
    = ((s + 1 : ℤ)) • dressingField F β (s + 1 - L.form β γ) := by
  rw [show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring, frameOscillator_add, add_mul,
    ← Int.cast_smul_eq_zsmul ℂ (s + 1)]
  have hL := LvirN_comm_dressingField F β (s - L.form β γ)
  have hcomm := frameOscillator_neg1_comm_dressingField F γ β (s - L.form β γ)
  rw [← Int.cast_smul_eq_zsmul ℂ ((s - L.form β γ) + 1)] at hL
  have hLZ : HeisenbergN.LvirN (rank L) 1 (-1) * dressingField F β (s - L.form β γ)
      = dressingField F β (s - L.form β γ) * HeisenbergN.LvirN (rank L) 1 (-1)
        + ((((s - L.form β γ) + 1 : ℤ) : ℂ) • dressingField F β ((s - L.form β γ) + 1)
          - frameOscillator F β (-1) * dressingField F β (s - L.form β γ)) := by rw [← hL]; abel
  have hcZ : frameOscillator F γ (-1) * dressingField F β (s - L.form β γ)
      = dressingField F β (s - L.form β γ) * frameOscillator F γ (-1)
        + ((L.form β γ : ℤ) : ℂ) • dressingField F β ((s - L.form β γ) + 1) := by rw [← hcomm]; abel
  rw [hLZ, hcZ]
  push_cast
  module


theorem frameTranslation_canonicalChargedField_on_state  (β : L.carrier) (s : ℤ) (γ : L.carrier)
    (p : FockN (rank L)) :
    (frameTranslation F * canonicalChargedField F β s - canonicalChargedField F β s * frameTranslation F) (latStateGen L p γ)
      = ((s + 1 : ℤ)) • canonicalChargedField F β (s + 1) (latStateGen L p γ) := by
  have hp := congrArg (fun T : End ℂ (FockN (rank L)) => T p) (frameTranslation_canonicalChargedField_bosonOp F β s γ)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at hp
  rw [← Int.cast_smul_eq_zsmul ℂ (s + 1)] at hp
  have hbracket : HeisenbergN.LvirN (rank L) 1 (-1) (dressingField F β (s - L.form β γ) p)
        + frameOscillator F (β + γ) (-1) (dressingField F β (s - L.form β γ) p)
        - (dressingField F β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
          + dressingField F β (s - L.form β γ) (frameOscillator F γ (-1) p))
      = (((s + 1 : ℤ) : ℂ)) • dressingField F β ((s - L.form β γ) + 1) p := by
    rw [show HeisenbergN.LvirN (rank L) 1 (-1) (dressingField F β (s - L.form β γ) p)
            + frameOscillator F (β + γ) (-1) (dressingField F β (s - L.form β γ) p)
            - (dressingField F β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
              + dressingField F β (s - L.form β γ) (frameOscillator F γ (-1) p))
          = HeisenbergN.LvirN (rank L) 1 (-1) (dressingField F β (s - L.form β γ) p)
            - dressingField F β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
            + frameOscillator F (β + γ) (-1) (dressingField F β (s - L.form β γ) p)
            - dressingField F β (s - L.form β γ) (frameOscillator F γ (-1) p) from by abel,
      hp, show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring, LinearMap.smul_apply]
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, canonicalChargedField_tmul, map_smul,
    frameTranslation_tmul, frameTranslation_tmul, map_add, canonicalChargedField_tmul, canonicalChargedField_tmul, smul_add,
    ← latStateGen_smul_boson, ← latStateGen_smul_boson, ← latStateGen_smul_boson,
    ← latStateGen_smul_boson, ← latStateGen_add_boson, ← latStateGen_add_boson,
    ← latStateGen_sub_boson,
    show latticeCocycle L β γ • HeisenbergN.LvirN (rank L) 1 (-1) (dressingField F β (s - L.form β γ) p)
          + latticeCocycle L β γ • frameOscillator F (β + γ) (-1) (dressingField F β (s - L.form β γ) p)
          - (latticeCocycle L β γ • dressingField F β (s - L.form β γ) (HeisenbergN.LvirN (rank L) 1 (-1) p)
            + latticeCocycle L β γ • dressingField F β (s - L.form β γ) (frameOscillator F γ (-1) p))
        = latticeCocycle L β γ • ((((s + 1 : ℤ) : ℂ)) • dressingField F β ((s - L.form β γ) + 1) p) from by
      rw [← smul_add, ← smul_add, ← smul_sub, hbracket],
    latStateGen_smul_boson, latStateGen_smul_boson,
    ← Int.cast_smul_eq_zsmul ℂ (s + 1), canonicalChargedField_tmul,
    smul_comm, show s + 1 - L.form β γ = (s - L.form β γ) + 1 from by ring]


theorem frameTranslation_canonicalChargedField_DCovariant  (β : L.carrier) :
    Reconstruction.DCovariant (frameTranslation F) (canonicalChargedField F β) := by
  intro s
  refine LinearMap.ext fun y => ?_
  change (frameTranslation F * canonicalChargedField F β s - canonicalChargedField F β s * frameTranslation F) y
    = ((s + 1 : ℤ)) • canonicalChargedField F β (s + 1) y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, zsmul_zero]
  | add y1 y2 h1 h2 =>
      rw [map_add (frameTranslation F * canonicalChargedField F β s - canonicalChargedField F β s * frameTranslation F) y1 y2, h1, h2,
        map_add (canonicalChargedField F β (s + 1)) y1 y2]
      exact (smul_add _ _ _).symm
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; simp only [map_zero, zsmul_zero]
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]
          simp only [map_add, h1, h2]
          exact (smul_add _ _ _).symm
      | single γ a =>
          rw [(Finsupp.smul_single_one γ a).symm,
            show (Finsupp.single γ (1 : ℂ) : L.carrier →₀ ℂ) = eGen L γ from rfl]
          erw [TensorProduct.tmul_smul, map_smul, map_smul,
            show p ⊗ₜ[ℂ] eGen L γ = latStateGen L p γ from rfl,
            frameTranslation_canonicalChargedField_on_state F β s γ]
          rw [← Int.cast_smul_eq_zsmul ℂ (s + 1) (canonicalChargedField F β (s + 1) (latStateGen L p γ)),
            ← Int.cast_smul_eq_zsmul ℂ (s + 1) (a • canonicalChargedField F β (s + 1) (latStateGen L p γ)), smul_comm]


theorem frameTranslation_frameDerivativeCurrent_DCovariant (a : Fin (rank L)) (i : ℕ) :
    Reconstruction.DCovariant (frameTranslation F) (frameDerivativeCurrent F a i) := by
  rw [frameDerivativeCurrent]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate (frameTranslation_frameCurrent_DCovariant F a) i)


end VOA.Moonshine.ConwayNorton
