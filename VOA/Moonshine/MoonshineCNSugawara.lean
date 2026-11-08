import VOA.Moonshine.MoonshineCNConformal

/-!
# Complex-frame lattice construction: Sugawara

Structural adaptation of `LatticeGenSugawaraTmul` using a complex bilinear
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

theorem normalOrdered_liftBosonField (L : IntegralLattice) (a b : FormalDist (End ℂ (FockN (rank L)))) (m n : ℤ) :
    normalOrdered (liftBosonField L a) (liftBosonField L b) m n
      = LinearMap.rTensor (L.carrier →₀ ℂ) (normalOrdered a b m n) := by
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h]
    change LinearMap.rTensor (L.carrier →₀ ℂ) (a m) * LinearMap.rTensor (L.carrier →₀ ℂ) (b n)
      = LinearMap.rTensor (L.carrier →₀ ℂ) (a m * b n)
    rw [tensorEndomorphism_mul]
  · rw [if_neg h, if_neg h]
    change LinearMap.rTensor (L.carrier →₀ ℂ) (b n) * LinearMap.rTensor (L.carrier →₀ ℂ) (a m)
      = LinearMap.rTensor (L.carrier →₀ ℂ) (b n * a m)
    rw [tensorEndomorphism_mul]


theorem liftBosonField_nprod (L : IntegralLattice) {a b : FormalDist (End ℂ (FockN (rank L)))} (ha : IsField a) (hb : IsField b) :
    nprod (liftBosonField_isField L ha) (liftBosonField_isField L hb) = liftBosonField L (nprod ha hb) := by
  funext s
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; change liftBosonField L (nprod ha hb) s 0 = 0; rw [map_zero]
  | add x y hx hy =>
      rw [map_add, hx, hy]; change _ = liftBosonField L (nprod ha hb) s (x + y)
      rw [map_add]
  | tmul p g =>
      rw [nprod_apply]
      change _ = LinearMap.rTensor (L.carrier →₀ ℂ) (nprod ha hb s) (p ⊗ₜ[ℂ] g)
      rw [show (nprod ha hb s) = nprodCoeff ha hb s from rfl,
        LinearMap.rTensor_tmul (L.carrier →₀ ℂ) (nprodCoeff ha hb s) g p,
        show (nprodCoeff ha hb s p) = ∑ᶠ m : ℤ, normalOrdered a b m (s - m) p from rfl]
      have hfin : (Function.support
          (fun m : ℤ => normalOrdered a b m (s - m) p)).Finite :=
        normalOrdered_diag_support_finite ha hb s p
      rw [finsum_congr (fun m => by
        rw [show normalOrdered (liftBosonField L a) (liftBosonField L b) m (s - m) (p ⊗ₜ[ℂ] g)
            = LinearMap.rTensor (L.carrier →₀ ℂ) (normalOrdered a b m (s - m)) (p ⊗ₜ[ℂ] g) from by
              rw [normalOrdered_liftBosonField L a b m (s - m)],
          LinearMap.rTensor_tmul,
          show (normalOrdered a b m (s - m) p) ⊗ₜ[ℂ] g
            = ((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip g)
                (normalOrdered a b m (s - m) p) from rfl])]
      rw [← map_finsum ((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip g) hfin]
      rfl


theorem latticeNormalProduct_add_left (L : IntegralLattice) {a₁ a₂ b : FormalDist (End ℂ (LatModuleGen L))}
    (ha₁ : IsField a₁) (ha₂ : IsField a₂) (hb : IsField b)
    (hadd : IsField (a₁ + a₂)) (s : ℤ) (x : LatModuleGen L) :
    nprod hadd hb s x = nprod ha₁ hb s x + nprod ha₂ hb s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha₁ hb s x)
      (normalOrdered_diag_support_finite ha₂ hb s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change ((a₁ m + a₂ m) * b (s - m)) x = (a₁ m * b (s - m)) x + (a₂ m * b (s - m)) x
    rw [add_mul, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change (b (s - m) * (a₁ m + a₂ m)) x = (b (s - m) * a₁ m) x + (b (s - m) * a₂ m) x
    rw [mul_add, LinearMap.add_apply]


theorem latticeNormalProduct_add_right (L : IntegralLattice) {a b₁ b₂ : FormalDist (End ℂ (LatModuleGen L))}
    (ha : IsField a) (hb₁ : IsField b₁) (hb₂ : IsField b₂)
    (hadd : IsField (b₁ + b₂)) (s : ℤ) (x : LatModuleGen L) :
    nprod ha hadd s x = nprod ha hb₁ s x + nprod ha hb₂ s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha hb₁ s x)
      (normalOrdered_diag_support_finite ha hb₂ s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change (a m * (b₁ (s - m) + b₂ (s - m))) x = (a m * b₁ (s - m)) x + (a m * b₂ (s - m)) x
    rw [mul_add, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change ((b₁ (s - m) + b₂ (s - m)) * a m) x = (b₁ (s - m) * a m) x + (b₂ (s - m) * a m) x
    rw [add_mul, LinearMap.add_apply]


theorem latticeNormalProduct_congr (L : IntegralLattice) {a b a' b' : FormalDist (End ℂ (LatModuleGen L))}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') : nprod ha hb = nprod ha' hb' := by
  subst haa; subst hbb; rfl


noncomputable def momentumField (a : Fin (rank L)) : FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => if j = -1 then frameMomentum F a else 0


theorem momentumField_isField (a : Fin (rank L)) : IsField (momentumField F a) := by
  intro x; refine ⟨-1, fun n hn => ?_⟩
  show (if n = -1 then frameMomentum F a else 0) x = 0
  rw [if_neg (by omega : ¬ n = -1)]; rfl


theorem frameCurrent_eq (a : Fin (rank L)) :
    frameCurrent F a = liftBosonField L (currentN (rank L) 1 a) + momentumField F a := by
  funext j
  show frameCurrent F a j = liftBosonField L (currentN (rank L) 1 a) j + momentumField F a j
  rw [frameCurrent_apply, liftBosonField, momentumField]


theorem liftBosonField_currentN_isField (L : IntegralLattice) (a : Fin (rank L)) : IsField (liftBosonField L (currentN (rank L) 1 a)) :=
  liftBosonField_isField L (currentN_isField (rank L) 1 a)


theorem nprod_lift_momentumField (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftBosonField_currentN_isField L a) (momentumField_isField F a) s (mkEα L γ q)
      = frameCoordinate F γ a • mkEα L γ (currentN (rank L) 1 a (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ s + 1 →
      normalOrdered (liftBosonField L (currentN (rank L) 1 a)) (momentumField F a) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : momentumField F a (s - m) = 0 := by
      show (if s - m = -1 then frameMomentum F a else 0) = 0; rw [if_neg (by omega)]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m) * momentumField F a (s - m)) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (momentumField F a (s - m) * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
  have hZss : momentumField F a (s - (s + 1)) = frameMomentum F a := by
    show (if s - (s + 1) = -1 then frameMomentum F a else 0) = frameMomentum F a; rw [if_pos (by ring)]
  rw [finsum_eq_single _ (s + 1) hsupp, normalOrdered_apply, hZss]
  by_cases h0 : 0 ≤ s + 1
  · rw [if_pos h0]
    change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)) * frameMomentum F a)
      (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, frameMomentum_latStateGen,
      map_smul]
    change frameCoordinate F γ a • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (q ⊗ₜ[ℂ] eGen L γ) = _
    rw [LinearMap.rTensor_tmul]; rfl
  · rw [if_neg h0]
    change (frameMomentum F a * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
      (mkEα L γ q) = _
    rw [Module.End.mul_apply]
    change frameMomentum F a (latStateGen L (currentN (rank L) 1 a (s + 1) q) γ) = _
    rw [frameMomentum_latStateGen]; rfl


theorem nprod_momentumField_lift (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (momentumField_isField F a) (liftBosonField_currentN_isField L a) s (mkEα L γ q)
      = frameCoordinate F γ a • mkEα L γ (currentN (rank L) 1 a (s + 1) q) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ -1 →
      normalOrdered (momentumField F a) (liftBosonField L (currentN (rank L) 1 a)) m (s - m) (mkEα L γ q) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : momentumField F a m = 0 := by
      show (if m = -1 then frameMomentum F a else 0) = 0; rw [if_neg hm]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      change (momentumField F a m * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - m))) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - m)) * momentumField F a m) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
  have hZm1 : momentumField F a (-1) = frameMomentum F a := by
    show (if (-1 : ℤ) = -1 then frameMomentum F a else 0) = frameMomentum F a; rw [if_pos rfl]
  rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    hZm1]
  change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s - -1)) * frameMomentum F a)
    (mkEα L γ q) = _
  rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, frameMomentum_latStateGen,
    map_smul, show s - -1 = s + 1 from by ring]
  change frameCoordinate F γ a • (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a (s + 1)))
    (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl


theorem nprod_momentumField_momentumField (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (momentumField_isField F a) (momentumField_isField F a) s (mkEα L γ q)
      = if s = -2 then (frameCoordinate F γ a * frameCoordinate F γ a) • mkEα L γ q else 0 := by
  rw [nprod_apply]
  by_cases hs : s = -2
  · have hsupp : ∀ m : ℤ, m ≠ -1 →
        normalOrdered (momentumField F a) (momentumField F a) m (s - m) (mkEα L γ q) = 0 := by
      intro m hm
      rw [normalOrdered_apply]
      have hZ : momentumField F a m = 0 := by
        show (if m = -1 then frameMomentum F a else 0) = 0; rw [if_neg hm]
      by_cases h0 : 0 ≤ m
      · rw [if_pos h0]; change (momentumField F a m * momentumField F a (s - m)) _ = 0
        rw [hZ, zero_mul, LinearMap.zero_apply]
      · rw [if_neg h0]; change (momentumField F a (s - m) * momentumField F a m) _ = 0
        rw [hZ, mul_zero, LinearMap.zero_apply]
    have hZm1 : momentumField F a (-1) = frameMomentum F a := by
      show (if (-1 : ℤ) = -1 then frameMomentum F a else 0) = frameMomentum F a; rw [if_pos rfl]
    have hZsm : momentumField F a (s - -1) = frameMomentum F a := by
      show (if s - -1 = -1 then frameMomentum F a else 0) = frameMomentum F a; rw [if_pos (by omega)]
    rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
      hZm1, hZsm, if_pos hs]
    change (frameMomentum F a * frameMomentum F a) (mkEα L γ q) = _
    rw [Module.End.mul_apply, show mkEα L γ q = latStateGen L q γ from rfl, frameMomentum_latStateGen,
      map_smul, frameMomentum_latStateGen, smul_smul]
  · rw [if_neg hs]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      have hZ : momentumField F a m = 0 := by
        show (if m = -1 then frameMomentum F a else 0) = 0; rw [if_neg (by omega)]
      change (momentumField F a m * momentumField F a (s - m)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      by_cases hm1 : m = -1
      · subst hm1
        have hZ : momentumField F a (s - -1) = 0 := by
          show (if s - -1 = -1 then frameMomentum F a else 0) = 0; rw [if_neg (by omega)]
        change (momentumField F a (s - -1) * momentumField F a (-1)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
      · have hZ : momentumField F a m = 0 := by
          show (if m = -1 then frameMomentum F a else 0) = 0; rw [if_neg hm1]
        change (momentumField F a (s - m) * momentumField F a m) _ = 0; rw [hZ, mul_zero, LinearMap.zero_apply]


theorem nprod_lift_lift_tmul (L : IntegralLattice) (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (liftBosonField_currentN_isField L a) (liftBosonField_currentN_isField L a) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s q) := by
  have heq : nprod (liftBosonField_currentN_isField L a) (liftBosonField_currentN_isField L a)
      = liftBosonField L (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a)) :=
    liftBosonField_nprod L (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a)
  rw [heq]
  show LinearMap.rTensor (L.carrier →₀ ℂ)
      (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s) (q ⊗ₜ[ℂ] eGen L γ) = _
  rw [LinearMap.rTensor_tmul]; rfl


theorem nprod_frameCurrent_tmul (a : Fin (rank L)) (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    nprod (frameCurrent_isField F a) (frameCurrent_isField F a) s (mkEα L γ q)
      = mkEα L γ (nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s q)
        + (2 * frameCoordinate F γ a) • mkEα L γ (currentN (rank L) 1 a (s + 1) q)
        + (if s = -2 then (frameCoordinate F γ a * frameCoordinate F γ a) • mkEα L γ q else 0) := by
  classical
  have hAZ : IsField (liftBosonField L (currentN (rank L) 1 a) + momentumField F a) :=
    frameCurrent_eq F a ▸ frameCurrent_isField F a
  rw [latticeNormalProduct_congr L (frameCurrent_isField F a) (frameCurrent_isField F a) hAZ hAZ
      (frameCurrent_eq F a) (frameCurrent_eq F a)]
  rw [latticeNormalProduct_add_left L (liftBosonField_currentN_isField L a) (momentumField_isField F a) hAZ hAZ s (mkEα L γ q)]
  rw [latticeNormalProduct_add_right L (liftBosonField_currentN_isField L a) (liftBosonField_currentN_isField L a)
        (momentumField_isField F a) hAZ s (mkEα L γ q),
    latticeNormalProduct_add_right L (momentumField_isField F a) (liftBosonField_currentN_isField L a) (momentumField_isField F a)
        hAZ s (mkEα L γ q)]
  rw [nprod_lift_lift_tmul, nprod_lift_momentumField, nprod_momentumField_lift, nprod_momentumField_momentumField]
  rw [two_mul, add_smul]
  abel


theorem half_nprod_currentN (L : IntegralLattice) (a : Fin (rank L)) (s : ℤ) :
    (1 / 2 : ℂ) • nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 a) s
      = HeisenbergN.LvirNa (rank L) 1 a (-s - 2) := by
  rw [HeisenbergN.LvirNa, show -(-s - 2) - 2 = s from by ring,
    show (1 / (2 * 1) : ℂ) = (1 / 2 : ℂ) from by norm_num]


theorem frameOscillator_neg_apply (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    frameOscillator F γ (-s - 2) q
      = ∑ a : Fin (rank L), frameCoordinate F γ a • currentN (rank L) 1 a (s + 1) q := by
  rw [frameOscillator_eq_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.smul_apply, currentN_apply, show -(s + 1) - 1 = -s - 2 from by ring]


theorem frameSugawaraField_tmul  (s : ℤ) (q : FockN (rank L)) (γ : L.carrier) :
    frameSugawaraField F s (latStateGen L q γ)
      = latStateGen L (HeisenbergN.LvirN (rank L) 1 (-s - 2) q) γ
        + latStateGen L (frameOscillator F γ (-s - 2) q) γ
        + (if s = -2 then ((1 / 2 : ℂ) * ((L.form γ γ : ℤ) : ℂ)) • latStateGen L q γ else 0) := by
  classical
  rw [frameSugawaraField]
  change (1 / 2 : ℂ) • (((∑ a : Fin (rank L),
      nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) s) (mkEα L γ q)) = _
  rw [show ((∑ a : Fin (rank L),
          nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) s : End ℂ (LatModuleGen L))
        = ∑ a : Fin (rank L), nprod (frameCurrent_isField F a) (frameCurrent_isField F a) s from
      Finset.sum_apply (s := Finset.univ)
        (g := fun a : Fin (rank L) => nprod (frameCurrent_isField F a) (frameCurrent_isField F a)) s,
    LinearMap.coe_sum, Finset.sum_apply,
    Finset.sum_congr rfl (fun a _ => nprod_frameCurrent_tmul F a s q γ),
    Finset.sum_add_distrib, Finset.sum_add_distrib, smul_add, smul_add]
  congr 1
  · congr 1
    · 
      rw [← map_sum (mkEα L γ), ← map_smul (mkEα L γ)]
      refine congrArg (mkEα L γ) ?_
      rw [HeisenbergN.LvirN_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← half_nprod_currentN L a s, LinearMap.smul_apply]
    · 
      rw [Finset.sum_congr rfl (fun a _ => (map_smul (mkEα L γ) (2 * frameCoordinate F γ a)
          (currentN (rank L) 1 a (s + 1) q)).symm),
        ← map_sum (mkEα L γ), ← map_smul (mkEα L γ)]
      refine congrArg (mkEα L γ) ?_
      
      rw [frameOscillator_neg_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [smul_smul]
      congr 1
      ring
  · 
    by_cases hs : s = -2
    · rw [Finset.sum_congr rfl (fun a _ => by rw [if_pos hs]), if_pos hs,
        ← Finset.sum_smul, smul_smul, frameCoordinate_pairing F γ γ]
      rfl
    · rw [Finset.sum_congr rfl (fun a _ => by rw [if_neg hs]), if_neg hs,
        Finset.sum_const_zero, smul_zero]


end VOA.Moonshine.ConwayNorton
