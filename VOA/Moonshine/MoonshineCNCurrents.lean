import VOA.Moonshine.MoonshineCNChargedLocality
import VOA.Moonshine.MoonshineCNGrading

/-!
# Complex-frame lattice construction: Currents

Structural adaptation of `LatticeGenBosonFields` using a complex bilinear
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

noncomputable def frameCoordinate (α : L.carrier) (a : Fin (rank L)) : ℂ := F.coordinate α a

theorem frameCoordinate_pairing (α β : L.carrier) :
    ∑ a, frameCoordinate F α a * frameCoordinate F β a = (L.form α β : ℂ) :=
  F.pairing α β

noncomputable abbrev canonicalChargedField (α : L.carrier) :=
  chargedField F (latticeCocycle L) α

theorem canonicalChargedField_tmul (α β : L.carrier) (t : ℤ) (p : FockN (rank L)) :
    canonicalChargedField F α t (latStateGen L p β) =
      latticeCocycle L α β • latStateGen L (dressingField F α (t - L.form α β) p) (α + β) :=
  chargedField_tmul F (latticeCocycle L) α β t p

theorem canonicalChargedField_vacuum (α : L.carrier) (t : ℤ) :
    canonicalChargedField F α t (latVacuumGen L) =
      if 0 ≤ t then latStateGen L (creationCoefficient F α t.toNat) α else 0 :=
  chargedField_vacuum F (latticeCocycle L) (latticeCocycle_zero_right L) α t

theorem canonicalChargedField_creation_z0 (α : L.carrier) :
    canonicalChargedField F α 0 (latVacuumGen L) = latChargeGen L α :=
  chargedField_creation_z0 F (latticeCocycle L) (latticeCocycle_zero_right L) α

theorem canonicalChargedField_creation_nonneg (α : L.carrier) {n : ℤ} (hn : 0 ≤ n) :
    mode (canonicalChargedField F α) n (latVacuumGen L) = 0 :=
  chargedField_creation_nonneg F (latticeCocycle L) (latticeCocycle_zero_right L) α hn

theorem canonicalChargedField_mode_neg_one_vacuum (α : L.carrier) :
    mode (canonicalChargedField F α) (-1) (latVacuumGen L) = latChargeGen L α :=
  chargedField_mode_neg_one_vacuum F (latticeCocycle L) (latticeCocycle_zero_right L) α

theorem canonicalChargedField_isField (α : L.carrier) : IsField (canonicalChargedField F α) :=
  chargedField_isField F _ α

theorem canonicalChargedField_local (hEven : L.Even) (α β : L.carrier) :
    Local (canonicalChargedField F α) (canonicalChargedField F β) :=
  chargedField_local F (canonicalChargeCommutationFactors L hEven) α β

theorem frameCoordinate_zero (a : Fin (rank L)) : frameCoordinate F (0 : L.carrier) a = 0 := by
  exact congrFun F.coordinate.map_zero a

noncomputable def groupMomentum (a : Fin (rank L)) : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ (fun γ => (frameCoordinate F γ a) •
    (Finsupp.lsingle γ : ℂ →ₗ[ℂ] (L.carrier →₀ ℂ)))


theorem groupMomentum_eGen (a : Fin (rank L)) (β : L.carrier) :
    groupMomentum F a (eGen L β) = (frameCoordinate F β a) • eGen L β := by
  rw [groupMomentum]
  show (Finsupp.lsum ℂ (fun γ => (frameCoordinate F γ a) •
      (Finsupp.lsingle γ : ℂ →ₗ[ℂ] (L.carrier →₀ ℂ)))) (Finsupp.single β 1) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]
  simp only [eGen]


noncomputable def frameMomentum (a : Fin (rank L)) : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  LinearMap.lTensor (FockN (rank L)) (groupMomentum F a)


theorem frameMomentum_latStateGen (a : Fin (rank L)) (p : FockN (rank L)) (β : L.carrier) :
    frameMomentum F a (latStateGen L p β)
      = (frameCoordinate F β a) • latStateGen L p β := by
  rw [frameMomentum, latStateGen, LinearMap.lTensor_tmul, groupMomentum_eGen, TensorProduct.tmul_smul]


theorem frameMomentum_vacuum (a : Fin (rank L)) : frameMomentum F a (latVacuumGen L) = 0 := by
  rw [latVacuumGen, frameMomentum_latStateGen, frameCoordinate_zero, zero_smul]


noncomputable def liftBosonField (L : IntegralLattice) (f : FormalDist (End ℂ (FockN (rank L)))) :
    FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => LinearMap.rTensor (L.carrier →₀ ℂ) (f j)


noncomputable def liftBosonDistribution (L : IntegralLattice) (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    FormalDist₂ (End ℂ (LatModuleGen L)) :=
  fun m n => LinearMap.rTensor (L.carrier →₀ ℂ) (F m n)


theorem liftBosonDistribution_zero (L : IntegralLattice) : liftBosonDistribution L (0 : FormalDist₂ (End ℂ (FockN (rank L)))) = 0 := by
  funext m n
  change LinearMap.rTensor (L.carrier →₀ ℂ) (0 : End ℂ (FockN (rank L))) = 0
  rw [LinearMap.rTensor_zero]


theorem tensorEndomorphism_mul (L : IntegralLattice) (f g : End ℂ (FockN (rank L))) :
    LinearMap.rTensor (L.carrier →₀ ℂ) (f * g)
      = LinearMap.rTensor (L.carrier →₀ ℂ) f * LinearMap.rTensor (L.carrier →₀ ℂ) g := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp]


theorem bracketDist_liftBosonField (L : IntegralLattice) (f g : FormalDist (End ℂ (FockN (rank L)))) :
    bracketDist (liftBosonField L f) (liftBosonField L g) = liftBosonDistribution L (bracketDist f g) := by
  funext m n
  rw [bracketDist_apply]
  change LinearMap.rTensor (L.carrier →₀ ℂ) (f m) * LinearMap.rTensor (L.carrier →₀ ℂ) (g n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (g n) * LinearMap.rTensor (L.carrier →₀ ℂ) (f m)
    = LinearMap.rTensor (L.carrier →₀ ℂ) ((bracketDist f g) m n)
  rw [bracketDist_apply, ← tensorEndomorphism_mul, ← tensorEndomorphism_mul, ← LinearMap.rTensor_sub]


theorem mulBySub_liftBosonDistribution (L : IntegralLattice) (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    mulBySub (liftBosonDistribution L F) = liftBosonDistribution L (mulBySub F) := by
  funext m n
  rw [mulBySub_apply]
  change LinearMap.rTensor (L.carrier →₀ ℂ) (F (m - 1) n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (F m (n - 1))
    = LinearMap.rTensor (L.carrier →₀ ℂ) ((mulBySub F) m n)
  rw [mulBySub_apply, ← LinearMap.rTensor_sub]


theorem mulBySubPow_liftBosonDistribution (L : IntegralLattice) (N : ℕ) (F : FormalDist₂ (End ℂ (FockN (rank L)))) :
    mulBySubPow N (liftBosonDistribution L F) = liftBosonDistribution L (mulBySubPow N F) := by
  induction N generalizing F with
  | zero => rw [mulBySubPow_zero, mulBySubPow_zero]; rfl
  | succ n ih =>
      have h1 : mulBySubPow (n + 1) (liftBosonDistribution L F) = mulBySub (mulBySubPow n (liftBosonDistribution L F)) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      have h2 : mulBySubPow (n + 1) F = mulBySub (mulBySubPow n F) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      rw [h1, ih, mulBySub_liftBosonDistribution, h2]


theorem Local_liftBosonField (L : IntegralLattice) {f g : FormalDist (End ℂ (FockN (rank L)))} (h : Local f g) :
    Local (liftBosonField L f) (liftBosonField L g) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [bracketDist_liftBosonField, mulBySubPow_liftBosonDistribution, hN, liftBosonDistribution_zero]⟩


theorem liftBosonField_isField (L : IntegralLattice) {f : FormalDist (End ℂ (FockN (rank L)))} (hf : IsField f) :
    IsField (liftBosonField L f) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (liftBosonField L f n).map_zero⟩
  | tmul p g =>
      obtain ⟨Bp, hBp⟩ := hf p
      refine ⟨Bp, fun n hn => ?_⟩
      change LinearMap.rTensor (L.carrier →₀ ℂ) (f n) (p ⊗ₜ[ℂ] g) = 0
      rw [LinearMap.rTensor_tmul, hBp n hn, TensorProduct.zero_tmul]
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (liftBosonField L f n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]


noncomputable def frameCurrent (a : Fin (rank L)) : FormalDist (End ℂ (LatModuleGen L)) :=
  fun j => LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j)
    + (if j = -1 then frameMomentum F a else 0)


theorem frameCurrent_apply (a : Fin (rank L)) (j : ℤ) :
    frameCurrent F a j = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a j)
      + (if j = -1 then frameMomentum F a else 0) := rfl


theorem frameCurrent_isField (a : Fin (rank L)) : IsField (frameCurrent F a) := by
  intro x
  obtain ⟨B, hB⟩ := liftBosonField_isField L (currentN_isField (rank L) 1 a) x
  refine ⟨min B (-1), fun n hn => ?_⟩
  rw [frameCurrent_apply, if_neg (by omega : ¬ n = -1), LinearMap.add_apply, LinearMap.zero_apply,
    add_zero]
  exact hB n (lt_of_lt_of_le hn (min_le_left _ _))


theorem frameMomentum_comm_rTensor (a : Fin (rank L)) (f : End ℂ (FockN (rank L))) :
    frameMomentum F a * (LinearMap.rTensor (L.carrier →₀ ℂ) f)
      = (LinearMap.rTensor (L.carrier →₀ ℂ) f) * frameMomentum F a := by
  simp only [frameMomentum, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]


theorem frameMomentum_comm (a b : Fin (rank L)) :
    frameMomentum F a * frameMomentum F b = frameMomentum F b * frameMomentum F a := by
  simp only [frameMomentum, Module.End.mul_eq_comp, ← LinearMap.lTensor_comp]
  congr 1
  refine Finsupp.lhom_ext fun γ c => ?_
  simp only [LinearMap.comp_apply, show (Finsupp.single γ c : L.carrier →₀ ℂ)
    = c • eGen L γ from by rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one], map_smul,
    groupMomentum_eGen, map_smul, groupMomentum_eGen, smul_smul, mul_comm]


theorem bracketDist_frameCurrent (a b : Fin (rank L)) :
    bracketDist (frameCurrent F a) (frameCurrent F b)
      = bracketDist (liftBosonField L (currentN (rank L) 1 a)) (liftBosonField L (currentN (rank L) 1 b)) := by
  have key : ∀ (Am An cm cn : End ℂ (LatModuleGen L)),
      cn * Am = Am * cn → cm * An = An * cm → cm * cn = cn * cm →
      (Am + cm) * (An + cn) - (An + cn) * (Am + cm) = Am * An - An * Am := by
    intro Am An cm cn h1 h2 h3
    simp only [mul_add, add_mul]; rw [h1, h2, h3]; abel
  funext m n
  rw [bracketDist_apply, bracketDist_apply]
  change (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
          + (if m = -1 then frameMomentum F a else 0))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
          + (if n = -1 then frameMomentum F b else 0))
      - (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
          + (if n = -1 then frameMomentum F b else 0))
        * (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
          + (if m = -1 then frameMomentum F a else 0))
    = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
        * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
      - LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b n)
        * LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a m)
  refine key _ _ _ _ ?_ ?_ ?_
  · by_cases hn : n = -1
    · rw [if_pos hn, frameMomentum_comm_rTensor]
    · rw [if_neg hn, zero_mul, mul_zero]
  · by_cases hm : m = -1
    · rw [if_pos hm, frameMomentum_comm_rTensor]
    · rw [if_neg hm, zero_mul, mul_zero]
  · by_cases hm : m = -1 <;> by_cases hn : n = -1
    · rw [if_pos hm, if_pos hn, frameMomentum_comm]
    · rw [if_pos hm, if_neg hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_pos hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_neg hn, mul_zero]


theorem frameCurrent_self_local (a b : Fin (rank L)) :
    Local (frameCurrent F a) (frameCurrent F b) := by
  rw [Local, bracketDist_frameCurrent]
  exact Local_liftBosonField L (currentN_local (rank L) 1 a b)


noncomputable def frameDerivativeCurrent (a : Fin (rank L)) (i : ℕ) : FormalDist (End ℂ (LatModuleGen L)) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (frameCurrent F a))


theorem frameDerivativeCurrent_isField (a : Fin (rank L)) (i : ℕ) : IsField (frameDerivativeCurrent F a i) := by
  intro x
  obtain ⟨B, hB⟩ := (frameCurrent_isField F a).deriv_iterate i x
  exact ⟨B, fun n hn => by
    change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (frameCurrent F a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩


theorem frameDerivativeCurrent_zero (a : Fin (rank L)) : frameDerivativeCurrent F a 0 = frameCurrent F a := by
  rw [frameDerivativeCurrent, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]


theorem dframeCurrent_local (a b : Fin (rank L)) (i j : ℕ) :
    Local (VOA.deriv^[i] (frameCurrent F a)) (VOA.deriv^[j] (frameCurrent F b)) :=
  ((frameCurrent_self_local F a b).deriv_iterate_left i).deriv_iterate_right j


theorem frameDerivativeCurrent_local (a b : Fin (rank L)) (i j : ℕ) :
    Local (frameDerivativeCurrent F a i) (frameDerivativeCurrent F b j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (frameCurrent F a)))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] (frameCurrent F b)))
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dframeCurrent_local F a b i j))


theorem frameCurrent_vacuum_neg (a : Fin (rank L)) {q : ℤ} (hq : q < 0) :
    frameCurrent F a q (latVacuumGen L) = 0 := by
  rw [frameCurrent_apply, LinearMap.add_apply]
  have hb : LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a q) (latVacuumGen L) = 0 := by
    rw [latVacuumGen, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
      oscN_vacuum (rank L) 1 a (-q - 1) (by omega), TensorProduct.zero_tmul]
  rw [hb, zero_add]
  by_cases hq1 : q = -1
  · rw [if_pos hq1, frameMomentum_vacuum]
  · rw [if_neg hq1]; rfl


theorem frameDerivativeCurrent_vacuum_neg (a : Fin (rank L)) (i : ℕ) {q : ℤ} (hq : q < 0) :
    frameDerivativeCurrent F a i q (latVacuumGen L) = 0 := by
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (frameCurrent F a)) q) (latVacuumGen L) = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [frameCurrent_vacuum_neg F a (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]


theorem frameDerivativeCurrent_zero_op (a : Fin (rank L)) (i : ℕ) :
    (frameDerivativeCurrent F a i) 0 = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a i) := by
  change (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (frameCurrent F a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, frameCurrent_apply,
    if_neg (by omega : ¬ (i : ℤ) = -1), add_zero]


end VOA.Moonshine.ConwayNorton
