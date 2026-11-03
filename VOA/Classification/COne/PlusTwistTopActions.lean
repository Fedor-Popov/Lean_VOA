import VOA.Classification.COne.PlusTwistTopSpaces

/-! # Actual E zero modes on the lowest vectors of the twisted plus modules -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusTwistLattice
open VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.Moonshine.LatticeTwistedGeneral
open VOA.TwistedHeisenberg VOA.TwistedSector VOA.TwistedPlus
open VOA.Moonshine.LatticeTwisted MvPolynomial PlusUnitary PlusCharacterTable
open scoped TensorProduct

/-- The vacuum or the first oscillator, in the actual rank of `latP`. -/
def oscillatorTop (m : ℕ) (odd : Bool) : FockT (rank (latP m)) :=
  if odd then X (0, LatMod.a0 m) else 1

theorem oscillatorTop_mem (m : ℕ) (odd : Bool) :
    oscillatorTop m odd ∈ gradingT (rank (latP m)) odd.toNat := by
  cases odd
  · change (1 : FockT _) ∈ gradingT _ 0
    rw [gradingT_zero]
    exact Submodule.mem_span_singleton_self _
  · simpa [oscillatorTop, gradingT, wT] using
      isWeightedHomogeneous_X ℂ (wT (r := rank (latP m))) (0, LatMod.a0 m)

theorem oscillatorTop_ne_zero (m : ℕ) (odd : Bool) : oscillatorTop m odd ≠ 0 := by
  cases odd
  · exact one_ne_zero
  · exact X_ne_zero _

def topTensor (m : ℕ) (odd : Bool) : FockT (rank (latP m)) ⊗[ℂ] ℂ :=
  oscillatorTop m odd ⊗ₜ 1

theorem topTensor_mem (m : ℕ) (odd : Bool) :
    topTensor m odd ∈ GT (rank (latP m)) ℂ odd.toNat :=
  tmul_mem_twGrading _ _ (oscillatorTop_mem m odd) 1

theorem topTensor_ne_zero (m : ℕ) (odd : Bool) : topTensor m odd ≠ 0 := by
  intro hz
  have h := congrArg (TensorProduct.rid ℂ (FockT (rank (latP m)))) hz
  simp only [topTensor, TensorProduct.rid_tmul, one_smul, map_zero] at h
  exact oscillatorTop_ne_zero m odd h

/-- A nonzero vector in each of the four ordinary modules. -/
def topVector (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    plusSub (parityLift (latP m) (latP_even m) (charge m t) (latP_posDef m hm) odd) :=
  ⟨topTensor m odd, by
    rw [mem_plusSub, parityLift_op_grade (latP m) (latP_even m) (charge m t) (latP_posDef m hm)
      odd odd.toNat _ (topTensor_mem m odd),
      (show Even (odd.toNat + odd.toNat) from ⟨odd.toNat, rfl⟩).neg_one_pow, one_smul]⟩

theorem topVector_mem (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    topVector m hm t odd ∈ (fourModules m hm t odd).weight (bottom odd) := by
  change topTensor m odd ∈ weightLT (rank (latP m)) ℂ (bottom odd)
  rw [← level_bottom m odd, weightLT_level]
  exact topTensor_mem m odd

theorem topVector_ne_zero (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    topVector m hm t odd ≠ 0 := by
  intro hz
  exact topTensor_ne_zero m odd (congrArg Subtype.val hz)

theorem dressing_zero_first_rank {r : ℕ} (hr : r = 1) (v : Fin r → ℂ) (a : Fin r) :
    DD v 0 (X (0, a)) = (1 - 2 * v a * v a) • X (0, a) := by
  subst r
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim _ _)
  conv_lhs => rw [hv]
  exact PlusTwistedOscillators.dressing_zero_first (v 0)

theorem dressing_top (m : ℕ) (hm : 1 ≤ m) (odd : Bool) :
    DD (chargeCoord (latP m) (1 : ℤ)) 0 (oscillatorTop m odd) =
      (if odd then 1 - 4 * (m : ℂ) else 1) • oscillatorTop m odd := by
  cases odd
  · change DD _ 0 (1 : FockT _) = (1 : ℂ) • 1
    rw [DD_one]
    simp [sMz]
  · change DD _ 0 (X (0, LatMod.a0 m)) = _
    rw [dressing_zero_first_rank (rank_latP m)]
    change (1 - 2 * PlusC2.cα m * PlusC2.cα m) • _ = (1 - 4 * (m : ℂ)) • _
    congr 1
    rw [mul_assoc, PlusC2.cα_sq m hm]
    ring

/-- The scalar prescribed for the E action on each of the four tops. -/
def eValue (m : ℕ) (t : ZMod 2) (odd : Bool) : ℂ :=
  (twistedScale m : ℂ) * VOA.Moonshine.Extraspecial.sgn t *
    (if odd then 1 - 4 * (m : ℂ) else 1)


theorem YML_charge (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (a k : ℤ) :
    VOA.Moonshine.LatticeTwistedGeneral.YML (latP m) (latP_even m) (charge m t)
      (VOA.LatGen.latChargeGen (latP m) a) k =
    VOA.Moonshine.LatticeTwistedGeneral.YTL (latP m) (latP_even m) (charge m t) a k := by
  rw [VOA.Moonshine.LatticeTwistedGeneral.YML_apply]
  change mode (VOA.Moonshine.LatticeTwistedGeneral.FL (latP m) (latP_even m) (charge m t)
    k (echg (latP m) a)).1 0 = _
  rw [VOA.Moonshine.LatticeTwistedGeneral.FL_echg _ _ _ (latP_posDef m hm),
    VOA.Moonshine.LatticeTwistedGeneral.mode_YTLFld]
  simp only [mul_zero, zero_add]

theorem YML_E (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) :
    VOA.Moonshine.LatticeTwistedGeneral.YML (latP m) (latP_even m) (charge m t)
      (EP m hm).1 (2 * ((m : ℤ) - 1)) =
    (2 : ℂ) • VOA.Moonshine.LatticeTwistedGeneral.YTL
      (latP m) (latP_even m) (charge m t) (1 : ℤ) (2 * ((m : ℤ) - 1)) := by
  simp only [EP_coe, map_add, Pi.add_apply, YML_charge m hm t]
  have hn := VOA.Moonshine.LatticeTwistedGeneral.YTL_neg
    (latP m) (latP_even m) (charge m t) (1 : ℤ) (2 * ((m : ℤ) - 1))
  rw [(show _root_.Even (2 * ((m : ℤ) - 1)) from ⟨(m : ℤ) - 1, by ring⟩).neg_one_zpow,
    one_smul] at hn
  rw [two_smul]
  exact congrArg (fun F => VOA.Moonshine.LatticeTwistedGeneral.YTL
    (latP m) (latP_even m) (charge m t) (1 : ℤ) (2 * ((m : ℤ) - 1)) + F) hn

theorem E_topTensor (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    VOA.Moonshine.LatticeTwistedGeneral.YML (latP m) (latP_even m) (charge m t)
      (EP m hm).1 (2 * ((m : ℤ) - 1)) (topTensor m odd) =
    eValue m t odd • topTensor m odd := by
  rw [YML_E, LinearMap.smul_apply, topTensor]
  erw [
    VOA.Moonshine.LatticeTwistedGeneral.YTL_tmul (latP m) (latP_even m)
      (charge m t) (1 : ℤ) _ (oscillatorTop m odd) (1 : ℂ)]
  have hf : (latP m).form (1 : ℤ) (1 : ℤ) = 2 * (m : ℤ) := by
    simp [latP_form]
  rw [hf, show -(2 * ((m : ℤ) - 1)) - 2 + 2 * (m : ℤ) = 0 by ring,
    dressing_top m hm]
  have he : VOA.Moonshine.LatticeTwistedGeneral.eT (latP m) (latP_even m)
      (charge m t) (1 : ℤ) (1 : ℂ) = VOA.Moonshine.Extraspecial.sgn t := by
    change PlusTwistedCharge.eT m t (1 : ℤ) 1 = _
    rw [PlusTwistedCharge.eT_generator]
    simp
  rw [he]
  change (2 : ℂ) • ((2 : ℂ) ^ (-(2 * (m : ℤ))) •
    (((if odd then 1 - 4 * (m : ℂ) else 1) • oscillatorTop m odd) ⊗ₜ[ℂ]
      VOA.Moonshine.Extraspecial.sgn t)) =
    eValue m t odd • (oscillatorTop m odd ⊗ₜ[ℂ] (1 : ℂ))
  apply (TensorProduct.rid ℂ (FockT (rank (latP m)))).injective
  simp only [map_smul, TensorProduct.rid_tmul, one_smul, smul_smul]
  congr 1
  rw [eValue]
  simp only [twistedScale, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  rw [show -(2 * (m : ℤ)) = -((2 * m : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]
  ring

/-- The candidate scalar is the actual E zero mode of the constructed module. -/
theorem topVector_E (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    oMod (fourModules m hm t odd) (EP m hm) (topVector m hm t odd) =
      eValue m t odd • topVector m hm t odd := by
  rw [oMod_homogeneous _ (EP_mem_grading m hm)]
  apply Subtype.ext
  change ((mode ((parityModule (latP m) (latP_even m) (charge m t)
    (latP_posDef m hm) odd).YM (EP m hm)) ((m : ℤ) - 1)
    (topVector m hm t odd) : plusSub _) : VOA.Moonshine.LatticeTwistedGeneral.MT (latP m) (latP_even m) (charge m t)) = _
  rw [mode_parityModule]
  exact E_topTensor m hm t odd

end VOA.Classification.COne.PlusTwistLattice
