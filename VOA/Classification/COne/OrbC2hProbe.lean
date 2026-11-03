import VOA.Classification.COne.OrbC2gDiagnostic

/-! The neutral oscillator functional on all negative Virasoro descendants. -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial PlusC2 OrbC2b OrbC2c OrbC2e OrbC2f OrbC2g LatMod

theorem firstOscillator_osc_neg (a : Fin (rank (latP 4))) (j : ℤ)
    (hj : j < 0) (p : FockN (rank (latP 4))) :
    firstOscillator (oscN (rank (latP 4)) 1 a j p) =
      (if j = -1 then 1 else 0) * firstOscillator p := by
  rw [oscN_apply_neg _ _ _ hj, map_mul]
  simp only [firstOscillator, aeval_X]
  change (if (-j-1).toNat = 0 then (1:ℂ) else 0) * _ = _
  have h : (-j-1).toNat = 0 ↔ j = -1 := by omega
  simp only [h]

theorem firstOscillator_sugTerm (k : ℕ) (a : Fin (rank (latP 4)))
    (j : ℤ) (p : FockN (rank (latP 4))) :
    firstOscillator (sugTermN (rank (latP 4)) 1 a (-(k:ℤ)-1) j p) =
      if k = 1 ∧ j = -1 then firstOscillator p else 0 := by
  rw [sugTermN_apply]
  by_cases hj : j < 0
  · rw [if_pos hj, firstOscillator_osc_neg a j hj]
    by_cases he : j = -1
    · subst j
      simp only [sub_neg_eq_add, sub_add_cancel, if_true, one_mul, and_true]
      cases k with
      | zero => simp [oscN_zero]
      | succ k =>
        rw [firstOscillator_osc_neg a _ (by omega)]
        split_ifs <;> simp_all
    · simp [he]
  · rw [if_neg hj, firstOscillator_osc_neg a _ (by omega)]
    by_cases he : -(k:ℤ)-1-j = -1
    · have hk : k = 0 := by omega
      have hj0 : j = 0 := by omega
      subst k; subst j
      simp [oscN_zero]
    · rw [if_neg he, zero_mul, if_neg]
      rintro ⟨_, rfl⟩
      omega

theorem firstOscillator_LvirN (k : ℕ) (p : FockN (rank (latP 4))) :
    firstOscillator (LvirN (rank (latP 4)) 1 (-(k:ℤ)-1) p) =
      (if k = 1 then (1/2 : ℂ) else 0) * firstOscillator p := by
  rw [LvirN_apply, map_sum]
  have ht (a : Fin (rank (latP 4))) :
      firstOscillator (LvirNa (rank (latP 4)) 1 a (-(k:ℤ)-1) p) =
        (if k = 1 then (1/2 : ℂ) else 0) * firstOscillator p := by
    rw [LvirNa_apply', map_smul]
    rw [show firstOscillator (∑ᶠ j : ℤ, sugTermN (rank (latP 4)) 1 a (-(k:ℤ)-1) j p) =
      ∑ᶠ j : ℤ, firstOscillator (sugTermN (rank (latP 4)) 1 a (-(k:ℤ)-1) j p) from
      map_finsum firstOscillator.toLinearMap (sugTermN_support_finite _ _ _ _ _)]
    simp only [firstOscillator_sugTerm]
    by_cases hk : k = 1
    · simp only [hk, true_and, if_true]
      rw [finsum_eq_single _ (-1)]
      · simp
      · intro j hj; simp [hj]
    · simp [hk]
  simp only [ht]
  simp [Finset.sum_const, rank_latP]

theorem coord_LLGen (n : ℤ) (p : LatModuleGen (latP 4)) :
    coordEα (latP 4) 0 (LLGen (latP 4) n p) =
      LvirN (rank (latP 4)) 1 n (coordEα (latP 4) 0 p) := by
  let f := (coordEα (latP 4) 0).comp (LLGen (latP 4) n)
  let g := (LvirN (rank (latP 4)) 1 n).comp (coordEα (latP 4) 0)
  change f p = g p
  suffices f = g by rw [this]
  apply LinearMap.ext_on_range (latStateGen_span (latP 4))
  rintro ⟨q,d⟩
  change coordEα (latP 4) 0 (LLGen (latP 4) n (latStateGen (latP 4) q d)) = _
  rw [LLGen_tmul _ (latP_posDef 4 four_ge_one), map_add, map_add]
  dsimp only [g, LinearMap.comp_apply]
  simp only [latStateGen, coordEα_apply]
  by_cases hd : (0 : (latP 4).carrier) = d
  · subst d
    simp [chargeOsc_apply_sum, chargeCoord_zero]
  · split_ifs <;> simp [hd, map_smul, coordEα_apply]

theorem neutralProbe_L (k : ℕ) (p : LatModuleGen (latP 4)) :
    neutralProbe ((V2m 4 four_ge_one).L (-(k:ℤ)-1) p) =
      (if k = 1 then (1/2 : ℂ) else 0) * neutralProbe p := by
  change firstOscillator (coordEα (latP 4) 0
    (mode (YfullGen (latP 4) (latP_even 4) (latP_posDef 4 four_ge_one) (omegaLatGen (latP 4))) _ p)) = _
  rw [mode_YfullGen_omega_eq_LLGen, coord_LLGen, firstOscillator_LvirN]
  rfl


noncomputable def plusProbe : VP 4 four_ge_one →ₗ[ℂ] ℂ :=
  neutralProbe.comp (PlusC2.VP 4 four_ge_one).subtype

theorem plusProbe_L (k : ℕ) (p : VP 4 four_ge_one) :
    plusProbe ((V2mPlus 4 four_ge_one).L (-(k:ℤ)-1) p) =
      (if k = 1 then (1/2 : ℂ) else 0) * plusProbe p :=
  neutralProbe_L k p

theorem plusProbe_vacuum : plusProbe (V2mPlus 4 four_ge_one).vacuum = 1 := by
  change firstOscillator (coordEα (latP 4) 0 (latStateGen (latP 4) 1 0)) = 1
  simp [latStateGen, coordEα_apply]

theorem plusProbe_L_pow (n : ℕ) (p : VP 4 four_ge_one) :
    plusProbe (((V2mPlus 4 four_ge_one).L (-2) ^ n) p) =
      (1/2 : ℂ)^n * plusProbe p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, show (-2:ℤ) = -(1:ℕ)-1 by norm_num,
      plusProbe_L, if_pos rfl]
    rw [show (-(1:ℕ)-1:ℤ) = -2 by norm_num, ih, pow_succ']
    ring

theorem plusProbe_virWord_bad (ks : List ℕ) (p : VP 4 four_ge_one)
    (h : ∃ k ∈ ks, k ≠ 1) : plusProbe (virWord (V2mPlus 4 four_ge_one) ks p) = 0 := by
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    rw [virWord, plusProbe_L]
    by_cases hk : k = 1
    · subst k
      rw [ih (by simpa using h), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem virError_le_ker_plusProbe (p : VP 4 four_ge_one) :
    virError (V2mPlus 4 four_ge_one) p ≤ plusProbe.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨ks,hks⟩,rfl⟩
  exact plusProbe_virWord_bad ks p hks

theorem remainder_probe (X : VP 4 four_ge_one) (n : ℤ) (p q : ℕ) (a b : ℂ)
    (h : modeRemainder (V2mPlus 4 four_ge_one) normalizedNine X n p q a b ∈
      virError (V2mPlus 4 four_ge_one) (V2mPlus 4 four_ge_one).vacuum ⊔
      virError (V2mPlus 4 four_ge_one) X) :
    plusProbe ((V2mPlus 4 four_ge_one).smul normalizedNine n normalizedNine) =
      a * (1/2:ℂ)^p + b * (1/2:ℂ)^q * plusProbe X := by
  have hh := (sup_le (virError_le_ker_plusProbe _) (virError_le_ker_plusProbe X)) h
  change plusProbe (modeRemainder _ _ _ _ _ _ _ _) = 0 at hh
  rw [modeRemainder, map_sub, map_add, map_smul, map_smul,
    plusProbe_L_pow, plusProbe_L_pow, plusProbe_vacuum] at hh
  simpa [smul_eq_mul, mul_assoc] using sub_eq_zero.mp hh

/-- The two scalar measurements exclude every existential witness X and t. -/
theorem not_cubicSeedRemainders_of_probes
    (h20 : plusProbe ((V2mPlus 4 four_ge_one).smul normalizedNine (-3) normalizedNine) =
      (djC20:ℂ)/13)
    (h22 : plusProbe ((V2mPlus 4 four_ge_one).smul normalizedNine (-5) normalizedNine) =
      (djC22:ℂ)) : ¬ CubicSeedRemainders := by
  rintro ⟨X,t,_,_,r20,r22⟩
  have e20 := remainder_probe X (-3) 10 2 _ _ r20
  have e22 := remainder_probe X (-5) 11 3 _ _ r22
  rw [h20] at e20
  rw [h22] at e22
  norm_num [djC20, djC22, djB20, djB22] at e20 e22
  have ht : plusProbe X = t := by
    linear_combination (norm := ring_nf) -(1513512/19408720:ℂ) * e22
  rw [ht] at e20
  ring_nf at e20
  norm_num at e20

end VOA.Classification.COne.OrbC2h
