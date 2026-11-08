import VOA.Moonshine.MoonshineLRSigmaB
import VOA.Moonshine.MonsterGriess.TrialityLabels

/-!
# Odd triality columns in spin coordinates

The normalized odd columns are single oscillator columns. Their charge coordinates
are a rational sign times `Rmat c` applied to one normalized seed. Minus-root
characters and the frame sector force the seed to have a single nonzero coordinate.
The invariant form forces its square to be one, proving rationality of the seed,
all odd columns, and triality on the full Griess dictionary, hence liftability.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.SigmaTop VOA.Moonshine.SigmaAssemble VOA.Moonshine.TrialityTw
open VOA.Moonshine.SigmaExist
open VOA.Moonshine.MonsterAction Matrix
open VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.InvForm VOA.Moonshine.TFormLeech

/-- The minus roots become diagonal cocode operators in the spin representation. -/
theorem sigmaBOddRoot_coord {i j : Fin 24} (hij : i < j) :
    coordOfRed (red leech (gM (piPerm.symm i) (piPerm.symm j))) =
      (0, deltaPair i j) := by
  apply phi0_injective
  rw [phi0_coordOfRed_red, ← coordOf_rMinus, phi0_coordOf_rMinus hij]
  have hv : (leechEquiv (gM (piPerm.symm i) (piPerm.symm j)) : Fin 24 → ℤ) =
      vMinus i j := by
    ext k
    rw [leechEquiv_apply]
    change lv (gM (piPerm.symm i) (piPerm.symm j)) (piPerm.symm k) = _
    simp only [lv_gM_apply, vMinus, Code.eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Equiv.apply_eq_iff_eq]
    ring
  rw [classOf_eq_cls (vMinus_mem hij).1]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hv)

/-- The minus-root matrix is diagonal, with the two-coordinate code character. -/
theorem sigmaBOddRoot_matrix (i j : Fin 24) :
    qmatR ℂ 0 0 (deltaPair i j) = Matrix.diagonal
      (fun a : SpinIdx => sgnR ℂ (a.2.1.1 i + a.2.1.1 j)) := by
  ext a b
  simp only [qmatR_apply, qPerm, qSign, shift_zero, map_zero, mul_zero,
    zero_add, deltaPair, pair_mk, dotProduct_add, dotProduct_single, mul_one,
    coe_ΩC, Code.Ω, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
  rw [Prod.mk.eta, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst b
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Nonzero coordinates of a seed have the same minus-root characters. -/
theorem sigmaBOddRoot_character {v : SpinRep} (hv : IsSeed (spinIso v))
    {a b : SpinIdx} (ha : v a ≠ 0) (hb : v b ≠ 0)
    {i j : Fin 24} (hij : i < j) :
    a.2.1.1 i + a.2.1.1 j = b.2.1.1 i + b.2.1.1 j := by
  have he : (spinOp (coordOfRed
      (red leech (gM (piPerm.symm i) (piPerm.symm j)))) *ᵥ v : SpinRep) =
      (2 * kM (piPerm.symm i) (piPerm.symm j))⁻¹ • v := by
    apply spinIso.injective
    erw [spinIso_spinOp, spinIso_smul]
    exact eL_gM_seed hv (fun h => hij.ne (piPerm.symm.injective h))
  rw [sigmaBOddRoot_coord hij, spinOp, sigmaBOddRoot_matrix] at he
  have hc (k : SpinIdx) (hk : v k ≠ 0) :
      signRefinement (0, deltaPair i j) * sgnR ℂ (k.2.1.1 i + k.2.1.1 j) =
        (2 * kM (piPerm.symm i) (piPerm.symm j))⁻¹ := by
    apply mul_right_cancel₀ hk
    have h := congrFun he k
    simpa only [Matrix.smul_mulVec, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc] using h
  apply sgnR_injective (by norm_num : (2 : ℂ) ≠ 0)
  have hz : signRefinement (0, deltaPair i j) ≠ 0 := by
    intro hz
    have hs := signRefinement_add (0, deltaPair i j) (0, deltaPair i j)
    have hp : (0, deltaPair i j) + (0, deltaPair i j) = (0 : Code.C × Cocode) := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [hp, signRefinement_zero, hz, zero_mul, zero_mul] at hs
    exact one_ne_zero hs
  exact mul_left_cancel₀ hz ((hc a ha).trans (hc b hb).symm)

/-- The root characters separate the code component of the spin index. -/
theorem sigmaBOddRoot_separates {v : SpinRep} (hv : IsSeed (spinIso v))
    {a b : SpinIdx} (ha : v a ≠ 0) (hb : v b ≠ 0) : a.2 = b.2 := by
  have hd : (a.2 : Code.C) + (b.2 : Code.C) =
      (a.2.1.1 0 + b.2.1.1 0) • ΩC := by
    apply Subtype.ext
    funext k
    change a.2.1.1 k + b.2.1.1 k = (a.2.1.1 0 + b.2.1.1 0) * 1
    by_cases hk : k = 0
    · subst k
      rw [mul_one]
    · have h := sigmaBOddRoot_character hv ha hb (i := 0) (j := k) (by omega)
      have h2 : (2 : ZMod 2) = 0 := rfl
      linear_combination h + (b.2.1.1 k - a.2.1.1 0) * h2
  have hz := congrArg μ₀ hd
  simp only [map_add, μ₀_coe, map_smul, μ₀_ΩC, smul_eq_mul, mul_one, add_zero] at hz
  rw [← hz, zero_smul] at hd
  apply Subtype.ext
  have hb0 : (b.2 : Code.C) + (b.2 : Code.C) = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  exact add_right_cancel (hd.trans hb0.symm)

/-- A fixed frame sector separates the remaining binary spin index. -/
theorem sigmaBOddFrame_separates {v : SpinRep} {s : ZMod 2}
    (hv : spinIso v ∈ leechFrameT s) {a b : SpinIdx}
    (ha : v a ≠ 0) (hb : v b ≠ 0) : a.1 = b.1 := by
  have he := (FrameT.mem_frameT leech leech_even leech_isUnit_det_gramMat).1 hv
  change frameJL (spinIso v) = Extraspecial.sgn s • spinIso v at he
  rw [spinIso_frameJ] at he
  have he' : (frameSign • (frameDiag *ᵥ v) : SpinRep) = Extraspecial.sgn s • v := by
    apply spinIso.injective
    erw [spinIso_smul, spinIso_smul]
    exact he
  have hc (k : SpinIdx) (hk : v k ≠ 0) :
      frameSign * sgnR ℂ k.1 = Extraspecial.sgn s := by
    apply mul_right_cancel₀ hk
    have h := congrFun he' k
    simpa only [frameDiag, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc] using h
  apply sgnR_injective (by norm_num : (2 : ℂ) ≠ 0)
  have hz : frameSign ≠ 0 := by
    intro h
    have heq := frameSign_mul_self
    rw [h, zero_mul] at heq
    exact zero_ne_one heq
  exact mul_left_cancel₀ hz ((hc a ha).trans (hc b hb).symm)

/-- The chosen short representative of an odd class lies outside the even sublattice. -/
theorem sigmaBOdd_not_mem (c : ShortIdx) (hc : sigmaBlockParity c = 1) :
    shortVec c ∉ lambda0 := by
  rw [mem_lambda0, sigmaBlockParity_eq, hc]
  exact one_ne_zero

/-- The top-map formula holds for either representative of an odd norm-four pair. -/
theorem sigmaBOddPhi_hP {β : leech.carrier} (hβ : β ∉ lambda0)
    (h4 : leech.form β β = 4) :
    Dnat.Φ (frameX0P β) = (cStar0 * cStar β) • hP (cw (blk β)) (eL β t0) := by
  change (cStar0 • Φ0) (frameX0P β) = _
  rw [LinearMap.smul_apply]
  have htop : frameX0P β ∈ OmegaV3 :=
    ⟨frameX0_mem_frameSector_one hβ, frameX0P_mem_grading_two h4⟩
  rw [Φ0_top _ htop, phiV, phiV3_frameX0P_any (tauStar_neg t0) hβ h4,
    tauStar, cE_eq hβ, hP_smul_right, smul_smul]

/-- The rational part of the odd top-map phase. -/
def sigmaBOddPhase (β : leech.carrier) : ℚ :=
  (-1 : ℚ) ^ ((lv β 0 - 1) / 2) * (lv β (blk β) : ℚ) / 3

/-- On odd charges the entire nonrational part of `cStar` is the common factor `I`. -/
theorem sigmaBOddPhase_spec {β : leech.carrier} (hβ : β ∉ lambda0) :
    cStar β = (sigmaBOddPhase β : ℂ) * Complex.I := by
  obtain ⟨k, hk⟩ := lv_odd_of_not_mem hβ 0
  have hexp : (lv β 0 - 1) / 2 = k := by omega
  rw [cStar, sgnBlk, sigmaBOddPhase, hexp, hk]
  rw [zpow_add₀ Complex.I_ne_zero, _root_.zpow_mul, zpow_one]
  norm_num only [zpow_ofNat, Complex.I_sq]
  push_cast
  ring

theorem sigmaBOddPhase_sq {β : leech.carrier} (hβ : β ∉ lambda0)
    (h4 : leech.form β β = 4) : sigmaBOddPhase β ^ 2 = 1 := by
  have hpow : ((-1 : ℚ) ^ ((lv β 0 - 1) / 2)) ^ 2 = 1 := by
    rw [neg_one_zpow_eq_ite]
    split_ifs <;> norm_num
  have h := lv_sq hβ h4 (blk β)
  rw [if_pos rfl] at h
  have hq : (lv β (blk β) : ℚ) ^ 2 = 9 := by exact_mod_cast h
  rw [sigmaBOddPhase, div_pow, mul_pow, hpow, one_mul, hq]
  norm_num

/-- A single normalized seed contains all remaining complex spin coordinates. -/
def sigmaBOddSeed : SpinRep :=
  (cStar0 * Complex.I / spinDictScale) • spinIso.symm t0

/-- The seed normalization uses exactly the scale of the rational dictionary. -/
theorem sigmaBOddSeed_spec :
    spinDictScale • spinIso sigmaBOddSeed = (cStar0 * Complex.I) • t0 := by
  rw [sigmaBOddSeed, spinIso_smul, spinIso.apply_symm_apply, smul_smul]
  congr 1
  field_simp [spinDictScale_ne_zero]

/-- The normalized seed retains the root eigenconditions. -/
theorem sigmaBOddSeed_isSeed : IsSeed (spinIso sigmaBOddSeed) := by
  rw [sigmaBOddSeed, spinIso_smul, spinIso.apply_symm_apply]
  intro j k hjk
  obtain ⟨h1, h2⟩ := t0_seed j k hjk
  constructor
  · rw [map_smul, h1, smul_comm]
  · rw [map_smul, h2, smul_comm]

theorem sigmaBOddSeed_frame : spinIso sigmaBOddSeed ∈ leechFrameT s0 := by
  rw [sigmaBOddSeed, spinIso_smul, spinIso.apply_symm_apply]
  exact Submodule.smul_mem _ _ t0_mem

/-- The seed is supported at a single spin index. -/
theorem sigmaBOddSeed_support {a b : SpinIdx}
    (ha : sigmaBOddSeed a ≠ 0) (hb : sigmaBOddSeed b ≠ 0) : a = b :=
  Prod.ext (sigmaBOddFrame_separates sigmaBOddSeed_frame ha hb)
    (sigmaBOddRoot_separates sigmaBOddSeed_isSeed ha hb)

/-- The full short phase cancels the phase of the extraspecial spin action. -/
theorem sigmaBOddSpin_action (c : ShortIdx) (v : SpinRep) :
    fullShortSign c • eL (shortVec c) (spinIso v) =
      spinIso (((Rmat c).map (Rat.castHom ℂ)) *ᵥ v) := by
  rw [← spinIso_spinOp, ← spinIso_smul]
  congr 1
  change fullShortSign c • ((spinOp (coordOfRed (red leech (shortVec c)))) *ᵥ v) = _
  rw [← Matrix.smul_mulVec, fullShortSign_smul_spinOp]

/-- Exact phased odd-column formula, with all charge coordinates in the spin model. -/
theorem sigmaBOddColumn_hP (c : ShortIdx) (hc : sigmaBlockParity c = 1) :
    fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) =
      spinDictScale • hP (cw (blk (shortVec c)))
        (spinIso ((sigmaBOddPhase (shortVec c) : ℂ) •
          (((Rmat c).map (Rat.castHom ℂ)) *ᵥ sigmaBOddSeed))) := by
  rw [sigmaBOddPhi_hP (sigmaBOdd_not_mem c hc) (shortVec_norm c),
    sigmaBOddPhase_spec (sigmaBOdd_not_mem c hc)]
  erw [spinIso_smul]
  rw [← sigmaBOddSpin_action, hP_smul_right, hP_smul_right]
  rw [sigmaBOddSeed, spinIso_smul, spinIso.apply_symm_apply,
    map_smul, hP_smul_right]
  simp only [smul_smul]
  congr 1
  field_simp [spinDictScale_ne_zero]

/-- The rational spin matrices preserve the complex bilinear dot product. -/
theorem sigmaBOddRmat_form (c : ShortIdx) (v : SpinRep) :
    (((Rmat c).map (Rat.castHom ℂ)) *ᵥ v) ⬝ᵥ
      (((Rmat c).map (Rat.castHom ℂ)) *ᵥ v) = v ⬝ᵥ v := by
  rw [Rmat_map]
  rw [← dotProduct_transpose_mulVec, mulVec_mulVec,
    qmatR_transpose_mul_self, Matrix.one_mulVec]

/-- The form normalization converts an oscillator column to twice its dot square. -/
theorem sigmaBOddColumn_form (b : Fin 24) (v : SpinRep) :
    TPForm (spinDictScale • hP (cw b) (spinIso v))
      (spinDictScale • hP (cw b) (spinIso v)) = 2 * (v ⬝ᵥ v) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [TPForm_hP_cw, if_pos rfl, TForm_spinIso]
  calc
    _ = (-4 * spinFormScale * spinDictScale ^ 2) * (v ⬝ᵥ v) := by ring
    _ = 2 * (v ⬝ᵥ v) := by
      rw [spinDictScale_sq]
      field_simp [spinFormScale_ne_zero]
      ring

/-- The full short phase and the isometry of triality give square norm two. -/
theorem sigmaBOddPhi_form (c : ShortIdx) (hc : sigmaBlockParity c = 1) :
    TPForm (fullShortSign c • Dnat.Φ (frameX0P (shortVec c)))
      (fullShortSign c • Dnat.Φ (frameX0P (shortVec c))) = 2 := by
  have hmem := (sigmaBlockShort_mem_iff c 1).2 hc
  have hiso := phiIso_mkData cStar0_norm (show (1 : ℂ) * 1 = 1 by norm_num)
  have hf := hiso _ hmem _ hmem
  change TPForm (Dnat.Φ (frameX0P (shortVec c)))
    (Dnat.Φ (frameX0P (shortVec c))) = _ at hf
  rw [leechBV_eq_plusForm, plusForm_frameX0P_frameX0P (shortVec_norm c),
    if_pos (Or.inl rfl)] at hf
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hf]
  have hs := shortSignDictionary_fullShortSign.sq c
  linear_combination 2 * hs

/-- The unique nonzero coordinate of the normalized seed has square one. -/
theorem sigmaBOddSeed_form : sigmaBOddSeed ⬝ᵥ sigmaBOddSeed = 1 := by
  obtain ⟨c, hc⟩ := sigmaBOddIndex_exists
  have hf := sigmaBOddPhi_form c hc
  rw [sigmaBOddColumn_hP c hc, sigmaBOddColumn_form,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    sigmaBOddRmat_form] at hf
  have hp : (sigmaBOddPhase (shortVec c) : ℂ) ^ 2 = 1 := by
    exact_mod_cast sigmaBOddPhase_sq (sigmaBOdd_not_mem c hc) (shortVec_norm c)
  linear_combination hf / 2 - (sigmaBOddSeed ⬝ᵥ sigmaBOddSeed) * hp

theorem sigmaBOddSeed_coord_sq (j : SpinIdx) (hj : sigmaBOddSeed j ≠ 0) :
    sigmaBOddSeed j ^ 2 = 1 := by
  rw [← sigmaBOddSeed_form, dotProduct,
    Finset.sum_eq_single j, pow_two]
  · intro k _ hkj
    have hk : sigmaBOddSeed k = 0 := by
      by_contra hk
      exact hkj (sigmaBOddSeed_support hk hj)
    rw [hk, zero_mul]
  · exact fun h => (h (Finset.mem_univ j)).elim

/-- Rational coordinates of the normalized seed; every entry is zero or a sign. -/
def sigmaBOddSeedQ (j : SpinIdx) : ℚ :=
  if sigmaBOddSeed j = 0 then 0 else sigmaBlockRSign (sigmaBOddSeed j)

theorem sigmaBOddSeedQ_cast (j : SpinIdx) :
    (sigmaBOddSeedQ j : ℂ) = sigmaBOddSeed j := by
  unfold sigmaBOddSeedQ
  split_ifs with hj
  · simpa only [Rat.cast_zero] using hj.symm
  · exact sigmaBlockRSign_cast _ (sigmaBOddSeed_coord_sq j hj)

/-- A single oscillator column, before restricting the spin coordinates to rationals. -/
def sigmaBOddEmbed (b : Fin 24) (v : SpinRep) : Matrix SpinIdx (Fin 24) ℂ :=
  fun j i => if i = b then v j else 0

theorem sigmaBOddEmbed_hP (b : Fin 24) (v : SpinRep) :
    spinTopVec (sigmaBOddEmbed b v) = hP (cw b) (spinIso v) := by
  classical
  rw [spinTopVec_apply, Finset.sum_eq_single b]
  · simp only [sigmaBOddEmbed, if_true, spinTopState_apply]
    rw [conwayVec, sigmaBlockAxis_eq]
    rfl
  · intro i _ hi
    have hz : (fun j => sigmaBOddEmbed b v j i) = 0 := by
      ext j
      simp only [sigmaBOddEmbed, if_neg hi, Pi.zero_apply]
    rw [hz, map_zero]
  · exact fun h => (h (Finset.mem_univ b)).elim

/-- Explicit rational coordinates of the column, assuming rational seed coordinates. -/
def sigmaBOddColumn (v : SpinIdx → ℚ) (c : ShortIdx) : SpaceW :=
  fun j i => if i = piPerm (blk (shortVec c)) then
    sigmaBOddPhase (shortVec c) * (Rmat c *ᵥ v) j else 0

theorem sigmaBOddColumn_conway (v : SpinIdx → ℚ) (c : ShortIdx) :
    spinToConway (sigmaBOddColumn v c) =
      sigmaBOddEmbed (blk (shortVec c))
        ((sigmaBOddPhase (shortVec c) : ℂ) •
          (((Rmat c).map (Rat.castHom ℂ)) *ᵥ (fun j => (v j : ℂ)))) := by
  ext j i
  simp only [spinToConway_apply, sigmaBOddColumn, sigmaBOddEmbed,
    Equiv.apply_eq_iff_eq, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Rat.coe_castHom, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> rfl

/-- All odd-column identities follow from the rationality of one normalized seed. -/
theorem sigmaBOddColumn_nat (v : SpinIdx → ℚ)
    (hv : ∀ j, sigmaBOddSeed j = (v j : ℂ))
    (c : ShortIdx) (hc : sigmaBlockParity c = 1) :
    fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) = spinDict (sigmaBOddColumn v c) := by
  rw [sigmaBOddColumn_hP c hc, spinDict_apply, sigmaBOddColumn_conway,
    sigmaBOddEmbed_hP]
  have he : sigmaBOddSeed = (fun j => (v j : ℂ) : SpinRep) := funext hv
  rw [he]

theorem sigmaBOdd_rational_of_seed (v : SpinIdx → ℚ)
    (hv : ∀ j, sigmaBOddSeed j = (v j : ℂ)) :
    ∀ u : SpaceB, ∃ w : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat w :=
  sigmaB_rational_iff_odd_columns.2 fun c hc => ⟨_, sigmaBOddColumn_nat v hv c hc⟩

theorem sigmaBOdd_liftable_of_seed (v : SpinIdx → ℚ)
    (hv : ∀ j, sigmaBOddSeed j = (v j : ℂ)) :
    ∃ g : liftableSubgroup, monsterLift g = sigmaAut :=
  sigmaB_liftable_of_odd_columns fun c hc => ⟨_, sigmaBOddColumn_nat v hv c hc⟩

/-- Every odd short class has the displayed rational spin-dictionary column. -/
theorem sigmaBOdd_columns (c : ShortIdx) (hc : sigmaBlockParity c = 1) :
    fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) =
      spinDict (sigmaBOddColumn sigmaBOddSeedQ c) :=
  sigmaBOddColumn_nat sigmaBOddSeedQ (fun j => (sigmaBOddSeedQ_cast j).symm) c hc

/-- Triality preserves the rational Griess dictionary on all of weight two. -/
theorem sigmaBOdd_rational :
    ∀ u : SpaceB, ∃ v : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat v :=
  sigmaBOdd_rational_of_seed sigmaBOddSeedQ (fun j => (sigmaBOddSeedQ_cast j).symm)

/-- The triality automorphism is unconditionally in the image of the Monster lift. -/
theorem sigmaBOdd_liftable : ∃ g : liftableSubgroup, monsterLift g = sigmaAut :=
  sigmaBOdd_liftable_of_seed sigmaBOddSeedQ (fun j => (sigmaBOddSeedQ_cast j).symm)

end VOA.Moonshine.ConwayNorton.M8
