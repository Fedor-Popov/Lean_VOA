import VOA.Moonshine.MoonshineLRSigmaBlock
import VOA.Moonshine.MoonshineLRLiftSign
import VOA.Moonshine.SigmaTop2Root

/-!
# Rational two-root coefficients of triality

The fixed short phases make the two-root transport ratios rational signs.
All indices below are in `ShortIdx`, including the Golay coordinate permutation.

`sigmaBlockRNat_matrix` gives the complete rational image of the oscillator summand.
`sigmaBlockRNat_P` and `sigmaBlockRNat_M` give the two-root short columns. With
`H = sigmaBlockRH j k`, `P` and `M` the corresponding unit short coordinates, and
rational signs `p = sigmaBlockRPWeight hjk`, `m = sigmaBlockRMWeight hjk`, these are
`H ↦ (p P + m M)/2`, `P ↦ p H + P/2 - p m M/2`,
`M ↦ m H - p m P/2 + M/2`. Diagonal oscillator columns are fixed.

The signs are defined relative to the fixed, noncomputable `griessShortSign`;
no numerical sign table is asserted. The octad `KS` coefficients are not treated,
so this file does not yet define triality on every even short coordinate.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.SigmaTop VOA.Moonshine.SigmaExist VOA.Moonshine.TrialityTw
open VOA.Moonshine.M8hKey VOA.Moonshine.SigmaAssemble VOA.Moonshine.VnatBlock
open VOA.LatGen VOA.IntegralLattice Matrix

/-- The unique short pair of a norm-four vector. -/
def sigmaBlockRIndex (a : leech.carrier) (ha : leech.form a a = 4) : ShortIdx :=
  (liftSignShort_exists a ha).choose

theorem sigmaBlockRIndex_spec (a : leech.carrier) (ha : leech.form a a = 4) :
    a = shortVec (sigmaBlockRIndex a ha) ∨ a = -shortVec (sigmaBlockRIndex a ha) :=
  (liftSignShort_exists a ha).choose_spec

theorem sigmaBlockRIndex_frame (a : leech.carrier) (ha : leech.form a a = 4) :
    frameX0P a = frameX0P (shortVec (sigmaBlockRIndex a ha)) := by
  rcases sigmaBlockRIndex_spec a ha with h | h
  · exact congrArg frameX0P h
  · exact (congrArg frameX0P h).trans (frameX0P_neg_eq _)

theorem sigmaBlockRIndex_cocycle (a : leech.carrier) (ha : leech.form a a = 4) :
    latticeCocycle leech a a = latticeCocycle leech
      (shortVec (sigmaBlockRIndex a ha)) (shortVec (sigmaBlockRIndex a ha)) := by
  rcases sigmaBlockRIndex_spec a ha with h | h
  · exact congrArg (fun b => latticeCocycle leech b b) h
  · exact (congrArg (fun b => latticeCocycle leech b b) h).trans
      (liftSignCocycle_neg _)

/-- Extract a rational sign from a complex number whose square is one. -/
def sigmaBlockRSign (z : ℂ) : ℚ := if z = 1 then 1 else -1

theorem sigmaBlockRSign_cast (z : ℂ) (hz : z ^ 2 = 1) :
    (sigmaBlockRSign z : ℂ) = z := by
  rcases sq_eq_one_iff.mp hz with h | h
  · simp [sigmaBlockRSign, h]
  · norm_num [sigmaBlockRSign, h]

theorem sigmaBlockRSign_values (z : ℂ) :
    sigmaBlockRSign z = 1 ∨ sigmaBlockRSign z = -1 := by
  unfold sigmaBlockRSign
  split_ifs <;> simp

/-- Equal cocycle-normalized squares imply a rational phase ratio. -/
theorem sigmaBlockRRatio_sq (a : leech.carrier) (ha : leech.form a a = 4)
    (z : ℂ) (hz : z ^ 2 * latticeCocycle leech a a = 1) :
    (z / griessShortSign (sigmaBlockRIndex a ha)) ^ 2 = 1 := by
  have hs := griessShortSign_sq (sigmaBlockRIndex a ha)
  rw [sigmaBlockRIndex_cocycle a ha] at hz
  have he : z ^ 2 = griessShortSign (sigmaBlockRIndex a ha) ^ 2 :=
    mul_right_cancel₀ (latticeCocycle_ne_zero leech _ _) (hz.trans hs.symm)
  rw [div_pow, he, div_self (pow_ne_zero 2 (liftSignPhase_ne_zero _))]

def sigmaBlockRP {j k : Fin 24} (hjk : j ≠ k) : ShortIdx :=
  sigmaBlockRIndex (gP j k) (form_gP_self hjk)

def sigmaBlockRM {j k : Fin 24} (hjk : j ≠ k) : ShortIdx :=
  sigmaBlockRIndex (gM j k) (form_gM_self hjk)

/-- The plus transport weight relative to the fixed dictionary phase. -/
def sigmaBlockRPWeight {j k : Fin 24} (hjk : j ≠ k) : ℚ :=
  sigmaBlockRSign (2 * kP j k / griessShortSign (sigmaBlockRP hjk))

/-- The minus transport weight relative to the fixed dictionary phase. -/
def sigmaBlockRMWeight {j k : Fin 24} (hjk : j ≠ k) : ℚ :=
  sigmaBlockRSign (2 * kM j k / griessShortSign (sigmaBlockRM hjk))

theorem sigmaBlockRPWeight_cast {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRPWeight hjk : ℂ) =
      2 * kP j k / griessShortSign (sigmaBlockRP hjk) := by
  apply sigmaBlockRSign_cast
  apply sigmaBlockRRatio_sq
  have h := kP_sq hjk
  change kP j k * kP j k * latticeCocycle leech (gP j k) (gP j k) = 1 / 4 at h
  linear_combination 4 * h

theorem sigmaBlockRMWeight_cast {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRMWeight hjk : ℂ) =
      2 * kM j k / griessShortSign (sigmaBlockRM hjk) := by
  apply sigmaBlockRSign_cast
  apply sigmaBlockRRatio_sq
  have h := kM_sq hjk
  change kM j k * kM j k * latticeCocycle leech (gM j k) (gM j k) = 1 / 4 at h
  linear_combination 4 * h

theorem sigmaBlockRPWeight_phase {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRPWeight hjk : ℂ) * griessShortSign (sigmaBlockRP hjk) = 2 * kP j k := by
  rw [sigmaBlockRPWeight_cast, div_mul_cancel₀ _ (liftSignPhase_ne_zero _)]

theorem sigmaBlockRMWeight_phase {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRMWeight hjk : ℂ) * griessShortSign (sigmaBlockRM hjk) = 2 * kM j k := by
  rw [sigmaBlockRMWeight_cast, div_mul_cancel₀ _ (liftSignPhase_ne_zero _)]

/-- The original plus transport coefficient is the dictionary phase times a rational sign. -/
theorem sigmaBlockRTransportP {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRPWeight hjk : ℂ) * griessShortSign (sigmaBlockRP hjk) =
      cQ j k 0 * tc (aQ j k 0) := by
  rw [sigmaBlockRPWeight_phase, kP_eq_dQ j k hjk]

/-- The original minus transport coefficient has the same rational normalization. -/
theorem sigmaBlockRTransportM {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRMWeight hjk : ℂ) * griessShortSign (sigmaBlockRM hjk) =
      cQ j k 1 * tc (aQ j k 1) := by
  rw [sigmaBlockRMWeight_phase, kM_eq_dQ j k hjk]

/-- Both transport weights are signs, not general rational numbers. -/
theorem sigmaBlockRWeight_values {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRPWeight hjk = 1 ∨ sigmaBlockRPWeight hjk = -1) ∧
      (sigmaBlockRMWeight hjk = 1 ∨ sigmaBlockRMWeight hjk = -1) :=
  ⟨sigmaBlockRSign_values _, sigmaBlockRSign_values _⟩

/-- One rational short coordinate. -/
def sigmaBlockRUnit (c : ShortIdx) : SpaceX := Pi.single c 1

theorem sigmaBlockRUnit_dict (c : ShortIdx) :
    shortDict griessShortSign (sigmaBlockRUnit c) =
      griessShortSign c • frameX0P (shortVec c) := by
  classical
  rw [shortDict_apply, Finset.sum_eq_single c]
  · simp [sigmaBlockRUnit]
  · intro b _ hbc
    simp [sigmaBlockRUnit, hbc]
  · simp

theorem sigmaBlockRP_even {j k : Fin 24} (hjk : j ≠ k) :
    sigmaBlockParity (sigmaBlockRP hjk) = 0 := by
  apply (sigmaBlockShort_mem_V0_iff _).mp
  unfold sigmaBlockRP
  rw [← sigmaBlockRIndex_frame]
  exact frameX0P_mem_V0 (gP_mem j k)

theorem sigmaBlockRM_even {j k : Fin 24} (hjk : j ≠ k) :
    sigmaBlockParity (sigmaBlockRM hjk) = 0 := by
  apply (sigmaBlockShort_mem_V0_iff _).mp
  unfold sigmaBlockRM
  rw [← sigmaBlockRIndex_frame]
  exact frameX0P_mem_V0 (gM_mem j k)

theorem sigmaBlockRShort_smul (q : ℚ) (x : SpaceX) :
    shortDict griessShortSign (q • x) = (q : ℂ) • shortDict griessShortSign x := by
  simp only [shortDict_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    Finset.smul_sum, smul_smul, mul_assoc]

/-- The two charged pairs in the image of a normalized off-diagonal oscillator. -/
def sigmaBlockROffX {j k : Fin 24} (hjk : j ≠ k) : SpaceX :=
  (sigmaBlockRPWeight hjk / 2) • sigmaBlockRUnit (sigmaBlockRP hjk) +
    (sigmaBlockRMWeight hjk / 2) • sigmaBlockRUnit (sigmaBlockRM hjk)

theorem sigmaBlockROffX_dict {j k : Fin 24} (hjk : j ≠ k) :
    shortDict griessShortSign (sigmaBlockROffX hjk) =
      kP j k • frameX0P (gP j k) + kM j k • frameX0P (gM j k) := by
  rw [sigmaBlockROffX, map_add, sigmaBlockRShort_smul, sigmaBlockRShort_smul,
    sigmaBlockRUnit_dict, sigmaBlockRUnit_dict, smul_smul, smul_smul]
  have hp : frameX0P (gP j k) = frameX0P (shortVec (sigmaBlockRP hjk)) :=
    sigmaBlockRIndex_frame _ _
  have hm : frameX0P (gM j k) = frameX0P (shortVec (sigmaBlockRM hjk)) :=
    sigmaBlockRIndex_frame _ _
  rw [← hp, ← hm]
  congr 1 <;> congr 1
  · push_cast
    linear_combination sigmaBlockRPWeight_phase hjk / 2
  · push_cast
    linear_combination sigmaBlockRMWeight_phase hjk / 2

/-- The raw four-charge formula grouped into its two short pairs. -/
theorem sigmaBlockROff_frame {j k : Fin 24} (hjk : j ≠ k) :
    (v0Sigma (dV (fw j) (fw k)) : VPlus) =
      (8 * kP j k) • frameX0P (gP j k) +
        (8 * kM j k) • frameX0P (gM j k) := by
  apply Subtype.ext
  change (((sig (dV (fw j) (fw k)) : V0Sub.carrier) : VPlus) :
    LatModuleGen leech) = _
  rw [sig_dV_offdiag_coe hjk, Fin.sum_univ_four]
  have hP := (dQ_symm hjk).1
  have hM := (dQ_symm hjk).2
  have h0 : 4 * cQ j k 0 * tc (aQ j k 0) = 8 * kP j k := by
    linear_combination -4 * kP_eq_dQ j k hjk
  have h1 : 4 * cQ j k 1 * tc (aQ j k 1) = 8 * kM j k := by
    linear_combination -4 * kM_eq_dQ j k hjk
  unfold dQ at hP hM
  rw [← hP, ← hM, h0, h1]
  have e0 : inclΛ (aQ j k 0) = gP j k := rfl
  have e1 : inclΛ (aQ j k 1) = gM j k := rfl
  have e2 : inclΛ (aQ j k 2) = -gM j k := by simp [aQ, gM]
  have e3 : inclΛ (aQ j k 3) = -gP j k := by simp [aQ, gP]
  rw [e0, e1, e2, e3]
  change _ = (8 * kP j k) • (latChargeGen leech (gP j k) +
    latChargeGen leech (-gP j k)) + (8 * kM j k) •
      (latChargeGen leech (gM j k) + latChargeGen leech (-gM j k))
  module

/-- A normalized off-diagonal oscillator maps to two rational half-sign coordinates. -/
theorem sigmaBlockRNat_offdiag {j k : Fin 24} (hjk : j ≠ k) :
    sigmaAut (((8 : ℂ)⁻¹ • (dV (fw j) (fw k) : VPlus), 0) : Vnat) =
      (untwistedDictNat griessShortSign (shortBlock (sigmaBlockROffX hjk)) : Vnat) := by
  change sigNat Dnat ((↑((8 : ℂ)⁻¹ • dV (fw j) (fw k)) : VPlus), 0) = _
  rw [sigNat_V0 Dnat ((8 : ℂ)⁻¹ • dV (fw j) (fw k)), map_smul]
  change ((((8 : ℂ)⁻¹ • (v0Sigma (dV (fw j) (fw k)) : VPlus)), 0) : Vnat) =
    (untwistedDict griessShortSign (shortBlock (sigmaBlockROffX hjk)), 0)
  rw [untwistedDict_shortBlock, sigmaBlockROff_frame hjk, sigmaBlockROffX_dict,
    smul_add, smul_smul, smul_smul]
  congr 2 <;> congr 1 <;> ring

/-- The symmetric matrix whose dictionary image is `dV(w_j,w_k)/8`. -/
def sigmaBlockRH (j k : Fin 24) : symMat :=
  ⟨(1 / 2 : ℚ) • (Matrix.single (piPerm j) (piPerm k) 1 +
      Matrix.single (piPerm k) (piPerm j) 1), by
    rw [mem_symMat, transpose_smul, transpose_add, transpose_single, transpose_single]
    rw [add_comm]⟩

theorem sigmaBlockRH_dict (j k : Fin 24) :
    matDict (sigmaBlockRH j k) = (8 : ℂ)⁻¹ • (dV (fw j) (fw k) : VPlus) := by
  have h : axiomToConway (sigmaBlockRH j k) =
      (1 / 2 : ℂ) • (Matrix.single j k 1 + Matrix.single k j 1) := by
    ext a b
    simp only [sigmaBlockRH, axiomToConway_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.single_apply, EmbeddingLike.apply_eq_iff_eq, smul_eq_mul]
    split_ifs <;> norm_num
  rw [matDict_apply, h, map_smul, map_add, ← transpose_single j k (1 : ℂ),
    conwayQuad_transpose, ← two_smul ℂ, smul_smul]
  norm_num
  rw [conwayQuad_eq_sum_dV]
  simp [Matrix.single_apply, ite_and, sigmaBlockAxis_eq]

/-- The off-diagonal formula entirely in the fixed rational dictionary. -/
theorem sigmaBlockRNat_H {j k : Fin 24} (hjk : j ≠ k) :
    sigmaAut (untwistedDictNat griessShortSign (symBlock (sigmaBlockRH j k)) : Vnat) =
      (untwistedDictNat griessShortSign (shortBlock (sigmaBlockROffX hjk)) : Vnat) := by
  change sigmaAut ((untwistedDict griessShortSign
    (symBlock (sigmaBlockRH j k)), 0) : Vnat) = _
  rw [untwistedDict_symBlock, sigmaBlockRH_dict]
  exact sigmaBlockRNat_offdiag hjk

/-- The plus short letter with the fixed dictionary phase, inside `V₀⁺`. -/
def sigmaBlockRPV {j k : Fin 24} (hjk : j ≠ k) : V0Sub.carrier :=
  griessShortSign (sigmaBlockRP hjk) • lV (gP j k) (gP_mem j k)

/-- The minus short letter with the fixed dictionary phase, inside `V₀⁺`. -/
def sigmaBlockRMV {j k : Fin 24} (hjk : j ≠ k) : V0Sub.carrier :=
  griessShortSign (sigmaBlockRM hjk) • lV (gM j k) (gM_mem j k)

theorem sigmaBlockRPV_dict {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRPV hjk : VPlus) =
      shortDict griessShortSign (sigmaBlockRUnit (sigmaBlockRP hjk)) := by
  rw [sigmaBlockRUnit_dict]
  change griessShortSign (sigmaBlockRP hjk) • frameX0P (gP j k) = _
  exact congrArg (fun v => griessShortSign (sigmaBlockRP hjk) • v)
    (sigmaBlockRIndex_frame _ _)

theorem sigmaBlockRMV_dict {j k : Fin 24} (hjk : j ≠ k) :
    (sigmaBlockRMV hjk : VPlus) =
      shortDict griessShortSign (sigmaBlockRUnit (sigmaBlockRM hjk)) := by
  rw [sigmaBlockRUnit_dict]
  change griessShortSign (sigmaBlockRM hjk) • frameX0P (gM j k) = _
  exact congrArg (fun v => griessShortSign (sigmaBlockRM hjk) • v)
    (sigmaBlockRIndex_frame _ _)

theorem sigmaBlockRPV_transport {j k : Fin 24} (hjk : j ≠ k) :
    golayToV0 (PPN j k) = (sigmaBlockRPWeight hjk : ℂ) • sigmaBlockRPV hjk := by
  rw [sigmaBlockRPV, smul_smul, sigmaBlockRPWeight_phase, golayToV0_PPN hjk]

theorem sigmaBlockRMV_transport {j k : Fin 24} (hjk : j ≠ k) :
    golayToV0 (MMN j k) = (sigmaBlockRMWeight hjk : ℂ) • sigmaBlockRMV hjk := by
  rw [sigmaBlockRMV, smul_smul, sigmaBlockRMWeight_phase, golayToV0_MMN hjk]

/-- Scalar algebra for a signed plus column, independent of the VOA implementation. -/
theorem sigmaBlockRSolveP {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p m : ℚ) (hp : p = 1 ∨ p = -1) (v h u w : W)
    (hv : (p : ℂ) • v = (1 / 8 : ℂ) • h +
      (1 / 2 : ℂ) • ((p : ℂ) • u) - (1 / 2 : ℂ) • ((m : ℂ) • w)) :
    v = (p : ℂ) • ((8 : ℂ)⁻¹ • h) + (1 / 2 : ℂ) • u -
      ((p * m / 2 : ℚ) : ℂ) • w := by
  rcases hp with rfl | rfl
  · norm_num at hv ⊢
    rw [hv]
    module
  · have hh := congrArg (fun a : W => (-1 : ℂ) • a) hv
    simp only [Rat.cast_neg, Rat.cast_one, neg_one_smul, neg_neg] at hh
    rw [hh]
    push_cast
    module

/-- Scalar algebra for the minus column. -/
theorem sigmaBlockRSolveM {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p m : ℚ) (hm : m = 1 ∨ m = -1) (v h u w : W)
    (hv : (m : ℂ) • v = (1 / 8 : ℂ) • h -
      (1 / 2 : ℂ) • ((p : ℂ) • u) + (1 / 2 : ℂ) • ((m : ℂ) • w)) :
    v = (m : ℂ) • ((8 : ℂ)⁻¹ • h) -
      ((p * m / 2 : ℚ) : ℂ) • u + (1 / 2 : ℂ) • w := by
  have hh := sigmaBlockRSolveP m p hm v h w u (by rw [hv]; module)
  rw [hh]
  push_cast
  module

/-- The plus column of the rational three-dimensional two-root block. -/
theorem sigmaBlockRPV_sigma {j k : Fin 24} (hjk : j ≠ k) :
    v0Sigma (sigmaBlockRPV hjk) =
      (sigmaBlockRPWeight hjk : ℂ) • ((8 : ℂ)⁻¹ • dV (fw j) (fw k)) +
        (1 / 2 : ℂ) • sigmaBlockRPV hjk -
          ((sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2 : ℚ) : ℂ) •
            sigmaBlockRMV hjk := by
  have h : sig (golayToV0 (PPN j k)) =
      (1 / 8 : ℂ) • dV (fw j) (fw k) +
        (1 / 2 : ℂ) • golayToV0 (PPN j k) -
          (1 / 2 : ℂ) • golayToV0 (MMN j k) := by
    rw [sig, ← golayToV0_sigma, golaySigma0_PPN hjk, map_sub, map_add,
      map_smul, map_smul, map_smul, golayToV0_HHo, smul_smul]
    norm_num
  rw [sigmaBlockRPV_transport hjk, sigmaBlockRMV_transport hjk, sig_smul] at h
  exact sigmaBlockRSolveP _ _ (sigmaBlockRWeight_values hjk).1 _ _ _ _ h

/-- The minus column of the rational three-dimensional two-root block. -/
theorem sigmaBlockRMV_sigma {j k : Fin 24} (hjk : j ≠ k) :
    v0Sigma (sigmaBlockRMV hjk) =
      (sigmaBlockRMWeight hjk : ℂ) • ((8 : ℂ)⁻¹ • dV (fw j) (fw k)) -
        ((sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2 : ℚ) : ℂ) •
          sigmaBlockRPV hjk + (1 / 2 : ℂ) • sigmaBlockRMV hjk := by
  have h : sig (golayToV0 (MMN j k)) =
      (1 / 8 : ℂ) • dV (fw j) (fw k) -
        (1 / 2 : ℂ) • golayToV0 (PPN j k) +
          (1 / 2 : ℂ) • golayToV0 (MMN j k) := by
    rw [sig, ← golayToV0_sigma, golaySigma0_MMN hjk, map_add, map_sub,
      map_smul, map_smul, map_smul, golayToV0_HHo, smul_smul]
    norm_num
  rw [sigmaBlockRPV_transport hjk, sigmaBlockRMV_transport hjk, sig_smul] at h
  exact sigmaBlockRSolveM _ _ (sigmaBlockRWeight_values hjk).2 _ _ _ _ h

/-- The fixed untwisted dictionary, explicitly as a rational linear map. -/
def sigmaBlockRDict : SpaceB →ₗ[ℚ] Vnat :=
  ((untwistedDict griessShortSign).prod 0).toRatLinearMap

theorem sigmaBlockRDict_apply (u : SpaceB) :
    sigmaBlockRDict u = (untwistedDictNat griessShortSign u : Vnat) := rfl

/-- Triality with scalars restricted to the rationals. -/
def sigmaBlockRAut : Vnat →ₗ[ℚ] Vnat := (sigNat Dnat).restrictScalars ℚ

theorem sigmaBlockRAut_apply (v : Vnat) : sigmaBlockRAut v = sigmaAut v := rfl

/-- The image column for each matrix letter, including the fixed diagonal. -/
def sigmaBlockRColumn (j k : Fin 24) : SpaceB :=
  if h : j = k then symBlock (sigmaBlockRH j k)
  else shortBlock (sigmaBlockROffX h)

theorem sigmaBlockRColumn_nat (j k : Fin 24) :
    sigmaBlockRAut (sigmaBlockRDict (symBlock (sigmaBlockRH j k))) =
      sigmaBlockRDict (sigmaBlockRColumn j k) := by
  rw [sigmaBlockRAut_apply, sigmaBlockRDict_apply, sigmaBlockRDict_apply]
  by_cases h : j = k
  · subst k
    rw [sigmaBlockRColumn, dif_pos rfl]
    apply sigmaBlockNat_diagonal
    intro a b hab
    change ((1 / 2 : ℚ) • (Matrix.single (piPerm j) (piPerm j) (1 : ℚ) +
      Matrix.single (piPerm j) (piPerm j) 1) : Matrix (Fin 24) (Fin 24) ℚ) a b = 0
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs with he
    · exact False.elim (hab (he.1.symm.trans he.2))
    · norm_num
  · rw [sigmaBlockRColumn, dif_neg h]
    exact sigmaBlockRNat_H h

/-- The finite rational column formula for an oscillator matrix. -/
def sigmaBlockRMatrixFun (A : symMat) : SpaceB :=
  ∑ j, ∑ k, (A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm j) (piPerm k) •
    sigmaBlockRColumn j k

/-- Explicit rational triality on the entire oscillator matrix summand. -/
def sigmaBlockRMatrix : symMat →ₗ[ℚ] SpaceB where
  toFun := sigmaBlockRMatrixFun
  map_add' A B := by
    simp only [sigmaBlockRMatrixFun, Submodule.coe_add, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' q A := by
    simp only [sigmaBlockRMatrixFun, Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem sigmaBlockRMatrix_apply (A : symMat) :
    sigmaBlockRMatrix A = sigmaBlockRMatrixFun A := rfl

theorem sigmaBlockRMatrix_decompose (A : symMat) :
    sigmaBlockRDict (symBlock A) = ∑ j, ∑ k,
      (A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm j) (piPerm k) •
        sigmaBlockRDict (symBlock (sigmaBlockRH j k)) := by
  have hm : matDict A = ∑ j, ∑ k,
      ((A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm j) (piPerm k) : ℂ) •
        matDict (sigmaBlockRH j k) := by
    conv_lhs => rw [matDict_apply, conwayQuad_eq_sum_dV]
    simp only [axiomToConway_apply, sigmaBlockAxis_eq, sigmaBlockRH_dict,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    module
  apply Prod.ext
  · change matDict A + shortDict griessShortSign 0 = _
    simp only [map_zero, add_zero, Prod.fst_sum, Prod.smul_fst]
    change matDict A = ∑ j, ∑ k,
      (A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm j) (piPerm k) •
        (matDict (sigmaBlockRH j k) + shortDict griessShortSign 0)
    simp only [map_zero, add_zero, ← Rat.cast_smul_eq_qsmul ℂ]
    exact hm
  · simp only [Prod.snd_sum, Prod.smul_snd]
    change (0 : TP) = ∑ j, ∑ k,
      (A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm j) (piPerm k) • (0 : TP)
    simp

/-- Every symmetric rational matrix has an explicit rational image under triality. -/
theorem sigmaBlockRNat_matrix (A : symMat) :
    sigmaAut (untwistedDictNat griessShortSign (symBlock A) : Vnat) =
      (untwistedDictNat griessShortSign (sigmaBlockRMatrix A) : Vnat) := by
  simp only [← sigmaBlockRDict_apply, ← sigmaBlockRAut_apply]
  rw [sigmaBlockRMatrix_apply, sigmaBlockRMatrixFun, sigmaBlockRMatrix_decompose]
  simp only [map_sum, map_smul, sigmaBlockRColumn_nat]

/-- The plus short column, in rational matrix and short coordinates. -/
def sigmaBlockRPImage {j k : Fin 24} (hjk : j ≠ k) : SpaceB :=
  (sigmaBlockRPWeight hjk • sigmaBlockRH j k,
    (1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRP hjk) -
      (sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2) •
        sigmaBlockRUnit (sigmaBlockRM hjk), 0)

/-- The minus short column, in rational matrix and short coordinates. -/
def sigmaBlockRMImage {j k : Fin 24} (hjk : j ≠ k) : SpaceB :=
  (sigmaBlockRMWeight hjk • sigmaBlockRH j k,
    -(sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2) •
      sigmaBlockRUnit (sigmaBlockRP hjk) +
        (1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRM hjk), 0)

/-- Triality on a plus two-root short coordinate, entirely in the rational dictionary. -/
theorem sigmaBlockRNat_P {j k : Fin 24} (hjk : j ≠ k) :
    sigmaAut (untwistedDictNat griessShortSign
      (shortBlock (sigmaBlockRUnit (sigmaBlockRP hjk))) : Vnat) =
        (untwistedDictNat griessShortSign (sigmaBlockRPImage hjk) : Vnat) := by
  change sigNat Dnat (untwistedDict griessShortSign
    (shortBlock (sigmaBlockRUnit (sigmaBlockRP hjk))), 0) = _
  rw [untwistedDict_shortBlock, ← sigmaBlockRPV_dict, sigNat_V0]
  apply Prod.ext
  · change (v0Sigma (sigmaBlockRPV hjk) : VPlus) =
      matDict (sigmaBlockRPWeight hjk • (sigmaBlockRH j k :
        Matrix (Fin 24) (Fin 24) ℚ)) + shortDict griessShortSign
          ((1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRP hjk) -
            (sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2) •
              sigmaBlockRUnit (sigmaBlockRM hjk))
    rw [sigmaBlockRPV_sigma, matDict_smul, sigmaBlockRH_dict, map_sub,
      sigmaBlockRShort_smul, sigmaBlockRShort_smul,
      ← sigmaBlockRPV_dict, ← sigmaBlockRMV_dict]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    abel
  · rfl

/-- Triality on a minus two-root short coordinate, entirely in the rational dictionary. -/
theorem sigmaBlockRNat_M {j k : Fin 24} (hjk : j ≠ k) :
    sigmaAut (untwistedDictNat griessShortSign
      (shortBlock (sigmaBlockRUnit (sigmaBlockRM hjk))) : Vnat) =
        (untwistedDictNat griessShortSign (sigmaBlockRMImage hjk) : Vnat) := by
  change sigNat Dnat (untwistedDict griessShortSign
    (shortBlock (sigmaBlockRUnit (sigmaBlockRM hjk))), 0) = _
  rw [untwistedDict_shortBlock, ← sigmaBlockRMV_dict, sigNat_V0]
  apply Prod.ext
  · change (v0Sigma (sigmaBlockRMV hjk) : VPlus) =
      matDict (sigmaBlockRMWeight hjk • (sigmaBlockRH j k :
        Matrix (Fin 24) (Fin 24) ℚ)) + shortDict griessShortSign
          (-(sigmaBlockRPWeight hjk * sigmaBlockRMWeight hjk / 2) •
            sigmaBlockRUnit (sigmaBlockRP hjk) +
              (1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRM hjk))
    rw [sigmaBlockRMV_sigma, matDict_smul, sigmaBlockRH_dict, map_add,
      sigmaBlockRShort_smul, sigmaBlockRShort_smul,
      ← sigmaBlockRPV_dict, ← sigmaBlockRMV_dict]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_smul]
    abel
  · rfl

end VOA.Moonshine.ConwayNorton.M8
