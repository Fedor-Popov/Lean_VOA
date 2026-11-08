import VOA.Moonshine.MoonshineLRSigmaBlock2
import VOA.Moonshine.SigmaTop2Class

/-!
# Octad coefficients of triality in the fixed short dictionary

The octad transport phases have a common normalized square. Their ratios in the
fixed short dictionary are rational signs, giving rational Hadamard columns.
`sigmaBlockONat` gives each octad column as a sum over the even-subset cube,
with coefficients `sigmaBlockOWeight / 16`. The sum retains both representatives
of each unoriented pair. `sigmaBlockOOctad_exists` covers every even short class
outside the two-root families.

`sigmaBlockOFull_nat` assembles all columns with the oscillator matrix formula.
`sigmaBlockOFullEven` restricts this rational linear map to matrices and
even-supported short coordinates. All signs are relative to the fixed,
noncomputable `griessShortSign`; no numerical sign table is selected.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.SigmaTop VOA.Moonshine.SigmaExist VOA.Moonshine.TrialityTw
open VOA.Moonshine.M8hKey VOA.Moonshine.SigmaAssemble VOA.Moonshine.VnatBlock
open VOA.LatGen VOA.IntegralLattice VOA.Moonshine.Triality Matrix

/-- Every cube normalization is a sign. -/
theorem sigmaBlockONu_sq (β : golayN.carrier) (S : Finset (Fin 24)) :
    nuC β S ^ 2 = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [nuC_empty]
  | @insert i S hi ih =>
    rw [nuC_insert β hi, mul_pow, mul_pow, ih, golayEps_sq,
      pow_two, εN_sq]
    norm_num

/-- The refinement on an even subset also has square one. -/
theorem sigmaBlockOXi_sq {S : Finset (Fin 24)} (he : Even S.card) :
    xi (ind S) ^ 2 = 1 := by
  have hn := sigmaBlockONu_sq (0 : golayN.carrier) S
  have hi : (Complex.I ^ S.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm S.card 2, pow_mul, Complex.I_sq, he.neg_one_pow]
  rw [nuC, mul_pow, mul_pow, pow_two (εN _ _), εN_sq, one_mul,
    inv_pow, hi, inv_one, mul_one] at hn
  exact hn

/-- Root-lattice shifts have normalized transport square one. -/
theorem sigmaBlockODelta_sq {S : Finset (Fin 24)} (he : Even S.card) :
    tc (dSA S) ^ 2 * εΛ (inclΛ (dSA S)) (inclΛ (dSA S)) = 1 := by
  obtain ⟨t, ht0, ht⟩ := seedExists
  have hv := mem_chargesS (mem_chargesS_dSA ht he) (inclN_dSA he)
  have h : (Wop (dSA S) * Wop (dSA S)) t = t := by
    rw [Module.End.mul_apply, hv, map_smul, hv, smul_smul, ← pow_two,
      sigmaBlockOXi_sq he, one_smul]
  have hw : Wop (dSA S) * Wop (dSA S) =
      (tc (dSA S) ^ 2 * εΛ (inclΛ (dSA S)) (inclΛ (dSA S))) • 1 := by
    rw [Wop, smul_mul_smul_comm, eL_mul_self, smul_smul, pow_two]
  rw [hw, LinearMap.smul_apply, Module.End.one_apply] at h
  exact (smul_left_injective ℂ ht0) (h.trans (one_smul ℂ t).symm)

/-- Normalized squares multiply when the two charges have even inner product. -/
theorem sigmaBlockOTransport_add (a b : lam0.carrier)
    (hc : εΛ (inclΛ a) (inclΛ b) * εΛ (inclΛ b) (inclΛ a) = 1) :
    tc (a + b) ^ 2 * εΛ (inclΛ (a + b)) (inclΛ (a + b)) =
      (tc a ^ 2 * εΛ (inclΛ a) (inclΛ a)) *
        (tc b ^ 2 * εΛ (inclΛ b) (inclΛ b)) := by
  have ht := congrArg (fun z : ℂ => z ^ 2) (tc_mul_tc a b)
  simp only [mul_pow, pow_two (εΛ _ _), pow_two (εN _ _), εΛ_sq, εN_sq,
    mul_one, one_mul] at ht
  rw [← ht, map_add]
  simp only [εΛ, latticeCocycle_add_left, latticeCocycle_add_right] at hc ⊢
  linear_combination (tc a ^ 2 * tc b ^ 2 *
    latticeCocycle leech (inclΛ a) (inclΛ a) *
    latticeCocycle leech (inclΛ b) (inclΛ b)) * hc

variable {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) (hD8 : D.card = 8)

/-- All even subsets of one octad have the same normalized transport square. -/
theorem sigmaBlockOTransport_sq {S : Finset (Fin 24)} (he : Even S.card)
    (hS : S ⊆ D) :
    tc (aSA hDA S) ^ 2 * εΛ (inclΛ (aSA hDA S)) (inclΛ (aSA hDA S)) =
      tc (bAD hDA) ^ 2 * εΛ (inclΛ (bAD hDA)) (inclΛ (bAD hDA)) := by
  have hc : εΛ (inclΛ (aSA hDA S)) (inclΛ (dSA S)) *
      εΛ (inclΛ (dSA S)) (inclΛ (aSA hDA S)) = 1 := by
    rw [latticeCocycle_comm leech leech_even, inclΛ_form, ← inclN_form,
      inclN_aSA hDA he, inclN_dSA he, map_sub, LinearMap.sub_apply]
    have hf : golayN.form (inclN (bAD hDA)) (dl S) = S.card := by
      rw [IntegralLattice.form_symm golayN]; exact form_dl_β hDA hS
    rw [hf]
    have hd : golayN.form (dl S) (dl S) = 2 * (S.card : ℤ) := by
      rw [dl, form_phiR]
      congr 1
      simp [dotProduct, ind]
    rw [hd, show (S.card : ℤ) - 2 * S.card = -(S.card : ℤ) by ring,
      _root_.zpow_neg, zpow_natCast, he.neg_one_pow, inv_one]
  have ht := sigmaBlockOTransport_add (aSA hDA S) (dSA S) hc
  rw [aSA, sub_add_cancel, sigmaBlockODelta_sq he, mul_one] at ht
  exact ht.symm

/-- The finite even-subset cube of an octad. -/
abbrev sigmaBlockOSubsets (D : Finset (Fin 24)) :=
  ↥(D.powerset.filter (fun S : Finset (Fin 24) => Even S.card))

theorem sigmaBlockOSubsets_spec (S : sigmaBlockOSubsets D) :
    S.val ⊆ D ∧ Even S.val.card := by
  simpa only [Finset.mem_filter, Finset.mem_powerset] using S.property

/-- Reindex the octad charge by its unique unoriented short pair. -/
def sigmaBlockOIndex (S : sigmaBlockOSubsets D) : ShortIdx :=
  sigmaBlockRIndex (inclΛ (aSA hDA S.val))
    (form_aSA hDA S.val (sigmaBlockOSubsets_spec S).2
      (sigmaBlockOSubsets_spec S).1 hD8)

theorem sigmaBlockOIndex_frame (S : sigmaBlockOSubsets D) :
    frameX0P (inclΛ (aSA hDA S.val)) =
      frameX0P (shortVec (sigmaBlockOIndex hDA hD8 S)) :=
  sigmaBlockRIndex_frame _ _

theorem sigmaBlockOIndex_even (S : sigmaBlockOSubsets D) :
    sigmaBlockParity (sigmaBlockOIndex hDA hD8 S) = 0 := by
  apply (sigmaBlockShort_mem_V0_iff _).mp
  rw [← sigmaBlockOIndex_frame]
  exact (lV (inclΛ (aSA hDA S.val)) (inclΛ_mem _)).property

/-- Cube transport measured against the fixed dictionary phase. -/
def sigmaBlockOPhase (S : sigmaBlockOSubsets D) : ℂ :=
  nuC (inclN (bAD hDA)) S.val * tc (aSA hDA S.val) /
    griessShortSign (sigmaBlockOIndex hDA hD8 S)

theorem sigmaBlockOPhase_ne_zero (S : sigmaBlockOSubsets D) :
    sigmaBlockOPhase hDA hD8 S ≠ 0 :=
  div_ne_zero (mul_ne_zero (nuC_ne_zero _ _) (tc_ne_zero _)) (liftSignPhase_ne_zero _)

theorem sigmaBlockOPhase_sq (S : sigmaBlockOSubsets D) :
    sigmaBlockOPhase hDA hD8 S ^ 2 =
      tc (bAD hDA) ^ 2 * εΛ (inclΛ (bAD hDA)) (inclΛ (bAD hDA)) := by
  have hs := griessShortSign_sq (sigmaBlockOIndex hDA hD8 S)
  have hc := sigmaBlockRIndex_cocycle (inclΛ (aSA hDA S.val))
    (form_aSA hDA S.val (sigmaBlockOSubsets_spec S).2
      (sigmaBlockOSubsets_spec S).1 hD8)
  change εΛ (inclΛ (aSA hDA S.val)) (inclΛ (aSA hDA S.val)) =
    εΛ (shortVec (sigmaBlockOIndex hDA hD8 S))
      (shortVec (sigmaBlockOIndex hDA hD8 S)) at hc
  change griessShortSign (sigmaBlockOIndex hDA hD8 S) ^ 2 *
    εΛ (shortVec (sigmaBlockOIndex hDA hD8 S))
      (shortVec (sigmaBlockOIndex hDA hD8 S)) = 1 at hs
  rw [← hc] at hs
  rw [sigmaBlockOPhase, div_pow, mul_pow, sigmaBlockONu_sq, one_mul]
  rw [div_eq_iff (pow_ne_zero 2 (liftSignPhase_ne_zero _))]
  rw [← sigmaBlockOTransport_sq hDA (sigmaBlockOSubsets_spec S).2
    (sigmaBlockOSubsets_spec S).1]
  linear_combination -(tc (aSA hDA S.val) ^ 2) * hs

/-- The sign of an octad Hadamard entry in the fixed dictionary. -/
def sigmaBlockOWeight (S T : sigmaBlockOSubsets D) : ℚ :=
  sigmaBlockRSign (cD D * (-1 : ℂ) ^ (S.val ∩ T.val).card *
    (sigmaBlockOPhase hDA hD8 T / sigmaBlockOPhase hDA hD8 S))

theorem sigmaBlockOWeight_values (S T : sigmaBlockOSubsets D) :
    sigmaBlockOWeight hDA hD8 S T = 1 ∨ sigmaBlockOWeight hDA hD8 S T = -1 :=
  sigmaBlockRSign_values _

theorem sigmaBlockOWeight_cast (S T : sigmaBlockOSubsets D) :
    (sigmaBlockOWeight hDA hD8 S T : ℂ) =
      cD D * (-1 : ℂ) ^ (S.val ∩ T.val).card *
        (sigmaBlockOPhase hDA hD8 T / sigmaBlockOPhase hDA hD8 S) := by
  apply sigmaBlockRSign_cast
  rw [mul_pow, mul_pow, pow_two (cD D), cD_mul_self, one_mul, ← pow_mul,
    mul_comm (S.val ∩ T.val).card 2, pow_mul]
  norm_num only [neg_one_sq, one_pow, one_mul]
  rw [div_pow, sigmaBlockOPhase_sq, sigmaBlockOPhase_sq]
  exact div_self (by
    rw [← sigmaBlockOPhase_sq hDA hD8 S]
    exact pow_ne_zero 2 (sigmaBlockOPhase_ne_zero hDA hD8 S))

/-- The original charged coefficient becomes a rational sign divided by eight. -/
theorem sigmaBlockOKS (S T : sigmaBlockOSubsets D) :
    griessShortSign (sigmaBlockOIndex hDA hD8 S) * KS hDA S.val T.val =
      ((sigmaBlockOWeight hDA hD8 S T : ℂ) / 8) *
        griessShortSign (sigmaBlockOIndex hDA hD8 T) := by
  rw [KS, coef_even hDA hD8 (sigmaBlockOSubsets_spec S).2
    (sigmaBlockOSubsets_spec S).1 (sigmaBlockOSubsets_spec T).1
    (sigmaBlockOSubsets_spec T).2, hD8, rH_pow_eight,
    sigmaBlockOWeight_cast, sigmaBlockOPhase, sigmaBlockOPhase, XS]
  field_simp [tc_ne_zero, nuC_ne_zero, liftSignPhase_ne_zero]
  ring

include hD8 in
/-- The paired octad formula, before dictionary normalization. -/
theorem sigmaBlockOPaired (S : sigmaBlockOSubsets D) :
    (sig (lV (inclΛ (aSA hDA S.val)) (inclΛ_mem _)) : VPlus) =
      ∑ T : sigmaBlockOSubsets D,
        (KS hDA S.val T.val / 2) • frameX0P (inclΛ (aSA hDA T.val)) := by
  have h := congrArg plusProj (sig_lV_aSA hDA hD8
    (sigmaBlockOSubsets_spec S).2 (sigmaBlockOSubsets_spec S).1)
  rw [plusProj_of_mem, map_sum] at h
  simp only [map_smul, plusProj_latChargeGen, smul_smul] at h
  rw [← Finset.sum_attach] at h
  simpa only [Finset.univ_eq_attach, div_eq_mul_inv, one_mul] using h

/-- Rational short-coordinate image of one octad pair. -/
def sigmaBlockOImage (S : sigmaBlockOSubsets D) : SpaceX :=
  ∑ T : sigmaBlockOSubsets D,
    (sigmaBlockOWeight hDA hD8 S T / 16) • sigmaBlockRUnit (sigmaBlockOIndex hDA hD8 T)

/-- The normalized octad letter in the even frame sector. -/
def sigmaBlockOV (S : sigmaBlockOSubsets D) : V0Sub.carrier :=
  griessShortSign (sigmaBlockOIndex hDA hD8 S) •
    lV (inclΛ (aSA hDA S.val)) (inclΛ_mem _)

theorem sigmaBlockOV_dict (S : sigmaBlockOSubsets D) :
    (sigmaBlockOV hDA hD8 S : VPlus) =
      shortDict griessShortSign (sigmaBlockRUnit (sigmaBlockOIndex hDA hD8 S)) := by
  rw [sigmaBlockRUnit_dict]
  change griessShortSign _ • frameX0P _ = _
  rw [sigmaBlockOIndex_frame hDA hD8]

theorem sigmaBlockOV_sigma (S : sigmaBlockOSubsets D) :
    (v0Sigma (sigmaBlockOV hDA hD8 S) : VPlus) =
      shortDict griessShortSign (sigmaBlockOImage hDA hD8 S) := by
  change (sig (sigmaBlockOV hDA hD8 S) : VPlus) = _
  rw [sigmaBlockOV, sig_smul, Submodule.coe_smul, sigmaBlockOPaired hDA hD8,
    Finset.smul_sum, sigmaBlockOImage, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [sigmaBlockRShort_smul, sigmaBlockRUnit_dict, smul_smul, smul_smul,
    sigmaBlockOIndex_frame hDA hD8]
  congr 1
  push_cast
  linear_combination sigmaBlockOKS hDA hD8 S T / 2

/-- Triality on every octad column of the fixed untwisted dictionary. -/
theorem sigmaBlockONat (S : sigmaBlockOSubsets D) :
    sigmaAut (untwistedDictNat griessShortSign
      (shortBlock (Pi.single (sigmaBlockOIndex hDA hD8 S) 1)) : Vnat) =
        (untwistedDictNat griessShortSign (shortBlock (sigmaBlockOImage hDA hD8 S)) :
          Vnat) := by
  change sigNat Dnat (untwistedDict griessShortSign
    (shortBlock (sigmaBlockRUnit (sigmaBlockOIndex hDA hD8 S))), 0) = _
  rw [untwistedDict_shortBlock, ← sigmaBlockOV_dict, sigNat_V0]
  apply Prod.ext
  · change (v0Sigma (sigmaBlockOV hDA hD8 S) : VPlus) =
      untwistedDict griessShortSign (shortBlock (sigmaBlockOImage hDA hD8 S))
    rw [untwistedDict_shortBlock, sigmaBlockOV_sigma]
  · rfl

/-- Equality up to sign identifies the reindexed short coordinate. -/
theorem sigmaBlockOIndex_eq (a : leech.carrier) (ha : leech.form a a = 4)
    {c : ShortIdx} (h : a = shortVec c ∨ a = -shortVec c) :
    sigmaBlockRIndex a ha = c :=
  shortSignDictionary_griessShortSign.pm_injective c _
    (liftSignPm_trans (liftSignPm_symm (sigmaBlockRIndex_spec a ha)) h)

/-- A column is explicitly one of the two-root or octad formulas. -/
inductive sigmaBlockOColumnData : ShortIdx → Type
  | P {j k : Fin 24} (hjk : j ≠ k) : sigmaBlockOColumnData (sigmaBlockRP hjk)
  | M {j k : Fin 24} (hjk : j ≠ k) : sigmaBlockOColumnData (sigmaBlockRM hjk)
  | octad {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) (hD8 : D.card = 8)
      (S : sigmaBlockOSubsets D) : sigmaBlockOColumnData (sigmaBlockOIndex hDA hD8 S)

/-- Exhaustiveness of the explicit formulas on all even short classes. -/
theorem sigmaBlockOColumn_exists (c : ShortIdx) (he : sigmaBlockParity c = 0) :
    Nonempty (sigmaBlockOColumnData c) := by
  classical
  have hn := (mem_normFour leech leech_posDef).mpr (shortVec_norm c)
  rw [normFour_eq_union, Finset.mem_union, Finset.mem_image] at hn
  obtain ⟨γ, hγ, hpair⟩ : ∃ γ ∈ halfFourChi 0,
      γ = shortVec c ∨ γ = -shortVec c := by
    rcases hn with hp | ⟨γ, hγ, hn⟩
    · exact ⟨shortVec c, Finset.mem_filter.mpr
        ⟨hp, (sigmaBlockParity_eq c).trans he⟩, Or.inl rfl⟩
    · refine ⟨γ, Finset.mem_filter.mpr ⟨hγ, ?_⟩, Or.inr ?_⟩
      · have hc := (sigmaBlockParity_eq c).trans he
        rw [← hn, map_neg, neg_eq_zero] at hc
        exact hc
      · rw [← hn, neg_neg]
  have hi (a : leech.carrier) (ha : leech.form a a = 4)
      (hg : γ = a ∨ γ = -a) : sigmaBlockRIndex a ha = c :=
    sigmaBlockOIndex_eq a ha (liftSignPm_trans (liftSignPm_symm hg) hpair)
  rcases classify_S0 hγ with ⟨j, k, hjk, hp | hp | hm | hm⟩ | ⟨D, hDA, hD8, S, he, hS, hg⟩
  · rw [← hi (gP j k) (form_gP_self hjk) (Or.inl hp)]
    exact ⟨sigmaBlockOColumnData.P hjk⟩
  · rw [← hi (gP j k) (form_gP_self hjk) (Or.inr hp)]
    exact ⟨sigmaBlockOColumnData.P hjk⟩
  · rw [← hi (gM j k) (form_gM_self hjk) (Or.inl hm)]
    exact ⟨sigmaBlockOColumnData.M hjk⟩
  · rw [← hi (gM j k) (form_gM_self hjk) (Or.inr hm)]
    exact ⟨sigmaBlockOColumnData.M hjk⟩
  · let s : sigmaBlockOSubsets D := ⟨S, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hS, he⟩⟩
    have hs : sigmaBlockOIndex hDA hD8 s = c :=
      hi _ (form_aSA hDA S he hS hD8) (Or.inl hg)
    rw [← hs]
    exact ⟨sigmaBlockOColumnData.octad hDA hD8 s⟩

/-- The rational image attached to each explicit type of column. -/
def sigmaBlockOColumnData.image {c : ShortIdx} : sigmaBlockOColumnData c → SpaceB
  | .P hjk => sigmaBlockRPImage hjk
  | .M hjk => sigmaBlockRMImage hjk
  | .octad hDA hD8 S => shortBlock (sigmaBlockOImage hDA hD8 S)

theorem sigmaBlockOColumnData.nat {c : ShortIdx} (d : sigmaBlockOColumnData c) :
    sigmaBlockRAut (sigmaBlockRDict (shortBlock (sigmaBlockRUnit c))) =
      sigmaBlockRDict d.image := by
  rw [sigmaBlockRAut_apply, sigmaBlockRDict_apply, sigmaBlockRDict_apply]
  cases d with
  | P hjk =>
    simp only [sigmaBlockOColumnData.image]
    exact sigmaBlockRNat_P hjk
  | M hjk =>
    simp only [sigmaBlockOColumnData.image]
    exact sigmaBlockRNat_M hjk
  | octad hDA hD8 S =>
    simp only [sigmaBlockOColumnData.image]
    exact sigmaBlockONat hDA hD8 S

/-- Choose an explicit column for each even short index; extend by zero on odd indices. -/
def sigmaBlockOColumn (c : ShortIdx) : SpaceB :=
  if he : sigmaBlockParity c = 0 then
    (Classical.choice (sigmaBlockOColumn_exists c he)).image else 0

/-- Every even short column satisfies the rational dictionary identity. -/
theorem sigmaBlockOColumn_nat (c : ShortIdx) (he : sigmaBlockParity c = 0) :
    sigmaBlockRAut (sigmaBlockRDict (shortBlock (sigmaBlockRUnit c))) =
      sigmaBlockRDict (sigmaBlockOColumn c) := by
  rw [sigmaBlockOColumn, dif_pos he]
  exact sigmaBlockOColumnData.nat _

/-- Rational triality on the full short summand, extended by zero on odd columns. -/
def sigmaBlockOShort : SpaceX →ₗ[ℚ] SpaceB where
  toFun x := ∑ c, x c • sigmaBlockOColumn c
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- A short vector decomposes into its unit-coordinate columns. -/
theorem sigmaBlockOShort_decompose (x : SpaceX) :
    shortBlock x = ∑ c, x c • shortBlock (sigmaBlockRUnit c) := by
  classical
  apply Prod.ext
  · simp [shortBlock, Prod.fst_sum]
  · apply Prod.ext
    · simp only [shortBlock, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst]
      change x = ∑ c, x c • sigmaBlockRUnit c
      ext d
      simp [sigmaBlockRUnit, Pi.single_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    · simp [shortBlock, Prod.snd_sum]

/-- The full short formula holds for every even-supported rational vector. -/
theorem sigmaBlockOShort_nat (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 0 → x c = 0) :
    sigmaBlockRAut (sigmaBlockRDict (shortBlock x)) =
      sigmaBlockRDict (sigmaBlockOShort x) := by
  rw [sigmaBlockOShort_decompose]
  change sigmaBlockRAut (sigmaBlockRDict (∑ c, x c • shortBlock (sigmaBlockRUnit c))) =
    sigmaBlockRDict (∑ c, x c • sigmaBlockOColumn c)
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c _
  by_cases he : sigmaBlockParity c = 0
  · rw [sigmaBlockOColumn_nat c he]
  · rw [hx c he, zero_smul, zero_smul]

/-- Full rational triality on the even untwisted block. -/
def sigmaBlockOFull : SpaceB →ₗ[ℚ] SpaceB where
  toFun u := sigmaBlockRMatrix u.1 + sigmaBlockOShort u.2.1
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' q u := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

theorem sigmaBlockOFull_apply (u : SpaceB) :
    sigmaBlockOFull u = sigmaBlockRMatrix u.1 + sigmaBlockOShort u.2.1 := rfl

/-- The rational map intertwines triality on every even-supported untwisted input. -/
theorem sigmaBlockOFull_nat (A : symMat) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 0 → x c = 0) :
    sigmaAut (untwistedDictNat griessShortSign (A, x, 0) : Vnat) =
      (untwistedDictNat griessShortSign (sigmaBlockOFull (A, x, 0)) : Vnat) := by
  simp only [← sigmaBlockRDict_apply, ← sigmaBlockRAut_apply]
  have hu : (A, x, 0) = symBlock A + shortBlock x := by simp [symBlock, shortBlock]
  rw [hu, map_add, map_add]
  have hm := sigmaBlockRNat_matrix A
  simp only [← sigmaBlockRDict_apply, ← sigmaBlockRAut_apply] at hm
  rw [hm, sigmaBlockOShort_nat x hx, ← map_add]
  congr 1
  rw [← hu, sigmaBlockOFull_apply]

/-- Every even column outside the two-root families has the explicit octad formula. -/
theorem sigmaBlockOOctad_exists (c : ShortIdx) (he : sigmaBlockParity c = 0)
    (hp : ∀ (j k : Fin 24) (h : j ≠ k), c ≠ sigmaBlockRP h)
    (hm : ∀ (j k : Fin 24) (h : j ≠ k), c ≠ sigmaBlockRM h) :
    ∃ (D : Finset (Fin 24)) (hDA : ind D ∈ Leech.subA) (hD8 : D.card = 8)
      (S : sigmaBlockOSubsets D), c = sigmaBlockOIndex hDA hD8 S ∧
        sigmaAut (untwistedDictNat griessShortSign (shortBlock (Pi.single c 1)) :
          Vnat) = (untwistedDictNat griessShortSign
            (shortBlock (sigmaBlockOImage hDA hD8 S)) : Vnat) := by
  obtain ⟨d⟩ := sigmaBlockOColumn_exists c he
  cases d with
  | P h => exact False.elim (hp _ _ h rfl)
  | M h => exact False.elim (hm _ _ h rfl)
  | @octad D hDA hD8 S => exact ⟨D, hDA, hD8, S, rfl, sigmaBlockONat hDA hD8 S⟩

/-- The rational domain consisting of matrices and even-supported short coordinates. -/
def sigmaBlockOEven : Submodule ℚ SpaceB where
  carrier := {u | u.2.2 = 0 ∧ ∀ c, sigmaBlockParity c ≠ 0 → u.2.1 c = 0}
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  add_mem' ha hb := by
    constructor
    · change _ + _ = 0
      rw [ha.1, hb.1, add_zero]
    · intro c hc
      simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply,
        ha.2 c hc, hb.2 c hc, add_zero]
  smul_mem' q u hu := by
    constructor
    · change q • u.2.2 = 0
      rw [hu.1, smul_zero]
    · intro c hc
      change q * u.2.1 c = 0
      rw [hu.2 c hc, mul_zero]

theorem sigmaBlockOUnit_zero (c : ShortIdx) (he : sigmaBlockParity c = 0)
    (d : ShortIdx) (hd : sigmaBlockParity d ≠ 0) : sigmaBlockRUnit c d = 0 := by
  have hdc : d ≠ c := fun h => hd (h ▸ he)
  simp [sigmaBlockRUnit, hdc]

theorem sigmaBlockOImage_mem (S : sigmaBlockOSubsets D) :
    shortBlock (sigmaBlockOImage hDA hD8 S) ∈ sigmaBlockOEven := by
  constructor
  · rfl
  · intro c hc
    change (sigmaBlockOImage hDA hD8 S) c = 0
    simp only [sigmaBlockOImage, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro T _
    rw [sigmaBlockOUnit_zero _ (sigmaBlockOIndex_even hDA hD8 T) c hc, mul_zero]

theorem sigmaBlockOColumnData.mem {c : ShortIdx} (d : sigmaBlockOColumnData c) :
    d.image ∈ sigmaBlockOEven := by
  cases d with
  | P h =>
    refine ⟨rfl, fun c hc => ?_⟩
    change ((1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRP h) -
      (sigmaBlockRPWeight h * sigmaBlockRMWeight h / 2) •
        sigmaBlockRUnit (sigmaBlockRM h)) c = 0
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sigmaBlockOUnit_zero _ (sigmaBlockRP_even h) c hc,
      sigmaBlockOUnit_zero _ (sigmaBlockRM_even h) c hc, mul_zero, sub_self]
  | M h =>
    refine ⟨rfl, fun c hc => ?_⟩
    change (-(sigmaBlockRPWeight h * sigmaBlockRMWeight h / 2) •
      sigmaBlockRUnit (sigmaBlockRP h) +
        (1 / 2 : ℚ) • sigmaBlockRUnit (sigmaBlockRM h)) c = 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      sigmaBlockOUnit_zero _ (sigmaBlockRP_even h) c hc,
      sigmaBlockOUnit_zero _ (sigmaBlockRM_even h) c hc, mul_zero, add_zero]
  | octad hDA hD8 S => exact sigmaBlockOImage_mem hDA hD8 S

theorem sigmaBlockOColumn_mem (c : ShortIdx) : sigmaBlockOColumn c ∈ sigmaBlockOEven := by
  rw [sigmaBlockOColumn]
  split_ifs
  · exact sigmaBlockOColumnData.mem _
  · exact sigmaBlockOEven.zero_mem

theorem sigmaBlockOShort_mem (x : SpaceX) : sigmaBlockOShort x ∈ sigmaBlockOEven :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (sigmaBlockOColumn_mem c)

theorem sigmaBlockOMatrix_mem (A : symMat) : sigmaBlockRMatrix A ∈ sigmaBlockOEven := by
  rw [sigmaBlockRMatrix_apply, sigmaBlockRMatrixFun]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ ?_
  rw [sigmaBlockRColumn]
  split_ifs with h
  · exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨rfl, fun c hc => ?_⟩
    change (sigmaBlockROffX h) c = 0
    simp only [sigmaBlockROffX, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      sigmaBlockOUnit_zero _ (sigmaBlockRP_even h) c hc,
      sigmaBlockOUnit_zero _ (sigmaBlockRM_even h) c hc, mul_zero, add_zero]

/-- The assembled map takes values in the same even rational domain. -/
theorem sigmaBlockOFull_mem (u : SpaceB) : sigmaBlockOFull u ∈ sigmaBlockOEven := by
  rw [sigmaBlockOFull_apply]
  exact Submodule.add_mem _ (sigmaBlockOMatrix_mem u.1) (sigmaBlockOShort_mem u.2.1)

/-- Triality as a rational linear endomorphism of the even untwisted domain. -/
def sigmaBlockOFullEven : sigmaBlockOEven →ₗ[ℚ] sigmaBlockOEven :=
  (sigmaBlockOFull.codRestrict sigmaBlockOEven sigmaBlockOFull_mem).comp
    sigmaBlockOEven.subtype

end VOA.Moonshine.ConwayNorton.M8
