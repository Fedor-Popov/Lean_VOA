import VOA.Moonshine.MoonshineCNGriessUntwisted
import VOA.Moonshine.AutSigma
import VOA.Moonshine.SigmaTopOffdiag

/-!
# Frame sectors and triality on the untwisted dictionary

The short-coordinate split is rational coordinate parity. All oscillator matrices are
in `V₀⁺`; diagonal matrices are fixed by triality. Odd short coordinates map through
`Φ` to the twisted frame sector. The full rational dictionary matrix of `v0Sigma`
still requires matching the off-diagonal and octad transport constants with `ζ`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.Moonshine.TrialityTw VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.M8hKey VOA.Moonshine.SigmaAssemble
open VOA.Moonshine.VnatBlock
open VOA.LatGen VOA.IntegralLattice Matrix

/-- Parity in the short-vector coordinates, pulled back by the Golay permutation. -/
def sigmaBlockParity (c : ShortIdx) : ZMod 2 := (uvec c (piPerm 0) : ZMod 2)

theorem sigmaBlockParity_eq (c : ShortIdx) :
    frameChar (shortVec c) = sigmaBlockParity c := by
  change (vec (shortVec c) 0 : ZMod 2) = _
  rw [vec_shortVec]
  rfl

/-- Every coordinate has the same parity, so the permutation does not affect the split. -/
theorem sigmaBlockParity_coord (c : ShortIdx) (j : Fin 24) :
    sigmaBlockParity c = (uvec c j : ZMod 2) := by
  obtain ⟨m, _, d, _, hd, _⟩ := (uvec_mem_minVecs c).1
  have hp (k : Fin 24) : (uvec c k : ZMod 2) = (m : ZMod 2) := by
    have h := (ZMod.intCast_eq_intCast_iff (uvec c k) (m + 2 * bitLift (d k)) 2).mpr
      ((hd k).of_dvd (by norm_num : (2 : ℤ) ∣ 4))
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero] using h
  exact (hp (piPerm 0)).trans (hp j).symm

theorem sigmaBlockFrameX_eigen (α : leech.carrier) :
    plusFrameAut (frameX0P α) = Extraspecial.sgn (frameChar α) • frameX0P α := by
  apply Subtype.ext
  change chiLat leech frameChar
    (latChargeGen leech α + latChargeGen leech (-α)) = _
  simp only [map_add, latChargeGen, chiLat_latStateGen, chiSign_neg]
  exact (smul_add _ _ _).symm

/-- An exact sector criterion, including the converse since a short state is nonzero. -/
theorem sigmaBlockShort_mem_iff (c : ShortIdx) (i : ZMod 2) :
    frameX0P (shortVec c) ∈ frameSector i ↔ sigmaBlockParity c = i := by
  rw [mem_frameSector', sigmaBlockFrameX_eigen, sigmaBlockParity_eq]
  constructor
  · intro h
    have hsign := (smul_left_injective ℂ (frameX0P_ne_zero (shortVec c))) h
    generalize sigmaBlockParity c = p at hsign ⊢
    fin_cases p <;> fin_cases i
    · rfl
    · change Extraspecial.sgn (0 : ZMod 2) = Extraspecial.sgn 1 at hsign
      rw [Extraspecial.sgn_zero, Extraspecial.sgn_one] at hsign
      norm_num at hsign
    · change Extraspecial.sgn (1 : ZMod 2) = Extraspecial.sgn 0 at hsign
      rw [Extraspecial.sgn_zero, Extraspecial.sgn_one] at hsign
      norm_num at hsign
    · rfl
  · rintro rfl
    rfl

theorem sigmaBlockShort_mem_V0_iff (c : ShortIdx) :
    frameX0P (shortVec c) ∈ V0Sub.carrier ↔ sigmaBlockParity c = 0 := by
  rw [V0Sub_carrier, sigmaBlockShort_mem_iff]

theorem sigmaBlockShort_even_iff (c : ShortIdx) (j : Fin 24) :
    frameX0P (shortVec c) ∈ V0Sub.carrier ↔ Even (uvec c j) := by
  rw [sigmaBlockShort_mem_V0_iff, sigmaBlockParity_coord c j,
    ZMod.intCast_eq_zero_iff_even]

theorem sigmaBlockShort_odd_iff (c : ShortIdx) (j : Fin 24) :
    frameX0P (shortVec c) ∈ frameSector 1 ↔ Odd (uvec c j) := by
  rw [sigmaBlockShort_mem_iff, sigmaBlockParity_coord c j,
    ZMod.intCast_eq_one_iff_odd]

/-- No condition on the rational matrix is needed for membership in `V₀⁺`. -/
theorem sigmaBlockMat_mem (M : Matrix (Fin 24) (Fin 24) ℚ) :
    matDict M ∈ V0Sub.carrier := by
  rw [matDict_apply, conwayQuad_eq_sum_dV]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (dV _ _).property)

/-- A matrix state can belong to the odd sector only when its image vanishes. -/
theorem sigmaBlockMat_mem_V3_iff (M : Matrix (Fin 24) (Fin 24) ℚ) :
    matDict M ∈ frameSector 1 ↔ matDict M = 0 := by
  constructor
  · exact Submodule.disjoint_def.mp V0_isCompl.disjoint _ (sigmaBlockMat_mem M)
  · rintro h
    rw [h]
    exact Submodule.zero_mem _

/-- Rational projections onto the even and odd short coordinates. -/
def sigmaBlockShortPart (i : ZMod 2) : SpaceX →ₗ[ℚ] SpaceX where
  toFun x c := if sigmaBlockParity c = i then x c else 0
  map_add' x y := by
    ext c
    by_cases h : sigmaBlockParity c = i <;> simp [h]
  map_smul' q x := by
    ext c
    by_cases h : sigmaBlockParity c = i <;> simp [h]

theorem sigmaBlockShortPart_add (x : SpaceX) :
    sigmaBlockShortPart 0 x + sigmaBlockShortPart 1 x = x := by
  ext c
  change (if sigmaBlockParity c = 0 then x c else 0) +
    (if sigmaBlockParity c = 1 then x c else 0) = x c
  generalize sigmaBlockParity c = p
  fin_cases p
  · change x c + 0 = x c
    exact add_zero _
  · change 0 + x c = x c
    exact zero_add _

theorem sigmaBlockShortDict_mem (ζ : ShortIdx → ℂ) (x : SpaceX) (i : ZMod 2)
    (hx : ∀ c, sigmaBlockParity c ≠ i → x c = 0) :
    shortDict ζ x ∈ frameSector i := by
  rw [shortDict_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : sigmaBlockParity c = i
  · exact Submodule.smul_mem _ _ ((sigmaBlockShort_mem_iff c i).mpr hc)
  · simp only [hx c hc, Rat.cast_zero, zero_mul, zero_smul]
    exact Submodule.zero_mem _

theorem sigmaBlockShortPart_mem (ζ : ShortIdx → ℂ) (x : SpaceX) (i : ZMod 2) :
    shortDict ζ (sigmaBlockShortPart i x) ∈ frameSector i := by
  apply sigmaBlockShortDict_mem
  intro c hc
  exact if_neg hc

theorem sigmaBlockUntwisted_mem (ζ : ShortIdx → ℂ) (u : SpaceB)
    (hu : ∀ c, sigmaBlockParity c ≠ 0 → u.2.1 c = 0) :
    untwistedDict ζ u ∈ V0Sub.carrier := by
  rw [untwistedDict_apply]
  have hs := sigmaBlockShortDict_mem ζ u.2.1 0 hu
  rw [← V0Sub_carrier] at hs
  exact Submodule.add_mem _ (sigmaBlockMat_mem _) hs

/-- The even component includes every matrix coordinate. -/
def sigmaBlockEvenState (ζ : ShortIdx → ℂ) (u : SpaceB) : V0Sub.carrier :=
  ⟨matDict u.1 + shortDict ζ (sigmaBlockShortPart 0 u.2.1), by
    have hs := sigmaBlockShortPart_mem ζ u.2.1 0
    rw [← V0Sub_carrier] at hs
    exact Submodule.add_mem _ (sigmaBlockMat_mem _) hs⟩

theorem sigmaBlockUntwisted_split (ζ : ShortIdx → ℂ) (u : SpaceB) :
    untwistedDict ζ u = (sigmaBlockEvenState ζ u : VPlus) +
      shortDict ζ (sigmaBlockShortPart 1 u.2.1) := by
  change matDict u.1 + shortDict ζ u.2.1 =
    (matDict u.1 + shortDict ζ (sigmaBlockShortPart 0 u.2.1)) +
    shortDict ζ (sigmaBlockShortPart 1 u.2.1)
  rw [add_assoc, ← map_add, sigmaBlockShortPart_add]

/-- The complete untwisted block formula; the twisted dictionary remains unspecified. -/
theorem sigmaBlockNat_split (ζ : ShortIdx → ℂ) (u : SpaceB) :
    sigmaAut (untwistedDictNat ζ u : Vnat) =
      (((v0Sigma (sigmaBlockEvenState ζ u) : V0Sub.carrier) : VPlus),
        Dnat.Φ (shortDict ζ (sigmaBlockShortPart 1 u.2.1))) := by
  rw [sigmaAut_apply]
  change sigNat Dnat (untwistedDict ζ u, 0) = _
  rw [sigmaBlockUntwisted_split]
  have hp (a b : VPlus) : ((a + b, 0) : Vnat) = (a, 0) + (b, 0) := by simp
  rw [hp, map_add, sigNat_V0, sigNat_V3 Dnat (sigmaBlockShortPart_mem ζ u.2.1 1)]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- Triality on the even dictionary, with its existing `v0Sigma` normalization. -/
theorem sigmaBlockNat_V0 (ζ : ShortIdx → ℂ) (u : SpaceB)
    (hu : ∀ c, sigmaBlockParity c ≠ 0 → u.2.1 c = 0) :
    sigmaAut (untwistedDictNat ζ u : Vnat) =
      (((v0Sigma ⟨untwistedDict ζ u, sigmaBlockUntwisted_mem ζ u hu⟩ :
        V0Sub.carrier) : VPlus), 0) := by
  rw [sigmaAut_apply]
  exact sigNat_V0 Dnat ⟨untwistedDict ζ u, sigmaBlockUntwisted_mem ζ u hu⟩

/-- Odd short coordinates enter precisely the twisted `T_s⁺` block via `Φ`. -/
theorem sigmaBlockNat_V3 (ζ : ShortIdx → ℂ) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 1 → x c = 0) :
    sigmaAut (untwistedDictNat ζ (shortBlock x) : Vnat) =
      (0, Dnat.Φ (shortDict ζ x)) := by
  change sigNat Dnat (untwistedDict ζ (shortBlock x), 0) = _
  rw [untwistedDict_shortBlock]
  exact sigNat_V3 Dnat (sigmaBlockShortDict_mem ζ x 1 hx)

theorem sigmaBlockNat_V3_mem (ζ : ShortIdx → ℂ) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 1 → x c = 0) :
    Dnat.Φ (shortDict ζ x) ∈ TPframe Dnat.s :=
  Dnat.Φ_mem _ (sigmaBlockShortDict_mem ζ x 1 hx)

/-- The two coordinate systems use the same vectors `8eᵢ`. -/
theorem sigmaBlockAxis_eq (i : Fin 24) : conwayAxis i = fw i := by
  apply Subtype.ext
  exact (lv_fw i).symm

/-- Diagonal matrices give a rational fixed subspace of the dictionary. -/
theorem sigmaBlockNat_diagonal (ζ : ShortIdx → ℂ) (A : symMat)
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 24) (Fin 24) ℚ) i j = 0) :
    sigmaAut (untwistedDictNat ζ (symBlock A) : Vnat) =
      (untwistedDictNat ζ (symBlock A) : Vnat) := by
  have hm : matDict A = (8 : ℂ)⁻¹ • ∑ i,
      ((A : Matrix (Fin 24) (Fin 24) ℚ) (piPerm i) (piPerm i) : ℂ) •
        (dV (fw i) (fw i) : VPlus) := by
    rw [matDict_apply, conwayQuad_eq_sum_dV]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [axiomToConway_apply, sigmaBlockAxis_eq]
    · intro j _ hji
      rw [axiomToConway_apply, hA _ _ (fun h => hji (piPerm.injective h).symm)]
      simp
    · simp
  change sigNat Dnat (untwistedDict ζ (symBlock A), 0) =
    (untwistedDict ζ (symBlock A), 0)
  rw [untwistedDict_symBlock]
  rw [hm]
  have hd (i : Fin 24) :
      sigNat Dnat ((dV (fw i) (fw i) : VPlus), 0) =
        ((dV (fw i) (fw i) : VPlus), 0) := by
    rw [sigNat_V0]
    exact congrArg (fun a : V0Sub.carrier => ((a : VPlus), (0 : TP))) (sig_dV_fw i)
  have hs (v : VPlus) (q : ℂ) : ((q • v, 0) : Vnat) = q • (v, 0) := by simp
  have hsum (f : Fin 24 → VPlus) :
      ((∑ i, f i, 0) : Vnat) = ∑ i, ((f i, 0) : Vnat) := by
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_const_zero]
  simp only [hs, hsum, map_smul, map_sum, hd]

/-- The untwisted/twisted sign `z`, as a complex linear map. -/
def sigmaBlockZ : Vnat →ₗ[ℂ] Vnat where
  toFun v := (v.1, -v.2)
  map_add' u v := by simp [add_comm]
  map_smul' q v := by simp

/-- The four frame-sector signs are `(+1,-1,+1,-1)`. -/
def sigmaBlockFrameSign (s : ZMod 2) : Vnat →ₗ[ℂ] Vnat :=
  blockOp plusFrame 0 0
    ((TPframe s).projection (TPframe (s + 1)) (TPframe_isCompl' s) -
      (TPframe (s + 1)).projection (TPframe s) (TPframe_isCompl' s).symm)

/-- Conjugating `z` by triality is the frame-sector sign, for any sigma data. -/
theorem sigmaBlockConjugate (D : SigmaData) :
    sigNat D ∘ₗ sigmaBlockZ ∘ₗ sigNat D = sigmaBlockFrameSign D.s := by
  have hinv (v : Vnat) : sigNat D (sigNat D v) = v := by
    have h := congrArg (fun f : Module.End ℂ Vnat => f v) (sigNat_sq D)
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  refine vnat_ext D.s ?_ ?_ ?_ ?_
  · intro a ha
    have hf : plusFrame a = a := by
      have h := mem_frameSector'.mp (V0Sub_carrier ▸ ha)
      simpa only [Extraspecial.sgn_zero, one_smul] using h
    simp only [LinearMap.comp_apply]
    have hz : sigmaBlockZ (sigNat D (a, 0)) = sigNat D (a, 0) := by
      rw [sigNat_V0 D ⟨a, ha⟩]
      simp [sigmaBlockZ]
    rw [hz, hinv]
    simp [sigmaBlockFrameSign, blockOp_apply, hf]
  · intro a ha
    have hf : plusFrame a = -a := by
      have h := mem_frameSector'.mp ha
      simpa only [Extraspecial.sgn_one, neg_one_smul] using h
    simp only [LinearMap.comp_apply]
    have hz : sigmaBlockZ (sigNat D (a, 0)) = -sigNat D (a, 0) := by
      rw [sigNat_V3 D ha]
      simp [sigmaBlockZ]
    rw [hz, map_neg, hinv]
    simp [sigmaBlockFrameSign, blockOp_apply, hf]
  · intro t ht
    simp only [LinearMap.comp_apply]
    have hz : sigmaBlockZ (sigNat D (0, t)) = sigNat D (0, t) := by
      rw [sigNat_Ts D ht]
      simp [sigmaBlockZ]
    rw [hz, hinv]
    simp [sigmaBlockFrameSign, blockOp_apply,
      Submodule.projection_apply_left _ ⟨t, ht⟩,
      Submodule.projection_apply_of_mem_right _ ht]
  · intro t ht
    simp only [LinearMap.comp_apply]
    have hz : sigmaBlockZ (sigNat D (0, t)) = -sigNat D (0, t) := by
      rw [sigNat_Ts1 D ht]
      simp [sigmaBlockZ]
    rw [hz, map_neg, hinv]
    simp [sigmaBlockFrameSign, blockOp_apply,
      Submodule.projection_apply_left _ ⟨t, ht⟩,
      Submodule.projection_apply_of_mem_right _ ht]

theorem sigmaBlockAut_conjugate (v : Vnat) :
    sigmaAut (sigmaBlockZ (sigmaAut v)) = sigmaBlockFrameSign Dnat.s v := by
  rw [sigmaAut_apply, sigmaAut_apply]
  have h := LinearMap.congr_fun (sigmaBlockConjugate Dnat) v
  simpa only [LinearMap.comp_apply] using h

/-- A rational sign map: even short coordinates are fixed, odd ones are negated. -/
def sigmaBlockShortSign : SpaceX →ₗ[ℚ] SpaceX :=
  sigmaBlockShortPart 0 - sigmaBlockShortPart 1

theorem sigmaBlockShortSign_apply (x : SpaceX) (c : ShortIdx) :
    sigmaBlockShortSign x c = if sigmaBlockParity c = 0 then x c else -x c := by
  change (if sigmaBlockParity c = 0 then x c else 0) -
    (if sigmaBlockParity c = 1 then x c else 0) = _
  generalize sigmaBlockParity c = p
  fin_cases p
  · change x c - 0 = x c
    exact sub_zero _
  · change 0 - x c = -x c
    exact zero_sub _

theorem sigmaBlockPlusFrame_dict (ζ : ShortIdx → ℂ) (u : SpaceB) :
    plusFrame (untwistedDict ζ u) =
      untwistedDict ζ (u.1, (sigmaBlockShortSign u.2.1, u.2.2)) := by
  have h0 : plusFrame (sigmaBlockEvenState ζ u : VPlus) =
      (sigmaBlockEvenState ζ u : VPlus) := by
    have hm := (le_of_eq V0Sub_carrier) (sigmaBlockEvenState ζ u).property
    have h := mem_frameSector'.mp hm
    simpa only [Extraspecial.sgn_zero, one_smul] using h
  have h1 : plusFrame (shortDict ζ (sigmaBlockShortPart 1 u.2.1)) =
      -shortDict ζ (sigmaBlockShortPart 1 u.2.1) := by
    have h := mem_frameSector'.mp (sigmaBlockShortPart_mem ζ u.2.1 1)
    simpa only [Extraspecial.sgn_one, neg_one_smul] using h
  rw [sigmaBlockUntwisted_split, map_add, h0, h1]
  change (matDict u.1 + shortDict ζ (sigmaBlockShortPart 0 u.2.1)) +
    -shortDict ζ (sigmaBlockShortPart 1 u.2.1) =
      matDict u.1 + shortDict ζ (sigmaBlockShortPart 0 u.2.1 -
        sigmaBlockShortPart 1 u.2.1)
  rw [map_sub]
  abel

/-- In untwisted coordinates, `σ z σ` fixes matrices and negates odd short entries. -/
theorem sigmaBlockAut_conjugate_dict (ζ : ShortIdx → ℂ) (u : SpaceB) :
    sigmaAut (sigmaBlockZ (sigmaAut (untwistedDictNat ζ u : Vnat))) =
      (untwistedDictNat ζ (u.1, (sigmaBlockShortSign u.2.1, u.2.2)) : Vnat) := by
  rw [sigmaBlockAut_conjugate]
  change sigmaBlockFrameSign Dnat.s (untwistedDict ζ u, 0) =
    (untwistedDict ζ (u.1, (sigmaBlockShortSign u.2.1, u.2.2)), 0)
  simp only [sigmaBlockFrameSign, blockOp_apply, LinearMap.zero_apply, map_zero,
    add_zero, sigmaBlockPlusFrame_dict]

end VOA.Moonshine.ConwayNorton.M8
