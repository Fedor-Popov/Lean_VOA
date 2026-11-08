import VOA.Moonshine.MoonshineLRGriessTransfer
import VOA.Moonshine.MoonshineCNMonsterActionLift

/-!
# Rational triality in the full Griess dictionary

The even untwisted block is rational unconditionally. Rationality of the inverse
`Dnat.Ψ` follows from the forward odd block by involutivity and the rational
Griess form. Products with an odd short class then supply the other twisted half,
so no independent `Θ` calculation remains. The final equivalence isolates the
unproved input: rational `spinDict` coordinates of the normalized `Φ` images of
individual odd short classes.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.M8hKey VOA.Moonshine.SigmaAssemble VOA.Moonshine.TrialityTw
open VOA.Moonshine.InvForm
open VOA.Moonshine.SigmaTop VOA.Moonshine.MonsterGriess.Spin Matrix
open scoped TensorProduct

/-- Triality has rational full Griess coordinates at this input. -/
def sigmaBRational (u : SpaceB) : Prop :=
  ∃ v : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat v

theorem sigmaBInvol (v : Vnat) : sigmaAut (sigmaAut v) = v :=
  sigNat_invol v

/-- Rational inputs with rational images form a rational subspace. -/
def sigmaBDomain : Submodule ℚ SpaceB where
  carrier := {u | sigmaBRational u}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp only [map_zero, Submodule.coe_zero]
  add_mem' := by
    rintro u v ⟨u', hu⟩ ⟨v', hv⟩
    refine ⟨u' + v', ?_⟩
    rw [map_add, Submodule.coe_add, autVnat_map_add, hu, hv,
      map_add, Submodule.coe_add]
  smul_mem' := by
    rintro q u ⟨u', hu⟩
    refine ⟨q • u', ?_⟩
    rw [griessNat_smul, Submodule.coe_smul, autVnat_map_smul, hu,
      griessNat_smul, Submodule.coe_smul]

/-- Multiplicativity propagates rationality through Griess products. -/
theorem sigmaBRational_gmul {u v : SpaceB}
    (hu : sigmaBRational u) (hv : sigmaBRational v) : sigmaBRational (gmul u v) := by
  obtain ⟨u', hu⟩ := hu
  obtain ⟨v', hv⟩ := hv
  refine ⟨gmul u' v', ?_⟩
  rw [griessNat_gmul, griessNat_gmul, VertexOperatorAlgebra.griessMul_coe,
    VertexOperatorAlgebra.griessMul_coe, Aut.map_smul, hu, hv]

/-- Every rational image has a rational inverse image under the involution. -/
theorem sigmaBRational_reverse {u v : SpaceB}
    (h : sigmaAut (griessNat u : Vnat) = griessNat v) :
    sigmaAut (griessNat v : Vnat) = griessNat u := by
  rw [← h, sigmaBInvol]

/-- The existing even-block formula, now stated directly with `griessNat`. -/
theorem sigmaBEven_nat (A : symMat) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 0 → x c = 0) :
    sigmaAut (griessNat (A, x, 0) : Vnat) =
      griessNat ((sigmaBlockOFull (A, griessTrX x, 0)).1,
        griessTrX (sigmaBlockOFull (A, griessTrX x, 0)).2.1, 0) := by
  simpa only [griessIso_tmul] using griessTrSigmaBlockOFull_nat A x hx

theorem sigmaBEven_rational (A : symMat) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 0 → x c = 0) : sigmaBRational (A, x, 0) :=
  ⟨_, sigmaBEven_nat A x hx⟩

theorem sigmaBSpin_nat (N : SpaceW) :
    (griessNat (spinBlock N) : Vnat) = (0, spinDict N) := by
  rw [griessNat_coe, untwistedDict_spinBlock]
  rfl

/-- The odd block lands in the twisted sector, with its full dictionary phases. -/
theorem sigmaBOdd_nat (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 1 → x c = 0) :
    sigmaAut (griessNat (shortBlock x) : Vnat) =
      (0, Dnat.Φ (shortDict fullShortSign x)) := by
  rw [griessNat_coe, untwistedDict_shortBlock]
  change sigNat Dnat (shortDict fullShortSign x, spinDict 0) = _
  rw [map_zero]
  exact sigNat_V3 Dnat (sigmaBlockShortDict_mem fullShortSign x 1 hx)

/-- Sector membership alone is weaker than this exact rational coordinate criterion. -/
theorem sigmaBOdd_rational_iff (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 1 → x c = 0) :
    sigmaBRational (shortBlock x) ↔
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N := by
  constructor
  · rintro ⟨v, hv⟩
    rw [sigmaBOdd_nat x hx, griessNat_coe] at hv
    exact ⟨v.2.2, congrArg Prod.snd hv⟩
  · rintro ⟨N, hN⟩
    refine ⟨spinBlock N, ?_⟩
    rw [sigmaBOdd_nat x hx, sigmaBSpin_nat, hN]

/-- The rational forward odd block suffices for the whole untwisted summand. -/
theorem sigmaBUntwisted_rational
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N)
    (u : SpaceB) (hu : u.2.2 = 0) : sigmaBRational u := by
  obtain ⟨A, x, N⟩ := u
  change N = 0 at hu
  subst N
  have he : sigmaBRational (A, sigmaBlockShortPart 0 x, 0) :=
    sigmaBEven_rational A _ fun c hc => if_neg hc
  have ho : sigmaBRational (shortBlock (sigmaBlockShortPart 1 x)) :=
    (sigmaBOdd_rational_iff _ fun c hc => if_neg hc).2
      (hΦ _ fun c hc => if_neg hc)
  have hsum : (A, x, (0 : SpaceW)) =
      (A, sigmaBlockShortPart 0 x, 0) + shortBlock (sigmaBlockShortPart 1 x) := by
    simp only [shortBlock, Prod.mk_add_mk, add_zero, sigmaBlockShortPart_add]
  rw [hsum]
  exact sigmaBDomain.add_mem he ho

/-- Triality is self-adjoint on weight two because it is an isometric involution. -/
theorem sigmaBForm_adjoint (u v : VnatVOA.grading 2) :
    SimpleNat.natForm (u : Vnat) (sigmaAut (v : Vnat)) =
      SimpleNat.natForm (sigmaAut (u : Vnat)) (v : Vnat) := by
  have h := natForm_autRestrict sigmaAut u (vnatWeightTwoRestrict sigmaAut v)
  rw [vnatWeightTwoRestrict_apply_coe, sigmaBInvol] at h
  exact h.symm

/-- Rational pairings with the untwisted dictionary recover rational coordinates. -/
theorem sigmaBUntwisted_of_pairings (y : VPlus) (hy : y ∈ leechVOAPlus.grading 2)
    (hpair : ∀ u : SpaceB, u.2.2 = 0 → ∃ q : ℚ,
      plusForm (untwistedDict fullShortSign u) y = 2 * (q : ℂ)) :
    ∃ u : SpaceB, u.2.2 = 0 ∧ y = untwistedDict fullShortSign u := by
  classical
  rw [← span_fullUntwistedImage] at hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  have hc : ∀ l, ∃ q : ℚ, c l = (q : ℂ) := by
    intro l
    obtain ⟨q, hq⟩ := hpair _ (mem_untwistedSub.1
      ((bform.restrict untwistedSub).dualBasis
        bform_restrict_nondegenerate untwistedBasisQ l).2)
    simp only [map_sum, map_smul, smul_eq_mul, plusForm_dual_fullUntwistedImage] at hq
    rw [Finset.sum_eq_single l (fun k _ hkl => by rw [if_neg hkl]; simp)
      (fun h' => absurd (Finset.mem_univ l) h')] at hq
    rw [if_pos rfl] at hq
    refine ⟨q, ?_⟩
    push_cast at hq
    linear_combination hq / 2
  choose q hq using hc
  refine ⟨∑ l, q l • (untwistedBasisQ l : SpaceB), ?_, ?_⟩
  · have hm : (∑ l, q l • (untwistedBasisQ l : SpaceB)) ∈ untwistedSub :=
      Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (untwistedBasisQ l).2
    exact mem_untwistedSub.1 hm
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [untwistedDict_smul, hq l]
    rfl

/-- On `T_s⁺`, the forward odd rationality already forces inverse rationality. -/
theorem sigmaBTs_rational
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N)
    (N : SpaceW) (hN : spinDict N ∈ TPframe Dnat.s) :
    sigmaBRational (spinBlock N) := by
  have hact : sigmaAut (griessNat (spinBlock N) : Vnat) =
      (Dnat.Ψ (spinDict N), 0) := by
    rw [sigmaBSpin_nat, sigmaAut_apply, sigNat_Ts Dnat hN]
  have hy : Dnat.Ψ (spinDict N) ∈ leechVOAPlus.grading 2 := by
    have hm := (vnatWeightTwoRestrict sigmaAut (griessNat (spinBlock N))).property
    rw [vnatWeightTwoRestrict_apply_coe, hact, VnatVOA_grading, mem_gradingNat] at hm
    exact hm.1
  obtain ⟨v, hv, hdict⟩ := sigmaBUntwisted_of_pairings _ hy (by
    intro u hu
    obtain ⟨u', hu'⟩ := sigmaBUntwisted_rational hΦ u hu
    refine ⟨bform u' (spinBlock N), ?_⟩
    have h := sigmaBForm_adjoint (griessNat u) (griessNat (spinBlock N))
    rw [hu', griessNat_form, hact, griessNat_coe, SimpleNat.natForm_apply] at h
    change leechBV (untwistedDict fullShortSign u) (Dnat.Ψ (spinDict N)) +
      TPForm (spinDict u.2.2) 0 = _ at h
    simpa only [map_zero, add_zero, leechBV_eq_plusForm] using h)
  refine ⟨v, ?_⟩
  rw [hact, griessNat_coe, hv, map_zero, hdict]

/-- On the other frame half, rationality is exactly rationality of the `Θ` matrix. -/
theorem sigmaBTheta_rational_iff (N : SpaceW)
    (hN : spinDict N ∈ TPframe (Dnat.s + 1)) :
    sigmaBRational (spinBlock N) ↔
      ∃ M : SpaceW, Dnat.Θ (spinDict N) = spinDict M := by
  have hact : sigmaAut (griessNat (spinBlock N) : Vnat) =
      (0, Dnat.Θ (spinDict N)) := by
    rw [sigmaBSpin_nat, sigmaAut_apply, sigNat_Ts1 Dnat hN]
  constructor
  · rintro ⟨v, hv⟩
    rw [hact, griessNat_coe] at hv
    exact ⟨v.2.2, congrArg Prod.snd hv⟩
  · rintro ⟨M, hM⟩
    refine ⟨spinBlock M, ?_⟩
    rw [hact, sigmaBSpin_nat, hM]

/-- The row-half offset fixed by the spin dictionary's normalization. -/
def sigmaBFrameShift : ZMod 2 := spinDict_mem_TPframe_shift.choose

/-- Rational projection onto a row half of the spin matrix. -/
def sigmaBSpinPart (t : ZMod 2) : SpaceW →ₗ[ℚ] SpaceW where
  toFun N j i := if j.1 = t then N j i else 0
  map_add' N M := by
    ext j i
    by_cases h : j.1 = t <;> simp [h]
  map_smul' q N := by
    ext j i
    by_cases h : j.1 = t <;> simp [h]

theorem sigmaBSpinPart_mem (N : SpaceW) (t : ZMod 2) :
    spinDict (sigmaBSpinPart t N) ∈ TPframe (sigmaBFrameShift + t) :=
  spinDict_mem_TPframe_shift.choose_spec _ _ fun _ _ hj => if_neg hj

theorem sigmaBSpinPart_add (N : SpaceW) (t : ZMod 2) :
    sigmaBSpinPart t N + sigmaBSpinPart (t + 1) N = N := by
  ext j i
  change (if j.1 = t then N j i else 0) +
    (if j.1 = t + 1 then N j i else 0) = N j i
  generalize j.1 = s
  fin_cases t <;> fin_cases s
  · exact add_zero _
  · exact zero_add _
  · exact zero_add _
  · exact add_zero _

/-- All four blocks are rational once the forward odd block and `Θ` are rational. -/
theorem sigmaB_rational_of_blocks
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N)
    (hΘ : ∀ N : SpaceW, spinDict N ∈ TPframe (Dnat.s + 1) →
      ∃ M : SpaceW, Dnat.Θ (spinDict N) = spinDict M) :
    ∀ u : SpaceB, ∃ v : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat v := by
  intro u
  have hW (N : SpaceW) : sigmaBRational (spinBlock N) := by
    let t := Dnat.s - sigmaBFrameShift
    have ht : sigmaBFrameShift + t = Dnat.s := add_sub_cancel _ _
    have h0 := sigmaBSpinPart_mem N t
    have h1 := sigmaBSpinPart_mem N (t + 1)
    rw [ht] at h0
    rw [← add_assoc, ht] at h1
    have hr0 := sigmaBTs_rational hΦ _ h0
    have hr1 := (sigmaBTheta_rational_iff _ h1).2 (hΘ _ h1)
    rw [← sigmaBSpinPart_add N t, spinBlock_add]
    exact sigmaBDomain.add_mem hr0 hr1
  rw [eq_untwistedPart_add u]
  exact sigmaBDomain.add_mem
    (sigmaBUntwisted_rational hΦ _ (untwistedPart_snd_snd u)) (hW u.2.2)

/-- The lifting theorem needs only these two remaining coordinate statements. -/
theorem sigmaB_liftable_of_blocks
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N)
    (hΘ : ∀ N : SpaceW, spinDict N ∈ TPframe (Dnat.s + 1) →
      ∃ M : SpaceW, Dnat.Θ (spinDict N) = spinDict M) :
    ∃ g : liftableSubgroup, monsterLift g = sigmaAut :=
  isVnatLiftable_of_rational sigmaAut (sigmaB_rational_of_blocks hΦ hΘ)

/-- The short-vector action on rational spin coordinates. -/
def sigmaBShortAction (c : ShortIdx) : SpaceW →ₗ[ℚ] SpaceW where
  toFun N := (8 : ℚ)⁻¹ • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))
  map_add' N M := by
    simp only [Matrix.mul_add, Matrix.add_mul, smul_add, add_sub_add_comm]
  map_smul' q N := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul,
      RingHom.id_apply]
    module

theorem sigmaBShortAction_gmul (c : ShortIdx) (N : SpaceW) :
    gmul (shortBlock (Pi.single c 1)) (spinBlock N) =
      spinBlock (sigmaBShortAction c N) := by
  classical
  rw [gmul_shortBlock_spinBlock]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl

theorem sigmaBShortAction_dict (c : ShortIdx) (N : SpaceW) :
    spinDict (sigmaBShortAction c N) =
      topAct (shortDict fullShortSign (Pi.single c 1)) (spinDict N) := by
  classical
  rw [topAct_shortDict_spinDict]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl

theorem sigmaBUmat_sq (c : ShortIdx) : Umat c * Umat c = (32 : ℚ) • Umat c := by
  have hnorm : uQ c ⬝ᵥ uQ c = 32 := by
    have h := (uvec_mem_minVecs c).2
    change (∑ i, (uvec c i : ℚ) * (uvec c i : ℚ)) = 32
    change (∑ i, (uvec c i : ℚ) * (uvec c i : ℚ)) / 8 = 4 at h
    linarith
  rw [Umat, vecMulVec_mul_vecMulVec, hnorm, vecMulVec_smul]

theorem sigmaBRmat_sq (c : ShortIdx) : Rmat c * Rmat c = 1 := by
  calc
    Rmat c * Rmat c = (Rmat c)ᵀ * Rmat c := by rw [Rmat_transpose_of_short]
    _ = 1 := qmatR_transpose_mul_self (R := ℚ) 0 c.1.1 c.1.2

/-- The short action is invertible: its oscillator factor has eigenvalues `1` and `-7`. -/
theorem sigmaBShortAction_injective (c : ShortIdx) :
    Function.Injective (sigmaBShortAction c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro N hN
  change (8 : ℚ)⁻¹ • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)) = 0 at hN
  have hK : Rmat c * N = (4 : ℚ)⁻¹ • (Rmat c * N * Umat c) := by
    exact sub_eq_zero.mp ((smul_eq_zero.mp hN).resolve_left (by norm_num))
  have hU := congrArg (fun M : SpaceW => M * Umat c) hK
  dsimp only at hU
  rw [Matrix.smul_mul, Matrix.mul_assoc (Rmat c * N), sigmaBUmat_sq,
    Matrix.mul_smul, smul_smul] at hU
  have hzero : Rmat c * N * Umat c = 0 := by
    ext j i
    have h := congrFun (congrFun hU j) i
    simp only [Matrix.smul_apply, smul_eq_mul] at h
    change _ = (0 : ℚ)
    linarith
  rw [hzero, smul_zero] at hK
  have h := congrArg (fun M : SpaceW => Rmat c * M) hK
  dsimp only at h
  rwa [← Matrix.mul_assoc, sigmaBRmat_sq, Matrix.one_mul, Matrix.mul_zero] at h

theorem sigmaBShortAction_surjective (c : ShortIdx) :
    Function.Surjective (sigmaBShortAction c) :=
  (LinearMap.injective_iff_surjective).1 (sigmaBShortAction_injective c)

/-- Odd short action interchanges the two rational frame halves. -/
theorem sigmaBShortAction_frame (c : ShortIdx) (hc : sigmaBlockParity c = 1)
    (N : SpaceW) (s : ZMod 2) (hN : spinDict N ∈ TPframe s) :
    spinDict (sigmaBShortAction c N) ∈ TPframe (s + 1) := by
  classical
  rw [sigmaBShortAction_dict]
  apply YM_V3_flip (k := -2) _ hN
  apply sigmaBlockShortDict_mem
  intro d hd
  have hdc : d ≠ c := fun h => hd (h ▸ hc)
  simp [hdc]

theorem sigmaBSpin_injective : Function.Injective spinDict := by
  intro N M h
  have hB : spinBlock N = spinBlock M := griessNat_coe_injective (by
    rw [sigmaBSpin_nat, sigmaBSpin_nat, h])
  exact congrArg (fun u : SpaceB => u.2.2) hB

/-- An odd short class exists without a finite enumeration. -/
theorem sigmaBOddIndex_exists : ∃ c : ShortIdx, sigmaBlockParity c = 1 := by
  refine ⟨sigmaBlockRIndex (nvec 0) (mem_halfFourChi (nvec_mem 0)).1, ?_⟩
  apply (sigmaBlockShort_mem_iff _ 1).mp
  rw [← sigmaBlockRIndex_frame]
  exact frameX0_mem_frameSector_one (nvec_not_mem 0)

/-- Products with one odd short class supply the remaining twisted frame half. -/
theorem sigmaBTs1_rational_of_phi
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N)
    (N : SpaceW) (hN : spinDict N ∈ TPframe (Dnat.s + 1)) :
    sigmaBRational (spinBlock N) := by
  classical
  obtain ⟨c, hc⟩ := sigmaBOddIndex_exists
  obtain ⟨M, hM⟩ := sigmaBShortAction_surjective c N
  let t := Dnat.s - sigmaBFrameShift
  have ht : sigmaBFrameShift + t = Dnat.s := add_sub_cancel _ _
  let M0 := sigmaBSpinPart t M
  let M1 := sigmaBSpinPart (t + 1) M
  have h0 : spinDict M0 ∈ TPframe Dnat.s := by
    simpa only [M0, ht] using sigmaBSpinPart_mem M t
  have h1 : spinDict M1 ∈ TPframe (Dnat.s + 1) := by
    simpa only [M1, ← add_assoc, ht] using sigmaBSpinPart_mem M (t + 1)
  have hsum : sigmaBShortAction c M0 + sigmaBShortAction c M1 = N := by
    rw [← map_add, sigmaBSpinPart_add, hM]
  have h10 : spinDict (sigmaBShortAction c M1) ∈ TPframe Dnat.s := by
    have h := sigmaBShortAction_frame c hc M1 (Dnat.s + 1) h1
    simpa only [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero] using h
  have h11 : spinDict (sigmaBShortAction c M1) ∈ TPframe (Dnat.s + 1) := by
    have heq : sigmaBShortAction c M1 = N - sigmaBShortAction c M0 := by
      rw [← hsum]
      abel
    rw [heq, map_sub]
    exact Submodule.sub_mem _ hN (sigmaBShortAction_frame c hc M0 Dnat.s h0)
  have hz : sigmaBShortAction c M1 = 0 := by
    apply sigmaBSpin_injective
    rw [map_zero]
    exact Submodule.disjoint_def.mp (TPframe_isCompl' Dnat.s).disjoint _ h10 h11
  rw [hz, add_zero] at hsum
  have hodd : ∀ d, sigmaBlockParity d ≠ 1 → (Pi.single c 1 : SpaceX) d = 0 := by
    intro d hd
    have hdc : d ≠ c := fun h => hd (h ▸ hc)
    simp [hdc]
  have hr := sigmaBRational_gmul
    ((sigmaBOdd_rational_iff _ hodd).2 (hΦ _ hodd)) (sigmaBTs_rational hΦ M0 h0)
  rwa [sigmaBShortAction_gmul, hsum] at hr

/-- No separate `Θ` computation is required once the forward odd block is rational. -/
theorem sigmaB_rational_of_phi
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N) :
    ∀ u : SpaceB, ∃ v : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat v :=
  sigmaB_rational_of_blocks hΦ fun N hN =>
    (sigmaBTheta_rational_iff N hN).1 (sigmaBTs1_rational_of_phi hΦ N hN)

theorem sigmaB_liftable_of_phi
    (hΦ : ∀ x : SpaceX, (∀ c, sigmaBlockParity c ≠ 1 → x c = 0) →
      ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N) :
    ∃ g : liftableSubgroup, monsterLift g = sigmaAut :=
  isVnatLiftable_of_rational sigmaAut (sigmaB_rational_of_phi hΦ)

theorem sigmaBShort_unit_dict (c : ShortIdx) :
    shortDict fullShortSign (Pi.single c 1) =
      fullShortSign c • frameX0P (shortVec c) := by
  classical
  rw [shortDict_apply, Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    simp [hdc]
  · simp

/-- It suffices to compute the normalized `Φ` images of individual odd short classes. -/
theorem sigmaBPhi_of_columns
    (hcol : ∀ c : ShortIdx, sigmaBlockParity c = 1 → ∃ N : SpaceW,
      fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) = spinDict N)
    (x : SpaceX) (hx : ∀ c, sigmaBlockParity c ≠ 1 → x c = 0) :
    ∃ N : SpaceW, Dnat.Φ (shortDict fullShortSign x) = spinDict N := by
  classical
  apply (sigmaBOdd_rational_iff x hx).1
  rw [sigmaBlockOShort_decompose]
  apply sigmaBDomain.sum_mem
  intro c _
  by_cases hc : sigmaBlockParity c = 1
  · apply sigmaBDomain.smul_mem
    apply (sigmaBOdd_rational_iff (sigmaBlockRUnit c) ?_).2
    · obtain ⟨N, hN⟩ := hcol c hc
      refine ⟨N, ?_⟩
      simpa only [sigmaBlockRUnit, sigmaBShort_unit_dict, map_smul] using hN
    · intro d hd
      have hdc : d ≠ c := fun h => hd (h ▸ hc)
      simp [sigmaBlockRUnit, hdc]
  · rw [hx c hc, zero_smul]
    exact sigmaBDomain.zero_mem

/-- Exact remaining gap: full rationality is equivalent to the odd-column identities. -/
theorem sigmaB_rational_iff_odd_columns :
    (∀ u : SpaceB, ∃ v : SpaceB, sigmaAut (griessNat u : Vnat) = griessNat v) ↔
      (∀ c : ShortIdx, sigmaBlockParity c = 1 → ∃ N : SpaceW,
        fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) = spinDict N) := by
  classical
  constructor
  · intro h c hc
    have hx : ∀ d, sigmaBlockParity d ≠ 1 → (Pi.single c 1 : SpaceX) d = 0 := by
      intro d hd
      have hdc : d ≠ c := fun h => hd (h ▸ hc)
      simp [hdc]
    obtain ⟨N, hN⟩ := (sigmaBOdd_rational_iff _ hx).1 (h (shortBlock (Pi.single c 1)))
    exact ⟨N, by simpa only [sigmaBShort_unit_dict, map_smul] using hN⟩
  · intro hcol
    exact sigmaB_rational_of_phi (sigmaBPhi_of_columns hcol)

theorem sigmaB_liftable_of_odd_columns
    (hcol : ∀ c : ShortIdx, sigmaBlockParity c = 1 → ∃ N : SpaceW,
      fullShortSign c • Dnat.Φ (frameX0P (shortVec c)) = spinDict N) :
    ∃ g : liftableSubgroup, monsterLift g = sigmaAut :=
  isVnatLiftable_of_rational sigmaAut (sigmaB_rational_iff_odd_columns.2 hcol)

end VOA.Moonshine.ConwayNorton.M8
