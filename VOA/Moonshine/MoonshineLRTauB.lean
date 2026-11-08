import VOA.Moonshine.MoonshineLRSigmaB2
import VOA.Moonshine.MoonshineLRMonsterVisible
import VOA.Moonshine.MonsterGriess.TrialityFourGroup

/-!
# Lifting rational triality from the frame involution

The frame involution is the conjugate of parity by the lifted VOA triality.
Assuming `tauB ∈ AutO`, parity extensionality identifies it with `yB` or `zB`
from the matrix and spin blocks. Its visible-centralizer coset then lifts `tauB`.
The final theorem retains only `tauB ∈ AutO` and `Generated.Gmat = AutO`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.Code
open VOA.Moonshine.MonsterGriess.Parity VOA.Moonshine.MonsterGriess.Visible
open VOA.Moonshine.SigmaAssemble VOA.Moonshine.TrialityTw VOA.Moonshine.VnatBlock

/-- The rational lift of the already constructed VOA triality involution. -/
def tauBLiftSigma : liftableSubgroup := sigmaBOdd_liftable.choose

theorem tauBLiftSigma_spec : monsterLift tauBLiftSigma = sigmaAut :=
  sigmaBOdd_liftable.choose_spec

theorem tauBLiftSigma_apply (u : SpaceB) :
    sigmaAut (griessNat u : Vnat) =
      griessNat (((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u) := by
  rw [← tauBLiftSigma_spec, monsterLift_apply_griessNat]

theorem tauBLiftSigma_inv : tauBLiftSigma⁻¹ = tauBLiftSigma := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  change ((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)
    (((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u) = u
  apply griessNat_coe_injective
  rw [← tauBLiftSigma_apply, ← tauBLiftSigma_apply]
  exact sigmaBInvol _

/-- Conjugation is formed inside `AutO`. -/
def tauBLiftConjugate : AutO :=
  (tauBLiftSigma : AutO) * ⟨xB, xB_mem_AutO⟩ * (tauBLiftSigma : AutO)⁻¹

theorem tauBLiftParity_dict (u : SpaceB) :
    sigmaBlockZ (griessNat u : Vnat) = griessNat (xB u) := by
  rw [griessNat_coe, xB_apply, griessNat_coe]
  change (untwistedDict fullShortSign u, -spinDict u.2.2) = _
  rw [map_neg]
  rfl

/-- The conjugate acts on the full dictionary by the four frame-sector signs. -/
theorem tauBLiftConjugate_dict (u : SpaceB) :
    (griessNat ((tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) u) : Vnat) =
      sigmaBlockFrameSign Dnat.s (griessNat u : Vnat) := by
  have hinv : (tauBLiftSigma : AutO)⁻¹ = (tauBLiftSigma : AutO) :=
    congrArg Subtype.val tauBLiftSigma_inv
  change (griessNat ((((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) * xB *
    ((tauBLiftSigma : AutO)⁻¹ : AutO)) u) : Vnat) = _
  rw [hinv]
  simp only [LinearEquiv.mul_apply]
  rw [← tauBLiftSigma_apply, ← tauBLiftParity_dict, ← tauBLiftSigma_apply]
  exact sigmaBlockAut_conjugate _

/-- The row half whose dictionary image has positive frame sign. -/
def tauBLiftRow : ZMod 2 := Dnat.s - sigmaBFrameShift

theorem tauBLiftRow_sector : sigmaBFrameShift + tauBLiftRow = Dnat.s := by
  unfold tauBLiftRow
  abel

/-- The conjugate fixes every symmetric-matrix state. -/
theorem tauBLiftConjugate_A (A : symMat) :
    (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) (inA A) = inA A := by
  apply griessNat_coe_injective
  rw [tauBLiftConjugate_dict]
  rw [griessNat_coe]
  change sigmaBlockFrameSign Dnat.s
    (untwistedDict fullShortSign (symBlock A), spinDict 0) = _
  change sigmaBlockFrameSign Dnat.s
    (untwistedDict fullShortSign (symBlock A), spinDict 0) =
      (untwistedDict fullShortSign (symBlock A), spinDict 0)
  rw [untwistedDict_symBlock]
  have hf : plusFrame (matDict A) = matDict A := by
    have h := mem_frameSector'.mp (V0Sub_carrier ▸ sigmaBlockMat_mem A)
    simpa only [Extraspecial.sgn_zero, one_smul] using h
  simp only [map_zero, sigmaBlockFrameSign, blockOp_apply, LinearMap.zero_apply,
    add_zero, hf]

/-- On either spin row half the frame sign is constant. -/
theorem tauBLiftConjugate_W (N : SpaceW) (t : ZMod 2)
    (hN : ∀ j i, j.1 ≠ t → N j i = 0) :
    (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) (spinBlock N) =
      if t = tauBLiftRow then spinBlock N else -spinBlock N := by
  have hm := spinDict_mem_TPframe_shift.choose_spec N t hN
  apply griessNat_coe_injective
  rw [tauBLiftConjugate_dict, sigmaBSpin_nat]
  by_cases ht : t = tauBLiftRow
  · subst t
    change spinDict N ∈ TPframe (sigmaBFrameShift + tauBLiftRow) at hm
    rw [tauBLiftRow_sector] at hm
    rw [if_pos rfl, sigmaBSpin_nat]
    simp only [sigmaBlockFrameSign, blockOp_apply, map_zero, LinearMap.zero_apply,
      zero_add, LinearMap.sub_apply, Submodule.projection_apply_left _ ⟨_, hm⟩,
      Submodule.projection_apply_of_mem_right _ hm, sub_zero]
  · have he : t = tauBLiftRow + 1 := by
      generalize tauBLiftRow = r at *
      fin_cases t <;> fin_cases r <;> first | exact rfl | exact (ht rfl).elim
    change spinDict N ∈ TPframe (sigmaBFrameShift + t) at hm
    rw [he, ← add_assoc, tauBLiftRow_sector] at hm
    rw [if_neg ht, map_neg, Submodule.coe_neg, sigmaBSpin_nat]
    simp only [sigmaBlockFrameSign, blockOp_apply, map_zero, LinearMap.zero_apply,
      zero_add, LinearMap.sub_apply, Submodule.projection_apply_left _ ⟨_, hm⟩,
      Submodule.projection_apply_of_mem_right _ hm, zero_sub, Prod.neg_mk, neg_zero]

/-- Frame signs commute with the untwisted/twisted parity operator. -/
theorem tauBLiftConjugate_parity :
    IsParityAut (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) := by
  refine ⟨tauBLiftConjugate.property.1, tauBLiftConjugate.property.2, fun u => ?_⟩
  apply griessNat_coe_injective
  rw [tauBLiftConjugate_dict, ← tauBLiftParity_dict, ← tauBLiftParity_dict,
    tauBLiftConjugate_dict]
  simp only [sigmaBlockFrameSign, sigmaBlockZ, blockOp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.zero_apply, map_neg, neg_zero, add_zero, zero_add]

/-- Agreement on the matrix and signed spin triality columns determines parity maps. -/
theorem tauBLiftParity_ext {f g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hf : IsParityAut f) (hg : IsParityAut g)
    (hA : ∀ A, f (inA A) = g (inA A))
    (hW : ∀ (c : C₀) (i : Fin 24) (k : Fin 3), k ≠ 0 →
      f (tbasis (.inr (.inr (.inl (c, i, k))))) =
        g (tbasis (.inr (.inr (.inl (c, i, k)))))) : f = g := by
  apply liftVisParity_ext hf hg
  · exact LinearMap.ext fun A => congrArg Prod.fst (hA A)
  · apply (Matrix.stdBasis ℚ SpinIdx (Fin 24)).ext
    rintro ⟨⟨t, c⟩, i⟩
    rw [Matrix.stdBasis_eq_single]
    have he : Matrix.single (t, c) i (1 : ℚ) =
        tensor (Spin.E t c) (Pi.single i 1) :=
      Matrix.single_eq_single_vecMulVec_single _ _
    rw [he, resW_apply, resW_apply]
    have ht : t = 0 ∨ t = 1 := by
      fin_cases t
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ht with rfl | rfl
    · have h := hW c i 2 (by decide)
      rw [tbasis_odd_two] at h
      have hs : (MonsterGriess.sgn (P ((c : Code.C) : Fin 24 → ZMod 2)) : ℚ) ≠ 0 := sgnR_ne_zero _
      have hsm (q : ℚ) (N : SpaceW) :
          ((0, 0, q • N) : SpaceB) = q • inW N := by simp [inW]
      rw [hsm, map_smul, map_smul] at h
      exact congrArg (fun u : SpaceB => u.2.2) ((smul_right_inj hs).mp h)
    · have h := hW c i 1 (by decide)
      rw [tbasis_odd_one] at h
      have hs : (MonsterGriess.sgn (((c : Code.C) : Fin 24 → ZMod 2) i) : ℚ) ≠ 0 := sgnR_ne_zero _
      have hsm (q : ℚ) (N : SpaceW) :
          ((0, 0, q • N) : SpaceB) = q • inW N := by simp [inW]
      rw [hsm, map_smul, map_smul] at h
      exact congrArg (fun u : SpaceB => u.2.2) ((smul_right_inj hs).mp h)

/-- Triality's two parity conjugates fix all symmetric matrices. -/
theorem tauBLiftTriality_A (g : SpaceB ≃ₗ[ℚ] SpaceB) (s : Fin 3 → ℚ)
    (hg : ∀ t, g (tbasis t) = oddSign s t • tbasis t) (A : symMat) :
    g (inA A) = inA A := by
  have h : g.toLinearMap.comp (LinearMap.inl ℚ symMat (SpaceX × SpaceW)) =
      LinearMap.inl ℚ symMat (SpaceX × SpaceW) := by
    apply basisA.ext
    intro z
    induction z using Sym2.ind with
    | h i j =>
      rcases lt_trichotomy i j with hij | rfl | hji
      · simpa [oddSign, tbasis_pair_zero] using
          hg (.inr (.inl (⟨(i, j), hij⟩, 0)))
      · simpa [oddSign, tbasis_diag] using hg (.inl i)
      · rw [Sym2.eq_swap]
        simpa [oddSign, tbasis_pair_zero] using
          hg (.inr (.inl (⟨(j, i), hji⟩, 0)))
  exact LinearMap.congr_fun h A

/-- The frame sign on a signed elementary spin column. -/
theorem tauBLiftConjugate_column (q : ℚ) (t : ZMod 2) (c : C₀) (i : Fin 24) :
    (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB)
        (0, 0, q • tensor (Spin.E t c) (Pi.single i 1)) =
      (if t = tauBLiftRow then (1 : ℚ) else -1) •
        ((0, 0, q • tensor (Spin.E t c) (Pi.single i 1)) : SpaceB) := by
  have hN : ∀ j k, j.1 ≠ t →
      (q • tensor (Spin.E t c) (Pi.single i 1)) j k = 0 := by
    intro j k hj
    have hne : j ≠ (t, c) := fun h => hj (congrArg Prod.fst h)
    simp [tensor, Spin.E, Matrix.vecMulVec_apply, Pi.single_apply, hne]
  have h := tauBLiftConjugate_W _ t hN
  by_cases ht : t = tauBLiftRow
  · simpa only [ht, if_true, spinBlock, one_smul] using h
  · simpa only [if_neg ht, spinBlock, neg_one_smul] using h

/-- The triality eigenvalue description identifies the conjugate using only `A` and `W`. -/
theorem tauBLiftConjugate_eq_of_signs (g : SpaceB ≃ₗ[ℚ] SpaceB) (s : Fin 3 → ℚ)
    (hg : IsParityAut g) (heig : ∀ t, g (tbasis t) = oddSign s t • tbasis t)
    (h1 : s 1 = if (1 : ZMod 2) = tauBLiftRow then 1 else -1)
    (h2 : s 2 = if (0 : ZMod 2) = tauBLiftRow then 1 else -1) :
    (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) = g := by
  apply tauBLiftParity_ext tauBLiftConjugate_parity hg
  · intro A
    rw [tauBLiftConjugate_A, tauBLiftTriality_A g s heig]
  · intro c i k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases hk' with rfl | rfl | rfl
    · exact (hk rfl).elim
    · rw [heig, oddSign_odd, h1, tbasis_odd_one]
      exact tauBLiftConjugate_column _ _ _ _
    · rw [heig, oddSign_odd, h2, tbasis_odd_two]
      exact tauBLiftConjugate_column _ _ _ _

/-- A commuting orthogonal algebra automorphism is a parity automorphism. -/
theorem tauBLiftParity_of_commute (g : AutO)
    (h : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xB = xB * (g : SpaceB ≃ₗ[ℚ] SpaceB)) :
    IsParityAut (g : SpaceB ≃ₗ[ℚ] SpaceB) :=
  ⟨g.property.1, g.property.2, fun u => LinearEquiv.congr_fun h u⟩

/-- Assuming triality preserves the product, its parity conjugates match the frame sign. -/
theorem tauBLiftSigma_conj_xB (hτ : tauB ∈ AutO) :
    (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) = yB ∨
      (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB) = zB := by
  have hy : yB ∈ AutO :=
    AutO.mul_mem (AutO.mul_mem hτ xB_mem_AutO) (AutO.inv_mem hτ)
  have hz : zB ∈ AutO :=
    AutO.mul_mem (AutO.mul_mem (AutO.pow_mem hτ 2) xB_mem_AutO)
      (AutO.inv_mem (AutO.pow_mem hτ 2))
  have hpy := tauBLiftParity_of_commute ⟨yB, hy⟩
    (yB_mul_xB.trans xB_mul_yB.symm)
  have hpz := tauBLiftParity_of_commute ⟨zB, hz⟩
    (zB_mul_xB.trans xB_mul_zB.symm)
  have ht : tauBLiftRow = 0 ∨ tauBLiftRow = 1 := by
    generalize tauBLiftRow = t
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ht with ht | ht
  · right
    exact tauBLiftConjugate_eq_of_signs zB sgnZ hpz zB_tbasis
      (by simp [ht, sgnZ]) (by simp [ht, sgnZ])
  · left
    exact tauBLiftConjugate_eq_of_signs yB sgnY hpy yB_tbasis
      (by simp [ht, sgnY]) (by simp [ht, sgnY])

/-- Equal parity conjugates differ by a visible element, so liftability transfers. -/
theorem tauBLift_of_conjugate (g : AutO)
    (hg : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xB * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
      (tauBLiftConjugate : SpaceB ≃ₗ[ℚ] SpaceB)) : IsVnatLiftable g := by
  let r : AutO := (tauBLiftSigma : AutO)⁻¹ * g
  have hc : (r : SpaceB ≃ₗ[ℚ] SpaceB) * xB * (r : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = xB := by
    change (((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
      (g : SpaceB ≃ₗ[ℚ] SpaceB)) * xB *
        (((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (g : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ = xB
    rw [mul_inv_rev, inv_inv]
    have h := congrArg (fun a : SpaceB ≃ₗ[ℚ] SpaceB =>
      ((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * a *
        ((tauBLiftSigma : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) hg
    simpa only [tauBLiftConjugate, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  have hr : (r : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
    rw [← AutO_inf_centralizer_xB_eq_Gvis, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨r.property, mul_inv_eq_iff_eq_mul.mp hc⟩
  have hl := (mem_liftableSubgroup.mp tauBLiftSigma.property).mul (liftVisRGvis r hr)
  simpa only [r, mul_inv_cancel_left] using hl

/-- Rational triality lifts whenever it is an orthogonal Griess automorphism. -/
theorem tauBLift_isVnatLiftable_tauB_of_mem_AutO (hτ : tauB ∈ AutO) :
    IsVnatLiftable ⟨tauB, hτ⟩ := by
  rcases tauBLiftSigma_conj_xB hτ with hy | hz
  · exact tauBLift_of_conjugate ⟨tauB, hτ⟩ (conj_tauB_xB.trans hy.symm)
  · have hpow : tauB⁻¹ = tauB ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', tauB_pow_three]
    have hconj : tauB⁻¹ * xB * (tauB⁻¹)⁻¹ = zB := by rw [hpow]; rfl
    have h := tauBLift_of_conjugate (⟨tauB, hτ⟩ : AutO)⁻¹ (hconj.trans hz.symm)
    simpa only [inv_inv] using h.inv

/-- Ambient generation transports to generation inside `AutO`. -/
theorem tauBLift_closure_eq_top (hτ : tauB ∈ AutO) (hGmat : Generated.Gmat = AutO) :
    Subgroup.closure (insert (⟨tauB, hτ⟩ : AutO) visibleSetAutO) = ⊤ := by
  apply Subgroup.map_injective AutO.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  have himage : AutO.subtype '' insert (⟨tauB, hτ⟩ : AutO) visibleSetAutO =
      insert tauB (Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
    rw [Set.image_insert_eq]
    congr 1
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hg
      exact ⟨⟨g, Gvis_le_AutO hg⟩, hg, rfl⟩
  rw [himage, ← Generated.Gmat_eq_closure_insert, hGmat]

/-- Conway–Norton for every `AutO` element assuming `τ_B ∈ AutO` and `Gmat = AutO`. -/
theorem tauBLift_conwayNorton_autO_of_Gmat (hτ : tauB ∈ AutO)
    (hGmat : Generated.Gmat = AutO) (g : AutO) :
    ∃ h : AutVnat, vnatWeightTwoRestrict h = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
        IsNormalizedHauptmodul Γ (mckayThompsonFun h) :=
  conwayNorton_autO_of_tauB (tauBLift_isVnatLiftable_tauB_of_mem_AutO hτ)
    (tauBLift_closure_eq_top hτ hGmat) g

end VOA.Moonshine.ConwayNorton.M8
