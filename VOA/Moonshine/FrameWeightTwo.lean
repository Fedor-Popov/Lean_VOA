/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameSectors

/-!
# Weight two of the Golay-frame sectors `V₀⁺`, `V₃⁺`  (Moonshine step M8e)

`(V_Λ⁺)₂` is spanned by the `300` quadratic states `h_a(-1)h_b(-1)𝟙` and the `98280` states
`e^α + e^{-α}` (`α` in a half `S = halfFour` of the norm-`4` vectors; `PlusWeightTwo.lean`).
The first kind, and `e^α + e^{-α}` with `α ∈ Λ₀`, lie in `V₀⁺`; `e^α + e^{-α}` with `α ∉ Λ₀`
lies in `V₃⁺`.  Hence

* `finrank_frameSector_zero_grading_two : dim (V₀⁺)₂ = 300 + #{α ∈ S | β α = 0}`;
* `finrank_frameSector_one_grading_two : dim (V₃⁺)₂ = #{α ∈ S | β α = 1}`;
* `two_mul_card_halfFourChi_one : 2·#{α ∈ S | β α = 1} = #{α | ⟨α,α⟩ = 4, β α = 1}`.

The remaining input for the expected values `49428` and `49152` is the lattice count
`#{α ∈ Λ \ Λ₀ | ⟨α,α⟩ = 4} = 98304 = 24·2¹²` (the vectors `(∓3, ±1²³)` of `u + 2A`, one for
each position of the `3` and each Golay codeword); it is proved in `FrameCount.lean`
(`card_normFour_frameChar_one`), which also states the final values.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open LatGen IntegralLattice Module HeisenbergN

/-- `S_i = {α ∈ S | β α = i}`, `S = halfFour` the chosen half of the norm-`4` vectors. -/
noncomputable def halfFourChi (i : ZMod 2) : Finset leech.carrier :=
  (halfFour leech leech_posDef).filter fun α => frameChar α = i

theorem card_halfFourChi_add :
    (halfFourChi 0).card + (halfFourChi 1).card = 98280 := by
  rw [← leech_halfFour_card, halfFourChi, halfFourChi,
    ← Finset.card_filter_add_card_filter_not (s := halfFour leech leech_posDef)
      (fun α => frameChar α = 0)]
  congr 2
  ext α
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h, h1⟩; exact ⟨h, by rw [h1]; decide⟩
  · rintro ⟨h, h1⟩
    refine ⟨h, ?_⟩
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (frameChar α) with h' | h'
    · exact absurd h' h1
    · exact h'

/-- `2·#S₁ = #{α | ⟨α,α⟩ = 4, β α = 1}`. -/
theorem two_mul_card_halfFourChi_one :
    2 * (halfFourChi 1).card
      = ((normFour leech leech_posDef).filter fun α => frameChar α = 1).card := by
  classical
  rw [normFour_eq_union leech leech_posDef, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (disjoint_halfFour_neg leech leech_posDef)),
    Finset.filter_image, Finset.card_image_of_injective _ neg_injective, two_mul]
  congr 2
  ext α
  simp only [map_neg, ZMod.neg_eq_self_mod_two]
  rfl

/-- `⨁_{α ∈ S_i} ℂ e^α`. -/
noncomputable def chargeHalfChi (i : ZMod 2) : Submodule ℂ (LatModuleGen leech) :=
  ⨆ α ∈ halfFourChi i, bigradα leech (0, α)

theorem chargeHalfChi_le (i : ZMod 2) : chargeHalfChi i ≤ chargeHalf leech leech_posDef :=
  biSup_mono fun _ hα => (Finset.mem_filter.mp hα).1

theorem chiLat_of_mem_chargeHalfChi (i : ZMod 2) {y : LatModuleGen leech}
    (hy : y ∈ chargeHalfChi i) :
    chiLat leech frameChar y = Extraspecial.sgn i • y := by
  have hle : chargeHalfChi i ≤ Module.End.eigenspace (chiLat leech frameChar).toLinearMap
      (Extraspecial.sgn i) := by
    refine iSup₂_le fun α hα z hz => ?_
    obtain ⟨p, _, rfl⟩ := hz
    rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe, chiLat_mkEα, chiSign,
      (Finset.mem_filter.mp hα).2]
  have := hle hy
  rwa [Module.End.mem_eigenspace_iff] at this

/-- `x ↦ x + θx`. -/
noncomputable def fPlus : LatModuleGen leech →ₗ[ℂ] LatModuleGen leech :=
  LinearMap.id + (1 : ℂ) • (thetaLat leech).toLinearMap

theorem fPlus_apply (y : LatModuleGen leech) : fPlus y = y + thetaLat leech y := by
  rw [fPlus, LinearMap.add_apply, LinearMap.smul_apply, one_smul]; rfl

theorem finrank_map_fPlus (i : ZMod 2) :
    finrank ℂ ↥((chargeHalfChi i).map fPlus) = (halfFourChi i).card := by
  unfold fPlus
  rw [finrank_map_of_injOn _ _
      (fun x hx h0 => injOn_chargeHalf leech leech_posDef 1 x (chargeHalfChi_le i hx) h0),
    chargeHalfChi, finrank_biSup_bigradα_zero]

/-- The `g = (-1)^i` part of `(V_Λ⁺)₂`, inside `V_Λ`. -/
noncomputable def plusTwoChi (i : ZMod 2) : Submodule ℂ (LatModuleGen leech) :=
  plusTwo leech ⊓ Module.End.eigenspace (chiLat leech frameChar).toLinearMap (Extraspecial.sgn i)

theorem mem_plusTwoChi {i : ZMod 2} {x : LatModuleGen leech} :
    x ∈ plusTwoChi i ↔ x ∈ plusTwo leech ∧ chiLat leech frameChar x = Extraspecial.sgn i • x := by
  rw [plusTwoChi, Submodule.mem_inf, Module.End.mem_eigenspace_iff]; rfl

theorem fPlus_mem_plusTwoChi (i : ZMod 2) {y : LatModuleGen leech} (hy : y ∈ chargeHalfChi i) :
    fPlus y ∈ plusTwoChi i := by
  refine mem_plusTwoChi.mpr ⟨(mem_plusTwo leech).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [gradingLatGen_two_of_rootless leech leech_even leech_posDef leech_no_roots, fPlus_apply]
    refine Submodule.mem_sup_right (Submodule.add_mem _ ?_ ?_)
    · exact chargeHalf_le leech leech_posDef (chargeHalfChi_le i hy)
    · exact chargeHalfNeg_le leech leech_posDef
        (thetaLat_mem_chargeHalfNeg leech leech_posDef (chargeHalfChi_le i hy))
  · rw [fPlus_apply, map_add, thetaLat_thetaLat, add_comm]
  · rw [fPlus_apply, map_add, chiLat_thetaLat, chiLat_of_mem_chargeHalfChi i hy, map_smul,
      smul_add]

theorem quad_mem_plusTwoChi_zero {p : FockN (rank leech)} (hp : p ∈ quadFock (rank leech)) :
    mkEα leech 0 p ∈ plusTwoChi 0 := by
  refine mem_plusTwoChi.mpr ⟨(mem_plusTwo leech).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [gradingLatGen_two_of_rootless leech leech_even leech_posDef leech_no_roots]
    refine Submodule.mem_sup_left ⟨p, ?_, rfl⟩
    rw [gradingZN_of_nonneg (by norm_num)]
    exact quadFock_le _ hp
  · rw [mkEα_apply, thetaLat_tmul, sigmaN_of_mem_quadFock _ hp, neg_zero]
  · rw [chiLat_mkEα, chiSign_zero, Extraspecial.sgn_zero]

theorem disjoint_plusTwoChi : Disjoint (plusTwoChi 0) (plusTwoChi 1) := by
  rw [Submodule.disjoint_def]
  intro x h0 h1
  have e0 := (mem_plusTwoChi.mp h0).2
  have e1 := (mem_plusTwoChi.mp h1).2
  rw [Extraspecial.sgn_zero, one_smul] at e0
  rw [Extraspecial.sgn_one, neg_one_smul, e0] at e1
  have h3 : (2 : ℂ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [e1]; exact neg_add_cancel x
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

/-- **`dim` of the two sectors of `(V_Λ⁺)₂`, inside `V_Λ`.** -/
theorem finrank_plusTwoChi :
    finrank ℂ (plusTwoChi 0) = 300 + (halfFourChi 0).card ∧
      finrank ℂ (plusTwoChi 1) = (halfFourChi 1).card := by
  haveI : FiniteDimensional ℂ (gradingLatGen leech 2) :=
    gradingLatGen_finrank_of_posDef leech leech_even leech_posDef 2
  haveI : FiniteDimensional ℂ (plusTwo leech) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : ∀ i, FiniteDimensional ℂ (plusTwoChi i) := fun i =>
    Submodule.finiteDimensional_of_le inf_le_left
  haveI := gradingWN_finiteDimensional (rank leech) 2
  haveI : FiniteDimensional ℂ (quadFock (rank leech)) :=
    Submodule.finiteDimensional_of_le (quadFock_le _)
  haveI : ∀ i, FiniteDimensional ℂ (chargeHalfChi i) := fun i =>
    (finrank_biSup_of_iSupIndep _ (iSupIndep_bigradα_zero leech) _).1
  -- lower bound for `i = 0`
  have hle0 : (quadFock (rank leech)).map (mkEα leech 0) ⊔ (chargeHalfChi 0).map fPlus
      ≤ plusTwoChi 0 := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩; exact quad_mem_plusTwoChi_zero hp
    · rintro _ ⟨y, hy, rfl⟩; exact fPlus_mem_plusTwoChi 0 hy
  have hle1 : (chargeHalfChi 1).map fPlus ≤ plusTwoChi 1 := by
    rintro _ ⟨y, hy, rfl⟩; exact fPlus_mem_plusTwoChi 1 hy
  have hdisj : Disjoint ((quadFock (rank leech)).map (mkEα leech 0)) ((chargeHalfChi 0).map fPlus) := by
    refine (disjoint_bigradα_chargeFour leech leech_posDef).mono ?_ ?_
    · rw [bigradα]; refine Submodule.map_mono ?_
      rw [gradingZN_of_nonneg (by norm_num)]; exact quadFock_le _
    · rintro _ ⟨y, hy, rfl⟩
      rw [fPlus_apply]
      exact Submodule.add_mem _ (chargeHalf_le leech leech_posDef (chargeHalfChi_le 0 hy))
        (chargeHalfNeg_le leech leech_posDef
          (thetaLat_mem_chargeHalfNeg leech leech_posDef (chargeHalfChi_le 0 hy)))
  have hquad : finrank ℂ ↥((quadFock (rank leech)).map (mkEα leech 0)) = 300 := by
    rw [← (Submodule.equivMapOfInjective _ (mkEα_injective leech 0) _).finrank_eq,
      finrank_quadFock, leech_rank]
    rfl
  have h0 := Submodule.finrank_mono hle0
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    ((quadFock (rank leech)).map (mkEα leech 0)) ((chargeHalfChi 0).map fPlus)
  rw [hdisj.eq_bot, finrank_bot, add_zero, hquad, finrank_map_fPlus] at hs
  rw [hs] at h0
  have h1 := Submodule.finrank_mono hle1
  rw [finrank_map_fPlus] at h1
  -- upper bound
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (plusTwoChi 0) (plusTwoChi 1)
  rw [disjoint_plusTwoChi.eq_bot, finrank_bot, add_zero] at h3
  have h4 : finrank ℂ ↥(plusTwoChi 0 ⊔ plusTwoChi 1) ≤ finrank ℂ (plusTwo leech) :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have hr : (rank leech + 1).choose 2 = 300 := by rw [leech_rank]; rfl
  rw [finrank_plusTwo leech leech_posDef leech_even leech_no_roots, hr,
    leech_halfFour_card] at h4
  have h5 := card_halfFourChi_add
  have h6 : (24 + 1).choose 2 = 300 := rfl
  constructor <;> omega

/-- The weight-`2` part of the frame sector `i`, transported into `V_Λ`. -/
noncomputable def frameSectorTwoEquiv (i : ZMod 2) :
    ↥((frameSector i).comap (leechVOAPlus.grading 2).subtype) ≃ₗ[ℂ] plusTwoChi i := by
  refine (Submodule.equivMapOfInjective
    ((orbifold (Subgroup.zpowers leechTheta)).carrier.subtype.comp (leechVOAPlus.grading 2).subtype)
    ((Submodule.injective_subtype _).comp (Submodule.injective_subtype _)) _).trans
    (LinearEquiv.ofEq _ _ ?_)
  ext x
  constructor
  · rintro ⟨⟨⟨y, hyP⟩, hy2⟩, hyS, rfl⟩
    refine mem_plusTwoChi.mpr ⟨(mem_plusTwo leech).mpr ⟨hy2, (mem_leechVOAPlus_iff y).mp hyP⟩, ?_⟩
    exact mem_frameSector.mp hyS
  · intro hx
    obtain ⟨hxP, hxS⟩ := mem_plusTwoChi.mp hx
    obtain ⟨hx2, hxθ⟩ := (mem_plusTwo leech).mp hxP
    have hxP' : x ∈ (orbifold (Subgroup.zpowers leechTheta)).carrier :=
      (mem_leechVOAPlus_iff x).mpr hxθ
    exact ⟨⟨⟨x, hxP'⟩, hx2⟩, mem_frameSector.mpr hxS, rfl⟩

/-- **`dim (V₀⁺)₂ = 300 + #{α ∈ S | β α = 0}`.** -/
theorem finrank_frameSector_zero_grading_two :
    finrank ℂ ↥((frameSector 0).comap (leechVOAPlus.grading 2).subtype)
      = 300 + (halfFourChi 0).card := by
  rw [(frameSectorTwoEquiv 0).finrank_eq, finrank_plusTwoChi.1]

/-- **`dim (V₃⁺)₂ = #{α ∈ S | β α = 1} = ½ #{α ∈ Λ \ Λ₀ | ⟨α,α⟩ = 4}`.** -/
theorem finrank_frameSector_one_grading_two :
    finrank ℂ ↥((frameSector 1).comap (leechVOAPlus.grading 2).subtype)
      = (halfFourChi 1).card := by
  rw [(frameSectorTwoEquiv 1).finrank_eq, finrank_plusTwoChi.2]

end VOA.Moonshine
