/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringPhysical

/-! # The abstract no-ghost decompositions at arbitrary weight

This completes the subspace and nondegeneracy assertions of the abstract no-ghost theorem in
every weight: `H = P ⊕ S_K` with `dim S = dim S_K`, the splitting of `S_K` along `S` and `K`,
`K = T ⊕ (K ⊓ S_K)` with `K ⊓ S_K` the radical, and nondegeneracy of the form on `T`.
Together with `StringPhysical`, it proves the weight-one physical splitting `P¹ = T¹ ⊕ N¹` at
central charge 26. The only additional hypothesis throughout is the explicit light-cone
splitting (`LightConeSplit`).
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

theorem eq_zero_of_weightComponents (x : H) (hx : ∀ N, M.weightComponent N x = 0) : x = 0 := by
  apply (DirectSum.decomposeLinearEquiv M.wt).injective
  ext N
  change M.weightComponent N x = M.weightComponent N 0
  rw [hx, map_zero]

/-- The dimension identity `dim S^N = dim S_K^N`. -/
theorem spurious_kSpurious_finrank (hF : M.LightConeSplit) (N : ℤ) :
    Module.finrank ℂ (M.weightSlice M.spurious N) =
      Module.finrank ℂ (M.weightSlice M.kSpurious N) := by
  letI := M.wt_finite N
  have h := Submodule.finrank_add_eq_of_isCompl (M.lightConeSplit_weight hF N)
  have h' := M.kVacuum_kSpurious_finrank N
  omega

theorem physical_disjoint_kSpurious_weight (hF : M.LightConeSplit) (N : ℤ) :
    Disjoint (M.weightSlice M.physical N) (M.weightSlice M.kSpurious N) := by
  rw [Submodule.disjoint_def]
  intro x hp hj
  apply Subtype.ext
  apply M.B_nondeg N x x.property
  intro y hy
  obtain ⟨s, hs, k, hk, hsw, hkw, he⟩ := M.lightConeSplit_decompose_weight hF N y hy
  rw [← he, map_add, M.physical_pair_spurious x s hp hs]
  rw [M.B_symm.eq x k, M.kVacuum_pair_kSpurious k x hk hj, add_zero]

/-- The finite-weight complementary decomposition `H^N = P^N ⊕ S_K^N`. -/
theorem physical_kSpurious_isCompl_weight (hF : M.LightConeSplit) (N : ℤ) :
    IsCompl (M.weightSlice M.physical N) (M.weightSlice M.kSpurious N) := by
  letI := M.wt_finite N
  have h := M.physical_spurious_finrank N
  rw [M.spurious_kSpurious_finrank hF N] at h
  exact (Submodule.isCompl_iff_disjoint _ _ (by omega)).mpr
    (M.physical_disjoint_kSpurious_weight hF N)

theorem physical_disjoint_kSpurious (hF : M.LightConeSplit) :
    Disjoint M.physical M.kSpurious := by
  rw [Submodule.disjoint_def]
  intro x hp hj
  apply M.eq_zero_of_weightComponents x
  intro N
  have h := Submodule.disjoint_def.mp (M.physical_disjoint_kSpurious_weight hF N)
    ⟨M.weightComponent N x, M.weightComponent_mem N x⟩
    (M.physical_weightComponent N x hp) (M.kSpurious_weightComponent N x hj)
  exact congrArg Subtype.val h

/-- The global complementary decomposition `H = P ⊕ S_K`. -/
theorem physical_kSpurious_isCompl (hF : M.LightConeSplit) :
    IsCompl M.physical M.kSpurious := by
  refine ⟨M.physical_disjoint_kSpurious hF, codisjoint_iff.mpr ?_⟩
  apply top_unique
  rw [← M.wt_isInternal.submodule_iSup_eq_top]
  apply iSup_le
  intro N x hx
  have h := (M.physical_kSpurious_isCompl_weight hF N).sup_eq_top
  obtain ⟨p, hp, j, hj, he⟩ := Submodule.mem_sup.mp
    (show (⟨x, hx⟩ : M.wt N) ∈ M.weightSlice M.physical N ⊔ M.weightSlice M.kSpurious N by
      rw [h]; trivial)
  exact Submodule.mem_sup.mpr ⟨p, hp, j, hj, congrArg Subtype.val he⟩

theorem weightSlice_sup_of_homogeneous (U W : Submodule ℂ H)
    (hU : ∀ N x, x ∈ U → M.weightComponent N x ∈ U)
    (hW : ∀ N x, x ∈ W → M.weightComponent N x ∈ W) (N : ℤ) :
    M.weightSlice (U ⊔ W) N = M.weightSlice U N ⊔ M.weightSlice W N := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, w, hw, he⟩ := Submodule.mem_sup.mp hx
    refine Submodule.mem_sup.mpr
      ⟨⟨M.weightComponent N u, M.weightComponent_mem N u⟩, hU N u hu,
        ⟨M.weightComponent N w, M.weightComponent_mem N w⟩, hW N w hw, ?_⟩
    apply Subtype.ext
    change M.weightComponent N u + M.weightComponent N w = (x : H)
    change u + w = (x : H) at he
    have h := congrArg (M.weightComponent N) he
    simpa only [map_add, M.weightComponent_of_mem N x x.property] using h
  · apply sup_le
    · intro x hx
      exact (show U ≤ U ⊔ W from le_sup_left) hx
    · intro x hx
      exact (show W ≤ U ⊔ W from le_sup_right) hx

/-- The splitting `S_K = (S_K ⊓ S) ⊕ (S_K ⊓ K)`, equality and directness, in every weight. -/
theorem kSpurious_weight_split (hF : M.LightConeSplit) (N : ℤ) :
    M.weightSlice M.kSpurious N =
      (M.weightSlice M.kSpurious N ⊓ M.weightSlice M.spurious N) ⊔
        (M.weightSlice M.kSpurious N ⊓ M.weightSlice M.kVacuum N) ∧
    Disjoint (M.weightSlice M.kSpurious N ⊓ M.weightSlice M.spurious N)
      (M.weightSlice M.kSpurious N ⊓ M.weightSlice M.kVacuum N) := by
  constructor
  · conv_lhs => rw [M.kSpurious_eq_intersections_sup hF]
    exact M.weightSlice_sup_of_homogeneous (M.kSpurious ⊓ M.spurious) (M.kSpurious ⊓ M.kVacuum)
      (fun Q x hx => ⟨M.kSpurious_weightComponent Q x hx.1, M.spurious_weightComponent Q x hx.2⟩)
      (fun Q x hx => ⟨M.kSpurious_weightComponent Q x hx.1, M.kVacuum_weightComponent Q x hx.2⟩) N
  · exact (M.lightConeSplit_weight hF N).disjoint.mono inf_le_right inf_le_right

theorem orthogonal_sup_eq_inf (N : ℤ) (U W : Submodule ℂ (M.wt N)) :
    (M.stringWeightForm N).orthogonal (U ⊔ W) =
      (M.stringWeightForm N).orthogonal U ⊓ (M.stringWeightForm N).orthogonal W := by
  ext x
  constructor
  · intro hx
    exact ⟨fun y hy => hx y (Submodule.mem_sup_left hy),
      fun y hy => hx y (Submodule.mem_sup_right hy)⟩
  · rintro ⟨hu, hw⟩ y hy
    obtain ⟨u, hu', w, hw', rfl⟩ := Submodule.mem_sup.mp hy
    change M.stringWeightForm N (u + w) x = 0
    rw [map_add, LinearMap.add_apply, hu u hu', hw w hw', add_zero]

theorem transverse_radical_disjoint (hF : M.LightConeSplit) (N : ℤ) :
    Disjoint (M.weightSlice M.transverse N) (M.formRadicalIn M.kVacuum N) := by
  rw [M.kVacuum_radical_eq N]
  exact (M.physical_disjoint_kSpurious_weight hF N).mono (fun _ h => h.1) (fun _ h => h.2)

/-- The longitudinal space is transverse plus its form radical. -/
theorem kVacuum_eq_transverse_sup_radical (hF : M.LightConeSplit) (N : ℤ) :
    M.weightSlice M.kVacuum N =
      M.weightSlice M.transverse N ⊔ M.formRadicalIn M.kVacuum N := by
  letI := M.wt_finite N
  let S := M.weightSlice M.spurious N
  let J := M.weightSlice M.kSpurious N
  let K := M.weightSlice M.kVacuum N
  let T := M.weightSlice M.transverse N
  let R := M.formRadicalIn M.kVacuum N
  have hR : R = K ⊓ J := M.kVacuum_radical_eq N
  have hJ : J = (J ⊓ S) ⊔ (J ⊓ K) := (M.kSpurious_weight_split hF N).1
  have hsums : S ⊔ J = S ⊔ R := by
    rw [hR]
    apply le_antisymm
    · apply sup_le le_sup_left
      intro x hx
      rw [hJ] at hx
      obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr ⟨a, ha.2, b, ⟨hb.2, hb.1⟩, he⟩
    · exact sup_le le_sup_left (le_trans inf_le_right le_sup_right)
  have horth : (M.stringWeightForm N).orthogonal (S ⊔ R) = T := by
    rw [← hsums, M.orthogonal_sup_eq_inf]
    rw [show (M.stringWeightForm N).orthogonal S = M.weightSlice M.physical N from
      M.orthogonal_spurious_eq N, show (M.stringWeightForm N).orthogonal J = K from
      M.orthogonal_kSpurious_eq N]
    rfl
  have hSR : Disjoint S R := (M.lightConeSplit_weight hF N).disjoint.mono_right
    (by rw [hR]; exact inf_le_left)
  have hdSR := Submodule.finrank_sup_add_finrank_inf_eq S R
  rw [hSR.eq_bot, finrank_bot, add_zero] at hdSR
  have hdT := (M.stringWeightForm N).finrank_add_finrank_orthogonal
    (M.stringWeightForm_symm N).isRefl (S ⊔ R)
  rw [horth, (M.stringWeightForm N).orthogonal_top_eq_bot (M.stringWeightForm_nondegenerate N),
    inf_bot_eq, finrank_bot, add_zero] at hdT
  have hdK := Submodule.finrank_add_eq_of_isCompl (M.lightConeSplit_weight hF N)
  have hdTR := Submodule.finrank_sup_add_finrank_inf_eq T R
  rw [(M.transverse_radical_disjoint hF N).eq_bot, finrank_bot, add_zero] at hdTR
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le (fun _ h => h.2) (by rw [M.kVacuum_radical_eq N]; exact fun _ h => h.1)
  · change Module.finrank ℂ ↥(T ⊔ R) = Module.finrank ℂ K
    change Module.finrank ℂ S + Module.finrank ℂ K = Module.finrank ℂ (M.wt N) at hdK
    omega

/-- The form on each transverse weight space is nondegenerate. -/
theorem transverse_nondegenerate (hF : M.LightConeSplit) (N : ℤ) (x : H)
    (hx : x ∈ M.transverse) (hw : x ∈ M.wt N)
    (hB : ∀ y ∈ M.transverse, y ∈ M.wt N → M.B x y = 0) : x = 0 := by
  have hr : (⟨x, hw⟩ : M.wt N) ∈ M.formRadicalIn M.kVacuum N := by
    rw [M.mem_formRadicalIn_iff]
    refine ⟨hx.2, ?_⟩
    intro y hy
    have hym : y ∈ M.weightSlice M.kVacuum N := hy
    rw [M.kVacuum_eq_transverse_sup_radical hF N] at hym
    obtain ⟨t, ht, r, hr, he⟩ := Submodule.mem_sup.mp hym
    have hrj : (r : H) ∈ M.kSpurious := by
      rw [M.kVacuum_radical_eq N] at hr
      exact hr.2
    have he' : (t : H) + (r : H) = y := congrArg Subtype.val he
    rw [← he', map_add, hB t ht t.property, M.kVacuum_pair_kSpurious x r hx.2 hrj, add_zero]
  exact congrArg Subtype.val (Submodule.disjoint_def.mp (M.transverse_radical_disjoint hF N)
    ⟨x, hw⟩ hx hr)

end VOA.Moonshine.ConwayNorton.StringModule
