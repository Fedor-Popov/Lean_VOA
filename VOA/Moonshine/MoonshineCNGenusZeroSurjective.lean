/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroIndex

/-!
# Genus zero on the abstract interface: surjectivity onto `ℙ¹`

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. Let `f = qSeriesFun c` be `J`-dominated with
property P, `Γ₁(M) ≤ G = symmetryGroup f` and `G` commensurable with `SL(2, ℤ)`. Then every
`w ∈ ℂ` is a value of `f` on `ℍ` or the value of `f` at an other cusp
(`surjective_of_gamma1GL_le`). Proof: the set `V` of such `w` is

* **open**: at a value `f τ` by the open mapping theorem in `ℍ`; at a cusp value by the open
  mapping theorem for the cusp function at `0` (`nhds_le_map_cuspFunction_of_other`), whose
  values at `q ≠ 0` are values of `f`;
* **closed**: `V = closure (range f)`. Every cusp value is a limit of values of `f`. Conversely
  if `w ∉ V`, then `f` stays at distance `≥ ε` from `w`: every `τ` is equivalent to `ρ σ` with
  `σ ∈ 𝒟` and `ρ` one of finitely many coset representatives; near the cusp `ρ ∞` the function
  `f ∘ ρ` stays away from `w` (`exists_im_bound_norm_sub_ge`), and on the compact truncated
  fundamental domain `|f ∘ ρ - w|` has a positive minimum;
* nonempty; so `V = ℂ` (`ℂ` is connected).

Also: the other cusps of `G` are the `ρ ∞`, `ρ ∈ SL(2, ℤ)`, not equivalent to `∞`
(`exists_SL2Z_of_isOtherCusp`, `isOtherCusp_smul_infty`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold Real Modular

variable {c : ℕ → ℂ}

/-! ### Other cusps -/

/-- `δ ∞` is an other cusp of `G` if `δ T^h δ⁻¹ ∈ G` (`h ≠ 0`) and no element of `G` maps `∞`
to it. -/
theorem isOtherCusp_smul_infty {G : Subgroup (GL (Fin 2) ℝ)} {δ : GL (Fin 2) ℝ} {h : ℝ}
    (hh : h ≠ 0) (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ G)
    (hother : ∀ γ ∈ G, (γ * δ) 1 0 ≠ 0) : IsOtherCusp G (δ • cuspInfty) := by
  have hT10 : glUpperUnipotent h 1 0 = 0 := by simp [glUpperUnipotent]
  have hTpar : (glUpperUnipotent h).IsParabolic := by
    rw [GeneralLinearGroup.IsParabolic, Matrix.isParabolic_iff_of_upperTriangular hT10]
    simp [glUpperUnipotent, hh]
  refine ⟨⟨_, hpar, (GeneralLinearGroup.isParabolic_conj_iff _ _).mpr hTpar, ?_⟩, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, OnePoint.smul_infty_eq_self_iff.mpr hT10]
  · intro γ hγ heq
    apply hother γ⁻¹ (G.inv_mem hγ)
    apply OnePoint.smul_infty_eq_self_iff.mp
    rw [mul_smul, ← heq, inv_smul_smul]

/-- The other cusps of a group commensurable with `SL(2, ℤ)` are the `ρ ∞`, `ρ ∈ SL(2, ℤ)`, with
`(γ ρ) ∞ ≠ ∞` for all `γ ∈ G`. -/
theorem exists_SL2Z_of_isOtherCusp {G : Subgroup (GL (Fin 2) ℝ)}
    (hcomm : Subgroup.Commensurable G 𝒮ℒ) {cc : OnePoint ℝ} (hcc : IsOtherCusp G cc) :
    ∃ ρ : SL(2, ℤ), cc = mapGL ℝ ρ • cuspInfty ∧ ∀ γ ∈ G, (γ * mapGL ℝ ρ) 1 0 ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := isCusp_SL2Z_iff'.mp (hcomm.isCusp_iff.mp hcc.1)
  refine ⟨ρ, hρ, fun γ hγ h0 => ?_⟩
  have h1 : (γ * mapGL ℝ ρ) • cuspInfty = cuspInfty := OnePoint.smul_infty_eq_self_iff.mpr h0
  apply hcc.2 γ⁻¹ (G.inv_mem hγ)
  calc γ⁻¹ • cuspInfty = γ⁻¹ • ((γ * mapGL ℝ ρ) • cuspInfty) := by rw [h1]
    _ = mapGL ℝ ρ • cuspInfty := by rw [← mul_smul, inv_mul_cancel_left]
    _ = cc := hρ.symm

/-! ### Open mapping at an other cusp -/

/-- **Open mapping of the cusp function** at an other cusp with value `w`. -/
theorem nhds_le_map_cuspFunction_of_other (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c))
    (hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) {w : ℂ}
    (hw : Tendsto (fun τ : ℍ => qSeriesFun c (δ • τ)) atImInfty (𝓝 w)) :
    𝓝 w ≤ map (cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ))) (𝓝 0) ∧
      cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) 0 = w := by
  obtain ⟨hA, hlim, hq⟩ := cuspData_of_other hc hP hδ hh hpar hother
  set Ψ := cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) with hΨ
  have hΨ0 : Ψ 0 = w := tendsto_nhds_unique hlim hw
  have hnc : ¬ ∀ᶠ q in 𝓝 (0 : ℂ), Ψ q = Ψ 0 := by
    intro hev
    have h1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Ψ q = Ψ 0 := hev.filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ∈ Metric.ball (0 : ℂ) 1 :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    have h3 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ≠ 0 := self_mem_nhdsWithin
    obtain ⟨q, hqc, hq1, hq0⟩ := (h1.and (h2.and h3)).exists
    rw [Metric.mem_ball, dist_zero_right] at hq1
    obtain ⟨τ, -, hτ⟩ := hq q hq0 hq1
    exact qSeriesFun_ne_of_tendsto_comp_smul hc hP hδ hh hpar hother hw (δ • τ)
      (by rw [← hτ, hqc, hΨ0])
  refine ⟨?_, hΨ0⟩
  rw [← hΨ0]
  exact hA.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc

/-! ### Surjectivity -/

/-- **Surjectivity of the induced map `X(G) → ℙ¹`**. -/
theorem surjective_of_gamma1GL_le (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {M : ℕ} (hM : 0 < M) (hΓ1 : gamma1GL M ≤ symmetryGroup (qSeriesFun c))
    (hcomm : Subgroup.Commensurable (symmetryGroup (qSeriesFun c)) 𝒮ℒ) (w : ℂ) :
    (∃ τ : ℍ, qSeriesFun c τ = w) ∨
      ∃ cc, IsOtherCusp (symmetryGroup (qSeriesFun c)) cc ∧ HasCuspValue (qSeriesFun c) cc w := by
  set G := symmetryGroup (qSeriesFun c) with hG
  set V : Set ℂ := {w | (∃ τ : ℍ, qSeriesFun c τ = w) ∨
    ∃ cc, IsOtherCusp G cc ∧ HasCuspValue (qSeriesFun c) cc w} with hV
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hcusp : ∀ cc w, IsOtherCusp G cc → HasCuspValue (qSeriesFun c) cc w →
      ∃ ρ : SL(2, ℤ), (∀ γ ∈ G, (γ * mapGL ℝ ρ) 1 0 ≠ 0) ∧
        Tendsto (fun τ : ℍ => qSeriesFun c (mapGL ℝ ρ • τ)) atImInfty (𝓝 w) := by
    intro cc w hcc hw
    obtain ⟨ρ, hρ, hother⟩ := exists_SL2Z_of_isOtherCusp hcomm hcc
    exact ⟨ρ, hother, hw _ ⟨by rw [det_val_mapGL]; exact one_pos, hρ.symm⟩⟩
  -- `V` is open
  have hopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro w (⟨τ, rfl⟩ | ⟨cc, hcc, hw⟩)
    · have hgA := (differentiableOn_qSeriesExt hc).analyticOnNhd isOpen_upperHalfPlaneSet
      have hτ0 : 0 < (τ : ℂ).im := τ.im_pos
      have hop : 𝓝 (qSeriesExt c τ) ≤ map (qSeriesExt c) (𝓝 (τ : ℂ)) :=
        (hgA τ hτ0).eventually_constant_or_nhds_le_map_nhds.resolve_left
          (not_eventually_eq_qSeriesExt hc hτ0)
      rw [← qSeriesExt_coe]
      refine mem_of_superset (hop (image_mem_map (isOpen_upperHalfPlaneSet.mem_nhds hτ0))) ?_
      rintro _ ⟨z, hz, rfl⟩
      exact Or.inl ⟨⟨z, hz⟩, (qSeriesExt_of_im_pos c hz).symm⟩
    · obtain ⟨ρ, hother, hlim⟩ := hcusp cc w hcc hw
      have hpar := conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ
      obtain ⟨hop, hΨ0⟩ :=
        nhds_le_map_cuspFunction_of_other hc hP (det_val_mapGL ρ) hMR hpar hother hlim
      refine mem_of_superset (hop (image_mem_map univ_mem)) ?_
      rintro _ ⟨q, -, rfl⟩
      by_cases hq : q = 0
      · subst hq
        rw [hΨ0]
        exact Or.inr ⟨cc, hcc, hw⟩
      · refine Or.inl ⟨mapGL ℝ ρ • ofComplex (Function.Periodic.invQParam M q), ?_⟩
        rw [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]
        rfl
  -- `V = closure (range f)`
  have hsub1 : V ⊆ closure (range (qSeriesFun c)) := by
    rintro w (⟨τ, rfl⟩ | ⟨cc, hcc, hw⟩)
    · exact subset_closure ⟨τ, rfl⟩
    · obtain ⟨ρ, -, hlim⟩ := hcusp cc w hcc hw
      exact mem_closure_of_tendsto hlim (Eventually.of_forall fun τ => ⟨_, rfl⟩)
  have hsub2 : closure (range (qSeriesFun c)) ⊆ V := by
    intro w hw
    by_contra hwV
    have hne : ∀ τ : ℍ, qSeriesFun c τ ≠ w := fun τ h => hwV (Or.inl ⟨τ, h⟩)
    haveI : NeZero M := ⟨hM.ne'⟩
    haveI := finiteIndex_comap_of_gamma1GL_le hΓ1
    have hper : ∀ r : SL(2, ℤ) ⧸ G.comap (mapGL ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ σ ∈ 𝒟,
        ε ≤ ‖qSeriesFun c (mapGL ℝ (Quotient.out r)⁻¹ • σ) - w‖ := by
      intro r
      set ρ := (Quotient.out r)⁻¹
      have hpar := conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ
      obtain ⟨Y, ε₁, hε₁, hY⟩ := exists_im_bound_norm_sub_ge hc hP (det_val_mapGL ρ) hMR hpar
        (v := w) fun hother w' hw' => by
          intro hww'
          apply hwV
          refine Or.inr ⟨_, isOtherCusp_smul_infty hMR.ne' hpar hother, ?_⟩
          rw [hww']
          exact hasCuspValue_of_tendsto_comp_smul hw'
      have hK := ModularGroup.isCompact_truncatedFundamentalDomain Y
      have hcont : ContinuousOn (fun σ : ℍ => ‖qSeriesFun c (mapGL ℝ ρ • σ) - w‖)
          (ModularGroup.truncatedFundamentalDomain Y) := by
        have h1 : Continuous (fun σ : ℍ => qSeriesFun c (mapGL ℝ ρ • σ)) :=
          ((mdifferentiable_qSeriesFun hc).comp
            (mdifferentiable_smul (by rw [det_val_mapGL]; exact one_pos))).continuous
        exact ((h1.sub continuous_const).norm).continuousOn
      by_cases hKne : (ModularGroup.truncatedFundamentalDomain Y).Nonempty
      · obtain ⟨σ₀, -, hmin⟩ := hK.exists_isMinOn hKne hcont
        have hε₂ : 0 < ‖qSeriesFun c (mapGL ℝ ρ • σ₀) - w‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr (hne _))
        refine ⟨min ε₁ _, lt_min hε₁ hε₂, fun σ hσ => ?_⟩
        by_cases hσY : Y ≤ σ.im
        · exact (min_le_left _ _).trans (hY σ hσY)
        · exact (min_le_right _ _).trans (hmin ⟨hσ, (not_le.mp hσY).le⟩)
      · refine ⟨ε₁, hε₁, fun σ hσ => ?_⟩
        by_cases hσY : Y ≤ σ.im
        · exact hY σ hσY
        · exact absurd ⟨σ, hσ, (not_le.mp hσY).le⟩ hKne
    choose ε hε hεσ using hper
    obtain ⟨r₀, hr₀⟩ := Finite.exists_min ε
    rw [Metric.mem_closure_iff] at hw
    obtain ⟨_, ⟨τ, rfl⟩, hdist⟩ := hw (ε r₀) (hε r₀)
    obtain ⟨r, g, hgG, σ, hσ, hgσ⟩ := exists_smul_eq_smul_fd G τ
    have h1 := hεσ r σ hσ
    rw [← hgσ, hgG.2] at h1
    rw [dist_comm, dist_eq_norm] at hdist
    linarith [hr₀ r]
  have hclosed : IsClosed V := by
    rw [show V = closure (range (qSeriesFun c)) from Subset.antisymm hsub1 hsub2]
    exact isClosed_closure
  have hVne : V.Nonempty := ⟨_, Or.inl ⟨UpperHalfPlane.I, rfl⟩⟩
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ hVne
  have hwV : w ∈ V := by rw [huniv]; exact mem_univ w
  exact hwV

end VOA.Moonshine.ConwayNorton
