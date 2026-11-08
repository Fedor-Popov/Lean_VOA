/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroCusps

/-!
# Genus zero on the abstract interface: commensurability with `SL(2, ℤ)`

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`. Let `f = qSeriesFun c` be `J`-dominated, with
property P, and let `Γ₁(M) ≤ G = symmetryGroup f` (`M > 0`). Then `G` is commensurable with
`SL(2, ℤ)` (`commensurable_symmetryGroup_of_gamma1GL_le`).

* `[SL(2, ℤ) : G ∩ SL(2, ℤ)] < ∞` because `Γ₁(M) ≤ G ∩ SL(2, ℤ)`.
* `[G : G ∩ SL(2, ℤ)] < ∞` ("counting a fibre in a fundamental domain"): for `γ ∈ G` move `γ i`
  into the standard fundamental domain by `g ∈ SL(2, ℤ)` and write `g` as a coset representative
  `ρ⁻¹` of `SL(2, ℤ) / (G ∩ SL(2, ℤ))` (finitely many) times an element of `G ∩ SL(2, ℤ)`. The
  resulting `κ ∈ G` maps `i` to `ρ σ` with `σ ∈ 𝒟` and `f (ρ σ) = f (i)`. Near the cusp `ρ ∞` the
  function `f ∘ ρ` stays away from `f (i)` (it tends to a cusp value that is not attained, or to
  `∞`), so `σ` lies in a truncated fundamental domain, a compact set; hence the entries of `κ`
  are bounded, and by Shimura's finiteness lemma only finitely many `κ` occur.

The fundamental-domain reduction (`exists_smul_eq_smul_fd`) and the estimate near a rational
cusp (`exists_im_bound_norm_sub_ge`) are reused for surjectivity (`MoonshineCNGenusZeroSurjective`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold Real Modular

variable {c : ℕ → ℂ}

/-! ### Parabolic elements at rational cusps -/

lemma upperSL_natCast_mem_Gamma (M : ℕ) : upperSL M ∈ Gamma M := by
  rw [Gamma_mem]; simp [upperSL]

lemma Gamma_le_Gamma1_of (M : ℕ) : Gamma M ≤ Gamma1 M := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

lemma mapGL_upperSL_natCast (M : ℕ) : mapGL ℝ (upperSL M) = glUpperUnipotent M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSL, glUpperUnipotent]

/-- If `Γ₁(M) ≤ G`, every rational cusp `ρ ∞` carries the parabolic `ρ T^M ρ⁻¹ ∈ G`. -/
theorem conj_glUpperUnipotent_mem_of_gamma1GL_le {G : Subgroup (GL (Fin 2) ℝ)} {M : ℕ}
    (hΓ1 : gamma1GL M ≤ G) (ρ : SL(2, ℤ)) :
    mapGL ℝ ρ * glUpperUnipotent (M : ℝ) * (mapGL ℝ ρ)⁻¹ ∈ G := by
  have hmem : ρ * upperSL M * ρ⁻¹ ∈ Gamma M :=
    (Gamma_normal M).conj_mem _ (upperSL_natCast_mem_Gamma M) ρ
  have h1 := hΓ1 ⟨_, Gamma_le_Gamma1_of M hmem, rfl⟩
  rwa [map_mul, map_mul, map_inv, mapGL_upperSL_natCast] at h1

lemma det_val_mapGL (ρ : SL(2, ℤ)) : (mapGL ℝ ρ).det.val = 1 := by
  rw [det_mapGL, Units.val_one]

/-! ### Away from the value near a rational cusp -/

/-- **Near a cusp `δ ∞`, `f ∘ δ` stays away from `v`**, unless `δ ∞` is an other cusp whose value
is `v`: either `δ ∞` is equivalent to `∞` (then `|f ∘ δ| → ∞`) or it is an other cusp whose value
differs from `v`. -/
theorem exists_im_bound_norm_sub_ge (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {δ : GL (Fin 2) ℝ} (hδ : δ.det.val = 1) {h : ℝ} (hh : 0 < h)
    (hpar : δ * glUpperUnipotent h * δ⁻¹ ∈ symmetryGroup (qSeriesFun c)) {v : ℂ}
    (hv : (∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0) →
      ∀ w, Tendsto (fun τ : ℍ => qSeriesFun c (δ • τ)) atImInfty (𝓝 w) → v ≠ w) :
    ∃ Y ε : ℝ, 0 < ε ∧ ∀ σ : ℍ, Y ≤ σ.im → ε ≤ ‖qSeriesFun c (δ • σ) - v‖ := by
  by_cases hother : ∀ γ ∈ symmetryGroup (qSeriesFun c), (γ * δ) 1 0 ≠ 0
  · obtain ⟨-, hlim, -⟩ := cuspData_of_other hc hP hδ hh hpar hother
    set w := cuspFunction h (fun τ : ℍ => qSeriesFun c (δ • τ)) 0
    have hvw : v ≠ w := hv hother w hlim
    have hε : 0 < ‖v - w‖ / 2 := by
      have : 0 < ‖v - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw)
      linarith
    obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp (hlim.eventually (Metric.ball_mem_nhds w hε))
    refine ⟨Y, _, hε, fun σ hσ => ?_⟩
    have h1 : ‖qSeriesFun c (δ • σ) - w‖ < ‖v - w‖ / 2 := by
      have h3 : qSeriesFun c (δ • σ) ∈ Metric.ball w (‖v - w‖ / 2) := hY σ hσ
      rw [Metric.mem_ball, dist_eq_norm] at h3
      exact h3
    have h2 := norm_sub_le_norm_sub_add_norm_sub v (qSeriesFun c (δ • σ)) w
    rw [norm_sub_rev v (qSeriesFun c (δ • σ))] at h2
    linarith
  · push Not at hother
    obtain ⟨γ, hγ, h0⟩ := hother
    have hlim := (tendsto_norm_qSeriesFun_atImInfty hc).comp (tendsto_smul_atImInfty h0)
    obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp (hlim.eventually (eventually_ge_atTop (‖v‖ + 1)))
    refine ⟨Y, 1, one_pos, fun σ hσ => ?_⟩
    have h1 : ‖v‖ + 1 ≤ ‖qSeriesFun c (δ • σ)‖ := by
      have h3 : ‖v‖ + 1 ≤ ‖qSeriesFun c ((γ * δ) • σ)‖ := hY σ hσ
      rwa [mul_smul, hγ.2] at h3
    have h2 := norm_sub_norm_le (qSeriesFun c (δ • σ)) v
    linarith

/-! ### The fundamental-domain reduction -/

/-- **Fundamental-domain reduction.** For a subgroup `G` and `τ ∈ ℍ`, there are a coset
`r ∈ SL(2, ℤ) / (G ∩ SL(2, ℤ))`, an element `g` of `G ∩ SL(2, ℤ)` and `σ ∈ 𝒟` with
`g τ = ρ_r σ`, where `ρ_r = (out r)⁻¹`. -/
theorem exists_smul_eq_smul_fd (G : Subgroup (GL (Fin 2) ℝ)) (τ : ℍ) :
    ∃ r : SL(2, ℤ) ⧸ G.comap (mapGL ℝ), ∃ g : SL(2, ℤ), mapGL ℝ g ∈ G ∧
      ∃ σ ∈ 𝒟, mapGL ℝ g • τ = mapGL ℝ (Quotient.out r)⁻¹ • σ := by
  obtain ⟨g₀, hg₀⟩ := ModularGroup.exists_smul_mem_fd τ
  obtain ⟨h₀, hout⟩ := QuotientGroup.mk_out_eq_mul (G.comap (mapGL ℝ)) g₀
  refine ⟨(g₀ : SL(2, ℤ) ⧸ G.comap (mapGL ℝ)), (h₀ : SL(2, ℤ))⁻¹, ?_, g₀ • τ, hg₀, ?_⟩
  · rw [map_inv]; exact G.inv_mem (Subgroup.mem_comap.mp h₀.2)
  · rw [hout, show g₀ • τ = mapGL ℝ g₀ • τ from rfl, ← mul_smul, ← map_mul, _root_.mul_inv_rev,
      inv_mul_cancel_right]

lemma finiteIndex_comap_of_gamma1GL_le {G : Subgroup (GL (Fin 2) ℝ)} {M : ℕ} [NeZero M]
    (hΓ1 : gamma1GL M ≤ G) : (G.comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)).FiniteIndex :=
  Subgroup.finiteIndex_of_le (H := Gamma1 M) fun γ hγ =>
    Subgroup.mem_comap.mpr (hΓ1 ⟨γ, hγ, rfl⟩)

/-! ### Compactness -/

/-- On a compact set, `Im (g σ)` is bounded below by a positive constant and `|g σ|` above. -/
lemma exists_im_ge_norm_le_of_isCompact {K : Set ℍ} (hK : IsCompact K) {g : GL (Fin 2) ℝ}
    (hg : 0 < g.det.val) :
    ∃ m R : ℝ, 0 < m ∧ ∀ σ ∈ K, m ≤ (g • σ).im ∧ ‖((g • σ : ℍ) : ℂ)‖ ≤ R := by
  have hcont : Continuous (fun σ : ℍ => g • σ) := (mdifferentiable_smul hg).continuous
  have hK' : IsCompact ((fun σ : ℍ => g • σ) '' K) := hK.image hcont
  obtain ⟨R, hR⟩ := hK'.exists_bound_of_continuousOn
    (f := fun σ : ℍ => (σ : ℂ)) UpperHalfPlane.continuous_coe.continuousOn
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK'.exists_isMinOn (hne.image _)
      (f := fun σ : ℍ => σ.im) UpperHalfPlane.continuous_im.continuousOn
    refine ⟨x.im, R, x.im_pos, fun σ hσ => ⟨hmin (mem_image_of_mem _ hσ), hR _
      (mem_image_of_mem _ hσ)⟩⟩
  · refine ⟨1, R, one_pos, fun σ hσ => absurd ⟨σ, hσ⟩ hne⟩

/-! ### Commensurability -/

/-- **Commensurability with `SL(2, ℤ)`**. -/
theorem commensurable_symmetryGroup_of_gamma1GL_le (hc : IsJDominated c)
    (hP : ∀ z w : ℍ, qSeriesFun c z = qSeriesFun c w →
      ∃ γ ∈ symmetryGroup (qSeriesFun c), γ • z = w)
    {M : ℕ} (hM : 0 < M) (hΓ1 : gamma1GL M ≤ symmetryGroup (qSeriesFun c)) :
    Subgroup.Commensurable (symmetryGroup (qSeriesFun c)) 𝒮ℒ := by
  haveI : NeZero M := ⟨hM.ne'⟩
  set G := symmetryGroup (qSeriesFun c) with hG
  haveI := finiteIndex_comap_of_gamma1GL_le hΓ1
  refine ⟨fun h0 => (Subgroup.IsArithmetic.is_commensurable (𝒢 := gamma1GL M)).1
    (Subgroup.relIndex_eq_zero_of_le_left hΓ1 h0), ?_⟩
  -- per coset representative, a bound for the elements `κ ∈ G` with `κ i = ρ σ`, `σ ∈ 𝒟`
  have hper : ∀ r : SL(2, ℤ) ⧸ G.comap (mapGL ℝ), ∃ B : ℝ, ∀ κ ∈ G, ∀ σ ∈ 𝒟,
      κ • UpperHalfPlane.I = mapGL ℝ (Quotient.out r)⁻¹ • σ → ∀ i j, |κ i j| ≤ B := by
    intro r
    set ρ := (Quotient.out r)⁻¹
    have hpar := conj_glUpperUnipotent_mem_of_gamma1GL_le hΓ1 ρ
    have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
    obtain ⟨Y, ε, hε, hYε⟩ := exists_im_bound_norm_sub_ge hc hP (det_val_mapGL ρ) hMR hpar
      (v := qSeriesFun c UpperHalfPlane.I) fun hother w hw =>
        qSeriesFun_ne_of_tendsto_comp_smul hc hP (det_val_mapGL ρ) hMR hpar hother hw _
    obtain ⟨m, R, hm, hmR⟩ := exists_im_ge_norm_le_of_isCompact
      (ModularGroup.isCompact_truncatedFundamentalDomain Y)
      (g := mapGL ℝ ρ) (by rw [det_val_mapGL]; exact one_pos)
    obtain ⟨B, hB⟩ := exists_bound_entries_of_smul_eq (Y := min m 1) (R := max R 1)
      (lt_min hm one_pos)
    refine ⟨B, fun κ hκ σ hσ hκσ => ?_⟩
    have hσY : σ.im < Y := by
      by_contra hge
      have h1 := hYε σ (not_lt.mp hge)
      rw [← hκσ, hκ.2, sub_self, norm_zero] at h1
      linarith
    have hσK : σ ∈ ModularGroup.truncatedFundamentalDomain Y := ⟨hσ, hσY.le⟩
    obtain ⟨hmσ, hRσ⟩ := hmR σ hσK
    obtain ⟨b1, b2, b3, b4⟩ := hB κ (det_val_eq_one_of_mem_symmetryGroup hκ) _ _ hκσ
      (by rw [UpperHalfPlane.I_im]; exact min_le_right _ _) (le_trans (min_le_left _ _) hmσ)
      (by rw [UpperHalfPlane.coe_I, Complex.norm_I]; exact le_max_right _ _)
      (hRσ.trans (le_max_left _ _))
    intro i j
    fin_cases i <;> fin_cases j
    · exact b1
    · exact b2
    · exact b3
    · exact b4
  choose B hB using hper
  obtain ⟨r₀, hr₀⟩ := Finite.exists_max B
  set S := {g : GL (Fin 2) ℝ | g ∈ G ∧ ∀ i j, |g i j| ≤ B r₀} with hS
  have hSfin : S.Finite := finite_bounded_mem_symmetryGroup hc (B r₀)
  haveI : Finite S := hSfin.to_subtype
  rw [Subgroup.relIndex]
  refine Subgroup.index_ne_zero_of_finite (hH := ?_)
  refine Finite.of_surjective (fun s : S => (QuotientGroup.mk
    (⟨(s : GL (Fin 2) ℝ)⁻¹, G.inv_mem s.2.1⟩ : G) : G ⧸ (𝒮ℒ).subgroupOf G)) ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨r, g, hgG, σ, hσ, hgσ⟩ := exists_smul_eq_smul_fd G ((x : GL (Fin 2) ℝ)⁻¹ •
    UpperHalfPlane.I)
  set κ := mapGL ℝ g * (x : GL (Fin 2) ℝ)⁻¹ with hκ
  have hκG : κ ∈ G := G.mul_mem hgG (G.inv_mem x.2)
  have hκσ : κ • UpperHalfPlane.I = mapGL ℝ (Quotient.out r)⁻¹ • σ := by
    rw [hκ, mul_smul, hgσ]
  refine ⟨⟨κ, hκG, fun i j => (hB r κ hκG σ hσ hκσ i j).trans (hr₀ r)⟩, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine ⟨g, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hκ]
  group

end VOA.Moonshine.ConwayNorton
