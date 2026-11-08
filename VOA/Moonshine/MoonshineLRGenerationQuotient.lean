import VOA.Moonshine.MoonshineLRGenerationPreData

/-!
# Graded quotients and forms pairing opposite degrees

* `form_decompose_eq`: if a bilinear form pairs degree `γ` only with degree `−γ`, then
  `B (x_γ) y = B x (y_{−γ})`.
* `isInternal_map_mkQ`: the quotient of an internally graded module by a submodule stable under
  the homogeneous projections is internally graded by the images.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

section Form

variable (W : ℤ × ℤ → Submodule ℂ M) [DirectSum.Decomposition W]

/-- **Forms pairing opposite degrees:** `B (x_γ) y = B x (y_{−γ})`. -/
theorem form_decompose_eq (B : LinearMap.BilinForm ℂ M)
    (hB : ∀ γ δ, γ + δ ≠ 0 → ∀ x ∈ W γ, ∀ y ∈ W δ, B x y = 0) (x y : M) (γ : ℤ × ℤ) :
    B (DirectSum.decompose W x γ) y = B x (DirectSum.decompose W y (-γ)) := by
  classical
  have hy := DirectSum.sum_support_decompose W y
  have hx := DirectSum.sum_support_decompose W x
  have h1 : B (DirectSum.decompose W x γ) y =
      B (DirectSum.decompose W x γ) (DirectSum.decompose W y (-γ)) := by
    conv_lhs => rw [← hy]
    rw [map_sum]
    refine Finset.sum_eq_single (-γ) (fun δ _ hδ => ?_) (fun hδ => ?_)
    · exact hB γ δ (fun h => hδ (eq_neg_of_add_eq_zero_right h)) _ (Submodule.coe_mem _) _
        (Submodule.coe_mem _)
    · rw [DFinsupp.notMem_support_iff.mp hδ, Submodule.coe_zero, map_zero]
  have h2 : B x (DirectSum.decompose W y (-γ)) =
      B (DirectSum.decompose W x γ) (DirectSum.decompose W y (-γ)) := by
    conv_lhs => rw [← hx]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_single γ (fun ε _ hε => ?_) (fun hγ => ?_)
    · refine hB ε (-γ) (fun h => hε ?_) _ (Submodule.coe_mem _) _ (Submodule.coe_mem _)
      rw [← sub_eq_add_neg, sub_eq_zero] at h
      exact h
    · rw [DFinsupp.notMem_support_iff.mp hγ, Submodule.coe_zero, map_zero, LinearMap.zero_apply]
  rw [h1, h2]

end Form

section Quotient

variable {ι : Type*} [DecidableEq ι] (W : ι → Submodule ℂ M) [DirectSum.Decomposition W]

/-- The homogeneous projections kill elements of the other degrees. -/
theorem decompose_eq_zero_of_mem_iSup_ne {i : ι} {b : M}
    (hb : b ∈ ⨆ (j : ι) (_ : j ≠ i), W j) : (DirectSum.decompose W b i : M) = 0 := by
  induction hb using Submodule.iSup_induction' with
  | mem j b hb =>
      induction hb using Submodule.iSup_induction' with
      | mem hj b hb => exact DirectSum.decompose_of_mem_ne W hb hj
      | zero => simp
      | add b c _ _ hb hc => simp [DirectSum.decompose_add, hb, hc]
  | zero => simp
  | add b c _ _ hb hc => simp [DirectSum.decompose_add, hb, hc]

/-- **Graded quotients:** if `N` is stable under the homogeneous projections, the images of the
pieces form an internal direct sum decomposition of `M ⧸ N`. -/
theorem isInternal_map_mkQ (N : Submodule ℂ M)
    (hN : ∀ x ∈ N, ∀ i, (DirectSum.decompose W x i : M) ∈ N) :
    DirectSum.IsInternal fun i => (W i).map N.mkQ := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro q hq hq'
    obtain ⟨a, ha, rfl⟩ := hq
    have hsup : (⨆ (j : ι) (_ : j ≠ i), (W j).map N.mkQ) =
        (⨆ (j : ι) (_ : j ≠ i), W j).map N.mkQ := by
      simp only [Submodule.map_iSup]
    rw [hsup] at hq'
    obtain ⟨b, hb, hab⟩ := hq'
    have hmem : b - a ∈ N := (Submodule.Quotient.eq N).mp hab
    have hcomp := hN _ hmem i
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
      decompose_eq_zero_of_mem_iSup_ne W hb, DirectSum.decompose_of_mem_same W ha, zero_sub,
      neg_mem_iff] at hcomp
    exact (Submodule.Quotient.mk_eq_zero N).mpr hcomp
  · rw [← Submodule.map_iSup, (DirectSum.Decomposition.isInternal W).submodule_iSup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

end Quotient

end VOA.Moonshine.ConwayNorton.M8
