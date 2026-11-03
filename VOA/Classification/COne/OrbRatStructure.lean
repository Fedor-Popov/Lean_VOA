import VOA.Classification.COne.ExceptionalOrbifoldBasic

/-!
# Finite orbifolds of a self-dual VOA: simplicity, self-duality, strong finiteness

For an arbitrary VOA `W` carrying a nondegenerate fully invariant form (`W.SelfDual`) and an
arbitrary finite subgroup `G ≤ Aut W`, the fixed-point algebra `W^G = orbifoldVOA G` is simple
and self-dual.  Consequently, for strongly finite (in particular strongly rational) `W`,

  `StronglyRational (W^G) ↔ C2Cofinite (W^G) ∧ AdmissiblyRational (W^G)`.

This generalizes `exceptionalOrbifold_isSimple` / `exceptionalOrbifold_selfDual` (proved there only
for `W = V₂`, via the explicit lattice form) to every self-dual `W`.  The argument is the same:

1. rescale the given nondegenerate form to the unit normalization `(𝟙|𝟙) = 1`
   (`form_vacuum_ne_zero_of_leftRadical_eq_bot` gives `(𝟙|𝟙) ≠ 0`);
2. uniqueness of the normalized fully invariant form (`invariantForm_unique`) makes every
   automorphism an isometry (`exceptional_form_aut_isometry`);
3. finite-group averaging gives nondegeneracy on fixed points
   (`restrictSubForm_leftRadical_finite`);
4. Li's radical criterion (`LiRadical.isSimple_iff_leftRadical_eq_bot`) gives simplicity.

Nothing about rationality or `C₂`-cofiniteness of `W^G` is proved here.
-/

namespace VOA.Classification.COne.OrbRat

open VOA VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The left radical is unchanged by a nonzero rescaling. -/
theorem leftRadical_scale {B : InvariantForm W} {c : ℂ} (hc : c ≠ 0) :
    InvariantForm.leftRadical (InvariantForm.scale c B) = InvariantForm.leftRadical B := by
  ext x
  rw [InvariantForm.mem_leftRadical, InvariantForm.mem_leftRadical]
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    have hy := DFunLike.congr_fun h y
    rw [InvariantForm.scale_form_apply, LinearMap.zero_apply, smul_eq_mul] at hy
    exact (mul_eq_zero.mp hy).resolve_left hc
  · intro h
    apply LinearMap.ext
    intro y
    rw [InvariantForm.scale_form_apply, LinearMap.zero_apply, h, LinearMap.zero_apply, smul_zero]

/-- A self-dual VOA with `𝟙 ≠ 0` carries a fully invariant, unit-normalized, nondegenerate form. -/
theorem exists_normalized_of_selfDual (hne : W.vacuum ≠ 0) (h : W.SelfDual) :
    ∃ B : InvariantForm W, B.IsFullyInvariant ∧ B.Normalized ∧
      InvariantForm.leftRadical B = ⊥ := by
  obtain ⟨B, hB, hrad⟩ := h
  have h1 : B.form W.vacuum W.vacuum ≠ 0 := form_vacuum_ne_zero_of_leftRadical_eq_bot hne hrad
  refine ⟨InvariantForm.scale (B.form W.vacuum W.vacuum)⁻¹ B, hB.scale _, ?_, ?_⟩
  · change (InvariantForm.scale (B.form W.vacuum W.vacuum)⁻¹ B).form W.vacuum W.vacuum = 1
    rw [InvariantForm.scale_form_apply, smul_eq_mul, inv_mul_cancel₀ h1]
  · rw [leftRadical_scale (inv_ne_zero h1), hrad]

/-- The restricted normalized form on a finite orbifold of a self-dual VOA. -/
theorem exists_orbifold_form (hne : W.vacuum ≠ 0) (h : W.SelfDual)
    (G : Subgroup (Aut W)) [Finite G] :
    ∃ B : InvariantForm (orbifoldVOA G), B.IsFullyInvariant ∧ B.Normalized ∧
      InvariantForm.leftRadical B = ⊥ := by
  obtain ⟨B, hB, hn, hrad⟩ := exists_normalized_of_selfDual hne h
  exact ⟨restrictSubForm (orbifold G) B, restrictSubForm_isFullyInvariant _ hB,
    restrictSubForm_normalized _ hn,
    restrictSubForm_leftRadical_finite G hrad
      (fun g _ => exceptional_form_aut_isometry hB hn g)⟩

/-- **Every finite orbifold of a self-dual VOA is simple** (any `W`, any finite `G`). -/
theorem orbifold_isSimple (hne : W.vacuum ≠ 0) (h : W.SelfDual)
    (G : Subgroup (Aut W)) [Finite G] : (orbifoldVOA G).IsSimple := by
  obtain ⟨B, hB, hn, hrad⟩ := exists_orbifold_form hne h G
  exact (LiRadical.isSimple_iff_leftRadical_eq_bot hB hn).mpr hrad

/-- **Every finite orbifold of a self-dual VOA is self-dual.** -/
theorem orbifold_selfDual (hne : W.vacuum ≠ 0) (h : W.SelfDual)
    (G : Subgroup (Aut W)) [Finite G] : (orbifoldVOA G).SelfDual := by
  obtain ⟨B, hB, _, hrad⟩ := exists_orbifold_form hne h G
  exact ⟨B, hB, hrad⟩

/-- A finite orbifold of a strongly finite VOA is strongly finite as soon as it is
`C₂`-cofinite. -/
theorem orbifold_stronglyFinite (hW : StronglyFinite W) (G : Subgroup (Aut W)) [Finite G]
    (hC2 : C2Cofinite (orbifoldVOA G)) : StronglyFinite (orbifoldVOA G) :=
  ⟨orbifold_isSimple hW.vacuum_ne_zero hW.selfDual G,
    orbifold_selfDual hW.vacuum_ne_zero hW.selfDual G, hC2⟩

/-- **For a finite orbifold of a strongly finite VOA, strong rationality is exactly
`C₂`-cofiniteness plus admissible rationality.**  Simplicity and self-duality are free. -/
theorem orbifold_stronglyRational_iff (hW : StronglyFinite W) (G : Subgroup (Aut W)) [Finite G] :
    StronglyRational (orbifoldVOA G) ↔
      C2Cofinite (orbifoldVOA G) ∧ AdmissiblyRational (orbifoldVOA G) :=
  ⟨fun h => ⟨h.c2Cofinite, h.rational⟩,
    fun h => { orbifold_stronglyFinite hW G h.1 with rational := h.2 }⟩

end VOA.Classification.COne.OrbRat
