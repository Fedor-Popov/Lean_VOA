import VOA.Classification.COne.PlusNice
import VOA.Classification.COne.Distinct

/-!
# Structural properties of finite orbifolds of `V₂`

No orbifold finiteness or rationality theorem is assumed here. Uniqueness of the
normalized invariant form makes every automorphism an isometry. Averaging over
a finite group then proves nondegeneracy on fixed points. Li's radical criterion
gives simplicity. CFT type is part of the ambient VOA structure, independently
of the additional vanishing of weight one for exceptional groups.
-/

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VertexOperatorAlgebra
open scoped BigOperators

universe u

section Forms
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

/-- Pullback along an automorphism, retaining Virasoro adjointness. -/
def exceptionalPullForm (B : InvariantForm W) (g : Aut W) : InvariantForm W where
  form := B.form.compl₁₂ g.toLinearEquiv.toLinearMap g.toLinearEquiv.toLinearMap
  virasoro_adj := by
    intro n a b
    change B.form (g (W.L n a)) (g b) = B.form (g a) (g (W.L (-n) b))
    have hg : IsVOAHom W W g.toLinearEquiv.toLinearMap :=
      ⟨g.map_vacuum, g.map_smul'⟩
    have hL (k : ℤ) (v : 𝒱) : g (W.L k v) = W.L k (g v) :=
      voaHom_map_L hg g.map_omega k v
    rw [hL, hL, B.virasoro_adj]

theorem exceptionalPullForm_fullyInvariant {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (g : Aut W) :
    (exceptionalPullForm B g).IsFullyInvariant := by
  have hg : IsVOAHom W W g.toLinearEquiv.toLinearMap :=
    ⟨g.map_vacuum, g.map_smul'⟩
  intro wt a ha n x y
  change B.form (g (W.smul a n x)) (g y) = _
  rw [g.map_smul', hB wt (g a) (g.map_grading ha) n (g x) (g y)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = (j.factorial : ℂ)⁻¹ • B.form (g x)
    (g (W.smul (((W.L 1) ^ j) a) (2 * wt - n - 2 - (j : ℤ)) y))
  have hp : g (((W.L 1) ^ j) a) = ((W.L 1) ^ j) (g a) :=
    voaHom_map_L_pow hg g.map_omega 1 j a
  rw [g.map_smul', hp]

/-- Uniqueness makes the normalized fully invariant form invariant under all automorphisms. -/
theorem exceptional_form_aut_isometry {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (hn : B.Normalized) (g : Aut W) (x y : 𝒱) :
    B.form (g x) (g y) = B.form x y := by
  have hn' : (exceptionalPullForm B g).Normalized := by
    change B.form (g W.vacuum) (g W.vacuum) = 1
    rw [show g W.vacuum = W.vacuum from g.map_vacuum]
    exact hn
  exact congrArg (fun f : LinearMap.BilinForm ℂ 𝒱 => f x y)
    (InvariantForm.invariantForm_unique (exceptionalPullForm_fullyInvariant hB g) hB hn' hn)

/-- Finite-group averaging preserves nondegeneracy on fixed points. -/
theorem restrictSubForm_leftRadical_finite (G : Subgroup (Aut W)) [Finite G]
    {B : InvariantForm W} (hB : InvariantForm.leftRadical B = ⊥)
    (hiso : ∀ g ∈ G, ∀ x y : 𝒱, B.form (g x) (g y) = B.form x y) :
    InvariantForm.leftRadical (restrictSubForm (orbifold G) B) = ⊥ := by
  classical
  letI := Fintype.ofFinite G
  rw [eq_bot_iff]
  intro x hx
  rw [InvariantForm.mem_leftRadical] at hx
  have hxrad : (x : 𝒱) ∈ InvariantForm.leftRadical B := by
    rw [InvariantForm.mem_leftRadical]
    apply LinearMap.ext
    intro y
    let z : 𝒱 := ∑ g : G, (g : Aut W) y
    have hz : z ∈ (orbifold G).carrier := by
      intro g hg
      change g.toLinearEquiv (∑ h : G, (h : Aut W) y) = ∑ h : G, (h : Aut W) y
      rw [map_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : G)) _ _ (fun h => rfl)
    have hxy : ∀ g : G, B.form (x : 𝒱) ((g : Aut W) y) = B.form (x : 𝒱) y := by
      intro g
      rw [← hiso g g.2 (x : 𝒱) y, x.2 g g.2]
    have hzero := DFunLike.congr_fun hx (⟨z, hz⟩ : (orbifold G).carrier)
    change B.form (x : 𝒱) z = 0 at hzero
    simp only [z, map_sum, hxy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hzero
    have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hzero).resolve_left hc
  rw [hB, Submodule.mem_bot] at hxrad
  exact (Submodule.mem_bot _).mpr (Subtype.ext hxrad)

end Forms

/-- The restricted lattice form on an arbitrary fixed-point algebra of `V₂`. -/
noncomputable def exceptionalOrbifoldForm (G : Subgroup (Aut (V2m 1 le_rfl))) :
    InvariantForm (orbifoldVOA G) :=
  restrictSubForm (orbifold G) (latInvForm (latP 1) (latP_even 1) (latP_posDef 1 le_rfl))

theorem exceptionalOrbifoldForm_fullyInvariant (G : Subgroup (Aut (V2m 1 le_rfl))) :
    (exceptionalOrbifoldForm G).IsFullyInvariant :=
  restrictSubForm_isFullyInvariant _ (latInvForm_isFullyInvariant _ _ _)

theorem exceptionalOrbifoldForm_normalized (G : Subgroup (Aut (V2m 1 le_rfl))) :
    (exceptionalOrbifoldForm G).Normalized :=
  restrictSubForm_normalized _ (latInvForm_normalized _ _ _)

theorem exceptionalOrbifoldForm_leftRadical (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    InvariantForm.leftRadical (exceptionalOrbifoldForm G) = ⊥ :=
  restrictSubForm_leftRadical_finite G (latInvForm_leftRadical _ _ _)
    (fun g _ => exceptional_form_aut_isometry (latInvForm_isFullyInvariant _ _ _)
      (latInvForm_normalized _ _ _) g)

/-- Every finite orbifold of `V₂` is simple. -/
theorem exceptionalOrbifold_isSimple (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    (orbifoldVOA G).IsSimple :=
  (LiRadical.isSimple_iff_leftRadical_eq_bot (exceptionalOrbifoldForm_fullyInvariant G)
    (exceptionalOrbifoldForm_normalized G)).mpr (exceptionalOrbifoldForm_leftRadical G)

/-- Every finite orbifold of `V₂` is self-dual, witnessed by the restricted lattice form. -/
theorem exceptionalOrbifold_selfDual (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    (orbifoldVOA G).SelfDual :=
  ⟨exceptionalOrbifoldForm G, exceptionalOrbifoldForm_fullyInvariant G,
    exceptionalOrbifoldForm_leftRadical G⟩

theorem exceptionalOrbifold_centralCharge (G : Subgroup (Aut (V2m 1 le_rfl))) :
    (orbifoldVOA G).centralCharge = 1 := V2m_centralCharge 1 le_rfl

/-- Exactly the three remaining properties required for niceness. -/
theorem exceptionalOrbifold_nice_iff (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    Nice (orbifoldVOA G) ↔ C2Cofinite (orbifoldVOA G) ∧
      AdmissiblyRational (orbifoldVOA G) ∧ PseudoUnitary (orbifoldVOA G) := by
  constructor
  · intro h
    exact ⟨h.1.c2Cofinite, h.1.rational, h.2⟩
  · rintro ⟨hC2, hRat, hPU⟩
    exact ⟨⟨⟨exceptionalOrbifold_isSimple G, exceptionalOrbifold_selfDual G, hC2⟩, hRat⟩, hPU⟩

end VOA.Classification.COne
