import VOA.Classification.COne.OrbPos13Braiding

/-! # The unit and Reynolds pairing for the B5 sector-projection route

Haploidity and the normalized averaging counit require neither positivity nor
rigidity of the fixed algebra. The pairing below is the actual multiplication
followed by that counit. Its symmetry is proved; a categorical copairing and
its zig-zag identities are NOT supplied by these results.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbB5
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open OrbPos9 OrbPos10 OrbPos13

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V}

/-- Every map from the fixed algebra's vacuum object into the ambient object
is a scalar multiple of the actual inclusion. This holds for any subgroup. -/
theorem ambient_haploid (G : Subgroup (Aut W))
    (f : vacuumObject ⟶ ambient G) : ∃ c : ℂ, f = c • unitInclusion G := by
  have hv : (orbifoldVOA G).vacuum ∈ (adjointModule (orbifoldVOA G)).weight 0 := by
    change (orbifoldVOA G).vacuum ∈ adjWeight (orbifoldVOA G) 0
    rw [← Int.cast_zero, adjWeight_cast]
    exact (orbifoldVOA G).vacuum_mem
  have hw := hom_mem_weight f.property hv
  change f.val (orbifoldVOA G).vacuum ∈ adjWeight W 0 at hw
  rw [← Int.cast_zero, adjWeight_cast, W.vacuum_grade] at hw
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • W.vacuum = f.val (orbifoldVOA G).vacuum :=
    Submodule.mem_span_singleton.mp hw
  refine ⟨c, Ordinary.hom_ext _ _ (fun x => ?_)⟩
  have he := f.property x (-1) (orbifoldVOA G).vacuum
  change f.val ((orbifoldVOA G).smul x (-1) (orbifoldVOA G).vacuum) =
    W.smul x.1 (-1) (f.val (orbifoldVOA G).vacuum) at he
  rw [(orbifoldVOA G).toPreVertexAlgebra.smul_vacuum_neg_one, ← hc] at he
  change f.val x = c • x.1
  change f.val x = mode (W.Y x.1) (-1) (c • W.vacuum) at he
  rw [map_smul] at he
  exact he.trans (congrArg (c • ·) (W.toPreVertexAlgebra.smul_vacuum_neg_one x.1))

/-- The inclusion is nonzero because it preserves the nonzero vacuum. -/
theorem unitInclusion_ne_zero (G : Subgroup (Aut W)) (hv : W.vacuum ≠ 0) :
    unitInclusion G ≠ 0 := by
  intro h
  have he := congrArg (fun f : vacuumObject ⟶ ambient G =>
    f.val (orbifoldVOA G).vacuum) h
  exact hv he

/-- The ambient object is haploid in the dimension formulation. -/
theorem ambient_hom_finrank (G : Subgroup (Aut W)) (hv : W.vacuum ≠ 0) :
    Module.finrank ℂ (vacuumObject ⟶ ambient G) = 1 := by
  apply (finrank_eq_one_iff_of_nonzero' (unitInclusion G) (unitInclusion_ne_zero G hv)).mpr
  intro f
  obtain ⟨c, hc⟩ := ambient_haploid G f
  exact ⟨c, hc.symm⟩

/-- The categorical composite is exactly the normalized group average. -/
theorem retraction_inclusion_average (G : Subgroup (Aut W)) [Fintype G] :
    unitRetraction G ≫ unitInclusion G =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ambientSymmetry G g).hom := by
  apply Ordinary.hom_ext
  intro x
  change (reynolds G x : V) = _
  rw [reynolds_apply]
  change _ = (Fintype.card G : ℂ)⁻¹ • (∑ g : G, (ambientSymmetry G g).hom).val x
  congr 1
  rw [Submodule.coe_sum, LinearMap.sum_apply]
  rfl

/-- Averaging is invariant under each actual group automorphism. -/
theorem symmetry_retraction (G : Subgroup (Aut W)) [Fintype G] (g : G) :
    (ambientSymmetry G g).hom ≫ unitRetraction G = unitRetraction G := by
  apply Ordinary.hom_ext
  intro x
  apply Subtype.ext
  change (reynolds G (g.1 x) : V) = (reynolds G x : V)
  rw [reynolds_apply, reynolds_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => rfl)

/-- The proposed duality evaluation, pinned to the VOA product and averaging. -/
def reynoldsPairing (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G)) :
    tensorObj F (ambient G) (ambient G) ⟶ vacuumObject :=
  ambientMultiplication G F ≫ unitRetraction G

/-- The evaluation is invariant under the diagonal group action. -/
theorem reynoldsPairing_invariant (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G)) (g : G) :
    tensorHom F (ambientSymmetry G g).hom (ambientSymmetry G g).hom ≫
        reynoldsPairing G F = reynoldsPairing G F := by
  rw [reynoldsPairing, ← Category.assoc, ambientSymmetry_mul, Category.assoc,
    symmetry_retraction]

/-- Braided symmetry of the actual Reynolds pairing. -/
theorem reynoldsPairing_symmetric (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G)) :
    (BraidRibbon.braiding F (ambient G) (ambient G)).hom ≫ reynoldsPairing G F =
      reynoldsPairing G F := by
  rw [reynoldsPairing, ← Category.assoc, ambientMultiplication_braiding]

/-- Haploidity makes the copairing normalization equivalent to its scalar
evaluation. This does not assert that a copairing exists. -/
theorem copairing_normalization_iff (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G))
    (c : vacuumObject ⟶ tensorObj F (ambient G) (ambient G)) (d : ℂ) :
    c ≫ ambientMultiplication G F = d • unitInclusion G ↔
      c ≫ reynoldsPairing G F = d • 𝟙 vacuumObject := by
  constructor
  · intro h
    rw [reynoldsPairing, ← Category.assoc, h, Linear.smul_comp,
      unitInclusion_retraction]
  · intro h
    obtain ⟨a, ha⟩ := ambient_haploid G (c ≫ ambientMultiplication G F)
    have hh : a • 𝟙 (vacuumObject (W := orbifoldVOA G)) = d • 𝟙 vacuumObject := by
      simpa only [reynoldsPairing, ← Category.assoc, ha, Linear.smul_comp,
        unitInclusion_retraction] using h
    have he := congrArg (fun f : vacuumObject ⟶ vacuumObject => f ≫ unitInclusion G) hh
    simpa only [Linear.smul_comp, Category.id_comp, ← ha] using he

end VOA.Classification.COne.OrbB5
