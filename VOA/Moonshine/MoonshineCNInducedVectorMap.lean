import VOA.Moonshine.MoonshineCNVermaMultiplication
import VOA.Moonshine.MoonshineCNBorcherdsResolutionRange
import VOA.Moonshine.MoonshineCNEnvelopingEmbedding

/-! The map from a module induced from a space of Lie algebra vectors to the module induced from
the trivial representation, `[a ⊗ u] ↦ [a u ⊗ 1]`.

It is well defined whenever the action on the vectors agrees with the adjoint action modulo the
inducing subalgebra.  Through the PBW multiplication maps it becomes right multiplication in the
enveloping algebra of a complement, so its injectivity is the injectivity of that
multiplication. -/

noncomputable section
open scoped TensorProduct
open Module
namespace VOA.Moonshine.ConwayNorton

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]
variable (p : LieSubalgebra ℂ g)

/-- The module induced from the trivial one-dimensional representation. -/
abbrev trivialInducedSpace := relativeInducedSpace p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)

/-- An element of the inducing subalgebra placed last kills the trivial bottom. -/
theorem trivialInduced_mk_mul_eq_zero (y : UniversalEnvelopingAlgebra ℂ g) (x : p) :
    (Submodule.Quotient.mk ((y * UniversalEnvelopingAlgebra.ι ℂ (x : g)) ⊗ₜ[ℂ] (1 : ℂ)) :
      trivialInducedSpace p) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨y, x, 1, by simp⟩

variable (S : Submodule ℂ g)

/-- The bilinear rule `a ⊗ u ↦ [a u ⊗ 1]` on the tensor product, before balancing. -/
def inducedVectorTensorMap :
    (UniversalEnvelopingAlgebra ℂ g ⊗[ℂ] S) →ₗ[ℂ] trivialInducedSpace p :=
  TensorProduct.lift (((LinearMap.mul ℂ (UniversalEnvelopingAlgebra ℂ g)).compl₂
    ((UniversalEnvelopingAlgebra.ι ℂ).toLinearMap ∘ₗ S.subtype)).compr₂
    ((PBWTheorem.balancing p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)).mkQ ∘ₗ
      (TensorProduct.mk ℂ (UniversalEnvelopingAlgebra ℂ g) ℂ).flip 1))

theorem inducedVectorTensorMap_tmul (a : UniversalEnvelopingAlgebra ℂ g) (u : S) :
    inducedVectorTensorMap p S (a ⊗ₜ[ℂ] u) =
      Submodule.Quotient.mk ((a * UniversalEnvelopingAlgebra.ι ℂ (u : g)) ⊗ₜ[ℂ] (1 : ℂ)) :=
  rfl

variable (σ : p →ₗ⁅ℂ⁆ End ℂ S)
variable (hσ : ∀ (x : p) (u : S), ⁅(x : g), (u : g)⁆ - (σ x u : g) ∈ p)

/-- The induced map `[a ⊗ u] ↦ [a u ⊗ 1]`. -/
def inducedVectorMap : relativeInducedSpace p σ →ₗ[ℂ] trivialInducedSpace p :=
  (PBWTheorem.balancing p σ).liftQ (inducedVectorTensorMap p S) (by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, x, u, rfl⟩
    change inducedVectorTensorMap p S _ = 0
    rw [map_sub, inducedVectorTensorMap_tmul, inducedVectorTensorMap_tmul, sub_eq_zero]
    have hr := hσ x u
    have hcomm : UniversalEnvelopingAlgebra.ι ℂ (x : g) * UniversalEnvelopingAlgebra.ι ℂ (u : g) =
        UniversalEnvelopingAlgebra.ι ℂ (u : g) * UniversalEnvelopingAlgebra.ι ℂ (x : g) +
          UniversalEnvelopingAlgebra.ι ℂ (σ x u : g) +
            UniversalEnvelopingAlgebra.ι ℂ ((⟨_, hr⟩ : p) : g) := by
      have h := (UniversalEnvelopingAlgebra.ι ℂ).map_lie (x : g) (u : g)
      rw [Ring.lie_def] at h
      change _ = _ + _ + UniversalEnvelopingAlgebra.ι ℂ (⁅(x : g), (u : g)⁆ - (σ x u : g))
      rw [map_sub, h]
      abel
    rw [mul_assoc, hcomm, mul_add, mul_add, TensorProduct.add_tmul, TensorProduct.add_tmul,
      Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, ← mul_assoc,
      trivialInduced_mk_mul_eq_zero, trivialInduced_mk_mul_eq_zero, zero_add, add_zero])

theorem inducedVectorMap_mk (a : UniversalEnvelopingAlgebra ℂ g) (u : S) :
    inducedVectorMap p S σ hσ (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) =
      Submodule.Quotient.mk ((a * UniversalEnvelopingAlgebra.ι ℂ (u : g)) ⊗ₜ[ℂ] (1 : ℂ)) :=
  rfl

/-- The induced map intertwines the two induced actions of the whole Lie algebra. -/
theorem inducedVectorMap_equivariant (z : g) (q : relativeInducedSpace p σ) :
    inducedVectorMap p S σ hσ (relativeInducedRep p σ z q) =
      relativeInducedRep p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) z (inducedVectorMap p S σ hσ q) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      change inducedVectorMap p S σ hσ
          (Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ z * a) ⊗ₜ[ℂ] u)) =
        Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ z *
          (a * UniversalEnvelopingAlgebra.ι ℂ (u : g))) ⊗ₜ[ℂ] (1 : ℂ))
      rw [inducedVectorMap_mk, mul_assoc]
  | add t s ht hs =>
      simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (· + ·) ht hs

/-- On the bottom, the induced map is the action of the vector on the trivial bottom. -/
theorem inducedVectorMap_bottom (u : S) :
    inducedVectorMap p S σ hσ (PBWTheorem.bottom p σ u) =
      relativeInducedRep p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) (u : g)
        (PBWTheorem.bottom p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) 1) := by
  change Submodule.Quotient.mk ((1 * UniversalEnvelopingAlgebra.ι ℂ (u : g)) ⊗ₜ[ℂ] (1 : ℂ)) =
    Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ (u : g) * 1) ⊗ₜ[ℂ] (1 : ℂ))
  rw [one_mul, mul_one]

variable (q : LieSubalgebra ℂ g) (hSq : S ≤ q.toSubmodule)

/-- Through the PBW multiplication maps, the induced map is right multiplication. -/
theorem inducedVectorMap_verma (a : UniversalEnvelopingAlgebra ℂ q) (u : S) :
    inducedVectorMap p S σ hσ (relativeVermaMultiplication p q σ (a ⊗ₜ[ℂ] u)) =
      relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)
        ((a * UniversalEnvelopingAlgebra.ι ℂ (⟨u, hSq u.property⟩ : q)) ⊗ₜ[ℂ] (1 : ℂ)) := by
  change Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.lift ℂ
      ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl) a *
        UniversalEnvelopingAlgebra.ι ℂ (u : g)) ⊗ₜ[ℂ] (1 : ℂ)) =
    Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.lift ℂ
      ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl)
        (a * UniversalEnvelopingAlgebra.ι ℂ (⟨u, hSq u.property⟩ : q))) ⊗ₜ[ℂ] (1 : ℂ))
  rw [map_mul, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The induced map composed with the PBW multiplication for `σ` is right multiplication by the
generators, followed by the PBW multiplication for the trivial representation. -/
theorem inducedVectorMap_verma_generator
    (t : UniversalEnvelopingAlgebra ℂ q ⊗[ℂ] (S.comap q.toSubmodule.subtype : Submodule ℂ q)) :
    inducedVectorMap p S σ hσ (relativeVermaMultiplication p q σ
      ((Submodule.comapSubtypeEquivOfLe hSq).toLinearMap.lTensor _ t)) =
        relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)
          (envelopingGeneratorMultiplication (S.comap q.toSubmodule.subtype : Submodule ℂ q) t
            ⊗ₜ[ℂ] (1 : ℂ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      rw [LinearMap.lTensor_tmul, inducedVectorMap_verma p S σ hσ q hSq,
        envelopingGeneratorMultiplication_tmul]
      rfl
  | add t s ht hs => simp only [map_add, TensorProduct.add_tmul, ht, hs]

include hSq in
/-- Injectivity of the induced map and of the PBW multiplication for `σ` give injectivity of
right multiplication `U(q) ⊗ S → U(q)`. -/
theorem generatorMultiplication_injective_of_inducedVectorMap
    (hΦ : Function.Injective (inducedVectorMap p S σ hσ))
    (hV : Function.Injective (relativeVermaMultiplication p q σ)) :
    Function.Injective
      (envelopingGeneratorMultiplication (S.comap q.toSubmodule.subtype : Submodule ℂ q)) := by
  intro t₁ t₂ h
  have h' := congrArg (fun a => relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)
    (a ⊗ₜ[ℂ] (1 : ℂ))) h
  simp only at h'
  rw [← inducedVectorMap_verma_generator p S σ hσ q hSq,
    ← inducedVectorMap_verma_generator p S σ hσ q hSq] at h'
  exact (LinearEquiv.lTensor _ (Submodule.comapSubtypeEquivOfLe hSq)).injective (hV (hΦ h'))

/-- A vector of the complement acting on the trivial bottom vanishes only if it is zero. -/
theorem trivialInduced_action_bottom_injective
    (hV0 : Function.Injective (relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)))
    {u : g} (hu : u ∈ q)
    (h0 : relativeInducedRep p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) u
      (PBWTheorem.bottom p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) 1) = 0) : u = 0 := by
  have hv : relativeInducedRep p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) u
      (PBWTheorem.bottom p (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ) 1) =
        relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ)
          (UniversalEnvelopingAlgebra.ι ℂ (⟨u, hu⟩ : q) ⊗ₜ[ℂ] (1 : ℂ)) := by
    change Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.ι ℂ u * 1) ⊗ₜ[ℂ] (1 : ℂ)) =
      Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.lift ℂ
        ((UniversalEnvelopingAlgebra.ι ℂ).comp q.incl)
          (UniversalEnvelopingAlgebra.ι ℂ (⟨u, hu⟩ : q))) ⊗ₜ[ℂ] (1 : ℂ))
    rw [mul_one, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  rw [hv, ← map_zero (relativeVermaMultiplication p q (0 : p →ₗ⁅ℂ⁆ End ℂ ℂ))] at h0
  have h1 := congrArg (TensorProduct.rid ℂ (UniversalEnvelopingAlgebra ℂ q)) (hV0 h0)
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h1
  have h2 : (⟨u, hu⟩ : q) = 0 :=
    envelopingEmbedding_injective q (h1.trans (map_zero _).symm)
  exact congrArg Subtype.val h2

end VOA.Moonshine.ConwayNorton
