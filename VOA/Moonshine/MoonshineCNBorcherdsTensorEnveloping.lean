import VOA.Moonshine.MoonshineCNBorcherdsResolution
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.Flat.Basic

/-! The tensor algebra on U is the enveloping algebra of the positive part.

For any Lie algebra `L` and subspace `S`, if right multiplication `U(L) ⊗ S → U(L)` is injective
then the canonical algebra map `T(S) → U(L)` is injective.  The proof is an induction along the
degree filtration of `T(S)`, using flatness over `ℂ` and the augmentation.  Combined with the
length-one resolution this gives `T(U) ≅ U(𝔲⁺)` for Borcherds data, compatibly with every
symmetry of the data. -/

noncomputable section
open scoped TensorProduct
open Module
namespace VOA.Moonshine.ConwayNorton

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] (S : Submodule ℂ L)

/-- The degree filtration `F 0 = ℂ`, `F (n+1) = ℂ + F n · S` of the tensor algebra. -/
def tensorDegreeFiltration : ℕ → Submodule ℂ (TensorAlgebra ℂ S)
  | 0 => 1
  | n + 1 => 1 ⊔ tensorDegreeFiltration n * LinearMap.range (TensorAlgebra.ι ℂ)

theorem tensorDegreeFiltration_succ (n : ℕ) :
    tensorDegreeFiltration S (n + 1) =
      1 ⊔ tensorDegreeFiltration S n * LinearMap.range (TensorAlgebra.ι ℂ) := rfl

theorem tensorDegreeFiltration_le_succ (n : ℕ) :
    tensorDegreeFiltration S n ≤ tensorDegreeFiltration S (n + 1) := by
  induction n with
  | zero => exact le_sup_left
  | succ n ih =>
      rw [tensorDegreeFiltration_succ S (n + 1), tensorDegreeFiltration_succ S n]
      exact sup_le_sup_left (mul_le_mul' ih le_rfl) _

theorem tensorDegreeFiltration_mono : Monotone (tensorDegreeFiltration S) :=
  monotone_nat_of_le_succ (tensorDegreeFiltration_le_succ S)

theorem tensorDegreeFiltration_mul (a b : ℕ) :
    tensorDegreeFiltration S a * tensorDegreeFiltration S b ≤
      tensorDegreeFiltration S (a + b) := by
  induction b with
  | zero =>
      change tensorDegreeFiltration S a * 1 ≤ _
      rw [Submodule.mul_one]
      exact le_rfl
  | succ b ih =>
      rw [tensorDegreeFiltration_succ S b, Submodule.mul_sup, Submodule.mul_one, ← mul_assoc]
      have hR : tensorDegreeFiltration S a * tensorDegreeFiltration S b *
          LinearMap.range (TensorAlgebra.ι ℂ) ≤ tensorDegreeFiltration S (a + (b + 1)) := by
        rw [show a + (b + 1) = (a + b) + 1 by omega, tensorDegreeFiltration_succ S (a + b)]
        exact le_sup_of_le_right (mul_le_mul' ih le_rfl)
      exact sup_le (tensorDegreeFiltration_mono S (show a ≤ a + (b + 1) by omega)) hR

theorem tensorDegreeFiltration_exhaustive (x : TensorAlgebra ℂ S) :
    ∃ n, x ∈ tensorDegreeFiltration S n := by
  induction x using TensorAlgebra.induction with
  | algebraMap c => exact ⟨0, Submodule.mem_one.mpr ⟨c, rfl⟩⟩
  | ι u =>
      refine ⟨1, Submodule.mem_sup_right ?_⟩
      rw [← one_mul (TensorAlgebra.ι ℂ u)]
      exact Submodule.mul_mem_mul (Submodule.mem_one.mpr ⟨1, map_one _⟩)
        (LinearMap.mem_range_self _ u)
  | mul x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, tensorDegreeFiltration_mul S a b (Submodule.mul_mem_mul ha hb)⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨max a b, Submodule.add_mem _
        (tensorDegreeFiltration_mono S (le_max_left a b) ha)
        (tensorDegreeFiltration_mono S (le_max_right a b) hb)⟩

/-- Right multiplication by generators lands in the augmentation kernel. -/
theorem envelopingAugmentation_generatorMultiplication
    (t : UniversalEnvelopingAlgebra ℂ L ⊗[ℂ] S) :
    envelopingAugmentation (envelopingGeneratorMultiplication S t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      rw [envelopingGeneratorMultiplication_tmul, map_mul]
      simp [envelopingAugmentation]
  | add t s ht hs => rw [map_add, map_add, ht, hs, add_zero]

/-- The tensor generators identified with their image in the tensor algebra. -/
def tensorGeneratorRangeEquiv : S ≃ₗ[ℂ] LinearMap.range (TensorAlgebra.ι ℂ (M := S)) :=
  LinearEquiv.ofInjective _ TensorAlgebra.ι_leftInverse.injective

/-- Injective right multiplication by generators makes `T(S) → U(L)` injective. -/
theorem tensorGeneratorToEnveloping_injective_of_multiplication
    (hμ : Function.Injective (envelopingGeneratorMultiplication S)) :
    Function.Injective (tensorGeneratorToEnveloping S) := by
  let τ := tensorGeneratorToEnveloping S
  let R := LinearMap.range (TensorAlgebra.ι ℂ (M := S))
  let E := tensorGeneratorRangeEquiv S
  have hstep : ∀ n, ∀ x ∈ tensorDegreeFiltration S n, τ x = 0 → x = 0 := by
    intro n
    induction n with
    | zero =>
        intro x hx h
        obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hx
        have hc := congrArg envelopingAugmentation h
        rw [AlgHom.commutes, AlgHom.commutes, map_zero, Algebra.algebraMap_self,
          RingHom.id_apply] at hc
        rw [hc, map_zero]
    | succ n ih =>
        intro x hx h
        rw [tensorDegreeFiltration_succ] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hy
        rw [← Submodule.mulMap_range] at hz
        obtain ⟨s, rfl⟩ := hz
        let T : (tensorDegreeFiltration S n ⊗[ℂ] R) →ₗ[ℂ]
            (UniversalEnvelopingAlgebra ℂ L ⊗[ℂ] S) :=
          (τ.toLinearMap ∘ₗ (tensorDegreeFiltration S n).subtype).rTensor S ∘ₗ
            E.symm.toLinearMap.lTensor _
        have hT : ∀ s, envelopingGeneratorMultiplication S (T s) =
            τ (Submodule.mulMap (tensorDegreeFiltration S n) R s) := by
          intro s
          induction s using TensorProduct.induction_on with
          | zero => simp
          | tmul a r =>
              have hr : (r : TensorAlgebra ℂ S) = TensorAlgebra.ι ℂ (E.symm r) := by
                have := congrArg Subtype.val (E.apply_symm_apply r)
                exact this.symm
              simp only [T, LinearMap.comp_apply, LinearMap.lTensor_tmul,
                LinearMap.rTensor_tmul, Submodule.mulMap_tmul,
                envelopingGeneratorMultiplication_tmul, map_mul, LinearEquiv.coe_coe,
                Submodule.coe_subtype, AlgHom.toLinearMap_apply]
              rw [hr, tensorGeneratorToEnveloping_generator]
          | add s t hs ht => simp only [map_add, hs, ht]
        have hinjT : Function.Injective T := by
          have hτn :
              Function.Injective (τ.toLinearMap ∘ₗ (tensorDegreeFiltration S n).subtype) := by
            rw [← LinearMap.ker_eq_bot, eq_bot_iff]
            intro w hw
            have := ih w w.property hw
            exact (Submodule.mem_bot ℂ).mpr (Subtype.ext this)
          exact (Module.Flat.rTensor_preserves_injective_linearMap _ hτn).comp
            (LinearEquiv.lTensor _ E.symm).injective
        rw [map_add, AlgHom.commutes] at h
        have hc : c = 0 := by
          have h1 := congrArg envelopingAugmentation h
          rw [map_add, AlgHom.commutes, ← hT, envelopingAugmentation_generatorMultiplication,
            map_zero, add_zero, Algebra.algebraMap_self, RingHom.id_apply] at h1
          exact h1
        subst hc
        rw [map_zero, zero_add, ← hT] at h
        have hs0 : s = 0 := hinjT (hμ (h.trans (map_zero _).symm))
        rw [hs0, map_zero, map_zero, add_zero]
  intro x y hxy
  obtain ⟨a, ha⟩ := tensorDegreeFiltration_exhaustive S x
  obtain ⟨b, hb⟩ := tensorDegreeFiltration_exhaustive S y
  have hmem : x - y ∈ tensorDegreeFiltration S (max a b) :=
    Submodule.sub_mem _ (tensorDegreeFiltration_mono S (le_max_left a b) ha)
      (tensorDegreeFiltration_mono S (le_max_right a b) hb)
  exact sub_eq_zero.mp (hstep _ _ hmem (by rw [map_sub, hxy, sub_self]))

/-- Functoriality of the enveloping algebra. -/
def envelopingMap {L' : Type*} [LieRing L'] [LieAlgebra ℂ L'] (φ : L →ₗ⁅ℂ⁆ L') :
    UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ L' :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp φ)

/-- Functoriality of the tensor algebra in a linear map of generators. -/
def tensorGeneratorMap {L' : Type*} [LieRing L'] [LieAlgebra ℂ L'] {S' : Submodule ℂ L'}
    (h : S →ₗ[ℂ] S') : TensorAlgebra ℂ S →ₐ[ℂ] TensorAlgebra ℂ S' :=
  TensorAlgebra.lift ℂ ((TensorAlgebra.ι ℂ).comp h)

/-- The canonical map from the tensor algebra is natural in Lie maps preserving generators. -/
theorem tensorGeneratorToEnveloping_natural {L' : Type*} [LieRing L'] [LieAlgebra ℂ L']
    (S' : Submodule ℂ L') (φ : L →ₗ⁅ℂ⁆ L') (hφ : ∀ u ∈ S, φ u ∈ S')
    (t : TensorAlgebra ℂ S) :
    tensorGeneratorToEnveloping S'
        (tensorGeneratorMap S (φ.toLinearMap.restrict (p := S) (q := S') hφ) t) =
      envelopingMap φ (tensorGeneratorToEnveloping S t) := by
  have h : (tensorGeneratorToEnveloping S').comp
      (tensorGeneratorMap S (φ.toLinearMap.restrict (p := S) (q := S') hφ)) =
        (envelopingMap φ).comp (tensorGeneratorToEnveloping S) := by
    apply TensorAlgebra.hom_ext
    apply LinearMap.ext
    intro u
    simp [envelopingMap, tensorGeneratorMap]
  exact congrArg (fun F : TensorAlgebra ℂ S →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ L' => F t) h

namespace BorcherdsData
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)
variable (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
  (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)

include he hf hef in
/-- The canonical map `T(U) → U(𝔲⁺)` is bijective. -/
theorem positiveTensorGeneratorToEnveloping_bijective :
    Function.Bijective (tensorGeneratorToEnveloping (D.positiveGeneratorSpace e)) :=
  ⟨tensorGeneratorToEnveloping_injective_of_multiplication _
      (D.positiveGeneratorMultiplication_injective e f he hf hef),
    D.positiveTensorGeneratorToEnveloping_surjective e f he hf hef⟩

/-- The algebra isomorphism `T(U) ≃ U(𝔲⁺)`. -/
def positiveTensorEnvelopingEquiv :
    TensorAlgebra ℂ (D.positiveGeneratorSpace e) ≃ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ D.positivePart :=
  AlgEquiv.ofBijective _ (D.positiveTensorGeneratorToEnveloping_bijective e f he hf hef)

@[simp] theorem positiveTensorEnvelopingEquiv_generator (u : D.positiveGeneratorSpace e) :
    D.positiveTensorEnvelopingEquiv e f he hf hef (TensorAlgebra.ι ℂ u) =
      UniversalEnvelopingAlgebra.ι ℂ (u : D.positivePart) :=
  tensorGeneratorToEnveloping_generator _ u

section Equivariance
variable {G : Type*} [Group G] (A : D.GAction G)

/-- Every symmetry of the data preserves the positive part. -/
theorem positivePart_action_mem (σ : G) {x : g} (hx : x ∈ D.positivePart) :
    A.action σ x ∈ D.positivePart := by
  change x ∈ D.weightSpan borcherdsPositiveCone at hx
  change A.action σ x ∈ D.weightSpan borcherdsPositiveCone
  induction hx using Submodule.iSup_induction' with
  | mem γ x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hγ x hx =>
          exact D.weightSpace_le_weightSpan hγ (A.graded σ γ x hx)
      | zero => simp
      | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- A symmetry of the data, restricted to the positive part, as a Lie algebra map. -/
def positivePartAction (σ : G) : D.positivePart →ₗ⁅ℂ⁆ D.positivePart where
  toLinearMap := (A.action σ).toLinearMap.restrict
    (p := D.positivePart.toSubmodule) (q := D.positivePart.toSubmodule)
    (fun _ hx => D.positivePart_action_mem A σ hx)
  map_lie' {x y} := Subtype.ext (A.preserves_lie σ x y)

include he in
theorem positiveGenerator_action_mem (σ : G) :
    ∀ u ∈ D.positiveGeneratorSpace e,
      D.positivePartAction A σ u ∈ D.positiveGeneratorSpace e :=
  fun _ hu => D.genSpace_equivariant A σ e he hu

include hf hef in
/-- `T(U) ≃ U(𝔲⁺)` intertwines every symmetry of the Borcherds data. -/
theorem positiveTensorEnvelopingEquiv_equivariant (σ : G)
    (t : TensorAlgebra ℂ (D.positiveGeneratorSpace e)) :
    D.positiveTensorEnvelopingEquiv e f he hf hef
        (tensorGeneratorMap _ ((D.positivePartAction A σ).toLinearMap.restrict
          (p := D.positiveGeneratorSpace e) (q := D.positiveGeneratorSpace e)
          (D.positiveGenerator_action_mem e he A σ)) t) =
      envelopingMap (D.positivePartAction A σ)
        (D.positiveTensorEnvelopingEquiv e f he hf hef t) :=
  tensorGeneratorToEnveloping_natural _ _ (D.positivePartAction A σ) _ t

end Equivariance

end BorcherdsData
end VOA.Moonshine.ConwayNorton
