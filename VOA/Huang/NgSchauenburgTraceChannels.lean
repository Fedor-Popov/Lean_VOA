import VOA.Huang.NgSchauenburgTracePairing

/-! # Simple-channel resolutions for categorical indicator traces

The inverse simple dimensions in the NS trace expansion are derived from
Schur's lemma. The resulting resolutions are identities of actual morphisms.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- Numerical trace recovers a simple endomorphism with the required dimension factor. -/
theorem simple_end_eq_trace (i : F.Label) (f : F.simple i ⟶ F.simple i) :
    f = (F.scalarTrace (F.simple i) f / F.dimension (F.simple i)) • 𝟙 (F.simple i) := by
  letI := F.simple_isSimple i
  letI := F.homFinite
  obtain ⟨z, rfl⟩ := endomorphism_simple_eq_smul_id ℂ f
  simp [F.dimension_simple_ne_zero]

/-- Reverse maps normalized by composition, rather than by categorical trace. -/
def compositionDual {Y : C} {i : F.Label} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (F.simple i ⟶ Y)) (a : ι) : Y ⟶ F.simple i :=
  F.dimension (F.simple i) • F.traceDualBasis b a

theorem comp_compositionDual {Y : C} {i : F.Label} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (F.simple i ⟶ Y)) (a : ι) (f : F.simple i ⟶ Y) :
    f ≫ F.compositionDual b a = b.repr f a • 𝟙 (F.simple i) := by
  rw [F.simple_end_eq_trace i (f ≫ F.compositionDual b a)]
  simp [compositionDual, F.dimension_simple_ne_zero]

theorem traceDualBasis_eq_inv_smul {Y : C} {i : F.Label} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (F.simple i ⟶ Y)) (a : ι) :
    F.traceDualBasis b a = (F.dimension (F.simple i))⁻¹ • F.compositionDual b a := by
  simp [compositionDual, smul_smul, F.dimension_simple_ne_zero]

open Classical in
/-- The bases used for simple channels are composition-dual after rescaling. -/
theorem basis_comp_compositionDual {Y : C} {i : F.Label} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (F.simple i ⟶ Y)) (a c : ι) :
    b c ≫ F.compositionDual b a = if c = a then 𝟙 (F.simple i) else 0 := by
  rw [F.comp_compositionDual]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- Morphisms between distinct members of the simple family vanish. -/
theorem hom_simple_eq_zero {i j : F.Label} (hij : i ≠ j)
    (f : F.simple i ⟶ F.simple j) : f = 0 := by
  letI := F.simple_isSimple i
  letI := F.simple_isSimple j
  by_contra hf
  letI := isIso_of_hom_simple hf
  exact hij (F.distinct i j ⟨asIso f⟩)

/-- The complete simple family detects equality of morphisms out of any object. -/
theorem hom_ext_from_simples {X Y : C} {f g : X ⟶ Y}
    (h : ∀ (i : F.Label) (q : F.simple i ⟶ X), q ≫ f = q ≫ g) : f = g := by
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  apply (cancel_epi e.inv).mp
  apply biproduct.hom_ext'
  intro k
  simpa only [Category.assoc] using
    h (a k) (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv)

/-- A resolution of the identity through all simple channels. No completeness
or orthogonality of the supplied bases is assumed beyond `Module.Basis`. -/
theorem sum_compositionDual_comp {Y : C} {ι : F.Label → Type*}
    [∀ i, Fintype (ι i)] (b : ∀ i, Module.Basis (ι i) ℂ (F.simple i ⟶ Y)) :
    (∑ i, ∑ a, F.compositionDual (b i) a ≫ b i a) = 𝟙 Y := by
  classical
  apply F.hom_ext_from_simples
  intro j f
  simp only [Preadditive.comp_sum, ← Category.assoc, Category.comp_id]
  rw [Finset.sum_eq_single j]
  · simp only [F.comp_compositionDual, Linear.smul_comp, Category.id_comp]
    exact (b j).sum_repr f
  · intro i _ hij
    apply Finset.sum_eq_zero
    intro a _
    rw [F.hom_simple_eq_zero (Ne.symm hij) (f ≫ F.compositionDual (b i) a), zero_comp]
  · simp

/-- Expansion of an arbitrary morphism through source-simple and target-simple
bases, with its coefficients supplied by the categorical trace pairing. -/
theorem hom_eq_sum_trace_channels {X Y : C} {ι κ : F.Label → Type*}
    [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (b : ∀ i, Module.Basis (ι i) ℂ (F.simple i ⟶ X))
    (c : ∀ i, Module.Basis (κ i) ℂ (F.simple i ⟶ Y)) (f : X ⟶ Y) :
    f = ∑ i, ∑ a, ∑ d,
      F.scalarTrace X (f ≫ F.traceDualBasis (c i) d ≫ b i a) •
        (F.compositionDual (b i) a ≫ c i d) := by
  calc
    f = (∑ i, ∑ a, F.compositionDual (b i) a ≫ b i a) ≫ f := by
      rw [F.sum_compositionDual_comp, Category.id_comp]
    _ = ∑ i, ∑ a, F.compositionDual (b i) a ≫ (b i a ≫ f) := by
      simp only [Preadditive.sum_comp, Category.assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      conv_lhs => rw [← (c i).sum_repr (b i a ≫ f)]
      simp only [Preadditive.comp_sum, Linear.comp_smul]
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      rw [← F.traceDualBasis_pair (c i) d]
      simpa only [Category.assoc] using
        F.scalarTrace_comp_comm (b i a) (f ≫ F.traceDualBasis (c i) d)

/-- The channel form of the ordinary linear trace on `Hom(X,Y)`. This is
the finite-dimensional contraction underlying NS's diagrammatic trace formulas. -/
theorem linearTrace_eq_sum_channels {X Y : C} {ι κ : F.Label → Type*}
    [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (b : ∀ i, Module.Basis (ι i) ℂ (F.simple i ⟶ X))
    (c : ∀ i, Module.Basis (κ i) ℂ (F.simple i ⟶ Y))
    (E : Module.End ℂ (X ⟶ Y)) :
    LinearMap.trace ℂ (X ⟶ Y) E = ∑ i, ∑ a, ∑ d,
      F.scalarTrace X
        (E (F.compositionDual (b i) a ≫ c i d) ≫ F.traceDualBasis (c i) d ≫ b i a) := by
  letI := F.homFinite
  have he : E = ∑ i, ∑ a, ∑ d,
      (F.tracePairing X Y (F.traceDualBasis (c i) d ≫ b i a)).smulRight
        (E (F.compositionDual (b i) a ≫ c i d)) := by
    ext f
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, tracePairing_apply,
      ← map_smul, ← map_sum]
    rw [← F.hom_eq_sum_trace_channels b c f]
  conv_lhs => rw [he]
  simp only [map_sum, LinearMap.trace_smulRight, tracePairing_apply]

/-- Both channel bases use composition-dual reverse maps. The remaining
inverse dimension is exactly the factor appearing in NS Theorem 5.4's proof. -/
theorem linearTrace_eq_sum_normalized_channels {X Y : C} {ι κ : F.Label → Type*}
    [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (b : ∀ i, Module.Basis (ι i) ℂ (F.simple i ⟶ X))
    (c : ∀ i, Module.Basis (κ i) ℂ (F.simple i ⟶ Y))
    (E : Module.End ℂ (X ⟶ Y)) :
    LinearMap.trace ℂ (X ⟶ Y) E = ∑ i, ∑ a, ∑ d,
      (F.dimension (F.simple i))⁻¹ * F.scalarTrace X
        (E (F.compositionDual (b i) a ≫ c i d) ≫ F.compositionDual (c i) d ≫ b i a) := by
  rw [F.linearTrace_eq_sum_channels b c E]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [F.traceDualBasis_eq_inv_smul]
  simp

/-- A concrete finite basis of each simple-source Hom space. -/
def simpleHomBasis (X : C) (i : F.Label) :
    Module.Basis (Fin (Module.finrank ℂ (F.simple i ⟶ X))) ℂ (F.simple i ⟶ X) := by
  letI := F.homFinite
  exact Module.finBasis ℂ _

end SphericalFusion

/-- The simple-channel trace expansion for the genuine central rotation, at every
integer power. The basis hypotheses are ordinary finite-dimensional bases. -/
theorem generalizedIndicatorInt_eq_sum_channels (F : SphericalFusion C)
    (A : Center C) (V : C) (n : ℕ) (l : ℤ) {ι κ : F.Label → Type*}
    [∀ i, Fintype (ι i)] [∀ i, Fintype (κ i)]
    (b : ∀ i, Module.Basis (ι i) ℂ (F.simple i ⟶ A.1))
    (c : ∀ i, Module.Basis (κ i) ℂ (F.simple i ⟶ tensorPower V (n + 1))) :
    generalizedIndicatorInt F.toPivotal A V n l = ∑ i, ∑ a, ∑ d,
      F.scalarTrace A.1
        (((generalizedRotation F.toPivotal A V n) ^ l)
          (F.compositionDual (b i) a ≫ c i d) ≫ F.traceDualBasis (c i) d ≫ b i a) :=
  F.linearTrace_eq_sum_channels b c _

/-- A basis-free statement of the normalized simple-channel indicator expansion:
all bases and inverse-dimension factors are constructed from `F`. -/
theorem generalizedIndicatorInt_eq_sum_simpleChannels (F : SphericalFusion C)
    (A : Center C) (V : C) (n : ℕ) (l : ℤ) :
    generalizedIndicatorInt F.toPivotal A V n l =
      ∑ i, ∑ a, ∑ d, (F.dimension (F.simple i))⁻¹ * F.scalarTrace A.1
        (((generalizedRotation F.toPivotal A V n) ^ l)
          (F.compositionDual (F.simpleHomBasis A.1 i) a ≫
            F.simpleHomBasis (tensorPower V (n + 1)) i d) ≫
          F.compositionDual (F.simpleHomBasis (tensorPower V (n + 1)) i) d ≫
          F.simpleHomBasis A.1 i a) :=
  F.linearTrace_eq_sum_normalized_channels
    (F.simpleHomBasis A.1) (F.simpleHomBasis (tensorPower V (n + 1))) _

end VOA.Huang.NgSchauenburg
