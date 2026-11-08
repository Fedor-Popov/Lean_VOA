import VOA.Moonshine.MoonshineCNBorcherdsCartanWeights
import VOA.Moonshine.MoonshineCNVermaMultiplication
import VOA.Moonshine.MoonshineCNBorcherdsParabolicAction

/-! Cartan weight gradings of modules induced from the opposite parabolic.

An induced module is generated from its bottom by the positive part.  Hence the span of the
eigenspaces with weights in a set closed under adding the positive cone is the whole module as
soon as the bottom lies in it.  This gives admissible gradings on the generalized Verma modules
induced from the trivial module and from the real-root string space U. -/

noncomputable section
open scoped TensorProduct
open Module
namespace VOA.Moonshine.ConwayNorton
namespace BorcherdsData

variable {g W : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup W] [Module ℂ W]
variable (D : BorcherdsData g) (σ : D.parabolicPart →ₗ⁅ℂ⁆ End ℂ W)

theorem cartan_mem_parabolic (ξ : ℂ × ℂ) : D.cartanMap ξ ∈ D.parabolicPart :=
  D.weightSpace_le_weightSpan (P := fun γ => ¬ borcherdsPositiveCone γ)
    (by simp [borcherdsPositiveCone]) (D.cartan_mem_weight_zero ξ)

theorem cartan_mem_levi (ξ : ℂ × ℂ) : D.cartanMap ξ ∈ D.leviPart :=
  D.weightSpace_le_weightSpan (P := borcherdsLeviDegree) (Or.inl rfl)
    (D.cartan_mem_weight_zero ξ)

/-- A subspace of an induced module stable under the positive part is stable under the image of
the whole positive enveloping algebra. -/
theorem inducedPositive_enveloping_stable
    (S : Submodule ℂ (relativeInducedSpace D.parabolicPart σ))
    (hS : ∀ x ∈ D.positivePart, ∀ v ∈ S, relativeInducedRep D.parabolicPart σ x v ∈ S)
    (a : UniversalEnvelopingAlgebra ℂ D.positivePart)
    {v : relativeInducedSpace D.parabolicPart σ} (hv : v ∈ S) :
    relativeInducedAlgebra D.parabolicPart σ
      (UniversalEnvelopingAlgebra.lift ℂ
        ((UniversalEnvelopingAlgebra.ι ℂ).comp D.positivePart.incl) a) v ∈ S := by
  induction a using envelopingAlgebra_induction generalizing v with
  | hscalar c =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply]
      exact S.smul_mem c hv
  | hlie x =>
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact hS x x.property _ hv
  | hmul a b ha hb =>
      rw [map_mul, map_mul, Module.End.mul_apply]
      exact ha (hb hv)
  | hadd a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply]
      exact S.add_mem (ha hv) (hb hv)

/-- An induced module is generated from its bottom by the positive part. -/
theorem inducedSpace_eq_top_of_bottom (S : Submodule ℂ (relativeInducedSpace D.parabolicPart σ))
    (hbot : ∀ w, PBWTheorem.bottom D.parabolicPart σ w ∈ S)
    (hS : ∀ x ∈ D.positivePart, ∀ v ∈ S, relativeInducedRep D.parabolicPart σ x v ∈ S) :
    S = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  obtain ⟨t, rfl⟩ := (D.parabolicVermaMultiplication_bijective σ).2 v
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
      have heq : D.parabolicVermaMultiplication σ (a ⊗ₜ[ℂ] w) =
          relativeInducedAlgebra D.parabolicPart σ
            (UniversalEnvelopingAlgebra.lift ℂ
              ((UniversalEnvelopingAlgebra.ι ℂ).comp D.positivePart.incl) a)
            (PBWTheorem.bottom D.parabolicPart σ w) := by
        change Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.lift ℂ
            ((UniversalEnvelopingAlgebra.ι ℂ).comp D.positivePart.incl) a) ⊗ₜ[ℂ] w) =
          Submodule.Quotient.mk ((UniversalEnvelopingAlgebra.lift ℂ
            ((UniversalEnvelopingAlgebra.ι ℂ).comp D.positivePart.incl) a * 1) ⊗ₜ[ℂ] w)
        rw [mul_one]
      rw [heq]
      exact D.inducedPositive_enveloping_stable σ S hS a (hbot w)
  | add t s ht hs =>
      rw [map_add]
      exact S.add_mem ht hs

/-- The eigenspaces with weights in a set closed under the positive cone span an induced module
once its bottom lies in their span. -/
theorem inducedCartanEigenspace_span (P : ℤ × ℤ → Prop)
    (hP : ∀ μ α, P μ → borcherdsPositiveCone α → P (μ + α))
    (hbot : ∀ w, PBWTheorem.bottom D.parabolicPart σ w ∈
      ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace (relativeInducedRep D.parabolicPart σ) μ) :
    ⨆ μ, ⨆ (_ : P μ), D.cartanEigenspace (relativeInducedRep D.parabolicPart σ) μ = ⊤ :=
  D.inducedSpace_eq_top_of_bottom σ _ hbot (fun _ hx _ hv =>
    D.cartanEigenspace_span_stable _ P borcherdsPositiveCone hP hx hv)

/-- A bottom vector on which the Cartan acts by a weight is a weight vector of that weight. -/
theorem bottom_mem_cartanEigenspace (μ : ℤ × ℤ) (w : W)
    (hw : ∀ ξ, σ ⟨D.cartanMap ξ, D.cartan_mem_parabolic ξ⟩ w =
      borcherdsCartanPairing ξ (borcherdsWeightVector μ) • w) :
    PBWTheorem.bottom D.parabolicPart σ w ∈
      D.cartanEigenspace (relativeInducedRep D.parabolicPart σ) μ := by
  rw [mem_cartanEigenspace]
  intro ξ
  have h := relativeInducedRep_bottom D.parabolicPart σ
    ⟨D.cartanMap ξ, D.cartan_mem_parabolic ξ⟩ w
  rw [hw, map_smul] at h
  exact h

/-! ### The module induced from the trivial representation -/

/-- The trivial one-dimensional representation of the opposite parabolic. -/
abbrev parabolicTrivialRep : D.parabolicPart →ₗ⁅ℂ⁆ End ℂ ℂ := 0

theorem trivialBottom_mem_cartanEigenspace (c : ℂ) :
    PBWTheorem.bottom D.parabolicPart D.parabolicTrivialRep c ∈
      D.cartanEigenspace (relativeInducedRep D.parabolicPart D.parabolicTrivialRep) 0 :=
  D.bottom_mem_cartanEigenspace _ 0 c (fun ξ => by
    simp [borcherdsCartanPairing_weight_zero])

theorem trivialVerma_cartanEigenspace_span :
    ⨆ μ, ⨆ (_ : μ = 0 ∨ borcherdsPositiveCone μ),
      D.cartanEigenspace (relativeInducedRep D.parabolicPart D.parabolicTrivialRep) μ = ⊤ := by
  apply D.inducedCartanEigenspace_span _ _ (fun μ α hμ hα => ?_) (fun c => ?_)
  · rcases hμ with rfl | hμ
    · exact Or.inr (by simpa using hα)
    · exact Or.inr (borcherdsPositiveCone_add hμ hα)
  · exact Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem (Or.inl rfl)
      (D.trivialBottom_mem_cartanEigenspace c))

/-- The admissible weight grading of the module induced from the trivial representation. -/
def trivialVermaAdmissible :
    BorcherdsAdmissible D (relativeInducedRep D.parabolicPart D.parabolicTrivialRep) :=
  D.cartanAdmissible _ 0 (fun μ => μ = 0 ∨ borcherdsPositiveCone μ)
    (fun μ hμ => by
      rcases hμ with rfl | hμ
      · simp [borcherdsRootHeight]
      · simp only [borcherdsPositiveCone, borcherdsRootHeight] at hμ ⊢
        omega)
    D.trivialVerma_cartanEigenspace_span

/-! ### The module induced from the real-root string space -/

variable (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
  (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)

/-- A property of bottom vectors of the generating space holds once it holds on every
homogeneous string vector. -/
theorem generatorBottom_mem_of_strings
    (X : Submodule ℂ
      (relativeInducedSpace D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)))
    (hX : ∀ (i : borcherdsStringIndex) (u : g) (hu : u ∈ D.genSpace e),
      u ∈ D.generatorString e i.val.1 i.val.2 →
        PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩ ∈ X)
    (w : D.genSpace e) :
    PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) w ∈ X := by
  suffices h : ∀ u (_ : u ∈ ⨆ i : borcherdsStringIndex, D.generatorString e i.val.1 i.val.2)
      (hu : u ∈ D.genSpace e),
      PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩ ∈ X by
    obtain ⟨u, hu⟩ := w
    exact h u (by rwa [← D.genSpace_eq_iSup_strings]) hu
  intro u hu'
  induction hu' using Submodule.iSup_induction' with
  | mem i u hu => exact fun hu' => hX i u hu' hu
  | zero =>
      intro hu
      have h0 : (⟨0, hu⟩ : D.genSpace e) = 0 := rfl
      rw [h0, map_zero]
      exact X.zero_mem
  | add x y hx hy ihx ihy =>
      intro hu
      have hxU : x ∈ D.genSpace e := by rw [D.genSpace_eq_iSup_strings]; exact hx
      have hyU : y ∈ D.genSpace e := by rw [D.genSpace_eq_iSup_strings]; exact hy
      have hsum : (⟨x + y, hu⟩ : D.genSpace e) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [hsum, map_add]
      exact X.add_mem (ihx hxU) (ihy hyU)

/-- A homogeneous vector of U gives a bottom weight vector of the same weight. -/
theorem generatorBottom_mem_cartanEigenspace (γ : ℤ × ℤ) (u : g) (hu : u ∈ D.genSpace e)
    (hγ : u ∈ D.weightSpace γ) :
    PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) ⟨u, hu⟩ ∈
      D.cartanEigenspace
        (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) γ := by
  apply D.bottom_mem_cartanEigenspace _ γ
  intro ξ
  apply Subtype.ext
  have h := D.genSpaceParabolicRep_levi e f he hf hef ⟨D.cartanMap ξ, D.cartan_mem_levi ξ⟩
    ⟨u, hu⟩
  refine h.trans ?_
  rw [D.cartan_action ξ γ u hγ]
  rfl

theorem generatorBottom_mem_positive_span (w : D.genSpace e) :
    PBWTheorem.bottom D.parabolicPart (D.genSpaceParabolicRep e f he hf hef) w ∈
      ⨆ μ, ⨆ (_ : borcherdsPositiveCone μ), D.cartanEigenspace
        (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) μ := by
  apply D.generatorBottom_mem_of_strings e f he hf hef
  intro i u hu hs
  exact Submodule.mem_iSup_of_mem (borcherdsStringDegree i)
    (Submodule.mem_iSup_of_mem (by
      obtain ⟨h1, h2⟩ := i.property
      simp only [borcherdsStringDegree, borcherdsPositiveCone]
      constructor <;> omega)
      (D.generatorBottom_mem_cartanEigenspace e f he hf hef _ u hu
        (D.generatorString_le_weight e he _ _ hs)))

theorem generatorVerma_cartanEigenspace_span :
    ⨆ μ, ⨆ (_ : borcherdsPositiveCone μ), D.cartanEigenspace
      (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) μ = ⊤ :=
  D.inducedCartanEigenspace_span _ borcherdsPositiveCone
    (fun _ _ hμ hα => borcherdsPositiveCone_add hμ hα)
    (D.generatorBottom_mem_positive_span e f he hf hef)

/-- The admissible weight grading of the module induced from U; all weights lie in the cone. -/
def generatorVermaAdmissible :
    BorcherdsAdmissible D
      (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) :=
  D.cartanAdmissible _ 2 borcherdsPositiveCone
    (fun μ hμ => by
      simp only [borcherdsPositiveCone, borcherdsRootHeight] at hμ ⊢
      omega)
    (D.generatorVerma_cartanEigenspace_span e f he hf hef)

theorem generatorVerma_weight_eq_bot {μ : ℤ × ℤ} (hμ : ¬ borcherdsPositiveCone μ) :
    D.cartanEigenspace
      (relativeInducedRep D.parabolicPart (D.genSpaceParabolicRep e f he hf hef)) μ = ⊥ :=
  D.cartanEigenspace_eq_bot_of_span _ _ (D.generatorVerma_cartanEigenspace_span e f he hf hef) hμ

end BorcherdsData
end VOA.Moonshine.ConwayNorton
