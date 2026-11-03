import VOA.Huang.AssocConverseAnalytic

/-! # Product coefficient uniqueness and converse associativity

The analytic uniqueness theorem is extended from homogeneous matrix coefficients
to all vectors, then applied to finite presentations of tensors. PBW is used
only by the final corollaries to supply a finite family of irreducibles.
-/

namespace VOA.Huang.AssocConverse
open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget
open VOA.Huang.PzTensorHatBridge VOA.Huang.PzTensorY3
open scoped BigOperators TensorProduct

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {P₁ P₂ P₃ P₄ : LWModule W}

/-- Scalar coefficient uniqueness detects the full vector-valued formal
product, by weight decomposition and the separating restricted dual. -/
theorem formal_products_zero_of_values_zero {ι : Type v} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (R : ι → LWModule W)
    (A : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod P₄.isMod)
    (B : ∀ j, IntertwiningOperator P₂.isMod P₃.isMod (R j).isMod)
    (hv : ∀ d : TestData P₁ P₂ P₃ P₄, ∑ j, productValue (A j) (B j) d = 0)
    (p q : ℂ) (x : P₁.carrier) (y : P₂.carrier) (z : P₃.carrier) :
    ∑ j, (A j).val p x ((B j).val q y z) = 0 := by
  classical
  let F : P₁.carrier → P₂.carrier → P₃.carrier → P₄.carrier :=
    fun x y z => ∑ j, (A j).val p x ((B j).val q y z)
  have h1 : ∀ x x' y z, F (x + x') y z = F x y z + F x' y z := by
    intros; simp [F, map_add, Finset.sum_add_distrib]
  have h2 : ∀ x y y' z, F x (y + y') z = F x y z + F x y' z := by
    intros; simp [F, map_add, Finset.sum_add_distrib]
  have h3 : ∀ x y z z', F x y (z + z') = F x y z + F x y z' := by
    intros; simp [F, map_add, Finset.sum_add_distrib]
  have hhom (α₁ α₂ α₃ : ℂ) (x : P₁.carrier) (y : P₂.carrier) (z : P₃.carrier)
      (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
      (hz : z ∈ P₃.isMod.weight α₃) : F x y z = 0 := by
    apply eq_zero_of_supported
    intro h₄ f hf
    let d : TestData P₁ P₂ P₃ P₄ :=
      ⟨α₁, α₂, α₃, h₄, x, y, z, f, hx, hy, hz, hf, 1 / 2, by norm_num, by norm_num⟩
    have hh := product_coefficients_zero_of_values_zero hV i₁ i₂ i₃ i₄ R A B d
      (fun s hs hs' => hv { d with x := s, xpos := hs, xlt := hs' }) p q
    simpa only [F, map_sum, prodCoeff, d] using hh
  have hxy (α : ℂ) (z : P₃.carrier) (hz : z ∈ P₃.isMod.weight α) :
      ∀ x y, F x y z = 0 :=
    eq_zero_of_homog (fun x y => F x y z) (fun x x' y => h1 x x' y z)
      (fun x y y' => h2 x y y' z) (fun a b x y hx hy => hhom a b α x y z hx hy hz)
  change F x y z = 0
  refine Submodule.iSup_induction P₃.isMod.weight (motive := fun z => F x y z = 0)
    (mem_iSup_weight P₃ z) ?_ ?_ ?_
  · intro α z hz; exact hxy α z hz x y
  · simp [F]
  · intro z z' hz hz'; rw [h3, hz, hz', add_zero]

/-- The original analytic residual, with no irreducibility or irredundancy
assumption on the finite intermediate family. Coincident exponents are summed. -/
theorem productCoefficientUniqueness_holds {ι : Type v} [Fintype ι]
    (hV : StronglyRational W) (R : ι → LWModule W) : ProductCoefficientUniqueness hV R := by
  classical
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ t ht
  change productFamilyMap hV i₁ i₂ i₃ i₄ R t = 0 at ht
  change formalProductFamilyMap P₁ P₂ P₃ P₄ R t = 0
  have hrep (j : ι) := TensorProduct.exists_sum_tmul_eq (t j)
  choose n A B hrep using hrep
  let J := (j : ι) × Fin (n j)
  have hv (d : TestData P₁ P₂ P₃ P₄) :
      ∑ s : J, productValue (A s.1 s.2) (B s.1 s.2) d = 0 := by
    have hh := congrFun ht d
    change (∑ j, productTensorMap hV i₁ i₂ i₃ i₄ (R j) (t j)) d = 0 at hh
    simp only [hrep, map_sum, Finset.sum_apply] at hh
    simpa only [J, Fintype.sum_sigma, productTensorMap, TensorProduct.lift.tmul,
      productBilinear, LinearMap.coe_mk, AddHom.coe_mk] using hh
  have hf := formal_products_zero_of_values_zero hV i₁ i₂ i₃ i₄
    (fun s : J => R s.1) (fun s => A s.1 s.2) (fun s => B s.1 s.2) hv
  funext d
  change (∑ j, formalProductTensorMap P₁ P₂ P₃ P₄ (R j) (t j)) d = 0
  simp only [hrep, map_sum, Finset.sum_apply, formalProductTensorMap_tmul]
  simpa only [J, Fintype.sum_sigma] using hf d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- Analytic product channels are faithful for a finite irredundant family. -/
theorem productChannelFaithful_of_irredundant {ι : Type v} [Fintype ι]
    (hV : StronglyRational W) (R : ι → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j) : ProductChannelFaithful hV R :=
  productChannelFaithful_of_coefficient_uniqueness hV R iR hne
    (productCoefficientUniqueness_holds hV R)

theorem associativityConverse_of_completeIrredundantFamily {ι : Type v} [Finite ι]
    (hV : StronglyRational W) (R : ι → LWModule W)
    (hR : CompleteIrredundantFamily R) : AssociativityConverse W := by
  letI := Fintype.ofFinite ι
  exact associativityConverse_of_stronglyRational_faithful hV R hR.1 hR.2.1
    (productChannelFaithful_of_irredundant hV R hR.1 hR.2.2)

theorem associativityBoth_of_completeIrredundantFamily {ι : Type v} [Finite ι]
    (hV : StronglyRational W) (R : ι → LWModule W)
    (hR : CompleteIrredundantFamily R) : AssociativityBoth W := by
  letI := Fintype.ofFinite ι
  exact associativityBoth_of_coefficient_uniqueness hV R hR
    (productCoefficientUniqueness_holds hV R)

/-- PBW enters only through existence of the finite irredundant family. -/
theorem associativityConverse_of_stronglyRational_pbw (hV : StronglyRational W) :
    AssociativityConverse W := by
  obtain ⟨n, R, hR⟩ := exists_completeIrredundantFamily_pbw hV
  exact associativityConverse_of_completeIrredundantFamily hV R hR

/-- Both associativity directions, with the same finite-family PBW dependency. -/
theorem associativityBoth_of_stronglyRational_pbw (hV : StronglyRational W) :
    AssociativityBoth W := by
  obtain ⟨n, R, hR⟩ := exists_completeIrredundantFamily_pbw hV
  exact associativityBoth_of_completeIrredundantFamily hV R hR

end VOA.Huang.AssocConverse
