import VOA.Huang.TensorCatFivePoint

/-! # Actual analytic channels factor through the chosen fusion products

The equality with the existing library four-point functions is proved by
reindexing the intermediate-weight sum. Off-spectrum coefficients vanish by
weight conservation. Thus the evaluation used by the naturality bridge is
tied to the proved analytic theorem, including its positive-real branch.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.AssocConverse
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- The irreducible-module tests are exactly tests of the bundled ordinary objects. -/
def ordinaryTest (d : TestData P₁ P₂ P₃ P₄) :
    FourPointTest (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod) :=
  ⟨d.α₁, d.α₂, d.α₃, d.h₄, d.w₁, d.w₂, d.w₃, d.f,
    d.hw₁, d.hw₂, d.hw₃, d.hf, d.x, d.xpos, d.xlt⟩

/-- Every ordinary test on these four LW objects comes from an irreducible-module test. -/
theorem ordinaryTest_surjective : Function.Surjective
    (ordinaryTest (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (P₄ := P₄)) := by
  intro d
  exact ⟨⟨d.α, d.β, d.γ, d.δ, d.x, d.y, d.z, d.functional,
    d.hx, d.hy, d.hz, d.supported, d.coordinate, d.positive, d.less_one⟩, rfl⟩

theorem weight_progression_injective (h : ℂ) :
    Function.Injective (fun n : ℕ => h + (n : ℂ)) := by
  intro m n he
  exact Nat.cast_injective (add_left_cancel he)

/-- No nonzero inner coefficient has an intermediate weight outside the LW spectrum. -/
theorem inner_mode_zero_off_spectrum {X Y : Ordinary W}
    (B : IntertwiningOperator X.isMod Y.isMod Q.isMod)
    {α β w : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight β)
    (hw : w ∉ Set.range (fun n : ℕ => Q.h + (n : ℂ))) :
    B.val (α + β - w - 1) x y = 0 := by
  have hm := FusionTop.mem_weight B.property hx hy (α + β - w - 1)
  rw [show α + β - (α + β - w - 1) - 1 = w by ring] at hm
  by_contra hn
  have hb : Q.isMod.weight w ≠ ⊥ := fun hb => hn (by
    rw [hb, Submodule.mem_bot] at hm
    exact hm)
  obtain ⟨n, hn⟩ := Q.isLow w hb
  exact hw ⟨n, hn.symm⟩

/-- Factor the inner channel of an iterate through the genuine universal intertwiner. -/
def representedIterate (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) :
    IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod) :=
  restrictInputs ((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift Q.isMod B)
    (𝟙 (Ordinary.of P₃.isMod)) A

/-- Factor the inner channel of a product through the genuine universal intertwiner. -/
def representedProduct (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod) :
    ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod) :=
  restrictInputs (𝟙 (Ordinary.of P₁.isMod))
    ((F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).lift Q.isMod B) A

theorem representedIterate_term (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (w : ℂ) :
    iterateWeightTerm F (representedIterate F A B) (ordinaryTest d) w =
      d.f (A.val (w + d.α₃ - d.h₄ - 1)
        (B.val (d.α₁ + d.α₂ - w - 1) d.w₁ d.w₂) d.w₃) *
          (d.x : ℂ) ^ (w - d.α₁ - d.α₂) := by
  have he := congrArg (fun I : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod =>
    I.val (d.α₁ + d.α₂ - w - 1) d.w₁ d.w₂)
      ((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift_spec Q.isMod B)
  exact congrArg (fun b : Q.carrier =>
    d.f (A.val (w + d.α₃ - d.h₄ - 1) b d.w₃) *
      (d.x : ℂ) ^ (w - d.α₁ - d.α₂)) he

theorem representedProduct_term (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (w : ℂ) :
    productWeightTerm F (representedProduct F A B) (ordinaryTest d) w =
      d.f (A.val (d.α₁ + w - d.h₄ - 1) d.w₁
        (B.val (d.α₂ + d.α₃ - w - 1) d.w₂ d.w₃)) *
          (1 + (d.x : ℂ)) ^ (d.h₄ - d.α₁ - w) := by
  have he := congrArg (fun I : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod =>
    I.val (d.α₂ + d.α₃ - w - 1) d.w₂ d.w₃)
      ((F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).lift_spec Q.isMod B)
  exact congrArg (fun b : Q.carrier =>
    d.f (A.val (d.α₁ + w - d.h₄ - 1) d.w₁ b) *
      (1 + (d.x : ℂ)) ^ (d.h₄ - d.α₁ - w)) he

theorem representedIterate_term_level (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (n : ℕ) :
    iterateWeightTerm F (representedIterate F A B) (ordinaryTest d) (Q.h + n) =
      AssocConverse.iterateTerm A B d n := by
  rw [representedIterate_term]
  simp only [AssocConverse.iterateTerm, iterCoeff, Complex.one_cpow, mul_one]
  ring_nf

theorem representedProduct_term_level (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (n : ℕ) :
    productWeightTerm F (representedProduct F A B) (ordinaryTest d) (Q.h + n) =
      AssocConverse.productTerm A B d n := by
  rw [representedProduct_term]
  simp only [AssocConverse.productTerm, prodCoeff, Complex.one_cpow, mul_one]
  ring_nf

theorem representedIterate_term_off_spectrum
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (w : ℂ)
    (hw : w ∉ Set.range (fun n : ℕ => Q.h + (n : ℂ))) :
    iterateWeightTerm F (representedIterate F A B) (ordinaryTest d) w = 0 := by
  rw [representedIterate_term]
  erw [inner_mode_zero_off_spectrum (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      B d.hw₁ d.hw₂ hw]
  simp

theorem representedProduct_term_off_spectrum
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod)
    (d : TestData P₁ P₂ P₃ P₄) (w : ℂ)
    (hw : w ∉ Set.range (fun n : ℕ => Q.h + (n : ℂ))) :
    productWeightTerm F (representedProduct F A B) (ordinaryTest d) w = 0 := by
  rw [representedProduct_term]
  erw [inner_mode_zero_off_spectrum (X := Ordinary.of P₂.isMod) (Y := Ordinary.of P₃.isMod)
      B d.hw₂ d.hw₃ hw]
  simp

/-- Exact identification with the existing analytic iterate value. -/
theorem representedIterate_evaluation (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    iterateEvaluation F (representedIterate F A B) (ordinaryTest d) =
      AssocConverse.iterateValue A B d := by
  rw [iterateEvaluation, ← (weight_progression_injective Q.h).tsum_eq]
  · exact tsum_congr (representedIterate_term_level F A B d)
  · intro w hw
    by_contra hn
    exact hw (representedIterate_term_off_spectrum F A B d w hn)

/-- Exact identification with the existing analytic product value. -/
theorem representedProduct_evaluation (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    productEvaluation F (representedProduct F A B) (ordinaryTest d) =
      AssocConverse.productValue A B d := by
  rw [productEvaluation, ← (weight_progression_injective Q.h).tsum_eq]
  · exact tsum_congr (representedProduct_term_level F A B d)
  · intro w hw
    by_contra hn
    exact hw (representedProduct_term_off_spectrum F A B d w hn)

/-- Genuine summability of a represented iterate channel, with no ordinary
evaluation input. External irreducibility is explicit; the middle LW module
need not be irreducible. -/
theorem representedIterate_summable (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (A : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod)
    (B : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (iterateWeightTerm F (representedIterate F A B) (ordinaryTest d)) := by
  apply (weight_progression_injective Q.h).summable_iff
    (representedIterate_term_off_spectrum F A B d) |>.mp
  simpa only [Function.comp_def, representedIterate_term_level] using
    AssocConverse.summable_iterateTerm hV i₁ i₂ i₃ i₄ A B d

theorem representedProduct_summable (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (A : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod)
    (B : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (productWeightTerm F (representedProduct F A B) (ordinaryTest d)) := by
  apply (weight_progression_injective Q.h).summable_iff
    (representedProduct_term_off_spectrum F A B d) |>.mp
  simpa only [Function.comp_def, representedProduct_term_level] using
    AssocConverse.summable_productTerm hV i₁ i₂ i₃ i₄ A B d

end VOA.Huang.TensorCat
