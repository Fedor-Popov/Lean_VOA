import VOA.Moonshine.MoonshineLRGenerationQuotient

/-!
# The radical of the form on `G` and the quotient `G / R`

For Borcherds pre-data `P` on `g`, let `G = P.simpleSpan` and `R` the radical of the form on `G`
(`simpleRadical`, a Lie ideal). It is homogeneous (`decompose_mem_simpleRadical`), so
`𝔤 := G ⧸ R` is graded by the images `quotientWeight γ` (`isInternal_quotientWeight`), and the
form descends (`quotientForm`).
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open Module

namespace BorcherdsPreData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (P : BorcherdsPreData g)

/-- The form restricted to `G`. -/
def simpleForm : LinearMap.BilinForm ℂ P.simpleSpan :=
  P.form.compl₁₂ P.simpleSpan.toSubmodule.subtype P.simpleSpan.toSubmodule.subtype

@[simp] theorem simpleForm_apply (x y : P.simpleSpan) :
    P.simpleForm x y = P.form (x : g) (y : g) := rfl

/-- The radical of the form on `G`, a Lie ideal of `G`. -/
def simpleRadical : LieIdeal ℂ P.simpleSpan where
  carrier := {x | ∀ y, P.simpleForm x y = 0}
  add_mem' {a b} ha hb y := by
    simp only [Set.mem_setOf_eq, map_add, LinearMap.add_apply] at ha hb ⊢
    rw [ha y, hb y, add_zero]
  zero_mem' y := by simp
  smul_mem' c x hx y := by
    simp only [Set.mem_setOf_eq, map_smul, LinearMap.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx y, mul_zero]
  lie_mem {z x} hx y := by
    have h := hx ⁅z, y⁆
    simp only [simpleForm_apply, LieSubalgebra.coe_bracket] at h ⊢
    rw [← lie_skew, map_neg, LinearMap.neg_apply, P.form_invariant, h, neg_zero]

theorem mem_simpleRadical {x : P.simpleSpan} :
    x ∈ P.simpleRadical ↔ ∀ y : P.simpleSpan, P.form (x : g) (y : g) = 0 := Iff.rfl

noncomputable instance : DirectSum.Decomposition P.simpleSpanWeight :=
  P.isInternal_simpleSpanWeight.chooseDecomposition

instance (γ : ℤ × ℤ) : FiniteDimensional ℂ (P.simpleSpanWeight γ) := by
  haveI := P.weight_finite γ
  exact Module.Finite.of_injective
    ((P.simpleSpan.toSubmodule.subtype ∘ₗ (P.simpleSpanWeight γ).subtype).codRestrict
      (P.weightSpace γ) fun x => x.2)
    fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply] at h'
      exact Subtype.ext (Subtype.ext h')

theorem simpleForm_orthogonal (γ δ : ℤ × ℤ) (h : γ + δ ≠ 0) :
    ∀ x ∈ P.simpleSpanWeight γ, ∀ y ∈ P.simpleSpanWeight δ, P.simpleForm x y = 0 :=
  fun _ hx _ hy => P.form_orthogonal γ δ h _ hx _ hy

/-- **The radical is homogeneous.** -/
theorem decompose_mem_simpleRadical {x : P.simpleSpan} (hx : x ∈ P.simpleRadical)
    (γ : ℤ × ℤ) : (DirectSum.decompose P.simpleSpanWeight x γ : P.simpleSpan) ∈
      P.simpleRadical := by
  intro y
  rw [form_decompose_eq P.simpleSpanWeight P.simpleForm P.simpleForm_orthogonal]
  exact hx _

/-- An element of `G_γ` orthogonal to `G_{−γ}` lies in the radical. -/
theorem mem_simpleRadical_of_orthogonal {γ : ℤ × ℤ} {x : P.simpleSpan}
    (hx : x ∈ P.simpleSpanWeight γ)
    (h : ∀ y ∈ P.simpleSpanWeight (-γ), P.simpleForm x y = 0) : x ∈ P.simpleRadical := by
  intro y
  have hxγ : (DirectSum.decompose P.simpleSpanWeight x γ : P.simpleSpan) = x :=
    DirectSum.decompose_of_mem_same _ hx
  rw [← hxγ, form_decompose_eq P.simpleSpanWeight P.simpleForm P.simpleForm_orthogonal]
  exact h _ (Submodule.coe_mem _)

/-! ### The quotient -/

/-- `𝔤 = G ⧸ R`. -/
abbrev simpleQuotient : Type _ := P.simpleSpan ⧸ P.simpleRadical

/-- The quotient map as a Lie algebra map. -/
def quotientMap : P.simpleSpan →ₗ⁅ℂ⁆ P.simpleQuotient :=
  { (LieSubmodule.Quotient.mk' P.simpleRadical : P.simpleSpan →ₗ[ℂ] P.simpleQuotient) with
    map_lie' := fun {_ _} => rfl }

@[simp] theorem quotientMap_apply (x : P.simpleSpan) :
    P.quotientMap x = LieSubmodule.Quotient.mk x := rfl

theorem quotientMap_surjective : Function.Surjective P.quotientMap :=
  LieSubmodule.Quotient.surjective_mk' _

theorem quotientMap_eq_zero {x : P.simpleSpan} : P.quotientMap x = 0 ↔ x ∈ P.simpleRadical :=
  LieSubmodule.Quotient.mk_eq_zero _

/-- The grading of `𝔤`. -/
def quotientWeight (γ : ℤ × ℤ) : Submodule ℂ P.simpleQuotient :=
  (P.simpleSpanWeight γ).map (P.quotientMap : P.simpleSpan →ₗ[ℂ] P.simpleQuotient)

theorem isInternal_quotientWeight : DirectSum.IsInternal P.quotientWeight :=
  isInternal_map_mkQ P.simpleSpanWeight (P.simpleRadical : Submodule ℂ P.simpleSpan)
    fun _ hx γ => P.decompose_mem_simpleRadical hx γ

/-! ### The descended form -/

/-- The form in the first variable descends. -/
def quotientFormLeft : P.simpleQuotient →ₗ[ℂ] P.simpleSpan →ₗ[ℂ] ℂ :=
  (P.simpleRadical : Submodule ℂ P.simpleSpan).liftQ P.simpleForm fun _ hx =>
    LinearMap.mem_ker.mpr (LinearMap.ext fun y => hx y)

theorem quotientFormLeft_mk (x y : P.simpleSpan) :
    P.quotientFormLeft (LieSubmodule.Quotient.mk x) y = P.simpleForm x y := rfl

/-- **The descended form** on `𝔤 = G ⧸ R`. -/
def quotientForm : LinearMap.BilinForm ℂ P.simpleQuotient :=
  ((P.simpleRadical : Submodule ℂ P.simpleSpan).liftQ P.quotientFormLeft.flip fun r hr => by
    refine LinearMap.mem_ker.mpr (LinearMap.ext fun q => ?_)
    obtain ⟨x, rfl⟩ := P.quotientMap_surjective q
    change P.simpleForm x r = 0
    rw [simpleForm_apply, P.form_symmetric]
    exact hr x).flip

@[simp] theorem quotientForm_mk (x y : P.simpleSpan) :
    P.quotientForm (LieSubmodule.Quotient.mk x) (LieSubmodule.Quotient.mk y) =
      P.form (x : g) (y : g) := rfl

end BorcherdsPreData

end VOA.Moonshine.ConwayNorton.M8
