import VOA.Moonshine.MoonshineLRGenerationCone
import VOA.Moonshine.MoonshineCNBorcherdsTensorEnveloping
import VOA.Moonshine.MoonshineCNBorcherdsGeneratorWeights

/-!
# The PBW character of `𝔲⁺` for Borcherds data

For `BorcherdsData D` and a normalised real pair `e, f`:
* `positiveWeight D`: the `ℕ × ℕ`-grading of `𝔲⁺ = D.positivePart`, pulled back from `D.weightSpace`
  along `(m, n) ↦ (m, n)`; it is internal, finite-dimensional, supported in the open cone and
  compatible with brackets;
* `positiveGenWeight D e`: the induced grading of the generating space `U`;
* **`positivePart_coneProd_mul_one_sub`**:
  `Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim 𝔲⁺_(m,n)} · (1 − Σ dim U_(a,b) pᵃ q^b) = 1`
  (blueprint: the PBW character identity in `MOON_BKM`), from
  `positiveTensorGeneratorToEnveloping_bijective`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open Module

/-- `(m, n) ↦ (m, n) ∈ ℤ × ℤ`. -/
def natWeight (γ : ℕ × ℕ) : ℤ × ℤ := ((γ.1 : ℤ), (γ.2 : ℤ))

theorem natWeight_add (γ δ : ℕ × ℕ) : natWeight (γ + δ) = natWeight γ + natWeight δ := by
  simp only [natWeight, Prod.fst_add, Prod.snd_add, Nat.cast_add, Prod.mk_add_mk]

theorem natWeight_injective : Function.Injective natWeight := by
  intro γ δ h
  simp only [natWeight, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext h.1 h.2

theorem natWeight_toNat {γ : ℤ × ℤ} (hγ : borcherdsPositiveCone γ) :
    natWeight (γ.1.toNat, γ.2.toNat) = γ := by
  obtain ⟨h1, h2⟩ := hγ
  simp only [natWeight]
  ext <;> simp <;> omega

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

/-- The `ℕ × ℕ`-grading of `𝔲⁺`. -/
def positiveWeight (γ : ℕ × ℕ) : Submodule ℂ D.positivePart :=
  (D.weightSpace (natWeight γ)).comap D.positivePart.toSubmodule.subtype

theorem positivePart_le_iSup :
    D.positivePart.toSubmodule ≤
      ⨆ γ : ℕ × ℕ, D.positivePart.toSubmodule ⊓ D.weightSpace (natWeight γ) := by
  change D.weightSpan borcherdsPositiveCone ≤ _
  refine iSup₂_le fun γ hγ => le_iSup_of_le (γ.1.toNat, γ.2.toNat) ?_
  rw [natWeight_toNat hγ]
  exact le_inf (le_iSup₂_of_le γ hγ le_rfl : D.weightSpace γ ≤ D.weightSpan borcherdsPositiveCone)
    le_rfl

theorem isInternal_positiveWeight : DirectSum.IsInternal (positiveWeight D) :=
  isInternal_comap_of_le_iSup_inf
    (D.weight_internal.submodule_iSupIndep.comp natWeight_injective) _ (positivePart_le_iSup D)

noncomputable instance : DirectSum.Decomposition (positiveWeight D) :=
  (isInternal_positiveWeight D).chooseDecomposition

instance (γ : ℕ × ℕ) : FiniteDimensional ℂ (positiveWeight D γ) := by
  haveI := D.weight_finite (natWeight γ)
  exact Module.Finite.of_injective
    ((D.positivePart.toSubmodule.subtype ∘ₗ (positiveWeight D γ).subtype).codRestrict
      (D.weightSpace (natWeight γ)) fun x => x.2)
    fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h'
      exact Subtype.ext (Subtype.ext h')

theorem positiveWeight_cone (γ : ℕ × ℕ) (hne : positiveWeight D γ ≠ ⊥) :
    1 ≤ γ.1 ∧ 1 ≤ γ.2 := by
  by_contra hγ
  apply hne
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hx1 : (x : g) ∈ D.weightSpace (natWeight γ) := hx
  have hx2 : (x : g) ∈ ⨆ (j : ℤ × ℤ) (_ : j ≠ natWeight γ), D.weightSpace j := by
    have hxP : (x : g) ∈ D.weightSpan borcherdsPositiveCone := x.2
    have hle : D.weightSpan borcherdsPositiveCone ≤
        ⨆ (j : ℤ × ℤ) (_ : j ≠ natWeight γ), D.weightSpace j := by
      refine iSup₂_le fun j hj => le_iSup₂_of_le
        (f := fun (j : ℤ × ℤ) (_ : j ≠ natWeight γ) => D.weightSpace j) j ?_ le_rfl
      intro h
      subst h
      simp only [borcherdsPositiveCone, natWeight] at hj
      omega
    exact hle hxP
  exact Subtype.ext (Submodule.disjoint_def.mp
    (D.weight_internal.submodule_iSupIndep (natWeight γ)) _ hx1 hx2)

theorem positiveWeight_bracket {γ δ : ℕ × ℕ} {x y : D.positivePart}
    (hx : x ∈ positiveWeight D γ) (hy : y ∈ positiveWeight D δ) :
    ⁅x, y⁆ ∈ positiveWeight D (γ + δ) := by
  change ((⁅x, y⁆ : D.positivePart) : g) ∈ D.weightSpace (natWeight (γ + δ))
  rw [LieSubalgebra.coe_bracket, natWeight_add]
  exact D.bracket_weight hx hy

/-- The induced grading of the generating space `U ⊆ 𝔲⁺`. -/
def positiveGenWeight (e : g) (γ : ℕ × ℕ) : Submodule ℂ (D.positiveGeneratorSpace e) :=
  (positiveWeight D γ).comap (D.positiveGeneratorSpace e).subtype

theorem positiveGenerator_le_iSup (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    D.positiveGeneratorSpace e ≤
      ⨆ γ : ℕ × ℕ, D.positiveGeneratorSpace e ⊓ positiveWeight D γ := by
  intro x hx
  have hxg : (x : g) ∈ D.genSpace e := hx
  rw [D.genSpace_eq_iSup_strings] at hxg
  have hle : (⨆ i : borcherdsStringIndex, D.generatorString e i.val.1 i.val.2) ≤
      (⨆ γ : ℕ × ℕ, D.positiveGeneratorSpace e ⊓ positiveWeight D γ).map
        D.positivePart.toSubmodule.subtype := by
    refine iSup_le fun i => ?_
    intro v hv
    have hvU : v ∈ D.genSpace e :=
      D.generatorString_le_genSpace e i.val.1 i.property.1 i.val.2 i.property.2 hv
    have hvP : v ∈ D.positivePart.toSubmodule := D.genSpace_le_positive e he hvU
    refine ⟨⟨v, hvP⟩, ?_, rfl⟩
    refine Submodule.mem_iSup_of_mem (1 + i.val.2, (i.val.1 - i.val.2).toNat)
      (Submodule.mem_inf.mpr ⟨hvU, ?_⟩)
    change v ∈ D.weightSpace (natWeight (1 + i.val.2, (i.val.1 - i.val.2).toNat))
    have hw := D.generatorString_le_weight e he i.val.1 i.val.2 hv
    have hk := i.property.2
    rwa [show natWeight (1 + i.val.2, (i.val.1 - i.val.2).toNat) =
        (1 + (i.val.2 : ℤ), i.val.1 - (i.val.2 : ℤ)) by
      refine Prod.ext ?_ ?_
      · simp [natWeight]
      · exact Int.toNat_of_nonneg (by omega)]
  obtain ⟨y, hy, hyx⟩ := hle hxg
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

theorem isInternal_positiveGenWeight (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    DirectSum.IsInternal (positiveGenWeight D e) :=
  isInternal_comap_of_le_iSup_inf (isInternal_positiveWeight D).submodule_iSupIndep _
    (positiveGenerator_le_iSup D e he)

instance (e : g) (γ : ℕ × ℕ) : FiniteDimensional ℂ (positiveGenWeight D e γ) :=
  Module.Finite.of_injective
    (((D.positiveGeneratorSpace e).subtype ∘ₗ (positiveGenWeight D e γ).subtype).codRestrict
      (positiveWeight D γ) fun x => x.2)
    fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h'
      exact Subtype.ext (Subtype.ext h')

/-- **The PBW character of `𝔲⁺` (blueprint: the character identity in `MOON_BKM`) for Borcherds
data:**
`Π_{m,n ≥ 1} (1 − pᵐ qⁿ)^{−dim 𝔲⁺_(m,n)} · (1 − Σ dim U_(a,b) pᵃ q^b) = 1`. -/
theorem positivePart_coneProd_mul_one_sub (e f : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    coneProd (fun m n => -(finrank ℂ (positiveWeight D (m, n)) : ℂ)) *
      (1 - finrankSeries (positiveGenWeight D e)) = 1 := by
  letI := (isInternal_positiveGenWeight D e he).chooseDecomposition
  exact coneProd_finrank_mul_one_sub_finrankSeries (positiveWeight D) (positiveWeight_cone D)
    (positiveWeight_bracket D) (D.positiveTensorGeneratorToEnveloping_bijective e f he hf hef)
    (positiveGenWeight D e) (fun _ _ hx => hx)

end VOA.Moonshine.ConwayNorton.M8
