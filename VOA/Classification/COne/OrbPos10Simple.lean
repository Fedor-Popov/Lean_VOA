import VOA.Classification.COne.OrbPos10Quotient

/-! # Simple quotients from finite endomorphism spaces

This is the finite-length argument expressed by a decreasing natural-number
measure. It only needs split underlying monomorphisms and finite Hom spaces.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos10
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open VOA.Huang.HKLRational OrbPos9
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [Linear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A]

omit [MonoidalCategory C] [MonoidalPreadditive C] in
/-- A nonzero kernel makes the endomorphism dimension of a split quotient
strictly smaller. No simplicity or algebra action is used in this estimate. -/
theorem end_finrank_lt_of_split_quotient {Y X Z : C} (f : Y ⟶ X) (hf : f ≠ 0)
    (p : X ⟶ Z) (s : Z ⟶ X) (hs : s ≫ p = 𝟙 Z) (hfp : f ≫ p = 0) :
    Module.finrank ℂ (Z ⟶ Z) < Module.finrank ℂ (X ⟶ X) := by
  let L : (Z ⟶ Z) →ₗ[ℂ] (X ⟶ X) :=
    { toFun := fun t => p ≫ t ≫ s
      map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by intros; simp }
  have hi : Function.Injective L := by
    intro t t' he
    have := congrArg (fun k => s ≫ k ≫ p) he
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, Category.assoc,
      reassoc_of% hs, hs, Category.comp_id, Category.id_comp] using this
  have hn : ¬ Function.Surjective L := by
    intro he
    obtain ⟨t, ht⟩ := he (𝟙 X)
    apply hf
    have := congrArg (fun k => f ≫ k) ht
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, ← Category.assoc,
      hfp, zero_comp, Category.comp_id] using this.symm
  have hle := LinearMap.finrank_le_finrank_of_injective hi
  exact lt_of_le_of_ne hle (fun he => hn
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mp hi))

/-- Every nonzero algebra module has a simple quotient in a Hom-finite split
abelian monoidal category. The quotient map is an epimorphism. -/
theorem exists_simple_quotient
    (split : ∀ {Y X : C} (f : Y ⟶ X), Mono f → ∃ r : X ⟶ Y, f ≫ r = 𝟙 Y)
    (X : C) (aX : A ⊗ X ⟶ X) (hX : IsLeftAct aX) (hne : 𝟙 X ≠ 0) :
    ∃ Q : SimpleAction A, ∃ q : X ⟶ Q.obj, IsLinear aX Q.act q ∧ Epi q := by
  classical
  generalize hd : Module.finrank ℂ (X ⟶ X) = d
  induction d using Nat.strong_induction_on generalizing X with
  | h d ih =>
    by_cases hsimple : ∀ (Y : C) (aY : A ⊗ Y ⟶ Y), IsLeftAct aY →
        ∀ f : Y ⟶ X, IsLinear aY aX f → Mono f → f = 0 ∨ IsIso f
    · exact ⟨⟨X, aX, hX, hne, hsimple⟩, 𝟙 X, isLinear_id aX, inferInstance⟩
    · push Not at hsimple
      obtain ⟨Y, aY, hY, f, hf, hm, hf0, hfi⟩ := hsimple
      letI := hm
      obtain ⟨r, hr⟩ := split f hm
      obtain ⟨aZ, hZ, hp, s, hs⟩ := cokernel_action aY aX hX f hf r hr
      have hnZ : 𝟙 (cokernel f) ≠ 0 := by
        intro hz
        have hp0 : cokernel.π f = 0 := by
          rw [← Category.comp_id (cokernel.π f), hz, comp_zero]
        letI := Abelian.epi_of_cokernel_π_eq_zero f hp0
        exact hfi (isIso_of_mono_of_epi f)
      have hlt : Module.finrank ℂ (cokernel f ⟶ cokernel f) < d := by
        rw [← hd]
        exact end_finrank_lt_of_split_quotient f hf0 (cokernel.π f) s hs
          (cokernel.condition f)
      obtain ⟨Q, q, hq, he⟩ := ih _ hlt (cokernel f) aZ hZ hnZ rfl
      letI := he
      exact ⟨Q, cokernel.π f ≫ q, isLinear_comp hp hq, inferInstance⟩

end VOA.Classification.COne.OrbPos10
