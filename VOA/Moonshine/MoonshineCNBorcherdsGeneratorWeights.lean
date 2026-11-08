import VOA.Moonshine.MoonshineCNBorcherdsStringAction

/-! Homogeneous components and the Levi module carried by the generating space. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton.BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

/-- The homogeneous piece of U at a string degree is exactly that string component. -/
theorem genSpace_weight_intersection (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (i : borcherdsStringIndex) :
    D.genSpace e ⊓ D.weightSpace (borcherdsStringDegree i) =
      D.generatorString e i.val.1 i.val.2 := by
  let R := ⨆ j : borcherdsStringIndex, ⨆ (_ : j ≠ i), D.generatorString e j.val.1 j.val.2
  have hsplit : D.genSpace e ≤ D.generatorString e i.val.1 i.val.2 ⊔ R := by
    rw [D.genSpace_eq_iSup_strings]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst j; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have hd : Disjoint (D.weightSpace (borcherdsStringDegree i)) R := by
    apply (iSupIndep_def.mp D.weight_internal.submodule_iSupIndep
      (borcherdsStringDegree i)).mono_right
    refine iSup_le fun j => iSup_le fun hji => ?_
    apply le_trans (D.generatorString_le_weight e he j.val.1 j.val.2)
    exact le_iSup_of_le (borcherdsStringDegree j)
      (le_iSup_of_le (fun h => hji (borcherdsStringDegree_injective h)) le_rfl)
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hsum⟩ := Submodule.mem_sup.mp (hsplit hx.1)
    have hbwt : b ∈ D.weightSpace (borcherdsStringDegree i) := by
      have hbx : b = x - a := by rw [← hsum]; abel
      rw [hbx]
      exact Submodule.sub_mem _ hx.2 (D.generatorString_le_weight e he _ _ ha)
    have hb0 : b = 0 := Submodule.disjoint_def.mp hd b hbwt hb
    have hx' : a = x := by simpa [hb0] using hsum
    exact hx' ▸ ha
  · exact le_inf (D.generatorString_le_genSpace e _ i.property.1 _ i.property.2)
      (D.generatorString_le_weight e he _ _)

theorem generatorString_finrank (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (j : ℤ) (hj : 1 ≤ j) (k : ℕ) (hk : (k : ℤ) < j) :
    Module.finrank ℂ (D.generatorString e j k) =
      Module.finrank ℂ (D.weightSpace (borcherdsImaginaryRoot j)) :=
  (D.generatorStringEquiv e f he hf hef j hj k hk).symm.finrank_eq

/-- U is a genuine module for the Levi, with its ambient adjoint action. -/
def genSpaceLeviSubmodule (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    LieSubmodule ℂ D.leviPart g where
  __ := D.genSpace e
  lie_mem {x _u} hu := D.genSpace_levi_stable e f he hf hef x.property hu

/-- BD6 preserves the entire direct sum of strings. -/
theorem genSpace_equivariant {G : Type*} [Group G] (A : D.GAction G)
    (σ : G) (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    {u : g} (hu : u ∈ D.genSpace e) : A.action σ u ∈ D.genSpace e := by
  have hle : D.genSpace e ≤ (D.genSpace e).comap (A.action σ).toLinearMap := by
    refine iSup_le fun j => iSup_le fun hj => iSup_le fun k => iSup_le fun hk => ?_
    rintro _ ⟨v, hv, rfl⟩
    change A.action σ ((LieModule.toEnd ℂ g g e ^ k) v) ∈ D.genSpace e
    rw [D.generatorStringMap_equivariant A σ e he k v]
    exact D.generatorString_le_genSpace e j hj k hk ⟨A.action σ v, A.graded σ _ v hv, rfl⟩
  exact hle hu

end VOA.Moonshine.ConwayNorton.BorcherdsData
