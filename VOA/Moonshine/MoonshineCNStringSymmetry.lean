import VOA.Moonshine.MoonshineCNStringQuotient

/-! # Symmetries of the abstract no-ghost quotient

Every string-module group action restricts to the derived spaces and descends
to their form quotients. The two transverse identifications intertwine these
actual quotient actions.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.StringGroupAction

universe u v
variable {H : Type u} [AddCommGroup H] [Module ℂ H]
  {M : StringModule H} {G : Type v} [Group G] (A : StringGroupAction M G)

theorem action_preserves_spurious (g : G) (x : H) (hx : x ∈ M.spurious) :
    A.action g x ∈ M.spurious := by
  apply (show M.spurious ≤ M.spurious.comap (A.action g).toLinearMap from ?_) hx
  apply iSup_le
  intro n y hy
  obtain ⟨z, rfl⟩ := hy
  change A.action g (M.L _ z) ∈ M.spurious
  rw [A.commutes_L]
  exact M.negative_L_mem_spurious n _

theorem action_preserves_kSpurious (g : G) (x : H) (hx : x ∈ M.kSpurious) :
    A.action g x ∈ M.kSpurious := by
  apply (show M.kSpurious ≤ M.kSpurious.comap (A.action g).toLinearMap from ?_) hx
  apply iSup_le
  intro n y hy
  obtain ⟨z, rfl⟩ := hy
  change A.action g (M.K _ z) ∈ M.kSpurious
  rw [A.commutes_K]
  exact M.negative_K_mem_kSpurious n _

theorem action_preserves_physical (g : G) (x : H) (hx : x ∈ M.physical) :
    A.action g x ∈ M.physical := by
  rw [M.mem_physical_iff] at hx ⊢
  intro n
  rw [← A.commutes_L, hx, map_zero]

theorem action_preserves_kVacuum (g : G) (x : H) (hx : x ∈ M.kVacuum) :
    A.action g x ∈ M.kVacuum := by
  rw [M.mem_kVacuum_iff] at hx ⊢
  intro n
  rw [← A.commutes_K, hx, map_zero]

theorem action_preserves_transverse (g : G) (x : H) (hx : x ∈ M.transverse) :
    A.action g x ∈ M.transverse :=
  ⟨A.action_preserves_physical g x hx.1, A.action_preserves_kVacuum g x hx.2⟩

theorem action_preserves_nullPhysical (g : G) (x : H)
    (hx : x ∈ M.physical ⊓ M.spurious) :
    A.action g x ∈ M.physical ⊓ M.spurious :=
  ⟨A.action_preserves_physical g x hx.1, A.action_preserves_spurious g x hx.2⟩

/-- Restriction of the group representation to any stable weight slice. -/
def stableWeightAction (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) :
    G →* (M.weightSlice U N ≃ₗ[ℂ] M.weightSlice U N) where
  toFun g :=
    { toFun := fun x => ⟨⟨A.action g x.val, A.preserves_wt g N _ x.val.property⟩,
        hU g _ x.property⟩
      invFun := fun x => ⟨⟨A.action g⁻¹ x.val, A.preserves_wt g⁻¹ N _ x.val.property⟩,
        hU g⁻¹ _ x.property⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; apply Subtype.ext; simp
      map_add' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro a x; apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem stableWeightAction_apply (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G)
    (x : M.weightSlice U N) :
    ((A.stableWeightAction U hU N g x).val : H) = A.action g x.val := rfl

theorem stableWeightAction_isometry (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G)
    (x y : M.weightSlice U N) :
    M.B (A.stableWeightAction U hU N g x).val (A.stableWeightAction U hU N g y).val =
      M.B x.val y.val := A.isometry g x.val y.val

theorem stableWeightAction_preserves_radical (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G)
    (x : M.weightSlice U N) (hx : x ∈ M.weightRadical U N) :
    A.stableWeightAction U hU N g x ∈ M.weightRadical U N := by
  rw [M.mem_weightRadical_iff] at hx ⊢
  intro y
  obtain ⟨z, rfl⟩ := (A.stableWeightAction U hU N g).surjective y
  rw [A.stableWeightAction_isometry]
  exact hx z

theorem stableWeightAction_map_radical (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G) :
    (M.weightRadical U N).map (A.stableWeightAction U hU N g).toLinearMap =
      M.weightRadical U N := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact A.stableWeightAction_preserves_radical U hU N g x hx
  · intro x hx
    refine ⟨A.stableWeightAction U hU N g⁻¹ x,
      A.stableWeightAction_preserves_radical U hU N g⁻¹ x hx, ?_⟩
    simp

/-- The group action induced on the genuine radical quotient. -/
def stableWeightQuotientAction (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) :
    G →* (M.weightRadicalQuotient U N ≃ₗ[ℂ] M.weightRadicalQuotient U N) where
  toFun g := Submodule.Quotient.equiv _ _ (A.stableWeightAction U hU N g)
    (A.stableWeightAction_map_radical U hU N g)
  map_one' := by
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with | _ x =>
    change Submodule.Quotient.mk (A.stableWeightAction U hU N 1 x) =
      Submodule.Quotient.mk x
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with | _ x =>
    change Submodule.Quotient.mk (A.stableWeightAction U hU N (g * h) x) =
      Submodule.Quotient.mk
        (A.stableWeightAction U hU N g (A.stableWeightAction U hU N h x))
    simp

@[simp] theorem stableWeightQuotientAction_mk (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G)
    (x : M.weightSlice U N) :
    A.stableWeightQuotientAction U hU N g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A.stableWeightAction U hU N g x) := rfl

theorem stableWeightQuotientAction_isometry (U : Submodule ℂ H)
    (hU : ∀ g x, x ∈ U → A.action g x ∈ U) (N : ℤ) (g : G)
    (x y : M.weightRadicalQuotient U N) :
    M.radicalQuotientForm U N (A.stableWeightQuotientAction U hU N g x)
      (A.stableWeightQuotientAction U hU N g y) = M.radicalQuotientForm U N x y := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  exact A.isometry g x.val y.val

theorem transverseKQuotientEquiv_equivariant (hF : M.LightConeSplit) (N : ℤ) (g : G)
    (x : M.weightSlice M.transverse N) :
    M.transverseKQuotientEquiv hF N
      (A.stableWeightAction M.transverse A.action_preserves_transverse N g x) =
    A.stableWeightQuotientAction M.kVacuum A.action_preserves_kVacuum N g
      (M.transverseKQuotientEquiv hF N x) := rfl

theorem transversePhysicalQuotientEquiv_equivariant (hc : M.c = 26)
    (hF : M.LightConeSplit) (g : G) (x : M.weightSlice M.transverse 1) :
    M.transversePhysicalQuotientEquiv hc hF
      (A.stableWeightAction M.transverse A.action_preserves_transverse 1 g x) =
    A.stableWeightQuotientAction M.physical A.action_preserves_physical 1 g
      (M.transversePhysicalQuotientEquiv hc hF x) := rfl

theorem physicalQuotientRepresentative_equivariant (hc : M.c = 26)
    (hF : M.LightConeSplit) (g : G) (q : M.weightRadicalQuotient M.physical 1) :
    (M.transversePhysicalQuotientEquiv hc hF).symm
      (A.stableWeightQuotientAction M.physical A.action_preserves_physical 1 g q) =
    A.stableWeightAction M.transverse A.action_preserves_transverse 1 g
      ((M.transversePhysicalQuotientEquiv hc hF).symm q) := by
  apply (M.transversePhysicalQuotientEquiv hc hF).injective
  rw [LinearEquiv.apply_symm_apply, A.transversePhysicalQuotientEquiv_equivariant,
    LinearEquiv.apply_symm_apply]

end VOA.Moonshine.ConwayNorton.StringGroupAction
