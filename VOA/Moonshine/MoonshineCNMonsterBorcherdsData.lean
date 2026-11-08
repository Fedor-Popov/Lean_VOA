import VOA.Moonshine.MoonshineCNMonsterCartanAction
import VOA.Moonshine.MoonshineCNMonsterLieInvariance
import VOA.Moonshine.MoonshineCNMonsterPairing
import VOA.Moonshine.MoonshineCNMonsterGrading
import VOA.Moonshine.MoonshineCNRootSpaceAction
import VOA.Moonshine.MoonshineCNBorcherdsFreeLie

/-! The Monster Lie algebra as abstract Borcherds data.

Borcherds coordinates `(m, n)` are the repository momenta `(m, -n)`; the Borcherds form
`-(m n' + m' n)` is then the hyperbolic lattice form, the real root `(1, -1)` is momentum `(1, 1)`
of norm two, and the root space at `(m, n) ≠ 0` is `V♮` in weight `1 + m n`.

Every field of the data is proved here from the vertex-algebra construction, except generation of
the algebra by its Cartan, real and imaginary simple root spaces.  That statement is kept as the
explicit hypothesis `MonsterLieSimpleRootGeneration`; it is equivalent, given the other fields, to
the product formula for `j(p) - j(q)`, which is not yet in Lean. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster

attribute [local instance] monsterPhysicalAddCommGroup

/-- Repository momentum of the Borcherds root `(m, n)`. -/
def borcherdsMomentum (γ : ℤ × ℤ) : lorentzianLattice.carrier := ![γ.1, -γ.2]

theorem borcherdsMomentum_apply_zero (γ : ℤ × ℤ) : borcherdsMomentum γ 0 = γ.1 := rfl

theorem borcherdsMomentum_apply_one (γ : ℤ × ℤ) : borcherdsMomentum γ 1 = -γ.2 := rfl

/-- Borcherds coordinates and repository momenta are in bijection. -/
def borcherdsMomentumEquiv : (ℤ × ℤ) ≃ lorentzianLattice.carrier where
  toFun := borcherdsMomentum
  invFun x := (x 0, -x 1)
  left_inv γ := by simp [borcherdsMomentum]
  right_inv x := by
    change (![x 0, -(-x 1)] : Fin 2 → ℤ) = x
    funext a
    fin_cases a <;> simp

theorem borcherdsMomentum_add (γ δ : ℤ × ℤ) :
    borcherdsMomentum (γ + δ) = borcherdsMomentum γ + borcherdsMomentum δ := by
  change (![γ.1 + δ.1, -(γ.2 + δ.2)] : Fin 2 → ℤ) = ![γ.1, -γ.2] + ![δ.1, -δ.2]
  funext a
  fin_cases a
  · simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Pi.add_apply, Matrix.cons_val_zero]
    ring

theorem borcherdsMomentum_neg (γ : ℤ × ℤ) : borcherdsMomentum (-γ) = -borcherdsMomentum γ := by
  change (![-γ.1, -(-γ.2)] : Fin 2 → ℤ) = -![γ.1, -γ.2]
  funext a
  fin_cases a <;> simp

theorem borcherdsMomentum_zero : borcherdsMomentum 0 = 0 := by
  change (![0, -0] : Fin 2 → ℤ) = 0
  funext a
  fin_cases a <;> simp

theorem borcherdsMomentum_eq_zero_iff (γ : ℤ × ℤ) : borcherdsMomentum γ = 0 ↔ γ = 0 := by
  rw [← borcherdsMomentum_zero]
  exact borcherdsMomentumEquiv.injective.eq_iff

/-- The Monster Lie algebra's root spaces in Borcherds coordinates. -/
def monsterLieBorcherdsWeight (γ : ℤ × ℤ) : Submodule ℂ monsterLieAlgebra :=
  monsterLieMomentum (borcherdsMomentum γ)

theorem monsterLieBorcherdsWeight_zero : monsterLieBorcherdsWeight 0 = monsterLieMomentum 0 :=
  congrArg monsterLieMomentum borcherdsMomentum_zero

theorem monsterLieBorcherdsWeight_isInternal : DirectSum.IsInternal monsterLieBorcherdsWeight := by
  classical
  obtain ⟨hind, htop⟩ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      monsterLieMomentum_isInternal
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
  refine ⟨hind.comp borcherdsMomentumEquiv.injective, ?_⟩
  rw [← htop]
  exact borcherdsMomentumEquiv.iSup_comp (g := monsterLieMomentum)

/-- A nonzero Borcherds root space is the root space of `V♮` in weight `1 + m n`. -/
def monsterLieBorcherdsRootEquiv (γ : ℤ × ℤ) (hγ : γ ≠ 0) :
    monsterLieBorcherdsWeight γ ≃ₗ[ℂ] VnatVOA.grading (1 + γ.1 * γ.2) :=
  (monsterLieRootSpaceEquiv γ.1 (-γ.2) (by
      by_contra h
      push Not at h
      exact hγ (Prod.ext h.1 (by simpa using h.2)))).trans
    (LinearEquiv.ofEq _ _ (congrArg VnatVOA.grading (by ring)))

instance monsterLieBorcherdsWeight_finite (γ : ℤ × ℤ) :
    FiniteDimensional ℂ (monsterLieBorcherdsWeight γ) := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [monsterLieBorcherdsWeight_zero]
    exact LinearEquiv.finiteDimensional monsterLieZeroMomentumEquiv.symm
  · haveI : FiniteDimensional ℂ (VnatVOA.grading (1 + γ.1 * γ.2)) :=
      finiteDimensional_gradingNat _
    exact LinearEquiv.finiteDimensional (monsterLieBorcherdsRootEquiv γ hγ).symm

/-- Integer arithmetic of the root support: `m n ≥ -1` and `m n ≠ 0`. -/
theorem borcherdsRootSupport_of_product (m n : ℤ) (h1 : -1 ≤ m * n) (h0 : m * n ≠ 0) :
    borcherdsRootSupport (m, n) := by
  simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone, borcherdsRealRoot,
    Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg]
  obtain ⟨k, hk⟩ : ∃ k, k = m * n := ⟨_, rfl⟩
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · omega
    · subst hn
      simp at h0
    · have ha : m * n ≤ m := by nlinarith
      have hb : m * n ≤ -n := by nlinarith
      rw [← hk] at h1 ha hb
      omega
  · subst hm
    simp at h0
  · rcases lt_trichotomy n 0 with hn | hn | hn
    · have ha : m * n ≤ n := by nlinarith
      have hb : m * n ≤ -m := by nlinarith
      rw [← hk] at h1 ha hb
      omega
    · subst hn
      simp at h0
    · omega

theorem monsterLieBorcherdsWeight_support (γ : ℤ × ℤ) (hne : monsterLieBorcherdsWeight γ ≠ ⊥) :
    borcherdsRootSupport γ := by
  by_cases hγ : γ = 0
  · exact Or.inl hγ
  have hV : VnatVOA.grading (1 + γ.1 * γ.2) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h := hbot.le (monsterLieBorcherdsRootEquiv γ hγ ⟨x, hx⟩).property
    rw [Submodule.mem_bot] at h
    have h0 : (⟨x, hx⟩ : monsterLieBorcherdsWeight γ) = 0 :=
      (monsterLieBorcherdsRootEquiv γ hγ).injective (Subtype.ext (by simpa using h))
    exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val h0)
  have h1 : -1 ≤ γ.1 * γ.2 := by
    by_contra h
    exact hV (gradingNat_neg (by omega))
  have h0 : γ.1 * γ.2 ≠ 0 := by
    intro h
    rw [h, add_zero] at hV
    exact hV gradingNat_one
  exact borcherdsRootSupport_of_product γ.1 γ.2 h1 h0

theorem vnat_finrank_zero : Module.finrank ℂ (VnatVOA.grading 0) = 1 := by
  change Module.finrank ℂ (gradingNat 0) = 1
  rw [gradingNat_zero]
  exact finrank_span_singleton VnatVOA_vacuum_ne_zero

theorem monsterLieBorcherdsWeight_real_finrank (γ : ℤ × ℤ)
    (hγ : γ = borcherdsRealRoot ∨ γ = -borcherdsRealRoot) :
    Module.finrank ℂ (monsterLieBorcherdsWeight γ) = 1 := by
  have hne : γ ≠ 0 := by
    rcases hγ with rfl | rfl <;> simp [borcherdsRealRoot, Prod.ext_iff]
  have hprod : 1 + γ.1 * γ.2 = 0 := by
    rcases hγ with rfl | rfl <;> simp [borcherdsRealRoot]
  rw [(monsterLieBorcherdsRootEquiv γ hne).finrank_eq,
    show VnatVOA.grading (1 + γ.1 * γ.2) = VnatVOA.grading 0 by rw [hprod]]
  exact vnat_finrank_zero

/-- The Borcherds coordinates of a Cartan element: `ξ ↦ (-ξ₂, ξ₁)` in no-ghost coordinates. -/
def borcherdsCartanCoordinates : (ℂ × ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun ξ := ![-ξ.2, ξ.1]
  map_add' ξ ζ := by
    funext a
    fin_cases a <;> simp [add_comm]
  map_smul' c ξ := by
    funext a
    fin_cases a <;> simp

theorem borcherdsCartanCoordinates_injective : Function.Injective borcherdsCartanCoordinates := by
  intro ξ ζ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [borcherdsCartanCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, neg_inj] at h0 h1
  exact Prod.ext h1 h0

theorem borcherdsCartanCoordinates_surjective : Function.Surjective borcherdsCartanCoordinates := by
  intro c
  refine ⟨(c 1, -c 0), ?_⟩
  funext a
  fin_cases a <;> simp [borcherdsCartanCoordinates]

/-- The Cartan map of the Monster Lie algebra. -/
def monsterLieCartanMap : (ℂ × ℂ) →ₗ[ℂ] monsterLieAlgebra :=
  (monsterLieMomentum 0).subtype ∘ₗ monsterLieZeroMomentumEquiv.symm.toLinearMap ∘ₗ
    borcherdsCartanCoordinates

theorem monsterLieCartanMap_mem (ξ : ℂ × ℂ) : monsterLieCartanMap ξ ∈ monsterLieMomentum 0 :=
  (monsterLieZeroMomentumEquiv.symm (borcherdsCartanCoordinates ξ)).property

theorem monsterLieZeroMomentumEquiv_cartan (ξ : ℂ × ℂ) :
    monsterLieZeroMomentumEquiv ⟨monsterLieCartanMap ξ, monsterLieCartanMap_mem ξ⟩ =
      borcherdsCartanCoordinates ξ := by
  change monsterLieZeroMomentumEquiv (monsterLieZeroMomentumEquiv.symm _) = _
  exact monsterLieZeroMomentumEquiv.apply_symm_apply _

theorem monsterLieCartanMap_injective : Function.Injective monsterLieCartanMap := by
  intro ξ ζ h
  apply borcherdsCartanCoordinates_injective
  rw [← monsterLieZeroMomentumEquiv_cartan, ← monsterLieZeroMomentumEquiv_cartan]
  congr 1
  exact Subtype.ext h

theorem monsterLieCartanMap_range :
    LinearMap.range monsterLieCartanMap = monsterLieBorcherdsWeight 0 := by
  rw [monsterLieBorcherdsWeight_zero]
  apply le_antisymm
  · rintro _ ⟨ξ, rfl⟩
    exact monsterLieCartanMap_mem ξ
  · intro x hx
    obtain ⟨ξ, hξ⟩ := borcherdsCartanCoordinates_surjective (monsterLieZeroMomentumEquiv ⟨x, hx⟩)
    refine ⟨ξ, ?_⟩
    change ((monsterLieZeroMomentumEquiv.symm (borcherdsCartanCoordinates ξ) :
      monsterLieMomentum 0) : monsterLieAlgebra) = x
    rw [hξ, LinearEquiv.symm_apply_apply]

/-- The Cartan acts on the Borcherds root space `(m, n)` by `-(ξ₁ n + m ξ₂)`. -/
theorem monsterLieCartanMap_action (ξ : ℂ × ℂ) (γ : ℤ × ℤ) (x : monsterLieAlgebra)
    (hx : x ∈ monsterLieBorcherdsWeight γ) :
    ⁅monsterLieCartanMap ξ, x⁆ =
      borcherdsCartanPairing ξ (borcherdsWeightVector γ) • x := by
  have h := monsterLie_zeroMomentum_bracket ⟨monsterLieCartanMap ξ, monsterLieCartanMap_mem ξ⟩
    (borcherdsMomentum γ) x hx
  rw [monsterLieZeroMomentumEquiv_cartan] at h
  refine h.trans ?_
  congr 1
  simp only [borcherdsCartanCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, borcherdsMomentum_apply_zero, borcherdsMomentum_apply_one,
    borcherdsCartanPairing, borcherdsWeightVector, Int.cast_neg]
  ring

theorem monsterLieCartanMap_form (ξ μ : ℂ × ℂ) :
    monsterLieBilinearForm (monsterLieCartanMap ξ) (monsterLieCartanMap μ) =
      borcherdsCartanPairing ξ μ := by
  have h := monsterLieBilinearForm_zeroMomentum
    ⟨monsterLieCartanMap ξ, monsterLieCartanMap_mem ξ⟩
    ⟨monsterLieCartanMap μ, monsterLieCartanMap_mem μ⟩
  rw [monsterLieZeroMomentumEquiv_cartan, monsterLieZeroMomentumEquiv_cartan] at h
  refine h.trans ?_
  simp only [borcherdsCartanCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, borcherdsCartanPairing]
  ring

/-- Generation of the Monster Lie algebra by its Cartan, real and imaginary simple root spaces.
It is the only Borcherds-data field not yet proved; it is equivalent, given the other fields,
to the product formula for `j(p) - j(q)`. -/
def MonsterLieSimpleRootGeneration : Prop :=
  LieSubalgebra.lieSpan ℂ monsterLieAlgebra (borcherdsSimpleGenerators monsterLieBorcherdsWeight) =
    ⊤

/-- The Monster Lie algebra with its momentum grading, Cartan, invariant form and support is
Borcherds data, given generation by its simple root spaces. -/
def monsterLieBorcherdsData (hgen : MonsterLieSimpleRootGeneration) :
    BorcherdsData monsterLieAlgebra where
  weightSpace := monsterLieBorcherdsWeight
  weight_internal := monsterLieBorcherdsWeight_isInternal
  weight_finite := monsterLieBorcherdsWeight_finite
  bracket_weight {γ δ} {x y} hx hy := by
    have h := monsterLieMomentum_bracket _ _ x y hx hy
    change ⁅x, y⁆ ∈ monsterLieMomentum (borcherdsMomentum (γ + δ))
    rwa [borcherdsMomentum_add]
  cartanMap := monsterLieCartanMap
  cartan_injective := monsterLieCartanMap_injective
  cartan_range := monsterLieCartanMap_range
  cartan_action := monsterLieCartanMap_action
  form := monsterLieBilinearForm
  form_symmetric := monsterLieBilinearForm_symmetric
  form_invariant := monsterLieBilinearForm_invariant
  form_orthogonal γ δ hγδ x hx y hy := by
    apply monsterLieBilinearForm_momentum_orthogonal _ _ _ x y hx hy
    rw [← borcherdsMomentum_add, Ne, borcherdsMomentum_eq_zero_iff]
    exact hγδ
  form_cartan := monsterLieCartanMap_form
  form_nondegenerate γ x hx hB := by
    apply monsterLieBilinearForm_pairing_nondegenerate _ x hx
    intro v hv
    apply hB v
    change v ∈ monsterLieMomentum (borcherdsMomentum (-γ))
    rwa [borcherdsMomentum_neg]
  root_support := monsterLieBorcherdsWeight_support
  real_dimension := ⟨monsterLieBorcherdsWeight_real_finrank _ (Or.inl rfl),
    monsterLieBorcherdsWeight_real_finrank _ (Or.inr rfl)⟩
  generated := hgen

/-- `Aut(V♮)` acts on the Monster Lie algebra by linear equivalences. -/
def monsterLieLinearAction : AutVnat →* (monsterLieAlgebra ≃ₗ[ℂ] monsterLieAlgebra) where
  toFun σ := (monsterLieAut σ).toLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change monsterLieAut 1 x = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro x
    change monsterLieAut (σ * τ) x = monsterLieAut σ (monsterLieAut τ x)
    rw [map_mul]
    rfl

theorem monsterLieAut_fixes_real (σ : AutVnat) (γ : ℤ × ℤ)
    (hγ : γ = borcherdsRealRoot ∨ γ = -borcherdsRealRoot) (x : monsterLieAlgebra)
    (hx : x ∈ monsterLieBorcherdsWeight γ) : monsterLieAut σ x = x := by
  have hne : γ ≠ 0 := by
    rcases hγ with rfl | rfl <;> simp [borcherdsRealRoot, Prod.ext_iff]
  have hprod : 1 - γ.1 * -γ.2 = 0 := by
    rcases hγ with rfl | rfl <;> simp [borcherdsRealRoot]
  have hne' : γ.1 ≠ 0 ∨ -γ.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 (by simpa using h.2))
  let E := monsterLieRootSpaceEquiv γ.1 (-γ.2) hne'
  have heq := monsterLieRootSpaceEquiv_equivariant γ.1 (-γ.2) hne' σ ⟨x, hx⟩
  have hfix : ∀ v : VnatVOA.grading (1 - γ.1 * -γ.2), GriessAut.autRestrict σ _ v = v := by
    intro v
    apply Subtype.ext
    rw [GriessAut.autRestrict_coe]
    have hv := v.property
    have hv0 : (v : Vnat) ∈ gradingNat 0 := by
      rw [← hprod]
      exact hv
    rw [gradingNat_zero, Submodule.mem_span_singleton] at hv0
    obtain ⟨c, hc⟩ := hv0
    rw [← hc, map_smul]
    congr 1
    exact σ.map_vacuum
  rw [hfix] at heq
  exact congrArg Subtype.val (E.injective heq)

/-- `Aut(V♮)` acts on the Monster Borcherds data: by graded Lie automorphisms preserving the form,
trivially on the Cartan and on the real root spaces. -/
def monsterLieBorcherdsAction (hgen : MonsterLieSimpleRootGeneration) :
    (monsterLieBorcherdsData hgen).GAction AutVnat where
  action := monsterLieLinearAction
  preserves_lie σ x y := (monsterLieAut σ).map_lie x y
  graded σ γ x hx := monsterLieAut_momentum σ _ x hx
  preserves_form σ x y := monsterLieBilinearForm_aut σ x y
  fixes_cartan σ x hx := by
    have hx' : x ∈ monsterLieMomentum 0 := by
      rw [← monsterLieBorcherdsWeight_zero]
      exact hx
    exact monsterLieZeroMomentum_aut_trivial σ ⟨x, hx'⟩
  fixes_real σ x hx := by
    rcases hx with hx | hx
    · exact monsterLieAut_fixes_real σ _ (Or.inl rfl) x hx
    · exact monsterLieAut_fixes_real σ _ (Or.inr rfl) x hx

/-! ### Consequences for the Monster Lie algebra, under the generation hypothesis -/

section Consequences
variable (hgen : MonsterLieSimpleRootGeneration) (e f : monsterLieAlgebra)
  (he : e ∈ monsterLieBorcherdsWeight borcherdsRealRoot)
  (hf : f ∈ monsterLieBorcherdsWeight (-borcherdsRealRoot))
  (hef : monsterLieBilinearForm e f = 1)

include he hf hef in
/-- Each component of U for the Monster has the dimension of `V♮` in weight `j + 1`. -/
theorem monsterLie_generatorString_finrank (j : ℤ) (hj : 1 ≤ j) (k : ℕ) (hk : (k : ℤ) < j) :
    Module.finrank ℂ ((monsterLieBorcherdsData hgen).generatorString e j k) =
      Module.finrank ℂ (VnatVOA.grading (1 + j)) := by
  rw [(monsterLieBorcherdsData hgen).generatorString_finrank e f he hf hef j hj k hk]
  have hne : borcherdsImaginaryRoot j ≠ 0 := by
    simp [borcherdsImaginaryRoot, Prod.ext_iff]
  change Module.finrank ℂ (monsterLieBorcherdsWeight (borcherdsImaginaryRoot j)) = _
  rw [(monsterLieBorcherdsRootEquiv _ hne).finrank_eq]
  have hj1 : (borcherdsImaginaryRoot j).1 * (borcherdsImaginaryRoot j).2 = j := by
    simp [borcherdsImaginaryRoot]
  rw [hj1]

/-- For the Monster Lie algebra, `N(U) → N(ℂ) → ℂ` is a length-one resolution. -/
theorem monsterLie_generatorVermaResolution_shortExact :
    Function.Injective ((monsterLieBorcherdsData hgen).generatorVermaResolution e f he hf hef) ∧
      Function.Exact ((monsterLieBorcherdsData hgen).generatorVermaResolution e f he hf hef)
        (monsterLieBorcherdsData hgen).trivialVermaAugmentation ∧
      Function.Surjective (monsterLieBorcherdsData hgen).trivialVermaAugmentation :=
  (monsterLieBorcherdsData hgen).generatorVermaResolution_shortExact e f he hf hef

include he hf hef in
/-- For the Monster Lie algebra, `T(U) → U(𝔲⁺)` is bijective. -/
theorem monsterLie_positiveTensorEnveloping_bijective :
    Function.Bijective (tensorGeneratorToEnveloping
      ((monsterLieBorcherdsData hgen).positiveGeneratorSpace e)) :=
  (monsterLieBorcherdsData hgen).positiveTensorGeneratorToEnveloping_bijective e f he hf hef

include he hf hef in
/-- For the Monster Lie algebra, `𝔲⁺` is free on U. -/
theorem monsterLie_positivePartFreeLie_bijective :
    Function.Bijective (freeLieGeneratorMap
      ((monsterLieBorcherdsData hgen).positiveGeneratorSpace e)
      ((monsterLieBorcherdsData hgen).positiveGeneratorBasis e)) :=
  (monsterLieBorcherdsData hgen).positivePartFreeLie_bijective e f he hf hef

end Consequences

end VOA.Moonshine.ConwayNorton
