import VOA.Classification.COne.OrbSglPrim
import VOA.Classification.COne.OrbOddReduce

/-!
# OrbSgl (2): the explicit identification `(V₈⁺)^σ ≅ V₂^{A₄}` and characters with values

`tetra_cubic_iso` is only existential.  Here the identification is explicit:
`tetraEquiv : (V₈⁺)^{plusCubic} ≃ W = V₂^{A₄}` has ambient map `scaleMorph 1 2`
(`fixedEquivKlein` followed by the iterated-orbifold identity, with `tetra = klein ⊔ ⟨rotC⟩`).

* `tetraRestrict`: a weak `V₈⁺`-module as a weak `W`-module along `tetraEquiv.symm`.
* `tetra_character_of_plus_top`: a `V₈⁺` top vector which is a common eigenvector of the Zhu
  generators `ω, W, E` gives a character `ψ` of `A(W)` with `ψ([ω]) = h` and the VALUE
  `ψ([a]) • x = o(tetraEquiv⁻¹ a) x` for every homogeneous `a`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu OrbOdd
  OrbC2e OrbC2f PlusCharacterTable ConverseUniverse PlusC2 PlusSplitting PlusUnitary OrbRat5

theorem mem_tetra_iff (x : VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 1)) :
    x ∈ (orbifold tetra).carrier ↔ x ∈ (orbifold (klein ⊔ Subgroup.zpowers rotC)).carrier := by
  rw [tetra_eq_join]
  exact Iff.rfl

/-- The iterated-orbifold identity `(V₂^{klein})^{rotC} = V₂^{A₄}`. -/
def kleinToTetra : (orbifold (Subgroup.zpowers kleinCubic)).carrier ≃ₗ[ℂ]
    (orbifold tetra).carrier where
  toFun x := ⟨x.1.1, (mem_tetra_iff _).mpr ((mem_join_fixed_iff klein rotC x.1.1).mpr
    ⟨x.1.2, congrArg Subtype.val ((mem_orbifold_zpowers_iff _ _).mp x.2)⟩)⟩
  invFun y := ⟨⟨y.1, ((mem_join_fixed_iff klein rotC y.1).mp ((mem_tetra_iff _).mp y.2)).1⟩,
    (mem_orbifold_zpowers_iff _ _).mpr
      (Subtype.ext ((mem_join_fixed_iff klein rotC y.1).mp ((mem_tetra_iff _).mp y.2)).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kleinToTetra_hom : IsVOAHom cubicModel Wt kleinToTetra.toLinearMap :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem kleinToTetra_omega : kleinToTetra cubicModel.conformalVector = Wt.conformalVector := rfl

/-- The explicit identification, ambient map `scaleMorph 1 2`. -/
def tetraEquiv : (orbifold (Subgroup.zpowers plusCubic)).carrier ≃ₗ[ℂ] (orbifold tetra).carrier :=
  fixedEquivKlein.trans kleinToTetra

theorem tetraEquiv_val (x : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
    ((tetraEquiv x : (orbifold tetra).carrier) : VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 1))
      = scaleMorph 1 2 ((x : VP 4 four_ge_one) : VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 4)) :=
  rfl

theorem tetraEquiv_hom :
    IsVOAHom (orbifoldVOA (Subgroup.zpowers plusCubic)) Wt tetraEquiv.toLinearMap := by
  constructor
  · change kleinToTetra (fixedEquivKlein _) = _
    rw [show fixedEquivKlein (orbifoldVOA (Subgroup.zpowers plusCubic)).vacuum = cubicModel.vacuum
      from fixedEquivKlein_hom.map_vacuum]
    rfl
  · intro a n b
    change kleinToTetra (fixedEquivKlein _) = _
    rw [show fixedEquivKlein ((orbifoldVOA (Subgroup.zpowers plusCubic)).smul a n b) =
      cubicModel.smul (fixedEquivKlein a) n (fixedEquivKlein b) from fixedEquivKlein_hom.map_smul a n b]
    rfl

theorem tetraEquiv_omega :
    tetraEquiv (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector = Wt.conformalVector := by
  change kleinToTetra (fixedEquivKlein _) = _
  rw [fixedEquivKlein_omega]; rfl

theorem tetraEquiv_symm_hom :
    IsVOAHom Wt (orbifoldVOA (Subgroup.zpowers plusCubic)) tetraEquiv.symm.toLinearMap :=
  isVOAHom_symm' tetraEquiv tetraEquiv_hom

theorem tetraEquiv_symm_omega :
    tetraEquiv.symm Wt.conformalVector = (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector := by
  rw [← tetraEquiv_omega, LinearEquiv.symm_apply_apply]

/-! ## Restriction of `V₈⁺`-modules to `W` -/

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- A weak `V₈⁺`-module restricted to the cubic fixed points and pulled back to `W`. -/
def tetraRestrict (A : WeakModule (V2mPlus 4 four_ge_one) M) : WeakModule Wt M :=
  pullWeak tetraEquiv_symm_hom ((orbifold (Subgroup.zpowers plusCubic)).restrictWeakModule A)

theorem tetraRestrict_YM (A : WeakModule (V2mPlus 4 four_ge_one) M) (v : (orbifold tetra).carrier) :
    (tetraRestrict A).YM v =
      A.YM ((tetraEquiv.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
        VP 4 four_ge_one) := rfl

theorem tetra_grading_symm {k : ℤ} {v : (orbifold tetra).carrier} (hv : v ∈ Wt.grading k) :
    ((tetraEquiv.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
      VP 4 four_ge_one) ∈ (V2mPlus 4 four_ge_one).grading k :=
  voaHom_map_grading tetraEquiv_symm_hom tetraEquiv_symm_omega hv

theorem mem_Omega_tetraRestrict (N : OrdVModule (V2mPlus 4 four_ge_one) M) {h : ℂ}
    (hlow : IsLowestWeight N h) {y : M} (hy : y ∈ N.weight h) :
    y ∈ Omega (tetraRestrict N.toWeakModule) := by
  intro β v hv n hn
  rw [tetraRestrict_YM]
  exact mode_lowering_vanish N hlow (tetra_grading_symm hv) hy hn

/-- A `V₈⁺` top vector which is a common eigenvector of `ω, W, E` gives a character of
`A(W)` with `[ω] ↦ h`, whose value on every homogeneous `a` is the `o(tetraEquiv⁻¹ a)`-eigenvalue. -/
theorem tetra_character_of_plus_top (N : OrdVModule (V2mPlus 4 four_ge_one) M) {h : ℂ}
    (hlow : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) (hx0 : x ≠ 0) (v : Fin 3 → ℂ)
    (hv : ∀ i, oMod N (gP 4 four_ge_one i) x = v i • x) :
    ∃ ψ : VOA.A Wt →ₗ[ℂ] ℂ, (∀ p q, ψ (Amul (zhuRingData_holds Wt) p q) = ψ p * ψ q) ∧
      ψ (VOA.mk Wt Wt.vacuum) = 1 ∧ ψ (VOA.mk Wt Wt.conformalVector) = h ∧
      ∀ (k : ℤ) (a : (orbifold tetra).carrier), a ∈ Wt.grading k →
        ψ (VOA.mk Wt a) • x = oMod N ((tetraEquiv.symm a : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
          VP 4 four_ge_one) x := by
  letI := instRingA Wt
  letI := instAlgebraA Wt
  have hΩ := mem_Omega_tetraRestrict N hlow hx
  obtain ⟨χ, hχ⟩ := exists_character_of_top_line (tetraRestrict N.toWeakModule) hΩ hx0 (by
    intro k a ha
    obtain ⟨c, hc⟩ := plus_top_eigen N hlow hx v hv
      ((tetraEquiv.symm a : (orbifold (Subgroup.zpowers plusCubic)).carrier) : VP 4 four_ge_one)
    refine ⟨c, ?_⟩
    rw [tetraRestrict_YM, ← oMod_homogeneous N (tetra_grading_symm ha)]
    exact hc)
  have hval : ∀ (k : ℤ) (a : (orbifold tetra).carrier), a ∈ Wt.grading k →
      χ (VOA.mk Wt a) • x = oMod N ((tetraEquiv.symm a : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
          VP 4 four_ge_one) x := by
    intro k a ha
    rw [← hχ, PlusSplitting.topEvaluation_mk, oLevW_homogeneous _ 0 ha, add_zero,
      oMod_homogeneous N (tetra_grading_symm ha)]
    rfl
  refine ⟨χ.toLinearMap, fun p q => map_mul χ p q, map_one χ, ?_, hval⟩
  refine character_omega_of_top _ hΩ hx0 ?_ χ hχ
  rw [tetraRestrict_YM, tetraEquiv_symm_omega]
  exact N.L0_weight h x hx

end VOA.Classification.COne.OrbSgl
