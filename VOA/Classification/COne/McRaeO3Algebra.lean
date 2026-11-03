/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO3Object

/-! # O3: multiplication, unit, unit laws and commutativity of the ambient algebra

For `C₂`-cofinite `W^G`, the vertex operator `Y_W` factors through the logarithmic tensor
product (`tensorFactor`, the universal property). This gives the multiplication
`mulHom : V ⊠ V ⟶ V`. The unit `unitHom : 𝟙 ⟶ V` is the inclusion `W^G ↪ W`.

* `mulHom_one_mul`, `mulHom_mul_one`: the unit laws, from the universal property, the creation
  property and skew-symmetry `omega_vertexIntertwiner`.
* `mulHom_comm`: `swapIso … 0 ≫ μ = μ`, from `omega_vertexIntertwiner`.
* `autHom g`, for `g ∈ G`, is a `W^G`-module automorphism of `V`. It is multiplicative
  (`autHom_mul`) and unital (`unitHom_autHom`).
* Haploid: `finrank_unit_hom : finrank ℂ (𝟙 ⟶ V) = 1`, from `W₀ = ℂ𝟙`.
* `counitHom : V ⟶ 𝟙`, the averaging projection onto `W^G` (`G` finite), with
  `unitHom_counitHom : ι ≫ ε = 𝟙` and `counitHom_unitHom : ε ≫ ι = |G|⁻¹ Σ_g g`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO3
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.C2Rigid.LocalInjective
open VOA.LogTensor.Pz VOA.LogSkew VOA.Classification.COne.McRaeM1
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)


/-! ## Module-level facts about `Y_W` -/

/-- `Y_W` restricted to `W^G` in the first slot is the module vertex operator of `V`. -/
theorem precompose_unit_vertexIntertwiner :
    precompose (orbifold G).adjointInclusion (weakIdentity (orbifold G).adjointRestrict) (vertexIntertwiner G) =
      logModuleIntertwiner (orbifold G).adjointRestrict := by
  apply Subtype.ext
  funext n k
  ext u w
  rcases k with _ | k
  · change weakModuleModes (adjointWeakModule W) n (u : V) w = weakModuleModes (orbifold G).adjointRestrict n u w
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      rw [weakModuleModes_apply_intCast, weakModuleModes_apply_intCast]
      rfl
    · rw [weakModuleModes_of_not_int _ (fun k hk => hn ⟨k, hk⟩),
        weakModuleModes_of_not_int _ (fun k hk => hn ⟨k, hk⟩)]
      rfl
  · rfl

/-- The same with the unit in the second slot is the inverse-`Ω₀` image of the module
operator, i.e. HLZ's right-unit operator. -/
theorem precompose_vertexIntertwiner_unit :
    precompose (weakIdentity (orbifold G).adjointRestrict) (orbifold G).adjointInclusion (vertexIntertwiner G) =
      rightUnitIntertwiner (ambientLog G) := by
  apply (omegaEquiv (orbifold G).adjointRestrict (adjointModule (orbifoldVOA G)).toWeakModule (orbifold G).adjointRestrict 0).injective
  refine ((omega_precompose (vertexIntertwiner G) (weakIdentity (orbifold G).adjointRestrict)
    (orbifold G).adjointInclusion 0).trans ?_).trans (LinearEquiv.apply_symm_apply _ _).symm
  refine (congrArg (precompose _ _) (omega_vertexIntertwiner G)).trans ?_
  exact precompose_unit_vertexIntertwiner G

/-- A group element `g ∈ G` as a `W^G`-module endomorphism of `V`. -/
def autWeakHom (g : G) : (orbifold G).adjointRestrict.Hom (orbifold G).adjointRestrict where
  toLinearMap := (g : Aut W).toLinearEquiv.toLinearMap
  map_act := by
    intro u n x
    change (g : Aut W) (W.smul (u : V) n x) = W.smul (u : V) n ((g : Aut W) x)
    rw [Aut.map_smul, u.2 g g.2]

theorem autWeakHom_apply (g : G) (x : V) :
    (autWeakHom G g).toLinearMap x = (g : Aut W) x := rfl

/-- `Y_W` is `G`-equivariant. -/
theorem precompose_aut_vertexIntertwiner (g : G) :
    precompose (autWeakHom G g) (autWeakHom G g) (vertexIntertwiner G) =
      postcompose (autWeakHom G g) (vertexIntertwiner G) := by
  apply Subtype.ext
  funext n k
  ext a b
  rcases k with _ | k
  · change weakModuleModes (adjointWeakModule W) n ((g : Aut W) a) ((g : Aut W) b) =
      (g : Aut W) (weakModuleModes (adjointWeakModule W) n a b)
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      rw [weakModuleModes_apply_intCast, weakModuleModes_apply_intCast]
      exact (Aut.map_smul (g : Aut W) a k b).symm
    · rw [weakModuleModes_of_not_int _ (fun k hk => hn ⟨k, hk⟩)]
      exact (map_zero ((g : Aut W).toLinearEquiv)).symm
  · exact (map_zero ((g : Aut W).toLinearEquiv)).symm

/-- Postcomposition with a composite, given the inner postcomposition. -/
theorem post_homComp_eq {U M₁ M₂ B M₃ M₄ : Type u} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄] {W' : VertexOperatorAlgebra U}
    {A₁ : WeakModule W' M₁} {A₂ : WeakModule W' M₂} {A : WeakModule W' B}
    {A₃ : WeakModule W' M₃} {A₄ : WeakModule W' M₄}
    (μ : A₃.Hom A₄) (T : A.Hom A₃) (𝒴 : LogIntertwiningOperator A₁ A₂ A)
    (Z : LogIntertwiningOperator A₁ A₂ A₃) (hT : postcompose T 𝒴 = Z) :
    postcompose (homComp μ T) 𝒴 = postcompose μ Z := by
  rw [postcompose_homComp', hT]

/-! ## The categorical data -/

section Category
variable (hC2 : C2Cofinite (orbifoldVOA G))

/-- The weak-module multiplication `V ⊠ V → V` induced by `Y_W`. -/
def mulWeakHom : (tensorModule hC2 (ambientLog G) (ambientLog G) hfg hfg).toWeakModule.Hom (orbifold G).adjointRestrict :=
  tensorFactor hC2 (ambientLog G) (ambientLog G) hfg hfg (ambientLog G) (vertexIntertwiner G)

theorem mulWeakHom_intertwiner :
    postcompose (mulWeakHom G hfg hC2)
      (tensorIntertwiner hC2 (ambientLog G) (ambientLog G) hfg hfg) = vertexIntertwiner G :=
  tensorFactor_comp_intertwiner hC2 (ambientLog G) (ambientLog G) hfg hfg (ambientLog G) _

/-- **The multiplication** `μ : V ⊠ V ⟶ V` of the ambient algebra. -/
def mulHom : tensorObject hC2 (vObj G hfg) (vObj G hfg) ⟶ vObj G hfg :=
  fromWeakHom (mulWeakHom G hfg hC2)

/-- **The unit** `ι : 𝟙 = W^G ⟶ V`, the inclusion. -/
def unitHom : (unitObject : LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg :=
  fromWeakHom (orbifold G).adjointInclusion

theorem unitHom_apply (u : (orbifold G).carrier) : (unitHom G hfg).1 u = (u : V) := rfl

/-- `g ∈ G` as an endomorphism of `V` in `C`. -/
def autHom (g : G) : vObj G hfg ⟶ vObj G hfg := fromWeakHom (autWeakHom G g)

theorem autHom_apply (g : G) (x : V) : (autHom G hfg g).1 x = (g : Aut W) x := rfl

/-- **Left unit law**: `(ι ⊠ 1) ≫ μ = λ_V`. -/
theorem mulHom_one_mul :
    tensorMorphism hC2 (unitHom G hfg) (𝟙 (vObj G hfg)) ≫ mulHom G hfg hC2 =
      (leftUnitIso hC2 (vObj G hfg)).hom := by
  apply hom_ext
  intro q
  have key : (homComp (mulWeakHom G hfg hC2)
      (tensorMap hC2 (adjointModule (orbifoldVOA G)).toLog (ambientLog G) finGen_adjoint hfg
        (ambientLog G) (ambientLog G) hfg hfg (orbifold G).adjointInclusion
        (weakIdentity (orbifold G).adjointRestrict))).toLinearMap =
      (tensorLeftUnitHom hC2 (ambientLog G) hfg).toLinearMap := by
    apply tensor_morphism_ext hC2 (adjointModule (orbifoldVOA G)).toLog (ambientLog G)
      finGen_adjoint hfg (ambientLog G)
    refine (post_homComp_eq _ _ _ _ (tensorMap_intertwiner hC2 _ _ _ _ _ _ _ _ _ _)).trans ?_
    refine ((postcompose_precompose' _ _ _ _).trans
      (congrArg (precompose _ _) (mulWeakHom_intertwiner G hfg hC2))).trans ?_
    exact (precompose_unit_vertexIntertwiner G).trans
      (tensorLeftUnit_intertwiner hC2 (ambientLog G) hfg).symm
  exact congrArg (fun F => F q) key

/-- **Right unit law**: `(1 ⊠ ι) ≫ μ = ρ_V`. -/
theorem mulHom_mul_one :
    tensorMorphism hC2 (𝟙 (vObj G hfg)) (unitHom G hfg) ≫ mulHom G hfg hC2 =
      (rightUnitIso hC2 (vObj G hfg)).hom := by
  apply hom_ext
  intro q
  have key : (homComp (mulWeakHom G hfg hC2)
      (tensorMap hC2 (ambientLog G) (adjointModule (orbifoldVOA G)).toLog hfg finGen_adjoint
        (ambientLog G) (ambientLog G) hfg hfg (weakIdentity (orbifold G).adjointRestrict)
        (orbifold G).adjointInclusion)).toLinearMap =
      (tensorRightUnitHom hC2 (ambientLog G) hfg).toLinearMap := by
    apply tensor_morphism_ext hC2 (ambientLog G) (adjointModule (orbifoldVOA G)).toLog
      hfg finGen_adjoint (ambientLog G)
    refine (post_homComp_eq _ _ _ _ (tensorMap_intertwiner hC2 _ _ _ _ _ _ _ _ _ _)).trans ?_
    refine ((postcompose_precompose' _ _ _ _).trans
      (congrArg (precompose _ _) (mulWeakHom_intertwiner G hfg hC2))).trans ?_
    exact (precompose_vertexIntertwiner_unit G).trans
      (tensorRightUnit_intertwiner hC2 (ambientLog G) hfg).symm
  exact congrArg (fun F => F q) key

set_option maxHeartbeats 1000000 in
/-- **Commutativity**: `c_{V,V} ≫ μ = μ` for the braiding `swapIso … 0`. -/
theorem mulHom_comm :
    (swapIso hC2 (vObj G hfg) (vObj G hfg) 0).hom ≫ mulHom G hfg hC2 = mulHom G hfg hC2 := by
  apply hom_ext
  intro q
  have key : (homComp (mulWeakHom G hfg hC2)
      (tensorBraid hC2 (ambientLog G) (ambientLog G) hfg hfg 0)).toLinearMap =
      (mulWeakHom G hfg hC2).toLinearMap := by
    apply tensor_morphism_ext hC2 (ambientLog G) (ambientLog G) hfg hfg (ambientLog G)
    have h1 := post_homComp_eq (mulWeakHom G hfg hC2)
      (tensorBraid hC2 (ambientLog G) (ambientLog G) hfg hfg 0)
      (tensorIntertwiner hC2 (ambientLog G) (ambientLog G) hfg hfg) _
      (tensorBraid_intertwiner hC2 (ambientLog G) (ambientLog G) hfg hfg 0)
    have h2 := omega_postcompose (tensorIntertwiner hC2 (ambientLog G) (ambientLog G) hfg hfg)
      (mulWeakHom G hfg hC2) 0
    have h3 := mulWeakHom_intertwiner G hfg hC2
    refine h1.trans (h2.symm.trans ?_)
    exact (congrArg _ h3).trans ((omega_vertexIntertwiner G).trans h3.symm)
  exact congrArg (fun F => F q) key

/-- `g ∈ G` is multiplicative: `(g ⊠ g) ≫ μ = μ ≫ g`. -/
theorem autHom_mul (g : G) :
    tensorMorphism hC2 (autHom G hfg g) (autHom G hfg g) ≫ mulHom G hfg hC2 =
      mulHom G hfg hC2 ≫ autHom G hfg g := by
  apply hom_ext
  intro q
  have key : (homComp (mulWeakHom G hfg hC2)
      (tensorMap hC2 (ambientLog G) (ambientLog G) hfg hfg
        (ambientLog G) (ambientLog G) hfg hfg (autWeakHom G g) (autWeakHom G g))).toLinearMap =
      (homComp (autWeakHom G g) (mulWeakHom G hfg hC2)).toLinearMap := by
    apply tensor_morphism_ext hC2 (ambientLog G) (ambientLog G) hfg hfg (ambientLog G)
    refine (post_homComp_eq _ _ _ _ (tensorMap_intertwiner hC2 _ _ _ _ _ _ _ _ _ _)).trans ?_
    refine ((postcompose_precompose' _ _ _ _).trans
      (congrArg (precompose _ _) (mulWeakHom_intertwiner G hfg hC2))).trans ?_
    refine (precompose_aut_vertexIntertwiner G g).trans ?_
    exact (post_homComp_eq _ _ _ _ (mulWeakHom_intertwiner G hfg hC2)).symm
  exact congrArg (fun F => F q) key

/-- `g ∈ G` fixes the unit: `ι ≫ g = ι`. -/
theorem unitHom_autHom (g : G) : unitHom G hfg ≫ autHom G hfg g = unitHom G hfg := by
  apply hom_ext
  intro u
  exact u.2 g g.2

end Category

/-! ## Haploid: `Hom(𝟙, V) = ℂ ι` -/

/-- A `W^G`-module map `W^G → W` is determined by the image of the vacuum. -/
theorem hom_unit_eq_smul (φ : (unitObject : LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg) :
    ∃ c : ℂ, φ = c • unitHom G hfg := by
  let f : (orbifold G).carrier →ₗ[ℂ] V := φ.1
  have hmap : ∀ (u : (orbifold G).carrier) (n : ℤ) (x : (orbifold G).carrier),
      f (mode ((orbifoldVOA G).Y u) n x) = W.smul (u : V) n (f x) := fun u n x => φ.2 u n x
  let vac : (orbifold G).carrier := ⟨W.vacuum, (orbifold G).vacuum_mem⟩
  -- `L₀ φ(𝟙) = φ(L₀ 𝟙) = 0`, so `φ(𝟙) ∈ W₀ = ℂ𝟙`.
  have hL0 : W.L 0 (f vac) = 0 := by
    have h := hmap ⟨W.conformalVector, (orbifold G).conformal_mem⟩ 1 vac
    have h0 : mode ((orbifoldVOA G).Y ⟨W.conformalVector, (orbifold G).conformal_mem⟩) 1 vac =
        0 := by
      apply Subtype.ext
      exact (W.creation W.conformalVector).2 1 (by norm_num)
    rw [h0, map_zero] at h
    rw [VertexOperatorAlgebra.L_def]
    exact h.symm
  have hmem : f vac ∈ W.grading 0 := by
    rw [VOA.Deform.grading_eq_L_zero_eigenspace]
    exact Module.End.mem_eigenspace_iff.mpr (by rw [hL0]; simp)
  rw [W.vacuum_grade] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_⟩
  apply hom_ext
  rintro (u : (orbifold G).carrier)
  change f u = c • (u : V)
  have hu : (u : (orbifold G).carrier) = mode ((orbifoldVOA G).Y u) (-1) vac :=
    Subtype.ext (W.creation ((u : (orbifold G).carrier) : V)).1.symm
  rw [hu, hmap, ← hc]
  change mode (W.Y (u : V)) (-1) (c • W.vacuum) = c • (W.smul (u : V) (-1) W.vacuum)
  rw [map_smul]
  rfl

theorem unitHom_ne_zero [Nontrivial V] : unitHom G hfg ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : (unitObject : LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg =>
    f.1 (⟨W.vacuum, (orbifold G).vacuum_mem⟩ : (orbifold G).carrier)) h
  change W.vacuum = 0 at h1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  have := (W.creation x).1
  change mode (W.Y x) (-1) W.vacuum = x at this
  rw [← this, h1, map_zero]

/-- **Haploid**: `dim Hom_C(𝟙, V) = 1`. -/
theorem finrank_unit_hom [Nontrivial V] :
    Module.finrank ℂ ((unitObject : LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg) = 1 :=
  (finrank_eq_one_iff_of_nonzero' (unitHom G hfg) (unitHom_ne_zero G hfg)).mpr fun φ => by
    obtain ⟨c, hc⟩ := hom_unit_eq_smul G hfg φ
    exact ⟨c, hc.symm⟩

/-! ## The averaging counit `ε : V ⟶ 𝟙` -/

section Counit
variable [Fintype G]

/-- The Reynolds average `|G|⁻¹ Σ_g g v`. -/
def average (v : V) : V := (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (g : Aut W) v

theorem average_mem (v : V) : average G v ∈ (orbifold G).carrier := by
  intro h hh
  unfold average
  rw [map_smul, map_sum]
  congr 1
  let e : G ≃ G := Equiv.mulLeft ⟨h, hh⟩
  refine Fintype.sum_equiv e _ _ fun g => ?_
  change (h : Aut W) ((g : Aut W) v) = ((h * g : Aut W)) v
  rfl

/-- The averaging map as a linear map into `W^G`. -/
def averageLinear : V →ₗ[ℂ] (orbifold G).carrier where
  toFun v := ⟨average G v, average_mem G v⟩
  map_add' a b := by
    apply Subtype.ext
    change average G (a + b) = average G a + average G b
    simp only [average, map_add, Finset.sum_add_distrib, smul_add]
  map_smul' c a := by
    apply Subtype.ext
    change average G (c • a) = c • average G a
    simp only [average, map_smul, ← Finset.smul_sum]
    rw [smul_comm]

/-- **The counit** `ε : V ⟶ 𝟙`, projection onto `G`-invariants. -/
def counitHom : vObj G hfg ⟶ (unitObject : LogModuleCat (orbifoldVOA G)) :=
  ⟨averageLinear G, fun u n x => by
    apply Subtype.ext
    change average G (W.smul (u : V) n x) = mode (W.Y (u : V)) n (average G x)
    unfold average
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Aut.map_smul, u.2 g g.2]
    rfl⟩

theorem counitHom_apply (x : V) : (counitHom G hfg).1 x = averageLinear G x := rfl

/-- `ι ≫ ε = 𝟙`. -/
theorem unitHom_counitHom : unitHom G hfg ≫ counitHom G hfg = 𝟙 _ := by
  apply hom_ext
  rintro (u : (orbifold G).carrier)
  apply Subtype.ext
  change average G (u : V) = (u : V)
  unfold average
  rw [Finset.sum_congr rfl fun (g : G) _ => u.2 (g : Aut W) g.2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by
      exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- `ε ≫ ι = |G|⁻¹ Σ_g g`. -/
theorem counitHom_unitHom :
    counitHom G hfg ≫ unitHom G hfg = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, autHom G hfg g := by
  classical
  apply hom_ext
  intro x
  change average G x = ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, autHom G hfg g).1 x
  have hsum : ∀ s : Finset G, ((∑ g ∈ s, autHom G hfg g) : vObj G hfg ⟶ vObj G hfg).1 x =
      ∑ g ∈ s, (g : Aut W) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      rfl
  change average G x = (Fintype.card G : ℂ)⁻¹ • ((∑ g : G, autHom G hfg g) :
    vObj G hfg ⟶ vObj G hfg).1 x
  rw [hsum]
  rfl

end Counit

end VOA.Classification.COne.McRaeO3
