/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO3MonObj
import VOA.Classification.COne.McRaeO4bInjective
import VOA.Classification.COne.McRaeO4bSpan

/-! # O4b: the ambient VOA is rigid and self-dual in the logarithmic category of `W^G`

Here `W` is a simple VOA and `G ≤ Aut W` is finite. We assume `W^G` is `C₂`-cofinite and `W` is
finitely generated over `W^G`. Let `V = vObj G hfg` be the commutative algebra of O3 in
`C = LogModuleCat (W^G)`, with multiplication `μ`, unit `ι` and averaging counit `ε`.

This file verifies the **rigidity and dimension conditions of McRae arXiv:1910.13226,
Assumption 3.1**. There is a coevaluation `ĩ = coevHom : 𝟙 ⟶ V ⊠ V` such that:
- (R) `(V, μ ≫ ε, ĩ)` is an exact pairing of `V` with itself. Both zigzag identities hold, with
  the associator and unitors of `logarithmicMonoidalCategory`. See `vObjExactPairing` and
  `rigidity_dimension`.
- (D) `ĩ ≫ μ = |G| • ι` (`coevHom_mulHom`), and hence `ĩ ≫ μ ≫ ε = |G| • 𝟙`.

## Route: Chase–Harrison–Rosenberg, not the Kirillov functor

The route is shorter than McRae's Cor 4.8. Write `ψ_g := (1 ⊠ g) ≫ μ : V ⊠ V → V`.
1. **Surjectivity of `Ψ = (ψ_g)_g` at the vector level** (`exists_delta`). There is
   `w ∈ V ⊠ V` with `ψ_g(w) = δ_{g,1} 𝟙`. The proof:
   - `ψ_g` sends a canonical tensor mode of `a ⊠ b` to `a₍ₙ₎ g(b)` (`psi_apply_int`);
   - such twisted products span every `G`-tuple (`linearMap_mem_modeSpan_orbit`, from
     Dedekind's lemma, Jacobson density and Li's lemma).
2. **Injectivity of `Ψ` at the vector level** (`psi_injective`). The proof evaluates the
   categorical identities `GaloisData.unit_cancel` and `GaloisData.sum_theta` on the canonical
   mode `w ⊠₋₁ x`. This is the categorical form of the CHR identity
   `x = Σ_h Ψ_h(x)·h(y)…`.
3. **The coevaluation** (`coevHom`) is `u ↦ u₍₋₁₎(|G| w)`. It is a `W^G`-module map: by
   injectivity of `Ψ`, it suffices to check this after every `ψ_g`.
4. **Zigzags.** `GaloisData.exactPairing` derives both zigzags from
   `ĩ ≫ ψ_g = δ_{g,1} |G| ι`.

No Kirillov functor, no fusion rules and no rigidity of `W^G`-modules are used.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO4b
open CategoryTheory MonoidalCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO3 VOA.LogTensor.Pz
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
  (hC2 : C2Cofinite (orbifoldVOA G))

/-! ## Group-action facts -/

theorem autHom_one : autHom G hfg 1 = 𝟙 _ := by
  apply hom_ext
  intro x
  rfl

theorem autHom_inv (g : G) : autHom G hfg g⁻¹ ≫ autHom G hfg g = 𝟙 _ := by
  apply hom_ext
  intro x
  change (((g * g⁻¹ : G) : Aut W)) x = x
  rw [mul_inv_cancel]
  rfl

/-- **`V` is a Galois algebra** in the logarithmic monoidal category. -/
theorem galoisData [Fintype G] :
    letI := logarithmicMonoidalCategory hC2
    haveI := logarithmic_monoidalPreadditive hC2
    haveI := logarithmic_monoidalLinear hC2
    GaloisData (vObj G hfg) (mulHom G hfg hC2) (unitHom G hfg) (counitHom G hfg) G
      (autHom G hfg) := by
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  exact
    { one_mul := mulHom_one_mul G hfg hC2
      mul_one := mulHom_mul_one G hfg hC2
      mul_assoc := mulHom_assoc G hfg hC2
      act_mul := autHom_mul G hfg hC2
      unit_act := unitHom_autHom G hfg
      act_inv := autHom_inv G hfg
      act_one := autHom_one G hfg
      counit := counitHom_unitHom G hfg }

/-! ## The twisted products `ψ_g` -/

/-- `ψ_g = (1 ⊠ g) ≫ μ : V ⊠ V ⟶ V`, on elements `a ⊠ b ↦ a · g(b)`. -/
def psiHom (g : G) : tensorObject hC2 (vObj G hfg) (vObj G hfg) ⟶ vObj G hfg :=
  tensorMorphism hC2 (𝟙 (vObj G hfg)) (autHom G hfg g) ≫ mulHom G hfg hC2

/-- `ψ_g` on a canonical tensor mode. -/
theorem psi_apply (g : G) (n : ℂ) (a b : V) :
    (psiHom G hfg hC2 g).1 ((canonical hC2 (vObj G hfg) (vObj G hfg)).1 n 0 a b) =
      (vertexIntertwiner G).1 n 0 a ((g : Aut W) b) := by
  change (mulHom G hfg hC2).1 ((tensorMorphism hC2 (𝟙 (vObj G hfg)) (autHom G hfg g)).1
    ((canonical hC2 (vObj G hfg) (vObj G hfg)).1 n 0 a b)) = _
  rw [tensorMorphism_apply]
  exact congrArg (fun Y : LogIntertwiningOperator (orbifold G).adjointRestrict
      (orbifold G).adjointRestrict (orbifold G).adjointRestrict => Y.1 n 0 a ((g : Aut W) b))
    (mulWeakHom_intertwiner G hfg hC2)

/-- `ψ_g` on an integral canonical tensor mode: `a ⊠ₖ b ↦ a₍ₖ₎ g(b)`. -/
theorem psi_apply_int (g : G) (k : ℤ) (a b : V) :
    (psiHom G hfg hC2 g).1 ((canonical hC2 (vObj G hfg) (vObj G hfg)).1 (k : ℂ) 0 a b) =
      W.smul a k ((g : Aut W) b) := by
  rw [psi_apply, vertexIntertwiner_int]

/-! ## Surjectivity: a vector with `ψ_g(w) = δ_{g,1} 𝟙` -/

section Surj
variable [Fintype G] [DecidableEq G]

/-- The `G`-tuples realized by `Ψ`, as a subspace of `Hom(ℂ^G, W)`. -/
def realizedTuples : Submodule ℂ ((G → ℂ) →ₗ[ℂ] V) where
  carrier := {ψ | ∃ w : tensorObject hC2 (vObj G hfg) (vObj G hfg),
    ∀ g : G, ψ (Pi.single g 1) = (psiHom G hfg hC2 g).1 w}
  zero_mem' := ⟨0, fun g => by rw [map_zero]; rfl⟩
  add_mem' := by
    rintro ψ φ ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨w + w', fun g => by rw [LinearMap.add_apply, hw, hw', map_add]; rfl⟩
  smul_mem' := by
    rintro c ψ ⟨w, hw⟩
    exact ⟨c • w, fun g => by rw [LinearMap.smul_apply, hw, map_smul]; rfl⟩

theorem orbitMap_single_apply (b : V) (g : G) :
    VOA.Huang.SchurWeyl.orbitMap G b (Pi.single g 1) = (g : Aut W) b := by
  rw [VOA.Huang.SchurWeyl.orbitMap_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hh
    rw [Pi.single_eq_of_ne hh, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem modeSpan_le_realizedTuples :
    VOA.Moonshine.SigmaExist.modeSpan (VOA.Huang.SchurWeyl.homModule W (G → ℂ))
      (Set.range (VOA.Huang.SchurWeyl.orbitMap G)) ≤ realizedTuples G hfg hC2 := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨a, q, x, ⟨b, rfl⟩, rfl⟩
  refine ⟨(canonical hC2 (vObj G hfg) (vObj G hfg)).1 (q : ℂ) 0 a b, fun g => ?_⟩
  rw [psi_apply_int, VOA.Huang.SchurWeyl.homModule_act, LinearMap.comp_apply,
    orbitMap_single_apply, VOA.Huang.SchurWeyl.modeOp_apply]

/-- **Surjectivity of `Ψ` onto `δ_{g,1} 𝟙`.** -/
theorem exists_delta (hW : W.IsSimple) :
    ∃ w : tensorObject hC2 (vObj G hfg) (vObj G hfg),
      ∀ g : G, (psiHom G hfg hC2 g).1 w = if g = 1 then W.vacuum else 0 := by
  let ψ₀ : (G → ℂ) →ₗ[ℂ] V := (LinearMap.proj (1 : G)).smulRight W.vacuum
  obtain ⟨w, hw⟩ := modeSpan_le_realizedTuples G hfg hC2
    (VOA.Huang.SchurWeyl.linearMap_mem_modeSpan_orbit G hW ψ₀)
  refine ⟨w, fun g => ?_⟩
  rw [← hw g]
  change (Pi.single g (1 : ℂ) : G → ℂ) 1 • W.vacuum = _
  by_cases hg : g = 1
  · subst hg
    rw [Pi.single_eq_same, one_smul, if_pos rfl]
  · rw [Pi.single_eq_of_ne' hg, zero_smul, if_neg hg]

end Surj

/-! ## Injectivity of `Ψ` -/

/-- A right whisker on a canonical mode. -/
theorem whiskerRight_apply {N₁ P₁ : LogModuleCat (orbifoldVOA G)} (Q : LogModuleCat (orbifoldVOA G))
    (f : N₁ ⟶ P₁) (n : ℂ) (x : N₁) (y : Q) :
    (tensorMorphism hC2 f (𝟙 Q)).1 ((canonical hC2 N₁ Q).1 n 0 x y) =
      (canonical hC2 P₁ Q).1 n 0 (f.1 x) y :=
  tensorMorphism_apply hC2 f (𝟙 Q) n 0 x y

/-- A left whisker on a canonical mode. -/
theorem whiskerLeft_apply (Q : LogModuleCat (orbifoldVOA G)) {N₂ P₂ : LogModuleCat (orbifoldVOA G)}
    (f : N₂ ⟶ P₂) (n : ℂ) (x : Q) (y : N₂) :
    (tensorMorphism hC2 (𝟙 Q) f).1 ((canonical hC2 Q N₂).1 n 0 x y) =
      (canonical hC2 Q P₂).1 n 0 x (f.1 y) :=
  tensorMorphism_apply hC2 (𝟙 Q) f n 0 x y

/-- `ψ_1 = μ`. -/
theorem psiHom_one : psiHom G hfg hC2 1 = mulHom G hfg hC2 := by
  unfold psiHom
  rw [autHom_one]
  have h := (tensorBifunctor hC2).map_id ((vObj G hfg, vObj G hfg) :
    LogModuleCat (orbifoldVOA G) × LogModuleCat (orbifoldVOA G))
  change tensorMorphism hC2 (𝟙 (vObj G hfg)) (𝟙 (vObj G hfg)) = _ at h
  rw [h]
  exact Category.id_comp _

/-- `GaloisData.unit_cancel`, in concrete form. -/
theorem unit_cancel_concrete [Fintype G] :
    (leftUnitIso hC2 (tensorObject hC2 (vObj G hfg) (vObj G hfg))).inv ≫
      tensorMorphism hC2 (unitHom G hfg) (𝟙 (tensorObject hC2 (vObj G hfg) (vObj G hfg))) ≫
      (associatorIso hC2 (vObj G hfg) (vObj G hfg) (vObj G hfg)).inv ≫
      tensorMorphism hC2 (mulHom G hfg hC2) (𝟙 (vObj G hfg)) = 𝟙 _ := by
  classical
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  exact (galoisData G hfg hC2).unit_cancel

/-- `GaloisData.sum_theta`, in concrete form. -/
theorem sum_theta_concrete [Fintype G] :
    ∑ h : G, tensorMorphism hC2 (psiHom G hfg hC2 h)
        (𝟙 (tensorObject hC2 (vObj G hfg) (vObj G hfg))) ≫
      (associatorIso hC2 (vObj G hfg) (vObj G hfg) (vObj G hfg)).inv ≫
      tensorMorphism hC2 (psiHom G hfg hC2 h) (𝟙 (vObj G hfg)) =
    ∑ y : G, tensorMorphism hC2 (𝟙 (tensorObject hC2 (vObj G hfg) (vObj G hfg)))
        (psiHom G hfg hC2 y⁻¹) ≫
      (associatorIso hC2 (vObj G hfg) (vObj G hfg) (vObj G hfg)).hom ≫
      tensorMorphism hC2 (𝟙 (vObj G hfg))
        (tensorMorphism hC2 (autHom G hfg y) (autHom G hfg y) ≫ mulHom G hfg hC2) := by
  classical
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  exact (galoisData G hfg hC2).sum_theta

/-- **Injectivity of `Ψ`**: the twisted products `ψ_g` are jointly injective on `V ⊠ V`. -/
theorem psi_injective (hW : W.IsSimple) [Fintype G]
    (w : tensorObject hC2 (vObj G hfg) (vObj G hfg))
    (h : ∀ g : G, (psiHom G hfg hC2 g).1 w = 0) : w = 0 := by
  classical
  obtain ⟨w', hw'⟩ := exists_delta G hfg hC2 hW
  exact injective_of_theta hC2 (mulHom G hfg hC2) (unitHom G hfg) (psiHom G hfg hC2)
    (fun y => (associatorIso hC2 (vObj G hfg) (vObj G hfg) (vObj G hfg)).hom ≫
      tensorMorphism hC2 (𝟙 (vObj G hfg))
        (tensorMorphism hC2 (autHom G hfg y) (autHom G hfg y) ≫ mulHom G hfg hC2))
    (unit_cancel_concrete G hfg hC2) (sum_theta_concrete G hfg hC2) (psiHom_one G hfg hC2)
    w' hw' w h

/-! ## The coevaluation `ĩ : 𝟙 ⟶ V ⊠ V` -/

section Coev
variable [Fintype G] [DecidableEq G] (hW : W.IsSimple)

/-- The scalar `|G| δ_{g,1}`. -/
def deltaCoeff (g : G) : ℂ := if g = 1 then (Fintype.card G : ℂ) else 0

/-- The vector `t = |G| w ∈ V ⊠ V`, where `ψ_g(w) = δ_{g,1} 𝟙`. -/
def coevVector : tensorObject hC2 (vObj G hfg) (vObj G hfg) :=
  (Fintype.card G : ℂ) • Classical.choose (exists_delta G hfg hC2 hW)

theorem psi_coevVector (g : G) :
    (psiHom G hfg hC2 g).1 (coevVector G hfg hC2 hW) = deltaCoeff G g • W.vacuum := by
  unfold coevVector deltaCoeff
  rw [map_smul, Classical.choose_spec (exists_delta G hfg hC2 hW) g]
  by_cases hg : g = 1
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg, zero_smul]
    change (Fintype.card G : ℂ) • (0 : V) = 0
    exact smul_zero _

omit [Fintype G] [DecidableEq G] in
/-- `ψ_g` commutes with the `W^G`-modes. -/
theorem psi_mode (g : G) (a : (orbifold G).carrier) (p : ℤ)
    (r : tensorObject hC2 (vObj G hfg) (vObj G hfg)) :
    (psiHom G hfg hC2 g).1
        (mode ((tensorObject hC2 (vObj G hfg) (vObj G hfg)).act.toWeakModule.YM a) p r) =
      W.smul (a : V) p ((psiHom G hfg hC2 g).1 r) :=
  (psiHom G hfg hC2 g).2 a p r

/-- The underlying linear map of `ĩ`: `u ↦ u₍₋₁₎ t`. -/
def coevLinear :
    (orbifold G).carrier →ₗ[ℂ] tensorObject hC2 (vObj G hfg) (vObj G hfg) where
  toFun x := mode ((tensorObject hC2 (vObj G hfg) (vObj G hfg)).act.toWeakModule.YM x) (-1)
    (coevVector G hfg hC2 hW)
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

theorem psi_coevLinear (g : G) (x : (orbifold G).carrier) :
    (psiHom G hfg hC2 g).1 (coevLinear G hfg hC2 hW x) = deltaCoeff G g • (x : V) := by
  change (psiHom G hfg hC2 g).1
    (mode ((tensorObject hC2 (vObj G hfg) (vObj G hfg)).act.toWeakModule.YM x) (-1)
      (coevVector G hfg hC2 hW)) = _
  rw [psi_mode, psi_coevVector, PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_def,
    (W.creation (x : V)).1]

/-- **The coevaluation** `ĩ : 𝟙 = W^G ⟶ V ⊠ V`. -/
def coevHom : (unitObject : LogModuleCat (orbifoldVOA G)) ⟶
    tensorObject hC2 (vObj G hfg) (vObj G hfg) :=
  ⟨coevLinear G hfg hC2 hW, fun a p r => by
    rw [← sub_eq_zero]
    apply psi_injective G hfg hC2 hW
    intro g
    rw [map_sub, sub_eq_zero, psi_mode]
    erw [psi_coevLinear, psi_coevLinear]
    rw [PreVertexAlgebra.smul_smul_right]
    rfl⟩

/-- `ĩ ≫ ψ_g = δ_{g,1} |G| ι`. -/
theorem coevHom_psi (g : G) :
    coevHom G hfg hC2 hW ≫ psiHom G hfg hC2 g =
      if g = 1 then (Fintype.card G : ℂ) • unitHom G hfg else 0 := by
  apply hom_ext
  intro x
  change (psiHom G hfg hC2 g).1 (coevLinear G hfg hC2 hW x) = _
  rw [psi_coevLinear]
  unfold deltaCoeff
  by_cases hg : g = 1
  · rw [if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg, zero_smul]
    rfl

end Coev

/-! ## Headlines: rigidity (R) and dimension (D) of McRae Assumption 3.1 -/

section Headline
variable [Fintype G] [DecidableEq G] (hW : W.IsSimple)
include hW

/-- **`V` is self-dual in `C`**: the exact pairing `(ĩ, μ ≫ ε)` of `V` with itself. -/
abbrev vObjExactPairing :
    letI := logarithmicMonoidalCategory hC2
    ExactPairing (vObj G hfg) (vObj G hfg) :=
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  (galoisData G hfg hC2).exactPairing (coevHom G hfg hC2 hW) (coevHom_psi G hfg hC2 hW)

/-- **(D)** `ĩ ≫ μ = |G| • ι`. -/
theorem coevHom_mulHom :
    coevHom G hfg hC2 hW ≫ mulHom G hfg hC2 = (Fintype.card G : ℂ) • unitHom G hfg := by
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  exact (galoisData G hfg hC2).coev_mul (coevHom G hfg hC2 hW) (coevHom_psi G hfg hC2 hW)

/-- The categorical dimension: `ĩ ≫ μ ≫ ε = |G| • 𝟙`. -/
theorem coevHom_mulHom_counitHom :
    coevHom G hfg hC2 hW ≫ mulHom G hfg hC2 ≫ counitHom G hfg =
      (Fintype.card G : ℂ) • 𝟙 _ := by
  rw [← Category.assoc, coevHom_mulHom, Linear.smul_comp, unitHom_counitHom]

/-- **Rigidity and dimension conditions of McRae arXiv:1910.13226, Assumption 3.1**, for
`V = W` over `W^G` (`W` simple, `G` finite, `W^G` `C₂`-cofinite, `W` finitely generated over `W^G`):
there is `ĩ : 𝟙 ⟶ V ⊗ V` making `(V, μ ≫ ε, ĩ)` a dual of `V` (both zigzag identities, with
the associator and unitors of `logarithmicMonoidalCategory`), and `ĩ ≫ μ = |G| • ι`. -/
theorem rigidity_dimension :
    letI := logarithmicMonoidalCategory hC2
    ∃ coev : 𝟙_ (LogModuleCat (orbifoldVOA G)) ⟶ vObj G hfg ⊗ vObj G hfg,
      coev ▷ vObj G hfg ≫ (α_ _ _ _).hom ≫ vObj G hfg ◁ (mulHom G hfg hC2 ≫ counitHom G hfg) =
          (λ_ _).hom ≫ (ρ_ _).inv ∧
        vObj G hfg ◁ coev ≫ (α_ _ _ _).inv ≫ (mulHom G hfg hC2 ≫ counitHom G hfg) ▷ vObj G hfg =
          (ρ_ _).hom ≫ (λ_ _).inv ∧
        coev ≫ mulHom G hfg hC2 = (Fintype.card G : ℂ) • unitHom G hfg := by
  letI := logarithmicMonoidalCategory hC2
  haveI := logarithmic_monoidalPreadditive hC2
  haveI := logarithmic_monoidalLinear hC2
  have D := galoisData G hfg hC2
  exact ⟨coevHom G hfg hC2 hW,
    D.evaluation_coevaluation _ (coevHom_psi G hfg hC2 hW),
    D.coevaluation_evaluation _ (coevHom_psi G hfg hC2 hW),
    coevHom_mulHom G hfg hC2 hW⟩

/-- **The case `V₂`**: for every finite `G ≤ Aut V₂` with `C₂`-cofinite `V₂^G`, the rigidity
and dimension conditions of McRae's Assumption 3.1 hold for `V₂` over `V₂^G`. -/
theorem V2m_rigidity_dimension (G : Subgroup (Aut (V2m 1 le_rfl))) [Fintype G]
    (hC2 : C2Cofinite (orbifoldVOA G)) :
    letI := logarithmicMonoidalCategory hC2
    ∃ coev : 𝟙_ (LogModuleCat (orbifoldVOA G)) ⟶ V2mObj G ⊗ V2mObj G,
      coev ▷ V2mObj G ≫ (α_ _ _ _).hom ≫
          V2mObj G ◁ (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2 ≫
            counitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) =
          (λ_ _).hom ≫ (ρ_ _).inv ∧
        V2mObj G ◁ coev ≫ (α_ _ _ _).inv ≫
          (mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2 ≫
            counitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)) ▷ V2mObj G =
          (ρ_ _).hom ≫ (λ_ _).inv ∧
        coev ≫ mulHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2 =
          (Fintype.card G : ℂ) • unitHom G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) := by
  classical
  exact rigidity_dimension G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2
    (V2m_isSimple 1 le_rfl)

end Headline

end VOA.Classification.COne.McRaeO4b
