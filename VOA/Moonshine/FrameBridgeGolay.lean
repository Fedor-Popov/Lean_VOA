/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameBridge

/-!
# `golayV0 ≅ V0P` and the triality on `V₀⁺`  (M8g-0, part 2: the `c_λ` residual)

`golayV0 = V_N^{⟨χ,Θ⟩}` (`TrialityGolay.lean`, `N = N(A₁²⁴)`, `Θ = σχσ`) is identified with
`V0P = V₀⁺ ⊆ V_Λ` (`FrameSectors.lean`) as vertex operator algebras, and the triality
`golaySigma0 : Aut golayV0` is transported to `v0Sigma : Aut V0P`.

## The argument
1. `χ` and `Θ` commute (`golayChi_golayTheta`: `Θ` maps `F_λ → F_{−λ}` and `χ = (−1)^{parity}` is
   even), so `Θ` preserves `V_N^χ = bridgeN(V_{Λ₀})` (`FrameBridge.lean`).
2. Pulling back gives `ψ := bridgeN⁻¹ Θ bridgeN ∈ Aut(V_{Λ₀})` (`lam0Psi`, via `Aut.pullback`).
   It negates every `α(−1)𝟙` (`lam0Psi_hSt`; from `golayTheta_hSt` on the 24 roots, since
   `2μ = ∑ⱼ μⱼ α_j`) and maps `F_λ → F_{−λ}` (`lam0Psi_chargeSec`, from `golayTheta_chargeSec`).
3. **The `c_λ` residual.**  By the rigidity theorem `lift_eq_conj_theta'`
   (`LatticeMorphRigid.lean`) there is a character `e : Λ₀ → ℂˣ` (`golayE`) with
   `ψ = g_e θ g_e⁻¹` (`lam0Psi_eq`).  Concretely `Θ e^λ = c_λ e^{−λ}` on `V_{Λ₀} ⊆ V_N` with
   `c_λ = e(λ)^{−2}` (in the `bridgeN` normalisation, `lam0Psi_latChargeGen`): the unknown
   scalars are a character, and the lift is conjugate to the standard `θ`.
4. Hence `golayV0 = bridgeN(g_e(V_{Λ₀}^θ))` (`lam0PlusToGolay`, bijective), and composing with
   `lam0PlusEquiv : V_{Λ₀}⁺ ≅ V0P` gives `golayToV0 : golayV0 ≃ V0P`, a VOA isomorphism
   (`golayToV0_isVOAHom`, `golayToV0_omega`).
5. `v0Sigma := golayToV0 ∘ σ₀ ∘ golayToV0⁻¹ ∈ Aut(V0P)` with `v0Sigma_sq`, `v0Sigma_ne_one`,
   `golayToV0_sigma`.

## Status
All declarations `sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
Unconditional.  The character `golayE` is obtained by choice (an existence theorem), not
computed.  What `v0Sigma` does to the `ℤ/2`-sectors of `V_Λ⁺` (e.g. `V₀⁻ ↔ V₁⁺`) is not stated
here: those sectors are outside `V0P`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA

/-! ## §0  Generic transport along VOA isomorphisms -/

section Transport

variable {𝒱 𝒲 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {W : VertexOperatorAlgebra 𝒲}

theorem IsVOAHom.symm_of_equiv (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap) :
    IsVOAHom W V E.symm.toLinearMap where
  map_vacuum := by
    apply E.injective
    change E (E.symm W.vacuum) = E V.vacuum
    rw [LinearEquiv.apply_symm_apply]
    exact hE.map_vacuum.symm
  map_smul u n v := by
    apply E.injective
    change E (E.symm (W.smul u n v)) = E (V.smul (E.symm u) n (E.symm v))
    rw [LinearEquiv.apply_symm_apply]
    have h := hE.map_smul (E.symm u) n (E.symm v)
    change E (V.smul (E.symm u) n (E.symm v)) = W.smul (E (E.symm u)) n (E (E.symm v)) at h
    rw [h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **Transport of automorphisms** along a VOA isomorphism `E`: `g ↦ E g E⁻¹`. -/
noncomputable def Aut.transport (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap)
    (hω : E V.conformalVector = W.conformalVector) (g : Aut V) : Aut W where
  toLinearEquiv := E.symm.trans (g.toLinearEquiv.trans E)
  map_smul' u n v := by
    have hs := (IsVOAHom.symm_of_equiv E hE).map_smul u n v
    change E (g (E.symm (W.smul u n v))) = W.smul (E (g (E.symm u))) n (E (g (E.symm v)))
    change E.symm (W.smul u n v) = V.smul (E.symm u) n (E.symm v) at hs
    rw [hs, g.map_smul]
    exact hE.map_smul _ n _
  map_vacuum := by
    change E (g (E.symm W.vacuum)) = W.vacuum
    have hs := (IsVOAHom.symm_of_equiv E hE).map_vacuum
    change E.symm W.vacuum = V.vacuum at hs
    rw [hs, g.map_vacuum]
    exact hE.map_vacuum
  map_omega := by
    change E (g (E.symm W.conformalVector)) = W.conformalVector
    rw [← hω, LinearEquiv.symm_apply_apply, g.map_omega]

theorem Aut.transport_apply (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap)
    (hω : E V.conformalVector = W.conformalVector) (g : Aut V) (x : 𝒱) :
    Aut.transport E hE hω g (E x) = E (g x) := by
  change E (g (E.symm (E x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem Aut.transport_mul (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap)
    (hω : E V.conformalVector = W.conformalVector) (g h : Aut V) :
    Aut.transport E hE hω (g * h) = Aut.transport E hE hω g * Aut.transport E hE hω h := by
  refine Aut.ext (LinearEquiv.ext fun x => ?_)
  change E ((g * h) (E.symm x)) = E (g (E.symm (E (h (E.symm x)))))
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem Aut.transport_one (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap)
    (hω : E V.conformalVector = W.conformalVector) : Aut.transport E hE hω 1 = 1 := by
  refine Aut.ext (LinearEquiv.ext fun x => ?_)
  change E (E.symm x) = x
  rw [LinearEquiv.apply_symm_apply]

theorem Aut.transport_injective (E : 𝒱 ≃ₗ[ℂ] 𝒲) (hE : IsVOAHom V W E.toLinearMap)
    (hω : E V.conformalVector = W.conformalVector) :
    Function.Injective (Aut.transport E hE hω) := by
  intro g h hgh
  refine Aut.ext (LinearEquiv.ext fun x => ?_)
  have := congrArg (fun k : Aut W => k (E x)) hgh
  simp only [Aut.transport_apply] at this
  exact E.injective this

end Transport

/-- Membership in the fixed points of a group generated by two elements. -/
theorem mem_orbifold_closure_pair {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (a b : Aut W) (v : 𝒱) :
    v ∈ (orbifold (Subgroup.closure {a, b})).carrier ↔ a v = v ∧ b v = v := by
  constructor
  · intro hv
    exact ⟨hv a (Subgroup.subset_closure (Set.mem_insert _ _)),
      hv b (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩
  · rintro ⟨ha, hb⟩
    let S : Subgroup (Aut W) :=
      { carrier := {h | h v = v}
        mul_mem' := fun {x y} hx hy => by
          change x (y v) = v
          rw [show y v = v from hy]; exact hx
        one_mem' := rfl
        inv_mem' := fun {x} hx => by
          change x.toLinearEquiv.symm v = v
          rw [LinearEquiv.symm_apply_eq]; exact hx.symm }
    have hS : Subgroup.closure {a, b} ≤ S := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact ha
      · exact hb
    exact fun h hh => hS hh

namespace Moonshine

open VOA.IntegralLattice VOA.LatGen Module
open VOA.Moonshine.Triality

/-! ## §1  `χ` and `Θ` commute; `Θ` on the Heisenberg states -/

theorem golayChi_latStateGen (p : HeisenbergN.FockN (rank golayN)) (γ : golayN.carrier) :
    golayChi (latStateGen golayN p γ) = chiSign golayN golayParity γ • latStateGen golayN p γ :=
  chiLat_latStateGen golayN golayParity p γ

theorem golayChi_golayTheta (x : LatModuleGen golayN) :
    golayChi (golayTheta x) = golayTheta (golayChi x) := by
  have h : golayChi.toLinearEquiv.toLinearMap ∘ₗ golayTheta.toLinearEquiv.toLinearMap
      = golayTheta.toLinearEquiv.toLinearMap ∘ₗ golayChi.toLinearEquiv.toLinearMap := by
    refine LinearMap.ext_on_range (latStateGen_span golayN) fun q => ?_
    obtain ⟨p, γ⟩ := q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    obtain ⟨r, hr⟩ := golayTheta_chargeSec γ (mem_chargeSec golayN γ p)
    rw [golayChi_latStateGen, Aut.map_smul_c, ← hr, mkEα_apply, ← latStateGen,
      golayChi_latStateGen, chiSign_neg]
  exact LinearMap.congr_fun h x

/-- `N(A₁²⁴) → ℤ²⁴` as an additive map. -/
def gvHom : golayN.carrier →+ (Fin 24 → ℤ) where
  toFun := gv
  map_zero' := rfl
  map_add' := gv_add

theorem two_smul_eq_sum_roots (μ : golayN.carrier) :
    (2 : ℤ) • μ = ∑ j : Fin 24, gv μ j • golayRoot j := by
  apply gv_injective
  change gvHom ((2 : ℤ) • μ) = gvHom (∑ j : Fin 24, gv μ j • golayRoot j)
  rw [map_zsmul, map_sum]
  simp only [map_zsmul]
  funext i
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  change 2 * gv μ i = ∑ j, gv μ j * gv (golayRoot j) i
  simp only [golayRoot_coe, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp [mul_comm]

/-- `Θ` negates **every** Heisenberg state `μ(−1)𝟙`, `μ ∈ N`. -/
theorem golayTheta_hSt_all (μ : golayN.carrier) : golayTheta (hSt golayN μ) = -hSt golayN μ := by
  let H : golayN.carrier →+ LatModuleGen golayN :=
    { toFun := hSt golayN, map_zero' := hSt_zero golayN, map_add' := hSt_add golayN }
  have hz : ∀ (n : ℤ) (x : LatModuleGen golayN), golayTheta (n • x) = n • golayTheta x :=
    fun n x => map_zsmul golayTheta.toLinearEquiv n x
  have h2 : golayTheta (H ((2 : ℤ) • μ)) = -H ((2 : ℤ) • μ) := by
    rw [two_smul_eq_sum_roots, map_sum, map_sum]
    have : ∀ j : Fin 24, golayTheta (H (gv μ j • golayRoot j)) = -H (gv μ j • golayRoot j) := by
      intro j
      rw [map_zsmul, hz]
      change gv μ j • golayTheta (hSt golayN (golayRoot j)) = -(gv μ j • hSt golayN (golayRoot j))
      rw [golayTheta_hSt j, zsmul_neg]
    simp only [this, Finset.sum_neg_distrib]
  rw [map_zsmul, hz, two_zsmul, two_zsmul] at h2
  change golayTheta (hSt golayN μ) + golayTheta (hSt golayN μ)
    = -(hSt golayN μ + hSt golayN μ) at h2
  have h3 : (2 : ℂ) • (golayTheta (hSt golayN μ) + hSt golayN μ) = 0 := by
    rw [two_smul]
    calc golayTheta (hSt golayN μ) + hSt golayN μ + (golayTheta (hSt golayN μ) + hSt golayN μ)
        = (golayTheta (hSt golayN μ) + golayTheta (hSt golayN μ))
          + (hSt golayN μ + hSt golayN μ) := by abel
      _ = 0 := by rw [h2]; abel
  rcases smul_eq_zero.mp h3 with h3 | h3
  · norm_num at h3
  · exact eq_neg_of_add_eq_zero_left h3

theorem golayTheta_golayTheta (x : LatModuleGen golayN) : golayTheta (golayTheta x) = x := by
  rw [← Aut.mul_apply, golayTheta_sq, Aut.one_apply]

theorem golayTheta_range_bridgeN :
    (LinearMap.range bridgeN).map golayTheta.toLinearEquiv.toLinearMap = LinearMap.range bridgeN := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_range_bridgeN_iff] at hx ⊢
    change golayChi (golayTheta x) = golayTheta x
    rw [golayChi_golayTheta, hx]
  · intro hy
    refine ⟨golayTheta y, ?_, golayTheta_golayTheta y⟩
    rw [mem_range_bridgeN_iff] at hy ⊢
    rw [golayChi_golayTheta, hy]

/-! ## §2  The pulled-back involution `ψ` on `V_{Λ₀}` and its rigidity -/

/-- `ψ = bridgeN⁻¹ Θ bridgeN ∈ Aut(V_{Λ₀})`. -/
noncomputable def lam0Psi : Aut lam0VOA :=
  Aut.pullback bridgeN bridgeN_injective golayTheta golayTheta_range_bridgeN bridgeN_isVOAHom
    bridgeN_omega

theorem bridgeN_lam0Psi (x : LatModuleGen lam0) : bridgeN (lam0Psi x) = golayTheta (bridgeN x) :=
  Aut.pullback_apply _ _ _ _ _ _ x

theorem bridgeN_hSt (α : lam0.carrier) : bridgeN (hSt lam0 α) = hSt golayN (inclN α) :=
  latMorphC_hSt lam0 golayN inclN _ (latCob_zero _ _ _) lam0_posDef α

theorem lam0Psi_hSt (α : lam0.carrier) : lam0Psi (hSt lam0 α) = -hSt lam0 α := by
  apply bridgeN_injective
  rw [bridgeN_lam0Psi, bridgeN_hSt, golayTheta_hSt_all, map_neg, bridgeN_hSt]

theorem bridgeN_mem_chargeSec {γ : lam0.carrier} {x : LatModuleGen lam0} (hx : x ∈ chargeSec lam0 γ) :
    bridgeN x ∈ chargeSec golayN (inclN γ) := by
  obtain ⟨q, rfl⟩ := hx
  rw [mkEα_apply, ← latStateGen, bridgeN, latMorph_latStateGen]
  exact Submodule.smul_mem _ _ (mem_chargeSec golayN _ _)

theorem lam0Psi_chargeSec (γ : lam0.carrier) (x : LatModuleGen lam0) (hx : x ∈ chargeSec lam0 γ) :
    lam0Psi x ∈ chargeSec lam0 (-γ) := by
  have h := golayTheta_chargeSec (inclN γ) (bridgeN_mem_chargeSec hx)
  rw [← bridgeN_lam0Psi, ← map_neg] at h
  exact mem_chargeSec_of_latMorphC lam0 golayN inclN _ (latCob_ne_zero _ _ _) lam0_posDef
    golayN_posDef inclN_form rank_lam0_golayN h

theorem exists_golayE :
    ∃ e : lam0.carrier →+ Additive ℂˣ,
      ∀ x, lam0Psi x = charLat lam0 e (thetaLat lam0 (charLat lam0 (-e) x)) :=
  lift_eq_conj_theta' lam0 lam0_even lam0_posDef lam0Psi lam0Psi_hSt lam0Psi_chargeSec

/-- **The character conjugating `θ` to `ψ`** (chosen). -/
noncomputable def golayE : lam0.carrier →+ Additive ℂˣ := exists_golayE.choose

/-- **`ψ = g_e θ g_e⁻¹`**: the pulled-back `Θ` is conjugate to the standard `θ` of `V_{Λ₀}`. -/
theorem lam0Psi_eq (x : LatModuleGen lam0) :
    lam0Psi x = charLat lam0 golayE (thetaLat lam0 (charLat lam0 (-golayE) x)) :=
  exists_golayE.choose_spec x

/-- **The scalars `c_λ`**: `Θ` acts on the charged vacua of `V_{Λ₀} ⊆ V_N` by
`Θ e^λ = e(λ)⁻² e^{−λ}` (in the `bridgeN` normalisation). -/
theorem lam0Psi_latChargeGen (γ : lam0.carrier) :
    lam0Psi (latChargeGen lam0 γ)
      = (charVal lam0 golayE (-γ) * charVal lam0 (-golayE) γ) • latChargeGen lam0 (-γ) := by
  rw [lam0Psi_eq, latChargeGen, charLat_latStateGen lam0 _ lam0_posDef, map_smul,
    thetaLat_latStateGen, map_smul, charLat_latStateGen lam0 _ lam0_posDef, smul_smul,
    show sigmaN (rank lam0) (HeisenbergN.vacuumN (rank lam0)) = HeisenbergN.vacuumN (rank lam0)
      from sigmaN_one _, mul_comm]
  rfl

theorem golayTheta_bridgeN_latChargeGen (γ : lam0.carrier) :
    golayTheta (bridgeN (latChargeGen lam0 γ))
      = (charVal lam0 golayE (-γ) * charVal lam0 (-golayE) γ) • bridgeN (latChargeGen lam0 (-γ)) := by
  rw [← bridgeN_lam0Psi, lam0Psi_latChargeGen, map_smul]

/-! ## §3  `golayV0 = bridgeN (g_e (V_{Λ₀}^θ))` -/

theorem mem_golayV0_iff (x : LatModuleGen golayN) :
    x ∈ (orbifold golayK).carrier ↔ golayChi x = x ∧ golayTheta x = x :=
  mem_orbifold_closure_pair golayChi golayTheta x

/-- The character automorphism `g_e` of `V_{Λ₀}`. -/
noncomputable def lam0CharAut : Aut lam0VOA := charAut lam0 golayE lam0_even lam0_posDef

theorem charLat_neg_charLat (x : LatModuleGen lam0) :
    charLat lam0 (-golayE) (charLat lam0 golayE x) = x := by
  rw [charLat_comp lam0 _ lam0_posDef, neg_add_cancel, charLat_zero lam0 lam0_posDef]

theorem charLat_charLat_neg (x : LatModuleGen lam0) :
    charLat lam0 golayE (charLat lam0 (-golayE) x) = x := by
  rw [charLat_comp lam0 _ lam0_posDef, add_neg_cancel, charLat_zero lam0 lam0_posDef]

/-- The map `V_{Λ₀}⁺ → golayV0`, `z ↦ bridgeN (g_e z)`. -/
noncomputable def lam0PlusToGolay : Lam0PlusCarrier →ₗ[ℂ] (orbifold golayK).carrier :=
  ((bridgeN ∘ₗ charLat lam0 golayE) ∘ₗ (orbifold (Subgroup.zpowers lam0Theta)).carrier.subtype).codRestrict
    _ fun z => by
      rw [mem_golayV0_iff]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      refine ⟨(mem_range_bridgeN_iff _).mp ⟨_, rfl⟩, ?_⟩
      rw [← bridgeN_lam0Psi, lam0Psi_eq, charLat_neg_charLat, (mem_lam0Plus_iff _).mp z.2]

@[simp] theorem lam0PlusToGolay_coe (z : Lam0PlusCarrier) :
    ((lam0PlusToGolay z : (orbifold golayK).carrier) : LatModuleGen golayN)
      = bridgeN (charLat lam0 golayE z) := rfl

theorem lam0PlusToGolay_bijective : Function.Bijective lam0PlusToGolay := by
  constructor
  · intro z w h
    have h1 := congrArg (fun y : (orbifold golayK).carrier => (y : LatModuleGen golayN)) h
    simp only [lam0PlusToGolay_coe] at h1
    have h2 := congrArg (charLat lam0 (-golayE)) (bridgeN_injective h1)
    rw [charLat_neg_charLat, charLat_neg_charLat] at h2
    exact Subtype.ext h2
  · intro y
    have hy := (mem_golayV0_iff y).mp y.2
    obtain ⟨w, hw⟩ := (mem_range_bridgeN_iff _).mpr hy.1
    have hψ : lam0Psi w = w := by
      apply bridgeN_injective
      rw [bridgeN_lam0Psi, hw, hy.2]
    have hθ : thetaLat lam0 (charLat lam0 (-golayE) w) = charLat lam0 (-golayE) w := by
      have h := congrArg (charLat lam0 (-golayE)) hψ
      rw [lam0Psi_eq, charLat_neg_charLat] at h
      exact h
    refine ⟨⟨charLat lam0 (-golayE) w, (mem_lam0Plus_iff _).mpr hθ⟩, ?_⟩
    apply Subtype.ext
    rw [lam0PlusToGolay_coe]
    change bridgeN (charLat lam0 golayE (charLat lam0 (-golayE) w)) = y
    rw [charLat_charLat_neg, hw]

theorem lam0PlusToGolay_isVOAHom : IsVOAHom lam0Plus golayV0 lam0PlusToGolay where
  map_vacuum := by
    apply Subtype.ext
    change bridgeN (lam0CharAut lam0VOA.vacuum) = golayVOA.vacuum
    rw [lam0CharAut.map_vacuum]
    exact bridgeN_isVOAHom.map_vacuum
  map_smul u n v := by
    apply Subtype.ext
    change bridgeN (lam0CharAut (lam0VOA.smul u n v))
      = golayVOA.smul (bridgeN (lam0CharAut u)) n (bridgeN (lam0CharAut v))
    rw [lam0CharAut.map_smul]
    exact bridgeN_isVOAHom.map_smul _ n _

theorem lam0PlusToGolay_omega :
    lam0PlusToGolay lam0Plus.conformalVector = golayV0.conformalVector := by
  apply Subtype.ext
  change bridgeN (lam0CharAut lam0VOA.conformalVector) = golayVOA.conformalVector
  rw [lam0CharAut.map_omega]
  exact bridgeN_omega

/-- `V_{Λ₀}⁺ ≃ golayV0`. -/
noncomputable def lam0PlusGolayEquiv : Lam0PlusCarrier ≃ₗ[ℂ] (orbifold golayK).carrier :=
  LinearEquiv.ofBijective lam0PlusToGolay lam0PlusToGolay_bijective

/-! ## §4  `golayV0 ≅ V0P` and the triality on `V₀⁺` -/

/-- **`golayV0 ≃ V0P`** (`V_N^{⟨χ,Θ⟩} ≅ V₀⁺`). -/
noncomputable def golayToV0 : (orbifold golayK).carrier ≃ₗ[ℂ] V0Sub.carrier :=
  lam0PlusGolayEquiv.symm.trans lam0PlusEquiv

/-- `golayToV0` is a homomorphism of vertex operator algebras. -/
theorem golayToV0_isVOAHom : IsVOAHom golayV0 V0P golayToV0.toLinearMap := by
  have h1 : IsVOAHom golayV0 lam0Plus lam0PlusGolayEquiv.symm.toLinearMap :=
    IsVOAHom.symm_of_equiv lam0PlusGolayEquiv lam0PlusToGolay_isVOAHom
  exact lam0PlusEquiv_isVOAHom.comp h1

theorem golayToV0_omega : golayToV0 golayV0.conformalVector = V0P.conformalVector := by
  change lam0PlusEquiv (lam0PlusGolayEquiv.symm golayV0.conformalVector) = _
  rw [← lam0PlusToGolay_omega]
  change lam0PlusEquiv (lam0PlusGolayEquiv.symm (lam0PlusGolayEquiv lam0Plus.conformalVector)) = _
  rw [LinearEquiv.symm_apply_apply, lam0PlusEquiv_omega]

/-- **The FLM/DGM triality on `V₀⁺ = V0P`**, transported from `golaySigma0`. -/
noncomputable def v0Sigma : Aut V0P :=
  Aut.transport golayToV0 golayToV0_isVOAHom golayToV0_omega golaySigma0

/-- `golayToV0 ∘ σ₀ = v0Sigma ∘ golayToV0`. -/
theorem golayToV0_sigma (x : (orbifold golayK).carrier) :
    golayToV0 (golaySigma0 x) = v0Sigma (golayToV0 x) :=
  (Aut.transport_apply _ _ _ _ x).symm

/-- `v0Sigma² = 1`. -/
theorem v0Sigma_sq : v0Sigma * v0Sigma = 1 := by
  rw [v0Sigma, ← Aut.transport_mul, golaySigma0_sq, Aut.transport_one]

/-- `v0Sigma ≠ 1`. -/
theorem v0Sigma_ne_one : v0Sigma ≠ 1 := by
  intro h
  apply golaySigma0_ne_one
  apply Aut.transport_injective golayToV0 golayToV0_isVOAHom golayToV0_omega
  rw [Aut.transport_one]
  exact h

end Moonshine

end VOA
