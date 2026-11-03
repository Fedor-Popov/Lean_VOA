/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeMorphRigid
import VOA.Moonshine.FrameSectors

/-!
# The sublattice bridge `V_{Λ₀} ↪ V_Λ`, `V_{Λ₀} ↪ V_{N(A₁²⁴)}` and `V_{Λ₀}⁺ ≅ V₀⁺`  (M8g-0, part 1)

`Λ₀ = A` (`Leech.subALattice`, the index-`2` sublattice of both the Leech lattice and the Niemeier
lattice `N(A₁²⁴)`) is transported to a `VOA.IntegralLattice` (`lam0`), and the two isometric
inclusions `Leech.inclL : A → Λ` (`a ↦ 2a`, image `Λ₀ = ker β`) and `Leech.inclG : A ⊆ N`
(image `ker parity`) give, by the general functoriality of `LatticeMorph.lean`, injective VOA
homomorphisms

  `bridgeΛ : V_{Λ₀} → V_Λ`,   `bridgeN : V_{Λ₀} → V_N`,

with images exactly the states whose momenta lie in `Λ₀` (`mem_range_bridgeΛ_iff`), resp. the
`χ`-fixed states (`mem_range_bridgeN_iff`).  `bridgeΛ` commutes with the standard involutions
(`bridgeΛ_thetaLat`), so it identifies the `θ`-orbifold of `V_{Λ₀}` with the subVOA
`V₀⁺ = V0P` of `V_Λ`:

  `lam0PlusEquiv : V_{Λ₀}⁺ ≃ₗ V0P`, a VOA isomorphism (`lam0PlusEquiv_isVOAHom`,
  `lam0PlusEquiv_omega`).

The Niemeier side (the identification of `golayV0` and the transport of the triality) is in
`FrameBridgeGolay.lean`.

## Status
All declarations `sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open VOA VOA.IntegralLattice VOA.LatGen Module
open VOA.Moonshine.Triality

/-! ## §1  The lattice `Λ₀ = A` and its two isometric embeddings -/

/-- `Λ₀ ≅ A` as a `VOA.IntegralLattice`. -/
noncomputable abbrev lam0 : VOA.IntegralLattice.{0} := ofEbeling Leech.subALattice

/-- `A ⊆ N(A₁²⁴)`. -/
noncomputable def inclN : lam0.carrier →ₗ[ℤ] golayN.carrier := Leech.inclG

/-- `A → Λ`, `a ↦ 2a` (image `Λ₀`). -/
noncomputable def inclΛ : lam0.carrier →ₗ[ℤ] leech.carrier := Leech.inclL

theorem inclN_form (a b : lam0.carrier) : golayN.form (inclN a) (inclN b) = lam0.form a b :=
  Leech.inclG_bilin a b

theorem inclΛ_form (a b : lam0.carrier) : leech.form (inclΛ a) (inclΛ b) = lam0.form a b :=
  Leech.inclL_bilin a b

theorem lam0_rank : rank lam0 = 24 := Leech.subALattice_rank

theorem lam0_posDef : lam0.PosDef := by
  intro v hv
  rw [← inclN_form]
  exact golayN_posDef _ fun h => hv (Leech.inclG_injective (h.trans (map_zero _).symm))

theorem lam0_even : lam0.Even := fun v => by rw [← inclN_form]; exact golayN_even _

theorem rank_lam0_leech : rank lam0 = rank leech := by rw [lam0_rank, leech_rank]

theorem rank_lam0_golayN : rank lam0 = rank golayN := by rw [lam0_rank, golayN_rank]

theorem mem_range_inclN (γ : golayN.carrier) : γ ∈ Set.range inclN ↔ golayParity γ = 0 :=
  (SetLike.ext_iff.mp Leech.range_inclG γ).trans Iff.rfl

theorem mem_range_inclΛ (γ : leech.carrier) : γ ∈ Set.range inclΛ ↔ γ ∈ lambda0 := by
  rw [lambda0_eq_range_inclL]; rfl

/-- The lattice VOA `V_{Λ₀}`. -/
noncomputable def lam0VOA : VertexOperatorAlgebra (LatModuleGen lam0) :=
  latticeVOAGen lam0 lam0_even lam0_posDef

/-! ## §2  The two bridges -/

/-- `bridgeΛ : V_{Λ₀} → V_Λ`. -/
noncomputable def bridgeΛ : LatModuleGen lam0 →ₗ[ℂ] LatModuleGen leech := latMorph lam0 leech inclΛ

/-- `bridgeN : V_{Λ₀} → V_N`. -/
noncomputable def bridgeN : LatModuleGen lam0 →ₗ[ℂ] LatModuleGen golayN := latMorph lam0 golayN inclN

theorem bridgeΛ_isVOAHom : IsVOAHom lam0VOA leechVOA bridgeΛ :=
  latMorph_isVOAHom lam0 leech inclΛ lam0_posDef leech_posDef inclΛ_form lam0_even leech_even

theorem bridgeN_isVOAHom : IsVOAHom lam0VOA golayVOA bridgeN :=
  latMorph_isVOAHom lam0 golayN inclN lam0_posDef golayN_posDef inclN_form lam0_even golayN_even

theorem bridgeΛ_omega : bridgeΛ lam0VOA.conformalVector = leechVOA.conformalVector :=
  latMorph_omega lam0 leech inclΛ lam0_posDef leech_posDef inclΛ_form rank_lam0_leech

theorem bridgeN_omega : bridgeN lam0VOA.conformalVector = golayVOA.conformalVector :=
  latMorph_omega lam0 golayN inclN lam0_posDef golayN_posDef inclN_form rank_lam0_golayN

theorem bridgeΛ_injective : Function.Injective bridgeΛ :=
  latMorph_injective lam0 leech inclΛ lam0_posDef leech_posDef inclΛ_form rank_lam0_leech

theorem bridgeN_injective : Function.Injective bridgeN :=
  latMorph_injective lam0 golayN inclN lam0_posDef golayN_posDef inclN_form rank_lam0_golayN

/-- The image of `bridgeΛ` is the space of states with all momenta in `Λ₀`. -/
theorem mem_range_bridgeΛ_iff (x : LatModuleGen leech) :
    x ∈ LinearMap.range bridgeΛ ↔ ∀ γ, γ ∉ lambda0 → coordEα leech γ x = 0 := by
  rw [bridgeΛ, mem_range_latMorph_iff lam0 leech inclΛ lam0_posDef leech_posDef inclΛ_form
    rank_lam0_leech]
  simp only [mem_range_inclΛ]

/-- The image of `bridgeN` is the `χ`-fixed subspace `V_N^χ`. -/
theorem mem_range_bridgeN_iff (x : LatModuleGen golayN) :
    x ∈ LinearMap.range bridgeN ↔ golayChi x = x := by
  rw [bridgeN, mem_range_latMorph_iff lam0 golayN inclN lam0_posDef golayN_posDef inclN_form
    rank_lam0_golayN]
  change _ ↔ chiLat golayN golayParity x = x
  rw [chiLat_eq_self_iff]
  simp only [mem_range_inclN]

theorem bridgeΛ_thetaLat (x : LatModuleGen lam0) :
    bridgeΛ (thetaLat lam0 x) = thetaLat leech (bridgeΛ x) :=
  latMorph_thetaLat lam0 leech inclΛ x

theorem bridgeN_thetaLat (x : LatModuleGen lam0) :
    bridgeN (thetaLat lam0 x) = thetaLat golayN (bridgeN x) :=
  latMorph_thetaLat lam0 golayN inclN x

/-- The Golay-frame automorphism `g` acts trivially on the image of `bridgeΛ`. -/
theorem frameAut_bridgeΛ (x : LatModuleGen lam0) : frameAut (bridgeΛ x) = bridgeΛ x := by
  rw [frameAut_apply, chiLat_eq_self_iff]
  intro α hα
  exact (mem_range_bridgeΛ_iff _).mp ⟨x, rfl⟩ α (by rwa [mem_lambda0])

/-! ## §3  `V_{Λ₀}⁺ ≅ V₀⁺` -/

/-- The standard involution `θ` of `V_{Λ₀}`. -/
noncomputable def lam0Theta : Aut lam0VOA := thetaAut lam0 lam0_even lam0_posDef

/-- `V_{Λ₀}⁺`, the `θ`-orbifold of `V_{Λ₀}`. -/
noncomputable def lam0Plus : VertexOperatorAlgebra (orbifold (Subgroup.zpowers lam0Theta)).carrier :=
  orbifoldVOA (Subgroup.zpowers lam0Theta)

/-- The carrier of `V_{Λ₀}⁺`. -/
abbrev Lam0PlusCarrier : Type := ↥(orbifold (Subgroup.zpowers lam0Theta)).carrier

theorem mem_lam0Plus_iff (v : LatModuleGen lam0) :
    v ∈ (orbifold (Subgroup.zpowers lam0Theta)).carrier ↔ thetaLat lam0 v = v :=
  mem_orbifold_zpowers_iff lam0Theta v

/-- `bridgeΛ` into `V_Λ⁺`. -/
noncomputable def lam0PlusToVPlus : Lam0PlusCarrier →ₗ[ℂ] VPlus :=
  (bridgeΛ ∘ₗ (orbifold (Subgroup.zpowers lam0Theta)).carrier.subtype).codRestrict _ fun x => by
    rw [LinearMap.comp_apply, Submodule.subtype_apply, mem_leechVOAPlus_iff, ← bridgeΛ_thetaLat,
      (mem_lam0Plus_iff _).mp x.2]

/-- **The map `V_{Λ₀}⁺ → V₀⁺`** induced by `bridgeΛ`. -/
noncomputable def lam0PlusToV0 : Lam0PlusCarrier →ₗ[ℂ] V0Sub.carrier :=
  lam0PlusToVPlus.codRestrict _ fun x => by
    rw [V0Sub_carrier, mem_frameSector_zero_iff]
    exact (mem_range_bridgeΛ_iff _).mp ⟨x, rfl⟩

@[simp] theorem lam0PlusToV0_coe (x : Lam0PlusCarrier) :
    (((lam0PlusToV0 x : V0Sub.carrier) : VPlus) : LatModuleGen leech) = bridgeΛ x := rfl

theorem lam0PlusToV0_injective : Function.Injective lam0PlusToV0 := by
  intro x y h
  apply Subtype.ext
  apply bridgeΛ_injective
  have := congrArg (fun z : V0Sub.carrier => ((z : VPlus) : LatModuleGen leech)) h
  simpa using this

theorem lam0PlusToV0_surjective : Function.Surjective lam0PlusToV0 := by
  intro y
  have hy : ((y : VPlus) : LatModuleGen leech) ∈ LinearMap.range bridgeΛ := by
    rw [mem_range_bridgeΛ_iff]
    have h1 : (y : VPlus) ∈ frameSector 0 := by rw [← V0Sub_carrier]; exact y.2
    exact (mem_frameSector_zero_iff _).mp h1
  obtain ⟨x, hx⟩ := hy
  have hθ : thetaLat lam0 x = x := by
    apply bridgeΛ_injective
    rw [bridgeΛ_thetaLat, hx]
    exact (mem_leechVOAPlus_iff _).mp (y : VPlus).2
  refine ⟨⟨x, (mem_lam0Plus_iff x).mpr hθ⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  exact hx

/-- **`V_{Λ₀}⁺ ≃ V₀⁺`** as vector spaces (a VOA isomorphism by `lam0PlusEquiv_isVOAHom`). -/
noncomputable def lam0PlusEquiv : Lam0PlusCarrier ≃ₗ[ℂ] V0Sub.carrier :=
  LinearEquiv.ofBijective lam0PlusToV0 ⟨lam0PlusToV0_injective, lam0PlusToV0_surjective⟩

@[simp] theorem lam0PlusEquiv_coe (x : Lam0PlusCarrier) :
    (((lam0PlusEquiv x : V0Sub.carrier) : VPlus) : LatModuleGen leech) = bridgeΛ x := rfl

/-- `lam0PlusEquiv` is a homomorphism of VOAs `V_{Λ₀}⁺ → V₀⁺`. -/
theorem lam0PlusEquiv_isVOAHom : IsVOAHom lam0Plus V0P lam0PlusEquiv.toLinearMap where
  map_vacuum := by
    apply Subtype.ext; apply Subtype.ext
    exact bridgeΛ_isVOAHom.map_vacuum
  map_smul u n v := by
    apply Subtype.ext; apply Subtype.ext
    exact bridgeΛ_isVOAHom.map_smul (u : LatModuleGen lam0) n v

theorem lam0PlusEquiv_omega : lam0PlusEquiv lam0Plus.conformalVector = V0P.conformalVector := by
  apply Subtype.ext; apply Subtype.ext
  exact bridgeΛ_omega

end VOA.Moonshine
