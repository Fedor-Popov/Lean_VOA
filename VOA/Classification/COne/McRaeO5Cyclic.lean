/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.AutV2Bridge
import VOA.Classification.COne.OrbifoldIdentification
import VOA.Classification.COne.LatticeRational2
import VOA.Classification.COne.OrbRat2Reduction

/-! # O5, part (c): cyclic orbifolds of `V₂` are rational

For every finite-order `g ∈ Aut V₂`, the cyclic orbifold `V₂^{⟨g⟩}` is admissibly rational
(`V2m_cyclic_admissiblyRational`).

Route: `g` is conjugate to a torus element `g_u` (`exists_conj_charU`), with `u` a primitive
`n`-th root of unity for `n = ord g`. Conjugation identifies the orbifolds
(`orbifold_zpowers_conj_iso`). The cyclic group `⟨g_u⟩` is the group `ℤ_n` of
`orbifold_cyclic_iso` (`zpowers_charU_eq_range`), so `V₂^{⟨g⟩} ≅ V₂^{ℤ_n} ≅ V_{2n²}`, which is
admissibly rational (`V2m_admissiblyRational`).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN

section Conj
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- Conjugation by an automorphism identifies the cyclic orbifolds. -/
theorem orbifold_zpowers_conj_iso (φ g : Aut W) :
    VOAIsomorphic (orbifoldVOA (Subgroup.zpowers g))
      (orbifoldVOA (Subgroup.zpowers (φ * g * φ⁻¹))) := by
  have hinv : ∀ y : 𝒱, φ (φ⁻¹ y) = y := fun y => φ.toLinearEquiv.apply_symm_apply y
  have hinv' : ∀ y : 𝒱, φ⁻¹ (φ y) = y := fun y => φ.toLinearEquiv.symm_apply_apply y
  have hcar : (orbifold (Subgroup.zpowers (φ * g * φ⁻¹))).carrier =
      (orbifold (Subgroup.zpowers g)).carrier.map φ.toLinearEquiv.toLinearMap := by
    ext y
    rw [mem_orbifold_zpowers_iff]
    constructor
    · intro hy
      refine ⟨φ⁻¹ y, (mem_orbifold_zpowers_iff g _).mpr ?_, hinv y⟩
      have h1 : φ (g (φ⁻¹ y)) = y := by simpa only [Aut.mul_apply] using hy
      have := congrArg (fun z => φ⁻¹ z) h1
      simpa only [hinv'] using this
    · rintro ⟨x, hx, rfl⟩
      have hx' : g x = x := (mem_orbifold_zpowers_iff g x).mp hx
      change (φ * g * φ⁻¹) (φ x) = φ x
      simp only [Aut.mul_apply, hinv', hx']
  let f : (orbifold (Subgroup.zpowers g)).carrier ≃ₗ[ℂ]
      (orbifold (Subgroup.zpowers (φ * g * φ⁻¹))).carrier :=
    (φ.toLinearEquiv.submoduleMap (orbifold (Subgroup.zpowers g)).carrier).trans
      (LinearEquiv.ofEq _ _ hcar.symm)
  have hf : ∀ x, ((f x : (orbifold (Subgroup.zpowers (φ * g * φ⁻¹))).carrier) : 𝒱) = φ x :=
    fun x => rfl
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact φ.map_vacuum
  · intro u n x
    apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact φ.map_smul' u n x
  · apply Subtype.ext
    rw [hf]
    exact φ.map_omega

end Conj

section V2

/-- `⟨g_u⟩ = ℤ_n` for a primitive `n`-th root of unity `u`. -/
theorem zpowers_charU_eq_range {n : ℕ} [NeZero n] {u : ℂˣ} (hu : IsPrimitiveRoot u n) :
    Subgroup.zpowers (charU 1 le_rfl u) = (cycHom 1 le_rfl n).range := by
  have hz : Subgroup.zpowers u = Subgroup.zpowers (zetaU n) := by
    rw [hu.zpowers_eq, (zetaU_isPrimitiveRoot (n := n)).zpowers_eq]
  have hr : (zmodToUnits n).range = Subgroup.zpowers (zetaU n) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact Subtype.mem _
    · intro hx
      refine ⟨(AddEquiv.toMultiplicativeLeft
        (zetaU_isPrimitiveRoot (n := n)).zmodEquivZPowers).symm ⟨x, hx⟩, ?_⟩
      simp [zmodToUnits]
  rw [← MonoidHom.map_zpowers, hz, ← hr, cycHom, MonoidHom.range_comp]

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

theorem conj_pow_aut (φ g : Aut V1) (j : ℕ) :
    (φ * g * φ⁻¹) ^ j = φ * g ^ j * φ⁻¹ := by
  have := map_pow (MulAut.conj φ) g j
  simp only [MulAut.conj_apply] at this
  exact this.symm

/-- The cyclic orbifold of a finite-order automorphism of `V₂` (lattice form). -/
theorem V1_cyclic_admissiblyRational (g : Aut V1) (hg : IsOfFinOrder g) :
    AdmissiblyRational (orbifoldVOA (Subgroup.zpowers g)) := by
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU g hg
  have hn : 0 < orderOf g := hg.orderOf_pos
  haveI : NeZero (orderOf g) := ⟨hn.ne'⟩
  have key : ∀ j : ℕ, g ^ j = 1 ↔ u ^ j = 1 := by
    intro j
    rw [← (charU_injective 1 le_rfl).eq_iff, map_pow, ← hφ, conj_pow_aut, map_one]
    constructor
    · intro h; rw [h]; group
    · intro h
      have := congrArg (fun y => φ⁻¹ * y * φ) h
      simpa [mul_assoc] using this
  have hu : IsPrimitiveRoot u (orderOf g) :=
    ⟨(key _).mp (pow_orderOf_eq_one g), fun l hl => orderOf_dvd_of_pow_eq_one ((key l).mpr hl)⟩
  have h1 : VOAIsomorphic (orbifoldVOA (Subgroup.zpowers g))
      (orbifoldVOA (Subgroup.zpowers (φ * g * φ⁻¹))) := orbifold_zpowers_conj_iso φ g
  rw [hφ, zpowers_charU_eq_range hu] at h1
  have h2 : VOAIsomorphic (orbifoldVOA (cycHom 1 le_rfl (orderOf g)).range)
      (V2m (1 * orderOf g ^ 2) (one_le_mn2 1 le_rfl (orderOf g))) :=
    orbifold_cyclic_iso 1 le_rfl (orderOf g)
  have h4 := OrbRat2.admissiblyRational_iff_of_iso h1
  have h5 := OrbRat2.admissiblyRational_iff_of_iso (𝒲 := LatModuleGen (latP (1 * orderOf g ^ 2))) h2
  have h6 : AdmissiblyRational (V2m (1 * orderOf g ^ 2) (one_le_mn2 1 le_rfl (orderOf g))) :=
    VOA.Classification.COne.V2m_admissiblyRational _
  rw [h4, h5]
  exact h6

/-- **O5 (c).** For every finite-order `g ∈ Aut V₂`, the cyclic orbifold `V₂^{⟨g⟩}` is
admissibly rational. -/
theorem V2m_cyclic_admissiblyRational (g : Aut (V2m 1 le_rfl)) (hg : IsOfFinOrder g) :
    AdmissiblyRational (orbifoldVOA (Subgroup.zpowers g)) :=
  V1_cyclic_admissiblyRational g hg

end V2

end VOA.Classification.COne.McRaeO5
