/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Statement
import VOA.Moonshine.TrialitySl2
import VOA.Moonshine.LatticeMorphRigid
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite groups of automorphisms of `V_{2m}` and of `V₂`

This file makes the exceptional clauses of `InCOneList` (`Statement.lean`) non-vacuous: it
constructs explicit finite subgroups of `Aut V₂` isomorphic to `A₄` and `S₄`, and, for every
`V_{2m}`, subgroups isomorphic to `ℤ_n` and to the dihedral group `D_n` (`n ≥ 1`).

## Main results
* `charU m hm : ℂˣ →* Aut V_{2m}`, `u ↦ (p ⊗ e^{kα} ↦ u^k p ⊗ e^{kα})` (the torus), injective.
* `aut_eq_one_of_fix` (**rigidity**): an automorphism of `V_{2m}` fixing `h = α(−1)𝟙` and `e^α`
  is the identity. Proof: such a `φ` commutes with `h₍₀₎`, so preserves the charge sectors; then
  `φθ` is a lift of `−1`, hence `φθ = g_d θ` by `exists_char_of_lift`, so `φ = g_d`, and
  `φ e^α = e^α` forces `d = 0`. Consequence `aut_ext_of_agree`: automorphisms are determined by
  their values on `h` and `e^α`.
* `cycHom`, `dihHom`: injective homomorphisms `ℤ_n → Aut V_{2m}` (`k ↦ g_{ζ_n^k}`) and
  `D_n → Aut V_{2m}` (`r^k ↦ g_{ζ_n^k}`, `s r^k ↦ θ g_{ζ_n^k}`, using `θ g_u θ = g_{u⁻¹}`).
  `exists_cyclic_subgroup`, `exists_dihedral_subgroup` (and the `_V2` versions).
* The octahedral group. On `(V₂)₁ ≅ sl₂` use `X = e + εf`, `Y = i(e − εf)`, `Z = h`
  (`ε = ε(α,−α)`, `xyz a b c = aX + bY + cZ`). Two automorphisms:
  `rot4 = g_i` (`(a,b,c) ↦ (−b,a,c)`, rotation by `π/2` about `Z`; `rot4_xyz`), and
  `rot2 = exp((i−1)E) exp(εF) exp((−1−i/2)E) g_{1/2}` (`(a,b,c) ↦ (−a,c,b)`, rotation by `π`
  about `Y+Z`; `rot2_xyz`), with `E = (e^α)₍₀₎`, `F = (e^{−α})₍₀₎` (`rootExp`). With the four
  tetrahedral vectors `t_i` (`tvec`), `IsOct σ φ` says `φ t_i = sgn(σ) t_{σ i}`; `rot4`, `rot2`
  realize the 4-cycle `finRotate 4` and the swap `(0 1)`, which generate `S₄`
  (`Perm.closure_cycle_adjacent_swap`), so every `σ` is realized (`exists_isOct`), uniquely by
  rigidity (`IsOct.unique`, since `h` and `e^α` are combinations of the `t_i`). This gives the
  injective `octHom : S₄ →* Aut V₂`.
* `exists_S4_subgroup`, `exists_A4_subgroup`; `exists_hasCOneLabel_tetra`,
  `exists_hasCOneLabel_octa`: the clauses `IsV2Orbifold _ (alternatingGroup (Fin 4))` and
  `IsV2Orbifold _ (Equiv.Perm (Fin 4))` are realized by `V₂^G` for these `G`.

## The icosahedral group
`A₅ ≤ Aut V₂` is proved in `V2Icosahedral.lean` (`exists_A5_subgroup`,
`exists_hasCOneLabel_icosa`), by the same rigidity method, with a half-turn generator in
`ℚ(√5, i)` and the action on the five inscribed tetrahedra of a dodecahedron.

## Status
`sorry`-free, no new axioms. Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN

section Rank1

variable (m : ℕ) (hm : 1 ≤ m)


/-- The generator `α = 1` of `L_m = √(2m) ℤ`. -/
abbrev a1 : (latP m).carrier := (1 : ℤ)

/-- The character `k ↦ u^k` of `L_m = ℤ`. -/
noncomputable def unitChar (u : ℂˣ) : (latP m).carrier →+ Additive ℂˣ :=
  zmultiplesHom (Additive ℂˣ) (Additive.ofMul u)

/-- The identity `L_m → ℤ` (the carrier of `latP m` is `ℤ`). -/
def ci (k : (latP m).carrier) : ℤ := k

theorem charVal_unitChar (u : ℂˣ) (k : (latP m).carrier) :
    charVal (latP m) (unitChar m u) k = ((u ^ ci m k : ℂˣ) : ℂ) := by
  show ((Additive.toMul ((ci m k) • Additive.ofMul u) : ℂˣ) : ℂ) = _
  rw [toMul_zsmul, toMul_ofMul]

theorem unitChar_mul (u v : ℂˣ) : unitChar m (u * v) = unitChar m u + unitChar m v := by
  apply AddMonoidHom.ext_int
  show (1 : ℤ) • Additive.ofMul (u * v) = (1 : ℤ) • Additive.ofMul u + (1 : ℤ) • Additive.ofMul v
  simp only [one_zsmul, ofMul_mul]

theorem unitChar_one : unitChar m 1 = 0 := by
  apply AddMonoidHom.ext_int
  show (1 : ℤ) • Additive.ofMul (1 : ℂˣ) = 0
  simp

local notation "VV" => latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)

/-- **The torus `ℂˣ → Aut V_{2m}`**, `u ↦ (e^{kα} ↦ u^k e^{kα})`. -/
noncomputable def charU : ℂˣ →* Aut VV where
  toFun u := charAut (latP m) (unitChar m u) (latP_even m) (latP_posDef m hm)
  map_one' := Aut.ext (LinearEquiv.ext fun x => by
    show charLat _ (unitChar m 1) x = x
    rw [unitChar_one]; exact charLat_zero _ (latP_posDef m hm) x)
  map_mul' u v := Aut.ext (LinearEquiv.ext fun x => by
    show charLat _ (unitChar m (u * v)) x = charLat _ (unitChar m u) (charLat _ (unitChar m v) x)
    rw [charLat_comp _ _ (latP_posDef m hm), unitChar_mul])

theorem charU_latStateGen (u : ℂˣ) (p : FockN (rank (latP m))) (k : (latP m).carrier) :
    charU m hm u (latStateGen (latP m) p k) = ((u ^ ci m k : ℂˣ) : ℂ) • latStateGen (latP m) p k := by
  show charLat _ (unitChar m u) _ = _
  rw [charLat_latStateGen _ _ (latP_posDef m hm), charVal_unitChar]

theorem charU_hSt (u : ℂˣ) (β : (latP m).carrier) :
    charU m hm u (hSt (latP m) β) = hSt (latP m) β := by
  rw [hSt, charU_latStateGen]
  show ((u ^ (0 : ℤ) : ℂˣ) : ℂ) • _ = _
  simp

theorem charU_latChargeGen (u : ℂˣ) (k : (latP m).carrier) :
    charU m hm u (latChargeGen (latP m) k) = ((u ^ ci m k : ℂˣ) : ℂ) • latChargeGen (latP m) k :=
  charU_latStateGen m hm u _ k

theorem latChargeGen_ne_zero (k : (latP m).carrier) : latChargeGen (latP m) k ≠ 0 :=
  Screen.latStateGen_ne_zero _ one_ne_zero k

theorem charU_injective : Function.Injective (charU m hm) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h := charU_latChargeGen m hm u (a1 m)
  rw [hu] at h
  change latChargeGen _ _ = _ at h
  have h2 : ((u ^ ci m (a1 m) : ℂˣ) : ℂ) = 1 :=
    (smul_left_injective ℂ (latChargeGen_ne_zero m (a1 m))) (by simpa using h.symm)
  ext
  simpa [a1, ci] using h2

/-! ### The Heisenberg state and `θ` -/

theorem hSt_int (k : (latP m).carrier) :
    hSt (latP m) k = ((ci m k : ℤ) : ℂ) • hSt (latP m) (a1 m) := by
  let f : (latP m).carrier →+ LatModuleGen (latP m) :=
    AddMonoidHom.mk' (hSt (latP m)) (hSt_add (latP m))
  have hk : k = (ci m k) • a1 m := by
    show ci m k = ci m k * 1
    rw [mul_one]
  have : f k = (ci m k) • f (a1 m) := by
    conv_lhs => rw [hk]
    exact map_zsmul f _ _
  simpa [f, ← Int.cast_smul_eq_zsmul ℂ] using this

theorem thetaLat_hSt' (β : (latP m).carrier) :
    thetaLat (latP m) (hSt (latP m) β) = -hSt (latP m) β := by
  rw [hSt_eq_sum, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, thetaLat_wordStateLatGen, List.length_singleton, pow_one, neg_zero, neg_one_smul,
    smul_neg]

/-! ### Rigidity: an automorphism is determined by its values on `h = α(−1)𝟙` and `e^α` -/

theorem aut_mem_chargeSec (φ : Aut VV) (hh : φ (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m))
    {μ : (latP m).carrier} {x : LatModuleGen (latP m)} (hx : x ∈ chargeSec (latP m) μ) :
    φ x ∈ chargeSec (latP m) μ := by
  apply mem_chargeSec_of_coordEα
  intro ν hν
  have hHx : (VV).smul (hSt (latP m) (a1 m)) 0 x
      = (((latP m).form (a1 m) μ : ℤ) : ℂ) • x := by
    obtain ⟨p, rfl⟩ := hx
    exact smul_hSt_zero_latStateGen _ (latP_even m) (latP_posDef m hm) _ p μ
  have hH : (VV).smul (hSt (latP m) (a1 m)) 0 (φ x)
      = (((latP m).form (a1 m) μ : ℤ) : ℂ) • φ x := by
    rw [← hh, ← Aut.map_smul, hHx, Aut.map_smul_c]
  have h1 := coordEα_smul_hSt_zero _ (latP_even m) (latP_posDef m hm) (a1 m) ν (φ x)
  rw [hH, map_smul] at h1
  have h2 : ((((latP m).form (a1 m) μ : ℤ) : ℂ) - (((latP m).form (a1 m) ν : ℤ) : ℂ))
      • coordEα (latP m) ν (φ x) = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hν
    rw [sub_eq_zero, Int.cast_inj, latP_form, latP_form] at h3
    have hm0 : (2 * (m : ℤ) * 1) ≠ 0 := by omega
    have := mul_left_cancel₀ hm0 h3
    exact this.symm
  · exact h3

theorem exists_char_of_fix_h (φ : Aut VV)
    (hh : φ (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m)) :
    ∃ d : (latP m).carrier →+ Additive ℂˣ, ∀ x, φ x = charLat (latP m) d x := by
  set θ := thetaAut (latP m) (latP_even m) (latP_posDef m hm)
  have hhall : ∀ β, φ (hSt (latP m) β) = hSt (latP m) β := by
    intro β
    rw [hSt_int m β, Aut.map_smul_c, hh]
  have hψ : ∀ β, (φ * θ) (hSt (latP m) β) = -hSt (latP m) β := by
    intro β
    rw [Aut.mul_apply, thetaAut_apply, thetaLat_hSt', ← neg_one_smul ℂ, Aut.map_smul_c, hhall,
      neg_one_smul]
  have hheis : ∀ a, (φ * θ) (heisSt (latP m) a) = -heisSt (latP m) a := by
    intro a
    suffices h : ∀ x ∈ Submodule.span ℂ (Set.range (hSt (latP m))), (φ * θ) x = -x from
      h _ (heisSt_mem_span_hSt (latP m) (latP_posDef m hm) a)
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨β, rfl⟩ := hx
        exact hψ β
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
    | smul c x _ hx => rw [Aut.map_smul_c, hx, smul_neg]
  have hsec : ∀ (γ : (latP m).carrier) (x : LatModuleGen (latP m)),
      x ∈ chargeSec (latP m) γ → (φ * θ) x ∈ chargeSec (latP m) (-γ) := by
    intro γ x hx
    exact aut_mem_chargeSec m hm φ hh (thetaLat_mem_chargeSec _ hx)
  obtain ⟨d, hd⟩ := exists_char_of_lift (latP m) (latP_even m) (latP_posDef m hm) (φ * θ) hheis hsec
  refine ⟨d, fun x => ?_⟩
  have := hd (thetaLat (latP m) x)
  rwa [Aut.mul_apply, thetaAut_apply, thetaLat_thetaLat] at this

/-- **Rigidity.** An automorphism of `V_{2m}` fixing `α(−1)𝟙` and `e^α` is the identity. -/
theorem aut_eq_one_of_fix (φ : Aut VV)
    (hh : φ (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m))
    (he : φ (latChargeGen (latP m) (a1 m)) = latChargeGen (latP m) (a1 m)) : φ = 1 := by
  obtain ⟨d, hd⟩ := exists_char_of_fix_h m hm φ hh
  have h1 : charVal (latP m) d (a1 m) = 1 := by
    have h := hd (latChargeGen (latP m) (a1 m))
    rw [he, latChargeGen, charLat_latStateGen _ _ (latP_posDef m hm)] at h
    exact (smul_left_injective ℂ (latChargeGen_ne_zero m (a1 m))) (by simpa using h.symm)
  have hd0 : d = 0 := by
    apply AddMonoidHom.ext_int
    show d (a1 m) = 0
    simpa [charVal] using h1
  subst hd0
  exact Aut.ext (LinearEquiv.ext fun x => (hd x).trans (charLat_zero _ (latP_posDef m hm) x))

/-- Two automorphisms of `V_{2m}` agreeing on `α(−1)𝟙` and `e^α` are equal. -/
theorem aut_ext_of_agree (φ ψ : Aut VV)
    (hh : φ (hSt (latP m) (a1 m)) = ψ (hSt (latP m) (a1 m)))
    (he : φ (latChargeGen (latP m) (a1 m)) = ψ (latChargeGen (latP m) (a1 m))) : φ = ψ := by
  have := aut_eq_one_of_fix m hm (ψ⁻¹ * φ)
    (by rw [Aut.mul_apply, hh]; exact ψ.toLinearEquiv.symm_apply_apply _)
    (by rw [Aut.mul_apply, he]; exact ψ.toLinearEquiv.symm_apply_apply _)
  exact (inv_mul_eq_one.mp this).symm

/-! ### `θ` and the torus; the cyclic and dihedral subgroups -/

include hm in
theorem hSt_a1_ne_zero : hSt (latP m) (a1 m) ≠ 0 := by
  intro h
  have h1 := Qscr_hSt (latP m) (latP_posDef m hm) (a1 m) (a1 m)
  rw [h, map_zero, latP_form] at h1
  have h2 : ((-((2 * (m : ℤ) * 1 * 1 : ℤ) : ℂ))) ≠ 0 := by
    have : (2 * (m : ℤ) * 1 * 1) ≠ 0 := by omega
    exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr this)
  exact (smul_ne_zero h2 (latChargeGen_ne_zero m (a1 m))) h1.symm

/-- `θ` (the lift of `−1`) on `V_{2m}`. -/
noncomputable abbrev thetaM : Aut VV := thetaAut (latP m) (latP_even m) (latP_posDef m hm)

theorem thetaM_mul_self : thetaM m hm * thetaM m hm = 1 := thetaAut_sq _ _ _

/-- `θ g_u θ⁻¹ = g_{u⁻¹}`. -/
theorem thetaM_mul_charU (u : ℂˣ) :
    thetaM m hm * charU m hm u = charU m hm u⁻¹ * thetaM m hm := by
  apply aut_ext_of_agree m hm
  · simp only [Aut.mul_apply, thetaAut_apply, charU_hSt, thetaLat_hSt']
    rw [← neg_one_smul ℂ, Aut.map_smul_c, charU_hSt, neg_one_smul]
  · simp only [Aut.mul_apply, thetaAut_apply, charU_latChargeGen, map_smul,
      thetaLat_latChargeGen]
    congr 1

theorem thetaM_ne_charU (u : ℂˣ) : thetaM m hm * charU m hm u ≠ 1 := by
  intro h
  have h1 : (thetaM m hm * charU m hm u) (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m) := by
    rw [h]; rfl
  rw [Aut.mul_apply, charU_hSt, thetaAut_apply, thetaLat_hSt', neg_eq_iff_add_eq_zero,
    ← two_smul ℂ] at h1
  exact hSt_a1_ne_zero m hm ((smul_eq_zero.mp h1).resolve_left two_ne_zero)

variable {n : ℕ} [NeZero n]

/-- A primitive `n`-th root of unity in `ℂˣ`. -/
noncomputable def zetaU (n : ℕ) [NeZero n] : ℂˣ :=
  ((Complex.isPrimitiveRoot_exp n (NeZero.ne n)).isUnit (NeZero.ne n)).unit

theorem zetaU_isPrimitiveRoot : IsPrimitiveRoot (zetaU n) n :=
  (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).isUnit_unit (NeZero.ne n)

/-- `ZMod n ≅ μ_n ⊆ ℂˣ`, `k ↦ ζ^k`. -/
noncomputable def zmodToUnits (n : ℕ) [NeZero n] : Multiplicative (ZMod n) →* ℂˣ :=
  (Subgroup.zpowers (zetaU n)).subtype.comp
    (AddEquiv.toMultiplicativeLeft (zetaU_isPrimitiveRoot (n := n)).zmodEquivZPowers).toMonoidHom

theorem zmodToUnits_injective : Function.Injective (zmodToUnits n) :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective
    (AddEquiv.toMultiplicativeLeft (zetaU_isPrimitiveRoot (n := n)).zmodEquivZPowers))

/-- **The cyclic group `ℤ_n ↪ Aut V_{2m}`**, `k ↦ g_{ζ^k}` (`e^{jα} ↦ ζ^{jk} e^{jα}`). -/
noncomputable def cycHom (n : ℕ) [NeZero n] : Multiplicative (ZMod n) →* Aut VV :=
  (charU m hm).comp (zmodToUnits n)

theorem cycHom_injective : Function.Injective (cycHom m hm n) :=
  (charU_injective m hm).comp zmodToUnits_injective

theorem thetaM_mul_cycHom (x : Multiplicative (ZMod n)) :
    thetaM m hm * cycHom m hm n x = cycHom m hm n x⁻¹ * thetaM m hm := by
  simp only [cycHom, MonoidHom.comp_apply, thetaM_mul_charU, map_inv]

/-- **The dihedral group `D_n ↪ Aut V_{2m}`**: `r^i ↦ g_{ζ^i}`, `s r^i ↦ θ g_{ζ^i}`. -/
noncomputable def dihHom (n : ℕ) [NeZero n] : DihedralGroup n →* Aut VV where
  toFun
    | .r i => cycHom m hm n (Multiplicative.ofAdd i)
    | .sr i => thetaM m hm * cycHom m hm n (Multiplicative.ofAdd i)
  map_one' := by
    rw [DihedralGroup.one_def]
    show cycHom m hm n (Multiplicative.ofAdd 0) = 1
    rw [ofAdd_zero, map_one]
  map_mul' := by
    have hc : ∀ i : ZMod n, cycHom m hm n (Multiplicative.ofAdd i) * thetaM m hm
        = thetaM m hm * cycHom m hm n (Multiplicative.ofAdd (-i)) := by
      intro i
      rw [thetaM_mul_cycHom, ofAdd_neg, inv_inv]
    rintro (i | i) (j | j)
    · show cycHom m hm n (Multiplicative.ofAdd (i + j)) = _ * _
      rw [ofAdd_add, map_mul]
    · show thetaM m hm * cycHom m hm n (Multiplicative.ofAdd (j - i)) = _ * (_ * _)
      rw [← mul_assoc, hc, mul_assoc, ← map_mul, ← ofAdd_add, neg_add_eq_sub]
    · show thetaM m hm * cycHom m hm n (Multiplicative.ofAdd (i + j)) = (_ * _) * _
      rw [ofAdd_add, map_mul, mul_assoc]
    · show cycHom m hm n (Multiplicative.ofAdd (j - i)) = (_ * _) * (_ * _)
      rw [mul_assoc, ← mul_assoc (cycHom m hm n _), hc, ← mul_assoc, ← mul_assoc,
        thetaM_mul_self, one_mul, ← map_mul, ← ofAdd_add, neg_add_eq_sub]

theorem dihHom_injective : Function.Injective (dihHom m hm n) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · have h' : cycHom m hm n (Multiplicative.ofAdd i) = cycHom m hm n 1 := by
      rw [map_one]; exact h
    have := cycHom_injective m hm h'
    rw [← ofAdd_zero] at this
    rw [Multiplicative.ofAdd.injective this, DihedralGroup.one_def]
  · exact absurd h (thetaM_ne_charU m hm _)

/-- **`ℤ_n ≤ Aut V_{2m}`** for every `n ≥ 1`. -/
theorem exists_cyclic_subgroup (n : ℕ) [NeZero n] :
    ∃ G : Subgroup (Aut VV), Nonempty (G ≃* Multiplicative (ZMod n)) :=
  ⟨(cycHom m hm n).range, ⟨(MonoidHom.ofInjective (cycHom_injective m hm)).symm⟩⟩

/-- **`D_n ≤ Aut V_{2m}`** (the dihedral group of order `2n`) for every `n ≥ 1`. -/
theorem exists_dihedral_subgroup (n : ℕ) [NeZero n] :
    ∃ G : Subgroup (Aut VV), Nonempty (G ≃* DihedralGroup n) :=
  ⟨(dihHom m hm n).range, ⟨(MonoidHom.ofInjective (dihHom_injective m hm)).symm⟩⟩

end Rank1

/-! ## The octahedral group `S₄` and the tetrahedral group `A₄` in `Aut V₂` -/

section Octahedral

open Complex Equiv

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)
local notation "α₁" => a1 1

theorem latP1_root : (latP 1).form (a1 1) (a1 1) = 2 := by rw [latP_form]; norm_num

theorem latP1_root' : (latP 1).form (-a1 1) (-a1 1) = 2 := by
  rw [latP_form]; show 2 * ((1 : ℕ) : ℤ) * (-1) * (-1) = 2; norm_num

/-- The sign `ε = ε(α, −α)` of the root `sl₂`-triple. -/
noncomputable def eps1 : ℂ := latticeCocycle (latP 1) (a1 1) (-a1 1)

theorem cocycle_eq_eps1 : latticeCocycle (latP 1) (a1 1) (-a1 1) = eps1 := rfl

theorem eps1_sq : eps1 * eps1 = 1 := latticeCocycle_sq _ _ _

theorem eps1_cases : eps1 = 1 ∨ eps1 = -1 := mul_self_eq_one_iff.mp eps1_sq

/-- `exp(c·(e^α)₍₀₎)`. -/
noncomputable abbrev expE (c : ℂ) : Aut V1 :=
  rootExp (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) latP1_root c

/-- `exp(c·(e^{−α})₍₀₎)`. -/
noncomputable abbrev expF (c : ℂ) : Aut V1 :=
  rootExp (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) latP1_root' c

theorem charU_vec3 (u : ℂˣ) (x₁ x₂ x₃ : ℂ) :
    charU 1 le_rfl u (vec3 (latP 1) (a1 1) x₁ x₂ x₃)
      = vec3 (latP 1) (a1 1) ((u : ℂ) * x₁) x₂ ((u : ℂ)⁻¹ * x₃) := by
  simp only [vec3, map_add, Aut.map_smul_c, charU_latChargeGen, charU_hSt, smul_smul]
  have h1 : ci 1 (a1 1) = 1 := rfl
  have h2 : ci 1 (-a1 1) = -1 := rfl
  rw [h1, h2]
  simp [mul_comm]

/-- The coordinates `aX + bY + cZ`, with `X = e + εf`, `Y = i(e − εf)`, `Z = h`. -/
noncomputable def xyz (a b c : ℂ) : LatModuleGen (latP 1) :=
  vec3 (latP 1) (a1 1) (a + I * b) c (eps1 * a - I * eps1 * b)

theorem xyz_congr {a b c a' b' c' : ℂ} (ha : a = a') (hb : b = b') (hc : c = c') :
    xyz a b c = xyz a' b' c' := by rw [ha, hb, hc]

theorem xyz_smul (t a b c : ℂ) : t • xyz a b c = xyz (t * a) (t * b) (t * c) := by
  rw [xyz, xyz, vec3_smul]; apply vec3_congr <;> ring

theorem xyz_add (a b c a' b' c' : ℂ) : xyz a b c + xyz a' b' c' = xyz (a + a') (b + b') (c + c') := by
  rw [xyz, xyz, xyz, vec3_add]; apply vec3_congr <;> ring

theorem hSt_eq_xyz : hSt (latP 1) (a1 1) = xyz 0 0 1 := by
  simp [xyz, vec3]

theorem latChargeGen_eq_xyz : latChargeGen (latP 1) (a1 1) = xyz (1 / 2) (-I / 2) 0 := by
  have h : xyz (1 / 2) (-I / 2) 0 = vec3 (latP 1) (a1 1) 1 0 0 := by
    rw [xyz]; apply vec3_congr
    · ring_nf; rw [I_sq]; ring
    · rfl
    · ring_nf; rw [I_sq]; ring
  rw [h]; simp [vec3]

/-- The unit `i ∈ ℂˣ`. -/
noncomputable def unitI : ℂˣ := Units.mk0 I I_ne_zero

/-- The rotation by `π/2` about the Heisenberg axis: `g_i`. -/
noncomputable def rot4 : Aut V1 := charU 1 le_rfl unitI

theorem rot4_xyz (a b c : ℂ) : rot4 (xyz a b c) = xyz (-b) a c := by
  rw [rot4, xyz, charU_vec3, xyz]
  simp only [unitI, Units.val_mk0, inv_I]
  apply vec3_congr
  · ring_nf; rw [I_sq]; ring
  · rfl
  · ring_nf; rw [I_sq]; ring

/-- The unit `1/2 ∈ ℂˣ`. -/
noncomputable def unitHalf : ℂˣ := Units.mk0 (1 / 2) (by norm_num)

/-- The rotation by `π` about the axis `Y + Z`:
`exp((i−1)E) exp(εF) exp((−1−i/2)E) g_{1/2}`. -/
noncomputable def rot2 : Aut V1 := expE (I - 1) * expF eps1 * expE (-1 - I / 2) * charU 1 le_rfl unitHalf

theorem rot2_vec3 (x₁ x₂ x₃ : ℂ) :
    rot2 (vec3 (latP 1) (a1 1) x₁ x₂ x₃)
      = vec3 (latP 1) (a1 1) (-x₁ / 2 + I * x₂ - eps1 * x₃ / 2) (-I * x₁ / 2 + I * eps1 * x₃ / 2)
          (-eps1 * x₁ / 2 - I * eps1 * x₂ - x₃ / 2) := by
  simp only [rot2, Aut.mul_apply, charU_vec3, unitHalf, Units.val_mk0]
  rw [rootExp_vec3_pos _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root,
    rootExp_vec3_neg _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root latP1_root',
    rootExp_vec3_pos _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root]
  simp only [cocycle_eq_eps1]
  rcases eps1_cases with h | h <;> rw [h] <;> apply vec3_congr <;>
    (ring_nf; try simp only [I_sq, I_pow_four, I_pow_three]; try ring_nf)

theorem rot2_xyz (a b c : ℂ) : rot2 (xyz a b c) = xyz (-a) c b := by
  rw [xyz, rot2_vec3, xyz]
  rcases eps1_cases with h | h <;> rw [h] <;> apply vec3_congr <;>
    (ring_nf; try simp only [I_sq]; try ring_nf)


/-! ### The four tetrahedral vectors and the octahedral action -/

/-- Coordinates of the vertices `(1,1,1), (1,−1,−1), (−1,−1,1), (−1,1,−1)` of a tetrahedron. -/
def ta : Fin 4 → ℂ := ![1, 1, -1, -1]
def tb : Fin 4 → ℂ := ![1, -1, -1, 1]
def tc : Fin 4 → ℂ := ![1, -1, 1, -1]

/-- The four tetrahedral vectors in the weight-one space `(V₂)₁ ≅ sl₂`. -/
noncomputable def tvec (i : Fin 4) : LatModuleGen (latP 1) := xyz (ta i) (tb i) (tc i)

/-- The sign of a permutation, in `ℂ`. -/
def sgnC (σ : Perm (Fin 4)) : ℂ := ((Perm.sign σ : ℤˣ) : ℤ)

theorem sgnC_mul (σ τ : Perm (Fin 4)) : sgnC (σ * τ) = sgnC σ * sgnC τ := by
  simp [sgnC]

theorem sgnC_one : sgnC 1 = 1 := by simp [sgnC]

theorem sgnC_inv (σ : Perm (Fin 4)) : sgnC σ⁻¹ = sgnC σ := by simp [sgnC]

theorem sgnC_mul_self (σ : Perm (Fin 4)) : sgnC σ * sgnC σ = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [sgnC, h]

/-- `φ` realizes the signed permutation `σ` of the tetrahedral vectors:
`φ(t_i) = sgn(σ) t_{σ i}`. -/
def IsOct (σ : Perm (Fin 4)) (φ : Aut V1) : Prop := ∀ i, φ (tvec i) = sgnC σ • tvec (σ i)

theorem IsOct.mul {σ τ : Perm (Fin 4)} {φ ψ : Aut V1} (h1 : IsOct σ φ) (h2 : IsOct τ ψ) :
    IsOct (σ * τ) (φ * ψ) := by
  intro i
  rw [Aut.mul_apply, h2, Aut.map_smul_c, h1, smul_smul, sgnC_mul, mul_comm]
  rfl

theorem IsOct.one : IsOct 1 (1 : Aut V1) := by
  intro i; rw [sgnC_one, one_smul]; rfl

theorem IsOct.inv {σ : Perm (Fin 4)} {φ : Aut V1} (h : IsOct σ φ) : IsOct σ⁻¹ φ⁻¹ := by
  intro i
  have h1 := h (σ⁻¹ i)
  rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at h1
  have h2 : φ⁻¹ (φ (tvec (σ⁻¹ i))) = tvec (σ⁻¹ i) := φ.toLinearEquiv.symm_apply_apply _
  rw [h1, Aut.map_smul_c] at h2
  rw [sgnC_inv, ← h2, smul_smul, sgnC_mul_self, one_smul]

theorem hSt_eq_tvec : hSt (latP 1) (a1 1) = (1 / 2 : ℂ) • (tvec 0 + tvec 2) := by
  rw [hSt_eq_xyz, tvec, tvec, xyz_add, xyz_smul]
  apply xyz_congr <;> simp [ta, tb, tc]
  norm_num

theorem latChargeGen_eq_tvec : latChargeGen (latP 1) (a1 1)
    = (1 / 4 : ℂ) • (tvec 0 + tvec 1) + (-I / 4) • (tvec 0 + tvec 3) := by
  rw [latChargeGen_eq_xyz, tvec, tvec, tvec, xyz_add, xyz_add, xyz_smul, xyz_smul, xyz_add]
  apply xyz_congr <;> simp [ta, tb, tc] <;> ring

theorem IsOct.unique {σ : Perm (Fin 4)} {φ ψ : Aut V1} (h1 : IsOct σ φ) (h2 : IsOct σ ψ) :
    φ = ψ := by
  have h : ∀ i, φ (tvec i) = ψ (tvec i) := fun i => by rw [h1, h2]
  apply aut_ext_of_agree 1 le_rfl
  · simp only [hSt_eq_tvec, map_add, Aut.map_smul_c, h]
  · simp only [latChargeGen_eq_tvec, map_add, Aut.map_smul_c, h]

theorem isOct_rot4 : IsOct (finRotate 4) rot4 := by
  have hs : sgnC (finRotate 4) = -1 := by simp [sgnC, sign_finRotate]
  intro i
  rw [tvec, rot4_xyz, hs, tvec, xyz_smul]
  fin_cases i <;> apply xyz_congr <;> simp [ta, tb, tc, finRotate_apply]

theorem isOct_rot2 : IsOct (swap 0 (finRotate 4 0)) rot2 := by
  have h01 : finRotate 4 0 = 1 := rfl
  have hs : sgnC (swap (0 : Fin 4) 1) = -1 := by simp [sgnC]
  rw [h01]
  intro i
  rw [tvec, rot2_xyz, hs, tvec, xyz_smul]
  fin_cases i <;> apply xyz_congr <;> simp [ta, tb, tc, swap_apply_def]

/-- Every permutation of the four tetrahedral vectors is realized (with sign) by an automorphism. -/
theorem exists_isOct (σ : Perm (Fin 4)) : ∃ φ : Aut V1, IsOct σ φ := by
  let H : Subgroup (Perm (Fin 4)) :=
    { carrier := {σ | ∃ φ : Aut V1, IsOct σ φ}
      mul_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ * ψ, hφ.mul hψ⟩
      one_mem' := ⟨1, IsOct.one⟩
      inv_mem' := fun ⟨φ, hφ⟩ => ⟨φ⁻¹, hφ.inv⟩ }
  have hcl : Subgroup.closure {finRotate 4, swap 0 (finRotate 4 0)} ≤ H := by
    rw [Subgroup.closure_le]
    intro τ hτ
    rcases hτ with rfl | rfl
    · exact ⟨rot4, isOct_rot4⟩
    · exact ⟨rot2, isOct_rot2⟩
  rw [Perm.closure_cycle_adjacent_swap isCycle_finRotate support_finRotate] at hcl
  exact hcl (Subgroup.mem_top σ)

/-- The automorphism realizing `σ`. -/
noncomputable def octFun (σ : Perm (Fin 4)) : Aut V1 := (exists_isOct σ).choose

theorem octFun_spec (σ : Perm (Fin 4)) : IsOct σ (octFun σ) := (exists_isOct σ).choose_spec

/-- **`S₄ → Aut V₂`**, the octahedral rotation group acting on `(V₂)₁ ≅ sl₂`. -/
noncomputable def octHom : Perm (Fin 4) →* Aut V1 where
  toFun := octFun
  map_one' := (octFun_spec 1).unique IsOct.one
  map_mul' σ τ := (octFun_spec (σ * τ)).unique ((octFun_spec σ).mul (octFun_spec τ))

theorem vec3_coord_one {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ}
    (h : vec3 (latP 1) (a1 1) x₁ x₂ x₃ = vec3 (latP 1) (a1 1) y₁ y₂ y₃) : x₁ = y₁ := by
  have hc := congrArg (coordEα (latP 1) (a1 1)) h
  have key : ∀ z₁ z₂ z₃ : ℂ, coordEα (latP 1) (a1 1) (vec3 (latP 1) (a1 1) z₁ z₂ z₃)
      = z₁ • vacuumN (rank (latP 1)) := by
    intro z₁ z₂ z₃
    have hne0 : (a1 1 : (latP 1).carrier) ≠ 0 := by show (1 : ℤ) ≠ 0; norm_num
    have hne1 : (a1 1 : (latP 1).carrier) ≠ -a1 1 := by show (1 : ℤ) ≠ -1; norm_num
    simp only [vec3, map_add, map_smul, latChargeGen, hSt, latStateGen, coordEα_apply]
    rw [if_pos trivial, if_neg hne0, if_neg hne1]
    simp
  rw [key, key] at hc
  exact smul_left_injective ℂ (one_ne_zero (α := FockN (rank (latP 1)))) hc

theorem vec3_coord_two {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ}
    (h : vec3 (latP 1) (a1 1) x₁ x₂ x₃ = vec3 (latP 1) (a1 1) y₁ y₂ y₃) : x₂ = y₂ := by
  have hq := congrArg (Screen.Qscr (latP 1) (a1 1)) h
  rw [Qscr_vec3_pos _ (latP_posDef 1 le_rfl) latP1_root,
    Qscr_vec3_pos _ (latP_posDef 1 le_rfl) latP1_root] at hq
  have := vec3_coord_one hq
  linear_combination (-1 / 2 : ℂ) * this

theorem tvec_inj {i j : Fin 4} {s : ℂ} (hs : s = 1 ∨ s = -1) (h : tvec i = s • tvec j) :
    i = j := by
  rw [tvec, tvec, xyz_smul, xyz, xyz] at h
  have h1 := vec3_coord_one h
  have h2 := vec3_coord_two h
  rcases hs with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [ta, tb, tc, Complex.ext_iff] at h1 h2 ⊢ <;>
    (try norm_num at h1) <;> (try norm_num at h2)

theorem octHom_injective : Function.Injective octHom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h := octFun_spec σ
  change IsOct σ (octHom σ) at h
  rw [hσ] at h
  have hs : sgnC σ = 1 ∨ sgnC σ = -1 := by
    rcases Int.units_eq_one_or (Perm.sign σ) with h' | h' <;> simp [sgnC, h']
  ext i
  exact congrArg Fin.val (tvec_inj hs (h i)).symm

end Octahedral

/-! ## The exceptional subgroups of `Aut V₂` -/

/-- **`S₄ ≤ Aut V₂`** (the octahedral group). -/
theorem exists_S4_subgroup :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* Equiv.Perm (Fin 4)) :=
  ⟨octHom.range, ⟨(MonoidHom.ofInjective octHom_injective).symm⟩⟩

/-- **`A₄ ≤ Aut V₂`** (the tetrahedral group). -/
theorem exists_A4_subgroup :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 4)) :=
  ⟨(alternatingGroup (Fin 4)).map octHom,
    ⟨((alternatingGroup (Fin 4)).equivMapOfInjective octHom octHom_injective).symm⟩⟩

/-- `ℤ_n ≤ Aut V₂` for every `n ≥ 1`. -/
theorem exists_cyclic_subgroup_V2 (n : ℕ) [NeZero n] :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* Multiplicative (ZMod n)) :=
  exists_cyclic_subgroup 1 le_rfl n

/-- `D_n ≤ Aut V₂` for every `n ≥ 1`. -/
theorem exists_dihedral_subgroup_V2 (n : ℕ) [NeZero n] :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* DihedralGroup n) :=
  exists_dihedral_subgroup 1 le_rfl n

/-! ## The exceptional clauses of `InCOneList` are inhabited -/

theorem voaIsomorphic_refl' {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) :
    VOAIsomorphic V V :=
  ⟨LinearEquiv.refl ℂ 𝒱, IsVOAHom.id V, rfl⟩

/-- Some fixed-point algebra `V₂^G` carries the label `tetra` (`G ≅ A₄`). -/
theorem exists_hasCOneLabel_tetra :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), HasCOneLabel (orbifoldVOA G) .tetra := by
  obtain ⟨G, ⟨e⟩⟩ := exists_A4_subgroup
  exact ⟨G, G, ⟨e⟩, voaIsomorphic_refl' _⟩

/-- Some fixed-point algebra `V₂^G` carries the label `octa` (`G ≅ S₄`). -/
theorem exists_hasCOneLabel_octa :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), HasCOneLabel (orbifoldVOA G) .octa := by
  obtain ⟨G, ⟨e⟩⟩ := exists_S4_subgroup
  exact ⟨G, G, ⟨e⟩, voaIsomorphic_refl' _⟩

end VOA.Classification.COne
