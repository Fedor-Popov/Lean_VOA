/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FZGenFiltration
import VOA.Moonshine.FZGenExcited
import VOA.Moonshine.SigmaExistZhu

/-!
# `V₃⁺` as a `V₀⁺`-module: word states and the excited sector

`M = V₃⁺ = frameSector 1` is the ordinary `V₀⁺`-module `MV3` (`SigmaExistZhu.lean`).  Its modes
are those of `V_Λ⁺` (`MV3_act_coe`), and `M_n` (as a subspace of `V_Λ⁺`) is spanned by the
projected word states `P(word(l) ⊗ e^ν)` with `ν ∈ Λ ∖ Λ₀` (`V3_le_span_words`).

The excited sector (`l ≠ []`) is spanned by weight-raising products of lower-weight states:
`excV3_mem_span`, from the generic charged argument `FZGen.gradingWN_le_of_quadClosed`
(`FZGenExcited.lean`) applied to the target `TsubV3 ν n`, whose `QuadClosed` property
(`quadClosed_V3`) is the module form of `FockSpan.quadF_mem_Tsub`: the quadratic Heisenberg
states `h_a(-i-1)h_b(-j-1)𝟙 ∈ V₀⁺` act on charge-`ν` states by `quadF` (`plus_smul_quad`, any
charge).

## Main results
* `MV3_act_coe`, `mem_MV3_weight_int`, `Lv`, `span_Lv_eq`.
* `excV3`, `excV3_mem`, `plus_smul_quad`, `TsubV3`, `quadClosed_V3`, `excV3_mem_span`.
* `Phi1`, `V3_le_span_words`.

## Status
`sorry`-free; no project axiom.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FZGen

open VOA VOA.Moonshine VOA.Moonshine.SigmaExist VOA.Moonshine.ZhuGen VOA.Moonshine.FockSpan LatGen
  IntegralLattice HeisenbergN MvPolynomial
open Submodule

/-! ## §1  The module `MV3` -/

theorem MV3_act_coe (a : V0Sub.carrier) (j : ℤ) (x : frameSector 1) :
    ((MV3.act a j x : frameSector 1) : VPlus) = leechVOAPlus.smul (a : VPlus) j (x : VPlus) := rfl

theorem mem_MV3_weight_int {k : ℤ} {x : frameSector 1} :
    x ∈ MV3.weight (k : ℂ) ↔ (x : VPlus) ∈ leechVOAPlus.grading k := by
  rw [mem_MV3_weight, adjWeight_cast]

/-- The weight-raising products of lower-weight states of `MV3`, inside `V_Λ⁺`. -/
def Lv (n : ℤ) : Set VPlus := (frameSector 1).subtype '' lowerProdM MV3 n

theorem span_Lv_eq (n : ℤ) :
    span ℂ (Lv n) = (span ℂ (lowerProdM MV3 n)).map (frameSector 1).subtype :=
  Submodule.span_image _

theorem mem_of_mem_span_Lv {x : frameSector 1} {n : ℤ} (h : (x : VPlus) ∈ span ℂ (Lv n)) :
    x ∈ span ℂ (lowerProdM MV3 n) := by
  rw [span_Lv_eq] at h
  obtain ⟨y, hy, hyx⟩ := h
  have : y = x := Subtype.ext hyx
  rwa [← this]

/-- `a₍ⱼ₎x ∈ Lv n` from the weight data, for `a ∈ V₀⁺`, `x ∈ V₃⁺` (elements of `V_Λ⁺`). -/
theorem smul_mem_Lv {p q j n : ℤ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading p)
    {x : VPlus} (hx1 : x ∈ frameSector 1) (hxq : x ∈ leechVOAPlus.grading q) (hq : q < n)
    (hj : j ≤ 0) (hw : p + q - j - 1 = n) : leechVOAPlus.smul (a : VPlus) j x ∈ Lv n :=
  ⟨MV3.act a j ⟨x, hx1⟩, ⟨p, q, j, hq, hj, hw, a, ha, ⟨x, hx1⟩, mem_MV3_weight_int.mpr hxq, rfl⟩,
    rfl⟩

/-! ## §2  Excited states of `V₃⁺` -/

/-- `p ↦ P(p ⊗ e^ν)` as a linear map `Fk → V_Λ⁺`. -/
noncomputable def excV3 (ν : leech.carrier) : Fk →ₗ[ℂ] VPlus where
  toFun p := plusProj (latStateGen leech p ν)
  map_add' p q := by rw [latStateGen_add_boson, map_add]
  map_smul' c p := by rw [latStateGen_smul, map_smul]; rfl

theorem excV3_apply (ν : leech.carrier) (p : Fk) :
    excV3 ν p = plusProj (latStateGen leech p ν) := rfl

theorem excV3_mem {ν : leech.carrier} (hν : ν ∉ lambda0) (p : Fk) : excV3 ν p ∈ frameSector 1 := by
  rw [excV3_apply, mem_frameSector, Moonshine.Extraspecial.sgn_one, plusProj_coe, map_smul,
    map_add, chiLat_thetaLat, chiLat_latStateGen, chiSign_frameChar_of_not_mem hν, neg_one_smul,
    map_neg]
  module

theorem excV3_mem_grading (ν : leech.carrier) {w : ℕ} {p : Fk} (hp : p ∈ gradingWN (rank leech) w) :
    excV3 ν p ∈ leechVOAPlus.grading ((w : ℤ) + LatGen.halfNorm leech ν) :=
  plusProj_mem_grading (latStateGen_mem_grading hp ν)

/-- **Quadratic states on any charge**:
`P(h_a(-i-1)h_b(-j-1)𝟙)₍ₙ₎ P(p ⊗ e^γ) = P(quadF(-n-1)(p) ⊗ e^γ)` in `V_Λ⁺`, for every `γ ∈ Λ`. -/
theorem plus_smul_quad (i j : ℕ) (a b : Fin (rank leech)) (γ : leech.carrier) (n : ℤ) (p : Fk) :
    leechVOAPlus.smul ((excitedV0 lambda0.zero_mem (X (i, a) * X (j, b) : Fk) : V0Sub.carrier) : VPlus)
      n (excV3 γ p) = excV3 γ (quadF γ a i b j (-n - 1) p) := by
  apply Subtype.ext
  rw [plus_smul_coe, excitedV0_quad_coe, excV3_apply, excV3_apply, plusProj_coe, plusProj_coe,
    ← smul_quad, PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_add_right]
  congr 2
  have h := thetaLat_mode leech leech_even leech_posDef
    (latStateGen leech (X (i, a) * X (j, b) : Fk) 0) n (latStateGen leech p γ)
  rw [thetaLat_quad] at h
  exact h.symm

/-- The Fock states `p` whose `P(p ⊗ e^ν)` is a combination of weight-raising products of
lower-weight states of `MV3` (target weight `n`). -/
noncomputable def TsubV3 (ν : leech.carrier) (n : ℤ) : Submodule ℂ Fk :=
  (span ℂ (Lv n)).comap (excV3 ν)

/-- The module analogue of `quadF_mem_Tsub`. -/
theorem quadClosed_V3 {ν : leech.carrier} (hν : ν ∉ lambda0) : QuadClosed ν (TsubV3 ν) := by
  intro i j a b n m hm w p hp h1 h2 h3
  rw [TsubV3, mem_comap, ← plus_smul_quad]
  refine subset_span (smul_mem_Lv (p := (i : ℤ) + j + 2) ?_ (excV3_mem hν p)
    (excV3_mem_grading ν hp) h2 hm h3)
  have := excitedV0_mem_grading lambda0.zero_mem (X_mul_X_mem_gradingWN i j a b)
  rwa [SigmaExist.halfNorm_zero, add_zero,
    show ((i + j + 2 : ℕ) : ℤ) = (i : ℤ) + j + 2 by push_cast; ring] at this

theorem ne_zero_of_not_mem {ν : leech.carrier} (hν : ν ∉ lambda0) : ν ≠ 0 := by
  rintro rfl; exact hν lambda0.zero_mem

/-- **The excited sector of `V₃⁺`**: for `ν ∈ Λ ∖ Λ₀` and `p` of Fock weight `w ≥ 1`,
`P(p ⊗ e^ν)` is a combination of weight-raising products of lower-weight states of `MV3`. -/
theorem excV3_mem_span {ν : leech.carrier} (hν : ν ∉ lambda0) {w : ℕ} (hw : 1 ≤ w) {p : Fk}
    (hp : p ∈ gradingWN (rank leech) w) :
    excV3 ν p ∈ span ℂ (Lv ((w : ℤ) + LatGen.halfNorm leech ν)) :=
  gradingWN_le_of_quadClosed (quadClosed_V3 hν) (ne_zero_of_not_mem hν) hw hp

/-! ## §3  Word states of `V₃⁺` -/

/-- The projection `Φ₁ = P ∘ ½(1 − χ) : V_Λ → V_Λ⁺` onto the `(Λ∖Λ₀)`-charged, `θ`-even part. -/
noncomputable def Phi1 : LatModuleGen leech →ₗ[ℂ] VPlus :=
  plusProj ∘ₗ ((1 / 2 : ℂ) • (LinearMap.id - (chiLat leech frameChar).toLinearMap))

theorem Phi1_of_mem {v : VPlus} (hv : v ∈ frameSector 1) : Phi1 (v : LatModuleGen leech) = v := by
  have h := mem_frameSector.mp hv
  rw [Moonshine.Extraspecial.sgn_one, neg_one_smul] at h
  simp only [Phi1, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, h, sub_neg_eq_add]
  rw [← two_smul ℂ, smul_smul]
  norm_num
  exact plusProj_of_mem v

open Classical in
theorem Phi1_word (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier) :
    Phi1 (wordStateLatGen leech l γ)
      = if γ ∈ lambda0 then 0 else plusProj (wordStateLatGen leech l γ) := by
  simp only [Phi1, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, chiLat_wordStateLatGen]
  split_ifs with h
  · rw [chiSign_frameChar_of_mem h, one_smul, sub_self, smul_zero, map_zero]
  · rw [chiSign_frameChar_of_not_mem h, neg_one_smul, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num

/-- The weight-`n` projected word states of `V₃⁺`. -/
def wordSetV3 (n : ℤ) : Set VPlus :=
  {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier), γ ∉ lambda0 ∧
    (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = plusProj (wordStateLatGen leech l γ)}

/-- **`(V₃⁺)_n` is spanned by the projected word states of weight `n`.** -/
theorem V3_le_span_words (n : ℤ) {v : VPlus} (hv1 : v ∈ frameSector 1)
    (hvn : v ∈ leechVOAPlus.grading n) : v ∈ span ℂ (wordSetV3 n) := by
  have hv' : (v : LatModuleGen leech) ∈ leechVOA.grading n := hvn
  have hv2 := leechVOA_grading_le_span_words n hv'
  have hv3 : v ∈ (span ℂ {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier),
      (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = wordStateLatGen leech l γ}).map Phi1 :=
    ⟨_, hv2, Phi1_of_mem hv1⟩
  rw [Submodule.map_span] at hv3
  refine (span_le.mpr ?_) hv3
  rintro _ ⟨_, ⟨l, γ, hw, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, Phi1_word]
  split_ifs with hγ
  · exact zero_mem _
  · exact subset_span ⟨l, γ, hγ, hw, rfl⟩

end VOA.Moonshine.FZGen
