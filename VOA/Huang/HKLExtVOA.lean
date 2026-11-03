/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtModes
import VOA.Moonshine.VnatAxiomsVir

/-!
# HKL extensions: the vertex operator algebra `W = A`, given locality

`extVOA` — the **vertex operator algebra structure on the carrier of an algebra object** `A`
of `Rep V` (HKL 2015, Thm 3.2), with

* grading `W_k = A_k` (integral by trivial twist, `isInternal_int`),
* vertex operator `Y_W(a, z) b = μ(𝒴_{A,A}(a, z) b)` (`extField`),
* vacuum `η(𝟙)`, conformal vector `η(ω)`, central charge `c_V`,

every axiom proved from the algebra structure and the proved tensor-category facts — VA1 (the
`L₀`-conjugation property of `𝒴`), VA2 (left unit law), VA3 (right unit law + the skew module
operator), VA5 (truncation), VOA1 (`Y_W(ηω) = Y_A(ω)` and the module Virasoro relations), VOA2
(weights), VOA3 (the `L₋₁`-derivative property of `𝒴`) — **except** the three explicit
hypotheses:

* `hloc` — **locality** of `Y_W` (VA4).  This is the analytic core of HKL Thm 3.2: from
  associativity of `μ`, the associativity/commutativity of intertwining operators
  (`evalAssoc_fourPoint`, `associativityBoth_of_stronglyRational_pbw`,
  `commutativityInput_of_stronglyRational_pbw`) and commutativity of `μ` (`ext_skew`), the matrix
  coefficients of `Y_W(a,z₁)Y_W(b,z₂)` and `Y_W(b,z₂)Y_W(a,z₁)` are expansions of one rational
  function with poles only at `z₁ = z₂` (integral weights: `ext_eq_zero_of_not_int`).
* `hvac`, `hpos` — **CFT type** `A_0 = ℂ η(𝟙)`, `A_k = 0` for `k < 0`: from haploidity and
  pseudo-unitarity of `V` via semisimplicity (`A ≅ ⊕ X_i`, non-vacuum `X_i` of positive weight).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLExt

open CategoryTheory
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable (F : FusionChoice V) {A : Ordinary V}

/-- A formal distribution is determined by its modes. -/
theorem formalDist_ext_mode {𝒲 : Type*} {f g : FormalDist 𝒲} (h : ∀ n, mode f n = mode g n) :
    f = g := by
  funext j
  have := h (-j - 1)
  change f (-(-j - 1) - 1) = g (-(-j - 1) - 1) at this
  rwa [show (-(-j - 1) - 1 : ℤ) = j by ring] at this

/-- With trivial twist, the integral weight spaces form an internal direct sum. -/
theorem isInternal_int (htw : (twistIso A).hom = 𝟙 A) :
    DirectSum.IsInternal (fun k : ℤ => A.isMod.weight (k : ℂ)) := by
  have hA := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp A.isMod.isInternal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep.comp hA.1 Int.cast_injective, ?_⟩
  rw [← hA.2]
  apply le_antisymm
  · exact iSup_le fun k => le_iSup_of_le (k : ℂ) le_rfl
  · refine iSup_le fun α => ?_
    by_cases hα : A.isMod.weight α = ⊥
    · rw [hα]; exact bot_le
    · obtain ⟨k, rfl⟩ := weight_int_of_twist htw hα
      exact le_iSup_of_le k le_rfl

/-- The vacuum of `V` lies in weight `0` of the adjoint module. -/
theorem vacuum_mem_adj : V.vacuum ∈ (adjointModule V).weight ((0 : ℤ) : ℂ) := by
  change V.vacuum ∈ adjWeight V ((0 : ℤ) : ℂ)
  rw [adjWeight_cast]; exact V.vacuum_mem

/-- The conformal vector of `V` lies in weight `2` of the adjoint module. -/
theorem omega_mem_adj : V.conformalVector ∈ (adjointModule V).weight ((2 : ℤ) : ℂ) := by
  change V.conformalVector ∈ adjWeight V ((2 : ℤ) : ℂ)
  rw [adjWeight_cast]; exact V.conformal_mem

variable (m : tensorObj F A A ⟶ A) (η : vacuumObject ⟶ A)

/-- `Y_W(η v)` is the `V`-module field `Y_A(v)` (left unit law). -/
theorem extField_unit (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom) (v : 𝒱) (k : ℤ) :
    mode (extField F m (η.val v)) k = mode (A.isMod.YM v) k := by
  refine LinearMap.ext fun b => ?_
  rw [mode_extField, ext_unit_left_int F m η hl]

/-- **The HKL extension vertex operator algebra** on the carrier of `A`, given locality
(`hloc`) and CFT type (`hvac`, `hpos`); all other axioms are proved. -/
def extVOA (hl : tensorHom F η (𝟙 A) ≫ m = (leftUnitor F A).hom)
    (hr : tensorHom F (𝟙 A) η ≫ m = (rightUnitor F A).hom) (htw : (twistIso A).hom = 𝟙 A)
    (hloc : ∀ a b : A.carrier, Local (extField F m a) (extField F m b))
    (hvac : A.isMod.weight 0 = ℂ ∙ η.val V.vacuum)
    (hpos : ∀ k : ℤ, k < 0 → A.isMod.weight (k : ℂ) = ⊥) :
    VertexOperatorAlgebra A.carrier where
  grading k := A.isMod.weight (k : ℂ)
  isInternal := isInternal_int htw
  finrank k := A.isMod.finrank (k : ℂ)
  Y := extField F m
  vacuum := η.val V.vacuum
  vacuum_mem := hom_mem_weight (M₂ := 𝒱) (A₂ := adjointModule V) η.property vacuum_mem_adj
  grading_mode := by
    intro k l u hu v hv n
    rw [mode_extField]
    have h := FusionTop.mem_weight (extIntertwiner F m).property hu hv (n : ℂ)
    convert h using 2
    push_cast; ring
  vacuum_Y := by
    refine formalDist_ext_mode fun k => ?_
    rw [mode_one]
    refine LinearMap.ext fun b => ?_
    rw [mode_extField, ext_vacuum_left F m η hl]
    split_ifs <;> rfl
  creation := by
    intro u
    refine ⟨?_, fun n hn => ?_⟩
    · rw [mode_extField]; exact (ext_creation F m η hr u).1
    · rw [mode_extField]; exact (ext_creation F m η hr u).2 n hn
  locality := hloc
  regularity := by
    intro u v
    obtain ⟨N, hN⟩ := (extIntertwiner F m).property.truncation u v 0
    refine ⟨N, fun n hn => ?_⟩
    rw [mode_extField]
    have := hN n hn
    rwa [zero_add] at this
  conformalVector := η.val V.conformalVector
  conformal_mem := hom_mem_weight (M₂ := 𝒱) (A₂ := adjointModule V) η.property omega_mem_adj
  centralCharge := V.centralCharge
  virasoro := by
    intro p q
    rw [extField_unit F m η hl, extField_unit F m η hl, extField_unit F m η hl]
    exact VOA.Moonshine.VnatAxioms.module_virasoro A.isMod.toWeakModule p q
  L0_grading := by
    intro n v hv
    rw [mode_extField, ext_unit_left_int F m η hl]
    have h := A.isMod.L0_weight _ v hv
    exact_mod_cast h
  translation := by
    intro v
    have hL : mode (extField F m (η.val V.conformalVector)) 0 v = A.isMod.Lm1 v := by
      rw [mode_extField, ext_unit_left_int F m η hl]
    rw [hL]
    refine formalDist_ext_mode fun n => ?_
    rw [mode_deriv]
    refine LinearMap.ext fun b => ?_
    rw [mode_extField, (extIntertwiner F m).property.L_neg_one, LinearMap.smul_apply,
      LinearMap.smul_apply, mode_extField]
    rw [show ((n - 1 : ℤ) : ℂ) = (n : ℂ) - 1 by push_cast; ring, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast; rfl
  vacuum_grade := by
    rw [Int.cast_zero]; exact hvac
  positivity := hpos

@[simp] theorem extVOA_vacuum (hl hr htw hloc hvac hpos) :
    (extVOA F m η hl hr htw hloc hvac hpos).vacuum = η.val V.vacuum := rfl

@[simp] theorem extVOA_conformalVector (hl hr htw hloc hvac hpos) :
    (extVOA F m η hl hr htw hloc hvac hpos).conformalVector = η.val V.conformalVector := rfl

@[simp] theorem extVOA_centralCharge (hl hr htw hloc hvac hpos) :
    (extVOA F m η hl hr htw hloc hvac hpos).centralCharge = V.centralCharge := rfl

theorem extVOA_grading (hl hr htw hloc hvac hpos) (k : ℤ) :
    (extVOA F m η hl hr htw hloc hvac hpos).grading k = A.isMod.weight (k : ℂ) := rfl

/-- The products of `extVOA` are the modes of `Y_W`. -/
theorem extVOA_smul (hl hr htw hloc hvac hpos) (a : A.carrier) (k : ℤ) (b : A.carrier) :
    (extVOA F m η hl hr htw hloc hvac hpos).smul a k b = (extIntertwiner F m).val (k : ℂ) a b :=
  mode_extField F m a k b

end VOA.Huang.HKLExt
