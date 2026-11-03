/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TrialityCurrents
import VOA.Examples.LatticeBackgroundChargeA

/-!
# `Θ = σχσ` is a lift of `−1`  (Moonshine step M8g)

`TrialityCurrents.lean` shows `Θ (α_j(−1)𝟙) = −α_j(−1)𝟙` for all 24 coordinate roots.  Since `Θ`
is an automorphism, it therefore **anticommutes with every Heisenberg mode**
`α_j(−1)𝟙₍ₙ₎` (`golayTheta_heis`).  The zero modes `H_j = α_j(−1)𝟙₍₀₎` act on the momentum sector
`F_λ = chargeSec λ` by `⟨α_j,λ⟩ = λ_j` (`smul_hSt_zero_latStateGen`, general `L`), and these 24
numbers determine `λ`; hence

  `golayTheta_chargeSec : Θ (F_λ) ⊆ F_{−λ}`.

Together: `Θ` maps `p(α(−n)) ⊗ e^λ` into `p(−α(−n)) ⊗ ℂ e^{−λ}` — it is a lift of `−1 ∈ O(N)`
to `Aut V_N` in the FLM sense (up to the scalars `c_λ` with `Θ e^λ = c_λ e^{−λ}`, which are not
computed here).  Consequently `golayV0 = V_N^{⟨χ,Θ⟩}` is the fixed-point algebra of a lift of `−1`
on `V_{Λ₀} = V_N^χ`.

## Status
`sorry`-free, no new axioms.  Unconditional.  The scalars `c_λ` are not computed in
this file; the isomorphism `golayV0 ≅ V0P` is proved downstream (`golayToV0`,
`golayToV0_isVOAHom`, `FrameBridgeGolay.lean`).
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

theorem smul_sum_left {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : PreVertexAlgebra 𝒱) {ι : Type*}
    (s : Finset ι) (f : ι → 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (∑ i ∈ s, f i) n v = ∑ i ∈ s, V.smul (f i) n v :=
  map_sum (AddMonoidHom.mk' (fun u => V.smul u n v) (fun a b => PreVertexAlgebra.smul_add_left V a b n v)) f s

theorem Aut.map_smul_c {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (g : Aut W) (c : ℂ) (x : 𝒱) : g (c • x) = c • g x :=
  g.toLinearEquiv.map_smul c x

theorem hSt_eq_sum (α : L.carrier) :
    hSt L α = ∑ a : Fin (rank L), chargeCoord L α a • wordStateLatGen L [(0, a)] 0 := by
  rw [hSt, WpC2.vSchur_one', vVar, latStateGen, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wordStateLatGen_eq, wordStateN_cons, wordStateN_nil, mul_one, TensorProduct.smul_tmul']

theorem mode_zero_alphaLatGen (a : Fin (rank L)) (p : FockN (rank L)) (γ : L.carrier) :
    mode (alphaLatGen L a) 0 (latStateGen L p γ) = chargeCoord L γ a • latStateGen L p γ := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 by norm_num, alphaLatGen_apply, if_pos rfl,
    currentN_apply, show (-(-1 : ℤ) - 1) = 0 by norm_num, oscN_zero, LinearMap.rTensor_zero,
    zero_add, zGradeOpGen_latStateGen]

/-- The Heisenberg zero mode `(α(−1)𝟙)₍₀₎` acts on `p ⊗ e^γ` by `⟨α,γ⟩`. -/
theorem smul_hSt_zero_latStateGen (α : L.carrier) (p : FockN (rank L)) (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (hSt L α) 0 (latStateGen L p γ)
      = ((L.form α γ : ℤ) : ℂ) • latStateGen L p γ := by
  rw [hSt_eq_sum, smul_sum_left]
  simp only [PreVertexAlgebra.smul_smul_left]
  have hw : ∀ a : Fin (rank L), (latticeVOAGen L hEven hPos).smul (wordStateLatGen L [(0, a)] 0) 0
      (latStateGen L p γ) = chargeCoord L γ a • latStateGen L p γ := by
    intro a
    show mode (YfullGen L hEven hPos _) 0 _ = _
    rw [YfullGen_word, BgA.YwordLatGen_singleton, genFieldLatGen_zero, mode_zero_alphaLatGen]
  simp only [hw, smul_smul]
  rw [← Finset.sum_smul, sum_chargeCoord L hPos]

theorem coordEα_smul_hSt_zero (α μ : L.carrier) (x : LatModuleGen L) :
    coordEα L μ ((latticeVOAGen L hEven hPos).smul (hSt L α) 0 x)
      = ((L.form α μ : ℤ) : ℂ) • coordEα L μ x := by
  have h : (coordEα L μ).comp (mode (YfullGen L hEven hPos (hSt L α)) 0)
      = ((L.form α μ : ℤ) : ℂ) • coordEα L μ := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    rw [LinearMap.comp_apply]
    show coordEα L μ ((latticeVOAGen L hEven hPos).smul (hSt L α) 0 (latStateGen L q.1 q.2)) = _
    rw [smul_hSt_zero_latStateGen, map_smul, LinearMap.smul_apply, latStateGen, coordEα_apply]
    split_ifs with h
    · rw [h]
    · simp
  exact congrArg (fun f => f x) h

theorem mem_chargeSec_of_coordEα {ν : L.carrier} {x : LatModuleGen L}
    (h : ∀ μ, μ ≠ ν → coordEα L μ x = 0) : x ∈ chargeSec L ν := by
  have hx : x - mkEα L ν (coordEα L ν x) = 0 := by
    apply eq_zero_of_coordEα
    intro μ
    rw [map_sub, mkEα_apply, coordEα_apply]
    by_cases hμ : μ = ν
    · subst hμ; rw [if_pos rfl, sub_self]
    · rw [if_neg hμ, h μ hμ, sub_zero]
  rw [sub_eq_zero] at hx
  rw [hx]; exact ⟨_, rfl⟩

end VOA.LatGen

namespace VOA.Moonshine.Triality

open scoped BigOperators TensorProduct
open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN

/-- `Θ` anticommutes with every Heisenberg mode `α_j(−1)𝟙₍ₙ₎`. -/
theorem golayTheta_heis (j : Fin 24) (n : ℤ) (v : LatModuleGen golayN) :
    golayTheta (golayVOA.smul (hSt golayN (golayRoot j)) n v)
      = -golayVOA.smul (hSt golayN (golayRoot j)) n (golayTheta v) := by
  rw [Aut.map_smul, golayTheta_hSt, ← neg_one_smul ℂ (hSt golayN (golayRoot j)),
    PreVertexAlgebra.smul_smul_left, neg_one_smul]

theorem golayRoot_form_eq (j : Fin 24) (μ : golayN.carrier) : golayN.form (golayRoot j) μ = gv μ j := by
  rw [golayN_form, golayRoot_coe]
  simp [dotProduct, Pi.single_apply]

theorem gv_injective : Function.Injective gv := by
  intro x y h
  exact (show Function.Injective (fun z : ↥Leech.preG => (z : Fin 24 → ℤ)) from Subtype.val_injective) h

set_option maxRecDepth 20000 in
/-- **`Θ` maps the momentum sector `F_λ` into `F_{−λ}`.** -/
theorem golayTheta_chargeSec (lam : golayN.carrier) {x : LatModuleGen golayN}
    (hx : x ∈ chargeSec golayN lam) : golayTheta x ∈ chargeSec golayN (-lam) := by
  apply mem_chargeSec_of_coordEα
  intro μ hμ
  by_contra hne
  apply hμ
  apply gv_injective
  funext j
  -- `H_j (Θx) = −λ_j Θx`
  have hHx : golayVOA.smul (hSt golayN (golayRoot j)) 0 x
      = ((golayN.form (golayRoot j) lam : ℤ) : ℂ) • x := by
    obtain ⟨p, rfl⟩ := hx
    exact smul_hSt_zero_latStateGen golayN golayN_even golayN_posDef _ p lam
  have hH : golayVOA.smul (hSt golayN (golayRoot j)) 0 (golayTheta x)
      = -((golayN.form (golayRoot j) lam : ℤ) : ℂ) • golayTheta x := by
    have h := golayTheta_heis j 0 x
    have h2 : golayTheta (golayVOA.smul (hSt golayN (golayRoot j)) 0 x)
        = ((golayN.form (golayRoot j) lam : ℤ) : ℂ) • golayTheta x := by
      exact (congrArg (fun y => golayTheta y) hHx).trans (golayTheta.toLinearEquiv.map_smul _ x)
    rw [h2] at h
    rw [neg_smul, h, neg_neg]
  have hc := coordEα_smul_hSt_zero golayN golayN_even golayN_posDef (golayRoot j) μ (golayTheta x)
  rw [show (latticeVOAGen golayN golayN_even golayN_posDef).smul = golayVOA.smul from rfl, hH,
    map_smul] at hc
  have hc' : (((golayN.form (golayRoot j) μ : ℤ) : ℂ) + ((golayN.form (golayRoot j) lam : ℤ) : ℂ))
      • coordEα golayN μ (golayTheta x) = 0 := by
    rw [add_smul, ← hc]; simp
  rcases smul_eq_zero.mp hc' with h0 | h0
  · rw [golayRoot_form_eq, golayRoot_form_eq] at h0
    rw [gv_neg, Pi.neg_apply]
    have h2 : gv μ j + gv lam j = 0 := by exact_mod_cast h0
    omega
  · exact absurd h0 hne

end VOA.Moonshine.Triality
