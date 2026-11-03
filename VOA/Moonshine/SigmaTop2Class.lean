/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Octad

/-!
# The norm-4 vectors of `Λ₀`, and the unconditional (R-top) on `V₃⁺`

A norm-4 vector of `Λ₀ = A` is `±(4e_j ± 4e_k)` or an octad vector `γ_S` (`classify_S0`; the
`(±4, ±2⁴)` shape is excluded by the minimum weight 8 of the Golay code,
`Code.golay_eight_le_weight`).  With the root letters (`SigmaTop2Root.lean`) and the octad letters
(`SigmaTop2Octad.lean`) every weight-2 letter of `V₀⁺` intertwines, so the Zhu-generation
reduction closes.

## Main results
* `classify_S0`.
* `octadResidualV3 : OctadResidualV3`.
* `topSigmaV3 : ∃ s φ, TopSigmaV3 s φ`.
* `sigmaV3T_exists` — a `v0Sigma`-twisted intertwiner `Φ : V₃⁺ → T_s⁺` of `V₀⁺`-modules
  (`IsSigmaV3T Φ`) hitting a nonzero cyclic vector `x0T t₀`, `t₀ ∈ T_s`.

## Status
**Unconditional**, `sorry`-free; `#print axioms topSigmaV3`, `sigmaV3T_exists`:
`[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`).  Which `s` occurs is not determined by
the library's definitions (`golayE_not_determined`), hence the `∃ s`.  Reached from the
umbrella `VOA/Moonshine.lean`.  The companion statement on `T_s⁺` (`TopSigmaTT`) is proved in
`SigmaTop2TTOct.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  The shapes of the norm-4 vectors of `Λ₀ = A` -/

theorem int_sq_cases {x : ℤ} (h : x ^ 2 ≤ 8) : x = 0 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  have h1 : x ≤ 2 := by nlinarith
  have h2 : -2 ≤ x := by nlinarith
  omega

theorem valA_form (a : lam0.carrier) : 2 * lam0.form a a = valA a ⬝ᵥ valA a := by
  rw [← inclN_form, golayN_form]
  change 2 * ((valA a ⬝ᵥ valA a) / 2) = _
  have hs : (4 : ℤ) ∣ ∑ i, valA a i := (show ↥Leech.subA from a).2.2
  have h2 : (2 : ℤ) ∣ valA a ⬝ᵥ valA a - ∑ i, valA a i := by
    rw [dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by
      have := Int.even_mul_pred_self (valA a i)
      rw [even_iff_two_dvd] at this
      have e : valA a i * valA a i - valA a i = valA a i * (valA a i - 1) := by ring
      rw [e]; exact this
  omega

theorem aP_valA (j k : Fin 24) : valA (aP j k) = apv j k := rfl

theorem aM_valA (j k : Fin 24) :
    valA (aM j k) = (2 : ℤ) • (Pi.single j 1 + (-1 : ℤ) • Pi.single k 1) := rfl

/-- **The norm-4 vectors of `Λ₀`**: either `±(4e_j ± 4e_k)` or an octad vector `γ_S`. -/
theorem classify_S0 {γ : leech.carrier} (hγ : γ ∈ halfFourChi 0) :
    (∃ j k : Fin 24, j ≠ k ∧ (γ = gP j k ∨ γ = -gP j k ∨ γ = gM j k ∨ γ = -gM j k)) ∨
    (∃ (D : Finset (Fin 24)) (hDA : ind D ∈ Leech.subA), D.card = 8 ∧
      ∃ S : Finset (Fin 24), _root_.Even S.card ∧ S ⊆ D ∧ γ = inclΛ (aSA hDA S)) := by
  obtain ⟨h4, h0⟩ := mem_halfFourChi hγ
  obtain ⟨a, rfl⟩ := (mem_range_inclΛ γ).mpr ((mem_lambda0 γ).mpr h0)
  set x := valA a with hxdef
  have hxx : x ⬝ᵥ x = 8 := by
    have := valA_form a
    rw [← inclΛ_form, h4] at this
    rw [← this]; norm_num
  have hsq : ∀ i, x i ^ 2 ≤ 8 := fun i => by
    rw [← hxx, dotProduct]
    have := Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
    simpa [pow_two] using this
  have hvals := fun i => int_sq_cases (hsq i)
  have hmem : x ∈ Leech.subA := (show ↥Leech.subA from a).2
  have hcode : reduceMod 2 24 x ∈ Code.golay := Leech.mem_preG.mp hmem.1
  have hsum4 : (4 : ℤ) ∣ ∑ i, x i := hmem.2
  set O := Finset.univ.filter (fun i => x i = 1 ∨ x i = -1) with hO
  set F := Finset.univ.filter (fun i => x i = 2 ∨ x i = -2) with hF
  have hsplit : x ⬝ᵥ x = O.card + 4 * F.card := by
    have : ∀ i, x i * x i = (if x i = 1 ∨ x i = -1 then 1 else 0) + 4 * (if x i = 2 ∨ x i = -2 then 1 else 0) := by
      intro i; rcases hvals i with h | h | h | h | h <;> simp [h]
    rw [dotProduct, Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_boole]
  have hsupp : Code.support (reduceMod 2 24 x) = O := by
    ext i
    rw [Code.mem_support, hO, Finset.mem_filter]
    change ((x i : ℤ) : ZMod 2) ≠ 0 ↔ i ∈ Finset.univ ∧ _
    simp only [Finset.mem_univ, true_and]
    rcases hvals i with h | h | h | h | h <;> rw [h] <;> decide
  by_cases hO0 : O.card = 0
  · left
    have hF2 : F.card = 2 := by omega
    obtain ⟨j, k, hjk, hFjk⟩ := Finset.card_eq_two.mp hF2
    have hO' : O = ∅ := Finset.card_eq_zero.mp hO0
    have hjF : j ∈ F := by rw [hFjk]; simp
    have hkF : k ∈ F := by rw [hFjk]; simp
    have hj : x j = 2 ∨ x j = -2 := by rw [hF, Finset.mem_filter] at hjF; exact hjF.2
    have hk : x k = 2 ∨ x k = -2 := by rw [hF, Finset.mem_filter] at hkF; exact hkF.2
    have hoth : ∀ i, i ≠ j → i ≠ k → x i = 0 := by
      intro i hij hik
      have hiF : i ∉ F := by rw [hFjk]; simp [hij, hik]
      have hiO : i ∉ O := by rw [hO']; simp
      rw [hF, Finset.mem_filter] at hiF
      rw [hO, Finset.mem_filter] at hiO
      rcases hvals i with h | h | h | h | h
      · exact h
      · exact absurd ⟨Finset.mem_univ i, Or.inl h⟩ hiO
      · exact absurd ⟨Finset.mem_univ i, Or.inr h⟩ hiO
      · exact absurd ⟨Finset.mem_univ i, Or.inl h⟩ hiF
      · exact absurd ⟨Finset.mem_univ i, Or.inr h⟩ hiF
    refine ⟨j, k, hjk, ?_⟩
    have hval : ∀ (u v : ℤ), x j = u → x k = v →
        x = fun i => if i = j then u else if i = k then v else 0 := by
      intro u v hu hv
      funext i
      by_cases hij : i = j
      · subst hij; simp [hu]
      · by_cases hik : i = k
        · subst hik; simp [hij, hv]
        · simp [hij, hik, hoth i hij hik]
    rcases hj with hj | hj <;> rcases hk with hk | hk
    · left
      have : a = aP j k := valA_injective (by
        rw [← hxdef, hval 2 2 hj hk, aP_valA]; funext i
        simp only [apv, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
        by_cases hij : i = j <;> by_cases hik : i = k <;> simp_all)
      rw [this]; rfl
    · right; right; left
      have : a = aM j k := valA_injective (by
        rw [← hxdef, hval 2 (-2) hj hk, aM_valA]; funext i
        simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
        by_cases hij : i = j <;> by_cases hik : i = k <;> simp_all)
      rw [this]; rfl
    · right; right; right
      have : a = -aM j k := valA_injective (by
        rw [map_neg, ← hxdef, hval (-2) 2 hj hk, aM_valA]; funext i
        simp only [Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
        by_cases hij : i = j <;> by_cases hik : i = k <;> simp_all)
      rw [this, map_neg]; rfl
    · right; left
      have : a = -aP j k := valA_injective (by
        rw [map_neg, ← hxdef, hval (-2) (-2) hj hk, aP_valA]; funext i
        simp only [apv, Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
        by_cases hij : i = j <;> by_cases hik : i = k <;> simp_all)
      rw [this, map_neg]; rfl
  · right
    have hne : reduceMod 2 24 x ≠ 0 := by
      intro h0'
      apply hO0
      rw [← hsupp, h0']
      simp [Code.support]
    have h8 := Code.golay_eight_le_weight hcode hne
    rw [Code.weight_eq_card_support, hsupp] at h8
    have hO8 : O.card = 8 := by omega
    have hF0 : F.card = 0 := by omega
    have hF' : F = ∅ := Finset.card_eq_zero.mp hF0
    have hx01 : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = -1 := by
      intro i
      have hiF : i ∉ F := by rw [hF']; simp
      rw [hF, Finset.mem_filter] at hiF
      rcases hvals i with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd ⟨Finset.mem_univ i, Or.inl h⟩ hiF
      · exact absurd ⟨Finset.mem_univ i, Or.inr h⟩ hiF
    set S := O.filter (fun i => x i = -1) with hSdef
    have hxind : x = ind O - (2 : ℤ) • ind S := by
      funext i
      simp only [ind, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hSdef, hO, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases hx01 i with h | h | h <;> simp [h]
    have hDA : ind O ∈ Leech.subA := by
      refine ⟨Leech.mem_preG.mpr ?_, ?_⟩
      · have : reduceMod 2 24 (ind O) = reduceMod 2 24 x := by
          rw [hxind, map_sub, map_smul]
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply]
          change _ = _ - (2 : ℤ) • (((ind S i : ℤ)) : ZMod 2)
          rw [show ((2 : ℤ) • (((ind S i : ℤ)) : ZMod 2)) = 0 by
            rw [zsmul_eq_mul]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul], sub_zero]
        rw [this]; exact hcode
      · simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hO8]
        norm_num
    have hSsub : S ⊆ O := Finset.filter_subset _ _
    have hSeven : _root_.Even S.card := by
      have h1 : ∑ i, x i = 8 - 2 * S.card := by
        rw [hxind]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hO8]
        push_cast; ring
      rw [h1] at hsum4
      obtain ⟨c, hc⟩ := hsum4
      exact ⟨S.card / 2, by omega⟩
    refine ⟨O, hDA, hO8, S, hSeven, hSsub, ?_⟩
    congr 1
    apply valA_injective
    rw [valA_aSA hDA hSeven, ← hxdef, hxind]

/-! ## §2  (R-top) on `V₃⁺`, and `σ : V₃⁺ → T_s⁺`, unconditionally -/

/-- The octad letters intertwine, for every seed. -/
theorem octadResidualV3 : OctadResidualV3 := by
  intro s t _ _ ht γ hγ hnot
  rcases classify_S0 hγ with ⟨j, k, hjk, hroot⟩ | ⟨D, hDA, hD8, S, hS, hSD, rfl⟩
  · exfalso
    obtain ⟨h1, h2, h3, h4⟩ := hnot j k hjk
    rcases hroot with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  · rw [lV'_eq (inclΛ_mem _)]
    exact phiV3_ZM_aSA hDA hD8 ht hS hSD

/-- **(R-top) on `V₃⁺`, unconditional**: some `φ` satisfies `TopSigmaV3 s φ`. -/
theorem topSigmaV3 : ∃ s φ, TopSigmaV3 s φ := topSigmaV3_exists octadResidualV3

/-- **The triality on the twisted sector, `σ : V₃⁺ → T_s⁺`**, unconditional: a
`v0Sigma`-twisted intertwiner of `V₀⁺`-modules hitting a cyclic vector of `T_s⁺`. -/
theorem sigmaV3T_exists :
    ∃ (s : ZMod 2) (Φ : VPlus →ₗ[ℂ] TP), IsSigmaV3T Φ ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, Φ x = x0T t₀ :=
  sigmaV3T_exists_of_octad octadResidualV3

end VOA.Moonshine.SigmaTop
