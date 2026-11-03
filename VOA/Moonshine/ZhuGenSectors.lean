/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenLattice

/-!
# `V0LowerSpanned` split into the Fock, charged-excited and ground-state sectors

`(V₀⁺)_n` is spanned by the projected word states `P(h_{a₁}(-n₁)⋯h_{a_r}(-n_r) ⊗ e^γ)` with
`γ ∈ Λ₀` and weight `∑ nᵢ + ½|γ|² = n`, where `P = ½(1 + θ)` (`plusProj`)
(`V0P_grading_le_span_wordV0`).  Hence the named residual `V0LowerSpanned` of `ZhuGenV0.lean`
follows from three sector residuals (`v0LowerSpanned_of_sectors`):

* `FockSpanned` — charge `0` (the `M(1)⁺` part), weight `≥ 3`;
* `ExcitedSpanned` — charge `γ ≠ 0`, at least one oscillator;
* `GroundSpanned` — the ground states `x_γ = e^γ + e^{-γ}`, `|γ|² ≥ 6`.

Each is a statement about weight-raising products of lower-weight states of `V₀⁺`; the expected
proofs were confirmed numerically in small rank.

## Main results
* `wordV0`, `wordV0_mem_grading`, `V0P_grading_le_span_wordV0`.
* `FockSpanned`, `ExcitedSpanned`, `GroundSpanned` (named residuals).
* `v0LowerSpanned_of_sectors`, `zhuGenerated_weightTwo_of_sectors`.

## Status
`sorry`-free; no project axiom.  The three sector residuals are open.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.ZhuGen LatGen IntegralLattice HeisenbergN
open Submodule

/-! ## §1  Word states in `V₀⁺` -/

theorem latStateGen_mem_grading {w : ℕ} {p : FockN (rank leech)} (hp : p ∈ gradingWN (rank leech) w)
    (γ : leech.carrier) :
    latStateGen leech p γ ∈ leechVOA.grading ((w : ℤ) + LatGen.halfNorm leech γ) := by
  have hb : latStateGen leech p γ ∈ bigradα leech ((w : ℤ), γ) :=
    ⟨p, by rw [gradingZN_of_nonneg (by positivity)]; simpa using hp, rfl⟩
  exact bigradα_le_gradingLatGen leech (w : ℤ) γ hb

theorem word_mem_grading (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier) :
    wordStateLatGen leech l γ ∈ leechVOA.grading ((wordWt l : ℤ) + LatGen.halfNorm leech γ) := by
  rw [wordStateLatGen_eq]
  exact latStateGen_mem_grading (wordStateN_mem_gradingWN l) γ

theorem plusProj_mem_grading {k : ℤ} {x : LatModuleGen leech} (hx : x ∈ leechVOA.grading k) :
    plusProj x ∈ leechVOAPlus.grading k := by
  change ((plusProj x : VPlus) : LatModuleGen leech) ∈ gradingLatGen leech k
  rw [plusProj_coe]
  exact smul_mem _ _ (add_mem hx (thetaLat_mem_gradingLatGen leech hx))

theorem chiSign_frameChar_of_mem {γ : leech.carrier} (hγ : γ ∈ lambda0) :
    chiSign leech frameChar γ = 1 := by
  rw [chiSign, (mem_lambda0 γ).mp hγ, Moonshine.Extraspecial.sgn_zero]

theorem chiSign_frameChar_of_not_mem {γ : leech.carrier} (hγ : γ ∉ lambda0) :
    chiSign leech frameChar γ = -1 := by
  have h : frameChar γ = 1 := by
    have h0 : frameChar γ ≠ 0 := fun h => hγ ((mem_lambda0 γ).mpr h)
    generalize frameChar γ = z at h0 ⊢
    fin_cases z
    · exact absurd rfl h0
    · rfl
  rw [chiSign, h, Moonshine.Extraspecial.sgn_one]

theorem plusProj_word_mem_V0 (l : List (ℕ × Fin (rank leech))) {γ : leech.carrier}
    (hγ : γ ∈ lambda0) : plusProj (wordStateLatGen leech l γ) ∈ V0Sub.carrier := by
  rw [V0Sub_carrier, mem_frameSector, Moonshine.Extraspecial.sgn_zero, one_smul, plusProj_coe,
    map_smul, map_add, chiLat_thetaLat, chiLat_wordStateLatGen, chiSign_frameChar_of_mem hγ,
    one_smul]

/-- The projected word state `P(word(l) ⊗ e^γ) ∈ V₀⁺` (`γ ∈ Λ₀`). -/
noncomputable def wordV0 (l : List (ℕ × Fin (rank leech))) {γ : leech.carrier} (hγ : γ ∈ lambda0) :
    V0Sub.carrier :=
  ⟨plusProj (wordStateLatGen leech l γ), plusProj_word_mem_V0 l hγ⟩

theorem wordV0_coe (l : List (ℕ × Fin (rank leech))) {γ : leech.carrier} (hγ : γ ∈ lambda0) :
    ((wordV0 l hγ : V0Sub.carrier) : VPlus) = plusProj (wordStateLatGen leech l γ) := rfl

theorem wordV0_mem_grading (l : List (ℕ × Fin (rank leech))) {γ : leech.carrier} (hγ : γ ∈ lambda0) :
    wordV0 l hγ ∈ V0P.grading ((wordWt l : ℤ) + LatGen.halfNorm leech γ) :=
  plusProj_mem_grading (word_mem_grading l γ)

theorem wordV0_nil {γ : leech.carrier} (hγ : γ ∈ lambda0) :
    wordV0 [] hγ = (1 / 2 : ℂ) • x0 hγ := by
  apply Subtype.ext
  rw [wordV0_coe, wordStateLatGen_nil, plusProj_latChargeGen]
  rfl

/-! ## §2  The spanning set -/

/-- The weight-`n` projected word states of `V₀⁺`. -/
def wordSet (n : ℤ) : Set V0Sub.carrier :=
  {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier) (hγ : γ ∈ lambda0),
    (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = wordV0 l hγ}

/-- `(V_Λ)_n` is spanned by the word states of weight `n`. -/
theorem leechVOA_grading_le_span_words (n : ℤ) :
    leechVOA.grading n ≤ span ℂ {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier),
      (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = wordStateLatGen leech l γ} := by
  intro v hv
  have hv' : v ∈ (span ℂ (Set.range (Function.uncurry (wordStateLatGen leech)))).map
      (piHom leechVOA n) := by
    rw [wordStateLatGen_span leech, Submodule.map_top]
    exact ⟨v, piHom_of_mem leechVOA hv⟩
  rw [Submodule.map_span] at hv'
  refine (span_le.mpr ?_) hv'
  rintro _ ⟨_, ⟨⟨l, γ⟩, rfl⟩, rfl⟩
  simp only [Function.uncurry_apply_pair, SetLike.mem_coe]
  by_cases h : (wordWt l : ℤ) + LatGen.halfNorm leech γ = n
  · rw [← h, piHom_of_mem leechVOA (word_mem_grading l γ)]
    exact subset_span ⟨l, γ, rfl, rfl⟩
  · rw [piHom_of_mem_ne leechVOA h (word_mem_grading l γ)]
    exact zero_mem _

/-- The projection `Φ = P ∘ ½(1 + χ) : V_Λ → V_Λ⁺` onto the `Λ₀`-charged, `θ`-even part. -/
noncomputable def Phi0 : LatModuleGen leech →ₗ[ℂ] VPlus :=
  plusProj ∘ₗ ((1 / 2 : ℂ) • (LinearMap.id + (chiLat leech frameChar).toLinearMap))

theorem Phi0_of_mem {v : VPlus} (hv : v ∈ frameSector 0) : Phi0 (v : LatModuleGen leech) = v := by
  have h := mem_frameSector.mp hv
  rw [Moonshine.Extraspecial.sgn_zero, one_smul] at h
  simp only [Phi0, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, h]
  rw [← two_smul ℂ, smul_smul]
  norm_num
  exact plusProj_of_mem v

open Classical in
theorem Phi0_word (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier) :
    Phi0 (wordStateLatGen leech l γ)
      = if γ ∈ lambda0 then plusProj (wordStateLatGen leech l γ) else 0 := by
  simp only [Phi0, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, chiLat_wordStateLatGen]
  split_ifs with h
  · rw [chiSign_frameChar_of_mem h, one_smul, ← two_smul ℂ, smul_smul]; norm_num
  · rw [chiSign_frameChar_of_not_mem h, neg_one_smul, add_neg_cancel, smul_zero, map_zero]

/-- **`(V₀⁺)_n` is spanned by the projected word states of weight `n`.** -/
theorem V0P_grading_le_span_wordV0 (n : ℤ) : V0P.grading n ≤ span ℂ (wordSet n) := by
  intro v hv
  have hv1 : ((v : VPlus) : LatModuleGen leech) ∈ leechVOA.grading n := hv
  have hv2 := leechVOA_grading_le_span_words n hv1
  have hv3 : (v : VPlus) ∈ (span ℂ {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier),
      (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = wordStateLatGen leech l γ}).map Phi0 := by
    refine ⟨_, hv2, ?_⟩
    exact Phi0_of_mem (by rw [← V0Sub_carrier]; exact v.2)
  rw [Submodule.map_span] at hv3
  have hle : span ℂ (Phi0 '' {x | ∃ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier),
      (wordWt l : ℤ) + LatGen.halfNorm leech γ = n ∧ x = wordStateLatGen leech l γ})
      ≤ (span ℂ (wordSet n)).map V0Sub.carrier.subtype := by
    rw [span_le]
    rintro _ ⟨_, ⟨l, γ, hw, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Phi0_word]
    split_ifs with hγ
    · exact ⟨wordV0 l hγ, subset_span ⟨l, γ, hγ, hw, rfl⟩, rfl⟩
    · exact zero_mem _
  obtain ⟨w, hw, hwv⟩ := hle hv3
  have : w = v := Subtype.ext hwv
  rwa [← this]

/-! ## §3  The three sector residuals -/

/-- **Fock sector residual.** Every projected charge-`0` word state of weight `≥ 3` is a
combination of weight-raising products of lower-weight states. -/
def FockSpanned : Prop :=
  ∀ l : List (ℕ × Fin (rank leech)), 3 ≤ (wordWt l : ℤ) →
    wordV0 l lambda0.zero_mem ∈ span ℂ (lowerProd V0P (wordWt l))

/-- **Charged-excited sector residual.** -/
def ExcitedSpanned : Prop :=
  ∀ (l : List (ℕ × Fin (rank leech))) (γ : leech.carrier) (hγ : γ ∈ lambda0), γ ≠ 0 → l ≠ [] →
    wordV0 l hγ ∈ span ℂ (lowerProd V0P ((wordWt l : ℤ) + LatGen.halfNorm leech γ))

/-- **Ground-state residual.** -/
def GroundSpanned : Prop :=
  ∀ (γ : leech.carrier) (hγ : γ ∈ lambda0), 6 ≤ leech.form γ γ →
    x0 hγ ∈ span ℂ (lowerProd V0P (LatGen.halfNorm leech γ))

theorem halfNorm_zero : LatGen.halfNorm leech 0 = 0 := by
  simp [LatGen.halfNorm]

/-- **The sector reduction.** -/
theorem v0LowerSpanned_of_sectors (hF : FockSpanned) (hE : ExcitedSpanned) (hG : GroundSpanned) :
    V0LowerSpanned := by
  intro n hn
  refine (V0P_grading_le_span_wordV0 n).trans (span_le.mpr ?_)
  rintro _ ⟨l, γ, hγ, hw, rfl⟩
  by_cases h0 : γ = 0
  · subst h0
    rw [halfNorm_zero, add_zero] at hw
    have := hF l (by omega)
    rwa [hw] at this
  · by_cases hl : l = []
    · subst hl
      rw [wordV0_nil]
      refine smul_mem _ _ ?_
      have e := two_mul_halfNorm γ
      simp only [wordWt_nil, Nat.cast_zero, zero_add] at hw
      have := hG γ hγ (by omega)
      rwa [hw] at this
    · have := hE l γ hγ h0 hl
      rwa [hw] at this

/-- `ZhuGenerated ((V₀⁺)₂)` from the three sector residuals. -/
theorem zhuGenerated_weightTwo_of_sectors (hF : FockSpanned) (hE : ExcitedSpanned)
    (hG : GroundSpanned) : ZhuGenerated weightTwo :=
  zhuGenerated_weightTwo_of_lowerSpanned (v0LowerSpanned_of_sectors hF hE hG)

end VOA.Moonshine.SigmaExist
