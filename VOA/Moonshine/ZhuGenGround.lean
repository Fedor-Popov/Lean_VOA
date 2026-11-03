/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenSectors

/-!
# The ground-state residual reduced to a statement about the lattice `Λ₀`

The ground states `x_γ = e^γ + e^{-γ}` of `V₀⁺` can only arise, at leading order, from products
of two ground states.  Three kinds of products are available (`α, β ∈ Λ₀ \ 0`, `k = ⟨α,β⟩`):

* `k = -1`: `x_α₍₀₎x_β = ε·x_{α+β}` (`ZhuGenLattice`);
* `k = 0`: `x_α₍₋₁₎x_β = ε·(x_{α+β} + x_{α-β})` (`ZhuGenLattice`);
* `k ≥ 1`: `frameX0P_smul_of_form_pos`:
  `x_α₍₋ₖ₋₁₎x_β = ε·x_{α+β} + 2ε·P(S_{2k}(α) ⊗ e^{α-β})`, and the second term is an
  **excited** state of charge `α - β` (a Fock state if `α = β`), so it is covered by
  `ExcitedSpanned` resp. `FockSpanned` (`excited_mem_span_lowerProd`).

Hence (`groundSpanned_of_lattice`) `GroundSpanned` follows from `FockSpanned`,
`ExcitedSpanned` and the purely lattice-theoretic statement `GroundLattice`: every `x_γ`,
`|γ|² ≥ 6`, lies in the span of the "ground relations" `GroundRel (½|γ|²)` listed above.
A hand proof of `GroundLattice` for `Λ₀` in Golay
coordinates (`⟨α,γ⟩ = 3` or `≥ 5` for some norm-4 `α`, `α = γ/2` allowed; the three exceptional
families `±4eᵢ`, `(±1)²⁴` with codeword sign set, and `(±3,±1²³)` with a codeword condition are
resolved by triangles of `k = 0` relations) was checked numerically; this file does **not** prove it.

## Main results
* `frameX0P_smul_of_form_pos`, `excitedV0`, `excited_mem_span_lowerProd`.
* `GroundRel`, `GroundLattice` (named residual), `groundSpanned_of_lattice`.
* `zhuGenerated_weightTwo_of_residuals : FockSpanned → ExcitedSpanned → GroundLattice →
  ZhuGenerated weightTwo`.

## Status
`sorry`-free; no project axiom.  `FockSpanned`, `ExcitedSpanned`, `GroundLattice` are hypotheses
here.  `GroundLattice` is proved in `GroundLattice.lean` (`SigmaExist.groundLattice`); see
`zhuGenerated_weightTwo_of_fock_excited`.  Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.ZhuGen LatGen IntegralLattice HeisenbergN
open Submodule

/-! ## §1  The `k ≥ 1` product -/

/-- `e^a₍ₙ₎e^c = ε(a,c)·S_d(a) ⊗ e^{a+c}` with `d = -n-1-⟨a,c⟩ ≥ 0`. -/
theorem e_smul_e_of_nonneg (a c : leech.carrier) {n : ℤ} {d : ℕ} (hd : -n - 1 - leech.form a c = d) :
    leechVOA.smul (latChargeGen leech a) n (latChargeGen leech c)
      = latticeCocycle leech a c • latStateGen leech (vSchur leech a d) (a + c) := by
  have h := leechVOA_smul_latChargeGen_state a c n (vacuumN (rank leech))
  change leechVOA.smul _ n (latStateGen leech (vacuumN (rank leech)) c) = _
  rw [h, hd, EEVec_vacuum, if_pos (by positivity), Int.toNat_natCast]

/-- `⟨α,β⟩ = k ≥ 1 ⇒ x_α₍₋ₖ₋₁₎x_β = ε·x_{α+β} + ε·(S_{2k}(α) ⊗ e^{α-β} + θ(⋯))`. -/
theorem frameX0P_smul_of_form_pos {α β : leech.carrier} {k : ℕ} (h : leech.form α β = k) :
    ((leechVOAPlus.smul (frameX0P α) (-(k : ℤ) - 1) (frameX0P β) : VPlus) : LatModuleGen leech)
      = latticeCocycle leech α β • (frameX0 (α + β)
        + (2 : ℂ) • (plusProj (latStateGen leech (vSchur leech α (2 * k)) (α - β)) :
            LatModuleGen leech)) := by
  rw [plus_smul_coe, frameX0P_coe, frameX0P_coe,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_add_right,
    e_smul_e_of_eq α β (by omega),
    e_smul_e_of_nonneg α (-β) (d := 2 * k) (by rw [leech_form_neg_right]; push_cast; omega),
    e_smul_e_of_nonneg (-α) β (d := 2 * k) (by rw [leech_form_neg_left]; push_cast; omega),
    e_smul_e_of_eq (-α) (-β) (by rw [leech_form_neg_left, leech_form_neg_right]; omega),
    latticeCocycle_neg_neg, latticeCocycle_neg_left, latticeCocycle_neg_right, plusProj_coe,
    thetaLat_latStateGen, sigmaN_vSchur, frameX0,
    show -α + -β = -(α + β) by abel, show -α + β = -(α - β) by abel, show α + -β = α - β by abel,
    smul_smul, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul]
  simp only [smul_add]
  abel

/-! ## §2  Excited states from `ExcitedSpanned` -/

theorem plusProj_latStateGen_mem_V0 (p : FockN (rank leech)) {δ : leech.carrier} (hδ : δ ∈ lambda0) :
    plusProj (latStateGen leech p δ) ∈ V0Sub.carrier := by
  rw [V0Sub_carrier, mem_frameSector, Moonshine.Extraspecial.sgn_zero, one_smul, plusProj_coe,
    map_smul, map_add, chiLat_thetaLat, chiLat_latStateGen, chiSign_frameChar_of_mem hδ, one_smul]

/-- `p ↦ P(p ⊗ e^δ)` as a linear map into `V₀⁺` (`δ ∈ Λ₀`). -/
noncomputable def excitedV0 {δ : leech.carrier} (hδ : δ ∈ lambda0) : FockN (rank leech) →ₗ[ℂ] V0Sub.carrier where
  toFun p := ⟨plusProj (latStateGen leech p δ), plusProj_latStateGen_mem_V0 p hδ⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [latStateGen_add_boson, map_add]
  map_smul' c p := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [latStateGen_smul, map_smul]

theorem excitedV0_coe {δ : leech.carrier} (hδ : δ ∈ lambda0) (p : FockN (rank leech)) :
    ((excitedV0 hδ p : V0Sub.carrier) : VPlus) = plusProj (latStateGen leech p δ) := rfl

theorem excitedV0_word {δ : leech.carrier} (hδ : δ ∈ lambda0) (l : List (ℕ × Fin (rank leech))) :
    excitedV0 hδ (wordStateN l) = wordV0 l hδ := by
  apply Subtype.ext
  rw [excitedV0_coe, wordV0_coe, wordStateLatGen_eq]
  rfl

/-- Under `FockSpanned` and `ExcitedSpanned`, every projected state `P(p ⊗ e^δ)` (`δ ∈ Λ₀`,
`p` of Fock weight `w ≥ 1`, total weight `w + ½|δ|² ≥ 3`) is a combination of weight-raising
products of lower-weight states. -/
theorem excited_mem_span_lowerProd (hF : FockSpanned) (hE : ExcitedSpanned) {δ : leech.carrier}
    (hδ : δ ∈ lambda0) {w : ℕ} (hw : 1 ≤ w) (h3 : 3 ≤ (w : ℤ) + LatGen.halfNorm leech δ)
    {p : FockN (rank leech)} (hp : p ∈ gradingWN (rank leech) w) :
    excitedV0 hδ p ∈ span ℂ (lowerProd V0P ((w : ℤ) + LatGen.halfNorm leech δ)) := by
  have hsp := gradingWN_le_span_words (rank leech) w hp
  have hle : span ℂ {p | ∃ l : List (ℕ × Fin (rank leech)), wordWt l = w ∧ p = wordStateN l}
      ≤ (span ℂ (lowerProd V0P ((w : ℤ) + LatGen.halfNorm leech δ))).comap (excitedV0 hδ) := by
    rw [span_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, mem_comap, excitedV0_word]
    by_cases hδ0 : δ = 0
    · subst hδ0
      rw [halfNorm_zero, add_zero] at h3 ⊢
      have := hF l (by rw [hl]; exact h3)
      rwa [hl] at this
    · have hl0 : l ≠ [] := by rintro rfl; simp at hl; omega
      have := hE l δ hδ hδ0 hl0
      rwa [hl] at this
  exact hle hsp

/-! ## §3  The lattice residual -/

/-- The **ground relations** of weight `n`: `x_{α+β}` for `⟨α,β⟩ = -1` or `⟨α,β⟩ ≥ 1`; and `x_{α+β} + x_{α-β}` for `⟨α,β⟩ = 0` (`α, β ∈ Λ₀ \ 0`, `½|α+β|² = n`). -/
def GroundRel (n : ℤ) : Set V0Sub.carrier :=
  {x | ∃ (α β : leech.carrier) (hα : α ∈ lambda0) (hβ : β ∈ lambda0), α ≠ 0 ∧ β ≠ 0 ∧
      LatGen.halfNorm leech (α + β) = n ∧
      ((leech.form α β = -1 ∨ 1 ≤ leech.form α β) ∧ x = x0 (lambda0.add_mem hα hβ) ∨
        leech.form α β = 0 ∧ x = x0 (lambda0.add_mem hα hβ) + x0 (lambda0.sub_mem hα hβ))}

/-- **Lattice residual (ground states).**  Every `x_γ`, `γ ∈ Λ₀`, `|γ|² ≥ 6`, is a linear
combination of the ground relations of its weight.  (Equivalently, since the `x_γ` are linearly
independent, a combinatorial statement about `Λ₀`.) -/
def GroundLattice : Prop :=
  ∀ (γ : leech.carrier) (hγ : γ ∈ lambda0), 6 ≤ leech.form γ γ →
    x0 hγ ∈ span ℂ (GroundRel (LatGen.halfNorm leech γ))

theorem GroundRel_le (hF : FockSpanned) (hE : ExcitedSpanned) (n : ℤ) :
    span ℂ (GroundRel n) ≤ span ℂ (lowerProd V0P n) := by
  rw [span_le]
  rintro _ ⟨α, β, hα, hβ, hα0, hβ0, hn, (⟨hk | hk, rfl⟩ | ⟨hk, rfl⟩)⟩
  · rw [← hn]; exact x0_mem_span_lowerProd_of_form_neg_one hα hβ hα0 hβ0 hk
  · -- `k ≥ 1`
    obtain ⟨k, hkk⟩ : ∃ k : ℕ, leech.form α β = k := ⟨(leech.form α β).toNat, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have h4α := form_ge_four hα0
    have h4β := form_ge_four hβ0
    have e1 := two_mul_halfNorm α
    have e2 := two_mul_halfNorm β
    have e3 := two_mul_halfNorm (α + β)
    have e4 := two_mul_halfNorm (α - β)
    rw [form_add_self, hkk] at e3
    rw [form_sub_self, hkk] at e4
    have hmem : V0P.smul (x0 hα) (-(k : ℤ) - 1) (x0 hβ) ∈ lowerProd V0P n :=
      ⟨LatGen.halfNorm leech α, LatGen.halfNorm leech β, -(k : ℤ) - 1, by omega, by omega,
        by omega, by omega, x0 hα, x0_mem_grading hα, x0 hβ, x0_mem_grading hβ, rfl⟩
    have hδ := lambda0.sub_mem hα hβ
    have hex := excited_mem_span_lowerProd hF hE hδ (w := 2 * k) (by omega) (by push_cast; omega)
      (vSchur_mem_gradingWN leech α (2 * k))
    rw [show ((2 * k : ℕ) : ℤ) + LatGen.halfNorm leech (α - β) = n by push_cast; omega] at hex
    have heq : V0P.smul (x0 hα) (-(k : ℤ) - 1) (x0 hβ)
        = latticeCocycle leech α β • (x0 (lambda0.add_mem hα hβ)
          + (2 : ℂ) • excitedV0 hδ (vSchur leech α (2 * k))) := by
      apply Subtype.ext
      apply Subtype.ext
      rw [V0P_smul_coe]
      exact frameX0P_smul_of_form_pos hkk
    have h1 := smul_mem _ (latticeCocycle leech α β) (subset_span (R := ℂ) hmem)
    rw [heq, smul_smul, latticeCocycle_sq, one_smul] at h1
    have := sub_mem h1 (smul_mem _ (2 : ℂ) hex)
    rwa [add_sub_cancel_right] at this
  · rw [← hn]; exact x0_add_mem_span_lowerProd_of_form_zero hα hβ hα0 hβ0 hk

/-- `GroundSpanned` from `ExcitedSpanned` and the lattice residual. -/
theorem groundSpanned_of_lattice (hF : FockSpanned) (hE : ExcitedSpanned) (hL : GroundLattice) :
    GroundSpanned :=
  fun γ hγ h6 => GroundRel_le hF hE _ (hL γ hγ h6)

/-- **`ZhuGenerated ((V₀⁺)₂)` from the three residuals** `FockSpanned`, `ExcitedSpanned`,
`GroundLattice`. -/
theorem zhuGenerated_weightTwo_of_residuals (hF : FockSpanned) (hE : ExcitedSpanned)
    (hL : GroundLattice) : ZhuGenerated weightTwo :=
  zhuGenerated_weightTwo_of_sectors hF hE (groundSpanned_of_lattice hF hE hL)

end VOA.Moonshine.SigmaExist
