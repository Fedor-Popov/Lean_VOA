/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenLocality

/-!
# The ℤ-extended annihilation exponential `E⁺(α)` and its Newton recursion

The infrastructure for the vector-charge exponential contraction (the heart of same-sign locality):
the ℤ-extended annihilation exponential `aExpVecZ α : ℤ → End` (`= aExpVec α N` for `N ≥ 0`, `0`
otherwise), its Newton recursion, and the reassembly lemma.  Direct cross-charge lifts of A₁'s
`aExpZ`/`aExpZ_recursion`/`aExpZ_sum_reassembly` (`Examples/LatticeFields` §8), with the single
A₁ oscillator `α (m+1)` replaced by the charge annihilation mode `chargeOsc α (m+1)`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice)

/-- The **ℤ-extended annihilation exponential** `E⁺(α)_{-N} = aExpVec α N` for `N ≥ 0`, `0` for
`N < 0`.  (`aExpVecZ α N = E⁺(α)_{-N}` as a `FormalDist` coefficient.) -/
noncomputable def aExpVecZ (α : L.carrier) (N : ℤ) : End ℂ (FockN (rank L)) :=
  if 0 ≤ N then aExpVec L α N.toNat else 0

theorem aExpVecZ_neg (α : L.carrier) {N : ℤ} (h : N < 0) : aExpVecZ L α N = 0 := by
  rw [aExpVecZ, if_neg (by omega)]

theorem aExpVecZ_nonneg (α : L.carrier) {N : ℤ} (h : 0 ≤ N) :
    aExpVecZ L α N = aExpVec L α N.toNat := by rw [aExpVecZ, if_pos h]

theorem aExpVecZ_zero (α : L.carrier) : aExpVecZ L α 0 = LinearMap.id := by
  rw [aExpVecZ_nonneg L α le_rfl]; simp [aExpVec_zero]

/-- `E⁺(α)` coefficient as the ℤ-extended `aExpVec`: `E⁺(α)_a = aExpVecZ α (-a)`. -/
theorem EplusVecField_eq_aExpVecZ (α : L.carrier) (a : ℤ) :
    EplusVecField L α a = aExpVecZ L α (-a) := by
  rw [EplusVecField_apply, aExpVecZ]
  by_cases h : a ≤ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- The `aExpVec` Newton recursion, ℤ-extended: for `N ≥ 1`,
`aExpVecZ α N = N⁻¹ ∑_{m<N} (-α(m+1)) ∘ aExpVecZ α (N-1-m)`. -/
theorem aExpVecZ_recursion (α : L.carrier) (N : ℤ) (hN : 1 ≤ N) :
    aExpVecZ L α N = (N : ℂ)⁻¹ • ∑ m ∈ Finset.range N.toNat,
      (-(chargeOsc L α ((m : ℤ) + 1))).comp (aExpVecZ L α (N - 1 - m)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, N.toNat = K + 1 := ⟨N.toNat - 1, by omega⟩
  have hNK : N = (K : ℤ) + 1 := by omega
  rw [aExpVecZ_nonneg L α (by omega), hK, aExpVec_succ, hNK]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  congr 2
  rw [aExpVecZ_nonneg L α (by omega)]
  congr 1
  omega

/-- Reassembly (all `M : ℤ`): for any range `K ≥ M.toNat`, the Newton sum equals `M • aExpVecZ α M`.
Cross-charge lift of `aExpZ_sum_reassembly`. -/
theorem aExpVecZ_sum_reassembly (α : L.carrier) (M : ℤ) (K : ℕ) (hK : M.toNat ≤ K) :
    ∑ m ∈ Finset.range K, (-(chargeOsc L α ((m : ℤ) + 1))).comp (aExpVecZ L α (M - 1 - m))
      = (M : ℂ) • aExpVecZ L α M := by
  by_cases hM : 1 ≤ M
  · have hsplit : ∑ m ∈ Finset.range K,
          (-(chargeOsc L α ((m : ℤ) + 1))).comp (aExpVecZ L α (M - 1 - m))
        = ∑ m ∈ Finset.range M.toNat,
          (-(chargeOsc L α ((m : ℤ) + 1))).comp (aExpVecZ L α (M - 1 - m)) := by
      refine (Finset.sum_subset (s₁ := Finset.range M.toNat) (s₂ := Finset.range K)
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [aExpVecZ_neg L α (by omega), LinearMap.comp_zero]
    rw [hsplit, aExpVecZ_recursion L α M hM, smul_smul, mul_inv_cancel₀ (by
      simp only [ne_eq]; exact_mod_cast (by omega : (M : ℤ) ≠ 0)), one_smul]
  · have hsum0 : ∑ m ∈ Finset.range K,
        (-(chargeOsc L α ((m : ℤ) + 1))).comp (aExpVecZ L α (M - 1 - m)) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [aExpVecZ_neg L α (by omega), LinearMap.comp_zero]
    rw [hsum0]
    rcases lt_or_eq_of_le (by omega : M ≤ 0) with hlt | heq
    · rw [aExpVecZ_neg L α hlt, smul_zero]
    · rw [heq]; simp

/-! ## The atomic field-level contraction move -/

/-- **The atomic field-level contraction** `[β(m+1), E⁻(α)_b] = ⟨α,β⟩·E⁻(α)_{b-(m+1)}` in
`FormalDist`-coefficient (`ℤ`-indexed `b`) form — the ℤ-extension of `chargeOsc_comp_EminusVec`,
the cross-charge lift of A₁'s `alphaC_succ_comp_EminusC`.  The atomic move iterated by the
exponential contraction `crossContr`. -/
theorem chargeOsc_succ_comp_EminusVecField (hPos : L.PosDef) (α β : L.carrier) (m : ℕ) (b : ℤ) :
    (chargeOsc L β ((m : ℤ) + 1)).comp (EminusVecField L α b)
      = (EminusVecField L α b).comp (chargeOsc L β ((m : ℤ) + 1))
        + ((L.form α β : ℤ) : ℂ) • EminusVecField L α (b - ((m : ℤ) + 1)) := by
  have hmode : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  by_cases hb : 0 ≤ b
  · rw [EminusVecField_apply, if_pos hb, hmode,
      chargeOsc_comp_EminusVec L hPos α β (m + 1) b.toNat (by omega)]
    congr 1
    by_cases hle : m + 1 ≤ b.toNat
    · rw [if_pos hle, EminusVecField_apply, if_pos (by omega : (0 : ℤ) ≤ b - ((m + 1 : ℕ) : ℤ))]
      congr 2
      omega
    · rw [if_neg hle, EminusVecField_apply,
        if_neg (by omega : ¬ (0 : ℤ) ≤ b - ((m + 1 : ℕ) : ℤ)), smul_zero]
  · rw [EminusVecField_neg L α (by omega : b < 0), LinearMap.comp_zero, LinearMap.zero_comp,
      EminusVecField_neg L α (by omega : b - ((m : ℤ) + 1) < 0), smul_zero, zero_add]

/-- The atomic move with a trailing operator `X` (the exact shape iterated inside the exponential
contraction `crossContr`'s inner recursion step): `(−β(m+1)) ∘ (E⁻(α)_b ∘ X) = E⁻(α)_b ∘ (−β(m+1)) ∘ X
− ⟨α,β⟩·(E⁻(α)_{b-(m+1)} ∘ X)`.  Cross-charge lift of A₁'s `move_alphaC_past_EminusC`. -/
theorem move_chargeOsc_past_EminusVecField (hPos : L.PosDef) (α β : L.carrier) (m : ℕ) (b : ℤ)
    (X : End ℂ (FockN (rank L))) :
    (-(chargeOsc L β ((m : ℤ) + 1))).comp ((EminusVecField L α b).comp X)
      = (EminusVecField L α b).comp ((-(chargeOsc L β ((m : ℤ) + 1))).comp X)
        - ((L.form α β : ℤ) : ℂ) • ((EminusVecField L α (b - ((m : ℤ) + 1))).comp X) := by
  rw [← LinearMap.comp_assoc, LinearMap.neg_comp,
    chargeOsc_succ_comp_EminusVecField L hPos α β m b]
  simp only [LinearMap.neg_comp, LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    LinearMap.comp_neg]
  abel

end VOA.LatGen
