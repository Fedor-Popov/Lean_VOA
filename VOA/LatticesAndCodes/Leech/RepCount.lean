/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Leech.Defs
import VOA.LatticesAndCodes.Theta.QExpansion
import VOA.LatticesAndCodes.ModularForms.LevelOne

/-!
# Ebeling's Proposition 2.8, and the 196560 minimal vectors of the Leech lattice

For **every** even unimodular positive definite lattice of rank `24`,

`r(4) + 24·r(2) = 196560`,

where `r(2m)` is the number of vectors of norm `2m`.  Ebeling uses it twice: for `Γ_Golay`
(`r(2) = 48`) and for the Leech lattice (`r(2) = 0`, so `r(4) = 196560`).

## The proof

`ϑ_Γ` is a modular form of weight `12` (M20), and `M₁₂` is two-dimensional with basis
`E₄³, E₆²` (M19).  On that two-dimensional space the three `q`-coefficients `c₀, c₁, c₂` satisfy
one linear relation, and evaluating on the basis identifies it as

`c₂ = 196560·c₀ − 24·c₁`.

The `q`-expansion bridge `IntegralLattice.coeff_qExpansion_thetaModularForm` turns that into the
statement about representation numbers.

## Main results

* `ModularForm.coeff_two_of_weight_twelve` — the relation on `M₁₂`.
* `IntegralLattice.repCount_four_of_rank_24` — Ebeling's Proposition 2.8.
* `Leech.repCount_four` — the Leech lattice has `196560` vectors of norm `4`.

## References

Ebeling, *Lattices and Codes*, §2.8 (Proposition 2.8).
-/

open Complex UpperHalfPlane EisensteinSeries
open scoped MatrixGroups Real

namespace ModularForm

/-! ### The `q`-coefficients of `E₄` and `E₆` up to order two -/

theorem E₄_coeff_zero : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero _ ⟨2, rfl⟩

theorem E₄_coeff_one : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 1 = 240 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]

theorem E₄_coeff_two : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 2 = 2160 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show (ArithmeticFunction.sigma 3 2 : ℕ) = 9 from by decide]

theorem E₆_coeff_zero : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 0 = 1 :=
  E_qExpansion_coeff_zero _ ⟨3, rfl⟩

theorem E₆_coeff_one : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 1 = -504 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

theorem E₆_coeff_two : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 2 = -16632 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel,
    show (ArithmeticFunction.sigma 5 2 : ℕ) = 33 from by decide]

/-! ### Low coefficients of a product of power series -/

theorem coeff_zero_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 0 = φ.coeff 0 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]

theorem coeff_one_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 1 = φ.coeff 0 * ψ.coeff 1 + φ.coeff 1 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_two_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 2
      = φ.coeff 0 * ψ.coeff 2 + φ.coeff 1 * ψ.coeff 1 + φ.coeff 2 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-! ### The relation on `M₁₂` -/

theorem qExpansion_eisMonomial (a b : ℕ) :
    qExpansion 1 (eisMonomial a b : ℍ → ℂ)
      = (qExpansion 1 (E₄ : ℍ → ℂ)) ^ a * (qExpansion 1 (E₆ : ℍ → ℂ)) ^ b := by
  rw [eisMonomial, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem wtIdx_twelve {p : ℕ × ℕ} (hp : p ∈ wtIdx 12) : p = (3, 0) ∨ p = (0, 2) := by
  rw [mem_wtIdx] at hp
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.injEq]
  omega

/-- On level-one modular forms of weight `12` the three lowest `q`-coefficients satisfy
`c₂ = 196560·c₀ − 24·c₁`.  Both `E₄³` (with `1, 720, 179280`) and `E₆²` (with `1, −1008, 220752`)
satisfy it, and they span. -/
theorem coeff_two_of_weight_twelve (f : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) :
    (qExpansion 1 (f : ℍ → ℂ)).coeff 2
      = 196560 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0
        - 24 * (qExpansion 1 (f : ℍ → ℂ)).coeff 1 := by
  have hf : f ∈ Submodule.span ℂ (Set.range (eisBasisFun 12)) := by
    rw [span_eisBasisFun]
    trivial
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨p, rfl⟩ := hg
    have hq : qExpansion 1 (eisBasisFun 12 p : ℍ → ℂ)
        = (qExpansion 1 (E₄ : ℍ → ℂ)) ^ (p : ℕ × ℕ).1
          * (qExpansion 1 (E₆ : ℍ → ℂ)) ^ (p : ℕ × ℕ).2 := by
      rw [eisBasisFun, ModularForm.qExpansion_mcast, qExpansion_eisMonomial]
    rcases wtIdx_twelve p.2 with hp | hp
    · rw [hq, hp]
      simp only [pow_zero, mul_one, pow_succ, pow_zero, one_mul]
      rw [coeff_zero_mul, coeff_zero_mul, coeff_one_mul, coeff_one_mul, coeff_two_mul,
        coeff_two_mul, coeff_zero_mul, coeff_one_mul, E₄_coeff_zero, E₄_coeff_one, E₄_coeff_two]
      ring
    · rw [hq, hp]
      simp only [pow_zero, one_mul, pow_succ]
      rw [coeff_zero_mul, coeff_one_mul, coeff_two_mul, E₆_coeff_zero, E₆_coeff_one,
        E₆_coeff_two]
      ring
  | zero =>
    have h0 : qExpansion 1 ((0 : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ) = 0 := by
      have h := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (0 : ℂ)
        (0 : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ))
      simpa using h
    rw [h0]
    simp
  | add x y _ _ hx hy =>
    have hadd : qExpansion 1 ((x + y : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ)
        = qExpansion 1 (x : ℍ → ℂ) + qExpansion 1 (y : ℍ → ℂ) :=
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL x y
    rw [hadd]
    simp only [map_add]
    rw [hx, hy]
    ring
  | smul a x _ hx =>
    have hsmul : qExpansion 1 ((a • x : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) : ℍ → ℂ)
        = a • qExpansion 1 (x : ℍ → ℂ) :=
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL a x
    rw [hsmul]
    simp only [PowerSeries.coeff_smul, smul_eq_mul]
    rw [hx]
    ring

end ModularForm

namespace IntegralLattice

variable {Γ : IntegralLattice}

/-- **Ebeling, Proposition 2.8.**  For every even unimodular positive definite lattice of rank
`24`, `r(4) + 24·r(2) = 196560`. -/
theorem repCount_four_of_rank_24 (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    (hrk : Γ.rank = 24) : Γ.repCount 4 + 24 * Γ.repCount 2 = 196560 := by
  have hw : ((Γ.rank / 2 : ℕ) : ℤ) = ((12 : ℕ) : ℤ) := by rw [hrk]
  set f := Γ.thetaModularForm h he hu with hf
  set g : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ) := ModularForm.mcast hw f with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
    rw [hg, ModularForm.qExpansion_mcast]
  have h2 := ModularForm.coeff_two_of_weight_twelve g
  rw [hqg] at h2
  have c0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 1 := by
    rw [hf]
    exact Γ.coeff_qExpansion_thetaModularForm_zero h he hu
  have c1 : (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = (Γ.repCount 2 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 1]
    norm_num
  have c2 : (qExpansion 1 (f : ℍ → ℂ)).coeff 2 = (Γ.repCount 4 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 2]
    norm_num
  rw [c0, c1, c2] at h2
  have hC : ((Γ.repCount 4 + 24 * Γ.repCount 2 : ℕ) : ℂ) = ((196560 : ℕ) : ℂ) := by
    push_cast
    rw [h2]
    ring
  exact_mod_cast hC

end IntegralLattice

namespace Leech

theorem lattice_repCount_two : Leech.lattice.repCount 2 = 0 := by
  have hset : {x : Leech.lattice | IntegralLattice.normSq x = 2} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact lattice_no_roots x
  show ({x : Leech.lattice | IntegralLattice.normSq x = 2}).ncard = 0
  rw [hset, Set.ncard_empty]

/-- **The Leech lattice has `196560` vectors of norm `4`** — Ebeling §2.8, from Proposition 2.8
and the absence of roots. -/
theorem repCount_four : Leech.lattice.repCount 4 = 196560 := by
  have h := IntegralLattice.repCount_four_of_rank_24 lattice_isPosDef lattice_isEven
    lattice_isUnimodular lattice_rank
  rw [lattice_repCount_two] at h
  omega

end Leech
