/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Leech.RepCount
import VOA.LatticesAndCodes.Roots.RootLattice

/-!
# Two more representation numbers of an even unimodular lattice of rank 24

`LatticesAndCodes.Leech.RepCount` runs the weight-`12` coefficient argument as far as `c₂` and
gets Ebeling's Proposition 2.8.  Here the same argument is pushed two coefficients further, to
`c₃` and `c₄`, giving `r(6)` and `r(8)` in terms of `r(2)`.

Because `M₁₂` is two dimensional with basis `E₄³, E₆²`, each coefficient `c_n` with `n ≥ 2` is a
fixed linear combination of `c₀` and `c₁`.  Evaluating on the two basis elements pins the
combination down:

* `c₃ = 16773120·c₀ + 252·c₁`,
* `c₄ = 398034000·c₀ − 1472·c₁`.

The point of the second relation is that its constant term is nonzero: a rank-`24` even unimodular
positive definite lattice with no roots must contain a vector of norm `8`, which is what a later
uniqueness argument needs.

## Main results

* `ModularForm.coeff_three_of_weight_twelve`, `ModularForm.coeff_four_of_weight_twelve` — the two
  relations on `M₁₂`.
* `IntegralLattice.repCount_six_of_rank_24`, `IntegralLattice.repCount_eight_of_rank_24`.
* `IntegralLattice.exists_normSq_eq_eight` — a rootless such lattice has a vector of norm `8`.
* `Leech.repCount_six`, `Leech.repCount_eight`.

## References

Ebeling, *Lattices and Codes*, §2.8 (Proposition 2.8) and §3.
-/

open Complex UpperHalfPlane EisensteinSeries
open scoped MatrixGroups Real

namespace ModularForm

/-! ### The `q`-coefficients of `E₄` and `E₆` in orders three and four -/

theorem E₄_coeff_three : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 3 = 6720 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show (ArithmeticFunction.sigma 3 3 : ℕ) = 28 from by decide]

theorem E₄_coeff_four : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 4 = 17520 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show (ArithmeticFunction.sigma 3 4 : ℕ) = 73 from by decide]

theorem E₆_coeff_three : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 3 = -122976 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel,
    show (ArithmeticFunction.sigma 5 3 : ℕ) = 244 from by decide]

theorem E₆_coeff_four : (qExpansion 1 (E₆ : ℍ → ℂ)).coeff 4 = -532728 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel,
    show (ArithmeticFunction.sigma 5 4 : ℕ) = 1057 from by decide]

/-! ### Coefficients three and four of a product of power series -/

theorem coeff_three_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 3
      = φ.coeff 0 * ψ.coeff 3 + φ.coeff 1 * ψ.coeff 2 + φ.coeff 2 * ψ.coeff 1
        + φ.coeff 3 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_four_mul (φ ψ : PowerSeries ℂ) :
    (φ * ψ).coeff 4
      = φ.coeff 0 * ψ.coeff 4 + φ.coeff 1 * ψ.coeff 3 + φ.coeff 2 * ψ.coeff 2
        + φ.coeff 3 * ψ.coeff 1 + φ.coeff 4 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

/-! ### The relations on `M₁₂` -/

/-- On level-one modular forms of weight `12`, `c₃ = 16773120·c₀ + 252·c₁`.  The two basis
elements have coefficients `1, 720, 179280, 16954560` (`E₄³`) and `1, −1008, 220752, 16519104`
(`E₆²`), and both satisfy the relation. -/
theorem coeff_three_of_weight_twelve (f : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) :
    (qExpansion 1 (f : ℍ → ℂ)).coeff 3
      = 16773120 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0
        + 252 * (qExpansion 1 (f : ℍ → ℂ)).coeff 1 := by
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
      simp only [pow_zero, mul_one, pow_succ, one_mul]
      simp only [coeff_zero_mul, coeff_one_mul, coeff_two_mul, coeff_three_mul,
        E₄_coeff_zero, E₄_coeff_one, E₄_coeff_two, E₄_coeff_three]
      ring
    · rw [hq, hp]
      simp only [pow_zero, one_mul, pow_succ]
      simp only [coeff_zero_mul, coeff_one_mul, coeff_three_mul,
        E₆_coeff_zero, E₆_coeff_one, E₆_coeff_two, E₆_coeff_three]
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

/-- On level-one modular forms of weight `12`, `c₄ = 398034000·c₀ − 1472·c₁`.  Checked on
`E₄³` (coefficient `396974160`) and on `E₆²` (coefficient `399517776`). -/
theorem coeff_four_of_weight_twelve (f : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ)) :
    (qExpansion 1 (f : ℍ → ℂ)).coeff 4
      = 398034000 * (qExpansion 1 (f : ℍ → ℂ)).coeff 0
        - 1472 * (qExpansion 1 (f : ℍ → ℂ)).coeff 1 := by
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
      simp only [pow_zero, mul_one, pow_succ, one_mul]
      simp only [coeff_zero_mul, coeff_one_mul, coeff_two_mul, coeff_three_mul, coeff_four_mul,
        E₄_coeff_zero, E₄_coeff_one, E₄_coeff_two, E₄_coeff_three, E₄_coeff_four]
      ring
    · rw [hq, hp]
      simp only [pow_zero, one_mul, pow_succ]
      simp only [coeff_zero_mul, coeff_one_mul, coeff_four_mul,
        E₆_coeff_zero, E₆_coeff_one, E₆_coeff_two, E₆_coeff_three, E₆_coeff_four]
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

/-- For every even unimodular positive definite lattice of rank `24`,
`r(6) = 16773120 + 252·r(2)`. -/
theorem repCount_six_of_rank_24 (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    (hrk : Γ.rank = 24) : Γ.repCount 6 = 16773120 + 252 * Γ.repCount 2 := by
  have hw : ((Γ.rank / 2 : ℕ) : ℤ) = ((12 : ℕ) : ℤ) := by rw [hrk]
  set f := Γ.thetaModularForm h he hu with hf
  set g : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ) := ModularForm.mcast hw f with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
    rw [hg, ModularForm.qExpansion_mcast]
  have h3 := ModularForm.coeff_three_of_weight_twelve g
  rw [hqg] at h3
  have c0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 1 := by
    rw [hf]
    exact Γ.coeff_qExpansion_thetaModularForm_zero h he hu
  have c1 : (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = (Γ.repCount 2 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 1]
    norm_num
  have c3 : (qExpansion 1 (f : ℍ → ℂ)).coeff 3 = (Γ.repCount 6 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 3]
    norm_num
  rw [c0, c1, c3] at h3
  have hC : ((Γ.repCount 6 : ℕ) : ℂ) = ((16773120 + 252 * Γ.repCount 2 : ℕ) : ℂ) := by
    push_cast
    rw [h3]
    ring
  exact_mod_cast hC

/-- For every even unimodular positive definite lattice of rank `24`,
`r(8) + 1472·r(2) = 398034000`.  Stated additively so that it stays inside `ℕ`. -/
theorem repCount_eight_of_rank_24 (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    (hrk : Γ.rank = 24) : Γ.repCount 8 + 1472 * Γ.repCount 2 = 398034000 := by
  have hw : ((Γ.rank / 2 : ℕ) : ℤ) = ((12 : ℕ) : ℤ) := by rw [hrk]
  set f := Γ.thetaModularForm h he hu with hf
  set g : ModularForm 𝒮ℒ ((12 : ℕ) : ℤ) := ModularForm.mcast hw f with hg
  have hqg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
    rw [hg, ModularForm.qExpansion_mcast]
  have h4 := ModularForm.coeff_four_of_weight_twelve g
  rw [hqg] at h4
  have c0 : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 1 := by
    rw [hf]
    exact Γ.coeff_qExpansion_thetaModularForm_zero h he hu
  have c1 : (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = (Γ.repCount 2 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 1]
    norm_num
  have c4 : (qExpansion 1 (f : ℍ → ℂ)).coeff 4 = (Γ.repCount 8 : ℂ) := by
    rw [hf, Γ.coeff_qExpansion_thetaModularForm h he hu 4]
    norm_num
  rw [c0, c1, c4] at h4
  have hC : ((Γ.repCount 8 + 1472 * Γ.repCount 2 : ℕ) : ℂ) = ((398034000 : ℕ) : ℂ) := by
    push_cast
    rw [h4]
    ring
  exact_mod_cast hC

/-- An even unimodular positive definite lattice of rank `24` with no roots contains a vector of
norm `8`: by the relation above its `r(8)` equals `398034000 ≠ 0`. -/
theorem exists_normSq_eq_eight (h : Γ.IsPosDef) (he : Γ.IsEven) (hu : Γ.IsUnimodular)
    (hrk : Γ.rank = 24) (hroot : Γ.rootSet = ∅) : ∃ u : Γ, IntegralLattice.normSq u = 8 := by
  have h2 : Γ.repCount 2 = 0 := by
    have hset : {x : Γ | IntegralLattice.normSq x = 2} = ∅ := by
      rw [← hroot]
      rfl
    show ({x : Γ | IntegralLattice.normSq x = 2}).ncard = 0
    rw [hset, Set.ncard_empty]
  have h8 := repCount_eight_of_rank_24 h he hu hrk
  rw [h2] at h8
  have hne : ({x : Γ | IntegralLattice.normSq x = 8}).ncard ≠ 0 := by
    show Γ.repCount 8 ≠ 0
    omega
  obtain ⟨u, hu8⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨u, hu8⟩

end IntegralLattice

namespace Leech

/-- The Leech lattice has `16773120` vectors of norm `6`. -/
theorem repCount_six : Leech.lattice.repCount 6 = 16773120 := by
  have h := IntegralLattice.repCount_six_of_rank_24 lattice_isPosDef lattice_isEven
    lattice_isUnimodular lattice_rank
  rw [lattice_repCount_two] at h
  omega

/-- The Leech lattice has `398034000` vectors of norm `8`. -/
theorem repCount_eight : Leech.lattice.repCount 8 = 398034000 := by
  have h := IntegralLattice.repCount_eight_of_rank_24 lattice_isPosDef lattice_isEven
    lattice_isUnimodular lattice_rank
  rw [lattice_repCount_two] at h
  omega

end Leech

#print axioms ModularForm.coeff_three_of_weight_twelve
#print axioms ModularForm.coeff_four_of_weight_twelve
#print axioms IntegralLattice.repCount_six_of_rank_24
#print axioms IntegralLattice.repCount_eight_of_rank_24
#print axioms IntegralLattice.exists_normSq_eq_eight
#print axioms Leech.repCount_six
#print axioms Leech.repCount_eight
