/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Distinct
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# The two distinctness residuals, proved: `GannonRayhaunDistinct` unconditionally

`Distinct.lean` reduced Gannon–Rayhaun "pairwise non-isomorphic" to `PlusExceptionalResidual`
(`V_{2m}⁺`, `m ≥ 4`, against `V₂^{A₄,S₄,A₅}`) and `ExceptionalResidual` (the three exceptional
orbifolds among themselves). This file proves both, by computing `dim (V₂^G)_n` at `n = 4, 16`
exactly for every `G ≤ Aut V₂` isomorphic to `A₄`, `S₄`, `A₅`.

## Method (Molien / averaging)
* `card_mul_finrank_orbifold`: `|G| · dim (W^G)_n = Σ_{g ∈ G} tr(g | W_n)` for any VOA `W` and
  finite `G ≤ Aut W` (Mathlib's Reynolds projection `Representation.averageMap` and
  `LinearMap.IsProj.trace`; `orbifoldGradingEquiv` identifies `(W^G)_n` with the invariants).
* `trace_charU`: `tr(g_u | (V₂)_n) = τ_n(u) = Σ_{w² ≤ n} u^w p(n − w²)` (torus elements act on the
  charge sectors `sectorK` by scalars; `LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup`).
* `exists_torus`: every finite-order `x ∈ Aut V₂` is conjugate to some `g_u` (`exists_conj_charU`),
  traces are class functions (`trace_autRes_conj`), and `x^j = 1 ↔ u^j = 1` (`charU_injective`).
* `torusTrace{4,16}_{one,two,three,four,five}`: `τ_n(u)` for `u` of order `1, 2, 3, 4`, and
  `τ_n(u) + τ_n(u²)` for `u` of order `5` (which is all that is needed: `g ↦ g²` permutes the
  order-5 elements, `two_mul_sum_by_order`).
* `A4_counts`, `S4_counts`, `A5_counts` (by `decide`): elements of order `1,2,3,4,5` are
  `(1,3,8,0,0)`, `(1,9,8,6,0)`, `(1,15,20,0,24)`.
* Result (`finrank_orbifold_A4/S4/A5`): `dim (V₂^G)₄ = p(4) − p(3)` for all three, and
  `dim (V₂^G)₁₆ = p(16) − p(15) + p(7)`, `p(16) − p(15) + p(0)`, `p(16) − p(15)` respectively
  (numerically `2` and `70, 56, 55`, checked independently in Python by spin decomposition
  `Σ_j (p(n − j²) − p(n − (j+1)²)) · dim (spin j)^G`).

## Main results
* `plusExceptionalResidual : PlusExceptionalResidual` — `dim (V_{2m}⁺)₄ = e + [m = 4]` and
  `p(4) − p(3) = e + o − 3` (`e`, `o` = partitions of `4` with an even / odd number of parts);
  equality would force `o ∈ {3, 4}`, but `o ≤ 2` (`fockCountOdd_one_four_le`).
* `exceptionalResidual : ExceptionalResidual` — weight `16`, with `p(7) ≥ 2`
  (`two_le_fockCount_one_seven`) and `p(0) = 1`.
* `gannonRayhaunDistinct : GannonRayhaunDistinct` — unconditional.

## Status
`sorry`-free, no new axioms.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice Module

/-! ## Averaging over a finite group of automorphisms -/

section Averaging

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The restriction of automorphisms to the weight-`n` space, as a monoid homomorphism. -/
noncomputable def autRes (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : Aut W →* Module.End ℂ (W.grading n) where
  toFun g := g.toLinearEquiv.toLinearMap.restrict (fun _ hx => Aut.map_grading g hx)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem autRes_apply (n : ℤ) (g : Aut W) (x : W.grading n) :
    ((autRes W n g x : W.grading n) : 𝒱) = g (x : 𝒱) := rfl

/-- The trace of an automorphism on a weight space is a class function. -/
theorem trace_autRes_conj (n : ℤ) (φ g : Aut W) :
    LinearMap.trace ℂ _ (autRes W n (φ * g * φ⁻¹)) = LinearMap.trace ℂ _ (autRes W n g) := by
  rw [(autRes W n).map_mul, (autRes W n).map_mul, LinearMap.trace_mul_comm, ← mul_assoc,
    ← (autRes W n).map_mul, ← (autRes W n).map_mul, inv_mul_cancel, one_mul]

/-- The weight-`n` space of the orbifold is the space of `G`-invariants. -/
noncomputable def orbifoldGradingEquiv (G : Subgroup (Aut W)) (n : ℤ) :
    (orbifoldVOA G).grading n ≃ₗ[ℂ]
      Representation.invariants ((autRes W n).comp G.subtype) where
  toFun z := ⟨⟨z.1.1, z.2⟩, fun g => Subtype.ext (z.1.2 g.1 g.2)⟩
  invFun x := ⟨⟨x.1.1, fun g hg => congrArg Subtype.val (x.2 ⟨g, hg⟩)⟩, x.1.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Averaging.** `|G| · dim (W^G)_n = Σ_{g ∈ G} tr(g | W_n)`. -/
theorem card_mul_finrank_orbifold (G : Subgroup (Aut W)) [Fintype G] (n : ℤ)
    [FiniteDimensional ℂ (W.grading n)] :
    (Fintype.card G : ℂ) * finrank ℂ ((orbifoldVOA G).grading n)
      = ∑ g : G, LinearMap.trace ℂ _ (autRes W n g) := by
  classical
  set ρ : Representation ℂ G (W.grading n) := (autRes W n).comp G.subtype
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hcard
  have htr := (Representation.isProj_averageMap ρ).trace
  rw [(orbifoldGradingEquiv G n).finrank_eq, ← htr]
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of]
  rw [smul_eq_mul, ← mul_assoc, mul_invOf_self, one_mul]
  rfl

end Averaging

/-! ## The trace of a torus element on a weight space of `V₂` -/

section TorusTrace

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- `τ_n(u) = Σ_{α² ≤ n} u^α p(n − α²)`: the trace of the torus element `g_u` on `(V₂)_n`. -/
noncomputable def torusTrace (n : ℕ) (u : ℂˣ) : ℂ :=
  ∑ α ∈ normLE (latP 1) (latP_posDef 1 le_rfl) n,
    ((u ^ ci 1 α : ℂˣ) : ℂ) * (fockCount 1 ((n : ℤ) - LatGen.halfNorm (latP 1) α).toNat : ℂ)

theorem charU_sectorK (u : ℂˣ) {k : ℤ} {α : (latP 1).carrier} {x : LatModuleGen (latP 1)}
    (hx : x ∈ sectorK (latP 1) k α) :
    charU 1 le_rfl u x = ((u ^ ci 1 α : ℂˣ) : ℂ) • x := by
  obtain ⟨p, -, rfl⟩ := hx
  exact charU_latStateGen 1 le_rfl u p α

/-- **`tr(g_u | (V₂)_n) = τ_n(u)`.** -/
theorem trace_charU (n : ℕ) (u : ℂˣ) :
    haveI := (V1).finrank (n : ℤ)
    LinearMap.trace ℂ _ (autRes V1 n (charU 1 le_rfl u)) = torusTrace n u := by
  haveI := (V1).finrank (n : ℤ)
  have hf : ∀ α, Set.MapsTo (charU 1 le_rfl u).toLinearEquiv.toLinearMap
      (sectorK (latP 1) n α) (sectorK (latP 1) n α) := by
    intro α x hx
    change charU 1 le_rfl u x ∈ sectorK (latP 1) n α
    rw [charU_sectorK u hx]
    exact Submodule.smul_mem _ _ hx
  have hp : (V1).grading n = ⨆ α ∈ normLE (latP 1) (latP_posDef 1 le_rfl) n, sectorK (latP 1) n α :=
    gradingLatGen_eq_biSup_normLE (latP 1) (latP_posDef 1 le_rfl) n
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup
    (normLE (latP 1) (latP_posDef 1 le_rfl) n)
    ((iSupIndep_sectorK (latP 1) n).comp Subtype.val_injective) hf ((V1).grading n) hp
    (fun _ hx => Aut.map_grading _ hx)
  refine key.trans (Finset.sum_congr rfl fun α hα => ?_)
  have hres : (charU 1 le_rfl u).toLinearEquiv.toLinearMap.restrict (hf α)
      = ((u ^ ci 1 α : ℂˣ) : ℂ) • LinearMap.id := by
    ext x
    exact charU_sectorK u x.2
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul,
    finrank_sectorK (latP 1) n α ((mem_normLE (latP 1) (latP_posDef 1 le_rfl)).mp hα)]
  rw [rank_latP]

/-- The lattice vectors of `√2 ℤ` of half-norm `≤ n` are `−s, …, s` (`s = ⌊√n⌋`). -/
theorem mem_normLE_latP1 (n s : ℕ) (hs : s * s ≤ n) (hs' : n < (s + 1) * (s + 1))
    (v : (latP 1).carrier) :
    v ∈ normLE (latP 1) (latP_posDef 1 le_rfl) n ↔ -(s : ℤ) ≤ ci 1 v ∧ ci 1 v ≤ s := by
  rw [mem_normLE, halfNorm_latP1]
  have hs2 : ((s : ℤ) * s) ≤ n := by exact_mod_cast hs
  have hs'' : (n : ℤ) < ((s : ℤ) + 1) * ((s : ℤ) + 1) := by exact_mod_cast hs'
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- The lattice point `w ∈ ℤ = √2 ℤ`. -/
def lp1 (w : ℤ) : (latP 1).carrier := w

@[simp] theorem ci_lp1 (w : ℤ) : ci 1 (lp1 w) = w := rfl

theorem torusTrace_eq_range (n s : ℕ) (hs : s * s ≤ n) (hs' : n < (s + 1) * (s + 1)) (u : ℂˣ) :
    torusTrace n u = ∑ i ∈ Finset.range (2 * s + 1),
      ((u ^ ((i : ℤ) - s) : ℂˣ) : ℂ) * (fockCount 1 ((n : ℤ) - ((i : ℤ) - s) * ((i : ℤ) - s)).toNat : ℂ) := by
  rw [torusTrace]
  refine Finset.sum_nbij' (fun v => ((ci 1 v + s).toNat : ℕ)) (fun i => lp1 ((i : ℤ) - s))
    ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_normLE_latP1 n s hs hs'] at hv
    rw [Finset.mem_range]; simp only; omega
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [mem_normLE_latP1 n s hs hs', ci_lp1]
    omega
  · intro v hv
    rw [mem_normLE_latP1 n s hs hs'] at hv
    change ((((ci 1 v + s).toNat : ℕ) : ℤ) - s : ℤ) = ci 1 v
    omega
  · intro i _
    change ((ci 1 (lp1 ((i : ℤ) - s)) + s).toNat : ℕ) = i
    rw [ci_lp1]; omega
  · intro v hv
    rw [mem_normLE_latP1 n s hs hs' v] at hv
    have e : ((((ci 1 v + s).toNat : ℕ) : ℤ) - s : ℤ) = ci 1 v := by omega
    rw [halfNorm_latP1, e]

/-- Reduce a power of a root of unity modulo its order. -/
theorem units_zpow_reduce {u : ℂˣ} {d : ℕ} (hd0 : 0 < d) (hd : u ^ d = 1) (w : ℤ) :
    ((u ^ w : ℂˣ) : ℂ) = (u : ℂ) ^ (w % (d : ℤ)).toNat := by
  rw [zpow_eq_zpow_emod' w hd, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

/-- `P k = p(k)` as a complex number. -/
noncomputable abbrev Pc (k : ℕ) : ℂ := (fockCount 1 k : ℂ)

theorem cube_rel {x : ℂ} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

theorem five_rel {x : ℂ} (h5 : x ^ 5 = 1) (h1 : x ≠ 1) : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0 := by
  have : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

theorem sq_rel {x : ℂ} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) : x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linear_combination h2
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1))

theorem four_rel {x : ℂ} (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : x ^ 2 = -1 := by
  have : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linear_combination h4
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2))

theorem units_val_ne_one {u : ℂˣ} (h : u ≠ 1) : (u : ℂ) ≠ 1 := fun e => h (Units.ext e)

theorem units_val_pow_eq_one {u : ℂˣ} {d : ℕ} (h : u ^ d = 1) : (u : ℂ) ^ d = 1 := by
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem units_sq_zpow (u : ℂˣ) (w : ℤ) : ((u ^ 2) ^ w : ℂˣ) = u ^ (2 * w) := by
  rw [← zpow_natCast, ← zpow_mul]; rfl

@[simp] theorem int_toNat_ofNat' (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℤ)).toNat = OfNat.ofNat n :=
  Int.toNat_natCast n

/-! ### The torus traces at weights `4` and `16`, by the order of `u` -/

theorem torusTrace4_one : torusTrace 4 1 = (1 : ℂ) * Pc 4 + (2 : ℂ) * Pc 3 + (2 : ℂ) * Pc 0 := by
  rw [torusTrace_eq_range 4 2 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (d := 1) (by norm_num) (one_pow 1)]
  norm_num [Pc, int_toNat_ofNat']
  ring

theorem torusTrace4_two {u : ℂˣ} (h2 : u ^ 2 = 1) (h1 : u ≠ 1) : torusTrace 4 u = (1 : ℂ) * Pc 4 + (-2 : ℂ) * Pc 3 + (2 : ℂ) * Pc 0 := by
  have hr := sq_rel (units_val_pow_eq_one h2) (units_val_ne_one h1)
  rw [torusTrace_eq_range 4 2 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h2]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (2 * Pc 3) * hr

theorem torusTrace4_three {u : ℂˣ} (h3 : u ^ 3 = 1) (h1 : u ≠ 1) : torusTrace 4 u = (1 : ℂ) * Pc 4 + (-1 : ℂ) * Pc 3 + (-1 : ℂ) * Pc 0 := by
  have hr := cube_rel (units_val_pow_eq_one h3) (units_val_ne_one h1)
  rw [torusTrace_eq_range 4 2 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h3]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (Pc 3 + Pc 0) * hr

theorem torusTrace4_four {u : ℂˣ} (h4 : u ^ 4 = 1) (h2 : u ^ 2 ≠ 1) : torusTrace 4 u = (1 : ℂ) * Pc 4 + (-2 : ℂ) * Pc 0 := by
  have hr := four_rel (units_val_pow_eq_one h4)
    (fun e => h2 (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one])))
  rw [torusTrace_eq_range 4 2 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h4]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination ((Pc 3) * (u : ℂ) + (2 * Pc 0)) * hr

theorem torusTrace4_five {u : ℂˣ} (h5 : u ^ 5 = 1) (h1 : u ≠ 1) :
    torusTrace 4 u + torusTrace 4 (u ^ 2) = (2 : ℂ) * Pc 4 + (-1 : ℂ) * Pc 3 + (-1 : ℂ) * Pc 0 := by
  have hr := five_rel (units_val_pow_eq_one h5) (units_val_ne_one h1)
  rw [torusTrace_eq_range 4 2 (by norm_num) (by norm_num), torusTrace_eq_range 4 2 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_sq_zpow, units_zpow_reduce (by norm_num) h5]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (Pc 3 + Pc 0) * hr

theorem torusTrace16_one : torusTrace 16 1 = (1 : ℂ) * Pc 16 + (2 : ℂ) * Pc 15 + (2 : ℂ) * Pc 12 + (2 : ℂ) * Pc 7 + (2 : ℂ) * Pc 0 := by
  rw [torusTrace_eq_range 16 4 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (d := 1) (by norm_num) (one_pow 1)]
  norm_num [Pc, int_toNat_ofNat']
  ring

theorem torusTrace16_two {u : ℂˣ} (h2 : u ^ 2 = 1) (h1 : u ≠ 1) : torusTrace 16 u = (1 : ℂ) * Pc 16 + (-2 : ℂ) * Pc 15 + (2 : ℂ) * Pc 12 + (-2 : ℂ) * Pc 7 + (2 : ℂ) * Pc 0 := by
  have hr := sq_rel (units_val_pow_eq_one h2) (units_val_ne_one h1)
  rw [torusTrace_eq_range 16 4 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h2]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (2 * Pc 15 + 2 * Pc 7) * hr

theorem torusTrace16_three {u : ℂˣ} (h3 : u ^ 3 = 1) (h1 : u ≠ 1) : torusTrace 16 u = (1 : ℂ) * Pc 16 + (-1 : ℂ) * Pc 15 + (-1 : ℂ) * Pc 12 + (2 : ℂ) * Pc 7 + (-1 : ℂ) * Pc 0 := by
  have hr := cube_rel (units_val_pow_eq_one h3) (units_val_ne_one h1)
  rw [torusTrace_eq_range 16 4 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h3]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (Pc 15 + Pc 12 + Pc 0) * hr

theorem torusTrace16_four {u : ℂˣ} (h4 : u ^ 4 = 1) (h2 : u ^ 2 ≠ 1) : torusTrace 16 u = (1 : ℂ) * Pc 16 + (-2 : ℂ) * Pc 12 + (2 : ℂ) * Pc 0 := by
  have hr := four_rel (units_val_pow_eq_one h4)
    (fun e => h2 (Units.ext (by rw [Units.val_pow_eq_pow_val, e, Units.val_one])))
  rw [torusTrace_eq_range 16 4 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_zpow_reduce (by norm_num) h4]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination ((Pc 15 + Pc 7) * (u : ℂ) + (2 * Pc 12)) * hr

theorem torusTrace16_five {u : ℂˣ} (h5 : u ^ 5 = 1) (h1 : u ≠ 1) :
    torusTrace 16 u + torusTrace 16 (u ^ 2) = (2 : ℂ) * Pc 16 + (-1 : ℂ) * Pc 15 + (-1 : ℂ) * Pc 12 + (-1 : ℂ) * Pc 7 + (-1 : ℂ) * Pc 0 := by
  have hr := five_rel (units_val_pow_eq_one h5) (units_val_ne_one h1)
  rw [torusTrace_eq_range 16 4 (by norm_num) (by norm_num), torusTrace_eq_range 16 4 (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, units_sq_zpow, units_zpow_reduce (by norm_num) h5]
  norm_num [Pc, int_toNat_ofNat']
  linear_combination (Pc 15 + Pc 12 + Pc 7 + Pc 0) * hr

/-! ### Every finite-order automorphism has the trace of a torus element -/

/-- `T_n(x) = tr(x | (V₂)_n)`. -/
noncomputable def autTrace (n : ℕ) (x : Aut V1) : ℂ := LinearMap.trace ℂ _ (autRes V1 n x)

theorem conj_pow' (φ g : Aut V1) (j : ℕ) : (φ * g * φ⁻¹) ^ j = φ * g ^ j * φ⁻¹ := by
  have := map_pow (MulAut.conj φ) g j
  simp only [MulAut.conj_apply] at this
  exact this.symm

/-- A finite-order `x ∈ Aut V₂` has, for some `u ∈ ℂˣ`, `tr(x^j | (V₂)_n) = τ_n(u^j)` and
`x^j = 1 ↔ u^j = 1` for all `j` (conjugate `x` into the torus, `exists_conj_charU`). -/
theorem exists_torus (n : ℕ) (x : Aut V1) (hx : IsOfFinOrder x) :
    ∃ u : ℂˣ, (∀ j : ℕ, autTrace n (x ^ j) = torusTrace n (u ^ j)) ∧ (∀ j : ℕ, x ^ j = 1 ↔ u ^ j = 1) := by
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU x hx
  refine ⟨u, fun j => ?_, fun j => ?_⟩
  · rw [autTrace, ← trace_autRes_conj (n : ℤ) φ, ← conj_pow', hφ, ← map_pow, trace_charU]
  · rw [← (charU_injective 1 le_rfl).eq_iff, map_pow, ← hφ, conj_pow', map_one]
    constructor
    · rintro h; rw [h]; group
    · intro h
      have := congrArg (fun y => φ⁻¹ * y * φ) h
      simpa [mul_assoc] using this

theorem isOfFinOrder_of_pow {x : Aut V1} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsOfFinOrder x :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, h⟩

theorem autTrace_one (n : ℕ) : autTrace n 1 = torusTrace n 1 := by
  rw [autTrace, ← map_one (charU 1 le_rfl), trace_charU]

theorem exists_torus_pow {n : ℕ} {x : Aut V1} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    ∃ u : ℂˣ, autTrace n x = torusTrace n u ∧ autTrace n (x ^ 2) = torusTrace n (u ^ 2) ∧
      (∀ j : ℕ, x ^ j = 1 ↔ u ^ j = 1) := by
  obtain ⟨u, hT, hP⟩ := exists_torus n x (isOfFinOrder_of_pow hk h)
  refine ⟨u, ?_, hT 2, hP⟩
  have := hT 1
  simp only [pow_one] at this
  exact this

end TorusTrace

/-! ## Summing a function over a finite group by element orders -/

section ClassSum

variable {H : Type*} [Group H]

/-- The order classes `1`, `2`, `3`, `4`, `5`, as exclusive predicates. -/
def OrdCls (h : H) : ℕ → Prop
  | 1 => h = 1
  | 2 => h ≠ 1 ∧ h ^ 2 = 1
  | 3 => h ^ 2 ≠ 1 ∧ h ^ 3 = 1
  | 4 => h ^ 2 ≠ 1 ∧ h ^ 3 ≠ 1 ∧ h ^ 4 = 1
  | 5 => h ^ 2 ≠ 1 ∧ h ^ 3 ≠ 1 ∧ h ^ 4 ≠ 1 ∧ h ^ 5 = 1
  | _ => False

instance ordClsDec [DecidableEq H] (h : H) : (k : ℕ) → Decidable (OrdCls h k)
  | 0 => isFalse id
  | 1 => inferInstanceAs (Decidable (h = 1))
  | 2 => inferInstanceAs (Decidable (h ≠ 1 ∧ h ^ 2 = 1))
  | 3 => inferInstanceAs (Decidable (h ^ 2 ≠ 1 ∧ h ^ 3 = 1))
  | 4 => inferInstanceAs (Decidable (h ^ 2 ≠ 1 ∧ h ^ 3 ≠ 1 ∧ h ^ 4 = 1))
  | 5 => inferInstanceAs (Decidable (h ^ 2 ≠ 1 ∧ h ^ 3 ≠ 1 ∧ h ^ 4 ≠ 1 ∧ h ^ 5 = 1))
  | _ + 6 => isFalse id

theorem ordCls5_sq {h : H} (hh : OrdCls h 5) : OrdCls (h ^ 2) 5 := by
  obtain ⟨h2, h3, h4, h5⟩ := hh
  have hm : ∀ m : ℕ, h ^ m = h ^ (m % 5) := fun m => pow_eq_pow_mod m h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pow_mul]; exact h4
  · rw [← pow_mul, hm]; norm_num; rintro rfl; simp at h2
  · rw [← pow_mul, hm]; norm_num; exact h3
  · rw [← pow_mul, hm]; norm_num

theorem ordCls5_cube {h : H} (hh : OrdCls h 5) : OrdCls (h ^ 3) 5 := by
  obtain ⟨h2, h3, h4, h5⟩ := hh
  have hm : ∀ m : ℕ, h ^ m = h ^ (m % 5) := fun m => pow_eq_pow_mod m h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, hm]; norm_num; rintro rfl; simp at h2
  · rw [← pow_mul, hm]; norm_num; exact h4
  · rw [← pow_mul, hm]; norm_num; exact h2
  · rw [← pow_mul, hm]; norm_num

theorem ordCls5_sq_cube {h : H} (hh : OrdCls h 5) : (h ^ 2) ^ 3 = h := by
  rw [← pow_mul, pow_eq_pow_mod _ hh.2.2.2]; norm_num

theorem ordCls5_cube_sq {h : H} (hh : OrdCls h 5) : (h ^ 3) ^ 2 = h := by
  rw [← pow_mul, pow_eq_pow_mod _ hh.2.2.2]; norm_num

variable [Fintype H] [DecidableEq H]

/-- The number of elements in an order class. -/
def clsCard (H : Type*) [Group H] [Fintype H] [DecidableEq H] (k : ℕ) : ℕ :=
  (Finset.univ.filter fun h : H => OrdCls h k).card

/-- **Summing over a group by element orders.** If every element has order `≤ 5`, `F` is
constant (`a_k`) on the order-`k` elements for `k ≤ 4`, and `F h + F h² = a₅` for `h` of order
`5`, then `2 Σ F = Σ_{k ≤ 4} 2 c_k a_k + c₅ a₅`. -/
theorem two_mul_sum_by_order (F : H → ℂ) (a : ℕ → ℂ)
    (hall : ∀ h : H, h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1)
    (hF : ∀ k ∈ ({1, 2, 3, 4} : Finset ℕ), ∀ h, OrdCls h k → F h = a k)
    (h5 : ∀ h, OrdCls h 5 → F h + F (h ^ 2) = a 5) :
    2 * ∑ h, F h = 2 * clsCard H 1 * a 1 + 2 * clsCard H 2 * a 2 + 2 * clsCard H 3 * a 3
      + 2 * clsCard H 4 * a 4 + clsCard H 5 * a 5 := by
  have hsplit : ∀ h : H, F h = (if OrdCls h 1 then F h else 0) + (if OrdCls h 2 then F h else 0)
      + (if OrdCls h 3 then F h else 0) + (if OrdCls h 4 then F h else 0)
      + (if OrdCls h 5 then F h else 0) := by
    intro h
    simp only [OrdCls]
    by_cases e1 : h = 1
    · simp [e1]
    by_cases e2 : h ^ 2 = 1
    · simp [e1, e2]
    by_cases e3 : h ^ 3 = 1
    · simp [e1, e2, e3]
    by_cases e4 : h ^ 4 = 1
    · simp [e1, e2, e3, e4]
    have e5 : h ^ 5 = 1 := by
      rcases hall h with e | e | e | e | e
      · exact absurd e e1
      · exact absurd e e2
      · exact absurd e e3
      · exact absurd e e4
      · exact e
    simp [e1, e2, e3, e4, e5]
  have hcls : ∀ k ∈ ({1, 2, 3, 4} : Finset ℕ),
      ∑ h, (if OrdCls h k then F h else 0) = clsCard H k * a k := by
    intro k hk
    rw [← Finset.sum_filter, Finset.sum_congr rfl (fun h hh => hF k hk h (Finset.mem_filter.mp hh).2),
      Finset.sum_const, nsmul_eq_mul, clsCard]
  have h5sum : 2 * ∑ h, (if OrdCls h 5 then F h else 0) = clsCard H 5 * a 5 := by
    rw [← Finset.sum_filter]
    have hbij : ∑ h ∈ Finset.univ.filter (fun h : H => OrdCls h 5), F (h ^ 2)
        = ∑ h ∈ Finset.univ.filter (fun h : H => OrdCls h 5), F h := by
      refine Finset.sum_nbij' (fun h => h ^ 2) (fun h => h ^ 3) ?_ ?_ ?_ ?_ ?_
      · intro h hh
        rw [Finset.mem_filter] at hh ⊢
        exact ⟨Finset.mem_univ _, ordCls5_sq hh.2⟩
      · intro h hh
        rw [Finset.mem_filter] at hh ⊢
        exact ⟨Finset.mem_univ _, ordCls5_cube hh.2⟩
      · intro h hh
        rw [Finset.mem_filter] at hh
        exact ordCls5_sq_cube hh.2
      · intro h hh
        rw [Finset.mem_filter] at hh
        exact ordCls5_cube_sq hh.2
      · intro h _; rfl
    rw [two_mul]
    nth_rw 2 [← hbij]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun h hh => h5 h (Finset.mem_filter.mp hh).2),
      Finset.sum_const, nsmul_eq_mul, clsCard]
  rw [Finset.sum_congr rfl (fun h _ => hsplit h)]
  simp only [Finset.sum_add_distrib]
  rw [hcls 1 (by decide), hcls 2 (by decide), hcls 3 (by decide), hcls 4 (by decide)]
  linear_combination h5sum

end ClassSum

/-! ## Counting the elements of `A₄`, `S₄`, `A₅` by order -/

section Counts

set_option maxRecDepth 100000 in
theorem A4_all : ∀ h : alternatingGroup (Fin 4), h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem S4_all : ∀ h : Equiv.Perm (Fin 4), h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem A5_all : ∀ h : alternatingGroup (Fin 5), h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1 := by
  decide

set_option maxRecDepth 100000 in
theorem A4_counts : clsCard (alternatingGroup (Fin 4)) 1 = 1 ∧ clsCard (alternatingGroup (Fin 4)) 2 = 3 ∧
    clsCard (alternatingGroup (Fin 4)) 3 = 8 ∧ clsCard (alternatingGroup (Fin 4)) 4 = 0 ∧
    clsCard (alternatingGroup (Fin 4)) 5 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem S4_counts : clsCard (Equiv.Perm (Fin 4)) 1 = 1 ∧ clsCard (Equiv.Perm (Fin 4)) 2 = 9 ∧
    clsCard (Equiv.Perm (Fin 4)) 3 = 8 ∧ clsCard (Equiv.Perm (Fin 4)) 4 = 6 ∧
    clsCard (Equiv.Perm (Fin 4)) 5 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem A5_counts : clsCard (alternatingGroup (Fin 5)) 1 = 1 ∧ clsCard (alternatingGroup (Fin 5)) 2 = 15 ∧
    clsCard (alternatingGroup (Fin 5)) 3 = 20 ∧ clsCard (alternatingGroup (Fin 5)) 4 = 0 ∧
    clsCard (alternatingGroup (Fin 5)) 5 = 24 := by
  decide

set_option maxRecDepth 100000 in
theorem A4_card : Fintype.card (alternatingGroup (Fin 4)) = 12 := by decide
set_option maxRecDepth 100000 in
theorem S4_card : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide
set_option maxRecDepth 100000 in
theorem A5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by decide

end Counts

/-! ## Three partition counts: `p(0) = 1`, `p(7) ≥ 2`, `#{λ ⊢ 4 : ℓ(λ) odd} ≤ 2` -/

section PartitionCounts

open HeisenbergN

/-- The embedding `Fin w × Fin r ↪ ℕ × Fin r`. -/
def finEmb (w r : ℕ) : Fin w × Fin r ↪ ℕ × Fin r :=
  ⟨fun x => (x.1.1, x.2), fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) h.2⟩

theorem support_subset_finEmb {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} (hd : d ∈ weightDegSetN r w) :
    d.support ⊆ Finset.univ.map (finEmb w r) := by
  intro i hi
  have hlt := weightDegSetN_support_lt hd (Finsupp.mem_support_iff.mp hi)
  rw [Finset.mem_map]
  exact ⟨(⟨i.1, hlt⟩, i.2), Finset.mem_univ _, rfl⟩

theorem weight_eq_fin_sum {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} (hd : d ∈ weightDegSetN r w) :
    Finsupp.weight weightFnN d = ∑ x : Fin w × Fin r, d (x.1.1, x.2) * (x.1.1 + 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset d (support_subset_finEmb hd)
    (fun i c => c • weightFnN i) (fun _ _ => zero_smul _ _), Finset.sum_map]
  rfl

theorem degree_eq_fin_sum {r w : ℕ} {d : (ℕ × Fin r) →₀ ℕ} (hd : d ∈ weightDegSetN r w) :
    d.degree = ∑ x : Fin w × Fin r, d (x.1.1, x.2) := by
  rw [Finsupp.degree_apply, Finset.sum_subset (support_subset_finEmb hd)
    (fun i _ hi => Finsupp.notMem_support_iff.mp hi), Finset.sum_map]
  rfl

/-- The exponent vectors of weight `4` with an odd number of oscillators, as functions. -/
def oddFourSet : Finset (Fin 4 × Fin 1 → Fin 5) :=
  Finset.univ.filter fun c => (∑ x, (c x : ℕ) * (x.1.1 + 1)) = 4 ∧ Odd (∑ x, (c x : ℕ))

set_option maxRecDepth 100000 in
theorem oddFourSet_card : oddFourSet.card = 2 := by decide

/-- `#{λ ⊢ 4 : ℓ(λ) odd} ≤ 2` (they are `(4)` and `(2,1,1)`). -/
theorem fockCountOdd_one_four_le : fockCountOdd 1 4 ≤ 2 := by
  classical
  let φ : ((ℕ × Fin 1) →₀ ℕ) → (Fin 4 × Fin 1 → Fin 5) := fun d x => ⟨min (d (x.1.1, x.2)) 4, by omega⟩
  have hφ : ∀ d ∈ weightDegSetN 1 4, ∀ x : Fin 4 × Fin 1, ((φ d x : Fin 5) : ℕ) = d (x.1.1, x.2) := by
    intro d hd x
    have := weightDegSetN_entry_le hd (x.1.1, x.2)
    change min _ _ = _
    omega
  rw [← oddFourSet_card, fockCountOdd, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn φ ?_ ?_ (Finset.finite_toSet _)
  · rintro d ⟨hw, ho⟩
    have hd : d ∈ weightDegSetN 1 4 := hw
    rw [Finset.mem_coe, oddFourSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Finset.sum_congr rfl (fun x _ => by rw [hφ d hd x]), ← weight_eq_fin_sum hd]; exact hw
    · rw [Finset.sum_congr rfl (fun x _ => hφ d hd x), ← degree_eq_fin_sum hd]; exact ho
  · intro d hd e he h
    have hd' : d ∈ weightDegSetN 1 4 := hd.1
    have he' : e ∈ weightDegSetN 1 4 := he.1
    refine Finsupp.ext fun i => ?_
    by_cases hi : i.1 < 4
    · have := congrArg (fun c => ((c (⟨i.1, hi⟩, i.2) : Fin 5) : ℕ)) h
      simp only at this
      rw [hφ d hd', hφ e he'] at this
      exact this
    · have hdz : d i = 0 := by
        by_contra hne; exact hi (weightDegSetN_support_lt hd' hne)
      have hez : e i = 0 := by
        by_contra hne; exact hi (weightDegSetN_support_lt he' hne)
      rw [hdz, hez]

/-- `p(7) ≥ 2` (`(7)` and `(1,…,1)`). -/
theorem two_le_fockCount_one_seven : 2 ≤ fockCount 1 7 := by
  classical
  have h1 : Finsupp.single ((6 : ℕ), (0 : Fin 1)) 1 ∈ weightDegSetN 1 7 := by
    change Finsupp.weight weightFnN _ = 7
    rw [Finsupp.weight_single, weightFnN_apply]; rfl
  have h2 : Finsupp.single ((0 : ℕ), (0 : Fin 1)) 7 ∈ weightDegSetN 1 7 := by
    change Finsupp.weight weightFnN _ = 7
    rw [Finsupp.weight_single, weightFnN_apply]; rfl
  have hne : Finsupp.single ((6 : ℕ), (0 : Fin 1)) 1 ≠ Finsupp.single ((0 : ℕ), (0 : Fin 1)) 7 := by
    intro h
    have := congrArg (fun f => f ((6 : ℕ), (0 : Fin 1))) h
    simp at this
  rw [fockCount, ← Set.ncard_pair hne]
  exact Set.ncard_le_ncard (Set.insert_subset h1 (Set.singleton_subset_iff.mpr h2))
    (weightDegSetN_finite 1 7)

end PartitionCounts

/-! ## The graded dimensions of `V₂^G` at weights `4` and `16` -/

section OrbifoldDims

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

theorem coe_symm_pow_eq_one_iff {H : Type*} [Group H] {G : Subgroup (Aut V1)} (e : G ≃* H) (h : H)
    (k : ℕ) : ((e.symm h : G) : Aut V1) ^ k = 1 ↔ h ^ k = 1 := by
  rw [← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

/-- **The orbifold dimension by element orders.** For `G ≅ H` finite with all orders `≤ 5`,
`2|G| dim (V₂^G)_n = Σ_{k ≤ 4} 2 c_k a_k + c₅ a₅`, where `a_k` is the torus trace `τ_n(u)` at
a `u` of order `k` (for `k = 5`, the sum `τ_n(u) + τ_n(u²)`). -/
theorem two_card_mul_finrank (n : ℕ) (G : Subgroup (Aut V1)) [Fintype G] {H : Type*} [Group H]
    [Fintype H] [DecidableEq H] (e : G ≃* H) (a : ℕ → ℂ)
    (hall : ∀ h : H, h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1)
    (ha1 : torusTrace n 1 = a 1)
    (ha2 : ∀ u : ℂˣ, u ^ 2 = 1 → u ≠ 1 → torusTrace n u = a 2)
    (ha3 : ∀ u : ℂˣ, u ^ 3 = 1 → u ≠ 1 → torusTrace n u = a 3)
    (ha4 : ∀ u : ℂˣ, u ^ 4 = 1 → u ^ 2 ≠ 1 → torusTrace n u = a 4)
    (ha5 : ∀ u : ℂˣ, u ^ 5 = 1 → u ≠ 1 → torusTrace n u + torusTrace n (u ^ 2) = a 5) :
    2 * (Fintype.card G : ℂ) * finrank ℂ ((orbifoldVOA G).grading n)
      = 2 * clsCard H 1 * a 1 + 2 * clsCard H 2 * a 2 + 2 * clsCard H 3 * a 3
        + 2 * clsCard H 4 * a 4 + clsCard H 5 * a 5 := by
  haveI := (V1).finrank (n : ℤ)
  have hsum := card_mul_finrank_orbifold G (n : ℤ)
  have hre : ∑ g : G, LinearMap.trace ℂ _ (autRes V1 n g)
      = ∑ h : H, autTrace n ((e.symm h : G) : Aut V1) :=
    (Fintype.sum_equiv e.symm.toEquiv _ _ (fun h => rfl)).symm
  rw [mul_assoc, hsum, hre]
  refine two_mul_sum_by_order _ a hall ?_ ?_
  · intro k hk h hh
    have hp : ∀ j : ℕ, ((e.symm h : G) : Aut V1) ^ j = 1 ↔ h ^ j = 1 :=
      coe_symm_pow_eq_one_iff e h
    have hne : ∀ j : ℕ, ¬ h ^ j = 1 → ((e.symm h : G) : Aut V1) ^ j ≠ 1 :=
      fun j hj e' => hj ((hp j).mp e')
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · have h1 : h = 1 := hh
      subst h1
      rw [map_one, OneMemClass.coe_one, autTrace_one, ha1]
    · obtain ⟨h1, h2⟩ := hh
      obtain ⟨u, hu, -, hP⟩ := exists_torus_pow (n := n) two_pos ((hp 2).mpr h2)
      rw [hu]
      refine ha2 u ((hP 2).mp ((hp 2).mpr h2)) fun e1 => ?_
      exact h1 (by simpa using (hp 1).mp ((hP 1).mpr (by simpa using e1)))
    · obtain ⟨h2, h3⟩ := hh
      obtain ⟨u, hu, -, hP⟩ := exists_torus_pow (n := n) three_pos ((hp 3).mpr h3)
      rw [hu]
      refine ha3 u ((hP 3).mp ((hp 3).mpr h3)) fun e1 => ?_
      apply h2
      have : ((e.symm h : G) : Aut V1) ^ 1 = 1 := (hP 1).mpr (by simpa using e1)
      rw [pow_one] at this
      rw [← (hp 2), show (2 : ℕ) = 1 + 1 from rfl, pow_add, pow_one, this, one_mul]
    · obtain ⟨h2, -, h4⟩ := hh
      obtain ⟨u, hu, -, hP⟩ := exists_torus_pow (n := n) four_pos ((hp 4).mpr h4)
      rw [hu]
      exact ha4 u ((hP 4).mp ((hp 4).mpr h4)) fun e2 => hne 2 h2 ((hP 2).mpr e2)
  · intro h hh
    obtain ⟨h2, -, -, h5⟩ := hh
    have hp : ∀ j : ℕ, ((e.symm h : G) : Aut V1) ^ j = 1 ↔ h ^ j = 1 :=
      coe_symm_pow_eq_one_iff e h
    obtain ⟨u, hu, hu2, hP⟩ := exists_torus_pow (n := n) (by norm_num : 0 < 5) ((hp 5).mpr h5)
    have hsq : ((e.symm (h ^ 2) : G) : Aut V1) = ((e.symm h : G) : Aut V1) ^ 2 := by
      rw [map_pow, Subgroup.coe_pow]
    rw [hsq, hu, hu2]
    refine ha5 u ((hP 5).mp ((hp 5).mpr h5)) fun e1 => h2 ?_
    have : ((e.symm h : G) : Aut V1) ^ 1 = 1 := (hP 1).mpr (by simpa using e1)
    rw [pow_one] at this
    rw [← hp 2, sq, this, one_mul]

/-- The torus-trace values at weight `4`, indexed by the order of `u`. -/
noncomputable def tv4 : ℕ → ℂ
  | 1 => (1 : ℂ) * Pc 4 + (2 : ℂ) * Pc 3 + (2 : ℂ) * Pc 0
  | 2 => (1 : ℂ) * Pc 4 + (-2 : ℂ) * Pc 3 + (2 : ℂ) * Pc 0
  | 3 => (1 : ℂ) * Pc 4 + (-1 : ℂ) * Pc 3 + (-1 : ℂ) * Pc 0
  | 4 => (1 : ℂ) * Pc 4 + (-2 : ℂ) * Pc 0
  | 5 => (2 : ℂ) * Pc 4 + (-1 : ℂ) * Pc 3 + (-1 : ℂ) * Pc 0
  | _ => 0

/-- The torus-trace values at weight `16`, indexed by the order of `u`. -/
noncomputable def tv16 : ℕ → ℂ
  | 1 => (1 : ℂ) * Pc 16 + (2 : ℂ) * Pc 15 + (2 : ℂ) * Pc 12 + (2 : ℂ) * Pc 7 + (2 : ℂ) * Pc 0
  | 2 => (1 : ℂ) * Pc 16 + (-2 : ℂ) * Pc 15 + (2 : ℂ) * Pc 12 + (-2 : ℂ) * Pc 7 + (2 : ℂ) * Pc 0
  | 3 => (1 : ℂ) * Pc 16 + (-1 : ℂ) * Pc 15 + (-1 : ℂ) * Pc 12 + (2 : ℂ) * Pc 7 + (-1 : ℂ) * Pc 0
  | 4 => (1 : ℂ) * Pc 16 + (-2 : ℂ) * Pc 12 + (2 : ℂ) * Pc 0
  | 5 => (2 : ℂ) * Pc 16 + (-1 : ℂ) * Pc 15 + (-1 : ℂ) * Pc 12 + (-1 : ℂ) * Pc 7 + (-1 : ℂ) * Pc 0
  | _ => 0


theorem two_card_mul_finrank_four (G : Subgroup (Aut V1)) [Fintype G] {H : Type*} [Group H]
    [Fintype H] [DecidableEq H] (e : G ≃* H)
    (hall : ∀ h : H, h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1) :
    2 * (Fintype.card G : ℂ) * finrank ℂ ((orbifoldVOA G).grading (4 : ℕ))
      = 2 * clsCard H 1 * tv4 1 + 2 * clsCard H 2 * tv4 2 + 2 * clsCard H 3 * tv4 3
        + 2 * clsCard H 4 * tv4 4 + clsCard H 5 * tv4 5 :=
  two_card_mul_finrank 4 G e tv4 hall torusTrace4_one (fun _ h2 h1 => torusTrace4_two h2 h1)
    (fun _ h3 h1 => torusTrace4_three h3 h1) (fun _ h4 h2 => torusTrace4_four h4 h2)
    (fun _ h5 h1 => torusTrace4_five h5 h1)

theorem two_card_mul_finrank_sixteen (G : Subgroup (Aut V1)) [Fintype G] {H : Type*} [Group H]
    [Fintype H] [DecidableEq H] (e : G ≃* H)
    (hall : ∀ h : H, h = 1 ∨ h ^ 2 = 1 ∨ h ^ 3 = 1 ∨ h ^ 4 = 1 ∨ h ^ 5 = 1) :
    2 * (Fintype.card G : ℂ) * finrank ℂ ((orbifoldVOA G).grading (16 : ℕ))
      = 2 * clsCard H 1 * tv16 1 + 2 * clsCard H 2 * tv16 2 + 2 * clsCard H 3 * tv16 3
        + 2 * clsCard H 4 * tv16 4 + clsCard H 5 * tv16 5 :=
  two_card_mul_finrank 16 G e tv16 hall torusTrace16_one (fun _ h2 h1 => torusTrace16_two h2 h1)
    (fun _ h3 h1 => torusTrace16_three h3 h1) (fun _ h4 h2 => torusTrace16_four h4 h2)
    (fun _ h5 h1 => torusTrace16_five h5 h1)

/-- **`dim (V₂^G)₄ = p(4) − p(3)` and `dim (V₂^G)₁₆ = p16 - p15 + p7` for `G ≅ A4`.** -/
theorem finrank_orbifold_A4 (G : Subgroup (Aut V1)) (e : G ≃* alternatingGroup (Fin 4)) :
    (finrank ℂ ((orbifoldVOA G).grading (4 : ℕ)) : ℂ) = Pc 4 - Pc 3 ∧
      (finrank ℂ ((orbifoldVOA G).grading (16 : ℕ)) : ℂ) = Pc 16 - Pc 15 + Pc 7 := by
  letI : Fintype G := Fintype.ofEquiv _ e.symm.toEquiv
  have hc : Fintype.card G = 12 := by rw [Fintype.card_congr e.toEquiv]; exact A4_card
  obtain ⟨c1, c2, c3, c4, c5⟩ := A4_counts
  have h4 := two_card_mul_finrank_four G e A4_all
  have h16 := two_card_mul_finrank_sixteen G e A4_all
  rw [hc, c1, c2, c3, c4, c5] at h4 h16
  simp only [tv4, tv16] at h4 h16
  push_cast at h4 h16
  constructor
  · linear_combination h4 / (2 * 12)
  · linear_combination h16 / (2 * 12)

/-- **`dim (V₂^G)₄ = p(4) − p(3)` and `dim (V₂^G)₁₆ = p16 - p15 + p0` for `G ≅ S4`.** -/
theorem finrank_orbifold_S4 (G : Subgroup (Aut V1)) (e : G ≃* Equiv.Perm (Fin 4)) :
    (finrank ℂ ((orbifoldVOA G).grading (4 : ℕ)) : ℂ) = Pc 4 - Pc 3 ∧
      (finrank ℂ ((orbifoldVOA G).grading (16 : ℕ)) : ℂ) = Pc 16 - Pc 15 + Pc 0 := by
  letI : Fintype G := Fintype.ofEquiv _ e.symm.toEquiv
  have hc : Fintype.card G = 24 := by rw [Fintype.card_congr e.toEquiv]; exact S4_card
  obtain ⟨c1, c2, c3, c4, c5⟩ := S4_counts
  have h4 := two_card_mul_finrank_four G e S4_all
  have h16 := two_card_mul_finrank_sixteen G e S4_all
  rw [hc, c1, c2, c3, c4, c5] at h4 h16
  simp only [tv4, tv16] at h4 h16
  push_cast at h4 h16
  constructor
  · linear_combination h4 / (2 * 24)
  · linear_combination h16 / (2 * 24)

/-- **`dim (V₂^G)₄ = p(4) − p(3)` and `dim (V₂^G)₁₆ = p16 - p15` for `G ≅ A5`.** -/
theorem finrank_orbifold_A5 (G : Subgroup (Aut V1)) (e : G ≃* alternatingGroup (Fin 5)) :
    (finrank ℂ ((orbifoldVOA G).grading (4 : ℕ)) : ℂ) = Pc 4 - Pc 3 ∧
      (finrank ℂ ((orbifoldVOA G).grading (16 : ℕ)) : ℂ) = Pc 16 - Pc 15 := by
  letI : Fintype G := Fintype.ofEquiv _ e.symm.toEquiv
  have hc : Fintype.card G = 60 := by rw [Fintype.card_congr e.toEquiv]; exact A5_card
  obtain ⟨c1, c2, c3, c4, c5⟩ := A5_counts
  have h4 := two_card_mul_finrank_four G e A5_all
  have h16 := two_card_mul_finrank_sixteen G e A5_all
  rw [hc, c1, c2, c3, c4, c5] at h4 h16
  simp only [tv4, tv16] at h4 h16
  push_cast at h4 h16
  constructor
  · linear_combination h4 / (2 * 60)
  · linear_combination h16 / (2 * 60)

end OrbifoldDims

/-! ## The residuals -/

section Residuals

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- The label-dependent part of `dim (V₂^G)₁₆`: `p(7)`, `p(0)`, `0` for `A₄`, `S₄`, `A₅`. -/
noncomputable def exc16 : COneLabel → ℂ
  | .tetra => Pc 7
  | .octa => Pc 0
  | .icosa => 0
  | .lat _ => 0
  | .plus _ => 0

/-- **The exceptional orbifolds at weights `4` and `16`:** `dim V₄ = p(4) − p(3)` and
`dim V₁₆ = p(16) − p(15) + {p(7), p(0), 0}`. -/
theorem exceptional_finrank {l : COneLabel} (hl : l.IsExceptional) (h : HasCOneLabel V l) :
    (finrank ℂ (V.grading (4 : ℕ)) : ℂ) = Pc 4 - Pc 3 ∧
      (finrank ℂ (V.grading (16 : ℕ)) : ℂ) = Pc 16 - Pc 15 + exc16 l := by
  cases l with
  | tetra =>
    obtain ⟨G, ⟨e⟩, hV⟩ := h
    rw [finrank_grading_eq_of_iso hV, finrank_grading_eq_of_iso hV]
    exact finrank_orbifold_A4 G e
  | octa =>
    obtain ⟨G, ⟨e⟩, hV⟩ := h
    rw [finrank_grading_eq_of_iso hV, finrank_grading_eq_of_iso hV]
    exact finrank_orbifold_S4 G e
  | icosa =>
    obtain ⟨G, ⟨e⟩, hV⟩ := h
    rw [finrank_grading_eq_of_iso hV, finrank_grading_eq_of_iso hV, exc16, add_zero]
    exact finrank_orbifold_A5 G e
  | lat _ => exact hl.elim
  | plus _ => exact hl.elim

/-- **Residual 1, proved.** No `V_{2m}⁺` (`m ≥ 4`) is an exceptional orbifold:
`dim (V_{2m}⁺)₄ = #{λ ⊢ 4 : ℓ(λ) even} + [m = 4]`, while `dim (V₂^G)₄ = p(4) − p(3)`; equality
would force `#{λ ⊢ 4 : ℓ(λ) odd} ≥ 3`. -/
theorem plusExceptionalResidual : PlusExceptionalResidual.{u} := by
  intro 𝒱 _ _ V m l hm4 hl hplus hl'
  obtain ⟨hm, -, e⟩ := hplus
  have horb := (exceptional_finrank hl hl').1
  rw [finrank_grading_eq_of_iso e] at horb
  have horbZ : (finrank ℂ ((V2mPlus m hm).grading ((4 : ℕ) : ℤ)) : ℤ)
      = (fockCount 1 4 : ℤ) - fockCount 1 3 := by
    exact_mod_cast horb
  have hplusZ := V2mPlus_two_mul m hm 4
  have hlat : (finrank ℂ ((V2m m hm).grading ((4 : ℕ) : ℤ)) : ℤ) = fockCount 1 4 ∨
      (finrank ℂ ((V2m m hm).grading ((4 : ℕ) : ℤ)) : ℤ) = fockCount 1 4 + 2 := by
    rcases Nat.lt_or_ge 4 m with h | h
    · left; rw [V2m_finrank_lt m hm 4 h]
    · right
      obtain rfl : m = 4 := le_antisymm h hm4
      have := V2m_finrank_self 4 hm
      push_cast at this ⊢
      omega
  have hs := fockSigned_eq 1 4
  have hp := fockCount_eq_even_add_odd 1 4
  have h3 : fockCount 1 3 = 3 := by rw [fockCount_three]; rfl
  have ho := fockCountOdd_one_four_le
  rw [hs] at hplusZ
  rw [h3] at horbZ
  push_cast at horbZ hplusZ hlat
  omega

/-- **Residual 2, proved.** `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}` are pairwise non-isomorphic: at
weight `16` their dimensions are `p(16) − p(15) + p(7)`, `… + p(0)`, `… + 0`, and
`p(7) ≥ 2 > p(0) = 1 > 0`. -/
theorem exceptionalResidual : ExceptionalResidual.{u} := by
  intro 𝒱 _ _ V l l' hl hl' h h'
  have e1 := (exceptional_finrank hl h).2
  have e2 := (exceptional_finrank hl' h').2
  have heq : exc16 l = exc16 l' := by
    have := e1.symm.trans e2
    linear_combination this
  have h7 := two_le_fockCount_one_seven
  have h0 : fockCount 1 0 = 1 := fockCount_zero 1
  cases l <;> cases l' <;> simp only [exc16, Pc] at heq hl hl' ⊢ <;> norm_cast at heq <;> omega

/-- **Gannon–Rayhaun "pairwise non-isomorphic", unconditional.** A VOA carries at most one
label of the list of Theorem 3.1. -/
theorem gannonRayhaunDistinct : GannonRayhaunDistinct.{u} :=
  gannonRayhaunDistinct_of_residuals plusExceptionalResidual exceptionalResidual

end Residuals

end VOA.Classification.COne
