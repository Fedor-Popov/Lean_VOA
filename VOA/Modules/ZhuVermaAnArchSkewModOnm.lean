/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchSkewGradingGen
import VOA.Modules.ZhuVermaAnArchAnm
import VOA.Core.InvariantFormPStep

/-!
# Skew symmetry **modulo the Dong–Jiang ideal** `O'_{N,m}`

This is the relation Dong–Jiang use (verbatim, in the proof of their Lemma 2.3) as

  `Y(v,z)u ≡ (1+z)^{−wt u−wt v−2m+p₁+p₂} Y(u, −z/(1+z)) v   (mod O'_{p₁+p₂−m,m}(V))`,

and which the repo has never had at **any** level (not even Zhu's level-0 `A(V)` ancestor).  It is
proved here **without ever building the Möbius substitution `z ↦ −z/(1+z)`** — following the repo's
house style of replacing a rational-function identity by its mode/`cbz` coefficients.

## The mechanism

Two ingredients suffice.

1. **VOA skew symmetry in mode form** (`smul_eq_skew_Lpow`, itself from `Core/SkewSymmetry.skew`):
   `v₍t₎u = ∑ⱼ (j!)⁻¹ · sgn(−t−1−j) · L₋₁ʲ (u₍t+j₎v)`.

2. **The `L₋₁`-tower collapses modulo `O'_{N,m}`** (`Lneg1_pow_mod_Onm`, new here).  The Dong–Jiang
   grading generator `anmLgen W N m w = L₋₁w + L₀w + (m−N)w` lies in `O'_{N,m}`, so on homogeneous
   `w` of weight `d`, `L₋₁w ≡ −(d+m−N)·w`.  Iterating — peeling the *innermost* `L₋₁`, so that each
   step is an exact `anmLgen` membership and only *scalars* ever multiply a congruence — gives

     `L₋₁ᵏ w ≡ djTowerScalar (d+m−N) k · w`,  `djTowerScalar c k = (−1)ᵏ ∏_{j<k}(c+j)`.

   (No `L₋₁`-stability of `O'` is needed — and indeed none holds: `L₋₁(anmLgen w) ≡ (d+m−N)·w`.)

Composing the two and collapsing the scalars — the rising product `∏_{j<k}(c+j)` at
`c = d+m−N = E−k+1` is exactly `k!·C(E, k)` with `E = wt u + wt v − 2 + m − N − t` — yields the
headline

  `skew_mod_Onm` :  `v₍t₎u ≡ sgn(t+1) · ∑ⱼ C(E, j) · u₍t+j₎v   (mod O'_{N,m})`,

the mode form of DJ's displayed skew relation.  The whole `−z/(1+z)` contour move is absorbed into
the single generalized binomial `C(E, j)`.

## Engine verification (verify-first)

The coefficient form of DJ Lemma 2.3 that this yields was checked symbolically *before* formalizing:
`0` failures over `0 ≤ wt u, wt v ≤ 4`, `0 ≤ m, p₁, p₂ ≤ 3`, `−3 ≤ ℓ ≤ 8`, with the tower exponent
`E = wt u + wt v − 2 + m − N − t` (an earlier off-by-one `… − 1 …` fails, which is how the correct
exponent was pinned).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.3 and its skew step); Zhu, J. Amer. Math. Soc. 9 (1996)
Lemma 2.1.3 (the level-0 ancestor, `N = m = 0`); `Core/SkewSymmetry` (`skew`, `skew_mode`),
`ZhuVermaAnArchSkewGradingGen` (`smul_eq_skew_Lpow`), `ZhuVermaAnArchAnm` (`anmLgen`,
`anmLgen_mem_Onm`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `L₋₁`-tower scalar. -/

/-- **The `L₋₁`-tower scalar** `(−1)ᵏ · c(c+1)⋯(c+k−1)`: the value of `L₋₁ᵏ` on a homogeneous vector
modulo `O'_{N,m}`, at `c = wt w + m − N`. -/
noncomputable def djTowerScalar (c : ℤ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * ∏ j ∈ Finset.range k, ((c : ℂ) + (j : ℂ))

@[simp] theorem djTowerScalar_zero (c : ℤ) : djTowerScalar c 0 = 1 := by
  simp [djTowerScalar]

/-- The tower scalar peels from the **inside**: `t_{k+1}(c) = −c · t_k(c+1)`. -/
theorem djTowerScalar_succ (c : ℤ) (k : ℕ) :
    djTowerScalar c (k + 1) = -(c : ℂ) * djTowerScalar (c + 1) k := by
  have hprod : ∏ j ∈ Finset.range (k + 1), ((c : ℂ) + (j : ℂ))
      = (∏ j ∈ Finset.range k, (((c + 1 : ℤ) : ℂ) + (j : ℂ))) * ((c : ℂ) + ((0 : ℕ) : ℂ)) := by
    rw [Finset.prod_range_succ']
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [djTowerScalar, djTowerScalar, hprod, pow_succ]
  push_cast
  ring

/-! ## The `L₋₁`-tower collapses modulo `O'_{N,m}`. -/

/-- **The Dong–Jiang grading relation**: on homogeneous `w` of weight `d`,
`L₋₁w + (d+m−N)·w = anmLgen W N m w ∈ O'_{N,m}`. -/
theorem Lneg1_grading_mem_Onm (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) {d : ℤ} {w : 𝒱}
    (hw : w ∈ W.grading d) :
    W.L (-1) w + ((d : ℂ) + (m : ℂ) - (N : ℂ)) • w ∈ Onm W N m := by
  have hL0 : W.L 0 w = (d : ℂ) • w := W.L0_grading w hw
  have h := anmLgen_mem_Onm W N m w
  rw [anmLgen, hL0] at h
  have hEq : W.L (-1) w + (d : ℂ) • w + ((m : ℂ) - (N : ℂ)) • w
      = W.L (-1) w + ((d : ℂ) + (m : ℂ) - (N : ℂ)) • w := by
    rw [add_assoc, ← add_smul]
    congr 2
    ring
  rwa [hEq] at h

/-- **The `L₋₁`-tower collapses modulo `O'_{N,m}`**: for homogeneous `w` of weight `d`,
`L₋₁ᵏ w ≡ djTowerScalar (d+m−N) k · w`.

The induction peels the *innermost* `L₋₁`: `L₋₁^{k+1}w = L₋₁ᵏ(L₋₁w)`, and the induction hypothesis
(stated for *all* homogeneous vectors) applies to `L₋₁w ∈ 𝒱_{d+1}`.  Only *scalars* ever multiply a
congruence, so no `O'`-stability under `L₋₁` is required. -/
theorem Lneg1_pow_mod_Onm (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) :
    ∀ (k : ℕ) {d : ℤ} {w : 𝒱}, w ∈ W.grading d →
      (W.L (-1) ^ k) w - djTowerScalar (d + (m : ℤ) - (N : ℤ)) k • w ∈ Onm W N m := by
  intro k
  induction k with
  | zero =>
    intro d w _
    have h0 : (W.L (-1) ^ 0) w = w := by simp
    rw [h0, djTowerScalar_zero, one_smul, sub_self]
    exact (Onm W N m).zero_mem
  | succ k ih =>
    intro d w hw
    have hLw : W.L (-1) w ∈ W.grading (d + 1) := W.L_neg_one_raise hw
    have h₁ : (W.L (-1) ^ k) (W.L (-1) w)
        - djTowerScalar ((d + 1) + (m : ℤ) - (N : ℤ)) k • (W.L (-1) w) ∈ Onm W N m := ih hLw
    have h₂ : djTowerScalar ((d + 1) + (m : ℤ) - (N : ℤ)) k •
        (W.L (-1) w + ((d : ℂ) + (m : ℂ) - (N : ℂ)) • w) ∈ Onm W N m :=
      Submodule.smul_mem _ _ (Lneg1_grading_mem_Onm W N m hw)
    have hsum := (Onm W N m).add_mem h₁ h₂
    have hcast : ((d + (m : ℤ) - (N : ℤ) : ℤ) : ℂ) = (d : ℂ) + (m : ℂ) - (N : ℂ) := by
      push_cast; ring
    have hshift : ((d + 1) + (m : ℤ) - (N : ℤ)) = (d + (m : ℤ) - (N : ℤ)) + 1 := by ring
    have hscal : djTowerScalar (d + (m : ℤ) - (N : ℤ)) (k + 1)
        = -((d : ℂ) + (m : ℂ) - (N : ℂ)) * djTowerScalar ((d + 1) + (m : ℤ) - (N : ℤ)) k := by
      rw [hshift, djTowerScalar_succ, hcast]
    have hpow : (W.L (-1) ^ (k + 1)) w = (W.L (-1) ^ k) (W.L (-1) w) := by
      rw [pow_succ]; rfl
    have hrw : (W.L (-1) ^ k) (W.L (-1) w)
          - djTowerScalar ((d + 1) + (m : ℤ) - (N : ℤ)) k • (W.L (-1) w)
        + djTowerScalar ((d + 1) + (m : ℤ) - (N : ℤ)) k •
            (W.L (-1) w + ((d : ℂ) + (m : ℂ) - (N : ℂ)) • w)
      = (W.L (-1) ^ (k + 1)) w - djTowerScalar (d + (m : ℤ) - (N : ℤ)) (k + 1) • w := by
      rw [hscal, hpow, smul_add, smul_smul]
      module
    rwa [hrw] at hsum

/-! ## Sign bookkeeping. -/

theorem sgn_neg' (n : ℤ) : sgn (-n) = sgn n := by
  unfold sgn
  by_cases h : Even n
  · rw [if_pos h.neg, if_pos h]
  · rw [if_neg (fun hc => h (by simpa using hc.neg)), if_neg h]

theorem sgn_add_natCast (n : ℤ) (j : ℕ) : sgn (n + (j : ℤ)) = sgn n * (-1 : ℂ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show (n + ((j + 1 : ℕ) : ℤ)) = (n + (j : ℤ)) + 1 from by push_cast; ring, sgn_succ, ih,
      pow_succ]
    ring

/-! ## The rising product is a generalized binomial. -/

/-- `djTowerScalar (n − k + 1) k = (−1)ᵏ · k! · C(n,k)`: the rising factorial based at `n−k+1` is
the falling factorial at `n`, reindexed by `j ↦ k−1−j`. -/
theorem djTowerScalar_shift_eq (n : ℤ) (k : ℕ) :
    djTowerScalar (n - (k : ℤ) + 1) k = (-1 : ℂ) ^ k * (k.factorial : ℂ) * cbz n (k : ℤ) := by
  have hprod : ∏ j ∈ Finset.range k, (((n - (k : ℤ) + 1 : ℤ) : ℂ) + (j : ℂ))
      = ∏ j ∈ Finset.range k, ((n : ℂ) - (j : ℂ)) := by
    rw [← Finset.prod_range_reflect (fun j => ((n : ℂ) - (j : ℂ))) k]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have h1 : (1 : ℕ) ≤ k := by omega
    have hjk : (j : ℕ) ≤ k - 1 := by omega
    have hcast : ((k - 1 - j : ℕ) : ℂ) = (k : ℂ) - 1 - (j : ℂ) := by
      rw [Nat.cast_sub hjk, Nat.cast_sub h1]
      push_cast; ring
    rw [hcast]
    push_cast; ring
  have hcbz : cbz n (k : ℤ) = gBinom n k := by
    rw [cbz, if_pos (Int.natCast_nonneg k), Int.toNat_natCast]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [djTowerScalar, hprod, hcbz, gBinom]
  field_simp

/-! ## Finsum membership in a submodule. -/

theorem finsum_mem_submodule_dj {ι : Type*} {p : Submodule ℂ 𝒱} (f : ι → 𝒱)
    (h : ∀ i, f i ∈ p) : (∑ᶠ i, f i) ∈ p := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact Submodule.sum_mem _ (fun i _ => h i)
  · rw [finsum_of_infinite_support hs]
    exact p.zero_mem

/-! ## The headline: skew symmetry modulo `O'_{N,m}`. -/

/-- A family indexed by `j : ℕ` that is a scalar multiple of `u₍t+j₎v` has finite support. -/
theorem skewFamily_support_finite (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (t : ℤ)
    (c : ℕ → ℂ) (F : ℕ → 𝒱 → 𝒱) (hF : ∀ j, F j 0 = 0) :
    (Function.support fun j : ℕ => c j • F j (W.smul u (t + (j : ℤ)) v)).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero u v
  refine Set.Finite.subset (Set.finite_Iio (Nz - t).toNat) ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hj (by rw [hNz (t + (j : ℤ)) (by omega), hF j, smul_zero])

/-- **Skew symmetry modulo the Dong–Jiang ideal `O'_{N,m}`** — the mode form of
`Y(v,z)u ≡ (1+z)^{…} Y(u, −z/(1+z)) v`:

  `v₍t₎u ≡ sgn(t+1) · ∑ⱼ C(E, j) · u₍t+j₎v   (mod O'_{N,m})`,  `E = wt u + wt v − 2 + m − N − t`.

This is the ingredient Dong–Jiang's Lemma 2.3 rests on, and (at `N = m = 0`) Zhu's Lemma 2.1.3.
Proved from the proved VOA skew symmetry `smul_eq_skew_Lpow` together with the `L₋₁`-tower collapse
`Lneg1_pow_mod_Onm`; **no Möbius substitution is used**. -/
theorem skew_mod_Onm (W : VertexOperatorAlgebra 𝒱) (N m : ℕ) {K M : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading K) (hv : v ∈ W.grading M) (t : ℤ) :
    W.smul v t u
        - sgn (t + 1) •
            ∑ᶠ j : ℕ, cbz (K + M - 2 + (m : ℤ) - (N : ℤ) - t) (j : ℤ) • W.smul u (t + (j : ℤ)) v
      ∈ Onm W N m := by
  set E : ℤ := K + M - 2 + (m : ℤ) - (N : ℤ) - t with hEdef
  -- per-index congruence
  have hterm : ∀ j : ℕ,
      ((j.factorial : ℂ)⁻¹) • (sgn (-t - 1 - (j : ℤ))) • ((W.L (-1) ^ j) (W.smul u (t + (j : ℤ)) v))
        - (sgn (t + 1) * cbz E (j : ℤ)) • W.smul u (t + (j : ℤ)) v ∈ Onm W N m := by
    intro j
    have hgr : W.smul u (t + (j : ℤ)) v ∈ W.grading (K + M - (t + (j : ℤ)) - 1) := by
      rw [PreVertexAlgebra.smul_def]
      exact W.grading_mode u hu v hv (t + (j : ℤ))
    have htow := Lneg1_pow_mod_Onm W N m j hgr
    have hscaled := Submodule.smul_mem (Onm W N m)
      (((j.factorial : ℂ)⁻¹) * sgn (-t - 1 - (j : ℤ))) htow
    -- identify the two scalars
    have hidx : (K + M - (t + (j : ℤ)) - 1) + (m : ℤ) - (N : ℤ) = E - (j : ℤ) + 1 := by
      rw [hEdef]; ring
    have hsgn : sgn (-t - 1 - (j : ℤ)) = sgn (t + 1) * (-1 : ℂ) ^ j := by
      rw [show (-t - 1 - (j : ℤ)) = -((t + 1) + (j : ℤ)) from by ring, sgn_neg', sgn_add_natCast]
    have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hscal : ((j.factorial : ℂ)⁻¹ * sgn (-t - 1 - (j : ℤ)))
        * djTowerScalar ((K + M - (t + (j : ℤ)) - 1) + (m : ℤ) - (N : ℤ)) j
      = sgn (t + 1) * cbz E (j : ℤ) := by
      have h2 : (((-1 : ℂ)) ^ j) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hidx, djTowerScalar_shift_eq, hsgn]
      field_simp
      rw [h2]
      ring
    rw [smul_sub, smul_smul, hscal] at hscaled
    rw [smul_smul]
    exact hscaled
  -- assemble the two finsums
  have hF1 : (Function.support fun j : ℕ =>
      ((j.factorial : ℂ)⁻¹ * sgn (-t - 1 - (j : ℤ))) •
        ((W.L (-1) ^ j) (W.smul u (t + (j : ℤ)) v))).Finite :=
    skewFamily_support_finite W u v t _ (fun j x => (W.L (-1) ^ j) x) (fun j => map_zero _)
  have hF2 : (Function.support fun j : ℕ =>
      (sgn (t + 1) * cbz E (j : ℤ)) • W.smul u (t + (j : ℤ)) v).Finite :=
    skewFamily_support_finite W u v t _ (fun _ x => x) (fun _ => rfl)
  have hLHS : W.smul v t u
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹ * sgn (-t - 1 - (j : ℤ))) •
          ((W.L (-1) ^ j) (W.smul u (t + (j : ℤ)) v)) := by
    rw [smul_eq_skew_Lpow W v u t]
    exact finsum_congr fun j => by rw [smul_smul]
  have hF0 : (Function.support fun j : ℕ => cbz E (j : ℤ) • W.smul u (t + (j : ℤ)) v).Finite :=
    skewFamily_support_finite W u v t _ (fun _ x => x) (fun _ => rfl)
  have hRHS : sgn (t + 1) • ∑ᶠ j : ℕ, cbz E (j : ℤ) • W.smul u (t + (j : ℤ)) v
      = ∑ᶠ j : ℕ, (sgn (t + 1) * cbz E (j : ℤ)) • W.smul u (t + (j : ℤ)) v := by
    rw [smul_finsum' (sgn (t + 1)) hF0]
    exact finsum_congr fun j => by rw [smul_smul]
  rw [hLHS, hRHS, ← finsum_sub_distrib hF1 hF2]
  refine finsum_mem_submodule_dj _ (fun j => ?_)
  have := hterm j
  rwa [smul_smul] at this

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.Lneg1_pow_mod_Onm
  #print axioms VOA.djTowerScalar_shift_eq
  #print axioms VOA.skew_mod_Onm
-/
