/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletW2Log
import VOA.Modules.ZhuVermaAnArchDLM3AdjointBottom

/-!
# Towards `A(W(2))`: the Zhu algebra of the triplet at `c = -2`

`Examples/TripletW2Log.lean` reduces the existence of a genuine logarithmic `W(2)`-module to a
single Zhu-algebra statement,

  `OmegaJordanAt tripletW2 h`  :  `[ω] − h ∉ A(W(2)) · ([ω] − h)²` ,

and discharges nothing about it.  This file attacks that statement head on.  It does **not**
close it.  What it does deliver is (i) the general Zhu-product calculus one needs to compute in
`A(𝒱)` at all, (ii) an exact reformulation of the blocker as a *representation-theoretic*
statement, which is the form in which it is actually tractable, and (iii) the `W(2)`
specialisations, including the fact that `A(W(2))` is not the zero algebra.

## §1 The Zhu product on a homogeneous left factor

`zhuMul` is defined through `DirectSum.decompose`, which makes it opaque.  `zhuMul_of_mem_grading`
collapses it on a homogeneous `u ∈ 𝒱_k` to the honest finite sum

  `u * v = ∑_{m=0}^{k} C(k,m) · u₍ₘ₋₁₎ v` .

Everything downstream is an instance of this.

## §2 `O(𝒱)` contains the `L`-generators, and `[L₋₁ v] = −k·[v]`

Taking `v = 𝟙` in Gannon's generating set `{(L₋₁u + L₀u) * v}` and using the right unit law gives
`L₋₁u + L₀u ∈ O(𝒱)` (`Lgen_mem_O`), hence in `A(𝒱)`

  `[L₋₁ u] = −[L₀ u]`,   and   `[L₋₁ u] = −k·[u]` for `u ∈ 𝒱_k`

(`mk_L_neg_one`, `mk_L_neg_one_of_mem_grading`).  This is the one relation in `A(𝒱)` that is
available with no input beyond the axioms, and it is what makes the weight grading visible in the
Zhu algebra.

## §3 Left multiplication by `[ω]`

`ω ∈ 𝒱₂`, so §1 gives `ω * v = ω₍₋₁₎v + 2·L₋₁v + L₀v` (`zhuMul_conformalVector`), and §2 collapses
the last two terms:

  `[ω]·[v] = [ω₍₋₁₎ v] − k·[v]`    for `v ∈ 𝒱_k`   (`Amul_omega_mk`),
  `([ω] − h)·[v] = [ω₍₋₁₎ v] − (k + h)·[v]`          (`Amul_omegaShift_mk`),
  `[ω]² = [ω₍₋₁₎ ω] − 2·[ω]`                          (`omega_sq`).

So the multiplication by the central element `[ω]` is completely explicit in terms of the
*normally ordered* product `v ↦ ω₍₋₁₎v` and the conformal weight.  These hold in every VOA.

## §4 The blocker, reformulated: a two-dimensional non-semisimple module

The crux `OmegaJordanAt 𝒱 h` is a non-membership statement in `A(𝒱)`, which is hard to attack
directly because `A(𝒱)` is a quotient by a span.  `omegaJordanAt_iff_exists_amod` turns it into an
*existence* statement:

  `OmegaJordanAt 𝒱 h`  ↔  `∃ U : AMod 𝒱`, `ρ([ω] − h)² = 0` and `ρ([ω] − h) ≠ 0` .

The `←` direction is the useful one and is elementary (`omegaJordanAt_of_amod`): the ideal
`A(𝒱)([ω]−h)²` is annihilated by any such `U`, while `[ω]−h` is not.  The `→` direction is free
from `TripletW2Log`'s `omegaJordanAMod`.  Together with `TripletW2Log` this says precisely:

  **a logarithmic `W(2)`-module exists (by the Dong–Jiang route) if and only if `A(W(2))` has a
  module on which `[ω] − h` is a nonzero square-zero operator** — i.e. exactly the "staggered"
  two-dimensional `A(𝒱)`-module of the physics literature.

`omegaJordanAt_of_functional` / `omegaJordanAt_of_functional_V` give the weaker linear-functional
form of the same sufficient condition: a single linear functional on `𝒱` killing `O(𝒱)` and
killing `𝒱 * (ω_h * ω_h)`, but not `ω_h := ω − h·𝟙`, already suffices.  This is the cheapest
possible certificate and is stated at the level of `𝒱` so that a future computation in the
symplectic-fermion Fock space can feed it directly.

## §5 Necessary conditions, `A(W(2)) ≠ 0`, and where `h` must be

`A(𝒱)` could a priori be the zero ring, in which case `OmegaJordanAt` fails for every `h` and the
whole programme is vacuous.  It is not: the weight-`0` space of the adjoint module is `𝒱₀ = ℂ𝟙`,
which is nonzero for `W(2)`, and `[𝟙]` acts on it as the identity, so

  `one_ne_zero`, `tripletW2_one_ne_zero` : `[𝟙] ≠ 0` in `A(W(2))`, i.e. `O(W(2)) ≠ W(2)`.

Two further facts pin down where to look.  First, `0` lies in every left ideal, so

  `omegaShift_ne_zero_of_omegaJordanAt` : `OmegaJordanAt 𝒱 h ⟹ [ω] − h ≠ 0`,

which at `h = 0` reads `mk_conformalVector_ne_zero_of_omegaJordanAt` : `[ω] ≠ 0` in `A(𝒱)`.
That is a *strictly smaller* open target than the blocker itself, and it too is undecided here.
Second, on the adjoint bottom `𝒱₀` the zero mode of `ω` is `L₀`, which vanishes there:

  `adjointBottom_rho_conformalVector` : `ρ([ω]) = 0` on the nonzero `A(W(2))`-module `W(2)₀`.

So `h = 0` is genuinely an eigenvalue of the central element `[ω]` on a nonzero module — the only
value of `h` at which this route can produce the vacuum-block Jordan cell.  (The adjoint bottom
itself is *not* a certificate: there `ρ([ω] − h) = −h`, which is either zero, or nonzero with
nonzero square.)

Also recorded: `tripletW2_mk_L_neg_one_omega` (`[L₋₁ω] = −2[ω]`) and `tripletW2_omega_sq`.

## ⚠ What is NOT proved here — the precise remaining gap

`OmegaJordanAt tripletW2 h` is **not** proved for any `h`.  What would close it, in decreasing
order of strength:

1. an explicit presentation of `A(W(2))` — in the literature (Adamović–Milas, *On the triplet
   vertex algebra `W(p)`*, Adv. Math. 217 (2008); Gaberdiel–Kausch) `A(W(p))` is finite
   dimensional with `[ω]` non-semisimple at the vacuum eigenvalue.  **This repository contains no
   copy of that reference** (`refs/` holds only Dong–Jiang and Dong–Li–Mason), so the precise
   dimension and the precise `h` are *asserted in the literature, not verified here*, and nothing
   below depends on them;
2. a bundled `AMod tripletW2` with `ρ([ω]−h)² = 0 ≠ ρ([ω]−h)` — by §4 this is *equivalent*;
3. a linear functional certificate as in §4.

Route 2 needs the genuine staggered module; route 3 needs enough of `O(W(2))` to know a functional
is well defined.  Both require a computation inside the symplectic-fermion Fock space that is not
attempted here.  Nothing in this file is `sorry`-ed, axiomatised, or asserted without proof.

## References
Zhu, *Modular invariance …*, J. AMS 9 (1996), §2; Gannon §5.3.2, eqs. (5.3.8)–(5.3.10);
Dong–Jiang `math/0601626`; Adamović–Milas, Adv. Math. 217 (2008) (for the shape of `A(W(p))`,
**not** verified here); repo cross-refs `Modules.ZhuAlgebra`, `Modules.ZhuRing`,
`Examples.TripletW2`, `Examples.TripletW2Log`.
-/

namespace VOA.ZhuW2

open VOA
open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 The Zhu product on a homogeneous left factor -/

/-- **The Zhu product collapses on a homogeneous left factor**: for `u ∈ 𝒱_k`,
`u * v = ∑_{m=0}^{k} C(k,m) u₍ₘ₋₁₎ v` (Gannon 5.3.8a).  `zhuMul` is defined through
`DirectSum.decompose`; this is the lemma that makes it computable. -/
theorem zhuMul_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) (v : 𝒱) :
    zhuMul W u v = ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • W.smul u ((m : ℤ) - 1) v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : zhuMul W u v = zhuFamily W v k ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (zhuFamily W v)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (zhuFamily W v) k ⟨u, hu⟩
  rw [hcollapse]
  rfl

/-! ## §2 `O(𝒱)` contains the `L`-generators -/

/-- **`L₋₁u + L₀u ∈ O(𝒱)`**: take `v = 𝟙` in Gannon's generating set `{(L₋₁u+L₀u)*v}` and use the
right unit law `w * 𝟙 = w`. -/
theorem Lgen_mem_O (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    W.L (-1) u + W.L 0 u ∈ O W :=
  Submodule.subset_span ⟨u, W.vacuum, (zhuMul_vacuum_right W (W.L (-1) u + W.L 0 u)).symm⟩

/-- `[L₋₁u + L₀u] = 0` in `A(𝒱)`. -/
theorem mk_Lgen (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    mk W (W.L (-1) u + W.L 0 u) = 0 :=
  (mk_eq_zero_iff W).mpr (Lgen_mem_O W u)

/-- **`[L₋₁u] = −[L₀u]`** in `A(𝒱)`. -/
theorem mk_L_neg_one (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    mk W (W.L (-1) u) = - mk W (W.L 0 u) := by
  have h := mk_Lgen W u
  rw [map_add] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **`[L₀u] = k·[u]`** for `u ∈ 𝒱_k`. -/
theorem mk_L_zero_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) :
    mk W (W.L 0 u) = (k : ℂ) • mk W u := by
  rw [W.L_zero_grading u hu, map_smul]

/-- **`[L₋₁u] = −k·[u]`** for `u ∈ 𝒱_k`: the translation generator acts on `A(𝒱)` by minus the
conformal weight. -/
theorem mk_L_neg_one_of_mem_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) :
    mk W (W.L (-1) u) = (-(k : ℂ)) • mk W u := by
  rw [mk_L_neg_one, mk_L_zero_of_mem_grading W hu, neg_smul]

/-! ## §3 Left multiplication by the conformal vector -/

private theorem cbz_two_one : cbz (2 : ℤ) 1 = 2 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num), show ((1 : ℤ)).toNat = 1 from rfl, gBinom]
  norm_num [Finset.prod_range_one]

private theorem cbz_two_two : cbz (2 : ℤ) 2 = 1 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num), show ((2 : ℤ)).toNat = 2 from rfl, gBinom]
  norm_num [Finset.prod_range_succ, Finset.prod_range_one]

private theorem sum_range_three {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ Finset.range 3, f m = f 0 + f 1 + f 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

/-- `ω₍₀₎v = L₋₁v`. -/
theorem smul_conformalVector_zero (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    W.smul W.conformalVector (0 : ℤ) v = W.L (-1) v := by
  rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = (0 : ℤ) by ring]

/-- `ω₍₁₎v = L₀v`. -/
theorem smul_conformalVector_one (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    W.smul W.conformalVector (1 : ℤ) v = W.L 0 v := by
  rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = (1 : ℤ) by ring]

/-- **The Zhu product with the conformal vector**, explicitly:
`ω * v = ω₍₋₁₎v + 2·L₋₁v + L₀v`  (the `k = 2` instance of `zhuMul_of_mem_grading`, with
`C(2,0) = 1`, `C(2,1) = 2`, `C(2,2) = 1`). -/
theorem zhuMul_conformalVector (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    zhuMul W W.conformalVector v
      = W.smul W.conformalVector (-1) v + (2 : ℂ) • W.L (-1) v + W.L 0 v := by
  have hsum := zhuMul_of_mem_grading W W.conformalVector_mem_grading_two v
  rw [show ((2 : ℤ).toNat + 1) = 3 from rfl] at hsum
  rw [hsum, sum_range_three]
  have e0 : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  have e2 : ((2 : ℕ) : ℤ) - 1 = 1 := by norm_num
  have b0 : cbz (2 : ℤ) ((0 : ℕ) : ℤ) = 1 := by
    rw [show (((0 : ℕ)) : ℤ) = (0 : ℤ) by norm_num]; exact cbz_zero 2
  have b1 : cbz (2 : ℤ) ((1 : ℕ) : ℤ) = 2 := by
    rw [show (((1 : ℕ)) : ℤ) = (1 : ℤ) by norm_num]; exact cbz_two_one
  have b2 : cbz (2 : ℤ) ((2 : ℕ) : ℤ) = 1 := by
    rw [show (((2 : ℕ)) : ℤ) = (2 : ℤ) by norm_num]; exact cbz_two_two
  rw [e0, e1, e2, b0, b1, b2, one_smul, one_smul, smul_conformalVector_zero,
    smul_conformalVector_one]

/-- **`[ω * v] = [ω₍₋₁₎v] − k·[v]`** for `v ∈ 𝒱_k`: the two Virasoro terms in
`zhuMul_conformalVector` collapse against `[L₋₁v] = −k[v]`, `[L₀v] = k[v]`. -/
theorem mk_zhuMul_conformalVector (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading k) :
    mk W (zhuMul W W.conformalVector v)
      = mk W (W.smul W.conformalVector (-1) v) - (k : ℂ) • mk W v := by
  have h1 : mk W (W.L (-1) v) = (-(k : ℂ)) • mk W v := mk_L_neg_one_of_mem_grading W hv
  have h2 : mk W (W.L 0 v) = (k : ℂ) • mk W v := mk_L_zero_of_mem_grading W hv
  rw [zhuMul_conformalVector, map_add, map_add, map_smul, h1, h2]
  module

/-- **Left multiplication by `[ω]` in `A(𝒱)`**: `[ω]·[v] = [ω₍₋₁₎v] − k·[v]` for `v ∈ 𝒱_k`. -/
theorem Amul_omega_mk (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {v : 𝒱} (hv : v ∈ W.grading k) :
    Amul (zhuRingData_holds W) (mk W W.conformalVector) (mk W v)
      = mk W (W.smul W.conformalVector (-1) v) - (k : ℂ) • mk W v := by
  rw [Amul_mk]
  exact mk_zhuMul_conformalVector W hv

/-- **Left multiplication by `[ω] − h`**: `([ω]−h)·[v] = [ω₍₋₁₎v] − (k+h)·[v]` for `v ∈ 𝒱_k`. -/
theorem Amul_omegaShift_mk (W : VertexOperatorAlgebra 𝒱) (h : ℂ) {k : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading k) :
    Amul (zhuRingData_holds W) (omegaShift W h) (mk W v)
      = mk W (W.smul W.conformalVector (-1) v) - ((k : ℂ) + h) • mk W v := by
  rw [omegaShift, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    Amul_one_left, Amul_omega_mk W hv]
  module

/-- **The square of `[ω]`**: `[ω]² = [ω₍₋₁₎ω] − 2·[ω]`.  (`ω₍₋₁₎ω` is the weight-`4` state
usually written `:ωω:`.) -/
theorem omega_sq (W : VertexOperatorAlgebra 𝒱) :
    Amul (zhuRingData_holds W) (mk W W.conformalVector) (mk W W.conformalVector)
      = mk W (W.smul W.conformalVector (-1) W.conformalVector)
        - (2 : ℂ) • mk W W.conformalVector := by
  have h := Amul_omega_mk W W.conformalVector_mem_grading_two
  rw [show (((2 : ℤ)) : ℂ) = 2 by norm_num] at h
  exact h

/-! ## §4 The blocker as a statement about modules -/

/-- The action of a bundled `AMod` is multiplicative on **all** of `A(𝒱)` (it is assumed only on
representable Zhu products, but `mk` is surjective). -/
theorem AMod_rho_Amul (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (p q : A W) :
    U.ρ (Amul (zhuRingData_holds W) p q) = U.ρ p * U.ρ q := by
  obtain ⟨u, rfl⟩ := mk_surjective W p
  obtain ⟨v, rfl⟩ := mk_surjective W q
  rw [Amul_mk]
  exact U.ρ_mul u v

/-- **A square-zero-but-nonzero action of `[ω] − h` on any `A(𝒱)`-module forces
`OmegaJordanAt 𝒱 h`.**  Indeed `A(𝒱)([ω]−h)²` is then annihilated by `U`, while `[ω]−h` is not.

This is the tractable form of the blocker: instead of a non-membership statement in a quotient by
a span, one has to exhibit a single module — the "staggered" module of logarithmic CFT. -/
theorem omegaJordanAt_of_amod (W : VertexOperatorAlgebra 𝒱) (h : ℂ) (U : AMod W)
    (hsq : U.ρ (omegaShift W h) ^ 2 = 0) (hne : U.ρ (omegaShift W h) ≠ 0) :
    OmegaJordanAt W h := by
  intro hmem
  obtain ⟨a, ha⟩ := (mem_zhuLeftMul W).mp hmem
  refine hne ?_
  rw [← ha, AMod_rho_Amul, AMod_rho_Amul, ← pow_two, hsq, mul_zero]

/-- The converse, free from `TripletW2Log`: `A(𝒱) ⧸ A(𝒱)([ω]−h)²` is such a module. -/
theorem exists_amod_of_omegaJordanAt (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hnd : OmegaJordanAt W h) :
    ∃ U : AMod W, U.ρ (omegaShift W h) ^ 2 = 0 ∧ U.ρ (omegaShift W h) ≠ 0 :=
  ⟨omegaJordanAMod W h, zhuQuotRho_omegaShift_sq W h, zhuQuotRho_omegaShift_ne_zero W h hnd⟩

/-- **The blocker, reformulated.**  `[ω] − h` fails to be a left multiple of `([ω]−h)²`
exactly when some `A(𝒱)`-module carries a nonzero square-zero `[ω] − h`. -/
theorem omegaJordanAt_iff_exists_amod (W : VertexOperatorAlgebra 𝒱) (h : ℂ) :
    OmegaJordanAt W h ↔
      ∃ U : AMod W, U.ρ (omegaShift W h) ^ 2 = 0 ∧ U.ρ (omegaShift W h) ≠ 0 :=
  ⟨exists_amod_of_omegaJordanAt W h,
    fun ⟨U, h1, h2⟩ => omegaJordanAt_of_amod W h U h1 h2⟩

/-- **A linear-functional certificate.**  A single `ℂ`-linear functional on `A(𝒱)` that kills the
left ideal `A(𝒱)([ω]−h)²` but not `[ω]−h` already gives `OmegaJordanAt 𝒱 h`.  (Strictly weaker
than exhibiting a module.) -/
theorem omegaJordanAt_of_functional (W : VertexOperatorAlgebra 𝒱) (h : ℂ) (φ : A W →ₗ[ℂ] ℂ)
    (hker : ∀ a : A W, φ (Amul (zhuRingData_holds W) a
      (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))) = 0)
    (hne : φ (omegaShift W h) ≠ 0) :
    OmegaJordanAt W h := by
  intro hmem
  obtain ⟨a, ha⟩ := (mem_zhuLeftMul W).mp hmem
  exact hne (by rw [← ha]; exact hker a)

/-- **The same certificate, phrased entirely inside `𝒱`** — the shape a concrete computation in
the symplectic-fermion Fock space would produce.  Write `ω_h := ω − h·𝟙`.  A linear functional `ψ`
on `𝒱` with

* `ψ = 0` on `O(𝒱)`,
* `ψ(a * (ω_h * ω_h)) = 0` for every `a ∈ 𝒱`,
* `ψ(ω_h) ≠ 0`,

gives `OmegaJordanAt 𝒱 h`. -/
theorem omegaJordanAt_of_functional_V (W : VertexOperatorAlgebra 𝒱) (h : ℂ) (ψ : 𝒱 →ₗ[ℂ] ℂ)
    (hO : ∀ x ∈ O W, ψ x = 0)
    (hker : ∀ a : 𝒱, ψ (zhuMul W a (zhuMul W (W.conformalVector - h • W.vacuum)
      (W.conformalVector - h • W.vacuum))) = 0)
    (hne : ψ (W.conformalVector - h • W.vacuum) ≠ 0) :
    OmegaJordanAt W h := by
  have hle : O W ≤ LinearMap.ker ψ := fun x hx => LinearMap.mem_ker.mpr (hO x hx)
  have hmk : mk W (W.conformalVector - h • W.vacuum) = omegaShift W h := by
    rw [map_sub, map_smul]; rfl
  have hlift : ∀ v : 𝒱, (O W).liftQ ψ hle (mk W v) = ψ v := by
    intro v
    rw [mk, Submodule.mkQ_apply, Submodule.liftQ_apply]
  refine omegaJordanAt_of_functional W h ((O W).liftQ ψ hle) (fun a => ?_) ?_
  · obtain ⟨b, rfl⟩ := mk_surjective W a
    rw [← hmk, Amul_mk, Amul_mk, hlift]
    exact hker b
  · rw [← hmk, hlift]
    exact hne

/-! ## §5 Necessary conditions, and `A(𝒱) ≠ 0` whenever `𝟙 ≠ 0` -/

/-- `[ω] − 0 = [ω]`. -/
theorem omegaShift_zero (W : VertexOperatorAlgebra 𝒱) :
    omegaShift W 0 = mk W W.conformalVector := by
  rw [omegaShift, zero_smul, sub_zero]

/-- **A necessary condition**: `OmegaJordanAt 𝒱 h` forces `[ω] − h ≠ 0` in `A(𝒱)` (the zero
element lies in every left ideal). -/
theorem omegaShift_ne_zero_of_omegaJordanAt (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hnd : OmegaJordanAt W h) : omegaShift W h ≠ 0 := by
  intro hz
  refine hnd ?_
  rw [hz]
  exact Submodule.zero_mem _

/-- **At `h = 0` the necessary condition is `[ω] ≠ 0` in `A(𝒱)`.**  So a strictly smaller open
target than `OmegaJordanAt tripletW2 0` is: *is the class of the conformal vector nonzero in
`A(W(2))`?*  Nothing in this repository decides it. -/
theorem mk_conformalVector_ne_zero_of_omegaJordanAt (W : VertexOperatorAlgebra 𝒱)
    (hnd : OmegaJordanAt W 0) : mk W W.conformalVector ≠ 0 := by
  have h := omegaShift_ne_zero_of_omegaJordanAt W 0 hnd
  rwa [omegaShift_zero] at h

/-- The adjoint module's weight-`0` space is `𝒱₀`. -/
theorem adjWeight_zero_eq (W : VertexOperatorAlgebra 𝒱) :
    adjWeight W 0 = W.grading 0 := by
  have h := adjWeight_cast W 0
  rwa [Int.cast_zero] at h

/-- `𝟙` lies in the weight-`0` space of the adjoint module. -/
theorem vacuum_mem_adjWeight_zero (W : VertexOperatorAlgebra 𝒱) :
    W.vacuum ∈ (adjointModule W).weight 0 := by
  change W.vacuum ∈ adjWeight W 0
  rw [adjWeight_zero_eq W]
  exact W.vacuum_mem

/-- Every vector of the adjoint bottom is a weight-`0` vector of `𝒱`. -/
theorem coe_mem_grading_zero (W : VertexOperatorAlgebra 𝒱)
    (x : (adjointModule W).weight 0) : (x : 𝒱) ∈ W.grading 0 := by
  have hx : (x : 𝒱) ∈ adjWeight W 0 := x.2
  rwa [adjWeight_zero_eq W] at hx

/-- **`[ω]` annihilates the adjoint bottom.**  On `𝒱₀` the zero mode of `ω` is `L₀`, which is
`0` there.  Hence for `W(2)` the value `h = 0` really is attained by `[ω]` on a *nonzero*
`A(𝒱)`-module — it is the only place where a Jordan block of `[ω]` can be looked for by this
route, and it also shows the ideal `A(𝒱)·[ω]` is proper. -/
theorem adjointBottom_rho_conformalVector (W : VertexOperatorAlgebra 𝒱) :
    (VHat.DLM3.adjointBottomAMod W).ρ (mk W W.conformalVector) = 0 := by
  refine LinearMap.ext (fun x : (adjointModule W).weight 0 => ?_)
  have hcoe := actA_mk_apply_coe (adjointModule W) (VHat.DLM3.adjointModule_isLowestWeight W)
    W.conformalVector x
  have hz : oMod (adjointModule W) W.conformalVector (x : 𝒱) = 0 := by
    rw [oMod_homogeneous (adjointModule W) W.conformalVector_mem_grading_two]
    change mode (W.Y W.conformalVector) ((2 : ℤ) - 1) (x : 𝒱) = 0
    rw [show ((2 : ℤ) - 1) = ((0 : ℤ) + 1) by ring, ← L_def,
      W.L_zero_grading _ (coe_mem_grading_zero W x), Int.cast_zero, zero_smul]
  rw [LinearMap.zero_apply]
  exact Subtype.ext (hcoe.trans hz)

/-- **`[𝟙] ≠ 0` in `A(𝒱)`**, i.e. `O(𝒱) ≠ 𝒱`, for any VOA with `𝟙 ≠ 0`.

The weight-`0` space of the adjoint module is `𝒱₀`, which contains `𝟙`; `[𝟙]` acts on it as the
identity (`AMod.ρ_one`), and the identity of a nonzero space is nonzero. -/
theorem one_ne_zero (W : VertexOperatorAlgebra 𝒱) (hv : W.vacuum ≠ 0) : one W ≠ 0 := by
  intro hzero
  have h1 : (VHat.DLM3.adjointBottomAMod W).ρ (one W) = 1 :=
    (VHat.DLM3.adjointBottomAMod W).ρ_one
  rw [hzero, map_zero] at h1
  have h2 := congrArg
    (fun f : End ℂ ((adjointModule W).weight 0) => f ⟨W.vacuum, vacuum_mem_adjWeight_zero W⟩) h1
  exact hv (congrArg Subtype.val h2).symm

/-- `A(𝒱)` is a nonzero `ℂ`-module whenever `𝟙 ≠ 0`. -/
theorem mk_vacuum_ne_zero (W : VertexOperatorAlgebra 𝒱) (hv : W.vacuum ≠ 0) :
    mk W W.vacuum ≠ 0 := one_ne_zero W hv

/-! ## §6 The `W(2)` specialisations -/

namespace SympFerm

open VOA.SympFerm

/-- **`A(W(2)) ≠ 0`**: the class of the vacuum is nonzero, i.e. `O(W(2)) ≠ W(2)`.  Without this
the whole `OmegaJordanAt` programme would be vacuous. -/
theorem tripletW2_one_ne_zero : one tripletW2 ≠ 0 :=
  one_ne_zero tripletW2 tripletW2_vacuum_ne_zero

/-- `[L₋₁ω] = −2·[ω]` in `A(W(2))` (the `k = 2` case of `mk_L_neg_one_of_mem_grading`). -/
theorem tripletW2_mk_L_neg_one_omega :
    mk tripletW2 (tripletW2.L (-1) tripletW2.conformalVector)
      = (-2 : ℂ) • mk tripletW2 tripletW2.conformalVector := by
  have h := mk_L_neg_one_of_mem_grading tripletW2 tripletW2.conformalVector_mem_grading_two
  rw [show (-(((2 : ℤ)) : ℂ)) = (-2 : ℂ) by norm_num] at h
  exact h

/-- `[ω]² = [ω₍₋₁₎ω] − 2·[ω]` in `A(W(2))`. -/
theorem tripletW2_omega_sq :
    Amul (zhuRingData_holds tripletW2) (mk tripletW2 tripletW2.conformalVector)
        (mk tripletW2 tripletW2.conformalVector)
      = mk tripletW2 (tripletW2.smul tripletW2.conformalVector (-1) tripletW2.conformalVector)
        - (2 : ℂ) • mk tripletW2 tripletW2.conformalVector :=
  omega_sq tripletW2

/-- **`[ω]` acts as `0` on the (nonzero) adjoint bottom `W(2)₀ = ℂ𝟙`.**  So `h = 0` is an
eigenvalue of the central element `[ω]` on a genuine nonzero `A(W(2))`-module: `h = 0` is where a
Jordan block must be sought. -/
theorem tripletW2_adjointBottom_rho_omega :
    (VHat.DLM3.adjointBottomAMod tripletW2).ρ (mk tripletW2 tripletW2.conformalVector) = 0 :=
  adjointBottom_rho_conformalVector tripletW2

/-- **A strictly smaller open target.**  `OmegaJordanAt tripletW2 0` implies
`[ω] ≠ 0` in `A(W(2))`; the latter is itself not decided anywhere in this repository. -/
theorem tripletW2_mk_omega_ne_zero_of_omegaJordanAt (hnd : OmegaJordanAt tripletW2 0) :
    mk tripletW2 tripletW2.conformalVector ≠ 0 :=
  mk_conformalVector_ne_zero_of_omegaJordanAt tripletW2 hnd

/-- **The sole remaining blocker for logarithmic `W(2)`-modules, in its tractable form.**

Combined with `Examples.TripletW2Log.tripletW2Log`, this says: a genuine logarithmic
`W(2)`-module with `L₀ⁿⁱˡ ≠ 0` follows (given the two cofiniteness inputs and the Dong–Jiang gate)
as soon as one exhibits **one** `A(W(2))`-module on which `[ω] − h` is nonzero and squares to
zero. -/
theorem tripletW2_omegaJordanAt_iff (h : ℂ) :
    OmegaJordanAt tripletW2 h ↔
      ∃ U : AMod tripletW2, U.ρ (omegaShift tripletW2 h) ^ 2 = 0
        ∧ U.ρ (omegaShift tripletW2 h) ≠ 0 :=
  omegaJordanAt_iff_exists_amod tripletW2 h

end SympFerm

end VOA.ZhuW2
