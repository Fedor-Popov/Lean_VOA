/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchGradedModeVanish
import VOA.Modules.ZhuVermaAnArchBottomDefectClose
import VOA.Modules.ZhuModule

/-!
# B1 — the annihilation half of the `(0,0)` gate

The gate of the Zhu bijection construction is `OnmFull W 0 0 ≤ O W` (Dong–Jiang Prop. 4.6 at `(n,m) = (0,0)`).  Its
**annihilation half** (B1) asks: for every `ℂ`-graded `𝒱`-module `N` with lowest weight `h` and
every bottom vector `w ∈ M_h`, the zero mode of every generator of `OnmAssoc W 0 0` and of
`OnmLevel W 0 0` kills `w`.

This file builds the **cross-level zero-mode calculus** that Dong–Jiang Lemma 4.1 lives in, proves
the level-`m` `O'_{n,m}`-annihilation **unconditionally**, and reduces B1 to the single named
composition law (DJ Lemma 4.1).

## The cross-level mode `o_{n,m}`

Dong–Jiang (`math/0601626`, §4, p. 15) set, for an admissible module `M = ⨁ₖ M(k)`,
```
  o_{n,m}(u) : M(m) → M(n),   o_{n,m}(u) w = u_{wt u + m − n − 1} w.
```
It depends on `(n,m)` only through `d = m − n`, so it is packaged here as
`oLev N d : 𝒱 →ₗ[ℂ] End ℂ M`, `oLev N d u = u₍ₖ₋₁₊d₎` on homogeneous `u ∈ 𝒱ₖ`.  It shifts the
conformal weight by `−d` (`oLev_mem_weight`), so `oLev N ((m:ℤ) − n)` is exactly `o_{n,m}`.
Anchors: `oLev N 0 = oMod N` (`oLev_zero`) and `oLev N (−n) = gMode N n` (`oLev_neg_eq_gMode`).

## What is proved here, unconditionally (axiom-clean)

* **`mode_vanish_of_level`** — the level-`m` mode truncation: for homogeneous `v ∈ 𝒱_β` and
  `w ∈ M(m) = N.weight (h+m)`, `v₍ₙ₎ w = 0` as soon as `n ≥ β + m`.  (Equivalently
  `M(m) ⊆ Ω_m(M)` in Dong–Jiang's notation, DJ p. 17 — pure grading, no admissibility needed.)
* **`oLev_anmLgen_vanish`** — `o_{n,m}(L₋₁u + (L₀ + m − n)u) = 0` for **all** `u`, on **any**
  module, with no lowest-weight hypothesis.  The cross-level form of Gannon 5.3.9b.
* **`resHom_vOutside_coeff_vanish`** — the *one* genuine binomial cancellation in B1:
  `∑_{j=0}^{P} C(P,j)(−1)^{j−q} C(j−q, i) = 0` for `0 ≤ i < P` (a finite difference of a
  polynomial of degree `i < P`; off the proved `altShift_vanish`).  Standard, level-independent.
* **`oLev_resHom_uOutside`** — the **structural expansion**: on `M(m)` with `m ≤ s`,
  `oLev N D (Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v) w` is a **pure `u`-outside** double sum
  `∑_j ∑_{i ∈ [0, m+s−q+2−D)} C(k+s,j)(−1)^i C(j−q,i) · u₍ⱼ₋q₋ᵢ₎ v₍…₎ w` — the entire
  `v`-outside Jacobi family cancels identically.  Every module-theoretic ingredient of
  Dong–Jiang Lemma 4.1 is contained in this theorem.
* **`oLev_resHom_vanish`** — the **high-pole annihilation law**: for `m ≤ s` and
  `q ≥ s + m − D + 2`,
  `oLev N D (Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v) w = 0`  for every `w ∈ M(m)`.
  Immediate from the previous item: the surviving index range `[0, m+s−q+2−D)` is empty.
* **`Onm_annihilates_level`** — `o_{n,m}(x) w = 0` for all `x ∈ O'_{n,m}(𝒱)` and `w ∈ M(m)`.
  Specialisations: `Onm_annihilates_diag` (`= O_p(𝒱)` kills `M(p)`, i.e. Dong–Jiang **Theorem
  4.3** restricted to the graded pieces — which is all B1 needs) and `O_annihilates_bottom`
  (Zhu's classical `O(𝒱)`-annihilation, recovered at `(n,m) = (0,0)`).
  This discharges the preliminary step **B0** for the graded pieces.

## What is REDUCED, and to exactly what

The residual is the single named hypothesis

* **`DJComposition W`** — Dong–Jiang **Lemma 4.1** (`math/0601626`, p. 15, verbatim):
  `o_{n,m}(a ∗ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w` for `w ∈ M(m)`.
  Its anchor case `(n,m,p) = (0,0,0)` is a **theorem** here (`djComposition_at_zero`, = Gannon
  5.3.9a), so the normalisation of the statement is pinned.  Via `oLev_resHom_uOutside` what
  remains of it is purely scalar: the surviving `u`-outside coefficients of
  `∑_{i'=0}^{p}(−1)^{i'}C(m+n−p+i',i') · resHom W m (m+n−p+i'+1)` must collapse to the single
  monomial `u₍wt u+p−n−1₎ v₍wt v+m−p−1₎` (Dong–Jiang's own Vandermonde
  `∑_{i=0}^{κ} C(n+m−p+i,i) C(−n−m+p−i−1,κ−i) = 0`, `κ = 1..p`).  No module theory is left in it.

and the deliverable

* **`GateAnnihilation W`** — B1 itself: `oMod N x w = 0` for `x ∈ OnmFull W 0 0`, `w ∈ M_h`.

**`gateAnnihilation_of_djComposition : DJComposition W → GateAnnihilation W`** — the full
assembly, proved here.  Concretely (`oMod_assocDefect_vanish`, `oMod_levelMix_vanish`):
the `O''` generator
`u ∗⁰_{0,p₃}((a ∗^{p₃}_{p₁,p₂} b) ∗^{p₃}_{0,p₁} c − a ∗^{p₃}_{0,p₂}(b ∗^{p₂}_{0,p₁} c))`
is killed by **four** applications of Lemma 4.1, which rewrite both halves as the same triple
composite `o_{0,p₃}(u) o_{p₃,p₂}(a) o_{p₂,p₁}(b) o_{p₁,0}(c) w`; the `O'''` generator
`(a ∗⁰_p g) ∗⁰_{0,p} v` with `g ∈ O_p(𝒱)` is killed by **two** applications plus the proven
`Onm_annihilates_diag`.  Nothing else is used — in particular no general-`n` DLM3, no
`A_{n,n} = A_n`, and no engine input.

## Status labels

proved (axiom-clean): `mode_vanish_of_level`, `oLev_*` API, `oLev_anmLgen_vanish`,
`resHom_vOutside_coeff_vanish`, `oLev_resHom_uOutside`, `oLev_resHom_vanish`,
`Onm_annihilates_level`, `Onm_annihilates_diag`, `O_annihilates_bottom`, `djComposition_at_zero`.
REDUCED-to-`DJComposition`: `oMod_assocDefect_vanish`, `oMod_levelMix_vanish`,
`gateAnnihilation_of_djComposition` (the hypothesis is a term argument, never an axiom).
NOT proved here: `DJComposition W` itself (general `(n,m,p)`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`) §2 (`O'/O''/O'''`, the products
`∗ⁿ_{m,p}`), §4 (`o_{n,m}`, Lemma 4.1, Thm 4.3, Prop 4.5, Prop 4.6);
Dong–Li–Mason, J. Algebra 206 (1998) 67–96, §3 (`Ω_n`, Thm 3.2); Gannon §5.3.2 (5.3.9a/b).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section CrossLevel

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (A) The cross-level zero mode `o_{n,m}` -/

/-- The weight-`k` slice of the **level-shifted zero mode**: `vₖ ↦ (vₖ)₍ₖ₋₁₊d₎` as a map
`𝒱ₖ → End M`.  At `d = 0` it is `Character.oModFamily`; at `d = −n` it is `gModeFamily _ n`. -/
noncomputable def oLevFamily (N : OrdVModule W M) (d : ℤ) (k : ℤ) : (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1 + d)).comp (N.YM.comp (W.grading k).subtype)

/-- **The level-shifted zero mode** `oLev N d v = ∑_k (v_k)₍ₖ₋₁₊d₎` — Dong–Jiang's `o_{n,m}` with
`d = m − n` (DJ §4, p. 15: `o_{n,m}(u) w = u_{wt u + m − n − 1} w`).  It lowers the conformal
weight by exactly `d`, i.e. maps `M(m) → M(m − d) = M(n)`. -/
noncomputable def oLev (N : OrdVModule W M) (d : ℤ) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oLevFamily N d)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- On a homogeneous `x ∈ 𝒱ₖ` the level-shifted zero mode is the single mode `x₍ₖ₋₁₊d₎`. -/
theorem oLev_homogeneous (N : OrdVModule W M) (d : ℤ) {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    oLev N d x = mode (N.YM x) (k - 1 + d) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oLev N d x = oLevFamily N d k ⟨x, hx⟩ := by
    change (DFinsupp.lsum ℂ (oLevFamily N d)) (DirectSum.decompose W.grading x) = _
    rw [DirectSum.decompose_of_mem W.grading hx]
    exact DFinsupp.lsum_single ℂ (oLevFamily N d) k ⟨x, hx⟩
  rw [hcollapse]; rfl

/-- At `d = 0` the slices are the zero-mode slices. -/
theorem oLevFamily_zero (N : OrdVModule W M) : oLevFamily N 0 = oModFamily N := by
  funext k
  unfold oLevFamily oModFamily
  norm_num

/-- **`oLev N 0 = oMod N`** — the diagonal `o_{n,n}` is the ordinary zero mode. -/
theorem oLev_zero (N : OrdVModule W M) : oLev N 0 = oMod N := by
  unfold oLev oMod
  rw [oLevFamily_zero]

/-- At `d = −n` the slices are the depth-`n` graded-mode slices. -/
theorem oLevFamily_neg (N : OrdVModule W M) (n : ℕ) : oLevFamily N (-(n : ℤ)) = gModeFamily N n := by
  funext k
  unfold oLevFamily gModeFamily
  norm_num [sub_eq_add_neg]

/-- **`oLev N (−n) = gMode N n`** — the raising mode `o_{n,0} : M(0) → M(n)`. -/
theorem oLev_neg_eq_gMode (N : OrdVModule W M) (n : ℕ) : oLev N (-(n : ℤ)) = gMode N n := by
  unfold oLev gMode
  rw [oLevFamily_neg]

/-! ## (B) The level filtration and the mode truncation -/

/-- **Level-`m` mode truncation.**  For homogeneous `v ∈ 𝒱_β` and `w` in the level-`m` piece
`M(m) = N.weight (h + m)` of a lowest-weight module, `v₍ₙ₎ w = 0` whenever `n ≥ β + m`: the mode
would push the conformal weight strictly below the lowest weight `h`.  This is exactly the
statement `M(m) ⊆ Ω_m(M)` (Dong–Jiang p. 17) — pure grading, no admissibility. -/
theorem mode_vanish_of_level (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) {m : ℕ} {x : M} (hx : x ∈ N.weight (h + (m : ℂ)))
    {n : ℤ} (hn : β + (m : ℤ) ≤ n) : mode (N.YM v) n x = 0 := by
  have hmem := mode_mem_weight N hv hx n
  have hbot : N.weight (h + (m : ℂ) + (β : ℂ) - (n : ℂ) - 1) = ⊥ := by
    by_contra hne
    obtain ⟨r, hr⟩ := hcw _ hne
    have hkeq : ((m : ℂ) + (β : ℂ) - (n : ℂ) - 1) = (r : ℂ) := by
      have hh : h + ((m : ℂ) + (β : ℂ) - (n : ℂ) - 1) = h + (r : ℂ) := by rw [← hr]; ring
      exact add_left_cancel hh
    have hz : (m : ℤ) + β - n - 1 = (r : ℤ) := by exact_mod_cast hkeq
    omega
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- The level-shifted zero mode lowers the conformal weight by `d`, on homogeneous `v`. -/
theorem oLev_mem_weight_homog (N : OrdVModule W M) (d : ℤ) {k : ℤ} {v : 𝒱} (hv : v ∈ W.grading k)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) : oLev N d v x ∈ N.weight (α - (d : ℂ)) := by
  rw [oLev_homogeneous N d hv]
  have hm := mode_mem_weight N hv hx (k - 1 + d)
  rwa [show α + (k : ℂ) - (((k - 1 + d : ℤ)) : ℂ) - 1 = α - (d : ℂ) from by push_cast; ring] at hm

/-- **`oLev N d` lowers the conformal weight by `d`** for every `v` (grade decomposition). -/
theorem oLev_mem_weight (N : OrdVModule W M) (d : ℤ) (v : 𝒱) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : oLev N d v x ∈ N.weight (α - (d : ℂ)) := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => oLev N d v x ∈ N.weight (α - (d : ℂ))) hvtop ?_ ?_ ?_
  · intro i y hy
    exact oLev_mem_weight_homog N d hy hx
  · change oLev N d 0 x ∈ _
    rw [map_zero, LinearMap.zero_apply]
    exact (N.weight _).zero_mem
  · intro y z hy hz
    change oLev N d (y + z) x ∈ _
    rw [map_add, LinearMap.add_apply]
    exact (N.weight _).add_mem hy hz

/-- **Level bookkeeping**: `o_{n,m}` maps `M(m)` into `M(n)`.  Stated in the `d = m − n` form:
`oLev N ((m:ℤ) − p) v` maps `M(m)` into `M(p)`. -/
theorem oLev_mem_level (N : OrdVModule W M) {h : ℂ} (m p : ℕ) (v : 𝒱) {x : M}
    (hx : x ∈ N.weight (h + (m : ℂ))) :
    oLev N ((m : ℤ) - (p : ℤ)) v x ∈ N.weight (h + (p : ℂ)) := by
  have := oLev_mem_weight N ((m : ℤ) - (p : ℤ)) v hx
  rwa [show h + (m : ℂ) - ((((m : ℤ) - (p : ℤ)) : ℤ) : ℂ) = h + (p : ℂ) from by
    push_cast; ring] at this

/-! ## (C) The grading generator: `o_{n,m}(L₋₁u + (L₀ + m − n)u) = 0` -/

/-- The level-shifted mode of `L₋₁c` on a homogeneous `c ∈ 𝒱ₖ` is `−(k+d)·c₍ₖ₋₁₊d₎`. -/
theorem oLev_L_neg_one (N : OrdVModule W M) (d : ℤ) {k : ℤ} {c : 𝒱} (hc : c ∈ W.grading k) :
    oLev N d (W.L (-1) c) = (-((k : ℂ) + (d : ℂ))) • oLev N d c := by
  have hmem : W.L (-1) c ∈ W.grading (k + 1) := L_neg_one_mem_grading_succ W hc
  rw [oLev_homogeneous N d hmem, oLev_homogeneous N d hc,
    show (k + 1 - 1 + d) = (k + d) from by ring]
  ext x
  simp only [LinearMap.smul_apply]
  have hcov := act_T_covariance N.toWeakModule c (k + d) x
  simp only [WeakModule.act_def] at hcov
  rw [show (k - (1 : ℤ) + d) = (k + d) - 1 from by ring, hcov]
  congr 2
  push_cast; ring

/-- **The grading-generator vanishing on a homogeneous `c`** (cross-level form of Gannon 5.3.9b):
`o_{n,m}(L₋₁c + (L₀ + m − n)c) = 0`.  The three contributions to the coefficient of `c₍ₖ₋₁₊d₎`
(`d = m − n`) are `−(k+d)`, `+k`, `+d`; they sum to `0`.  Unconditional. -/
theorem oLev_anmLgen_homogeneous (N : OrdVModule W M) (n m : ℕ) {k : ℤ} {c : 𝒱}
    (hc : c ∈ W.grading k) : oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0 := by
  unfold anmLgen
  rw [map_add, map_add, map_smul, oLev_L_neg_one N _ hc, W.L_zero_grading c hc, map_smul,
    ← add_smul, ← add_smul,
    show (-((k : ℂ) + ((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ))) + (k : ℂ) + ((m : ℂ) - (n : ℂ)) = 0 from by
      push_cast; ring, zero_smul]

/-- **The grading-generator vanishing for all `c`** — `o_{n,m}(L₋₁c + (L₀ + m − n)c) = 0` on any
module, no lowest-weight hypothesis.  Drops homogeneity by `iSup`-induction. -/
theorem oLev_anmLgen_vanish (N : OrdVModule W M) (n m : ℕ) (c : 𝒱) :
    oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0 := by
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) = 0) hctop ?_ ?_ ?_
  · intro i x hx
    exact oLev_anmLgen_homogeneous N n m hx
  · change oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m (0 : 𝒱)) = 0
    have h0 : anmLgen W n m (0 : 𝒱) = 0 := by
      have := anmLgen_smul W n m (0 : ℂ) (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero]
  · intro x y hx hy
    change oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m (x + y)) = 0
    rw [anmLgen_add, map_add, hx, hy, add_zero]

/-! ## (D) The high-pole annihilation law

The engine room of B1.  For a residue `Res_z (1+z)^{wt u + s} z^{−q} Y(u,z) v` whose pole order is
high enough relative to the level (`q ≥ s + m − D + 2`), the level-`D` mode kills `M(m)`.  Two
families arise from the module iterate formula:

* the `u`-outside family `u₍ℓ₋ᵢ₎ v₍ₜ₊ᵢ₎ w` dies **termwise** — the inner `v`-mode overshoots the
  level ceiling (`mode_vanish_of_level`), which is precisely the pole hypothesis;
* the `v`-outside family `v₍ₖ₊ₗ₋₂₊D₋ᵢ₎ u₍ᵢ₎ w` survives termwise but its `j`-sum coefficient is
  `∑_{j} (−1)^j C(k+s, j) C(j−q, i) = 0` for `i < k+s`, the finite-difference identity
  `altShift_vanish`; the range `i ≤ k+m−1` is guaranteed by `m ≤ s`. -/

/-- **The `v`-outside coefficient cancellation** — the *one* genuine binomial identity in B1.
For `0 ≤ i < P`,
`∑_{j=0}^{P} C(P, j) · (−1)^i C(j−q, i) (−1)^{j−q} = 0`, i.e. the `j`-sum coefficient of every
`v₍·₎u₍ᵢ₎w` monomial vanishes.  This is the `P`-th finite difference of the degree-`i < P`
polynomial `j ↦ C(j−q, i)` (`altShift_vanish`), and it is what makes B1 *structural*: no
level-dependent cancellation, just Vandermonde/finite differences. -/
theorem resHom_vOutside_coeff_vanish (P q : ℤ) (hP : 0 ≤ P) {i : ℤ} (hi0 : 0 ≤ i) (hiP : i < P) :
    ∑ j ∈ Finset.range (P.toNat + 1),
      cbz P (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q)) = 0 := by
  classical
  have hPz : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hP
  have hiN : i.toNat < P.toNat := by omega
  have hav := altShift_vanish (c := q) (M := P.toNat) (j := i.toNat) hiN
  have hrw : ∀ j ∈ Finset.range (P.toNat + 1),
      cbz P (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))
        = (negOnePow i * negOnePow q) *
            (negOnePow (j : ℤ) * cbz ((P.toNat : ℕ) : ℤ) (j : ℤ)
              * cbz ((j : ℤ) - q) ((i.toNat : ℕ) : ℤ)) := by
    intro j _
    have h1 : negOnePow ((j : ℤ) - q) = negOnePow (j : ℤ) * negOnePow q := by
      rw [sub_eq_add_neg, negOnePow_add, negOnePow_neg']
    have h2 : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
    rw [h1, h2, hPz]
    ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, hav, mul_zero]

/-- **Per-pole step, both Jacobi families kept.**  For any bound `B` past the level ceiling
(`m − k + ℓ + 2 − D ≤ B`), the level-`D` mode of `u₍ℓ₎v` on `M(m)` is the `u`-outside family over
`Ico 0 B` minus the `v`-outside family over `Ico 0 (k+m)`.  Both truncations are forced by
`mode_vanish_of_level`; nothing is discarded. -/
private theorem oLev_smul_step_full (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (D : ℤ) (m : ℕ) {k l : ℤ} {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l)
    {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) (ℓ B : ℤ) (hB : (m : ℤ) - k + ℓ + 2 - D ≤ B) :
    oLev N D (W.smul u ℓ v) w
      = (∑ i ∈ Finset.Ico (0 : ℤ) B, (negOnePow i * cbz ℓ i) •
            mode (N.YM u) (ℓ - i) (mode (N.YM v) (k + l - ℓ - 2 + D + i) w))
        - ∑ i ∈ Finset.Ico (0 : ℤ) (k + (m : ℤ)),
            (negOnePow i * cbz ℓ i * negOnePow ℓ) •
              mode (N.YM v) (k + l - 2 + D - i) (mode (N.YM u) i w) := by
  classical
  have hgr : W.smul u ℓ v ∈ W.grading (k + l - ℓ - 1) := W.smul_mem_grading hu hv ℓ
  rw [oLev_homogeneous N D hgr, show k + l - ℓ - 1 - 1 + D = k + l - ℓ - 2 + D from by ring,
    module_iterate0 N.toWeakModule u v w ℓ (k + l - ℓ - 2 + D)]
  set F : ℤ → M := fun i => (negOnePow i * cbz ℓ i) •
    mode (N.YM u) (ℓ - i) (mode (N.YM v) (k + l - ℓ - 2 + D + i) w) with hF
  set G : ℤ → M := fun i => (negOnePow i * cbz ℓ i * negOnePow ℓ) •
    mode (N.YM v) (k + l - 2 + D - i) (mode (N.YM u) i w) with hG
  have hFsupp : (Function.support F) ⊆ ↑(Finset.Ico (0 : ℤ) B) := by
    intro i hi
    simp only [hF, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by
      rw [mode_vanish_of_level N hcw hv hw (n := k + l - ℓ - 2 + D + i) (by omega), map_zero,
        smul_zero])
  have hGsupp : (Function.support G) ⊆ ↑(Finset.Ico (0 : ℤ) (k + (m : ℤ))) := by
    intro i hi
    simp only [hG, Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    have h0 : 0 ≤ i := by
      by_contra hneg
      exact hi (by rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_mul, zero_smul])
    refine ⟨h0, ?_⟩
    by_contra hge
    exact hi (by
      rw [mode_vanish_of_level N hcw hu hw (n := i) (by omega), map_zero, smul_zero])
  have hsplit : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
      (mode (N.YM u) (ℓ - i) (mode (N.YM v) (k + l - ℓ - 2 + D + i) w)
        - negOnePow ℓ • mode (N.YM v) (ℓ + (k + l - ℓ - 2 + D) - i) (mode (N.YM u) i w))
      = F i - G i := by
    intro i
    rw [hF, hG, smul_sub, smul_smul,
      show ℓ + (k + l - ℓ - 2 + D) - i = k + l - 2 + D - i from by ring]
  rw [funext hsplit, finsum_sub_distrib (Set.Finite.subset (Finset.Ico (0 : ℤ) B).finite_toSet
      hFsupp) (Set.Finite.subset (Finset.Ico (0 : ℤ) (k + (m : ℤ))).finite_toSet hGsupp),
    finsum_eq_sum_of_support_subset _ hFsupp, finsum_eq_sum_of_support_subset _ hGsupp]

/-- **The `u`-outside expansion** — the structural core of Dong–Jiang Lemma 4.1.  On the
level-`m` piece `M(m)` of a lowest-weight module (`m ≤ s`), the level-`D` mode of an arbitrary
residue `Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v` is a **pure `u`-outside** double sum: the whole
`v`-outside family cancels identically, by `resHom_vOutside_coeff_vanish`.
Consequently Dong–Jiang Lemma 4.1 (`DJComposition`) is reduced to a *purely scalar* statement
about the surviving coefficients — no further module theory is involved. -/
theorem oLev_resHom_uOutside (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (D s : ℤ) (m : ℕ) (hms : (m : ℤ) ≤ s) (q : ℤ)
    {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l)
    {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N D (resHom W s q u v) w
      = ∑ j ∈ Finset.range ((k + s).toNat + 1),
          ∑ i ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + s - q + 2 - D),
            (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
              mode (N.YM u) ((j : ℤ) - q - i)
                (mode (N.YM v) (k + l - ((j : ℤ) - q) - 2 + D + i) w) := by
  classical
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hks : (0 : ℤ) ≤ k + s := by omega
  rw [resHom_homogeneous W s q hu v, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  have hstep : ∀ j ∈ Finset.range ((k + s).toNat + 1),
      (oLev N D (cbz (k + s) (j : ℤ) • W.smul u ((j : ℤ) - q) v)) w
        = (∑ i ∈ Finset.Ico (0 : ℤ) ((m : ℤ) + s - q + 2 - D),
              (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
                mode (N.YM u) ((j : ℤ) - q - i)
                  (mode (N.YM v) (k + l - ((j : ℤ) - q) - 2 + D + i) w))
          - ∑ i ∈ Finset.Ico (0 : ℤ) (k + (m : ℤ)),
              (cbz (k + s) (j : ℤ) *
                (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
                mode (N.YM v) (k + l - 2 + D - i) (mode (N.YM u) i w) := by
    intro j hj
    have hjle : (j : ℤ) ≤ k + s := by
      have hj' : j ≤ (k + s).toNat := by
        simp only [Finset.mem_range] at hj; omega
      omega
    have hB : (m : ℤ) - k + ((j : ℤ) - q) + 2 - D ≤ (m : ℤ) + s - q + 2 - D := by omega
    rw [map_smul, LinearMap.smul_apply,
      oLev_smul_step_full N hcw D m hu hv hw ((j : ℤ) - q) ((m : ℤ) + s - q + 2 - D) hB,
      smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  have hY : ∑ j ∈ Finset.range ((k + s).toNat + 1),
      ∑ i ∈ Finset.Ico (0 : ℤ) (k + (m : ℤ)),
        (cbz (k + s) (j : ℤ) *
          (negOnePow i * cbz ((j : ℤ) - q) i * negOnePow ((j : ℤ) - q))) •
          mode (N.YM v) (k + l - 2 + D - i) (mode (N.YM u) i w) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_Ico] at hi
    rw [← Finset.sum_smul, resHom_vOutside_coeff_vanish (k + s) q hks hi.1 (by omega), zero_smul]
  rw [hY, sub_zero]

/-- **High-pole annihilation, homogeneous slots.**  For `m ≤ s` and `q ≥ s + m − D + 2`,
`oLev N D (resHom W s q u v) w = 0` for every `w ∈ M(m)`, homogeneous `u ∈ 𝒱ₖ` (`k ≥ 0`),
`v ∈ 𝒱ₗ`.  Immediate corollary of `oLev_resHom_uOutside`: the pole hypothesis makes the surviving
`u`-outside index range `Ico 0 (m + s − q + 2 − D)` **empty**. -/
theorem oLev_resHom_vanish_homog (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (D s : ℤ) (m : ℕ) (hms : (m : ℤ) ≤ s) (q : ℤ) (hq : s + (m : ℤ) - D + 2 ≤ q)
    {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k) (hv : v ∈ W.grading l)
    {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N D (resHom W s q u v) w = 0 := by
  rw [oLev_resHom_uOutside N hcw D s m hms q hk hu hv hw]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [show Finset.Ico (0 : ℤ) ((m : ℤ) + s - q + 2 - D) = (∅ : Finset ℤ) from
    Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- **High-pole annihilation, right slot arbitrary.** -/
theorem oLev_resHom_vanish_homogL (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (D s : ℤ) (m : ℕ) (hms : (m : ℤ) ≤ s) (q : ℤ) (hq : s + (m : ℤ) - D + 2 ≤ q)
    {k : ℤ} (hk : 0 ≤ k) {u : 𝒱} (hu : u ∈ W.grading k) (v : 𝒱)
    {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N D (resHom W s q u v) w = 0 := by
  have hvtop : v ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun v => oLev N D (resHom W s q u v) w = 0) hvtop ?_ ?_ ?_
  · intro i y hy
    exact oLev_resHom_vanish_homog N hcw D s m hms q hq hk hu hy hw
  · change oLev N D (resHom W s q u 0) w = 0
    have h0 : resHom W s q u (0 : 𝒱) = 0 := by
      have := resHom_smul_right W s q (0 : ℂ) u (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLev N D (resHom W s q u (y + z)) w = 0
    rw [resHom_add_right, map_add, LinearMap.add_apply, hy, hz, add_zero]

/-- **The high-pole annihilation law** (fully general slots).  For `m ≤ s` and
`q ≥ s + m − D + 2`, the level-`D` mode of `Res_z (1+z)^{wt u + s} z^{−q} Y(u,z)v` annihilates the
level-`m` piece `M(m)` of any lowest-weight module.  Unconditional. -/
theorem oLev_resHom_vanish (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    (D s : ℤ) (m : ℕ) (hms : (m : ℤ) ≤ s) (q : ℤ) (hq : s + (m : ℤ) - D + 2 ≤ q)
    (u v : 𝒱) {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N D (resHom W s q u v) w = 0 := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oLev N D (resHom W s q u v) w = 0) hutop ?_ ?_ ?_
  · intro i y hy
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [W.positivity i hneg, Submodule.mem_bot] at hy
      subst hy
      have h0 : resHom W s q (0 : 𝒱) v = 0 := by
        have := resHom_smul_left W s q (0 : ℂ) (0 : 𝒱) v
        rwa [zero_smul, zero_smul] at this
      rw [h0, map_zero, LinearMap.zero_apply]
    · exact oLev_resHom_vanish_homogL N hcw D s m hms q hq hpos hy v hw
  · change oLev N D (resHom W s q 0 v) w = 0
    have h0 : resHom W s q (0 : 𝒱) v = 0 := by
      have := resHom_smul_left W s q (0 : ℂ) (0 : 𝒱) v
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLev N D (resHom W s q (y + z) v) w = 0
    rw [resHom_add_left, map_add, LinearMap.add_apply, hy, hz, add_zero]

/-! ## (E) `O'_{n,m}(𝒱)` annihilates `M(m)` — Dong–Jiang Prop. 4.5, `O'`-branch -/

/-- The **level-`d` annihilator** of a vector `w`: the `ℂ`-subspace `{x | oLev N d x w = 0}`. -/
def levAnnihilator (N : OrdVModule W M) (d : ℤ) (w : M) : Submodule ℂ 𝒱 where
  carrier := {x : 𝒱 | oLev N d x w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, LinearMap.zero_apply]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

@[simp] theorem mem_levAnnihilator (N : OrdVModule W M) (d : ℤ) (w : M) (x : 𝒱) :
    x ∈ levAnnihilator N d w ↔ oLev N d x w = 0 := Iff.rfl

/-- **The circle generator annihilates `M(m)`**: `o_{n,m}(u ∘ⁿ_m v) w = 0`.  Instance of the
high-pole law with `s = m`, `q = n + m + 2`, `D = m − n` (the inequality is an equality). -/
theorem oLev_anmCirc_vanish (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h) (n m : ℕ)
    (c d : 𝒱) {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N ((m : ℤ) - (n : ℤ)) (anmCirc W n m c d) w = 0 := by
  rw [anmCirc]
  refine oLev_resHom_vanish N hcw ((m : ℤ) - (n : ℤ)) (m : ℤ) m le_rfl
    ((n : ℤ) + (m : ℤ) + 2) (by omega) c d hw

/-- **`O'_{n,m}(𝒱)` annihilates `M(m)`** (Dong–Jiang Prop. 4.5, `O'`-branch — the part that
needs no composition law).  Both generator families are covered unconditionally: circle by
`oLev_anmCirc_vanish`, grading by `oLev_anmLgen_vanish`. -/
theorem Onm_annihilates_level (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h) (n m : ℕ)
    {x : 𝒱} (hx : x ∈ Onm W n m) {w : M} (hw : w ∈ N.weight (h + (m : ℂ))) :
    oLev N ((m : ℤ) - (n : ℤ)) x w = 0 := by
  have hle : Onm W n m ≤ levAnnihilator N ((m : ℤ) - (n : ℤ)) w := by
    simp only [Onm, OnmL]
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro y ⟨c, d, rfl⟩
      exact oLev_anmCirc_vanish N hcw n m c d hw
    · rintro y ⟨c, rfl⟩
      change oLev N ((m : ℤ) - (n : ℤ)) (anmLgen W n m c) w = 0
      rw [oLev_anmLgen_vanish N n m c, LinearMap.zero_apply]
  exact hle hx

/-- **`O_p(𝒱) = O'_{p,p}(𝒱)` annihilates `M(p)`** — Dong–Jiang **Theorem 4.3** restricted to
the graded pieces (`M(p) ⊆ Ω_p(M)`), which is exactly what B1 consumes.  Unconditional. -/
theorem Onm_annihilates_diag (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h) (p : ℕ)
    {x : 𝒱} (hx : x ∈ Onm W p p) {w : M} (hw : w ∈ N.weight (h + (p : ℂ))) :
    oLev N ((p : ℤ) - (p : ℤ)) x w = 0 :=
  Onm_annihilates_level N hcw p p hx hw

/-- **Zhu's classical bottom annihilation, recovered**: `o(x) w = 0` for `x ∈ O(𝒱)`, `w ∈ M_h`
(the `(n,m) = (0,0)` case, using `Onm W 0 0 = O W`). -/
theorem O_annihilates_bottom (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h)
    {x : 𝒱} (hx : x ∈ O W) {w : M} (hw : w ∈ N.weight h) : oMod N x w = 0 := by
  have hx' : x ∈ Onm W 0 0 := by rwa [Onm_zero_zero_eq_O]
  have hw' : w ∈ N.weight (h + ((0 : ℕ) : ℂ)) := by simpa using hw
  have := Onm_annihilates_level N hcw 0 0 hx' hw'
  simpa [oLev_zero] using this

end CrossLevel

/-! ## (F) The named composition law and the B1 statement -/

/-- **Dong–Jiang Lemma 4.1** (`math/0601626`, p. 15, verbatim):
`o_{n,m}(a ∗ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w` for `w ∈ M(m)`.  Written in the `oLev`
normalisation `o_{n,m} = oLev ((m:ℤ) − n)`.  This is the **only** carried hypothesis of B1. -/
def DJComposition (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ},
    IsLowestWeight N h → ∀ (n m p : ℕ) (a b : 𝒱) {w : M}, w ∈ N.weight (h + (m : ℂ)) →
      oLev N ((m : ℤ) - (n : ℤ)) (anmGen W n m p a b) w
        = oLev N ((p : ℤ) - (n : ℤ)) a (oLev N ((m : ℤ) - (p : ℤ)) b w)

/-- **B1 — the annihilation half of the `(0,0)` gate**: for every lowest-weight module and every
bottom vector `w ∈ M_h`, the zero mode of every element of the full Dong–Jiang ideal
`O_{0,0}(𝒱) = O'_{0,0} + O''_{0,0} + O'''_{0,0}` annihilates `w`. -/
def GateAnnihilation (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ},
    IsLowestWeight N h → ∀ x ∈ OnmFull W 0 0, ∀ {w : M}, w ∈ N.weight h → oMod N x w = 0

/-- At `(n,m,p) = (0,0,0)` the Dong–Jiang three-index product is exactly Zhu's product
(`resHom W 0 1 = zhuMul`). -/
theorem anmGen_zero_zero_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    anmGen W 0 0 0 u v = zhuMul W u v := by
  rw [anmGen, Finset.range_one, Finset.sum_singleton]
  norm_num [resHom_zero_one]

section Reduction

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Anchor: `DJComposition` at `(n,m,p) = (0,0,0)` is a THEOREM** — it is exactly Gannon 5.3.9a
(`oMod_zhuMul_lowest_all`, `o(u*v) = o(u)o(v)` on the lowest-weight space).  This pins the
normalisation of `DJComposition` against the already-proved bottom case, so the carried hypothesis
is a genuine generalisation of a proved statement, not a mis-stated one. -/
theorem djComposition_at_zero (N : OrdVModule W M) {h : ℂ} (hcw : IsLowestWeight N h) (u v : 𝒱)
    {w : M} (hw : w ∈ N.weight (h + ((0 : ℕ) : ℂ))) :
    oLev N (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 0 0 u v) w
      = oLev N (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) u
          (oLev N (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) v w) := by
  have hw' : w ∈ N.weight h := by simpa using hw
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [hz, oLev_zero, anmGen_zero_zero_zero]
  exact oMod_zhuMul_lowest_all N hcw u v hw'

/-- **The `O''_{0,0}` (associator-defect) generators annihilate the bottom**, given the
composition law.  Four applications of Dong–Jiang Lemma 4.1 rewrite both halves of the associator
as the same triple composite `o_{p₃,p₂}(a) o_{p₂,p₁}(b) o_{p₁,0}(c) w`, so their difference is
killed before the outer `o_{0,p₃}(u)` is even applied. -/
theorem oMod_assocDefect_vanish (hdj : DJComposition W) (N : OrdVModule W M) {h : ℂ}
    (hcw : IsLowestWeight N h) (p₁ p₂ p₃ : ℕ) (a b c u : 𝒱) {w : M} (hw : w ∈ N.weight h) :
    oMod N (assocDefect W 0 0 p₁ p₂ p₃ a b c u) w = 0 := by
  have hw0 : w ∈ N.weight (h + ((0 : ℕ) : ℂ)) := by simpa using hw
  set y : M := oLev N (((0 : ℕ) : ℤ) - (p₁ : ℤ)) c w with hy
  have hyw : y ∈ N.weight (h + (p₁ : ℂ)) := oLev_mem_level N 0 p₁ c hw0
  have e1 := hdj N hcw p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c hw0
  have e2 := hdj N hcw p₃ p₁ p₂ a b hyw
  have e3 := hdj N hcw p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c) hw0
  have e4 := hdj N hcw p₂ 0 p₁ b c hw0
  have hX : oLev N (((0 : ℕ) : ℤ) - (p₃ : ℤ))
      (anmGen W p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c)) w = 0 := by
    rw [map_sub, LinearMap.sub_apply, e1, e3, e2, e4, ← hy, sub_self]
  have e0 := hdj N hcw 0 0 p₃ u
      (anmGen W p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c
        - anmGen W p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c)) hw0
  rw [assocDefect, ← oLev_zero N]
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [← hz, e0, hX, map_zero]

/-- **The `O'''_{0,0}` (level-mixing) generators annihilate the bottom**, given the composition
law.  Two applications of Dong–Jiang Lemma 4.1 peel `(a ∗⁰_p g) ∗⁰_{0,p} v` down to
`o_{0,p}(a) o_{p,p}(g) o_{p,0}(v) w`, and the middle factor dies by the **proven**
`Onm_annihilates_diag` (`g ∈ O_p(𝒱)`, `o_{p,0}(v)w ∈ M(p)`). -/
theorem oMod_levelMix_vanish (hdj : DJComposition W) (N : OrdVModule W M) {h : ℂ}
    (hcw : IsLowestWeight N h) (p : ℕ) (a v g : 𝒱) (hg : g ∈ Onm W p p)
    {w : M} (hw : w ∈ N.weight h) :
    oMod N (levelMix W 0 0 p a g v) w = 0 := by
  have hw0 : w ∈ N.weight (h + ((0 : ℕ) : ℂ)) := by simpa using hw
  set y : M := oLev N (((0 : ℕ) : ℤ) - (p : ℤ)) v w with hy
  have hyw : y ∈ N.weight (h + (p : ℂ)) := oLev_mem_level N 0 p v hw0
  have e0 := hdj N hcw 0 0 p (anmGen W 0 p p a g) v hw0
  have e1 := hdj N hcw 0 p p a g hyw
  have hmid : oLev N ((p : ℤ) - (p : ℤ)) g y = 0 := Onm_annihilates_diag N hcw p hg hyw
  rw [levelMix, ← oLev_zero N]
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  rw [← hz, e0, ← hy, e1, hmid, map_zero]

/-- **B1, assembled**: the composition law (Dong–Jiang Lemma 4.1) implies the full annihilation
half of the `(0,0)` gate.  The `O'_{0,0}`-summand is discharged by the **proven**
`Onm_annihilates_level`, the `O''` and `O'''` summands by the two theorems above. -/
theorem gateAnnihilation_of_djComposition (hdj : DJComposition W) : GateAnnihilation W := by
  intro M _ _ N h hcw x hx w hw
  have hw0 : w ∈ N.weight (h + ((0 : ℕ) : ℂ)) := by simpa using hw
  have hz : ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
  have hle : OnmFull W 0 0 ≤ levAnnihilator N (0 : ℤ) w := by
    simp only [OnmFull, OnmAssoc, OnmLevel]
    refine sup_le (sup_le ?_ (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
    · intro z hz'
      have := Onm_annihilates_level N hcw 0 0 hz' hw0
      rw [hz] at this
      exact this
    · rintro z ⟨q₁, q₂, q₃, aa, bb, cc, uu, rfl⟩
      have := oMod_assocDefect_vanish hdj N hcw q₁ q₂ q₃ aa bb cc uu hw
      simpa [oLev_zero] using this
    · rintro z ⟨q, aa, vv, gg, hgg, rfl⟩
      have := oMod_levelMix_vanish hdj N hcw q aa vv gg hgg hw
      simpa [oLev_zero] using this
  have := hle hx
  simp only [mem_levAnnihilator] at this
  rw [← oLev_zero N]
  exact this

end Reduction

end VOA

/-! ## Axiom audit (final gate) -/
