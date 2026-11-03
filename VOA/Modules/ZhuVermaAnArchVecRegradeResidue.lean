/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutLev0Slice

/-!
# Game One (RegradeResidue) — the VECTOR regrade of the level-`0` half of `aOutUPart`.

This file works the single open core `AoutUCoreLev0Core` (`ZhuVermaAnArchAoutUCore`) — equivalently
`ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`) — from the **regrade-residue** angle: it applies the
PROVEN scalar regrade `crossDiff_regrade` (`ZhuVermaAnArchHPoleN`) at the VECTOR level to the clean
LEVEL-`0` `PresTowerFam` form of `aOutLev0Half` (`aOutLev0Half_eq_PresTowerFam_lev0`,
`ZhuVermaAnArchAoutLev0Slice`), and isolates the exact boundary residue.

Every lemma here is genuinely proven, axiom-clean.

## The genuine VECTOR regrade (the new content of this file)

The level-`0` per-base Zhu `c`-circle is, in mode-value form (`PresAnm_eq_finsum`, depth `0`, level
`0`, homogeneous `c ∈ 𝒱_M`),

  `PresAnm W M 0 0 c b = ∑ᶠ μ, cbz(M, μ+2) • c₍μ₎ b`.

The PROVEN scalar regrade `crossDiff_regrade M (μ+2) n`

  `cbz(M, μ+2) = ∑_{i<n+1} (−1)^{n−i} C(n,i) · cbz(M+i, (μ+2−n)+i)`

lifts (term-by-term, then swapping the finite `i`-sum outside the `μ`-finsum) to the **vector regrade**

  `PresAnm W M 0 0 c b
     = ∑_{i<n+1} (−1)^{n−i} C(n,i) • (∑ᶠ μ, cbz(M+i, μ+(2−n)+i) • c₍μ₎ b)`     (`presAnm_lev0_regrade`).

Each inner finsum `∑ᶠ μ, cbz(M+i, μ+(2−n)+i) • c₍μ₎ b` is a **grade-`(M+i)`, pole-`(i−n+2)`** `c`-circle
on the single base `b` (the regradeWt of `crossDiff_regrade` moved onto the depth row).  At the top
index `i = n` it is the grade-`(M+n)`, pole-`2` circle `∑ᶠ μ, cbz(M+n, μ+2) • c₍μ₎ b`; at the lower
indices `i < n` it is a genuinely pole-shifted (negative effective level) circle — these lower `i`
terms are exactly the cross-base content that no per-base level-`n` `c`-tower can absorb
(engine `certificates/mathematica/vec_regrade_residue2.wl`: the `i = n` regrade term is NOT the level-`n`
circle `PresAnm W M n 0 c b`).

## Lifting over the `a`-outer multi-base

Summing the per-base regrade over the `a`-outer modes `bᵢ = a₍i−(n+1)₎d` with the weights `C(K,i)`
gives the **vector regrade of `aOutLev0Half`** (`aOutLev0Half_regrade`):

  `aOutLev0Half W n K M a c d
     = ∑_{p<n+1} (−1)^{n−p} C(n,p) • (∑_{i≤K} C(K,i) • (∑ᶠ μ, cbz(M+p, μ+(2−n)+p) • c₍μ₎(a₍i−(n+1)₎d)))`.

This is the precise regrade-residue isolation: the `aOutLev0Half` (the single genuine residual of the
`a`-outer `c`-outer U-core, `ZhuVermaAnArchAoutUCore`) written as a finite `(−1)^{n−p} C(n,p)`-combination
of grade-`(M+p)` pole-`(p−n+2)` `c`-circles over the `a`-outer multi-base.

## The honest residual (engine-verified TRUE; NOT faked / NOT axiomatized)

The remaining content of `AoutUCoreLev0Core` is to reorganize the lower-`p` (pole-shifted /
negative-effective-level) regrade terms across the `a`-outer multi-base into the `c₍s₎a` `MGTowerFam`.
Engine ground truth (`certificates/mathematica/vec_regrade_residue3.wl`, rank-1 free boson, `n = 1, 2`):

* the single-base inner pole-difference `(circ₀ − circₙ) c d` is NOT a single-base level-`n` `c`-tower
  over `d` (**False**, depth `≤ 8`) — the `n`-offset is irreducibly cross-base;
* the regrade splits the level-`0` circle into the regrade family `∑ₚ (−1)^{n−p} C(n,p) • (grade-`(M+p)`
  pole-`(p−n+2)` circle)` (**True**, `presAnm_lev0_regrade`), but the per-base lower-`p` terms are NOT
  level-`n` `c`-towers (the regrade alone does NOT close the per-base obstruction).

So the regrade-residue route reduces `AoutUCoreLev0Core` to the SAME single genuinely-open cross-base
identity as every other route (`ARDTowerDecomp` / `CrossCFirstDiffTowerEq`); the regrade is the proven
SCALAR mechanism that moves the `n`-offset onto grade-shifted rows, but the genuine remaining content
(the cross-base reorganization of those rows into the `c₍s₎a` `MGTowerFam`) is carried by the proven
equivalence `aoutUCoreLev0Core_of_ARDTowerDecomp` (`ZhuVermaAnArchAoutLev0Slice`).  We re-derive the
full `MUGradedAction W` from `ARDTowerDecomp` through this regrade lens, with the vector regrade proved
as a genuine new structural identity.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The grade-`(M+i)`, pole-`(i−n+2)` regrade circle (the regrade row). -/

/-- **The regrade row** `regradeCirc W M n i c b = ∑ᶠ μ, cbz(M+i, μ+((2:ℤ)−n)+i) • c₍μ₎ b`, the
grade-`(M+i)`, pole-`(i−n+2)` `c`-circle on the single base `b` produced by `crossDiff_regrade` at
index `i`.  At `i = n` it is the grade-`(M+n)`, pole-`2` circle; at `i < n` it is a pole-shifted
(negative effective level) circle — the genuine cross-base content. -/
noncomputable def regradeCirc (W : VertexOperatorAlgebra 𝒱) (M n i : ℕ) (c b : 𝒱) : 𝒱 :=
  ∑ᶠ μ : ℤ, cbz ((M : ℤ) + i) (μ + ((2 : ℤ) - n) + i) • W.smul c μ b

/-! ## The per-base VECTOR regrade of the level-`0` Zhu circle. -/

/-- **The per-base VECTOR regrade of the level-`0` Zhu circle** (FULLY proven; homogeneous `c ∈ 𝒱_M`).
The level-`0` depth-`0` `c`-circle `PresAnm W M 0 0 c b` (mode-value form `∑ᶠ μ, cbz(M, μ+2) • c₍μ₎b`,
`PresAnm_eq_finsum`) regrades by the PROVEN scalar `crossDiff_regrade` into the `(−1)^{n−i} C(n,i)`
-combination of the grade-`(M+i)`, pole-`(i−n+2)` regrade rows:

  `PresAnm W M 0 0 c b
     = ∑_{i<n+1} (−1)^{n−i} C(n,i) • regradeCirc W M n i c b`.

Proof: in mode-value form rewrite each scalar `cbz(M, μ+2)` by `crossDiff_regrade M (μ+2) n` (the
diagonal-shift regrade), turning the inner `μ`-finsum into a finite `i`-sum of scalars; pull the
finite `i`-sum out of the finsum (`finsum_sum_comm`), and identify each per-`i` finsum with
`regradeCirc`.  The single load-bearing input is the PROVEN `crossDiff_regrade`. -/
theorem presAnm_lev0_regrade (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c b : 𝒱) :
    PresAnm W M 0 0 c b
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ)) • regradeCirc W M n i c b := by
  -- the per-`i` regrade-row scalar `μ ↦ cbz(M+i, (μ+2−n)+i)` has finite support.
  have hfin : ∀ i : ℕ, Function.HasFiniteSupport
      (fun μ : ℤ => cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ)) • W.smul c μ b) :=
    fun i => ZhuHR.smul_support_of_scalar W c b _
      (Set.Finite.subset
        (ZhuHR.cbz_shift_support_fin (d := (M : ℤ) + (i : ℤ)) (by positivity)
          (((2 : ℤ) - n) + (i : ℤ)))
        (fun μ hμ => by
          rw [Function.mem_support] at hμ ⊢
          intro h; apply hμ
          rwa [show (μ + ((2 : ℤ) - n)) + (i : ℤ) = μ + (((2 : ℤ) - n) + (i : ℤ)) from by ring]))
  -- mode-value form of the level-`0` depth-`0` circle.
  rw [PresAnm_eq_finsum W M 0 0 c b]
  simp only [Nat.cast_zero]
  -- each scalar `cbz(M, μ+2)` regrades into a finite `i`-sum (PROVEN `crossDiff_regrade`);
  -- distribute the resulting finite sum across the `•`.
  rw [show (∑ᶠ μ : ℤ, cbz (((M : ℤ)) + 0) (μ + (0 + 2) + 0) • W.smul c μ b)
        = ∑ᶠ μ : ℤ,
            ∑ i ∈ Finset.range (n + 1),
              (((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
                  * cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ)))
                • W.smul c μ b from
      finsum_congr fun μ => by
        rw [show cbz (((M : ℤ)) + 0) (μ + (0 + 2) + 0) = cbz (M : ℤ) (μ + 2) from by
            congr 1 <;> · ring,
          crossDiff_regrade (M : ℤ) (μ + 2) n, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((μ + 2) - (n : ℤ)) + (i : ℤ) = (μ + ((2 : ℤ) - n)) + (i : ℤ) from by ring,
          ← smul_smul]]
  -- pull the finite `i`-sum out of the `μ`-finsum.
  rw [finsum_sum_comm (Finset.range (n + 1))
      (fun μ i => (((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
          * cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ))) • W.smul c μ b)
      (fun i _ => Set.Finite.subset (hfin i) (fun μ hμ => by
        simp only [Function.mem_support] at hμ ⊢
        intro h; apply hμ
        rw [show (((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
              * cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ))) • W.smul c μ b
            = ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
              • (cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ)) • W.smul c μ b) from by
            rw [smul_smul], h, smul_zero]))]
  -- identify each per-`i` finsum with the `regradeCirc` row.
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ᶠ μ : ℤ, (((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
              * cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ))) • W.smul c μ b)
        = ∑ᶠ μ : ℤ, ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ))
            • (cbz ((M : ℤ) + (i : ℤ)) ((μ + ((2 : ℤ) - n)) + (i : ℤ)) • W.smul c μ b) from
      finsum_congr fun μ => by rw [smul_smul]]
  rw [regradeCirc, smul_finsum' ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ)) (hfin i)]

/-! ## The VECTOR regrade of `aOutLev0Half` over the `a`-outer multi-base. -/

/-- **The VECTOR regrade of `aOutLev0Half`** (FULLY proven).  Summing the per-base regrade
`presAnm_lev0_regrade` over the `a`-outer modes `bᵢ = a₍i−(n+1)₎d` (weighted by `C(K,i)`) and swapping
the two finite sums, the level-`0` half collapses onto the `(−1)^{n−p} C(n,p)`-combination of the
`a`-outer regrade-row families:

  `aOutLev0Half W n K M a c d
     = ∑_{p<n+1} (−1)^{n−p} C(n,p)
          • (∑_{i≤K} C(K,i) • regradeCirc W M n p c (a₍i−(n+1)₎d))`.

This is the precise regrade-residue isolation of the single genuine residual `aOutLev0Half` of the
`a`-outer `c`-outer U-core (`ZhuVermaAnArchAoutUCore`): the level-`0` half written as a finite
`(−1)^{n−p} C(n,p)`-combination of grade-`(M+p)`, pole-`(p−n+2)` `c`-circles over the `a`-outer
multi-base.  Proof: unfold `aOutLev0Half`, rewrite each per-base level-`0` circle by
`presAnm_lev0_regrade`, distribute the `C(K,i) • (·)` over the finite `p`-sum (`Finset.smul_sum`),
and swap the `i`- and `p`-sums (`Finset.sum_comm`), collecting the `C(n,p)` weight outside. -/
theorem aOutLev0Half_regrade (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutLev0Half W n K M a c d
      = ∑ p ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ (n - p) * (Nat.choose n p : ℂ))
            • ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ)
                  • regradeCirc W M n p c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) := by
  rw [aOutLev0Half]
  -- per `i`, regrade the level-`0` circle and distribute `C(K,i)` over the `p`-sum.
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) • PresAnm W M 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ i ∈ Finset.range (K + 1), ∑ p ∈ Finset.range (n + 1),
            cbz (K : ℤ) (i : ℤ)
              • (((-1 : ℂ) ^ (n - p) * (Nat.choose n p : ℂ))
                  • regradeCirc W M n p c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from
      Finset.sum_congr rfl fun i _ => by
        rw [presAnm_lev0_regrade W M n c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d), Finset.smul_sum]]
  -- swap `i` and `p`, then pull the `C(n,p)` weight outside the `i`-sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

/-! ## The honest residual — `AoutUCoreLev0Core` via the regrade lens + the proven cross-base core.

The vector regrade `aOutLev0Half_regrade` is the PROVEN scalar regrade mechanism `crossDiff_regrade`
lifted to the level-`0` half: it moves the level-`0`-vs-level-`n` `n`-offset onto grade-shifted
(grade-`(M+p)`) regrade rows.  But the per-base lower-`p` rows are pole-shifted (negative effective
level) `c`-circles, NOT level-`n` `c`-towers — engine `certificates/mathematica/vec_regrade_residue2.wl`
(the `p = n` regrade row is NOT the level-`n` circle) / `certificates/mathematica/vec_regrade_residue3.wl` (the single-base
inner pole-difference is NOT a single-base level-`n` `c`-tower).  So the regrade ALONE does not close
the per-base obstruction; the genuine remaining content is the cross-base reorganization of the
regrade rows into the `c₍s₎a` `MGTowerFam`, exactly the single open core `ARDTowerDecomp`
(`ZhuVermaAnArchCrossCFirstGate`).

We re-state the conditional close through this regrade lens, supplying `AoutUCoreLev0Core` from the
genuine cross-base core via the PROVEN `aoutUCoreLev0Core_of_ARDTowerDecomp`
(`ZhuVermaAnArchAoutLev0Slice`), and chaining to the full `MUGradedAction W`. -/

/-- **`AoutUCoreLev0Core` from the cross-base core `ARDTowerDecomp`** (the regrade-lens conditional
close).  The vector regrade `aOutLev0Half_regrade` isolates `aOutLev0Half` as the `(−1)^{n−p} C(n,p)`
-combination of grade-shifted regrade rows; the genuine remaining cross-base reorganization of those
rows into the `c₍s₎a` `MGTowerFam` is the single open core `ARDTowerDecomp`, which discharges
`AoutUCoreLev0Core` through the PROVEN `aoutUCoreLev0Core_of_ARDTowerDecomp`. -/
theorem aoutUCoreLev0Core_of_ARDTowerDecomp_regrade (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {K M P : ℕ} {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ)) (hard : ARDTowerDecomp W n K M P a c d) :
    AoutUCoreLev0Core W n K M P a c d :=
  aoutUCoreLev0Core_of_ARDTowerDecomp W n ha hc hd hard

/-- **The full `MUGradedAction W` from the single universal cross-base core, via the regrade lens.**
Given, for every level `n` and all homogeneous data, the `a`-outer right-action-difference tower
decomposition `ARDTowerDecomp` (the genuine cross-base reorganization of the regrade rows isolated by
`aOutLev0Half_regrade`), `aoutUCoreLev0Core_of_ARDTowerDecomp_regrade` supplies the universal
`AoutUCoreLev0Core`, and the PROVEN `MUGradedAction_of_aOutUCoreLev0Core` (`ZhuVermaAnArchAoutUCore`)
assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` — the `q_act` source of the
bijection `Function.Bijective (forwardMap W)` (Zhu Thm 5.3.4). -/
theorem MUGradedAction_of_ARDTowerDecomp_via_regrade (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_aOutUCoreLev0Core W
    (fun n K M P a ha c hc d hd =>
      aoutUCoreLev0Core_of_ARDTowerDecomp_regrade W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — the VECTOR regrade of the level-`0` half proved; the cross-base core isolated.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`regradeCirc`** — the grade-`(M+p)`, pole-`(p−n+2)` regrade row produced by `crossDiff_regrade`.
* **`presAnm_lev0_regrade`** — **the per-base VECTOR regrade**: the level-`0` depth-`0` `c`-circle
  `PresAnm W M 0 0 c b = ∑_{i<n+1} (−1)^{n−i} C(n,i) • regradeCirc W M n i c b`, the genuine vector
  lift of the PROVEN scalar `crossDiff_regrade`.  Engine-verified (`certificates/mathematica/vec_regrade_residue2.wl`).
* **`aOutLev0Half_regrade`** — **the VECTOR regrade of `aOutLev0Half`** over the `a`-outer multi-base:
  `aOutLev0Half = ∑_{p<n+1} (−1)^{n−p} C(n,p) • (∑_{i≤K} C(K,i) • regradeCirc W M n p c (a₍i−(n+1)₎d))`,
  the precise regrade-residue isolation of the single genuine residual of the `a`-outer `c`-outer
  U-core.
* **`aoutUCoreLev0Core_of_ARDTowerDecomp_regrade`** / **`MUGradedAction_of_ARDTowerDecomp_via_regrade`**
  — the regrade-lens conditional close: `ARDTowerDecomp` ⟹ `AoutUCoreLev0Core` ⟹ `MUGradedAction W`,
  through the PROVEN `aoutUCoreLev0Core_of_ARDTowerDecomp` / `MUGradedAction_of_aOutUCoreLev0Core`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`ARDTowerDecomp W n K M P a c d`.  The regrade `aOutLev0Half_regrade` moves the level-`0`-vs-level-`n`
`n`-offset onto grade-shifted regrade rows (PROVEN), but the lower-`p` rows are pole-shifted (negative
effective level) `c`-circles that no per-base level-`n` `c`-tower absorbs (engine
`certificates/mathematica/vec_regrade_residue2.wl` / `certificates/mathematica/vec_regrade_residue3.wl`); the genuine remaining content is the
cross-base reorganization of those rows into the `c₍s₎a` `MGTowerFam`, the single open core
`ARDTowerDecomp`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.presAnm_lev0_regrade
  #print axioms VOA.aOutLev0Half_regrade
  #print axioms VOA.aoutUCoreLev0Core_of_ARDTowerDecomp_regrade
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_via_regrade
-/
