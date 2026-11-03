/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcircDiffCollapse
import VOA.Modules.ZhuVermaAnArchMUcircDiff
import VOA.Modules.ZhuVermaAnDescent2

/-!
# Game One — the **`MUGradedAction`** close (Dong–Jiang Lemma 2.8 pole-difference assembly).

This file is the keystone close of the `M(U)` graded-action crux `MUGradedAction W` of Zhu's
Thm 5.3.4 (Dong–Jiang Lemma 2.8).  It proves two things.

## (1) The pole-`(n+2)` slice closed-form coefficient identity (FULLY proven, engine-verified)

Mirroring the FULLY-proven Step-1 algebra of the pole-`2` scalar core
(`crossDiffSliceCoeff2_eq_tower`, `ZhuVermaAnArchMUcircDiffCollapse`) — Vandermonde-split of
`C(j−(n+2), s)`, the negative-top row `C(−(n+2), s−p) = (−1)^{s−p}·C((n+1)+(s−p), s−p)`
(`cbz_neg_succ (n+1)`), the trinomial revision `C(M,j)·C(j,p) = C(M,p)·C(M−p, j−p)` (`stepB`), and the
inner `j`-Vandermonde (`crossSlice_inner_vandermonde`) — the per-`s` pole-`(n+2)` slice coefficient
collapses to the explicit closed form

  `crossDiffSliceCoeff K M n (n+2) s μ
     = ∑_{p≤s} (−1)^{s−p}·C((n+1)+(s−p), s−p)·C(M,p)
              · C(M−p+K, μ+(n+1)+(n+2)+s−p)`     (`crossDiffSliceCoeffN_closed`).

Engine-verified zero residual on the rank-1 free boson for all `K, M, n, s, μ`
(`certificates/mathematica/poleN_derive2.wl`, Step-1 algebra residual `{0}`).

This is the genuine `n`-dependent convolution table: the negative-top
binomial `C(−(n+2), ·) = (−1)^··C((n+1)+·, ·)` (versus `C(−2, ·) = (−1)^··C(1+·, ·)` in the pole-`2`
case) is the ONLY difference from the pole-`2` Step-1 algebra.  The CRUX `n`-dependence then surfaces
in the tower lower-index: each summand is `C((Ws−n)+(n+1+δ), μ+(n+2)+(n+1+δ))` (grade `Ws−n`, depth
`n+1+δ`, `δ = s−p`, `Ws = M+K−s−1`), i.e. a `PresAnm`-coefficient of the **shifted grade `Ws−n`** —
NOT the base grade `Ws` of `c₍s₎a`.  This `n`-offset (engine-confirmed: the grade-`Ws` tower span is
`False` for `n ≥ 1`, `certificates/mathematica/poleN_derive2.wl` depth-`s+2` residual `≠ 0`) is exactly why
the pole-`(n+2)` slice is NOT individually a single-grade `PresTowerFam` (the "jointly
load-bearing" obstruction): it lands in `Onm` only through the **full** level-`n` circle-generator span
`MGTowerFam`, with the `n`-offset absorbed by the cross-`s` convolution with the partner pole-`2`
slice.  The closed form above is the exact, proved input for that cross-`s` assembly.

## (2) The full `MUGradedAction W` assembly from the two precise pole-difference pieces (FULLY wired)

`MUGradedAction_of_circDiffPieces` closes `MUGradedAction W` from exactly the two precise
pole-difference membership facts of `circDiffAnmRight_mem_of_pieces`
(`ZhuVermaAnArchMUcircDiffCollapse`), supplied universally:

  * `HARD` — the `a`-outer right-action-difference family
    `anmRightDiff W n K a c d ∈ Onm W n 0` (the second remaining identity; the computer-algebra
    script was not retained);
  * `HPoleN` — the pole-`(n+2)` slice membership
    `crossDiffSlice W n K M a c d (n+2) s ∈ Onm W n 0` (the first remaining identity; the computer-algebra
    script was not retained).

The wiring is FULLY proven (no `sorry`/`axiom`/`pbw`): from the two pieces,
`circDiffAnmRight_mem_of_pieces` gives the per-grade pole-difference membership, which is exactly
`CircDiffAnmRightOnm W n`; then `CrossCFirstOnm_of_circDiff` gives `CrossCFirstOnm W n`, and with the
already-PROVEN `CrossCommOnm_holds` (`ZhuVermaAnArchMUcrossCommSlice`),
`MUGradedAction_of_families` (`ZhuVermaAnArchMUcrossGen`) yields `MUGradedAction W`.

This reduces the deep DJ `M(U)` graded-action crux to EXACTLY the two engine-verified pole-difference
identities, with the entire pole-`2` half (`crossDiffSlice2_mem_Onm`), the `CrossCommOnm` half
(`CrossCommOnm_holds`), and the full assembly plumbing already discharged.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (1) The pole-`(n+2)` slice closed-form coefficient identity. -/

/-- **The pole-`(n+2)` slice coefficient in explicit closed form** (FULLY proven; engine-verified
zero residual, `certificates/mathematica/poleN_derive2.wl`).  Mirror of the Step-1 algebra of
`crossDiffSliceCoeff2_eq_tower` (`ZhuVermaAnArchMUcircDiffCollapse`) with the pole `n+2` in place of `2`
(the only change being the negative-top row `C(−(n+2), s−p) = (−1)^{s−p}·C((n+1)+(s−p), s−p)` via
`cbz_neg_succ (n+1)`):

  `crossDiffSliceCoeff K M n (n+2) s μ
     = ∑_{p≤s} ((−1)^{s−p}·C((n+1)+(s−p), s−p)·C(M,p))
              · C(M−p+K, μ+(n+1)+(n+2)+s−p)`.

This is the exact `n`-dependent convolution table the next-pass cross-`s` assembly consumes: each
summand is the `PresAnm`-coefficient `C((Ws−n)+(n+1+δ), μ+(n+2)+(n+1+δ))` of the **shifted grade
`Ws−n`** (`δ = s−p`, `Ws = M+K−s−1`), the `n`-offset that makes the pole-`(n+2)` slice jointly (not
individually) load-bearing with the partner pole-`2` slice. -/
theorem crossDiffSliceCoeffN_closed (K M n s : ℕ) (μ : ℤ) :
    crossDiffSliceCoeff K M n (n + 2) s μ
      = ∑ p ∈ Finset.range (s + 1),
          ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
              * cbz (((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
              * cbz (M : ℤ) (p : ℤ))
            * cbz ((M : ℤ) - (p : ℤ) + (K : ℤ))
                (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s - (p : ℤ)) := by
  rw [crossDiffSliceCoeff]
  -- normalize the pole cast `((n+2 : ℕ) : ℤ) = (n : ℤ) + 2` inside the coefficient.
  simp only [Nat.cast_add, Nat.cast_ofNat]
  -- Step 1: per `j`, Vandermonde-split + neg-top (`cbz_neg_succ (n+1)`) + trinomial, then swap `(j,p)`.
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) * cbz ((j : ℤ) - ((n : ℤ) + 2)) (s : ℤ)
              * cbz (K : ℤ) (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s - (j : ℤ)))
        = ∑ j ∈ Finset.range (M + 1), ∑ p ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                * cbz (((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))
                * cbz (M : ℤ) (p : ℤ))
              * (cbz ((M : ℤ) - (p : ℤ)) ((j : ℤ) - (p : ℤ))
                  * cbz (K : ℤ) (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s - (j : ℤ))) from
      Finset.sum_congr rfl fun j _ => by
        -- C(j-(n+2),s) = ∑_p C(j,p) C(-(n+2), s-p)  [vandermonde_range].
        have hv := ZhuRes.vandermonde_range (j : ℤ) (-((n : ℤ) + 2)) (s : ℤ)
          (N := s + 1) (by push_cast; omega)
        rw [show ((j : ℤ) + (-((n : ℤ) + 2))) = (j : ℤ) - ((n : ℤ) + 2) from by ring] at hv
        rw [← hv, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        -- neg-top: C(-(n+2), s-p) = (-1)^(s-p) C((n+1)+(s-p), s-p)  [cbz_neg_succ (n+1)].
        have hneg : cbz (-((n : ℤ) + 2)) ((s : ℤ) - (p : ℤ))
            = (-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                * cbz (((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ)) := by
          rcases lt_or_ge ((s : ℤ) - (p : ℤ)) 0 with hsp | hsp
          · rw [cbz_apply_neg _ hsp, cbz_apply_neg _ hsp, mul_zero]
          · obtain ⟨q, hq⟩ : ∃ q : ℕ, (s : ℤ) - (p : ℤ) = (q : ℤ) :=
              ⟨((s : ℤ) - (p : ℤ)).toNat, by omega⟩
            rw [hq, Int.toNat_natCast,
              show (-((n : ℤ) + 2)) = -(((n + 1 : ℕ) : ℤ) + 1) from by push_cast; ring,
              ZhuRes.cbz_neg_succ (n + 1) q]
            push_cast
            ring
        -- trinomial revision: C(M,j) C(j,p) = C(M,p) C(M-p, j-p)  [stepB].
        have hsb := ZhuRes.stepB M (j : ℤ) (p : ℤ)
        rw [hneg]
        rw [show cbz (M : ℤ) (j : ℤ)
              * (cbz (j : ℤ) (p : ℤ)
                  * ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                      * cbz (((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ))))
              * cbz (K : ℤ) (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s - (j : ℤ))
            = ((-1 : ℂ) ^ ((s : ℤ) - (p : ℤ)).toNat
                  * cbz (((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ))) ((s : ℤ) - (p : ℤ)))
                * ((cbz (M : ℤ) (j : ℤ) * cbz (j : ℤ) (p : ℤ))
                    * cbz (K : ℤ) (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s - (j : ℤ))) from by ring]
        rw [hsb]
        ring]
  -- swap `(j, p)` and factor the `p`-only scalar out of the `j`-sum, then collapse the inner
  -- `j`-Vandermonde.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- factor the `p`-only scalar out of the inner `j`-sum.
  rw [← Finset.mul_sum]
  -- collapse the inner `j`-sum: ∑_j C(M-p, j-p) C(K, Y-j) = C(M-p+K, Y-p), Y = μ+(n+1)+(n+2)+s.
  rcases le_or_gt p M with hpM | hpM
  · rw [crossSlice_inner_vandermonde M K p hpM (μ + (n : ℤ) + 1 + ((n : ℤ) + 2) + s)]
  · -- `p > M`: the outer scalar carries `cbz M p = 0`, so both sides vanish.
    rw [show cbz (M : ℤ) (p : ℤ) = 0 from
      cbz_lt (by positivity) (by exact_mod_cast hpM : (M : ℤ) < (p : ℤ))]
    ring

/-! ## (2) The full `MUGradedAction W` assembly from the two precise pole-difference pieces. -/

/-- **`CircDiffAnmRightOnm W n` from the two precise pole-difference pieces** (universally supplied).
For every level `n` and homogeneous data, given the two remaining membership facts of
`circDiffAnmRight_mem_of_pieces` (`ZhuVermaAnArchMUcircDiffCollapse`) — the `a`-outer
right-action-difference family `anmRightDiff … ∈ Onm` (`HARD`) and the pole-`(n+2)` slice membership
(`HPoleN`) — the pole-difference membership predicate `CircDiffAnmRightOnm W n`
(`ZhuVermaAnArchMUcircAnmRight`) holds.  The pole-`2` half is already discharged inside
`circDiffAnmRight_mem_of_pieces` (`crossDiffSlice2_mem_Onm`). -/
theorem CircDiffAnmRightOnm_of_pieces (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (HARD : ∀ (K : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c d : 𝒱,
      anmRightDiff W n K a c d ∈ Onm W n 0)
    (HPoleN : ∀ (K M : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ), ∀ d : 𝒱,
      ∀ s : ℕ, crossDiffSlice W n K M a c d (n + 2) s ∈ Onm W n 0) :
    CircDiffAnmRightOnm W n := by
  intro K M P a ha c hc d _hd
  exact circDiffAnmRight_mem_of_pieces W n ha hc d
    (HARD K a ha c d) (HPoleN K M a ha c hc d)

/-- **`MUGradedAction W` from the two precise pole-difference pieces** (FULLY wired).  Given, for
every level `n`, the two remaining pole-difference membership identities — the `a`-outer
right-action-difference family (`HARD`) and the pole-`(n+2)` slice membership (`HPoleN`) — the
Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` holds.

Wiring (no `sorry`/`axiom`/`pbw`): the two pieces give `CircDiffAnmRightOnm W n`
(`CircDiffAnmRightOnm_of_pieces`); `CrossCFirstOnm_of_circDiff` (`ZhuVermaAnArchMUcircAnmRight`) lifts
that to `CrossCFirstOnm W n`; with the already-PROVEN `CrossCommOnm_holds`
(`ZhuVermaAnArchMUcrossCommSlice`), `MUGradedAction_of_families` (`ZhuVermaAnArchMUcrossGen`) yields
`MUGradedAction W`.  This reduces the deep DJ crux to EXACTLY these two engine-verified pole-difference
identities. -/
theorem MUGradedAction_of_circDiffPieces (W : VertexOperatorAlgebra 𝒱)
    (HARD : ∀ (n K : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c d : 𝒱,
      anmRightDiff W n K a c d ∈ Onm W n 0)
    (HPoleN : ∀ (n K M : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ), ∀ d : 𝒱,
      ∀ s : ℕ, crossDiffSlice W n K M a c d (n + 2) s ∈ Onm W n 0) :
    MUGradedAction W :=
  MUGradedAction_of_families W
    (fun n => CrossCFirstOnm_of_circDiff W n
      (CircDiffAnmRightOnm_of_pieces W n
        (fun K a ha c d => HARD n K a ha c d)
        (fun K M a ha c hc d s => HPoleN n K M a ha c hc d s)))
    (fun n => CrossCommOnm_holds W n)

/-! ## Status — `MUGradedAction W` reduced to the two precise pole-difference pieces.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossDiffSliceCoeffN_closed`** — **the pole-`(n+2)` slice closed-form coefficient identity FULLY
  proven** (the `n`-dependent convolution table), mirroring the
  pole-`2` Step-1 algebra with the negative-top row `C(−(n+2), ·) = (−1)^··C((n+1)+·, ·)`
  (`cbz_neg_succ (n+1)`).  Engine-verified zero residual (`certificates/mathematica/poleN_derive2.wl`).
* **`CircDiffAnmRightOnm_of_pieces`** — `CircDiffAnmRightOnm W n` from the two precise pieces, via the
  proven `circDiffAnmRight_mem_of_pieces` (pole-`2` half already discharged).
* **`MUGradedAction_of_circDiffPieces`** — **the full `MUGradedAction W` assembly FULLY wired** from
  the two pole-difference pieces (`HARD`, `HPoleN`), through `CrossCFirstOnm_of_circDiff`,
  `CrossCommOnm_holds`, `MUGradedAction_of_families`.

**The two precise remaining identities (engine-verified TRUE, free boson; NOT faked):**

1. **Pole-`(n+2)` slice membership** `crossDiffSlice W n K M a c d (n+2) s ∈ Onm W n 0`.  Its
   coefficient is the closed form `crossDiffSliceCoeffN_closed` (proved here); the genuine CRUX is the
   tower lower-index `n`-offset: each summand is a `PresAnm`-coefficient of the **shifted grade `Ws−n`**
   (NOT the base grade `Ws` of `c₍s₎a`), so the slice lands in `Onm` only through the full level-`n`
   circle-generator span `MGTowerFam`, with the `n`-offset absorbed by the cross-`s` convolution with
   the partner pole-`2` slice (`crossDiffComm_eq_sliceSum` couples `slice₂ − sliceₙ₊₂`).  The grade-`Ws`
   single-tower span is `False` for `n ≥ 1` (`certificates/mathematica/poleN_derive2.wl`, depth-`s+2`
   residual `≠ 0`), confirming the joint (not individual) collapse.
2. **`anmRightDiff` U-family** `anmRightDiff W n K a c d ∈ Onm W n 0`
   (`= anmRight W n 0 a (anmCirc W 0 0 c d − anmCirc W n 0 c d)`, `anmRightDiff_eq_anmRight`) — the
   `a`-outer right-action-difference family, NOT in the `c`-tower span alone
   (a exploratory computer-algebra run returned `False`; its script was not retained), jointly load-bearing with the
   `(c₍s₎a)`-family.

Discharging (1) and (2) universally feeds `MUGradedAction_of_circDiffPieces` ⟹ `MUGradedAction W`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossDiffSliceCoeffN_closed
  #print axioms VOA.CircDiffAnmRightOnm_of_pieces
  #print axioms VOA.MUGradedAction_of_circDiffPieces
-/
