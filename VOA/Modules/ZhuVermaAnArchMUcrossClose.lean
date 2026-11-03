/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcross
import VOA.Modules.ZhuVermaAnArchMUcirc

/-!
# Game One — the `m = 0` cross-level circle core `CrossCircCore`: homogeneous reduction.

This file works on the last open `MUGradedAction` family of the Dong–Jiang induced module `M(U)`
`V`-action: the **cross-level circle** core `CrossCircCore W n` from `ZhuVermaAnArchMUcross.lean`,

  `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`),

i.e. the outer level-`n` residue (pole `n+1`, the right action `a *^n_0 (·)`) applied to the inner
**level-`0`** Zhu circle generator `anmCirc W 0 0 c d = resHom W 0 2 c d` (pole `2`).  This is the
`m = 0`, mixed-level analogue of the proven left-slot `leftProd_circ_mem_On`
(`ZhuVermaAnDescent4`).

## What is the cross-level subtlety (versus `leftProd_circ_mem_On`)

In `leftProd_circ_mem_On` BOTH circles sit at level `n` (poles `2n+2` and the consistent `circ W n`
weighting), so after the mode-split `a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` the `c`-first inner
sum is *again* a level-`n` circle `circ W n c (a₍α₎d) ∈ Oₙ`.  Here the inner circle is **level `0`**
(pole `2`), so the `c`-first inner sum is the *level-`0`* circle `anmCirc W 0 0 c (a₍α₎d)
= resHom W 0 2 c (a₍α₎d)` — which is NOT in `Onm W n 0` (the `Onm`-circle has pole `n+2`).  The
membership therefore is genuinely carried by the **commutator/iterate family** combining with the
`c`-first family; this is the same cross combinatorial collapse as the still-open shift-`0` tower
predicate `AnmCircTowerEq` (`ZhuVermaAnArchMUcirc`).

## What is proved here (axiom-clean)

* `resHom_zero_right'` — the right-zero helper for `resHom`.
* **`crossCirc_resHom_homog`** — the explicit homogeneous **double-mode-sum** form of the core
  target: for `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`,
  `resHom W 0 (n+1) a (resHom W 0 2 c d)
     = ∑_{i≤K} C(K,i) • a₍i−n−1₎ (∑_{j≤M} C(M,j) • c₍j−2₎ d)`
  (the outer level-`n` residue of the inner level-`0` Zhu circle, both expanded).
* **`CrossCircCoreHM`** — the fully **homogeneous** (in `a, c, d`) core predicate, the precise
  remaining cross combinatorial identity.
* **`CrossCircCore_of_HM`** — the reduction `CrossCircCoreHM W n → CrossCircCore W n` (de-homogenize
  `c` and `d` via `reduce_homogeneous`; the existing `CrossCircCore` already de-homogenizes `a`).

Feeding `CrossCircCore_of_HM` to `anmRight_zero_crossCirc_mem_Onm_of_core`
(`ZhuVermaAnArchMUcross`) discharges (hcrossCirc) — the last `MUGradedAction` family — from the
single fully-homogeneous core `CrossCircCoreHM`.

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized)

`CrossCircCoreHM W n` is reduced (by `crossCirc_resHom_homog`) to the membership of the explicit
double-mode-sum.  By the mode-split `a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` it splits into the
`c`-first family (a level-`0` circle family) and the Borcherds commutator/iterate family; their
combination collapses onto `PresAnm`-towers (via `Pres_mem_Onm`, `ZhuVermaAnArchMUcirc`) exactly as
in the shift-`0` tower predicate.  This is the genuine cross combinatorial collapse — the same
content as `AnmCircTowerEq` — and is engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/mucross_circ.wl`: `n = 1, a = c = d = J` and `n = 2` both land in `Onm10`/
`Onm20`).  It is left as the precise stated `CrossCircCoreHM` target, NOT a `sorry`/axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Right-zero helper for `resHom`. -/

@[simp] theorem resHom_zero_right' (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (a : 𝒱) :
    resHom W s p a (0 : 𝒱) = 0 := by
  have h := resHom_smul_right W s p (0 : ℂ) a (0 : 𝒱)
  rwa [zero_smul, zero_smul] at h

/-! ## The explicit homogeneous double-mode-sum form of the cross-level circle core. -/

/-- **The explicit homogeneous double-mode-sum form of the cross-level circle core.**  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, expanding the outer level-`n` residue (pole `n+1`)
and the inner level-`0` Zhu circle (pole `2`) gives
`resHom W 0 (n+1) a (resHom W 0 2 c d)
   = ∑_{i≤K} C(K,i) • a₍i−n−1₎ (∑_{j≤M} C(M,j) • c₍j−2₎ d)`.

Proof: `resHom_homogeneous` on the outer residue (`s = 0`, `p = n+1`, `(K+0).toNat+1 = K+1`) and on
the inner residue (`s = 0`, `p = 2`, `(M+0).toNat+1 = M+1`). -/
theorem crossCirc_resHom_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            W.smul a ((i : ℤ) - ((n : ℤ) + 1))
              (∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ) • W.smul c ((j : ℤ) - 2) d) := by
  -- inner level-`0` Zhu circle expansion.
  have hinner : resHom W 0 2 c d
      = ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) • W.smul c ((j : ℤ) - 2) d := by
    rw [resHom_homogeneous W 0 2 hc d]
    simp only [add_zero]
    rw [show ((M : ℤ)).toNat + 1 = M + 1 from by rw [Int.toNat_natCast]]
  rw [hinner]
  -- outer level-`n` residue expansion.
  rw [resHom_homogeneous W 0 ((n : ℤ) + 1) ha _]
  simp only [add_zero]
  rw [show ((K : ℤ)).toNat + 1 = K + 1 from by rw [Int.toNat_natCast]]

/-! ## The fully-homogeneous cross-level circle core and the de-homogenization in `c`, `d`. -/

/-- **The fully-homogeneous cross-level circle core** (`Prop`): for homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`,
`resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`.  This is the precise remaining cross
combinatorial identity (the `m = 0`, mixed-level analogue of `leftProd_circ_mem_On_homog`), engine-
verified TRUE on the rank-1 free boson (`certificates/mathematica/mucross_circ.wl`).  Its membership is
carried by the `c`-first level-`0` circle family combining with the Borcherds commutator/iterate
family, collapsing onto `PresAnm`-towers (`Pres_mem_Onm`) — the same cross collapse as
`AnmCircTowerEq`. -/
def CrossCircCoreHM (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ),
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0

/-- **`CrossCircCoreHM W n → CrossCircCore W n`.**  The existing `CrossCircCore` (which already
de-homogenizes `a`, `ZhuVermaAnArchMUcross`) follows from the fully-homogeneous core by reducing
both `c` and `d` to homogeneous slices (`reduce_homogeneous`); on negative grades the slice is `0`
and `resHom`'s bilinearity (`resHom_zero_left'`/`resHom_zero_right'`/`resHom_add_*`) finishes. -/
theorem CrossCircCore_of_HM (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (hHM : CrossCircCoreHM W n) :
    CrossCircCore W n := by
  intro K a ha c d
  -- reduce `c` to homogeneous.
  refine reduce_homogeneous W
    (P := fun c => resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0) ?_ ?_ ?_ c
  · intro Mc c hcM
    rcases le_or_gt 0 Mc with hMnn | hMneg
    · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMnn
      -- reduce `d` to homogeneous.
      refine reduce_homogeneous W
        (P := fun d => resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0) ?_ ?_ ?_ d
      · intro Pd d hdP
        rcases le_or_gt 0 Pd with hPnn | hPneg
        · obtain ⟨P, rfl⟩ := Int.eq_ofNat_of_zero_le hPnn
          exact hHM K M P a ha c hcM d hdP
        · have hzero : d = 0 := by
            have : d ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Pd hPneg]; exact hdP
            simpa using this
          rw [hzero, resHom_zero_right', resHom_zero_right']
          exact (Onm W n 0).zero_mem
      · change resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c (0 : 𝒱)) ∈ Onm W n 0
        rw [resHom_zero_right', resHom_zero_right']
        exact (Onm W n 0).zero_mem
      · intro x y hx hy
        change resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c (x + y)) ∈ Onm W n 0
        rw [resHom_add_right, resHom_add_right]
        exact (Onm W n 0).add_mem hx hy
    · -- `Mc < 0`: the grading is `⊥`, the slice is `0`.
      have hzero : c = 0 := by
        have : c ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Mc hMneg]; exact hcM
        simpa using this
      rw [hzero, resHom_zero_left', resHom_zero_right']
      exact (Onm W n 0).zero_mem
  · change resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 (0 : 𝒱) d) ∈ Onm W n 0
    rw [resHom_zero_left', resHom_zero_right']
    exact (Onm W n 0).zero_mem
  · intro x y hx hy
    change resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 (x + y) d) ∈ Onm W n 0
    rw [resHom_add_left, resHom_add_right]
    exact (Onm W n 0).add_mem hx hy

/-! ## Status — the last Game-One cross family reduced to ONE fully-homogeneous core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* `resHom_zero_right'` — right-zero helper.
* **`crossCirc_resHom_homog`** — the explicit homogeneous double-mode-sum form of the core target.
* **`CrossCircCoreHM`** — the fully-homogeneous (in `a, c, d`) cross-level circle core.
* **`CrossCircCore_of_HM`** — reduces the consumed `CrossCircCore W n`
  (`anmRight_zero_crossCirc_mem_Onm_of_core`, `ZhuVermaAnArchMUcross`) to `CrossCircCoreHM W n`, by
  de-homogenizing `c` and `d`.

**Remaining core (engine-verified TRUE, free boson; NOT faked):** `CrossCircCoreHM W n` — the
fully-homogeneous cross-level residue-of-residue membership
`resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`.  By `crossCirc_resHom_homog` this is the
membership of the explicit double-mode-sum; via the mode-split
`a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` it is the `c`-first level-`0` circle family combining
with the Borcherds commutator/iterate family, collapsing onto `PresAnm`-towers (`Pres_mem_Onm`,
`ZhuVermaAnArchMUcirc`) — the same cross combinatorial collapse as the shift-`0` tower predicate
`AnmCircTowerEq`.  Engine value (`certificates/mathematica/mucross_circ.wl`): for `n = 1, a = c = d = J`
the residue-of-residue lands in `Onm W 1 0`; likewise `n = 2`.  Discharging `CrossCircCoreHM` closes
(hcrossCirc) outright via
`anmRight_zero_crossCirc_mem_Onm_of_core W n (CrossCircCore_of_HM W n ·)`, supplying the last
`MUGradedAction` family of the DJ `M(U)` `V`-action crux.
-/

end VOA
