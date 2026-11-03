/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LeeYangRigidity
import VOA.Core.Reconstruction

/-!
# The level-4 Gram matrix of `V(c,0)`: an explicit nonzero entry, and the Lee–Yang values

## Why this file exists

`Examples/LeeYangRigidity.shapForm_leeYang_degenerate` proves that the level-4 Shapovalov form
of `V(-22/5, 0)` is **degenerate**.  Taken alone that statement does not distinguish the
interesting reason (a Kac-determinant zero: a nonzero form with a null direction) from the
trivial one (the identically zero form, which is degenerate for free).  It therefore may not be
quoted as `det M₄(-22/5) = 0` until one exhibits a **nonzero** entry of the Gram matrix.

This file computes one, from the repository's own definitions:

`⟨L₋₄|0⟩ , L₋₄|0⟩⟩₄ = ε( (L₋₄|0⟩)₍₇₎ (L₋₄|0⟩) ) = 105·c`,  hence `-462 ≠ 0` at `c = -22/5`.

## ⚠ Normalisation: `105c`, **not** `5c`

The textbook contravariant Virasoro Gram entry is `(c/12)(n³-n)`, which at `n = 4` is `5c`.  That
value belongs to the *contravariant* form defined by the adjoint `Lₙ† = L₋ₙ` with `⟨0|0⟩ = 1`.
`RigidBridge.shapForm` is instead defined by the **top mode**, `⟨a,b⟩ₖ := ε(a₍₂ₖ₋₁₎b)`, and the two
agree (up to the sign `(-1)^{k+1}`) only on *quasi-primary* vectors — `invariantForm_eq_shapForm`
carries the hypothesis `L₁ s = 0`.  `L₋₄|0⟩` is **not** quasi-primary: `Lop_one_L4vac` gives
`L₁L₋₄|0⟩ = 5L₋₃|0⟩ ≠ 0`.  The mismatch is the factor `21` computed in §3, and it is real:

`L₋₄|0⟩ = ω₍₋₃₎|0⟩ = T²ω/2!`, so `(L₋₄|0⟩)₍₇₎ = (T²ω)₍₇₎/2 = ((-7)(-6)/2)·ω₍₅₎ = 21·L₄`,

whence `(L₋₄|0⟩)₍₇₎(L₋₄|0⟩) = 21·L₄L₋₄|0⟩ = 21·5c·|0⟩ = 105c·|0⟩`.

Two internal checks of the convention are proved here rather than asserted:

* §2 `shapForm_omegaVir_self` — at level `2`, where the state `ω = L₋₂|0⟩` **is** quasi-primary
  (`Lop_one_L2vac`), the same definition returns the textbook value `⟨ω,ω⟩₂ = c/2 = (c/12)(2³-2)`
  on the nose.  So `shapForm` is *not* globally rescaled; the level-4 factor `21` is exactly the
  non-quasi-primarity of `L₋₄|0⟩`.
* §6 `shapForm_leeYang_level4_eq_kac` — the full level-4 Gram matrix at `c = -22/5` is `21 ×` the
  textbook Kac matrix `[[(c/2)(c+8), 3c], [3c, 5c]]`.  (This check is scale-invariant, so it
  confirms *proportionality* to the Kac matrix — and thereby that `c = -22/5` is a Kac root — but
  not the constant `21` itself, which comes from the direct computation of §3.)

## Main results

* `smul_omegaVir` — `ω₍ₙ₎ = L_{n-1}` on `V(c,0)` (the mode shift, at the VOA level).
* `shapForm_omegaVir_self` — `⟨ω,ω⟩₂ = c/2`: the level-2 normalisation check.
* `Lop_neg_one_L3vac` — `L₋₁L₋₃|0⟩ = 2L₋₄|0⟩`.
* `Tpow_two_omegaVir` — `T²ω = 2·L₋₄|0⟩`: `L₋₄|0⟩` is a translate of the conformal vector.
* `Lop_four_L4vac` — `L₄L₋₄|0⟩ = 5c·|0⟩` (the `(c/12)(4³-4)` central term).
* `smul_L4vac_seven` — `(L₋₄|0⟩)₍₇₎ v = 21·L₄ v` for every `v`; the factor `21`.
* `shapForm_L4vac_self` — **the Gram entry**: `⟨L₋₄|0⟩, L₋₄|0⟩⟩₄ = 105c`, for arbitrary `c`.
* `leeYangGram_L4vac` — its Lee–Yang value `105·(-22/5) = -462 ≠ 0`.
* `shapForm_leeYang_ne_zero` — hence the level-4 Shapovalov form of `V(-22/5,0)` is **not**
  the zero form (`shapForm_leeYang_exists_ne_zero` is the explicit-witness restatement).
* `shapForm_leeYang_degenerate_and_ne_zero` — **degenerate *and* nonzero**.  This is the
  statement that licenses quoting the level-4 result as a Kac-determinant phenomenon: the
  determinant vanishes on a form that is not itself zero.
* `radBil_shapForm_leeYang_proper` — the same content as a subspace statement: the radical is
  neither `⊥` (that is the degeneracy) nor `⊤` (that is the nonvanishing).
* `shapForm_L2L2vac_L4vac_leeYang`, `shapForm_L2L2vac_self_leeYang` — the other two entries of the
  level-4 Gram matrix at `c = -22/5`, obtained from the one computed entry together with the
  already-proved fact that the singular vector is in the radical.
* `shapForm_leeYang_level4_eq_kac` — the whole matrix, compared with the textbook Kac matrix.

## Status
No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axiom;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every declaration below, so the
theorem `VOA.pbw` is **not** used.
-/

namespace VOA

open VOA.VirModule
open RigidBridge

namespace LeeYang

variable (c : ℂ)

/-! ## §1  The modes of `ω` on `V(c,0)`

`Core.RigidityBridge.shapForm` pairs weight-`k` states with the **top mode** `(·)₍₂ₖ₋₁₎`.  For
`k = 2` that mode is `(·)₍₃₎` and for `k = 4` it is `(·)₍₇₎`.  Both computations below start from
the same fact: the VOA modes of the conformal vector are the abstract Virasoro operators, shifted
by one. -/

/-- **`ω₍ₙ₎ = L_{n-1}`** on `V(c,0)`: the VOA mode of the conformal vector is the abstract
Virasoro mode, with the standard shift (`W.L n = ω₍ₙ₊₁₎`, `virasoroVOA_L_eq_Lop`). -/
theorem smul_omegaVir (n : ℤ) (v : VirUniv c) :
    (virasoroVOA c).smul (omegaVir c) n v = Lop c (n - 1) v := by
  have hom : (virasoroVOA c).conformalVector = omegaVir c := rfl
  rw [← virasoroVOA_L_eq_Lop, VertexOperatorAlgebra.L_def, hom, PreVertexAlgebra.smul_def,
    show (n - 1 + 1) = n from by ring]

/-! ## §2  The level-2 normalisation check

`ω = L₋₂|0⟩` **is** quasi-primary (`Lop_one_L2vac : L₁ω = 0`), so at level `2` the top-mode form
and the textbook contravariant form must agree exactly.  They do: both give `c/2`.  This pins the
convention, and shows that the factor `21` appearing at level `4` in §3 is not a global rescaling
of `shapForm` but genuinely the failure of `L₋₄|0⟩` to be quasi-primary. -/

/-- **The level-2 Gram entry** `⟨ω,ω⟩₂ = ε(ω₍₃₎ω) = ε(L₂L₋₂|0⟩) = c/2`, exactly the textbook
`(c/12)(2³-2) = c/2`. -/
theorem shapForm_omegaVir_self (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 2 ⟨omegaVir c, omegaVir_mem_gradingVir_two c⟩
        ⟨omegaVir c, omegaVir_mem_gradingVir_two c⟩ = c / 2 := by
  have h : (virasoroVOA c).smul (omegaVir c) 3 (omegaVir c) = (c / 2) • vacVec c := by
    rw [smul_omegaVir, show ((3 : ℤ) - 1) = 2 from by norm_num]
    exact Lop_two_L2vac c
  rw [shapForm_eq_iff, show (2 * (2 : ℤ) - 1) = 3 from by norm_num]
  exact h

/-! ## §3  `L₋₄|0⟩` is a translate of `ω`, and its Shapovalov mode

`T = L₋₁` (`T_eq_Lneg1`) and `[L₋₁, L₋ₙ] = (n-1)L₋ₙ₋₁`, so applying `T` twice to `ω = L₋₂|0⟩`
produces `2·L₋₄|0⟩`.  That lets `Core.Reconstruction.smul_Tpow` trade the mode `(L₋₄|0⟩)₍₇₎` for
the mode `ω₍₅₎ = L₄`, at the cost of the numerical factor `(-(7-0))·(-(7-1))/2! = 21`. -/

/-- `L₋₁L₋₃|0⟩ = 2L₋₄|0⟩`, from `[L₋₁,L₋₃] = 2L₋₄` and `L₋₁|0⟩ = 0`. -/
theorem Lop_neg_one_L3vac : Lop c (-1) (L3vac c) = (2 : ℂ) • L4vac c := by
  have h := Lop_apply_comm c (-1) (-3) (vacVec c)
  rw [if_neg (by norm_num : ¬((-1 : ℤ) + -3 = 0)), zero_smul,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ -1), map_zero,
    show (-1 : ℤ) + -3 = -4 from by norm_num] at h
  push_cast at h
  simp only [L3vac, L4vac]
  rw [h]
  module

/-- **`T²ω = 2·L₋₄|0⟩`.**  Equivalently `L₋₄|0⟩ = ω₍₋₃₎|0⟩ = T²ω/2!`, the creation formula. -/
theorem Tpow_two_omegaVir :
    (((virasoroVOA c).toPreVertexAlgebra.T) ^ 2) (omegaVir c) = (2 : ℂ) • L4vac c := by
  rw [VertexOperatorAlgebra.T_eq_Lneg1, virasoroVOA_L_eq_Lop, pow_two, Module.End.mul_apply,
    show omegaVir c = L2vac c from rfl, Lop_neg_one_L2vac, Lop_neg_one_L3vac]

/-- `L₄L₋₄|0⟩ = 5c·|0⟩`: the central term `(c/12)(4³-4) = 5c` of `[L₄, L₋₄]`, with both
boundary terms killed by `Lₙ|0⟩ = 0` for `n ≥ -1`. -/
theorem Lop_four_L4vac : Lop c 4 (L4vac c) = (5 * c) • vacVec c := by
  have h := Lop_apply_comm c 4 (-4) (vacVec c)
  rw [if_pos (by norm_num : (4 : ℤ) + -4 = 0),
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 4), map_zero,
    show (4 : ℤ) + -4 = 0 from by norm_num,
    Lop_vacuum c (by norm_num : (-1 : ℤ) ≤ 0), smul_zero] at h
  push_cast at h
  norm_num at h
  simp only [L4vac]
  rw [h]

/-- **The factor `21`.**  `(L₋₄|0⟩)₍₇₎ = 21·L₄` as an operator on `V(c,0)`.

`smul_Tpow` gives `(T²ω)₍₇₎ = (-(7-0))·(-(7-1))·ω₍₅₎ = 42·ω₍₅₎`, and `T²ω = 2·L₋₄|0⟩`. -/
theorem smul_L4vac_seven (v : VirUniv c) :
    (virasoroVOA c).smul (L4vac c) 7 v = (21 : ℂ) • Lop c 4 v := by
  have hT := VertexOperatorAlgebra.smul_Tpow (virasoroVOA c) (omegaVir c) v 2 7
  rw [Tpow_two_omegaVir, PreVertexAlgebra.smul_smul_left,
    show ((7 : ℤ) - ((2 : ℕ) : ℤ)) = 5 from by norm_num, smul_omegaVir,
    show ((5 : ℤ) - 1) = 4 from by norm_num,
    show (∏ i ∈ Finset.range 2, (-((7 : ℤ) - (i : ℤ)))) = 42 from by decide,
    ← Int.cast_smul_eq_zsmul ℂ (42 : ℤ)] at hT
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  refine smul_right_injective (VirUniv c) h2 ?_
  change (2 : ℂ) • (virasoroVOA c).smul (L4vac c) 7 v = (2 : ℂ) • (21 : ℂ) • Lop c 4 v
  rw [hT, smul_smul]
  norm_num

/-- The self-pairing top product: `(L₋₄|0⟩)₍₇₎(L₋₄|0⟩) = 105c·|0⟩`. -/
theorem smul_L4vac_seven_self :
    (virasoroVOA c).smul (L4vac c) 7 (L4vac c) = (105 * c) • vacVec c := by
  rw [smul_L4vac_seven, Lop_four_L4vac, smul_smul]
  congr 1
  ring

/-! ## §4  The Gram entry -/

/-- `L₋₂L₋₂|0⟩` as an element of the weight-4 space `𝒱₄`. -/
noncomputable def L2L2vec4 : (virasoroVOA c).grading 4 :=
  ⟨L2L2vac c, L2L2vac_mem_grading c⟩

/-- `L₋₄|0⟩` as an element of the weight-4 space `𝒱₄`. -/
noncomputable def L4vec4 : (virasoroVOA c).grading 4 :=
  ⟨L4vac c, L4vac_mem_grading c⟩

@[simp] theorem L2L2vec4_coe : ((L2L2vec4 c : (virasoroVOA c).grading 4) : VirUniv c)
    = L2L2vac c := rfl

@[simp] theorem L4vec4_coe : ((L4vec4 c : (virasoroVOA c).grading 4) : VirUniv c)
    = L4vac c := rfl

/-- **The explicit Gram entry**, for arbitrary central charge:
`⟨L₋₄|0⟩, L₋₄|0⟩⟩₄ = 105·c`.

⚠ Not `5c`: `RigidBridge.shapForm` is the top-mode form `ε(a₍₂ₖ₋₁₎b)`, which agrees with the
textbook contravariant form only on quasi-primary vectors, and `L₁L₋₄|0⟩ = 5L₋₃|0⟩ ≠ 0`.  See the
file docstring, and `shapForm_omegaVir_self` for the level-2 case where the two do agree. -/
theorem shapForm_L4vac_self (hvac : (virasoroVOA c).vacuum ≠ 0) :
    shapForm (virasoroVOA c) hvac 4 (L4vec4 c) (L4vec4 c) = 105 * c := by
  rw [shapForm_eq_iff, show (2 * (4 : ℤ) - 1) = 7 from by norm_num]
  exact smul_L4vac_seven_self c

/-- **The Lee–Yang value**: `⟨L₋₄|0⟩, L₋₄|0⟩⟩₄ = 105·(-22/5) = -462 ≠ 0` at `c = -22/5`. -/
theorem leeYangGram_L4vac :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
      (L4vec4 leeYangC) (L4vec4 leeYangC) = -462 := by
  rw [shapForm_L4vac_self leeYangC leeYang_vacuum_ne_zero, leeYangC]
  norm_num

/-- **The level-4 Shapovalov form of `V(-22/5,0)` is not the zero form.**

This is the ingredient that `shapForm_leeYang_degenerate` was missing: an identically zero form
is degenerate for free, so degeneracy alone carries no information. -/
theorem shapForm_leeYang_ne_zero :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4 ≠ 0 := by
  intro h
  have hg := leeYangGram_L4vac
  rw [h] at hg
  simp only [LinearMap.zero_apply] at hg
  norm_num at hg

/-- The explicit-witness form of `shapForm_leeYang_ne_zero`: `L₋₄|0⟩` pairs nontrivially with
itself. -/
theorem shapForm_leeYang_exists_ne_zero :
    ∃ a b : (virasoroVOA leeYangC).grading 4,
      shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4 a b ≠ 0 :=
  ⟨L4vec4 leeYangC, L4vec4 leeYangC, by rw [leeYangGram_L4vac]; norm_num⟩

/-! ## §5  Degenerate **and** nonzero -/

/-- **The Kac-determinant statement, with its nontriviality attached.**

The level-4 Shapovalov form of `V(-22/5, 0)` is **degenerate** — the Lee–Yang singular vector
`5L₋₂²|0⟩ - 3L₋₄|0⟩` is a null direction (`shapForm_leeYang_degenerate`, via
`leeYangSingular_mem_radBil`) — **and it is not the zero form** — the entry
`⟨L₋₄|0⟩, L₋₄|0⟩⟩₄ = -462` is nonzero.

So `det M₄(-22/5) = 0` is the *interesting* vanishing, produced by a genuine null vector inside a
Gram matrix that is not identically zero, and not the vacuous vanishing of a matrix of zeros.  It
is this conjunction, not degeneracy alone, that may be quoted as the level-4 Kac determinant
zero. -/
theorem shapForm_leeYang_degenerate_and_ne_zero :
    ¬ LinearMap.Nondegenerate (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4)
      ∧ shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4 ≠ 0 :=
  ⟨shapForm_leeYang_degenerate, shapForm_leeYang_ne_zero⟩

/-- The same content stated on the radical: it is a **proper nonzero** subspace of `𝒱₄`.

`≠ ⊥` is the degeneracy (the singular vector lies in it); `≠ ⊤` is the nonvanishing (if every
vector were in the radical the form would be zero). -/
theorem radBil_shapForm_leeYang_proper :
    DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) ≠ ⊥
      ∧ DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) ≠ ⊤ := by
  refine ⟨radBil_shapForm_leeYang_ne_bot, ?_⟩
  intro htop
  refine shapForm_leeYang_ne_zero ?_
  ext a b
  have ha : a ∈ DefForm.radBil (shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4) := by
    rw [htop]; trivial
  simpa using DefForm.mem_radBil.mp ha b

/-! ## §6  The whole level-4 Gram matrix at `c = -22/5`

One computed entry plus the already-proved radical membership of the singular vector
`s = 5L₋₂²|0⟩ - 3L₋₄|0⟩` determines the other two entries with no further mode computation:
`⟨s, y⟩₄ = 0` reads `5⟨L₋₂²|0⟩, y⟩₄ = 3⟨L₋₄|0⟩, y⟩₄`. -/

/-- The singular vector, decomposed in the basis `{L₋₂²|0⟩, L₋₄|0⟩}` of `𝒱₄`. -/
theorem leeYangSing4_eq :
    leeYangSing4 = (5 : ℂ) • L2L2vec4 leeYangC + (-3 : ℂ) • L4vec4 leeYangC := by
  apply Subtype.ext
  change leeYangSingular = (5 : ℂ) • L2L2vac leeYangC + (-3 : ℂ) • L4vac leeYangC
  rfl

/-- The singular vector pairs to zero with everything at level 4 (`leeYangSingular_mem_radBil`,
restated as an application). -/
theorem shapForm_leeYangSing4_apply (y : (virasoroVOA leeYangC).grading 4) :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4 leeYangSing4 y = 0 :=
  DefForm.mem_radBil.mp leeYangSingular_mem_radBil y

/-- The off-diagonal entry: `⟨L₋₂²|0⟩, L₋₄|0⟩⟩₄ = -1386/5` at `c = -22/5` (`= 63c = 21·3c`). -/
theorem shapForm_L2L2vac_L4vac_leeYang :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
      (L2L2vec4 leeYangC) (L4vec4 leeYangC) = -1386 / 5 := by
  have h := shapForm_leeYangSing4_apply (L4vec4 leeYangC)
  rw [leeYangSing4_eq] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    leeYangGram_L4vac] at h
  linear_combination h / 5

/-- The remaining diagonal entry: `⟨L₋₂²|0⟩, L₋₂²|0⟩⟩₄ = -4158/25` at `c = -22/5`
(`= 189c/5 = 21·(c/2)(c+8)`). -/
theorem shapForm_L2L2vac_self_leeYang :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
      (L2L2vec4 leeYangC) (L2L2vec4 leeYangC) = -4158 / 25 := by
  have h := shapForm_leeYangSing4_apply (L2L2vec4 leeYangC)
  rw [leeYangSing4_eq] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [shapForm_symm leeYang_vacuum_ne_zero 4 (L4vec4 leeYangC) (L2L2vec4 leeYangC),
    shapForm_L2L2vac_L4vac_leeYang] at h
  linear_combination h / 5

/-- **The level-4 Gram matrix of `V(-22/5,0)` is `21 ×` the textbook Kac matrix**
`[[(c/2)(c+8), 3c], [3c, 5c]]`.

This is a consistency audit of the whole level-4 picture: the top-mode form is *proportional* to
the contravariant form on `𝒱₄`, so its degeneracy really is the Kac-determinant degeneracy, and
the proportionality forces `5c(c+8)/2 · 5c - (3c)² = 0`, i.e. `c = -22/5`.  Being scale-invariant
it does **not** by itself pin the constant `21`; that comes from `smul_L4vac_seven`. -/
theorem shapForm_leeYang_level4_eq_kac :
    shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
        (L2L2vec4 leeYangC) (L2L2vec4 leeYangC) = 21 * (leeYangC / 2 * (leeYangC + 8))
      ∧ shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
        (L2L2vec4 leeYangC) (L4vec4 leeYangC) = 21 * (3 * leeYangC)
      ∧ shapForm (virasoroVOA leeYangC) leeYang_vacuum_ne_zero 4
        (L4vec4 leeYangC) (L4vec4 leeYangC) = 21 * (5 * leeYangC) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [shapForm_L2L2vac_self_leeYang, leeYangC]; norm_num
  · rw [shapForm_L2L2vac_L4vac_leeYang, leeYangC]; norm_num
  · rw [leeYangGram_L4vac, leeYangC]; norm_num

end LeeYang

end VOA
