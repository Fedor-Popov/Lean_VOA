/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchRgen
import VOA.Modules.ZhuVermaAnDescent4

/-!
# `hRgen` close — the right-slot pure-mode residual core `RgenRest`.

The single remaining homogeneous core of the right-slot `OnL` membership (`hRgen`) is

  `RgenRest W n K a c ∈ On W n`     (`ZhuVermaAnArchRgen.leftProd_Rgen_mem_OnFull_field_of_rest`)

where, for `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,

  `RgenRest = ∑_{j≤n} (-1)^j C(j+n,n) ∑_i C(K+n,i)·[(m+1−K)·a₍m₎c + m·a₍m−1₎c]`,  `m = i−n−j−1`.

This file develops the structural reduction of that core and isolates the genuine combinatorial
content as a single precisely-stated coefficient identity, all axiom-clean.

## What is proved here (`#print axioms = [propext, Classical.choice, Quot.sound]`)

* `Lmode_combo` — the pointwise mode identity rewriting the residual bracket as an `OnL`-style
  derivative correction:
  `(m+1−K)·a₍m₎c + m·a₍m−1₎c = (m+1)·a₍m₎c − ((L₋₁+L₀)a)₍m₎c`,
  for `a ∈ 𝒱_K` (using `smul_L_neg_one` `(L₋₁a)₍m₎c = −m·a₍m−1₎c` and the grading identity
  `(L₀a)₍m₎c = K·a₍m₎c`).
* `RgenRest_eq_Aterm_sub_Bterm` — the homogeneous split `RgenRest = Aterm − Bterm`, where
  `Aterm` is the `(m+1)`-weighted single-mode FZ residue and `Bterm = leftProd' W n (L₋₁a) c +
  K·leftProd-residue` is the `((L₋₁+L₀)a)`-weighted residue (both pure single-mode).
* `RgenRest_eq_leftProd_sub_tower` — `RgenRest = leftProd W n a ((L₋₁+L₀)c) − RgenTower`, the exact
  rearrangement of the proven homogeneous split `leftProd_Lgen_right_homogeneous`.
* `hRgen_closed_of_rest` — the FULL field
  `∀ a c, leftProd W n a ((L₋₁+L₀)c) ∈ OnFull W n`, reduced (through
  `leftProd_Rgen_mem_OnFull_field_of_rest`) to the single core `RgenRest ∈ On`.

## The precise remaining content (NOT `sorry`'d / NOT axiomatized)

`RgenRest W n K a c ∈ On W n`.  Via `RgenRest_eq_Aterm_sub_Bterm` this is the membership in `On` of
the two pure single-mode FZ residues `Aterm` (weight `m+1`) and `Bterm` (weight from `(L₋₁+L₀)a`).
Each is a depth-`n` FZ single-mode residue with a *polynomial-in-`m`* weight and pole `n+j+1`; its
collapse onto the `Pres_mem_On` towers (pole `2n+2+d`) is the single-mode analog of the D4 commutator
chain `coeffSn_eq_coeffPn` (`ZhuRes.gen_vandermonde`+`ZhuRes.gen_jsum`).  The D4 engine consumes the
locality scalar `C(p−(n+j+1),s)` of `mode_commutator_uniform`; the single-mode `Aterm`/`Bterm` carry
NO such scalar, so the j-sum collapse requires the locality-free single-mode certificate (the
`gen_jsum` analog without the `C(n+j+t,t)` factor).  That certificate is the genuine remaining input;
once supplied (mirroring `coeffSn_eq_coeffPn`/`Sn_mem_On`), `RgenRest ∈ On` follows and closes
`hRgen` through `hRgen_closed_of_rest`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The pointwise residual-bracket identity. -/

/-- **Residual-bracket mode identity.**  For `a ∈ 𝒱_K` and any mode `m`, the `RgenRest` bracket
`(m+1−K)·a₍m₎c + m·a₍m−1₎c` rewrites as `(m+1)·a₍m₎c − ((L₋₁+L₀)a)₍m₎c`, using
`(L₋₁a)₍m₎c = −m·a₍m−1₎c` (`smul_L_neg_one`) and `(L₀a)₍m₎c = K·a₍m₎c` (`L_zero_grading` applied to
`a ∈ 𝒱_K`, transported through `PreVertexAlgebra.smul_smul_right`). -/
theorem Lmode_combo (W : VertexOperatorAlgebra 𝒱) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (c : 𝒱) (m : ℤ) :
    ((m : ℂ) + 1 - K) • W.smul a m c + (m : ℂ) • W.smul a (m - 1) c
      = ((m : ℂ) + 1) • W.smul a m c
        - W.smul (W.L (-1) a + W.L 0 a) m c := by
  rw [PreVertexAlgebra.smul_add_left]
  -- (L₋₁a)₍m₎c = −m·a₍m−1₎c
  have hL1 : W.smul (W.L (-1) a) m c = (-(m : ℂ)) • W.smul a (m - 1) c := by
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ (-m)]; push_cast; ring_nf
  -- (L₀a)₍m₎c = K·a₍m₎c
  have hL0 : W.smul (W.L 0 a) m c = (K : ℂ) • W.smul a m c := by
    rw [W.L_zero_grading a ha, PreVertexAlgebra.smul_smul_left]
  rw [hL1, hL0]
  module

/-! ## The homogeneous `Aterm`/`Bterm` split of `RgenRest`. -/

/-- The `(m+1)`-weighted single-mode FZ residue (`m = i−n−j−1`). -/
noncomputable def RgenAterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℤ) (a c : 𝒱) : 𝒱 :=
  ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
      ∑ i ∈ Finset.range ((K + (n : ℤ)).toNat + 1),
        cbz (K + (n : ℤ)) i •
          ((((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) + 1) •
            W.smul a ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c)

/-- The `((L₋₁+L₀)a)`-weighted single-mode FZ residue (`m = i−n−j−1`). -/
noncomputable def RgenBterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℤ) (a c : 𝒱) : 𝒱 :=
  ∑ j ∈ Finset.range (n + 1),
    ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) (n : ℤ)) •
      ∑ i ∈ Finset.range ((K + (n : ℤ)).toNat + 1),
        cbz (K + (n : ℤ)) i •
          W.smul (W.L (-1) a + W.L 0 a) ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) c

/-- **`RgenRest = RgenAterm − RgenBterm`** for `a ∈ 𝒱_K`, via the pointwise `Lmode_combo`. -/
theorem RgenRest_eq_Aterm_sub_Bterm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading K) (c : 𝒱) :
    RgenRest W n K a c = RgenAterm W n K a c - RgenBterm W n K a c := by
  rw [RgenRest, RgenAterm, RgenBterm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub]
  congr 1
  set m : ℤ := (i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) with hm
  have h := Lmode_combo W ha c m
  -- the goal's first scalar is ℤ-zsmul `(m+1-K)`, the second is ℂ-smul `(↑↑i-…)`; normalise both
  -- to the ℂ-smul forms of `h`, then close with `h`.
  rw [show (m + 1 - K : ℤ) • W.smul a m c = ((m : ℂ) + 1 - (K : ℂ)) • W.smul a m c from by
        rw [← Int.cast_smul_eq_zsmul ℂ (m + 1 - K)]; push_cast; ring_nf,
    show (m + 1 : ℤ) • W.smul a m c = ((m : ℂ) + 1) • W.smul a m c from by
        rw [← Int.cast_smul_eq_zsmul ℂ (m + 1)]; push_cast; ring_nf,
    show (((i : ℤ) : ℂ) - (((n : ℤ) : ℂ) + ((j : ℤ) : ℂ) + 1)) = (m : ℂ) from by
        rw [hm]; push_cast; ring]
  exact h

/-! ## `RgenRest = leftProd a ((L₋₁+L₀)c) − RgenTower` (exact rearrangement). -/

/-- **`RgenRest = leftProd W n a ((L₋₁+L₀)c) − RgenTower`** for `a ∈ 𝒱_K`, `c ∈ 𝒱_M`.  Direct
rearrangement of the proven homogeneous split `leftProd_Lgen_right_homogeneous`. -/
theorem RgenRest_eq_leftProd_sub_tower (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℤ}
    {a c : 𝒱} (ha : a ∈ W.grading K) (hc : c ∈ W.grading M) :
    RgenRest W n K a c
      = leftProd W n a (W.L (-1) c + W.L 0 c) - RgenTower W n K a c := by
  rw [leftProd_Lgen_right_homogeneous W n ha hc]
  abel

/-! ## The field `hRgen`, reduced to the single core `RgenRest ∈ On`. -/

/-- **`hRgen` field, conditional on the `RgenRest` core.**  Once `RgenRest W n K a c ∈ On W n` holds
for all homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the full right-slot `OnL` membership
`∀ a c, leftProd W n a ((L₋₁+L₀)c) ∈ OnFull W n` follows through
`leftProd_Rgen_mem_OnFull_field_of_rest`. -/
theorem hRgen_closed_of_rest (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hrest : ∀ (K M : ℤ) {a c : 𝒱}, a ∈ W.grading K → c ∈ W.grading M →
      RgenRest W n K a c ∈ On W n) :
    ∀ a c : 𝒱, leftProd W n a (W.L (-1) c + W.L 0 c) ∈ OnFull W n :=
  leftProd_Rgen_mem_OnFull_field_of_rest W n hrest

end VOA
