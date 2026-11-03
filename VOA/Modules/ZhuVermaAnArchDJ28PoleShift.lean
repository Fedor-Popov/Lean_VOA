/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcirc

/-!
# The off-diagonal pole-shift `Res Y(u,z)v (1+z)^{wt u + s}/z^{n+2+t} ∈ O'_{n,0}` for `t ≥ s`.

This is the `m = 0` case of **Dong–Li–Mason Lemma 2.1(i)** (= Zhu Lemma 2.1.2), the single
"pole-shifting absorption" black box that powers the entire ideal/filtration theory of `A_n(𝒱)` and
`A_{n,m}(𝒱)`:

  `Res_z Y(u,z)v (1+z)^{wt u + s}/z^{n+2+t}  ∈  O'_{n,0}(𝒱)   for all  t ≥ s ≥ 0`

(homogeneous `u ∈ 𝒱_M`).  The repo already has the **diagonal** case `s = t` — that is exactly
`Pres_mem_Onm` (`PresAnm W M n d = Res_z Y(u,z)v (1+z)^{M+d}/z^{n+2+d}`).  This file adds the
**off-diagonal** case `t > s`, which the diagonal machinery does not directly cover.

## Why this matters (the corrected Half-A route)

Dong–Li–Mason / Zhu prove the ideal property `𝒱 ∗ⁿ₀ O ⊆ O_{n,0}` **directly**, NOT by induction on
`n`: the Jacobi/iterate expansion of `a ∗ⁿ₀ (c ∘ᵏ₀ d)` produces a finite sum of single-variable
residues `Res_z Y(a₍ⱼ₎c, z) d (1+z)^{wt(a₍ⱼ₎c) + s}/z^{n+2+t}` — each with `t ≥ s` — and every one
lands in `O'_{n,0}` by this off-diagonal pole-shift.  **No closed-form coefficient collapse is
needed** — which is exactly why a diagonal-only "explicit tower witness" approach
hits a wall: it solves a strictly harder problem than DLM's proof.  This lemma is the black box
that lets the DLM expansion go through term-by-term.

## The proof (elementary, no integration-by-parts)

Unlike DLM's own inductive proof of Lemma 2.1(i) (which trades pole order for the `(L₋₁+L₀)`
generator via `Y(L₋₁u,z) = d/dz Y(u,z)`), we reduce the off-diagonal case to the diagonal
`Pres_mem_Onm` by the **atomic Pascal-shift identity**

  `Res Y(u,z)v (1+z)^{M+s+1}/z^p  =  Res Y(u,z)v (1+z)^{M+s}/z^p  +  Res Y(u,z)v (1+z)^{M+s}/z^{p-1}`

(from `(1+z)^{s+1} = (1+z)^s + z·(1+z)^s`, i.e. `cbz_pascal_up`), and induction on the pole excess
`e = t - s`.  Engine-verified TRUE on the rank-1 free boson (`certificates/mathematica/pascal_shift.wl`,
`certificates/mathematica/offdiag_vandermonde.wl`, all cases exact zero).

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96, Lemma 2.1(i); Zhu, J. AMS 9 (1996), Lemma 2.1.2;
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), Lemma 2.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The off-diagonal residue** `PresAnmOff W M n s t u v = Res_z Y(u,z)v (1+z)^{M+s}/z^{n+2+t}`
(mode form, restricted to the finite support `i ≤ M+s` of `cbz (M+s) ·`).  Shift `s`, pole `n+2+t`;
the diagonal `t = s` is `PresAnm W M n s`. -/
noncomputable def PresAnmOff (W : VertexOperatorAlgebra 𝒱) (M n s t : ℕ) (u v : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (M + s + 1),
    cbz ((M : ℤ) + s) (i : ℤ) • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - t) v

/-- On the diagonal `t = s`, `PresAnmOff` is the diagonal `PresAnm` (definitionally). -/
theorem presAnmOff_diag (W : VertexOperatorAlgebra 𝒱) (M n s : ℕ) (u v : 𝒱) :
    PresAnmOff W M n s s u v = PresAnm W M n s u v := rfl

/-- **The atomic Pascal-shift identity.**  Raising the weight-shift by one at fixed pole `n+2+(t+1)`
splits into the same shift at pole `n+2+(t+1)` plus the same shift at pole `n+2+t`:

  `PresAnmOff W M n (s+1) (t+1) = PresAnmOff W M n s (t+1) + PresAnmOff W M n s t`.

The residue image of `(1+z)^{M+s+1} = (1+z)^{M+s} + z·(1+z)^{M+s}`, via `cbz_pascal_up`. -/
theorem presAnmOff_pascal (W : VertexOperatorAlgebra 𝒱) (M n s t : ℕ) (u v : 𝒱) :
    PresAnmOff W M n (s + 1) (t + 1) u v
      = PresAnmOff W M n s (t + 1) u v + PresAnmOff W M n s t u v := by
  simp only [PresAnmOff, Nat.cast_add, Nat.cast_one]
  rw [show M + (s + 1) + 1 = (M + s + 1) + 1 from by omega]
  -- Split each summand by Pascal on the `cbz` upper index.
  have hpas : ∀ i ∈ Finset.range ((M + s + 1) + 1),
      cbz ((M : ℤ) + ((s : ℤ) + 1)) (i : ℤ) • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - ((t : ℤ) + 1)) v
        = cbz ((M : ℤ) + (s : ℤ)) (i : ℤ) • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - ((t : ℤ) + 1)) v
          + cbz ((M : ℤ) + (s : ℤ)) ((i : ℤ) - 1)
              • W.smul u ((i : ℤ) - ((n : ℤ) + 2) - ((t : ℤ) + 1)) v := by
    intro i _
    rw [show ((M : ℤ) + ((s : ℤ) + 1)) = ((M : ℤ) + (s : ℤ)) + 1 from by ring,
        cbz_pascal_up ((M : ℤ) + (s : ℤ)) (i : ℤ), add_smul]
  rw [Finset.sum_congr rfl hpas, Finset.sum_add_distrib]
  congr 1
  · -- First sum: drop the vanishing top term `i = M+s+1` (`cbz (M+s) (M+s+1) = 0`).
    rw [Finset.sum_range_succ,
        show cbz ((M : ℤ) + (s : ℤ)) (((M + s + 1 : ℕ)) : ℤ) = 0 from
          cbz_lt (by positivity) (by push_cast; omega), zero_smul, add_zero]
  · -- Second sum: reindex `i ↦ i+1`, drop the vanishing bottom term (`cbz (M+s) (-1) = 0`).
    rw [Finset.sum_range_succ',
        show cbz ((M : ℤ) + (s : ℤ)) (((0 : ℕ) : ℤ) - 1) = 0 from
          cbz_apply_neg _ (by norm_num), zero_smul, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hx : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by push_cast; ring
    have hm : ((i + 1 : ℕ) : ℤ) - ((n : ℤ) + 2) - ((t : ℤ) + 1)
        = (i : ℤ) - ((n : ℤ) + 2) - (t : ℤ) := by push_cast; ring
    rw [hx, hm]

/-- **The off-diagonal pole-shift membership** (packaged as an induction on the pole excess `e`).
For homogeneous `u ∈ 𝒱_M`, `PresAnmOff W M n s (s + e) u v ∈ Onm W n 0` for every excess `e` and
shift `s`.  Base `e = 0`: the diagonal `PresAnm`, by `Pres_mem_Onm`.  Step: the Pascal-shift writes
the excess-`(e+1)` residue as (excess-`e` at shift `s+1`) − (excess-`e` at shift `s`). -/
theorem presAnmOff_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    ∀ (e s : ℕ), PresAnmOff W M n s (s + e) u v ∈ Onm W n 0 := by
  intro e
  induction e with
  | zero =>
    intro s
    rw [Nat.add_zero, presAnmOff_diag]
    exact Pres_mem_Onm W n hu v s
  | succ e ih =>
    intro s
    have hpascal := presAnmOff_pascal W M n s (s + e) u v
    -- hpascal : PresAnmOff (s+1) (s+e+1) = PresAnmOff s (s+e+1) + PresAnmOff s (s+e)
    have hstep : PresAnmOff W M n s (s + (e + 1)) u v
        = PresAnmOff W M n (s + 1) ((s + 1) + e) u v - PresAnmOff W M n s (s + e) u v := by
      rw [show s + (e + 1) = (s + e) + 1 from by omega,
          show (s + 1) + e = (s + e) + 1 from by omega]
      exact eq_sub_of_add_eq hpascal.symm
    rw [hstep]
    exact Submodule.sub_mem _ (ih (s + 1)) (ih s)

/-- `PresAnmOff` is the homogeneous residue `resHom W s (n+2+t)` (mode identification). -/
theorem resHom_eq_presAnmOff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (s t : ℕ) :
    resHom W (s : ℤ) ((n : ℤ) + 2 + (t : ℤ)) u v = PresAnmOff W M n s t u v := by
  rw [resHom_homogeneous W (s : ℤ) ((n : ℤ) + 2 + (t : ℤ)) hu v]
  rw [show (M : ℤ) + (s : ℤ) = ((M + s : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((M + s : ℕ) : ℤ) = (M : ℤ) + (s : ℤ) from by push_cast; ring]
  congr 2
  ring

/-- **The off-diagonal pole-shift** (`m = 0` DLM Lemma 2.1(i) / Zhu 2.1.2): for homogeneous
`u ∈ 𝒱_M`, `Res_z Y(u,z)v (1+z)^{M+s}/z^{n+2+t} = resHom W s (n+2+t) u v ∈ Onm W n 0` for all
`t ≥ s`.  The single pole-shift black box behind the DLM/DJ ideal proofs, off the diagonal
`Pres_mem_Onm`. -/
theorem resHom_offdiag_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) {s t : ℕ} (hst : s ≤ t) :
    resHom W (s : ℤ) ((n : ℤ) + 2 + (t : ℤ)) u v ∈ Onm W n 0 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [resHom_eq_presAnmOff W n hu v s (s + e)]
  exact presAnmOff_mem_Onm W n hu v e s

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.presAnmOff_pascal
  #print axioms VOA.presAnmOff_mem_Onm
  #print axioms VOA.resHom_offdiag_mem_Onm
-/
