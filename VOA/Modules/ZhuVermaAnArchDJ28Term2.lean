/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28PoleShift
import VOA.Modules.ZhuVermaAnArchDJ28Induction

/-!
# `Term2Level` reduced to the DLM commutator *identity* (the membership side, packaged).

`Term2Level W n` is `anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0` for all `a c d`.  The DLM
Part-3 **commutator** expansion (derived + engine-verified, `certificates/mathematica/
certificates/mathematica/term2_fullformula.wl`), for homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, is

  `anmRight W n 0 a (anmCirc W n 0 c d)`
    `= anmCirc W n 0 c (anmRight W n 0 a d)`                                    ← the ordered "circle" term
    `  + ∑_j ∑_{p≤j} cbz(-(n+1), j-p)·cbz(K, p) · resHom W (j+1-p) (2n+3+j-p) (a₍ⱼ₎c) d`   ← commutator

and **every summand lands in `Onm W n 0`**:

* the ordered term `anmCirc W n 0 c (anmRight W n 0 a d)` is a level-`n` circle generator
  (`anmCirc_mem_Onm`);
* each commutator residue `resHom W (j+1-p) (2n+3+j-p) (a₍ⱼ₎c) d` is **off-diagonal**: shift `s = j+1-p`,
  pole `2n+3+j-p = (n+2)+(n+1+j-p)`, so pole-excess `t = n+1+j-p` with `t − s = n ≥ 0` — hence in
  `Onm W n 0` by the proved `resHom_offdiag_mem_Onm` (for homogeneous `a₍ⱼ₎c`).

This file proves the **membership side** of that expansion as `term2_mem_of_commExpansion`: any vector
presented as `anmCirc W n 0 c e + (finite ℂ-combination of off-diagonal `resHom`s on homogeneous
factors)` lies in `Onm W n 0`.  With it, proving `Term2Level` reduces to the single **commutator
identity** (exhibiting the explicit `(a₍ⱼ₎c)` factors, the off-diagonal shifts/poles, and the `cbz`
coefficients) — the `jacobi_commutator` + `cbz`-Vandermonde reorganization, the sole remaining step.

Note this is the *clean* piece: the ordered term here is the **level-`n`** circle `anmCirc W n 0`, in
`Onm W n 0`.  The `Term₁` (`k = 0`) analogue has a **level-`0`** ordered circle `anmCirc W 0 0 c e`
(pole `2`), NOT in `Onm W n 0` — that is the genuine cross-level wall, handled elsewhere.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2; Dong–Li–Mason, J. Algebra 206 (1998);
Zhu, J. AMS 9 (1996), §2.1.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The membership side of the `Term₂` DLM commutator expansion.**  If `X` is presented as the
level-`n` ordered circle `anmCirc W n 0 c e` plus a finite ℂ-combination of **off-diagonal** residues
`resHom W (sh r) (n+2+(po r)) (u r) d` on homogeneous factors `u r ∈ 𝒱_{Mu r}` with `sh r ≤ po r`,
then `X ∈ Onm W n 0`.  The circle term is `anmCirc_mem_Onm`; each residue is `resHom_offdiag_mem_Onm`;
`Submodule.add_mem`/`sum_mem`/`smul_mem` assemble.  This packages the entire membership half of the
DLM Part-3 expansion, leaving only the commutator *identity* (`X = …`) to supply. -/
theorem term2_mem_of_commExpansion (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c e d : 𝒱)
    {R : ℕ} (coeff : Fin R → ℂ) (u : Fin R → 𝒱) (Mu sh po : Fin R → ℕ)
    (hu : ∀ r, u r ∈ W.grading ((Mu r : ℤ))) (hsp : ∀ r, sh r ≤ po r)
    {X : 𝒱}
    (hX : X = anmCirc W n 0 c e
      + ∑ r : Fin R, coeff r • resHom W ((sh r : ℤ)) ((n : ℤ) + 2 + (po r : ℤ)) (u r) d) :
    X ∈ Onm W n 0 := by
  rw [hX]
  refine Submodule.add_mem _ (anmCirc_mem_Onm W n 0 c e) ?_
  refine Submodule.sum_mem _ (fun r _ => ?_)
  exact Submodule.smul_mem _ _ (resHom_offdiag_mem_Onm W n (hu r) d (hsp r))

/-- **`Term2Level W n` from the commutator identity** (membership side discharged).  Supplying, for
every `a c d`, the DLM commutator expansion of `anmRight W n 0 a (anmCirc W n 0 c d)` as
`anmCirc W n 0 c (anmRight W n 0 a d)` plus an off-diagonal residue combination on homogeneous factors
(`hexp`) yields `Term2Level W n`.  The membership side is `term2_mem_of_commExpansion`; the hypothesis
`hexp` is exactly the remaining `jacobi_commutator` + `cbz`-reorganization identity. -/
theorem Term2Level_of_commIdentity (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hexp : ∀ a c d : 𝒱, ∃ (R : ℕ) (coeff : Fin R → ℂ) (uu : Fin R → 𝒱) (Mu sh po : Fin R → ℕ),
      (∀ r, uu r ∈ W.grading ((Mu r : ℤ))) ∧ (∀ r, sh r ≤ po r) ∧
      anmRight W n 0 a (anmCirc W n 0 c d)
        = anmCirc W n 0 c (anmRight W n 0 a d)
          + ∑ r : Fin R, coeff r • resHom W ((sh r : ℤ)) ((n : ℤ) + 2 + (po r : ℤ)) (uu r) d) :
    Term2Level W n := by
  intro a c d
  obtain ⟨R, coeff, uu, Mu, sh, po, hu, hsp, hid⟩ := hexp a c d
  exact term2_mem_of_commExpansion W n c (anmRight W n 0 a d) d coeff uu Mu sh po hu hsp hid

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.term2_mem_of_commExpansion
  #print axioms VOA.Term2Level_of_commIdentity
-/
