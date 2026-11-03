/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28PoleShift

/-!
# Dong–Jiang Lemma 2.4 at **general base level `m`**

The repo has the high-pole residue membership only at base level `m = 0`
(`resHom_offdiag_mem_Onm`, `ZhuVermaAnArchDJ28PoleShift`).  Dong–Jiang's Lemma 2.4 is stated at
general `m`: for homogeneous `u ∈ 𝒱_M` and `t ≥ s ≥ 0`,

  `Res_z (1+z)^{wt u + m + s}/z^{q+m+2+t} Y(u,z)v ∈ O'_{q,m}(𝒱)`.

This file supplies it.  The point is that the two shift-`0` workhorses are already **parameter
generic** — `PresAnm`/`PresAnmOff` take the weight and level as *formal* parameters, and
`presAnm_recursion` / `presAnmOff_pascal` carry no hypothesis on `u` — so the whole `m = 0`
argument transports verbatim under the substitution

  `M ↦ M + m`,  `n ↦ q + m`,

which is exactly the reindexing that turns `Res_z (1+z)^{M+d}/z^{n+2+d}` into
`Res_z (1+z)^{(M+m)+d}/z^{(q+m)+2+d}`.  Only two things must be redone at the new base level:

* the **base case** `PresAnm W (M+m) (q+m) 0 u v = anmCirc W q m u v` — the circle generator of
  `O'_{q,m}` rather than of `O'_{q,0}`;
* the **target ideal** `Onm W q m` in place of `Onm W q 0`.

Everything else (the integration-by-parts recursion, the Pascal pole-shift) is reused unchanged.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §2 (Lemma 2.4); `ZhuVermaAnArchMUcirc` (`PresAnm`, `presAnm_recursion`,
`Pres_mem_Onm` — the `m = 0` template), `ZhuVermaAnArchDJ28PoleShift` (`PresAnmOff`,
`presAnmOff_pascal`, `presAnmOff_diag`), `ZhuVermaAnArchAnm` (`anmCirc`, `anmCirc_mem_Onm`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The base case at level `m`: the shift-`m` residue is the circle generator of `O'_{q,m}`. -/

/-- At `d = 0` the shift-`m` residue `Res_z (1+z)^{M+m}/z^{q+m+2} Y(u,z)v` is the circle generator
`anmCirc W q m u v` of `O'_{q,m}` (for homogeneous `u ∈ 𝒱_M`). -/
theorem PresAnm_shift_zero (W : VertexOperatorAlgebra 𝒱) {M q m : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    PresAnm W (M + m) (q + m) 0 u v = anmCirc W q m u v := by
  rw [anmCirc, resHom_homogeneous W (m : ℤ) ((q : ℤ) + (m : ℤ) + 2) hu v, PresAnm]
  rw [show ((M : ℤ) + (m : ℤ)) = ((M + m : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]
  refine Finset.sum_congr (by rw [Nat.add_zero]) fun i _ => ?_
  simp only [Nat.cast_zero, add_zero, sub_zero]
  congr 2 <;> (push_cast; ring)

/-! ## The diagonal family at level `m`. -/

/-- **The diagonal high-pole residue lies in `O'_{q,m}`** — the general-base-level analogue of
`Pres_mem_Onm`.  Induction on the shift `d`: the base is the circle generator `anmCirc W q m`, and
the step is the (hypothesis-free, parameter-generic) integration-by-parts recursion
`presAnm_recursion` applied at `(M+m, q+m)`, using that `L₋₁u ∈ 𝒱_{M+1}` and `(M+1)+m = (M+m)+1`. -/
theorem PresAnm_shift_mem_Onm (W : VertexOperatorAlgebra 𝒱) (q m : ℕ) :
    ∀ (d M : ℕ) {u : 𝒱}, u ∈ W.grading (M : ℤ) → ∀ v : 𝒱,
      PresAnm W (M + m) (q + m) d u v ∈ Onm W q m := by
  intro d
  induction d with
  | zero =>
    intro M u hu v
    rw [PresAnm_shift_zero W hu v]
    exact anmCirc_mem_Onm W q m u v
  | succ d ih =>
    intro M u hu v
    have huL : W.L (-1) u ∈ W.grading (((M + 1 : ℕ)) : ℤ) := by
      have := L_neg_one_mem_grading_succ W hu
      rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring]
    have hG : PresAnm W ((M + m) + 1) (q + m) d (W.L (-1) u) v ∈ Onm W q m := by
      have h := ih (M + 1) huL v
      rwa [show (M + 1) + m = (M + m) + 1 from by omega] at h
    have hP : PresAnm W (M + m) (q + m) d u v ∈ Onm W q m := ih M hu v
    have hscal : ((d : ℂ) + ((q + m : ℕ) : ℂ) + 2) ≠ 0 := by
      have hcast : ((d : ℂ) + ((q + m : ℕ) : ℂ) + 2) = ((d + (q + m) + 2 : ℕ) : ℂ) := by
        push_cast; ring
      rw [hcast]
      exact_mod_cast (by omega : d + (q + m) + 2 ≠ 0)
    have hrec := presAnm_recursion W (M + m) (q + m) d u v
    have hmem_rhs : PresAnm W ((M + m) + 1) (q + m) d (W.L (-1) u) v
        + (((M + m : ℕ) : ℂ) + d + 1) • PresAnm W (M + m) (q + m) d u v ∈ Onm W q m :=
      Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP)
    have hsplit : PresAnm W (M + m) (q + m) (d + 1) u v
        = ((d : ℂ) + ((q + m : ℕ) : ℂ) + 2)⁻¹
            • (((d : ℂ) + ((q + m : ℕ) : ℂ) + 2) • PresAnm W (M + m) (q + m) (d + 1) u v) := by
      rw [smul_smul, inv_mul_cancel₀ hscal, one_smul]
    rw [hsplit, hrec]
    exact Submodule.smul_mem _ _ hmem_rhs

/-! ## The off-diagonal family at level `m`. -/

/-- **The off-diagonal pole shift at base level `m`** — the general-base-level analogue of
`presAnmOff_mem_Onm`.  Induction on the pole excess `e`, with the diagonal base supplied by
`PresAnm_shift_mem_Onm` and the step by the parameter-generic `presAnmOff_pascal`. -/
theorem presAnmOff_shift_mem_Onm (W : VertexOperatorAlgebra 𝒱) (q m : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    ∀ (e s : ℕ), PresAnmOff W (M + m) (q + m) s (s + e) u v ∈ Onm W q m := by
  intro e
  induction e with
  | zero =>
    intro s
    rw [Nat.add_zero, presAnmOff_diag]
    exact PresAnm_shift_mem_Onm W q m s M hu v
  | succ e ih =>
    intro s
    have hpascal := presAnmOff_pascal W (M + m) (q + m) s (s + e) u v
    have hstep : PresAnmOff W (M + m) (q + m) s (s + (e + 1)) u v
        = PresAnmOff W (M + m) (q + m) (s + 1) ((s + 1) + e) u v
          - PresAnmOff W (M + m) (q + m) s (s + e) u v := by
      rw [show s + (e + 1) = (s + e) + 1 from by omega,
          show (s + 1) + e = (s + e) + 1 from by omega]
      exact eq_sub_of_add_eq hpascal.symm
    rw [hstep]
    exact Submodule.sub_mem _ (ih (s + 1)) (ih s)

/-! ## The residue form: DJ Lemma 2.4 at general base level `m`. -/

/-- `resHom` at shift `m+s` and pole `q+m+2+t` is the `PresAnmOff` family at `(M+m, q+m)`. -/
theorem resHom_eq_presAnmOff_shift (W : VertexOperatorAlgebra 𝒱) (q m : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (s t : ℕ) :
    resHom W ((m : ℤ) + (s : ℤ)) ((q : ℤ) + (m : ℤ) + 2 + (t : ℤ)) u v
      = PresAnmOff W (M + m) (q + m) s t u v := by
  rw [resHom_homogeneous W ((m : ℤ) + (s : ℤ)) ((q : ℤ) + (m : ℤ) + 2 + (t : ℤ)) hu v]
  rw [show ((M : ℤ) + ((m : ℤ) + (s : ℤ))) = ((M + m + s : ℕ) : ℤ) from by push_cast; ring,
    Int.toNat_natCast, PresAnmOff]
  refine Finset.sum_congr (by rw [show M + m + s = (M + m) + s from by omega]) fun i _ => ?_
  congr 2 <;> (push_cast; ring)

/-- **DONG–JIANG LEMMA 2.4 AT GENERAL BASE LEVEL `m`.**  For homogeneous `u ∈ 𝒱_M` and `t ≥ s ≥ 0`,

  `Res_z (1+z)^{M+m+s}/z^{q+m+2+t} Y(u,z)v = resHom W (m+s) (q+m+2+t) u v ∈ O'_{q,m}(𝒱)`.

The `m = 0` case is the proved `resHom_offdiag_mem_Onm`. -/
theorem resHom_offdiag_mem_Onm_gen (W : VertexOperatorAlgebra 𝒱) (q m : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) {s t : ℕ} (hst : s ≤ t) :
    resHom W ((m : ℤ) + (s : ℤ)) ((q : ℤ) + (m : ℤ) + 2 + (t : ℤ)) u v ∈ Onm W q m := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [resHom_eq_presAnmOff_shift W q m hu v s (s + e)]
  exact presAnmOff_shift_mem_Onm W q m hu v e s

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.PresAnm_shift_mem_Onm
  #print axioms VOA.presAnmOff_shift_mem_Onm
  #print axioms VOA.resHom_offdiag_mem_Onm_gen
-/
