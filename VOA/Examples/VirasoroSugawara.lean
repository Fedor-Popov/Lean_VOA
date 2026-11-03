/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergCentral
import VOA.Examples.HeisenbergConformal
import VOA.Examples.HeisenbergVOA

/-!
# The `c = 1` Virasoro VOA as the Sugawara sub-structure of Heisenberg

## Status
The `c = 1` Virasoro VOA as the Sugawara sub-structure of the (`pbw`-free) Heisenberg
VOA — `virasoro_relation_c1`, `central_charge_one`, `omega_generates_virasoro_c1` — proved
`sorry`-free / axiom-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, **no
`pbw`**, since it rests on the `pbw`-free `heisenbergVOA`).  The abstract general-`c` `Vir(c)`
(vacuum Verma → `L(c,0)`) and minimal-model rationality are NOT targets here — they are the
SEPARATE, reconstruction-gated `Examples/VirasoroVOA` (general-`c`) row.

The rank-1 Heisenberg VOA `heisenbergVOA k hk : VertexOperatorAlgebra Fock` (free boson,
level `k ≠ 0`) carries the conformal vector `ω = (1/2k)a₋₁a₋₁1`.  Its Virasoro modes
`Lₙ := ω₍ₙ₊₁₎ = mode (Y ω)(n+1)` realise the Virasoro algebra at **central charge `c = 1`**
— this is the Sugawara `Vir(1)` sitting inside `M(1)` (Gannon §5.2, eq. 5.2.5d).

This file packages that `c = 1` realisation:

* `VirasoroVOA.L k hk n` — the Virasoro modes of the conformal field `Y(ω)`, defined as
  `mode (Y k (ω k)) (n+1)` (definitionally `Lvir k n`, via the bridge
  `Lvir_eq_mode_Y_omega`).
* `VirasoroVOA.virasoro_relation_c1` — the Virasoro relation with the `c = 1` central term
  `δ_{m+n,0}(m³-m)/12`, transported from `L_virasoro` (HeisenbergCentral) + the bridge.
* `VirasoroVOA.central_charge_one` — `(heisenbergVOA k hk).centralCharge = 1`.
* `VirasoroVOA.L_eq_voaL` / `VirasoroVOA.omega_generates_virasoro_c1` — a clean statement
  that `ω` generates a Virasoro algebra of central charge `1` *inside* `heisenbergVOA`
  (the `c = 1` Sugawara realisation), phrased through the abstract VOA mode `W.L`.

## Scope
This file records only the `c = 1` Sugawara sub-structure of Heisenberg.  The general-`c`
universal Virasoro VOA is `VirModule.virasoroVOA c` (`Examples.VirasoroInstance`, carrier
`VirUniv c`), and its simple quotient `L(c,0)` is `virasoroSimple c` (`Examples.VirasoroSimple`).

## Dependencies
* `Examples.HeisenbergCentral` (`L_virasoro`, the `c = 1` central term),
  `Examples.HeisenbergConformal` (`Lvir_eq_mode_Y_omega`, `conf_virasoro`),
  `Examples.HeisenbergVOA` (`heisenbergVOA`, `heisenberg_central_charge`).
-/

namespace VOA.VirasoroVOA

open scoped BigOperators
open Module (End)

/-! ## §1  The Virasoro modes of the conformal field `Y(ω)` -/

/-- **The Virasoro modes of the `c = 1` Sugawara conformal field** `Y(ω)` (Gannon 5.2.5d):
`Lₙ := ω₍ₙ₊₁₎ = mode (Y k (ω k)) (n+1)`.  By the conformal bridge `Lvir_eq_mode_Y_omega`
this is exactly the free-boson Sugawara mode `Lvir k n`, hence carries all of its proved
algebra.  (The hypothesis `hk : k ≠ 0` is kept for uniformity with the relation below; the
mode itself is defined for every `k`.) -/
noncomputable def L (k : ℂ) (_hk : k ≠ 0) (n : ℤ) : End ℂ Fock :=
  mode (Y k (ω k)) (n + 1)

/-- `L k hk n` unfolds to `mode (Y k (ω k)) (n+1)`. -/
@[simp] theorem L_apply (k : ℂ) (hk : k ≠ 0) (n : ℤ) :
    L k hk n = mode (Y k (ω k)) (n + 1) := rfl

/-- **The bridge `Lₙ = Lvir k n`**: the packaged Virasoro mode coincides with the
free-boson Sugawara mode (`Lvir_eq_mode_Y_omega`, transported). -/
theorem L_eq_Lvir (k : ℂ) (hk : k ≠ 0) (n : ℤ) : L k hk n = Lvir k n :=
  (Lvir_eq_mode_Y_omega k n).symm

/-! ## §2  The Virasoro relation at central charge `c = 1` -/

/-- **The Virasoro relation for the conformal modes, central charge `c = 1`** (Gannon 5.2.5d):
`⁅Lₘ, Lₙ⁆ = (m-n)L_{m+n} + δ_{m+n,0}·(m³-m)/12·1`.
Pure transport of the proved `L_virasoro` (HeisenbergCentral) along the bridge `L = Lvir`;
the central term is the free-boson `(m³-m)/12`, i.e. `c = 1`. -/
theorem virasoro_relation_c1 (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    ⁅L k hk m, L k hk n⁆
      = ((m : ℂ) - n) • L k hk (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0) • (1 : End ℂ Fock) := by
  rw [L_eq_Lvir, L_eq_Lvir, L_eq_Lvir, Ring.lie_def, L_virasoro k hk m n,
    show (1 : End ℂ Fock) = (LinearMap.id : End ℂ Fock) from rfl]

/-! ## §3  The central charge is `1` -/

/-- **The central charge of the Sugawara conformal structure is `1`** (the free-boson `c = 1`,
`heisenberg_central_charge`). -/
theorem central_charge_one (k : ℂ) (hk : k ≠ 0) :
    (heisenbergVOA k hk).centralCharge = 1 :=
  heisenberg_central_charge k hk

/-! ## §4  `ω` generates a Virasoro algebra of central charge `1` inside `heisenbergVOA`

The abstract VOA Virasoro mode `(heisenbergVOA k hk).L n = mode (Y k (ω k)) (n+1)` is, by
construction, our packaged `L k hk n` (the conformal field is `ω k` and the vertex map is
`Y k`).  Hence the abstract VOA Virasoro relation (`VertexOperatorAlgebra.L_virasoro`)
specialises to the `c = 1` relation, exhibiting `ω` as the generator of a Virasoro algebra
of central charge `1`.  This is the deliverable: the `c = 1` Virasoro VOA *as the Sugawara
sub-structure of Heisenberg*.  (The general-`c` VOA is `VirModule.virasoroVOA c`, in
`Examples.VirasoroInstance`.) -/

/-- The abstract VOA mode `(heisenbergVOA k hk).L n` is the packaged Sugawara mode
`L k hk n` — the conformal vector is `ω k`, the vertex map is `Y k`. -/
theorem L_eq_voaL (k : ℂ) (hk : k ≠ 0) (n : ℤ) :
    (heisenbergVOA k hk).L n = L k hk n := rfl

/-- **`ω` generates the `c = 1` Virasoro algebra inside `heisenbergVOA`** (the Sugawara
realisation). The abstract VOA Virasoro modes `W.L m` of `W = heisenbergVOA k hk` satisfy the
Virasoro relation whose central term is exactly `(c/12)(m³-m)` with `c = 1`. This is the
`c = 1` Virasoro VOA presented as the conformal sub-structure of the free boson. -/
theorem omega_generates_virasoro_c1 (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    ⁅(heisenbergVOA k hk).L m, (heisenbergVOA k hk).L n⁆
      = ((m : ℂ) - n) • (heisenbergVOA k hk).L (m + n)
        + (if m + n = 0 then
            (((m : ℂ) ^ 3 - m) / 12 * (heisenbergVOA k hk).centralCharge) • (1 : End ℂ Fock)
           else 0) :=
  (heisenbergVOA k hk).L_virasoro m n

/-- Specialising `omega_generates_virasoro_c1` with `centralCharge = 1`: the Sugawara modes
obey the `c = 1` Virasoro relation in the abstract VOA modes `W.L`, matching
`virasoro_relation_c1` exactly. -/
theorem omega_generates_virasoro_c1' (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    ⁅(heisenbergVOA k hk).L m, (heisenbergVOA k hk).L n⁆
      = ((m : ℂ) - n) • (heisenbergVOA k hk).L (m + n)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0) • (1 : End ℂ Fock) := by
  rw [L_eq_voaL, L_eq_voaL, L_eq_voaL]
  exact virasoro_relation_c1 k hk m n

/-! ## §5  Axiom audit -/


end VOA.VirasoroVOA
