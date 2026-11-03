/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.BilinearForm

/-!
# Anti-linear automorphisms of a VOA (clauses (i)–(ii) of the graded-unitarity data)

⚠ **This file is a DEFINITION, not a theorem.**  Nothing here proves that any VOA carries the
structure defined below, and nothing here proves graded unitarity of anything.  It records, as a
Lean structure, the *first two clauses* of the datum that Arabi Ardehali–Beem–Lemos–Rastelli,
*Graded Unitarity in the SCFT/VOA Correspondence*, arXiv:2507.23781v2 = JHEP 06 (2026) 075,
Definition 2.2, attaches to a vertex operator algebra: a **half-integer grading with an
`R`-parity** and an **anti-linear vertex-algebra automorphism `ρ` whose square is that parity**.

⚠ **The source paper was not available when this file was written.**  Definition 2.2 could
therefore not be transcribed verbatim, and this file must not be described as "Definition 2.2"
until someone checks the paper against it.  Two points are at risk and are handled by *not*
committing to a resolution:

* ABLR write the `R`-parity as `s = (-1)^{h + d/2}` with `d` the cohomological grading.  At `d = 0`
  that reads `s = (-1)^h`, i.e. `ρ² = -1` on odd-weight spaces — which is **not** what a naive real
  structure does.  We therefore carry `parity : ℤ → ℂ` as a **field**, not as the hard-coded
  `(-1)^h`.  Downstream (`Core.GradedUnitarity`, `Core.GoodFiltration`) nothing depends on which
  value it takes, so the reduction is insensitive to how this is eventually resolved.
* A genuine real structure (`parity = 1`) is the `ρ² = 1` special case and is the one a Virasoro
  instance would naturally supply.

## What is here

* `RealStructure W` — `ρ` as an additive map with explicit conjugate-homogeneity, compatible with
  every mode product and fixing `𝟙` and `ω`, together with the parity function and `ρ² = s`.
* `RealStructure.rho_L` — `ρ` commutes with every Virasoro mode `Lₙ` (immediate from `map_smul`
  at `u = ω` and `map_omega`).
* `RealStructure.Fixes` — the predicate "`ρ` is the identity on a given set".  This is the hinge
  used by `Core.GradedUnitarity`: on a `ρ`-fixed real form the sesquilinear form (2.30) collapses
  onto the ℂ-**bi**linear invariant form that this repository already constructs, which is why the
  reduction in `Core.GradedUnitarity` needs no sesquilinear machinery.

## Design note — why `ρ : V →+ V` and not a `LinearMap`

There is **no** anti-linear map anywhere else in this repository: `Core.Automorphism.Aut` carries
a ℂ-*linear* `toLinearEquiv`, and the only occurrences of `StarRing ℂ` were an unused binder.
Encoding `ρ` as a semilinear map over `starRingEnd ℂ` forces the conjugate-module dance into every
downstream proof for no gain; the additive-map-plus-`antilinear`-field spelling is what the proofs
actually consume.

## Status
Definitions and their immediate consequences, `sorry`-free, no new axioms.
A concrete partition-basis conjugation for real Virasoro VOAs is constructed downstream in
`Examples.VirasoroRealStructure` and descended there to every simple Virasoro quotient admitting
a real Feigin--Fuchs parameter.  Boundary-model specializations are in
`Examples.VirasoroBoundaryRealStructure`.

## References
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2, Definition 2.2, clauses (i)–(ii).
-/

namespace VOA

open VOA.VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- An **anti-linear vertex-algebra automorphism with parity** — clauses (i) and (ii) of the
graded-unitarity datum of ABLR Definition 2.2 (arXiv:2507.23781v2).

`rho` is additive and conjugate-homogeneous (`antilinear`), respects every mode product
(`map_smul`), and fixes the vacuum and the conformal vector.  Its square is *not* required to be
the identity: it is required to be multiplication by `parity h` on the weight-`h` space (`sq`),
where `parity` is ABLR's `R`-parity `s`.

⚠ `parity` is deliberately a field.  See the file docstring: ABLR's `s = (-1)^{h + d/2}` has not
been checked against this repository's conventions, and no downstream statement depends on it. -/
structure RealStructure (W : VertexOperatorAlgebra 𝒱) where
  /-- The underlying additive map. -/
  rho : 𝒱 →+ 𝒱
  /-- **Anti-linearity**: `ρ(z·v) = z̄·ρ(v)`. -/
  antilinear : ∀ (z : ℂ) (v : 𝒱), rho (z • v) = (starRingEnd ℂ) z • rho v
  /-- **Vertex-algebra compatibility**: `ρ(u₍ₙ₎v) = ρ(u)₍ₙ₎ρ(v)` for every mode. -/
  map_smul : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱), rho (W.smul u n v) = W.smul (rho u) n (rho v)
  /-- `ρ` fixes the vacuum. -/
  map_vacuum : rho W.vacuum = W.vacuum
  /-- `ρ` fixes the conformal vector. -/
  map_omega : rho W.conformalVector = W.conformalVector
  /-- ABLR's `R`-parity `s`, as a function of the conformal weight.  Carried as data. -/
  parity : ℤ → ℂ
  /-- **`ρ² = s`** on each weight space. -/
  sq : ∀ {h : ℤ} (v : 𝒱), v ∈ W.grading h → rho (rho v) = parity h • v

namespace RealStructure

variable {W : VertexOperatorAlgebra 𝒱} (R : RealStructure W)

@[simp] theorem map_zero : R.rho 0 = 0 := AddMonoidHom.map_zero _

@[simp] theorem map_add (a b : 𝒱) : R.rho (a + b) = R.rho a + R.rho b :=
  AddMonoidHom.map_add _ a b

@[simp] theorem map_neg (a : 𝒱) : R.rho (-a) = -R.rho a := AddMonoidHom.map_neg _ a

/-- `ρ` commutes with every Virasoro mode: `ρ(Lₙ v) = Lₙ ρ(v)`.  Immediate from `map_smul` at
`u = ω` (`Lₙ = ω₍ₙ₊₁₎`) together with `map_omega`. -/
theorem rho_L (n : ℤ) (v : 𝒱) : R.rho (W.L n v) = W.L n (R.rho v) := by
  have h : W.L n v = W.smul W.conformalVector (n + 1) v := rfl
  have h' : W.L n (R.rho v) = W.smul W.conformalVector (n + 1) (R.rho v) := rfl
  rw [h, h', R.map_smul, R.map_omega]

/-- `ρ` is **the identity on `S`**.  On such a set the sesquilinear form `(ρ·|·)` of ABLR (2.30)
agrees with the ℂ-bilinear invariant form; see `Core.GradedUnitarity.sesqForm_eq_form_of_fixes`.
This is the only property of `ρ` that the reduction in `Core.GradedUnitarity` uses. -/
def Fixes (S : Set 𝒱) : Prop := ∀ x ∈ S, R.rho x = x

theorem Fixes.apply {W' : VertexOperatorAlgebra 𝒱} {R' : RealStructure W'} {S : Set 𝒱}
    (h : R'.Fixes S) {x : 𝒱} (hx : x ∈ S) : R'.rho x = x := h x hx

/-- On a `ρ`-fixed weight space the parity is forced to `1` (whenever that space is nonzero):
`v = ρ(ρ v) = parity h • v`. -/
theorem parity_eq_one_of_fixes {h : ℤ} {S : Set 𝒱} (hfix : R.Fixes S) {v : 𝒱} (hv : v ∈ S)
    (hgr : v ∈ W.grading h) (hne : v ≠ 0) : R.parity h = 1 := by
  have h1 : R.rho (R.rho v) = v := by rw [hfix.apply hv, hfix.apply hv]
  have h2 : R.parity h • v = v := by rw [← R.sq v hgr, h1]
  have : (R.parity h - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
  rcases smul_eq_zero.mp this with hz | hz
  · exact sub_eq_zero.mp hz
  · exact absurd hz hne

end RealStructure

end VOA
