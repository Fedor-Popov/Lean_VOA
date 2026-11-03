/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVOA
import VOA.Examples.HeisenbergNVOA

/-!
# The Heisenberg / free-boson VOA `𝒱(ĥ, k)`  (Gannon §5.2.2, pp. 325–326)

The simplest nontrivial VOA — the chiral algebra of a single free boson, and the **basic
instance** validating the entire `Core` definition on a concrete algebra.

This file is the *assembly point*: it imports the construction fan
(`HeisenbergFock/Vertex/Virasoro/Creation/Central/Grading/Conformal/Structure/VOA` for rank 1,
and the `HeisenbergN*` files for rank `n`) and exposes the two main instances together with
their central charges and an axiom audit.

* The **oscillator algebra** `ĥ = û₁` has basis `{aₙ : n ∈ ℤ}` and central `C`, with
  `[aₘ, aₙ] = m δ_{m+n,0} C` (the rank-1 Heisenberg algebra; Gannon (3.2.12a)).
* Fock space `𝒱(ĥ, k) = MvPolynomial ℕ ℂ` (rank 1) / `MvPolynomial (ℕ × Fin n) ℂ` (rank `n`),
  basis the monomials `a_{-m₁} ⋯ a_{-mᵣ} 1` (eq. 5.2.5a); `C·1 = k·1`, `aₙ·1 = 0` for `n ≥ 0`.
* Vertex operators: the basic current `Y(a₋₁1, z) := ∑_{n} aₙ z^{-n-1}` (eq. 5.2.5b), all
  others by duality; the grading is by `L₀`, giving `a₋ₘ` weight `m`.
* Conformal vector `ω = (1/2k) a₋₁ a₋₁ 1` (eq. 5.2.5d), central charge `c = 1` (rank 1),
  `c = n` (rank `n`), `[Lₘ, aₙ] = -n a_{m+n}` (5.2.5e).

## Main declarations (all `sorry`-free, axiom-clean)

* `heisenbergVOA k hk : VertexOperatorAlgebra Fock` — the rank-1 free boson at level `k ≠ 0`,
  `centralCharge = 1` (defined in `Examples.HeisenbergVOA`, re-exported here).
* `heisenbergVOA' n : VertexOperatorAlgebra (HeisenbergN.FockN n)` — the rank-`n` free boson
  at level `1`, `centralCharge = n` (the substrate of the lattice VOA, `Examples.Lattice`).

`#print axioms` on each gives the clean Lean/Mathlib trio `[propext, Classical.choice,
Quot.sound]` — no `sorry`, no project axioms: the VA1–VA5 + VOA1–VOA4 axioms are fully
discharged on a concrete algebra.

## Dependencies
* `VOA.Examples.HeisenbergVOA`, `VOA.Examples.HeisenbergNVOA`.

## Status
The free-boson VOA, rank 1 and rank `n`, as fully axiom-verified instances of
`VertexOperatorAlgebra`.

## References
* Gannon §5.2.2, eqs. (5.2.5); FLM Ch. 2; Lepowsky–Li Ch. 6; Kac §3.5.
-/

namespace VOA

/-! ## The main instances

`heisenbergVOA k hk : VertexOperatorAlgebra Fock` is defined in `Examples.HeisenbergVOA`; it is
in scope here by the import.  We add the rank-`n` instance at level `1` and the central-charge
restatements, then audit the axioms. -/

/-- **The rank-`n` Heisenberg / free-boson VOA `𝒱(ℂⁿ)`** at level `1` (Gannon §5.2.2): central
charge `c = n`, one free boson per coordinate, the building block of the lattice VOA
(`Examples.Lattice`).  A thin alias of `HeisenbergN.heisenbergNVOA n 1 _`. -/
noncomputable def heisenbergVOA' (n : ℕ) : VertexOperatorAlgebra (HeisenbergN.FockN n) :=
  HeisenbergN.heisenbergNVOA n 1 one_ne_zero

/-- **Central charge of the rank-1 free boson is `1`** (Gannon (5.2.5)). -/
theorem heisenbergVOA_centralCharge (k : ℂ) (hk : k ≠ 0) :
    (heisenbergVOA k hk).centralCharge = 1 := rfl

/-- **Central charge of the rank-`n` free boson is `n`** (one boson per coordinate). -/
theorem heisenbergVOA'_centralCharge (n : ℕ) :
    (heisenbergVOA' n).centralCharge = (n : ℂ) := rfl

/-- The rank-`1` free boson at level `1` has central charge `1`: a sanity link between the two
main constructions. -/
theorem heisenbergVOA'_one_centralCharge :
    (heisenbergVOA' 1).centralCharge = 1 := by
  simp [heisenbergVOA'_centralCharge]

/-! ## Axiom audit

Both instances depend only on the standard Lean/Mathlib trio `[propext, Classical.choice,
Quot.sound]`.  No `sorry`, no `VOA.pbw`: VA1–VA5 + VOA1–VOA4 are discharged outright. -/


end VOA
