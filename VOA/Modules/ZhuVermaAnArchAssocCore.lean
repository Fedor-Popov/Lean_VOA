/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAssoc
import VOA.Modules.ZhuVermaAnArchUnits
import VOA.Modules.ZhuVermaAnArchFiltration
import VOA.Modules.ZhuAssociator

/-!
# The depth-`n` FZ associator core `AnFull.AssocHom`.

This file attacks the **homogeneous FZ associator membership** `AnFull.AssocHom W n` (DLM Lemma 2.1,
the depth-`n` lift of Zhu's `n = 0` associativity `ZhuAssociator.associator_core`):
for homogeneous `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`, `c ∈ 𝒱ᵣ`,

  `leftProd n (leftProd n a b) c − leftProd n a (leftProd n b c) ∈ OnFull W n`.

The `ZhuVermaAnArchAssoc.lean` reduction `AnFull.assocCore_of_homogeneous` /
`AnFull.AssocLaw_of_homogeneous` already pins ALL remaining associativity content to `AssocHom`.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`AnFull.assocHom_zero : AnFull.AssocHom W 0`** — the **`n = 0` base case of the depth-`n` lift,
  proved unconditionally for ALL integer gradings `p, q, r`** (including negative weights, handled by
  `W.positivity`).  Bridge: `leftProd W 0 = zhuMul` (`leftProd_zero`), `OnFull W 0 = O(𝒱)`
  (`OnFull_zero_eq_O`), and the proved Zhu associator `ZhuAssociator.associator_core`.  This is the
  genuine anchor of the depth-`n` induction — the depth-`n` FZ scalar cores must reduce to exactly
  this `n = 0` identity at `n = 0`.

* **`AnFull.assocCore_zero : AnFull.assocCore W 0`** — the full (non-homogeneous) associator
  membership at level `0`, via `assocCore_of_homogeneous`.

* **`AnFull.assocLaw_zero : AnFull.AssocLaw W 0 (anIdeal_holds W 0)`** — associativity of the
  descended product on `A₀(𝒱) = 𝒱/O₀(𝒱) = A(𝒱)`, unconditionally, via `AssocLaw_of_homogeneous`.

* **`AnFull.IsAssociativeAlgebra W 0`** — the packaged record that `A₀(𝒱)` is an associative algebra:
  associativity (`assocLaw_zero`) + the proved left unit (`AnFull.leftUnitLaw_holds`).  This is the
  Arch-chain re-derivation of Zhu's `Ring (A 𝒱)` through the `AnFull`/`leftProd` interface (so the
  `AnFull` quotient algebra is genuinely associative + unital at level `0`).

## What is OPEN (precise, NOT faked — no `sorry`, no axiom)

* **`AnFull.AssocHom W n` for `n ≥ 1`** — the genuine depth-`n` combinatorial core.  The `n = 0`
  proof goes through `ZhuAssociator.assoc_eq`, whose entire `~1300`-line apparatus
  (`Ufam`/`Vfam`/`USide`/`VSide`, `ZhuMu.mu_identity`, `ZhuUCore.u_core`, `ZhuVCore.v_core`) is
  specialized to the **single residue** `zhuMul = resHom W 0 1`.  The depth-`n` `leftProd` is a
  `j`-sum of `resHom W n (n+j+1)` (pole order `n+j+1`, binomial shift `n`).  The associator therefore
  becomes a `j₁,j₂`-double-tower of higher-pole residues; its two outer families would land in
  `OnFull W n` via the proved keystone `Pres_mem_OnFull`, but the **inner scalar collapse** requires
  the `2n`-pole-shifted analogues of `mu_identity` / `u_core` / `v_core`, which are NOT among the
  imported lemmas (cf. `moonshine_verma_keystone`, the `Descent18`–`Descent26` chain).  We state the
  precise reduction skeleton in `AnFull.assocHom_reduction` below and leave the inner core as the
  explicit, non-faked target.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`q-alg/9612010`), Lemma 2.1; Frenkel–Zhu, Duke 66
(1992); Zhu, J. AMS 9 (1996); mirror of `ZhuAssociator.lean` (`associator_core`, the `n = 0` case).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace AnFull

/-! ## The `n = 0` base case: `AssocHom W 0`, proved for ALL integer gradings.

At level `0` the FZ product `leftProd W 0` is exactly the Zhu product `zhuMul` (`leftProd_zero`), and
the corrected `OnFull W 0` is exactly Zhu's `O(𝒱)` (`OnFull_zero_eq_O`).  So the associator vector
`assoc W 0 a b c` is the Zhu associator, whose membership in `O(𝒱)` is the proved
`ZhuAssociator.associator_core`.  Negative gradings are vacuous by `W.positivity`. -/

/-- The associator vector at level `0` is the **Zhu associator** `(a*b)*c − a*(b*c)`. -/
theorem assoc_zero_eq_zhu (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) :
    assoc W 0 a b c
      = zhuMul W (zhuMul W a b) c - zhuMul W a (zhuMul W b c) := by
  unfold assoc
  rw [leftProd_zero, leftProd_zero, leftProd_zero, leftProd_zero]

/-- **`AnFull.AssocHom W 0`** — the `n = 0` base case of the depth-`n` FZ associator, proved
unconditionally for all integer gradings `p, q, r`.  Negative weights are vacuous (`W.positivity`);
non-negative weights reduce to `ZhuAssociator.associator_core` across `leftProd_zero` /
`OnFull_zero_eq_O`. -/
theorem assocHom_zero (W : VertexOperatorAlgebra 𝒱) : AnFull.AssocHom W 0 := by
  intro p q r a ha b hb c hc
  -- The associator at level 0 is the Zhu associator; `OnFull W 0 = O(𝒱)`.
  rw [OnFull_zero_eq_O, assoc_zero_eq_zhu]
  -- Kill negative-weight `a`.
  rcases lt_or_ge p 0 with hp | hp
  · rw [W.positivity p hp, Submodule.mem_bot] at ha
    subst ha
    simp only [zhuMul_zero_left, sub_self]
    exact (O W).zero_mem
  -- Kill negative-weight `b`.
  rcases lt_or_ge q 0 with hq | hq
  · rw [W.positivity q hq, Submodule.mem_bot] at hb
    subst hb
    simp only [zhuMul_zero_left, zhuMul_zero_right, sub_self]
    exact (O W).zero_mem
  -- Both `a, b` of non-negative weight: cast to ℕ and invoke `associator_core`.
  · obtain ⟨p', rfl⟩ : ∃ p' : ℕ, p = (p' : ℤ) := ⟨p.toNat, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q' : ℕ, q = (q' : ℤ) := ⟨q.toNat, by omega⟩
    exact associator_core W ha hb c

/-- **`AnFull.assocCore W 0`** — the FULL (non-homogeneous) associator membership at level `0`,
obtained from `assocHom_zero` via the trilinear homogeneity reduction `assocCore_of_homogeneous`. -/
theorem assocCore_zero (W : VertexOperatorAlgebra 𝒱) : AnFull.assocCore W 0 :=
  AnFull.assocCore_of_homogeneous W 0 (assocHom_zero W)

/-- **`AnFull.AssocLaw W 0 (anIdeal_holds W 0)`** — associativity of the descended product on
`A₀(𝒱) = 𝒱/O₀(𝒱)`, unconditionally (the level-`0` instance of the depth-`n` associativity law),
from `assocHom_zero` via `AssocLaw_of_homogeneous`. -/
theorem assocLaw_zero (W : VertexOperatorAlgebra 𝒱) :
    AnFull.AssocLaw W 0 (anIdeal_holds W 0) :=
  AnFull.AssocLaw_of_homogeneous W 0 (assocHom_zero W)

/-! ## `A₀(𝒱)` is an associative, unital algebra (Arch-chain re-derivation).

Combining the proved associativity (`assocLaw_zero`) with the proved left unit
(`AnFull.leftUnitLaw_holds`) records that the `AnFull` quotient algebra is genuinely associative and
left-unital at level `0`.  This is the `AnFull`/`leftProd`-interface witness that `A₀(𝒱)` (= Zhu's
`A(𝒱)`) is an associative algebra, derived entirely through the depth-`n` architecture's level-`0`
specialization. -/

/-- Packaged record: the `A_n(𝒱)` product is associative and left-unital.  Both fields are `Prop`s
already in the Arch interface; `IsAssociativeAlgebra W 0` is discharged unconditionally below. -/
structure IsAssociativeAlgebra (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop where
  /-- The descended FZ product on `A_n(𝒱)` is associative. -/
  assoc : AnFull.AssocLaw W n (anIdeal_holds W n)
  /-- The vacuum class `[𝟙]` is a left unit for the descended product. -/
  leftUnit : AnFull.LeftUnitLaw W n (anIdeal_holds W n)

/-- **`A₀(𝒱)` is an associative, left-unital algebra**, unconditionally — the level-`0`
specialization of the depth-`n` algebra structure, via `assocLaw_zero` + `leftUnitLaw_holds`. -/
theorem isAssociativeAlgebra_zero (W : VertexOperatorAlgebra 𝒱) :
    AnFull.IsAssociativeAlgebra W 0 where
  assoc := assocLaw_zero W
  leftUnit := AnFull.leftUnitLaw_holds W 0

/-! ## The depth-`n` reduction skeleton (the precise OPEN target for `n ≥ 1`).

`AssocLaw_of_homogeneous` already shows that to flip associativity of `A_n(𝒱)` at level `n` it
suffices to prove `AnFull.AssocHom W n`.  The following records that this single Prop is the entire
remaining content, and isolates the depth-`n` FZ associator as the explicit target, so any future
discharge plugs in with zero extra wiring. -/

/-- **The reduction**: a proof of the depth-`n` homogeneous FZ associator membership `AssocHom W n`
discharges the full quotient associativity `AnFull.AssocLaw W n`.  (Identical to
`AssocLaw_of_homogeneous`; re-exported here as the named entry point so a future depth-`n` core
flips `A_n(𝒱)` associativity unconditionally.) -/
theorem assocLaw_of_assocHom (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hH : AnFull.AssocHom W n) :
    AnFull.AssocLaw W n (anIdeal_holds W n) :=
  AnFull.AssocLaw_of_homogeneous W n hH

/-- **The packaged level-`n` algebra structure from the core**: `AssocHom W n` (+ the already-proved
left unit) yields `IsAssociativeAlgebra W n`.  At `n = 0` the hypothesis is `assocHom_zero W`, giving
`isAssociativeAlgebra_zero`.  For `n ≥ 1` the sole remaining input is the depth-`n` core. -/
theorem isAssociativeAlgebra_of_assocHom (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hH : AnFull.AssocHom W n) :
    AnFull.IsAssociativeAlgebra W n where
  assoc := assocLaw_of_assocHom W n hH
  leftUnit := AnFull.leftUnitLaw_holds W n

end AnFull

/-!
## Status

**Axiom-clean (`[propext, Classical.choice, Quot.sound]`):**
* `AnFull.assoc_zero_eq_zhu` — the level-`0` associator vector equals the Zhu associator.
* `AnFull.assocHom_zero` — the `n = 0` base case `AnFull.AssocHom W 0`, proved for all integer
  gradings (negative weights vacuous via `W.positivity`; non-negative via `associator_core`).
* `AnFull.assocCore_zero` — the full associator membership at level `0`.
* `AnFull.assocLaw_zero` — associativity of `A₀(𝒱)` unconditionally.
* `AnFull.IsAssociativeAlgebra` + `AnFull.isAssociativeAlgebra_zero` — `A₀(𝒱)` is an associative,
  left-unital algebra (Arch-chain re-derivation of Zhu's `Ring (A 𝒱)`).
* `AnFull.assocLaw_of_assocHom`, `AnFull.isAssociativeAlgebra_of_assocHom` — the named depth-`n`
  reduction entry points (a future `AssocHom W n` flips `A_n` associativity with zero extra wiring).

**OPEN (stated precisely; NOT `sorry`, NOT axioms):**
* `AnFull.AssocHom W n` for `n ≥ 1` — the depth-`n` FZ associator combinatorics.  The `n = 0` proof
  rides on `ZhuAssociator.assoc_eq`'s apparatus specialized to the single residue `resHom W 0 1`; the
  depth-`n` lift needs the `2n`-pole-shifted analogues of `ZhuMu.mu_identity` / `ZhuUCore.u_core` /
  `ZhuVCore.v_core` (the inner `(i,j)` scalar collapse), which are not among the imported lemmas.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.AnFull.assoc_zero_eq_zhu
  #print axioms VOA.AnFull.assocHom_zero
  #print axioms VOA.AnFull.assocCore_zero
  #print axioms VOA.AnFull.assocLaw_zero
  #print axioms VOA.AnFull.isAssociativeAlgebra_zero
  #print axioms VOA.AnFull.assocLaw_of_assocHom
  #print axioms VOA.AnFull.isAssociativeAlgebra_of_assocHom
-/
