/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Base

/-!
# Dong–Jiang Lemma 2.8 — the induction-on-`n` scaffold for `V ∗ⁿ₀ O(V) ⊆ O_{n,0}(V)`.

The sole open Half-A core is `anmRightDiff W n K a c d ∈ Onm W n 0`
(`ZhuVermaAnArchAnmRightDiff.MUGradedAction_of_HARDhom`).  By `anmRightDiff_eq_terms`,

  `anmRightDiff W n K a c d
     = anmRight W n 0 a (anmCirc W 0 0 c d) − anmRight W n 0 a (anmCirc W n 0 c d)`,
    `                    └──────── Term₁ ────────┘   └──────── Term₂ ────────┘`

so `anmRightDiff ∈ Onm W n 0` follows from the two **raw membership** statements

  `(Term₁)   anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0`   ( = `𝒱 ∗ⁿ₀ O(𝒱)-circle ⊆ O_{n,0}` )
  `(Term₂)   anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0`   ( = `𝒱 ∗ⁿ₀ O_{n,0}-circle ⊆ O_{n,0}` )

by `Submodule.sub_mem` — **no explicit tower-coefficient decomposition required** (a route through
named coefficient families hits a wall at grade ≥ 2; the raw memberships do not).

## The induction on the level `n`

We package the two pieces as per-level predicates `Term1Level`/`Term2Level` and reduce the whole
Half-A crux `MUGradedAction W` to

  `(∀ n, Term1Level W n)   and   (∀ n, Term2Level W n)`,

each of which is to be proved by **induction on `n`**:

* **Base `n = 0`** — proved.  Both `Term1Level W 0` and `Term2Level W 0` are the coincident level-`0`
  circle membership `anmRight W 0 0 a (anmCirc W 0 0 c d) ∈ Onm W 0 0`, which is Zhu's two-sided ideal
  property `𝒱 ∗ O(𝒱) ⊆ O(𝒱)` (`ZhuVermaAnArchDJ28Base.anmRight_circ_base`, via `zhuRingData_holds`
  and `Onm_zero_zero_eq_O`).
* **Step `n → n+1`** — the genuine Dong–Jiang inter-level content (`math/0601626`, §2 Lemmas 2.2–2.8),
  the OPEN obligation `TermInductiveStep` recorded below.

## Proved here (axiom-clean)

* `Term1Level`, `Term2Level` — the two per-level raw-membership predicates.
* `anmRightDiff_mem_of_raw` — `anmRightDiff ∈ Onm` from the two raw memberships (`Submodule.sub_mem`).
* `Term1Level_base`, `Term2Level_base` — the `n = 0` base cases (the Zhu ideal).
* `HARDhom_of_TermLevels` / `MUGradedAction_of_TermLevels` — the full `MUGradedAction W` from
  `(∀ n, Term1Level W n)` + `(∀ n, Term2Level W n)`.
* `TermInductiveStep` — the precise remaining OPEN obligation (the inductive step, both pieces).
* `TermLevels_of_step` / `MUGradedAction_of_step` — closing `MUGradedAction W` from the base (done)
  + `TermInductiveStep` alone (`Nat.rec`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.2–2.8); Dong–Li–Mason,
J. Algebra 206 (1998); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two per-level raw-membership predicates. -/

/-- **`Term1Level W n`** — the level-`0`-inner cross membership `𝒱 ∗ⁿ₀ O(𝒱)-circle ⊆ O_{n,0}`:
`anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` for all `a c d`.  (Universally quantified — no
homogeneity assumption, since `anmRight`/`anmCirc` are ℂ-bilinear.) -/
def Term1Level (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a c d : 𝒱, anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0

/-- **`Term2Level W n`** — the level-`n`-inner membership `𝒱 ∗ⁿ₀ O_{n,0}-circle ⊆ O_{n,0}`:
`anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0` for all `a c d`. -/
def Term2Level (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a c d : 𝒱, anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0

/-! ## `anmRightDiff ∈ Onm` from the two raw memberships. -/

/-- **`anmRightDiff ∈ Onm W n 0` from the two raw memberships** (homogeneous `a ∈ 𝒱_K`).  By
`anmRightDiff_eq_terms`, `anmRightDiff = Term₁ − Term₂`; `Submodule.sub_mem` finishes.  This is the
tower-free reduction: it consumes only the plain memberships, not any explicit decomposition. -/
theorem anmRightDiff_mem_of_raw (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱)
    (hT1 : anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0)
    (hT2 : anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0) :
    anmRightDiff W n K a c d ∈ Onm W n 0 := by
  rw [anmRightDiff_eq_terms W n ha c d]
  exact Submodule.sub_mem _ hT1 hT2

/-! ## The base case `n = 0`. -/

/-- **`Term1Level W 0`** (base).  At `n = 0`, `anmRight W 0 0 a (anmCirc W 0 0 c d) ∈ Onm W 0 0` is
Zhu's two-sided ideal property (`anmRight_circ_base`). -/
theorem Term1Level_base (W : VertexOperatorAlgebra 𝒱) : Term1Level W 0 :=
  fun a c d => anmRight_circ_base W a c d

/-- **`Term2Level W 0`** (base).  At `n = 0` the inner circle `anmCirc W 0 0 c d` coincides with
`anmCirc W 0 0 c d`, so this is the same Zhu ideal membership as `Term1Level_base`. -/
theorem Term2Level_base (W : VertexOperatorAlgebra 𝒱) : Term2Level W 0 :=
  fun a c d => anmRight_circ_base W a c d

/-! ## Reducing `MUGradedAction W` to the two per-level predicates (all `n`). -/

/-- **The homogeneous `(HARD)` from the two per-level predicates.**  For every `n`,
`Term1Level W n` (Term₁) and `Term2Level W n` (Term₂) give `anmRightDiff ∈ Onm W n 0` at homogeneous
`a` (via `anmRightDiff_mem_of_raw`). -/
theorem HARDhom_of_TermLevels (W : VertexOperatorAlgebra 𝒱)
    (hT1 : ∀ n, Term1Level W n) (hT2 : ∀ n, Term2Level W n) :
    ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), anmRightDiff W n K a c d ∈ Onm W n 0 :=
  fun n _K _M _P a ha c _ d _ => anmRightDiff_mem_of_raw W n ha c d (hT1 n a c d) (hT2 n a c d)

/-- **`MUGradedAction W` from the two per-level predicates.**  Supplying `Term1Level W n` and
`Term2Level W n` for every `n` closes the Dong–Jiang `M(U)` graded-action crux, via the in-repo
`MUGradedAction_of_HARDhom`. -/
theorem MUGradedAction_of_TermLevels (W : VertexOperatorAlgebra 𝒱)
    (hT1 : ∀ n, Term1Level W n) (hT2 : ∀ n, Term2Level W n) :
    MUGradedAction W :=
  MUGradedAction_of_HARDhom W (HARDhom_of_TermLevels W hT1 hT2)

/-! ## The remaining OPEN obligation: the inductive step `n → n+1`. -/

/-- **The inductive step of the DJ Lemma 2.8 induction on `n`** (the genuine remaining content).  For
every `n`, the level-`n` memberships imply the level-`(n+1)` memberships, *for both pieces*:

  `Term1Level W n → Term2Level W n → Term1Level W (n+1) ∧ Term2Level W (n+1)`.

This is the Dong–Jiang inter-level recursion (`math/0601626`, §2 Lemmas 2.2–2.8): relating the
level-`(n+1)` products `a ∗^{n+1}_0 (c ∘^k_0 d)` (`k = 0, n+1`) to the level-`n` data plus terms
manifestly in `O_{n+1,0}`.  Both pieces are engine-verified TRUE on the rank-1 free boson; the
constructive inter-level identity is the open target.  (Stated as one predicate carrying both pieces
because the DJ recursion couples them: the level-`(n+1)` circle `c ∘^{n+1}_0 d` is built from the
level-`n` circle via the grading/pole-shift relations, so `Term₂` at `n+1` naturally consumes `Term₁`
and `Term₂` at `n`.) -/
def TermInductiveStep (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ n, Term1Level W n → Term2Level W n → (Term1Level W (n + 1) ∧ Term2Level W (n + 1))

/-- **Both per-level families from the base + the inductive step** (`Nat.rec`).  Given the (proven)
base cases and `TermInductiveStep`, `Term1Level W n` and `Term2Level W n` hold for every `n`. -/
theorem TermLevels_of_step (W : VertexOperatorAlgebra 𝒱) (hstep : TermInductiveStep W) :
    ∀ n, Term1Level W n ∧ Term2Level W n := by
  intro n
  induction n with
  | zero => exact ⟨Term1Level_base W, Term2Level_base W⟩
  | succ k ih => exact hstep k ih.1 ih.2

/-- **`MUGradedAction W` from the inductive step alone** (the base is discharged).  The single
remaining obligation for Half A's `anmRightDiff` core is `TermInductiveStep W`. -/
theorem MUGradedAction_of_step (W : VertexOperatorAlgebra 𝒱) (hstep : TermInductiveStep W) :
    MUGradedAction W :=
  MUGradedAction_of_TermLevels W
    (fun n => (TermLevels_of_step W hstep n).1)
    (fun n => (TermLevels_of_step W hstep n).2)

/-! ## Status — Half A reduced to ONE inductive step, base discharged.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`Term1Level` / `Term2Level`** — the two per-level raw-membership predicates (tower-free).
* **`anmRightDiff_mem_of_raw`** — `anmRightDiff ∈ Onm` from the two raw memberships (`Submodule.sub_mem`),
  bypassing the tower-coefficient decomposition entirely.
* **`Term1Level_base` / `Term2Level_base`** — the `n = 0` base cases (Zhu's two-sided ideal, proved).
* **`MUGradedAction_of_TermLevels`** — the Half-A crux `MUGradedAction W` from the two per-level
  families (all `n`).
* **`MUGradedAction_of_step`** — `MUGradedAction W` from the base (done) + the single OPEN obligation
  `TermInductiveStep W`.

**The single remaining OPEN obligation:** `TermInductiveStep W` — the Dong–Jiang inter-level recursion
`n → n+1` for the two circle-carrying memberships.  NOT an axiom, NOT `sorry`'d: it is the precise,
engine-verified-TRUE identity whose constructive form is the open Half-A step.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmRightDiff_mem_of_raw
  #print axioms VOA.Term1Level_base
  #print axioms VOA.Term2Level_base
  #print axioms VOA.MUGradedAction_of_TermLevels
  #print axioms VOA.MUGradedAction_of_step
-/
