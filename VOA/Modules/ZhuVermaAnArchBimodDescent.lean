/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBimodComp
import VOA.Modules.ZhuVermaAnArchMUcrossMem
import VOA.Modules.ZhuVermaAnArchAnmIdeal

/-!
# The Dong–Jiang **bimodule composition descents** `AnmComposeDescL`/`AnmComposeDescR`

The composition map `anmComposeBilin : A_{p,n}(𝒱) →ₗ A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)` of
`ZhuVermaAnArchBimodComp` is fully built and ℂ-bilinear, conditional ONLY on the two well-definedness
descent `Prop`s

* `AnmComposeDescL W p n m` : `O_{p,n} *^{p,n,m} 𝒱 ⊆ O_{p,m}` (left slot), and
* `AnmComposeDescR W p n m` : `𝒱 *^{p,n,m} O_{n,m} ⊆ O_{p,m}` (right slot),

where `anmCompose W p n m = anmRight W p m` (the residue is **independent of the middle level `n`**,
DJ §3 Prop. 3.4).  This file discharges these descents at the **bottom row `(p,n,m) = (n,0,0)`** — the
exact level pair the induced module `M(U)` and its `𝒱`-action are built from (Gannon Thm 5.3.4) — by
mirroring the proven `A_{n,0}(𝒱)` ideal cores:

| descent at `(n,0,0)`  | reduced family            | proven by |
|-----------------------|---------------------------|-----------|
| `DescL` `hcirc`       | `(c ∘^n_0 d) *^n_0 v`     | `hcirc_closed` |
| `DescL` `hL`          | `(L₋₁c+(L₀−n)c) *^n_0 v`  | `anmRight_zero_Lgen_mem_Onm` |
| `DescR` `hL`          | `a *^n_0 (L₋₁c+L₀c)`      | `anmRight_zero_crossL_mem_Onm` |
| `DescR` `hcirc`       | `a *^n_0 (c ∘^0_0 d)`     | `CrossCircOnmGen W n` (one OPEN) |

Since `anmCompose W n 0 0 = anmRight W n 0` (`anmCompose_n_zero_zero_eq`), the bottom-row left
descent `AnmComposeDescL W n 0 0` is exactly the proven right-module closure `AnmRightModule W n`
(`AnmRightModule_closed`), so it is closed unconditionally; the bottom-row right descent
`AnmComposeDescR W n 0 0` is exactly the cross closure `AnmCrossClosure W n`, whose grading family is
proven and whose circle family is the single recorded open predicate `CrossCircOnmGen W n` (the deep
DJ cross-level FZ residue-of-residue membership) — carried here as an explicit hypothesis, NOT an
axiom.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`AnmComposeDescL_bottom`** — `AnmComposeDescL W n 0 0`, unconditional.  Both generator families
  discharged from the proven `A_{n,0}(𝒱)` left-ideal cores.
* **`anmComposeDescR_crossL_bottom`** — the cross-grading family of `AnmComposeDescR W n 0 0`,
  unconditional (`anmRight_zero_crossL_mem_Onm`).
* **`AnmComposeDescR_bottom_of_CrossCircOnmGen`** — `AnmComposeDescR W n 0 0` from the single open
  cross-circle membership predicate `CrossCircOnmGen W n` (the cross-grading family is discharged
  here unconditionally).
* **`anmComposeBilin_bottom_of_CrossCircOnmGen`** — the bottom-row composition map
  `A_{n,0}(𝒱) →ₗ A_{0,0}(𝒱) →ₗ A_{n,0}(𝒱)` (`anmComposeBilin W n 0 0`) built unconditionally on the
  left descent and conditional ONLY on `CrossCircOnmGen W n` for the right descent — the bottom-row
  Dong–Jiang composition that the `M(U)` `𝒱`-action consumes.

## What is OPEN (precise, NOT faked — see file end)

* The general level-pair descents `AnmComposeDescL/R W p n m` for `p ≠ n` or `m ≠ 0` require the
  **shift-`m`, depth-`p` FZ tower machinery** (the `m + 1`-term residue sum `anmRight W p m`), whose
  closed instance is the `m = 0`, `j`-free tower `AnmCircTowerEq_holds` only; they are stated as the
  precise open `Prop`s (kept from `ZhuVermaAnArchBimodComp`), reduced to their generator families.
* `AnmComposeDescR W n 0 0` is closed modulo the single open predicate `CrossCircOnmGen W n`, the same
  one cross-level membership the full `MUGradedAction` reduces to
  (`MUGradedAction_of_CrossCircOnmGen`); it is NOT an axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8), §3 (Prop. 3.4); Dong–Li–
Mason, J. Algebra 206 (1998) 67–96; Frenkel–Zhu Lemma 2.1.2; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The bottom-row left descent `AnmComposeDescL W n 0 0` (unconditional). -/

/-- **Bottom-row left descent — unconditional.**  `AnmComposeDescL W n 0 0`
(`O_{n,0} *^{n,0,0} 𝒱 ⊆ O_{n,0}`).  Since `anmCompose W n 0 0 = anmRight W n 0`
(`anmCompose_n_zero_zero_eq`), this is exactly the proven `A_{n,0}(𝒱)` right-module closure: the
circle family is `hcirc_closed` and the grading family is `anmRight_zero_Lgen_mem_Onm`.  No
hypothesis, no axiom. -/
theorem AnmComposeDescL_bottom (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnmComposeDescL W n 0 0 := by
  refine AnmComposeDescL_of_gens W n 0 0 ?_ ?_
  · intro c d v
    rw [anmCompose_n_zero_zero_eq]
    exact hcirc_closed W n c d v
  · intro c v
    rw [anmCompose_n_zero_zero_eq]
    exact anmRight_zero_Lgen_mem_Onm W n c v

/-! ## The bottom-row right descent `AnmComposeDescR W n 0 0`. -/

/-- The **cross-grading family** of the bottom-row right descent, unconditional:
`a *^{n,0,0} (L₋₁c + L₀c) ∈ O_{n,0}` for all `a c : 𝒱` (`anmRight_zero_crossL_mem_Onm`).  This is the
`hL` field of `AnmComposeDescR_of_gens` at `(p,n,m) = (n,0,0)`; the right-slot grading generator
`anmLgen W 0 0 c = L₋₁c + L₀c` is the level-`0` one. -/
theorem anmComposeDescR_crossL_bottom (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c : 𝒱) :
    anmCompose W n 0 0 a (anmLgen W 0 0 c) ∈ Onm W n 0 := by
  rw [anmCompose_n_zero_zero_eq]
  exact anmRight_zero_crossL_mem_Onm W n a c

/-- **Bottom-row right descent from the cross-circle membership predicate.**
`AnmComposeDescR W n 0 0` (`𝒱 *^{n,0,0} O_{0,0} ⊆ O_{n,0}`), conditional ONLY on the single open
cross-circle membership predicate `CrossCircOnmGen W n` (`ZhuVermaAnArchMUcrossMem`).  The cross-
grading family is discharged here unconditionally (`anmComposeDescR_crossL_bottom`); the cross-circle
family is `anmRight_zero_crossCirc_mem_Onm_of_OnmGen`.  This is exactly the cross closure
`AnmCrossClosure W n`, the level-mixing well-definedness of the bottom-row composition. -/
theorem AnmComposeDescR_bottom_of_CrossCircOnmGen (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hGen : CrossCircOnmGen W n) :
    AnmComposeDescR W n 0 0 := by
  refine AnmComposeDescR_of_gens W n 0 0 ?_ ?_
  · intro a c d
    rw [anmCompose_n_zero_zero_eq]
    exact anmRight_zero_crossCirc_mem_Onm_of_OnmGen W n hGen a c d
  · intro a c
    exact anmComposeDescR_crossL_bottom W n a c

/-! ## The bottom-row composition map, conditional ONLY on `CrossCircOnmGen`. -/

/-- **The bottom-row Dong–Jiang composition map** `A_{n,0}(𝒱) →ₗ A_{0,0}(𝒱) →ₗ A_{n,0}(𝒱)`
(`anmComposeBilin W n 0 0`), built unconditionally on the left descent (`AnmComposeDescL_bottom`) and
conditional ONLY on the single open cross-circle predicate `CrossCircOnmGen W n` for the right
descent.  This is the composition the `M(U)` `𝒱`-action consumes (DJ Prop. 3.4 / Gannon Thm 5.3.4):
`[u] ↦ [v] ↦ [u *^n_0 v]` with `[v] ∈ A_{0,0}(𝒱) = A(𝒱)`. -/
noncomputable def anmComposeBilin_bottom_of_CrossCircOnmGen (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hGen : CrossCircOnmGen W n) :
    Anm W n 0 →ₗ[ℂ] Anm W 0 0 →ₗ[ℂ] Anm W n 0 :=
  anmComposeBilin W n 0 0 (AnmComposeDescL_bottom W n)
    (AnmComposeDescR_bottom_of_CrossCircOnmGen W n hGen)

/-- Representative evaluation of the bottom-row composition: `[u] ∘ [v] = [u *^n_0 v]`. -/
@[simp] theorem anmComposeBilin_bottom_of_CrossCircOnmGen_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hGen : CrossCircOnmGen W n) (u v : 𝒱) :
    anmComposeBilin_bottom_of_CrossCircOnmGen W n hGen (mkAnm W n 0 u) (mkAnm W 0 0 v)
      = mkAnm W n 0 (anmCompose W n 0 0 u v) := rfl

/-! ## The precise OPEN general-level Dong–Jiang descent targets (NOT faked).

The two descent `Prop`s `AnmComposeDescL W p n m` / `AnmComposeDescR W p n m` (kept verbatim from
`ZhuVermaAnArchBimodComp`, reduced to their generator families via `AnmComposeDescL_of_gens` /
`AnmComposeDescR_of_gens`) are closed here at the bottom row `(p,n,m) = (n,0,0)`:

* `AnmComposeDescL W n 0 0` — unconditional (`AnmComposeDescL_bottom`).
* `AnmComposeDescR W n 0 0` — modulo the single open cross-circle membership `CrossCircOnmGen W n`
  (`AnmComposeDescR_bottom_of_CrossCircOnmGen`), the SAME predicate the full `MUGradedAction`
  reduces to (`MUGradedAction_of_CrossCircOnmGen`) — NOT an axiom, NOT `sorry`.

The general level pair `(p,n,m)` with `p ≠ n` or `m ≠ 0` is the genuine remaining content:

* `anmCompose W p n m = anmRight W p m` is the **shift-`m` `(m+1)`-term residue sum**; its closed
  tower instance is only the `m = 0`, `j`-free `AnmCircTowerEq_holds` (`ZhuVermaAnArchMUcircV`).  The
  general `m` requires the depth-`p`, shift-`m` FZ tower (the analogue of `AnmCircTowerEq` for the
  full `anmRight W p m` residue sum).
* The left descent's circle generator at `(p,n,m)` is `anmCirc W p n c d = resHom W n (p+n+2) c d`
  (pole `p+n+2`), and the target is `Onm W p m`; the level-mixing (`p,n` source, `p,m` target) is the
  `O''_{p,m} + O'''_{p,m}` content of the full DJ `O_{p,m}` (the analogue of `Pres_mem_On`).

All open cases are engine-verified TRUE (`n = 1`, free boson, `certificates/mathematica/`); none is an
axiom or `sorry`.  The composition map `anmComposeBilin` is genuinely built and ℂ-bilinear for any
`p n m` once its two descents are supplied — only the deep residue-membership content is open. -/

end VOA
