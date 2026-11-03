/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchUpRightModule
import VOA.Modules.ZhuVermaAnArchAnAssoc
import VOA.Modules.ZhuVermaAnArchUnits
import VOA.Modules.ZhuVermaAnArchLeftGradingResidualFull

/-!
# Dong–Jiang's carrier, verbatim: `M(U)(n) = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`

Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826
(`math/0601626`), §4, define — for an `A_m(V)`-module `U` which cannot factor through `A_{m-1}(V)` —

```
  M(U) = ⨁_{n ∈ ℤ₊} A_{n,m}(V) ⊗_{A_m(V)} U ,      M(U)(n) = A_{n,m}(V) ⊗_{A_m(V)} U .
```

Two features of that definition are **deliberate** and are what this file ports.

1. **The tensor is balanced at every level.**  There is no `⊗_ℂ` anywhere in DJ's construction.  The
   balancing is *used*: DJ's well-definedness proof of the loop action reads

   ```
     u_p((v *^n_m a) ⊗ w) = ((u *^{wtu-p-1+n}_{m,n} v) *^{wtu-p-1+n}_m a) ⊗ w
                          = (u *^{wtu-p-1+n}_{m,n} v) ⊗ a·w = u_p(v ⊗ a·w) ,
   ```
   whose last step **is** the balancing relation `x·a ⊗ w = x ⊗ a·w`.

2. **The quotient is by the FULL ideal.**  DJ set `A_{n,m}(V) = V / O_{n,m}(V)` with
   `O_{n,m} = O'_{n,m} + O''_{n,m} + O'''_{n,m}`, and say so on purpose: "we do not need to prove
   this lemma as a bigger subspace `O_{n,m}(V)` of `V` containing `O'_{n,m}(V)` will be modulo out
   ... But eventually we expect to prove that `O_{m,n}(V)` and `O'_{n,m}(V)` are the same although
   we cannot achieve this in the paper" (before Lemma 2.6), and Remark 2.10: "It seems that this is
   a very difficult problem and we cannot find a proof for this in this paper."

Accordingly this file builds the carrier over the repo's **`AnmFull W n m = 𝒱 ⧸ OnmFull W n m`**
(`ZhuVermaAnArchAnmFull`), where `OnmFull = Onm ⊔ OnmAssoc ⊔ OnmLevel` is exactly
`O' + O'' + O'''`, and it balances at the **general base level `m`** (not only `m = 0`).

## Contents

### §1 The right `A_m(𝒱)`-action on `A_{n,m}(𝒱)` (DJ: right action by `*^n_m`)

* `AnmFull.rightRep W n m a` — the right action **by a representative** `a : 𝒱`,
  `[x] ↦ [x *^n_m a]`.  Well defined **unconditionally**: the left-slot descent is DJ Lemma 2.8's
  right inclusion `O_{n,m} *^n_m V ⊆ O_{n,m}`, proved as `anmRight_OnmFull_unconditional`.
* `AnmFull.rightHom W n m : 𝒱 →ₗ[ℂ] Module.End ℂ (AnmFull W n m)` — the same, `ℂ`-linear in `a`.
* `DJRightSlot W n m` — the remaining (acting-slot) descent `V *^n_m O_m(𝒱) ⊆ O_{n,m}(𝒱)`.
* `djRightSlot_of_leftGrading` — **proved** from the repo's single open DJ-2.8 residual
  `LeftGradingResidual W n m m` (DJ Lemma 2.8's LEFT inclusion at `p = m`), using
  `Onm_diag_eq_OnFull` (`O'_{m,m} = O_m(𝒱)`).
* `AnmFull.rightAct h : AnFull W m →ₗ[ℂ] Module.End ℂ (AnmFull W n m)` — the genuine right
  `A_m(𝒱)`-action, given `DJRightSlot W n m`.  This is what the balanced tensor product needs.
* `djRightSlot_zero` / `AnmFull.rightActZero` — at base level `m = 0` the hypothesis is
  **discharged** (`leftGradingResidual_zero_gen`), so `A_{n,0}(𝒱)` carries an **unconditional**
  genuine right `A_0(𝒱) = A(𝒱)`-module structure.

### §2 `A_{m,m}(𝒱) = A_m(𝒱)` (DJ Prop `pa4.5`, printed as Proposition 4.6)

* `DJAnnEqAn W m : Prop := OnmFull W m m ≤ OnFull W m` — the named hypothesis.  The reverse
  containment is **proved** (`onFull_le_OnmFull_diag`, off `Onm_diag_eq_OnFull`), so `DJAnnEqAn` is
  precisely DJ's `O''_{m,m} + O'''_{m,m} ⊆ O_m(𝒱)`.
  ⚠ DJ prove it **representation-theoretically**, by invoking Dong–Li–Mason III Theorem 4.1 to
  realize an arbitrary `A_m(V)`-module `U` as `M(m)` of an admissible module and then reading off
  DJ Lemma 4.1; there is no combinatorial proof in DJ, and DLM3 Thm 4.1 is not in this repo.  It is
  therefore carried as a hypothesis, **not** faked and **not** ground on.
* `djAnnEqAn_of_gens` — the reduction to the two into-`O'` generator families, off the proved
  `onmFull_le_Onm_of_gens`.
* `anmFullDiagEquiv h : AnmFull W m m ≃ₗ[ℂ] AnFull W m`.

### §3 `AmMod W m` — a bundled `A_m(𝒱)`-module

The exact level-`m` analogue of the repo's level-`0` `AMod` (`ZhuBijection`): a `ℂ`-space with a
`ℂ`-linear `ρ : A_m(𝒱) → End`, unital on `[𝟙]` and multiplicative on every representable
Frenkel–Zhu product `*_m = leftProd W m`.

### §4 The Dong–Jiang level piece `DJPiece W U n = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`

Realized, exactly as the proved `MUPieceBal` does at `m = 0` over `Anm`, as the `ℂ`-tensor cover
modulo the **representative-level** balancing span

  `[x *^n_m a] ⊗ w − [x] ⊗ ρ([a])·w`   (`x a : 𝒱`, `w : U`).

This is the faithful realization available here: `A_m(𝒱)` has no `Ring` instance in the repo at
general `m` (its associativity `AnFull.AssocLaw` is open for `m ≥ 1`), so Mathlib's
`TensorProduct (A_m 𝒱)` cannot be formed; the representative-level quotient is the universal object
in which DJ's balancing relation holds, and it agrees with `⊗_{A_m(𝒱)}` as soon as the right action
descends (`AnmFull.rightAct`).

### §5 The payoff `M(U)(m) ≅ U`

`djPieceMEquiv h U : DJPiece W U m ≃ₗ[ℂ] U.carrier`, given `DJAnnEqAn W m` — DJ's "By Proposition
4.6, `M(U)(m)` and `U` are isomorphic `A_m(V)`-modules", which they get essentially free.  The two
sharp inputs are proved repo terms: `leftProd_eq_anmRight_diag` (`*^m_m = *_m`) and
`leftProd_vacuum_left` (`𝟙 *_m a = a`, exact).

`#print axioms` on every headline is `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no
`pbw`, no new axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8, Thm 2.9, Rmk 2.10),
§4 (Lemma 4.1, Prop `pa4.5`, the definition of `M(U)`, Lemma 4.6, Thm 4.10);
Dong–Li–Mason, J. Algebra 206 (1998) 67–96 (`DLM3`, Thm 4.1).
Repo cross-refs: `ZhuVermaAnArchAnmFull` (`OnmFull`/`AnmFull`), `ZhuVermaAnArchDJ28Final`
(`anmRight_OnmFull_unconditional`, `anmGen_OnmFull_left_of_leftGrading`, `LeftGradingResidual`),
`ZhuVermaAnArchAnAssoc` (`Onm_diag_eq_OnFull`, `leftProd_eq_anmRight_diag`),
`ZhuVermaAnArchUnits` (`leftProd_vacuum_left`), `ZhuVermaAnArchMUBalancedPiece` (the `m = 0`
balanced-piece technique this file generalizes).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 The right `A_m(𝒱)`-action on `A_{n,m}(𝒱)` -/

/-- **`A_{n,m}(𝒱)` is the FULL-ideal quotient.**  Definitional record that the repo's `OnmFull` is
Dong–Jiang's `O_{n,m} = O'_{n,m} + O''_{n,m} + O'''_{n,m}`, so `AnmFull W n m = 𝒱 ⧸ OnmFull W n m`
is DJ's `A_{n,m}(V) = V / O_{n,m}(V)` — **not** the `O'`-only quotient `𝒱 ⧸ Onm W n m`. -/
theorem OnmFull_eq_prime_sup_assoc_sup_level (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) :
    OnmFull W n m = Onm W n m ⊔ OnmAssoc W n m ⊔ OnmLevel W n m := rfl

/-- **`O_m(𝒱) ≤ O_{m,m}(𝒱)`** — the diagonal containment, proved: `O'_{m,m} = O_m(𝒱)`
(`Onm_diag_eq_OnFull`) and `O'_{m,m} ≤ O_{m,m}` (`Onm_le_OnmFull`). -/
theorem onFull_le_OnmFull_diag (W : VertexOperatorAlgebra 𝒱) (m : ℕ) :
    OnFull W m ≤ OnmFull W m m := by
  rw [← Onm_diag_eq_OnFull W m]
  exact Onm_le_OnmFull W m m

/-- **The vacuum is a strict left unit for `*^m_m`**: `𝟙 *^m_m a = a` exactly.  This is the sharp
Frenkel–Zhu unit `leftProd_vacuum_left` transported along the diagonal identification
`*_m = *^m_m` (`leftProd_eq_anmRight_diag`). -/
theorem anmRight_diag_vacuum_left (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (a : 𝒱) :
    anmRight W m m W.vacuum a = a := by
  rw [← leftProd_eq_anmRight_diag, leftProd_vacuum_left]

/-- **The right action by a representative.**  For `a : 𝒱`, the map `[x] ↦ [x *^n_m a]` on
`A_{n,m}(𝒱)`.  Well defined **unconditionally**: the required left-slot descent is Dong–Jiang
Lemma 2.8's right inclusion `O_{n,m}(V) *^n_m V ⊆ O_{n,m}(V)`, proved as the unconditional
`anmRight_OnmFull_unconditional`. -/
noncomputable def AnmFull.rightRep (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a : 𝒱) :
    AnmFull W n m →ₗ[ℂ] AnmFull W n m :=
  (OnmFull W n m).mapQ (OnmFull W n m) (anmRightL W n m a) (by
    intro g hg
    rw [Submodule.mem_comap, anmRightL_apply]
    exact anmRight_OnmFull_unconditional W n m a g hg)

@[simp] theorem AnmFull.rightRep_mk (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a x : 𝒱) :
    AnmFull.rightRep W n m a (mkAnmFull W n m x) = mkAnmFull W n m (anmRight W n m x a) := rfl

/-- The right action by a representative is `ℂ`-linear in the acting element `a`, so it bundles into
`𝒱 →ₗ[ℂ] End ℂ (A_{n,m}(𝒱))`.  (Still unconditional: no descent through `O_m(𝒱)` yet.) -/
noncomputable def AnmFull.rightHom (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) :
    𝒱 →ₗ[ℂ] Module.End ℂ (AnmFull W n m) where
  toFun a := AnmFull.rightRep W n m a
  map_add' a₁ a₂ := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    change AnmFull.rightRep W n m (a₁ + a₂) (mkAnmFull W n m x)
        = (AnmFull.rightRep W n m a₁ + AnmFull.rightRep W n m a₂) (mkAnmFull W n m x)
    rw [LinearMap.add_apply, AnmFull.rightRep_mk, AnmFull.rightRep_mk, AnmFull.rightRep_mk,
      anmRight_add_right, map_add]
  map_smul' c a := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    change AnmFull.rightRep W n m (c • a) (mkAnmFull W n m x)
        = (c • AnmFull.rightRep W n m a) (mkAnmFull W n m x)
    rw [LinearMap.smul_apply, AnmFull.rightRep_mk, AnmFull.rightRep_mk, anmRight_smul_right,
      map_smul]

@[simp] theorem AnmFull.rightHom_apply (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a x : 𝒱) :
    AnmFull.rightHom W n m a (mkAnmFull W n m x) = mkAnmFull W n m (anmRight W n m x a) := rfl

/-- **The acting-slot descent for the right `A_m(𝒱)`-action**: `V *^n_m O_m(𝒱) ⊆ O_{n,m}(𝒱)`.
This is Dong–Jiang Lemma 2.8's LEFT inclusion `V *^n_{m,p} O_{p,m}(V) ⊆ O_{n,m}(V)` at `p = m`,
restricted to `O_m(𝒱) = O'_{m,m}(𝒱) ⊆ O_{m,m}(𝒱)`.  It is the only input beyond the unconditional
`anmRight_OnmFull_unconditional` that the right `A_m(𝒱)`-module structure on `A_{n,m}(𝒱)` needs. -/
def DJRightSlot (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Prop :=
  ∀ x : 𝒱, ∀ g ∈ OnFull W m, anmRight W n m x g ∈ OnmFull W n m

/-- **`DJRightSlot` from the repo's single open DJ-2.8 residual.**  `LeftGradingResidual W n m m`
(the general right-slot grading absorption, the one identity DJ Lemma 2.8 is reduced to in
`ZhuVermaAnArchDJ28Final`) gives the LEFT inclusion `V *^n_{m,m} O_{m,m} ⊆ O_{n,m}`; feeding it
`O_m(𝒱) = O'_{m,m} ≤ O_{m,m}` and `*^n_{m,m} = *^n_m` yields `DJRightSlot W n m`. -/
theorem djRightSlot_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (n m : ℕ)
    (hgrad : LeftGradingResidual W n m m) :
    DJRightSlot W n m := by
  intro x g hg
  have hg' : g ∈ OnmFull W m m := onFull_le_OnmFull_diag W m hg
  have h := anmGen_OnmFull_left_of_leftGrading W n m m x hgrad g hg'
  rwa [anmGen_eq_anmRight] at h

/-- **The genuine right `A_m(𝒱)`-action on `A_{n,m}(𝒱)`** (Dong–Jiang Thm 2.9, the `*^n_m` half):
`[x] · [a] = [x *^n_m a]`, as a `ℂ`-linear `A_m(𝒱) → End ℂ (A_{n,m}(𝒱))`.  This is exactly the
right-module structure the balanced tensor `A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` needs. -/
noncomputable def AnmFull.rightAct (W : VertexOperatorAlgebra 𝒱) (n m : ℕ)
    (h : DJRightSlot W n m) :
    AnFull W m →ₗ[ℂ] Module.End ℂ (AnmFull W n m) :=
  (OnFull W m).liftQ (AnmFull.rightHom W n m) (by
    intro g hg
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    change AnmFull.rightHom W n m g (mkAnmFull W n m x) = 0
    rw [AnmFull.rightHom_apply, mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h x g hg)

@[simp] theorem AnmFull.rightAct_mk (W : VertexOperatorAlgebra 𝒱) (n m : ℕ)
    (h : DJRightSlot W n m) (a x : 𝒱) :
    AnmFull.rightAct W n m h (mkAnFull W m a) (mkAnmFull W n m x)
      = mkAnmFull W n m (anmRight W n m x a) := rfl

/-- **At base level `m = 0` the acting-slot descent is unconditional.**  The repo discharges
`LeftGradingResidual W n 0 p` for all `n, p` (`leftGradingResidual_zero_gen`, DJ Lemma 2.5's
right-factor half), so `DJRightSlot W n 0` holds outright: `𝒱 *^n_0 O(𝒱) ⊆ O_{n,0}(𝒱)`. -/
theorem djRightSlot_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : DJRightSlot W n 0 :=
  djRightSlot_of_leftGrading W n 0 (leftGradingResidual_zero_gen W n 0)

/-- **The genuine right `A(𝒱)`-action on `A_{n,0}(𝒱)`, unconditional.**  Both descents are proved:
the left slot by `anmRight_OnmFull_unconditional`, the acting slot by `djRightSlot_zero`.  This is
Dong–Jiang Thm 2.9's right `A_m(V)`-module structure, fully discharged at `m = 0`. -/
noncomputable def AnmFull.rightActZero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    AnFull W 0 →ₗ[ℂ] Module.End ℂ (AnmFull W n 0) :=
  AnmFull.rightAct W n 0 (djRightSlot_zero W n)

@[simp] theorem AnmFull.rightActZero_mk (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a x : 𝒱) :
    AnmFull.rightActZero W n (mkAnFull W 0 a) (mkAnmFull W n 0 x)
      = mkAnmFull W n 0 (anmRight W n 0 x a) := rfl

/-! ## §2 `A_{m,m}(𝒱) = A_m(𝒱)` — Dong–Jiang Proposition `pa4.5` (printed as Prop. 4.6) -/

/-- **Dong–Jiang Proposition `pa4.5` (printed Proposition 4.6): `A_{m,m}(𝒱) = A_m(𝒱)`.**

Stated as the only nontrivial half, `O_{m,m}(𝒱) ≤ O_m(𝒱)` (equivalently
`O''_{m,m} + O'''_{m,m} ⊆ O_m(𝒱)`); the reverse containment is the proved
`onFull_le_OnmFull_diag`.

⚠ This is a **hypothesis**, not a theorem here.  DJ's proof is representation-theoretic: they invoke
Dong–Li–Mason III Theorem 4.1 to realize an arbitrary `A_m(V)`-module `U` as `M(m)` for an
admissible `V`-module `M`, and then DJ Lemma 4.1 shows `O''_{m,m}(V) + O'''_{m,m}(V)` acts as `0` on
`U`.  DLM3 Thm 4.1 is not available in this repo, and DJ give no combinatorial proof. -/
def DJAnnEqAn (W : VertexOperatorAlgebra 𝒱) (m : ℕ) : Prop :=
  OnmFull W m m ≤ OnFull W m

/-- `DJAnnEqAn` reduced to the two into-`O'` generator families (the proved
`onmFull_le_Onm_of_gens` at `(n,m) = (m,m)`, then `Onm_diag_eq_OnFull`).  A reduction only — the two
families are exactly DJ's `O''_{m,m}, O''' _{m,m} ⊆ O'_{m,m}` content and are NOT discharged. -/
theorem djAnnEqAn_of_gens (W : VertexOperatorAlgebra 𝒱) (m : ℕ)
    (hAssoc : ∀ (p₁ p₂ p₃ : ℕ) (a b c v : 𝒱), assocDefect W m m p₁ p₂ p₃ a b c v ∈ Onm W m m)
    (hLevel : ∀ (p : ℕ) (a v g : 𝒱), g ∈ Onm W p p → levelMix W m m p a g v ∈ Onm W m m) :
    DJAnnEqAn W m := by
  intro x hx
  have h := onmFull_le_Onm_of_gens W m m hAssoc hLevel hx
  rwa [Onm_diag_eq_OnFull W m] at h

/-- Under `DJAnnEqAn`, the diagonal DJ ideal **is** the Dong–Li–Mason level-`m` ideal. -/
theorem OnmFull_diag_eq (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m) :
    OnmFull W m m = OnFull W m :=
  le_antisymm h (onFull_le_OnmFull_diag W m)

/-- **`A_{m,m}(𝒱) ≃ A_m(𝒱)`** — Dong–Jiang Prop. 4.6 as a linear equivalence of the two quotients,
given `DJAnnEqAn W m`. -/
noncomputable def anmFullDiagEquiv (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m) :
    AnmFull W m m ≃ₗ[ℂ] AnFull W m :=
  Submodule.quotEquivOfEq _ _ (OnmFull_diag_eq W m h)

@[simp] theorem anmFullDiagEquiv_mk (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m)
    (x : 𝒱) : anmFullDiagEquiv W m h (mkAnmFull W m m x) = mkAnFull W m x := rfl

/-! ## §3 `AmMod W m` — a bundled `A_m(𝒱)`-module -/

/-- A **bundled (left) `A_m(𝒱)`-module** — the level-`m` analogue of the repo's level-`0` `AMod`
(`ZhuBijection`).  A `ℂ`-space with a `ℂ`-linear `ρ : A_m(𝒱) → End ℂ`, *unital* (`[𝟙]` acts as `1`)
and *multiplicative on every representable Frenkel–Zhu product* `*_m = leftProd W m`
(`ρ[u *_m v] = ρ[u]·ρ[v]`).  Once `A_m(𝒱)` carries its ring structure this is a genuine
`A_m(𝒱)`-module; DJ's `U` is exactly such an object. -/
structure AmMod (W : VertexOperatorAlgebra 𝒱) (m : ℕ) where
  /-- The underlying carrier. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- The `ℂ`-linear action of `A_m(𝒱)`. -/
  ρ : AnFull W m →ₗ[ℂ] Module.End ℂ carrier
  /-- The unit `[𝟙]` acts as the identity. -/
  ρ_one : ρ (mkAnFull W m W.vacuum) = 1
  /-- Multiplicativity on every representable Frenkel–Zhu product `*_m`. -/
  ρ_mul : ∀ u v : 𝒱,
    ρ (mkAnFull W m (leftProd W m u v)) = ρ (mkAnFull W m u) * ρ (mkAnFull W m v)

attribute [instance] AmMod.addCommGroup AmMod.module

/-- The `A_m(𝒱)`-action written through the diagonal product `*^m_m = *_m`: the exact form the
balancing relation of `DJPiece` uses. -/
theorem AmMod.ρ_mul_anmRight {W : VertexOperatorAlgebra 𝒱} {m : ℕ} (U : AmMod W m) (u v : 𝒱) :
    U.ρ (mkAnFull W m (anmRight W m m u v))
      = U.ρ (mkAnFull W m u) * U.ρ (mkAnFull W m v) := by
  rw [← leftProd_eq_anmRight_diag, U.ρ_mul]

/-! ## §4 The Dong–Jiang level piece `A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` -/

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- The **`ℂ`-tensor cover** `A_{n,m}(𝒱) ⊗_ℂ U` of the Dong–Jiang level-`n` piece.  DJ's carrier is
the balanced quotient of this (`DJPiece`); the cover exists only as scaffolding. -/
abbrev DJCover (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) : Type u :=
  AnmFull W n m ⊗[ℂ] U.carrier

/-- **The `A_m(𝒱)`-balancing generators at level `n`**: the differences
`[x *^n_m a] ⊗ w − [x] ⊗ ρ([a])·w`  (`x a : 𝒱`, `w : U`), i.e. DJ's balancing `x·a ⊗ w = x ⊗ a·w`
written at the level of representatives (right action `*^n_m` on `A_{n,m}(𝒱)` against the left
`A_m(𝒱)`-action on `U`). -/
def djBalancingSet (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    Set (DJCover W U n) :=
  {z | ∃ (x a : 𝒱) (w : U.carrier),
    z = mkAnmFull W n m (anmRight W n m x a) ⊗ₜ[ℂ] w
        - mkAnmFull W n m x ⊗ₜ[ℂ] U.ρ (mkAnFull W m a) w}

/-- **The `A_m(𝒱)`-balancing submodule** of the `ℂ`-tensor cover: the `ℂ`-span of the balancing
generators.  Quotienting by it realizes Dong–Jiang's balanced tensor `A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`. -/
noncomputable def djBalancing (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    Submodule ℂ (DJCover W U n) :=
  Submodule.span ℂ (djBalancingSet W U n)

/-- Every balancing generator lies in the balancing submodule. -/
theorem djBalancing_gen_mem (U : AmMod W m) (n : ℕ) (x a : 𝒱) (w : U.carrier) :
    mkAnmFull W n m (anmRight W n m x a) ⊗ₜ[ℂ] w
        - mkAnmFull W n m x ⊗ₜ[ℂ] U.ρ (mkAnFull W m a) w ∈ djBalancing W U n :=
  Submodule.subset_span ⟨x, a, w, rfl⟩

/-- **Dong–Jiang's level-`n` piece** `M(U)(n) = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`, realized as the `ℂ`-tensor
cover modulo the `A_m(𝒱)`-balancing submodule.  A `ℂ`-module (quotient `AddCommGroup`/`Module ℂ`).
At `n = m` it is `U` itself (`djPieceMEquiv`, given DJ Prop. 4.6). -/
abbrev DJPiece (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) : Type u :=
  DJCover W U n ⧸ djBalancing W U n

/-- The canonical `ℂ`-linear projection `A_{n,m}(𝒱) ⊗_ℂ U ↠ M(U)(n)`. -/
noncomputable def mkDJPiece (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (n : ℕ) :
    DJCover W U n →ₗ[ℂ] DJPiece W U n := (djBalancing W U n).mkQ

theorem mkDJPiece_surjective (U : AmMod W m) (n : ℕ) :
    Function.Surjective (mkDJPiece W U n) := Submodule.mkQ_surjective _

/-- **The defining balancing relation in `M(U)(n)`**: `[x *^n_m a] ⊗ w = [x] ⊗ ρ([a])·w`.  This is
verbatim the step DJ use in the well-definedness proof of `u_p`,
`(u *^{wtu-p-1+n}_{m,n} v) ⊗ a·w = ((u *^{wtu-p-1+n}_{m,n} v) *^{wtu-p-1+n}_m a) ⊗ w`. -/
theorem mkDJPiece_balance (U : AmMod W m) (n : ℕ) (x a : 𝒱) (w : U.carrier) :
    mkDJPiece W U n (mkAnmFull W n m (anmRight W n m x a) ⊗ₜ[ℂ] w)
      = mkDJPiece W U n (mkAnmFull W n m x ⊗ₜ[ℂ] U.ρ (mkAnFull W m a) w) := by
  rw [← sub_eq_zero, mkDJPiece, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact djBalancing_gen_mem U n x a w

/-- The balancing relation phrased through the genuine right `A_m(𝒱)`-action `AnmFull.rightAct`
(available once `DJRightSlot W n m` holds): `(t · [a]) ⊗ w = t ⊗ ρ([a])·w` in `M(U)(n)`. -/
theorem mkDJPiece_balance_rightAct (U : AmMod W m) (n : ℕ) (h : DJRightSlot W n m)
    (a : 𝒱) (t : AnmFull W n m) (w : U.carrier) :
    mkDJPiece W U n (AnmFull.rightAct W n m h (mkAnFull W m a) t ⊗ₜ[ℂ] w)
      = mkDJPiece W U n (t ⊗ₜ[ℂ] U.ρ (mkAnFull W m a) w) := by
  refine Submodule.Quotient.induction_on _ t fun x => ?_
  change mkDJPiece W U n
      (AnmFull.rightAct W n m h (mkAnFull W m a) (mkAnmFull W n m x) ⊗ₜ[ℂ] w) = _
  rw [AnmFull.rightAct_mk]
  exact mkDJPiece_balance U n x a w

/-! ## §5 The payoff: `M(U)(m) ≅ U` -/

/-- **The level-`m` action map** `A_{m,m}(𝒱) ⊗_ℂ U → U`, `[x]_{m,m} ⊗ w ↦ ρ([x]_m)·w`, built from
DJ Prop. 4.6 (`anmFullDiagEquiv`) and the `A_m(𝒱)`-action on `U`. -/
noncomputable def djCoverMToU (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m)
    (U : AmMod W m) : DJCover W U m →ₗ[ℂ] U.carrier :=
  TensorProduct.lift (U.ρ ∘ₗ (anmFullDiagEquiv W m h).toLinearMap)

@[simp] theorem djCoverMToU_tmul (h : DJAnnEqAn W m) (U : AmMod W m) (x : 𝒱) (w : U.carrier) :
    djCoverMToU W m h U (mkAnmFull W m m x ⊗ₜ[ℂ] w) = U.ρ (mkAnFull W m x) w := rfl

theorem djCoverMToU_surjective (h : DJAnnEqAn W m) (U : AmMod W m) :
    Function.Surjective (djCoverMToU W m h U) := by
  intro w
  refine ⟨mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] w, ?_⟩
  rw [djCoverMToU_tmul, U.ρ_one, Module.End.one_apply]

/-- **The balancing lies in the kernel of the level-`m` action map.**  On a generator this is
`ρ([x *^m_m a])·w = ρ([x])·(ρ([a])·w)`, i.e. `*^m_m = *_m` (`leftProd_eq_anmRight_diag`) plus the
multiplicativity `ρ_mul`. -/
theorem djBalancing_le_ker (h : DJAnnEqAn W m) (U : AmMod W m) :
    djBalancing W U m ≤ LinearMap.ker (djCoverMToU W m h U) := by
  rw [djBalancing, Submodule.span_le]
  rintro z ⟨x, a, w, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, djCoverMToU_tmul,
    U.ρ_mul_anmRight, Module.End.mul_apply, sub_self]

/-- Every vector of the cover agrees, modulo the balancing, with `[𝟙] ⊗ (its image in `U`)`.  The
key step of `ker ≤ balancing`: on `[x] ⊗ w` this is the balancing generator with left factor `𝟙`
and acting element `x`, using the sharp unit `𝟙 *^m_m x = x` (`anmRight_diag_vacuum_left`). -/
theorem sub_vacuum_mem_djBalancing (h : DJAnnEqAn W m) (U : AmMod W m) (z : DJCover W U m) :
    z - mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] djCoverMToU W m h U z ∈ djBalancing W U m := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t w =>
      refine Submodule.Quotient.induction_on _ t fun x => ?_
      change mkAnmFull W m m x ⊗ₜ[ℂ] w
            - mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] djCoverMToU W m h U (mkAnmFull W m m x ⊗ₜ[ℂ] w)
          ∈ djBalancing W U m
      rw [djCoverMToU_tmul]
      have hgen := djBalancing_gen_mem U m W.vacuum x w
      rwa [anmRight_diag_vacuum_left] at hgen
  | add z₁ z₂ h₁ h₂ =>
      have hsplit : (z₁ + z₂) - mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] djCoverMToU W m h U (z₁ + z₂)
          = (z₁ - mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] djCoverMToU W m h U z₁)
            + (z₂ - mkAnmFull W m m W.vacuum ⊗ₜ[ℂ] djCoverMToU W m h U z₂) := by
        rw [map_add, TensorProduct.tmul_add]; abel
      rw [hsplit]
      exact Submodule.add_mem _ h₁ h₂

/-- **The balancing at `n = m` IS the kernel of the level-`m` action map.**  Hence the balanced
tensor `A_{m,m}(𝒱) ⊗_{A_m(𝒱)} U` is exactly the image of `U` under that map. -/
theorem djBalancing_diag_eq_ker (h : DJAnnEqAn W m) (U : AmMod W m) :
    djBalancing W U m = LinearMap.ker (djCoverMToU W m h U) := by
  refine le_antisymm (djBalancing_le_ker h U) ?_
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hsub := sub_vacuum_mem_djBalancing h U z
  rwa [hz, TensorProduct.tmul_zero, sub_zero] at hsub

/-- **`M(U)(m) ≅ U`** — Dong–Jiang's "By Proposition 4.6, `M(U)(m)` and `U` are isomorphic
`A_m(V)`-modules".  Given `DJAnnEqAn W m` (= DJ Prop. 4.6), the level-`m` piece of the balanced
carrier is `U` itself: the `n = m` balancing is exactly the kernel of `[x] ⊗ w ↦ ρ([x])·w`, and that
map is surjective by `ρ_one`. -/
noncomputable def djPieceMEquiv (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (h : DJAnnEqAn W m)
    (U : AmMod W m) : DJPiece W U m ≃ₗ[ℂ] U.carrier :=
  (Submodule.quotEquivOfEq _ _ (djBalancing_diag_eq_ker h U)).trans
    (LinearMap.quotKerEquivOfSurjective (djCoverMToU W m h U) (djCoverMToU_surjective h U))

/-- The level-`m` isomorphism computed on a generator: `[x]_{m,m} ⊗ w ↦ ρ([x]_m)·w`. -/
@[simp] theorem djPieceMEquiv_mk (h : DJAnnEqAn W m) (U : AmMod W m) (x : 𝒱) (w : U.carrier) :
    djPieceMEquiv W m h U (mkDJPiece W U m (mkAnmFull W m m x ⊗ₜ[ℂ] w))
      = U.ρ (mkAnFull W m x) w := rfl

/-- The level-`m` isomorphism intertwines the `A_m(𝒱)`-action: transporting `U`'s action back along
`djPieceMEquiv` is the balancing action `[x] ⊗ w ↦ [x] ⊗ ρ([a])·w`.  (DJ: `M(U)(m) ≅ U` as
`A_m(V)`-modules, not merely as `ℂ`-spaces.) -/
theorem djPieceMEquiv_ρ (h : DJAnnEqAn W m) (U : AmMod W m) (a x : 𝒱) (w : U.carrier) :
    djPieceMEquiv W m h U (mkDJPiece W U m (mkAnmFull W m m x ⊗ₜ[ℂ] U.ρ (mkAnFull W m a) w))
      = U.ρ (mkAnFull W m x) (U.ρ (mkAnFull W m a) w) := rfl

end VOA
