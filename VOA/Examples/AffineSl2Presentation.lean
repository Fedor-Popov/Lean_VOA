/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Symbol
import VOA.Examples.AffineSl2Rigidity43
import VOA.Examples.AffineSl2QuasiLisse
import VOA.Examples.AffineSl2Reconstruction
import VOA.Modules.PoissonQuotient

/-!
# The `𝔰𝔩₂` symbol presentation of `A₂(L₋₄⁄₃(𝔰𝔩₂))` — **constructed**

`Examples.AffineSl2QuasiLisse` defines a hypothesis bundle

```
structure Sl2Presentation (W : VertexOperatorAlgebra 𝒱) where
  map : SymSl2 →ₗ[ℂ] A₂ W
  surjective  : Function.Surjective map
  cas_vanishes : ∀ p ∈ casIdeal, map p = 0
  adE_compat / adH_compat / adF_compat
```

and proves that it yields `EtingofFinite W` — the Etingof–Schedler finiteness datum that
Arakawa–Kawasetsu feed into their modular linear differential equation — **without** any appeal
to `C₂`-cofiniteness.  Without an inhabitant of the bundle, every downstream statement is
universally quantified over a structure nothing constructs (`Modularity.AKSl2Payoff` records
this caveat: the statement there is an implication, not an example).

**This file constructs it**, at the flagship algebra `W = L₋₄⁄₃(𝔰𝔩₂) = simpleSl2QL`.

## What made it possible, and why it does not need PBW

The one thing the previous accounts assumed was needed — a PBW coordinate functional pinning
`A₂(V^k(𝔰𝔩₂))` down to `Sym(𝔰𝔩₂)` — is needed only for the **converse** inclusion `IsExact`, not
for the presentation itself.  All six fields go through with material that was already proved
and is already `pbw`-free:

* `surjective` ← `AffineSl2Reconstruction.wordStateA_span` (the word states span `V^k`), plus
  `Sl2Symbol.J_mem_O₂` (modes `≤ -2` die in `A₂`) and `AffineSl2VOAInstance.smul_currentState_eq_J`
  (a `₍₋₁₎`-mode of a current state is a Poisson product).  No grading argument, no PBW.
* `cas_vanishes` ← `Sl2Symbol.mk₂_sl2Singular_casimir` (`[s] = 9·[e]·Cas` in `A₂(V^{-4/3})`)
  composed with `AffineSl2Rigidity43.mkQ_sl2Singular_eq_zero` (`s` dies in the simple
  quotient).  The latter is a genuine theorem — Li's invariant-form radical, with
  `Wak.vacuumA_ne_zero_free` and `Wak.sl2Singular_ne_zero` supplying non-degeneracy — and it is
  `pbw`-free.  This is the input the earlier status notes did not know was available.
* `adE_compat` / `adH_compat` / `adF_compat` ← `Modules.PoissonDescent.A₂_leibniz` and the six
  generator brackets `Sl2Symbol.A₂bracket_{e_f, h_e, h_f, e_h, f_h, f_e}`, by
  `MvPolynomial.induction_on`.

The bridge from the **universal** VOA `V^{-4/3}(𝔰𝔩₂)`, where all the symbol computations live, to
the **simple quotient** `L₋₄⁄₃(𝔰𝔩₂)`, where the presentation is wanted, is the new generic
`Modules.PoissonQuotient.A₂quot : A₂(W) ↠ A₂(W ⧸ I)`.

## Main results

* `symbolAlg k hk : SymSl2 →ₐ[ℂ] A₂(V^k(𝔰𝔩₂))` and `symbolAlg_surjective` — for **every**
  non-critical level, `A₂(V^k(𝔰𝔩₂))` is generated as a `ℂ`-algebra by the three current classes.
* `symbolAlgL : SymSl2 →ₐ[ℂ] A₂(L₋₄⁄₃(𝔰𝔩₂))`, `symbolAlgL_surjective`.
* `eL_mul_casL : [e]·Cas = 0` in `A₂(L₋₄⁄₃(𝔰𝔩₂))` — the symbol of the singular vector dies.
* `cas_vanishes_L : ∀ p ∈ casIdeal, symbolAlgL p = 0` — the whole Poisson ideal `Cas·𝔪` dies.
* `sl2PresentationSimpleSl2QL : Sl2Presentation simpleSl2QL` — **the structure, inhabited.**
* `etingofFinite_simpleSl2QL' : EtingofFinite simpleSl2QL` — **unconditional**, and
  `pbw`-free.

## ⚠ What is NOT delivered — read this before quoting anything above

* **`Sl2Presentation.IsExact` is NOT proved.**  `IsExact` says `symbolAlgL p = 0 → p ∈ casIdeal`:
  the symbol ideal of the maximal graded ideal is no larger than `Cas·𝔪`.  It is carried as the
  named hypothesis `Sl2ExactSymbol` (§6).  It is **stronger** than Arakawa's associated-variety
  theorem `X_{L_k(𝔰𝔩₂)} = 𝒩`, which determines only the radical of the kernel.
  `¬ C2Cofinite (L₋₄⁄₃(𝔰𝔩₂))` is nevertheless proved unconditionally, by a different route, in
  `Examples.AffineSl2NonLisse` (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`).
* **Quasi-lisseness is not formalized anywhere in this repository** (no associated varieties, no
  symplectic leaves); `EtingofFinite` remains the axiomatized *conclusion* of Etingof–Schedler.
* **`A₂(V^k(𝔤)) ≅ Sym(𝔤)` is not proved** — indeed it is not even statable for general `𝔤`, since
  the repository builds an affine VOA only for `𝔰𝔩₂` (`Examples.Affine` is an `𝔰𝔩₂`-only file and
  says so).  What `symbolAlg_surjective` gives is the **surjection** `Sym(𝔰𝔩₂) ↠ A₂(V^k(𝔰𝔩₂))`;
  injectivity follows from PBW for `V^k(𝔰𝔩₂)` (proved,
  `AffineSl2WakimotoLiLeading.affineSl2PBWBasis`) via
  `AffineSl2PBWWakimotoReduction.symbolAlg_injective_of_wakimotoOrderedCreationState_linearIndependent`.

## Status
`sorry`-free and axiom-clean: every declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.  In particular **nothing here uses the theorem
`VOA.pbw`** — including `vacuum_simpleSl2QL_ne_zero'`, which is
re-routed through `AffineSl2Rigidity43.L43_vacuum_ne_zero` (Wakimoto, `pbw`-free) rather than
through `QuasiLisseSl2.vacuum_simpleSl2QL_ne_zero` (which consumes `pbw`).

## References
* T. Arakawa, K. Kawasetsu, *Quasi-lisse vertex algebras and modular linear differential
  equations*, arXiv:1610.05865.
* T. Arakawa, *Associated varieties of modules over Kac–Moody algebras and C₂-cofiniteness of
  W-algebras*, IMRN 2015 (the `IsExact` half).
* D. Adamović, A. Milas, *Vertex operator algebras associated to modular invariant
  representations for A₁⁽¹⁾*, Math. Res. Lett. **2** (1995).
* H. Li, *Symmetric invariant bilinear forms on vertex operator algebras* (via
  `Core.InvariantFormRadical`, used by `AffineSl2Rigidity43`).
-/

namespace VOA.Sl2Pres

open VOA
open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.QuasiLisseSl2
open VOA.Sl2Symbol
open VertexOperatorAlgebra
open MvPolynomial

universe u

noncomputable section

/-! ## §0  A generic transfer lemma for the three bracket-compatibilities

`adE`, `adH`, `adF` are all derivations of `Sym(𝔰𝔩₂)` killing constants.  For any `ℂ`-algebra map
`φ : Sym(𝔰𝔩₂) → A₂(W)` and any class `x ∈ A₂(W)`, checking `φ ∘ D = ⁅x, ·⁆ ∘ φ` on the three
variables suffices: the constants are handled by `A₂bracket_one`, sums by linearity, and the
multiplicative step is exactly the Poisson–Leibniz rule `Modules.PoissonDescent.A₂_leibniz`
matched against the Leibniz rule of `D`. -/

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- A `ℂ`-algebra map out of `Sym(𝔰𝔩₂)` intertwines a constant-killing derivation `D` with the
Poisson bracket against `x` as soon as it does so on the three variables. -/
theorem adCompat_of_generators (W : VertexOperatorAlgebra 𝒲) (φ : SymSl2 →ₐ[ℂ] A₂ W)
    (D : SymSl2 →ₗ[ℂ] SymSl2) (hlei : ∀ p q : SymSl2, D (p * q) = D p * q + p * D q)
    (hC : ∀ c : ℂ, D (MvPolynomial.C c) = 0) (x : A₂ W)
    (hgen : ∀ i : Fin 3, φ (D (MvPolynomial.X i)) = A₂bracket W x (φ (MvPolynomial.X i)))
    (p : SymSl2) : φ (D p) = A₂bracket W x (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      have h1 : φ (MvPolynomial.C c) = c • (1 : A₂ W) := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, A₂_algebraMap_apply]
      rw [hC, map_zero, h1, LinearMap.map_smul, A₂bracket_one, smul_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
      have hleib : A₂bracket W x (φ p * φ (MvPolynomial.X i))
          = A₂bracket W x (φ p) * φ (MvPolynomial.X i)
            + φ p * A₂bracket W x (φ (MvPolynomial.X i)) :=
        A₂_leibniz W x (φ p) (φ (MvPolynomial.X i))
      rw [hlei, map_add, map_mul, map_mul, hp, hgen i, map_mul, hleib]

/-- `adOf a i b j` kills the constants of `Sym(𝔰𝔩₂)`. -/
theorem adOf_C (a : SymSl2) (i : Fin 3) (b : SymSl2) (j : Fin 3) (c : ℂ) :
    adOf a i b j (MvPolynomial.C c) = 0 := by
  simp [adOf_apply]

/-! ## §1  The values of `adE`, `adH`, `adF` on the three variables, in `ℂ`-scalar form

`Examples.AffineSl2QuasiLisse` defines `adE = adOf (-2e) 1 h 2`, `adH = adOf (2e) 0 (-2f) 2`,
`adF = adOf (-h) 0 (2f) 1`.  The nine values below are exactly the Kirillov–Kostant brackets
`{e,·}`, `{h,·}`, `{f,·}` on the generators, written with **`ℂ`-scalars** so that they line up
with the six generator brackets of `Examples.AffineSl2Symbol`, which are stated with `•`. -/

theorem adE_e : adE eSym = 0 := by simp [adE, eSym, hSym, pderiv_X]

theorem adE_h : adE hSym = (-2 : ℂ) • eSym := by
  rw [MvPolynomial.smul_eq_C_mul]
  simp [adE, eSym, hSym, pderiv_X, C_two]

theorem adE_f : adE fSym = hSym := by simp [adE, eSym, hSym, fSym, pderiv_X]

theorem adH_e : adH eSym = (2 : ℂ) • eSym := by
  rw [MvPolynomial.smul_eq_C_mul]
  simp [adH, eSym, fSym, pderiv_X, C_two]

theorem adH_h : adH hSym = 0 := by simp [adH, eSym, fSym, hSym, pderiv_X]

theorem adH_f : adH fSym = (-2 : ℂ) • fSym := by
  rw [MvPolynomial.smul_eq_C_mul]
  simp [adH, eSym, fSym, pderiv_X, C_two]

theorem adF_e : adF eSym = (-1 : ℂ) • hSym := by
  rw [MvPolynomial.smul_eq_C_mul]
  simp [adF, eSym, hSym, fSym, pderiv_X]

theorem adF_h : adF hSym = (2 : ℂ) • fSym := by
  rw [MvPolynomial.smul_eq_C_mul]
  simp [adF, hSym, fSym, pderiv_X, C_two]

theorem adF_f : adF fSym = 0 := by simp [adF, hSym, fSym, pderiv_X]

/-! ## §2  The symbol algebra map of the **universal** affine VOA `V^k(𝔰𝔩₂)`

`Examples.AffineSl2Symbol` computes with the three classes `eCl`, `fCl`, `hCl` of the current
states `Jᵃ₋₁|0⟩` in `A₂(V^k(𝔰𝔩₂))`.  With `Algebra ℂ (A₂ W)` available
(`Modules.PoissonQuotient.A₂Algebra`) those three classes assemble into an **algebra** map out of
`Sym(𝔰𝔩₂) = ℂ[X₀,X₁,X₂]`.

⚠ **Index warning.**  `SymSl2` uses `eSym = X 0`, `hSym = X 1`, `fSym = X 2`
(`AffineSl2QuasiLisse`), whereas the affine colours are `colE = 0`, `colF = 1`, `colH = 2`
(`AffineSl2`).  The two `Fin 3`s are **different**; the vector below is `![e, h, f]`, not
`![e, f, h]`. -/

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- The **symbol map** `Sym(𝔰𝔩₂) → A₂(V^k(𝔰𝔩₂))`, `X₀ ↦ [e], X₁ ↦ [h], X₂ ↦ [f]`, as a
`ℂ`-algebra homomorphism. -/
def symbolAlg : SymSl2 →ₐ[ℂ] A₂ (affineSl2VOA_closed k hk) :=
  MvPolynomial.aeval ![eCl k hk, hCl k hk, fCl k hk]

@[simp] theorem symbolAlg_eSym : symbolAlg k hk eSym = eCl k hk := by simp [symbolAlg, eSym]

@[simp] theorem symbolAlg_hSym : symbolAlg k hk hSym = hCl k hk := by simp [symbolAlg, hSym]

@[simp] theorem symbolAlg_fSym : symbolAlg k hk fSym = fCl k hk := by simp [symbolAlg, fSym]

/-- The image of the Casimir polynomial is the Casimir class of `Examples.AffineSl2Symbol`. -/
theorem symbolAlg_casSym : symbolAlg k hk casSym = casimirCl k hk := by
  rw [casSym, map_add, map_pow, map_mul, map_mul, symbolAlg_eSym, symbolAlg_hSym, symbolAlg_fSym,
    map_ofNat, casimirCl, pow_two, mul_assoc, A₂_four_mul, add_comm]

/-- Each current class is in the image of the symbol map. -/
theorem curCl_mem_range (a : Fin 3) :
    mk₂ (affineSl2VOA_closed k hk) (currentState k a) ∈ (symbolAlg k hk).range := by
  fin_cases a
  · exact ⟨eSym, symbolAlg_eSym k hk⟩
  · exact ⟨fSym, symbolAlg_fSym k hk⟩
  · exact ⟨hSym, symbolAlg_hSym k hk⟩

/-- A `₍₋₁₎`-mode of a current is the Poisson product with the current class:
`[Jᵃ₋₁ v] = [Jᵃ₋₁|0⟩] · [v]`. -/
theorem mk₂_J_neg_one (a : Fin 3) (v : WakModule k) :
    mk₂ (affineSl2VOA_closed k hk) (J k a (-1) v)
      = mk₂ (affineSl2VOA_closed k hk) (currentState k a)
        * mk₂ (affineSl2VOA_closed k hk) v := by
  rw [A₂_mul_mk, poissonMul_def, smul_currentState_eq_J]

/-- Every word state has its class in the image of the symbol map: depths `≥ 1` carry a mode
`≤ -2` and die (`J_mem_O₂`), depth `0` is a Poisson product with a current class. -/
theorem mk₂_wordStateA_mem_range (l : List (Fin 3 × ℕ)) :
    mk₂ (affineSl2VOA_closed k hk) (wordStateA k l) ∈ (symbolAlg k hk).range := by
  induction l with
  | nil =>
      rw [wordStateA_nil, show vacuumA k = (affineSl2VOA_closed k hk).vacuum from rfl,
        ← A₂_one_eq]
      exact one_mem _
  | cons ai rest ih =>
      obtain ⟨a, n⟩ := ai
      rw [wordStateA_cons]
      rcases n with _ | m
      · rw [show (-((0 : ℕ) : ℤ) - 1) = -1 by norm_num, mk₂_J_neg_one]
        exact mul_mem (curCl_mem_range k hk a) ih
      · rw [(mk₂_eq_zero_iff _).mpr
          (J_mem_O₂ k hk a (show (-((m + 1 : ℕ) : ℤ) - 1) ≤ -2 by push_cast; omega) _)]
        exact zero_mem _

/-- **`A₂(V^k(𝔰𝔩₂))` is generated as a `ℂ`-algebra by the three current classes**, at every
non-critical level.  This is the honest half of "`R_{V^k(𝔤)} = ℂ[𝔤*]`": the surjection.
Injectivity is a separate matter, not proved in this file (see the module docstring). -/
theorem symbolAlg_surjective : Function.Surjective (symbolAlg k hk) := by
  intro y
  obtain ⟨v, rfl⟩ := mk₂_surjective (affineSl2VOA_closed k hk) y
  have hv : v ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span k]; trivial
  have hmem : mk₂ (affineSl2VOA_closed k hk) v ∈ (symbolAlg k hk).range := by
    induction hv using Submodule.span_induction with
    | mem z hz => obtain ⟨l, rfl⟩ := hz; exact mk₂_wordStateA_mem_range k hk l
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  exact hmem

/-! ## §3  Transport to the simple quotient `L₋₄⁄₃(𝔰𝔩₂)`

`QuasiLisseSl2.affineSl2QL` and `AffineSl2VOAInstance.voaSl2Adm` are the *same* vertex operator
algebra — they differ only in which proof of `-4/3 + 2 ≠ 0` is supplied, and proof irrelevance is
definitional in Lean 4.  Likewise `QuasiLisseSl2.simpleSl2QL` and `AffineSl2Rigidity43.L43`.  So
the symbol computations of `Examples.AffineSl2Symbol` and the singular-vector vanishing of
`Examples.AffineSl2Rigidity43` are directly available here. -/

/-- `V^{-4/3}(𝔰𝔩₂)` and `voaSl2Adm` are the same object. -/
theorem affineSl2QL_eq_voaSl2Adm : affineSl2QL = voaSl2Adm := rfl

/-- The class `[e]` of `A₂(V^{-4/3}(𝔰𝔩₂))`. -/
abbrev eV : A₂ affineSl2QL := eCl (-4 / 3 : ℂ) hkQL
/-- The class `[h]` of `A₂(V^{-4/3}(𝔰𝔩₂))`. -/
abbrev hV : A₂ affineSl2QL := hCl (-4 / 3 : ℂ) hkQL
/-- The class `[f]` of `A₂(V^{-4/3}(𝔰𝔩₂))`. -/
abbrev fV : A₂ affineSl2QL := fCl (-4 / 3 : ℂ) hkQL
/-- The Casimir class `4[e][f] + [h]²` of `A₂(V^{-4/3}(𝔰𝔩₂))`. -/
abbrev casV : A₂ affineSl2QL := casimirCl (-4 / 3 : ℂ) hkQL

/-- The surjection `A₂(V^{-4/3}(𝔰𝔩₂)) ↠ A₂(L₋₄⁄₃(𝔰𝔩₂))` of `Modules.PoissonQuotient`. -/
def A₂QL : A₂ affineSl2QL →ₐ[ℂ] A₂ simpleSl2QL :=
  QuotVOA.A₂quot (QuotVOA.maxGradedIdeal_isIdeal affineSl2QL)
    (QuotVOA.maxGradedIdeal_isGradedIdeal affineSl2QL)

theorem A₂QL_surjective : Function.Surjective A₂QL :=
  QuotVOA.A₂quot_surjective _ _

theorem A₂QL_mk₂ (u : WakModule (-4 / 3 : ℂ)) :
    A₂QL (mk₂ affineSl2QL u)
      = mk₂ simpleSl2QL ((QuotVOA.maxGradedIdeal affineSl2QL).mkQ u) := rfl

theorem A₂QL_bracket (p q : A₂ affineSl2QL) :
    A₂QL (A₂bracket affineSl2QL p q) = A₂bracket simpleSl2QL (A₂QL p) (A₂QL q) :=
  QuotVOA.A₂quot_bracket _ _ p q

/-- The class `[e]` of `A₂(L₋₄⁄₃(𝔰𝔩₂))`. -/
def eL : A₂ simpleSl2QL := A₂QL eV
/-- The class `[h]` of `A₂(L₋₄⁄₃(𝔰𝔩₂))`. -/
def hL : A₂ simpleSl2QL := A₂QL hV
/-- The class `[f]` of `A₂(L₋₄⁄₃(𝔰𝔩₂))`. -/
def fL : A₂ simpleSl2QL := A₂QL fV
/-- The Casimir class `4[e][f] + [h]²` of `A₂(L₋₄⁄₃(𝔰𝔩₂))`. -/
def casL : A₂ simpleSl2QL := (4 : ℂ) • (eL * fL) + hL * hL

theorem A₂QL_casV : A₂QL casV = casL := by
  have h : (casV : A₂ affineSl2QL) = (4 : ℂ) • (eV * fV) + hV * hV := rfl
  rw [h, map_add, map_smul, map_mul, map_mul]
  rfl

/-! ### The nine generator brackets on `A₂(L₋₄⁄₃(𝔰𝔩₂))` -/

theorem bracket_eL_eL : A₂bracket simpleSl2QL eL eL = 0 := A₂bracket_self _ _

theorem bracket_hL_hL : A₂bracket simpleSl2QL hL hL = 0 := A₂bracket_self _ _

theorem bracket_fL_fL : A₂bracket simpleSl2QL fL fL = 0 := A₂bracket_self _ _

theorem bracket_eL_fL : A₂bracket simpleSl2QL eL fL = hL := by
  have h : A₂bracket affineSl2QL eV fV = hV := Sl2Symbol.A₂bracket_e_f _ _
  rw [eL, fL, hL, ← A₂QL_bracket, h]

theorem bracket_eL_hL : A₂bracket simpleSl2QL eL hL = (-2 : ℂ) • eL := by
  have h : A₂bracket affineSl2QL eV hV = (-2 : ℂ) • eV := Sl2Symbol.A₂bracket_e_h _ _
  rw [eL, hL, ← A₂QL_bracket, h, map_smul]

theorem bracket_hL_eL : A₂bracket simpleSl2QL hL eL = (2 : ℂ) • eL := by
  have h : A₂bracket affineSl2QL hV eV = (2 : ℂ) • eV := Sl2Symbol.A₂bracket_h_e _ _
  rw [eL, hL, ← A₂QL_bracket, h, map_smul]

theorem bracket_hL_fL : A₂bracket simpleSl2QL hL fL = (-2 : ℂ) • fL := by
  have h : A₂bracket affineSl2QL hV fV = (-2 : ℂ) • fV := Sl2Symbol.A₂bracket_h_f _ _
  rw [hL, fL, ← A₂QL_bracket, h, map_smul]

theorem bracket_fL_eL : A₂bracket simpleSl2QL fL eL = (-1 : ℂ) • hL := by
  have h : A₂bracket affineSl2QL fV eV = -hV := Sl2Symbol.A₂bracket_f_e _ _
  rw [eL, fL, hL, ← A₂QL_bracket, h, map_neg, neg_one_smul]

theorem bracket_fL_hL : A₂bracket simpleSl2QL fL hL = (2 : ℂ) • fL := by
  have h : A₂bracket affineSl2QL fV hV = (2 : ℂ) • fV := Sl2Symbol.A₂bracket_f_h _ _
  rw [hL, fL, ← A₂QL_bracket, h, map_smul]

/-! ## §4  The symbol map of `L₋₄⁄₃(𝔰𝔩₂)`, and the death of the Casimir ideal -/

/-- The **symbol map** `Sym(𝔰𝔩₂) → A₂(L₋₄⁄₃(𝔰𝔩₂))`. -/
def symbolAlgL : SymSl2 →ₐ[ℂ] A₂ simpleSl2QL := MvPolynomial.aeval ![eL, hL, fL]

@[simp] theorem symbolAlgL_eSym : symbolAlgL eSym = eL := by simp [symbolAlgL, eSym]

@[simp] theorem symbolAlgL_hSym : symbolAlgL hSym = hL := by simp [symbolAlgL, hSym]

@[simp] theorem symbolAlgL_fSym : symbolAlgL fSym = fL := by simp [symbolAlgL, fSym]

/-- The symbol map of the simple quotient is the symbol map of the universal VOA followed by the
quotient surjection. -/
theorem symbolAlgL_eq_comp : symbolAlgL = A₂QL.comp (symbolAlg (-4 / 3 : ℂ) hkQL) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i
  · show symbolAlgL eSym = A₂QL (symbolAlg (-4 / 3 : ℂ) hkQL eSym)
    rw [symbolAlgL_eSym, symbolAlg_eSym]; rfl
  · show symbolAlgL hSym = A₂QL (symbolAlg (-4 / 3 : ℂ) hkQL hSym)
    rw [symbolAlgL_hSym, symbolAlg_hSym]; rfl
  · show symbolAlgL fSym = A₂QL (symbolAlg (-4 / 3 : ℂ) hkQL fSym)
    rw [symbolAlgL_fSym, symbolAlg_fSym]; rfl

/-- **The presentation is surjective** — `A₂(L₋₄⁄₃(𝔰𝔩₂))` is generated by `[e], [h], [f]`. -/
theorem symbolAlgL_surjective : Function.Surjective symbolAlgL := by
  rw [symbolAlgL_eq_comp]
  exact A₂QL_surjective.comp (symbolAlg_surjective (-4 / 3 : ℂ) hkQL)

theorem symbolAlgL_casSym : symbolAlgL casSym = casL := by
  rw [symbolAlgL_eq_comp]
  show A₂QL (symbolAlg (-4 / 3 : ℂ) hkQL casSym) = casL
  rw [symbolAlg_casSym]
  exact A₂QL_casV

/-- The symbol of the weight-3 singular vector in `A₂(V^{-4/3}(𝔰𝔩₂))`
(`Sl2Symbol.mk₂_sl2Singular_casimir`, restated in the `QuasiLisseSl2` naming). -/
theorem mk₂_sl2Singular_QL :
    mk₂ affineSl2QL Sl2Sing.sl2Singular = (9 : ℂ) • (eV * casV) :=
  Sl2Symbol.mk₂_sl2Singular_casimir

/-- **The singular vector dies in `L₋₄⁄₃(𝔰𝔩₂)`** (`AffineSl2Rigidity43.mkQ_sl2Singular_eq_zero`,
a genuine theorem via Li's invariant-form radical, and `pbw`-free). -/
theorem mkQ_sl2Singular_QL :
    (QuotVOA.maxGradedIdeal affineSl2QL).mkQ Sl2Sing.sl2Singular = 0 :=
  LQ43.mkQ_sl2Singular_eq_zero

/-- **`[e]·Cas = 0` in `A₂(L₋₄⁄₃(𝔰𝔩₂))`** — the symbol `9·e·Cas` of the weight-3 singular
vector vanishes in the `C₂`-algebra of the simple quotient. -/
theorem eL_mul_casL : eL * casL = 0 := by
  have h0 : A₂QL (mk₂ affineSl2QL Sl2Sing.sl2Singular) = 0 := by
    rw [A₂QL_mk₂, mkQ_sl2Singular_QL, map_zero]
  rw [mk₂_sl2Singular_QL] at h0
  have h1 : A₂QL ((9 : ℂ) • (eV * casV)) = (9 : ℂ) • (eL * casL) := by
    rw [map_smul, map_mul, A₂QL_casV]
    rfl
  rw [h1] at h0
  have h9 : (9 : ℂ) ≠ 0 := by norm_num
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd h h9
  · exact h

/-! ### The three bracket compatibilities -/

theorem adE_compat_L (p : SymSl2) : symbolAlgL (adE p) = A₂bracket simpleSl2QL eL (symbolAlgL p) :=
  adCompat_of_generators simpleSl2QL symbolAlgL adE adE_mul (fun c => by rw [adE]; exact adOf_C _ _ _ _ c)
    eL (by
      intro i
      fin_cases i
      · show symbolAlgL (adE eSym) = A₂bracket simpleSl2QL eL (symbolAlgL eSym)
        rw [adE_e, map_zero, symbolAlgL_eSym, bracket_eL_eL]
      · show symbolAlgL (adE hSym) = A₂bracket simpleSl2QL eL (symbolAlgL hSym)
        rw [adE_h, map_smul, symbolAlgL_eSym, symbolAlgL_hSym, bracket_eL_hL]
      · show symbolAlgL (adE fSym) = A₂bracket simpleSl2QL eL (symbolAlgL fSym)
        rw [adE_f, symbolAlgL_hSym, symbolAlgL_fSym, bracket_eL_fL]) p

theorem adH_compat_L (p : SymSl2) : symbolAlgL (adH p) = A₂bracket simpleSl2QL hL (symbolAlgL p) :=
  adCompat_of_generators simpleSl2QL symbolAlgL adH adH_mul (fun c => by rw [adH]; exact adOf_C _ _ _ _ c)
    hL (by
      intro i
      fin_cases i
      · show symbolAlgL (adH eSym) = A₂bracket simpleSl2QL hL (symbolAlgL eSym)
        rw [adH_e, map_smul, symbolAlgL_eSym, bracket_hL_eL]
      · show symbolAlgL (adH hSym) = A₂bracket simpleSl2QL hL (symbolAlgL hSym)
        rw [adH_h, map_zero, symbolAlgL_hSym, bracket_hL_hL]
      · show symbolAlgL (adH fSym) = A₂bracket simpleSl2QL hL (symbolAlgL fSym)
        rw [adH_f, map_smul, symbolAlgL_fSym, bracket_hL_fL]) p

theorem adF_compat_L (p : SymSl2) : symbolAlgL (adF p) = A₂bracket simpleSl2QL fL (symbolAlgL p) :=
  adCompat_of_generators simpleSl2QL symbolAlgL adF adF_mul (fun c => by rw [adF]; exact adOf_C _ _ _ _ c)
    fL (by
      intro i
      fin_cases i
      · show symbolAlgL (adF eSym) = A₂bracket simpleSl2QL fL (symbolAlgL eSym)
        rw [adF_e, map_smul, symbolAlgL_eSym, symbolAlgL_hSym, bracket_fL_eL]
      · show symbolAlgL (adF hSym) = A₂bracket simpleSl2QL fL (symbolAlgL hSym)
        rw [adF_h, map_smul, symbolAlgL_hSym, symbolAlgL_fSym, bracket_fL_hL]
      · show symbolAlgL (adF fSym) = A₂bracket simpleSl2QL fL (symbolAlgL fSym)
        rw [adF_f, map_zero, symbolAlgL_fSym, bracket_fL_fL]) p

/-! ### The Casimir ideal dies

`casIdeal = Ideal.span {Cas·e, Cas·h, Cas·f} = Cas·𝔪` has three generators, all of **degree 3** —
matching the conformal weight of the singular vector, whose symbol is `9e·Cas`.  The degree-2
Casimir itself is *not* in `casIdeal` and is *not* asked to vanish (and indeed
`R_{L_k(𝔰𝔩₂)}` at admissible level is genuinely non-reduced).

Only the first generator needs the singular vector; the other two follow from it by applying
`{f, ·}` twice, using `adF_cas : {f, Cas} = 0`. -/

theorem symbolAlgL_hSym_mul_casSym : symbolAlgL (hSym * casSym) = 0 := by
  have hcompat := adF_compat_L (eSym * casSym)
  have hval : adF (eSym * casSym) = (-1 : ℂ) • (hSym * casSym) := by
    rw [adF_mul, adF_e, adF_cas, mul_zero, add_zero, smul_mul_assoc]
  have hzero : symbolAlgL (eSym * casSym) = 0 := by
    rw [map_mul, symbolAlgL_eSym, symbolAlgL_casSym, eL_mul_casL]
  rw [hval, hzero, map_smul, map_zero] at hcompat
  have : (-1 : ℂ) • symbolAlgL (hSym * casSym) = 0 := hcompat
  simpa using this

theorem symbolAlgL_fSym_mul_casSym : symbolAlgL (fSym * casSym) = 0 := by
  have hcompat := adF_compat_L (hSym * casSym)
  have hval : adF (hSym * casSym) = (2 : ℂ) • (fSym * casSym) := by
    rw [adF_mul, adF_h, adF_cas, mul_zero, add_zero, smul_mul_assoc]
  rw [hval, symbolAlgL_hSym_mul_casSym, map_smul, map_zero] at hcompat
  have : (2 : ℂ) • symbolAlgL (fSym * casSym) = 0 := hcompat
  simpa using this

/-- **The whole Poisson ideal `Cas·𝔪` dies in `A₂(L₋₄⁄₃(𝔰𝔩₂))`.** -/
theorem cas_vanishes_L : ∀ p ∈ casIdeal, symbolAlgL p = 0 := by
  have hle : casIdeal ≤ RingHom.ker (symbolAlgL : SymSl2 →+* A₂ simpleSl2QL) := by
    rw [casIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    fin_cases i
    · show symbolAlgL (casSym * eSym) = 0
      rw [map_mul, symbolAlgL_eSym, symbolAlgL_casSym, mul_comm, eL_mul_casL]
    · show symbolAlgL (casSym * hSym) = 0
      rw [mul_comm]; exact symbolAlgL_hSym_mul_casSym
    · show symbolAlgL (casSym * fSym) = 0
      rw [mul_comm]; exact symbolAlgL_fSym_mul_casSym
  intro p hp
  exact hle hp

/-! ## §5  The presentation, and the unconditional Etingof–Schedler finiteness -/

/-- **`Sl2Presentation simpleSl2QL` — the structure, INHABITED.**

The bundle `Examples.AffineSl2QuasiLisse.Sl2Presentation` is constructed here for
`L₋₄⁄₃(𝔰𝔩₂)`.  Everything it consumes is `pbw`-free.

⚠ This does **not** include `IsExact`; see §6 and the module docstring. -/
def sl2PresentationSimpleSl2QL : Sl2Presentation simpleSl2QL where
  map := symbolAlgL.toLinearMap
  surjective := symbolAlgL_surjective
  cas_vanishes := cas_vanishes_L
  adE_compat := by
    intro p
    show symbolAlgL (adE p) = A₂bracket simpleSl2QL (symbolAlgL eSym) (symbolAlgL p)
    rw [symbolAlgL_eSym]; exact adE_compat_L p
  adH_compat := by
    intro p
    show symbolAlgL (adH p) = A₂bracket simpleSl2QL (symbolAlgL hSym) (symbolAlgL p)
    rw [symbolAlgL_hSym]; exact adH_compat_L p
  adF_compat := by
    intro p
    show symbolAlgL (adF p) = A₂bracket simpleSl2QL (symbolAlgL fSym) (symbolAlgL p)
    rw [symbolAlgL_fSym]; exact adF_compat_L p

/-- **`EtingofFinite (L₋₄⁄₃(𝔰𝔩₂))`, unconditionally.**

The Etingof–Schedler finiteness datum `dim (A₂(W) ⧸ {A₂,A₂}) < ∞` holds for the simple affine
vertex operator algebra `L₋₄⁄₃(𝔰𝔩₂)`, with **no** hypotheses and **no** `VOA.pbw`.

⚠ The route is `Sl2Presentation.etingofFinite` — spanning `A₂` by Poisson brackets together with
the three classes `[1]`, `[h²]`, `[ef]` — **not** `EtingofFinite_of_C2Cofinite`.  Nothing here
claims `C₂`-cofiniteness, and nothing here refutes it either: see §6. -/
theorem etingofFinite_simpleSl2QL' : EtingofFinite simpleSl2QL :=
  sl2PresentationSimpleSl2QL.etingofFinite

/-- The finite-dimensional **Poisson trace space** of `L₋₄⁄₃(𝔰𝔩₂)`, unconditionally — the
linear-algebra input Arakawa–Kawasetsu feed into the modular linear differential equation. -/
theorem finiteDimensional_poissonTraces_simpleSl2QL' :
    FiniteDimensional ℂ (poissonTraces simpleSl2QL) :=
  finiteDimensional_poissonTraces simpleSl2QL etingofFinite_simpleSl2QL'

/-- The vacuum of `L₋₄⁄₃(𝔰𝔩₂)` is nonzero, **`pbw`-free**: routed through
`AffineSl2Rigidity43.L43_vacuum_ne_zero` (Wakimoto `vacuumA_ne_zero_free`) instead of
`QuasiLisseSl2.vacuum_simpleSl2QL_ne_zero` (which uses the theorem `VOA.pbw`). -/
theorem vacuum_simpleSl2QL_ne_zero' : (simpleSl2QL).vacuum ≠ 0 :=
  LQ43.L43_vacuum_ne_zero

/-- `A₂(L₋₄⁄₃(𝔰𝔩₂)) ≠ 0`, **`pbw`-free** (compare `QuasiLisseSl2.A₂_simpleSl2QL_nontrivial`,
which uses `pbw`).  So the presentation above is not the degenerate zero map. -/
theorem A₂_simpleSl2QL_nontrivial' : Nontrivial (A₂ simpleSl2QL) :=
  A₂_nontrivial simpleSl2QL vacuum_simpleSl2QL_ne_zero'

/-! ## §6  ⚠ `IsExact` — a SEPARATE named hypothesis, NOT proved here

`Sl2Presentation.IsExact S : ∀ p, S.map p = 0 → p ∈ casIdeal` is the converse inclusion: the
kernel of the symbol map is no *larger* than `Cas·𝔪`.  It is what upgrades the presentation to
`¬ C2Cofinite` (`Sl2Presentation.not_C2Cofinite`).  (`¬ C2Cofinite` is also proved
unconditionally, without `IsExact`: `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`.)

⚠ **It is not a PBW statement and it is not proved here.**  Mathematically it is a Hilbert-series
squeeze whose *lower* bound is Arakawa's theorem that the associated variety of `L_k(𝔰𝔩₂)` at
admissible level is the nilpotent cone `𝒩`; PBW for `V^k(𝔰𝔩₂)` gives only the *upper* bound,
which is `symbolAlg_surjective` and is already free.  So it is carried, in the manner of
`EtingofFinite`, `ZhuAdmissibleSemisimple`, `RegularImpliesTrivialGraded` and
`DLMSimpleAdmissibleOrdinary`, as a named citation hypothesis. -/

/-- **Exactness of the symbol presentation of `L₋₄⁄₃(𝔰𝔩₂)`**: the symbol map
`Sym(𝔰𝔩₂) → A₂(L₋₄⁄₃(𝔰𝔩₂))` has kernel exactly `Cas·𝔪`.

Equivalently `R_{L₋₄⁄₃(𝔰𝔩₂)} ≅ Sym(𝔰𝔩₂)/Cas·𝔪`, whose reduction is `ℂ[𝒩]`.

⚠ **Status: NOT proved in this repository.**  This is *not* Arakawa's theorem: T. Arakawa,
*Associated varieties of modules over Kac–Moody algebras and C₂-cofiniteness of W-algebras*,
IMRN 2015, gives `X_{L_k(𝔰𝔩₂)} = 𝒩` at admissible level, i.e. only the **radical** of the kernel;
the kernel itself being `Cas·𝔪` is a stronger, unverified statement.  It is a **lower** bound on
`A₂`, so no amount of PBW input supplies it. -/
def Sl2ExactSymbol : Prop := sl2PresentationSimpleSl2QL.IsExact

/-- Under the named hypothesis `Sl2ExactSymbol`, `L₋₄⁄₃(𝔰𝔩₂)` is **not** `C₂`-cofinite.

⚠ Conditional on `Sl2ExactSymbol` (not proved).  The unconditional statement is
`Sl2NonLisse.not_C2Cofinite_simpleSl2QL` (`Examples.AffineSl2NonLisse`). -/
theorem not_C2Cofinite_simpleSl2QL_of_exact (hex : Sl2ExactSymbol) : ¬ C2Cofinite simpleSl2QL :=
  sl2PresentationSimpleSl2QL.not_C2Cofinite hex

/-- Under `Sl2ExactSymbol`, both halves of the Arakawa–Kawasetsu configuration at once:
`L₋₄⁄₃(𝔰𝔩₂)` is not `C₂`-cofinite yet does satisfy Etingof–Schedler finiteness.

⚠ Only the second half is unconditional (`etingofFinite_simpleSl2QL'`). -/
theorem quasiLisseWitness_simpleSl2QL_of_exact (hex : Sl2ExactSymbol) :
    ¬ C2Cofinite simpleSl2QL ∧ EtingofFinite simpleSl2QL :=
  ⟨not_C2Cofinite_simpleSl2QL_of_exact hex, etingofFinite_simpleSl2QL'⟩

/-- Under `Sl2ExactSymbol`, the symbol map identifies `A₂(L₋₄⁄₃(𝔰𝔩₂))` with the explicit model
`R = Sym(𝔰𝔩₂) ⧸ Cas·𝔪` of `Examples.AffineSl2QuasiLisse`. -/
def nilpEquiv_simpleSl2QL_of_exact (hex : Sl2ExactSymbol) : NilpAlg ≃ₗ[ℂ] A₂ simpleSl2QL :=
  sl2PresentationSimpleSl2QL.nilpEquiv hex

end

end VOA.Sl2Pres

section AxiomAudit
#print axioms VOA.Sl2Pres.adCompat_of_generators
#print axioms VOA.Sl2Pres.symbolAlg
#print axioms VOA.Sl2Pres.symbolAlg_casSym
#print axioms VOA.Sl2Pres.mk₂_wordStateA_mem_range
#print axioms VOA.Sl2Pres.symbolAlg_surjective
#print axioms VOA.Sl2Pres.affineSl2QL_eq_voaSl2Adm
#print axioms VOA.Sl2Pres.A₂QL
#print axioms VOA.Sl2Pres.A₂QL_surjective
#print axioms VOA.Sl2Pres.A₂QL_bracket
#print axioms VOA.Sl2Pres.A₂QL_casV
#print axioms VOA.Sl2Pres.bracket_eL_fL
#print axioms VOA.Sl2Pres.bracket_eL_hL
#print axioms VOA.Sl2Pres.bracket_hL_eL
#print axioms VOA.Sl2Pres.bracket_hL_fL
#print axioms VOA.Sl2Pres.bracket_fL_eL
#print axioms VOA.Sl2Pres.bracket_fL_hL
#print axioms VOA.Sl2Pres.symbolAlgL
#print axioms VOA.Sl2Pres.symbolAlgL_eq_comp
#print axioms VOA.Sl2Pres.symbolAlgL_surjective
#print axioms VOA.Sl2Pres.symbolAlgL_casSym
#print axioms VOA.Sl2Pres.mk₂_sl2Singular_QL
#print axioms VOA.Sl2Pres.mkQ_sl2Singular_QL
#print axioms VOA.Sl2Pres.eL_mul_casL
#print axioms VOA.Sl2Pres.adE_compat_L
#print axioms VOA.Sl2Pres.adH_compat_L
#print axioms VOA.Sl2Pres.adF_compat_L
#print axioms VOA.Sl2Pres.symbolAlgL_hSym_mul_casSym
#print axioms VOA.Sl2Pres.symbolAlgL_fSym_mul_casSym
#print axioms VOA.Sl2Pres.cas_vanishes_L
#print axioms VOA.Sl2Pres.sl2PresentationSimpleSl2QL
#print axioms VOA.Sl2Pres.etingofFinite_simpleSl2QL'
#print axioms VOA.Sl2Pres.finiteDimensional_poissonTraces_simpleSl2QL'
#print axioms VOA.Sl2Pres.vacuum_simpleSl2QL_ne_zero'
#print axioms VOA.Sl2Pres.A₂_simpleSl2QL_nontrivial'
#print axioms VOA.Sl2Pres.not_C2Cofinite_simpleSl2QL_of_exact
#print axioms VOA.Sl2Pres.quasiLisseWitness_simpleSl2QL_of_exact
#print axioms VOA.Sl2Pres.nilpEquiv_simpleSl2QL_of_exact
end AxiomAudit
