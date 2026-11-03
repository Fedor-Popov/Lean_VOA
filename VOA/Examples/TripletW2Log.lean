/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogVModule
import VOA.Modules.ZhuVermaAnArchDJCarrierWeak
import VOA.Modules.ZhuVermaAnArchLU
import VOA.Modularity.OmegaCentral
import VOA.Modularity.Anm0FiniteDim
import VOA.Examples.TripletW2

/-!
# Genuine logarithmic modules: `L₀` with a nonzero nilpotent part

`Modules.LogVModule` defines the grading-restricted **generalized** module (Huang–Lepowsky–Zhang,
McRae Def. 2.4) and splits `L₀ = L₀ˢˢ + L₀ⁿⁱˡ`.  Nothing in the library so far produces an object
with `L₀ⁿⁱˡ ≠ 0`: every module built to date is an `OrdVModule` in disguise.  This file supplies
the mechanism that does, and states — precisely, without faking it — the one Zhu-algebra fact that
is still missing before the mechanism fires at a concrete vertex operator algebra.

## §1–§2 The mechanism, entirely unconditional

Dong–Jiang's induced module `M(U) = ⨁ₙ A_{n,0}(𝒱) ⊗_{A(𝒱)} U` is a weak module for **any**
bundled `A(𝒱)`-module `U`, with **zero** carried hypotheses (`djCarrierWeak`, proved in
`Modules.ZhuVermaAnArchDJCarrierWeak`).  What this file adds is the `L₀` law on it:

* `anmFull_omega_level` — the level-`n` collapse `[ω ∗̄ⁿ₀ v] = [v ∗ⁿ₀ ω] + n·[v]` in `A_{n,0}(𝒱)`;
* `djModeZero_omega_tmul` — hence, on `M(U)(n)`,

    `L₀ ([v] ⊗ w) = [v] ⊗ ρ([ω])·w  +  n · ([v] ⊗ w)` ,

  i.e. **`L₀ = ρ([ω]) + n` on level `n`, with no assumption on `U` whatsoever.**

This is the exact generalization of `Modularity.HL0Scoped.genHL0`, which assumes `AMod.OmegaScalar`
(`[ω]` acts on `U` by a single scalar) and concludes `L₀ = h + n`.  Dropping that assumption is the
whole point: if `ρ([ω])` is **not** semisimple, `M(U)` has genuine Jordan blocks.  Consequences:

* `djModeZero_omega_sub_tmul` / `djModeZero_omega_sub_pow_tmul` — `(L₀ − (h+n))ᵏ` on `M(U)(n)` is
  `1 ⊗ (ρ([ω]) − h)ᵏ`;
* `djCarrier_deg_le_maxGenEigenspace` — so `M(U)(n)` sits in the **generalized** `L₀`-eigenspace
  of eigenvalue `h + n` as soon as `(ρ([ω]) − h)ᵏ = 0` on `U`;
* `djModeZero_omega_bottom` — the textbook logarithmic pair on the bottom,
  `L₀ x_w = h·x_w + x_{(ρ([ω])−h)w}`.

## §3–§4 The packaging

* `djLogVModule W U h k hnil hfin : LogVModule W (DJCarrier W U)` — the `LogVModule` structure.
  Two carried inputs: the nilpotency datum `hnil : (ρ([ω]) − h)ᵏ = 0` on `U`, and
  `hfin : ∀ n, FiniteDimensional ℂ (DJPiece W U n)`, which `LogVModule.finrank` demands.
  (`GradedLWWeakModule` was invented in `ZhuVermaAnArchDJCarrierWeak` precisely to avoid `finrank`
  at the *regular* bottom; here the bottom is finite-dimensional whenever `A(𝒱)` is, so `finrank`
  is available and the honest `LogVModule` can be built.)
* `djLogVModule_L0nil_ne_zero` — `L₀ⁿⁱˡ ≠ 0`, given the Dong–Jiang gate `DJAnnEqAn W 0`
  (which identifies `M(U)(0) ≅ U`) and `ρ([ω]) − h ≠ 0` on `U`.
* `djLogVModule_jordan_pair` — the same fact in explicit form: two weight-`h` vectors with
  `y ≠ 0` and `L₀ x = h·x + y`.

## §5–§6 The canonical non-semisimple bottom, and why its nilpotency is free

The cheapest legal `U` is `U_h = A(𝒱) ⧸ A(𝒱)·([ω] − h)²` (`omegaJordanAMod`), built here from
scratch: `zhuLeftMul`/`zhuQuotRho`/`zhuQuotAMod` give the quotient of the regular module by a left
ideal as a bundled `AMod`.  Two features make it the right choice.

* **Nilpotency is automatic** (`omegaJordan_nil_sq`): `(ρ([ω]) − h)² = 0` on `U_h` for *every*
  `𝒱` and *every* `h`, because `[ω]` is central in `A(𝒱)` (`omega_central`, Zhu's Lemma 2.1.3),
  so `A(𝒱)·([ω]−h)²` is two-sided.  Recorded here as `omegaShift_central`.
* **It is local at `h`.**  The naive alternative — `U =` the regular module `A(𝒱)` — would need
  `[ω] − h` nilpotent on all of `A(𝒱)`, which is FALSE for the triplet `W(2)`: its Zhu algebra also
  carries the `h = −1/8` and `h = 3/8` blocks.  Passing to `A(𝒱)/A(𝒱)([ω]−h)²` is exactly the
  localization at the eigenvalue `h`, and it costs nothing.

So `omegaJordanLogVModule W h hAnm hA : LogVModule W (DJCarrier W U_h)` carries only finiteness
data, and `omegaJordanLogVModule_L0nil_ne_zero` / `omegaJordanLogVModule_jordan_pair` add the gate
and one Zhu-algebra fact, named `OmegaJordanAt W h`.

## ⚠ THE CARRIED HYPOTHESES — what is NOT proved here, and why

Nothing in this file is `sorry`-ed or axiomatized; everything is either proved or an explicit
argument.  Four inputs are carried, and for `W(2)` **none of them is discharged anywhere in this
repository**:

1. `hA : FiniteDimensional ℂ (A 𝒱)` — `C₂`-cofiniteness of `𝒱`.  Feeds `LogVModule.finrank`
   through `finiteDimensional_DJPiece`.
2. `hAnm : ∀ n, FiniteDimensional ℂ (AnmFull 𝒱 n 0)` — `C_{n+2}`-cofiniteness
   (`Modularity.Anm0FiniteDim.finiteDimensional_AnmFull_of_cofinite` is the bridge, and it is
   stated there that this is *not* implied by `C₂` alone in the form needed).
3. `hgate : DJAnnEqAn 𝒱 0` — Dong–Jiang Prop. 4.6 at level `0`, i.e. `O_{0,0}(𝒱) ≤ O(𝒱)`.  Used
   ONLY by the nonvanishing statements, to identify the bottom `M(U)(0)` with `U`
   (`djPieceMEquiv`).  At project level this is discharged by `gate_of_pbwDatum Pr` from the
   `BottomProjection` datum supplied by the theorem `VOA.pbw`; it is carried explicitly here so that
   this file stays `pbw`-free.
4. ⚠ `hnd : OmegaJordanAt 𝒱 h`, i.e. `[ω] − h ∉ A(𝒱)·([ω] − h)²`.  **This is the crux, and it is
   a statement about the Zhu algebra of a specific vertex operator algebra.**

On (4): for the triplet `W(2) = (Sympl. Fermions)^{even}` the statement is true at `h = 0` —
`W(2)` is `C₂`-cofinite and non-rational, so `A(W(2))` is finite-dimensional and non-semisimple,
and its central element `[ω]` has a rank-two Jordan block at the eigenvalue `0` (this is exactly
the well known `c = −2` logarithmic pair `ω`, `ω̃`).  Proving it in Lean needs an explicit
description of `A(W(2)) = W(2) ⧸ O(W(2))`, and **the repository contains no computation of any
nontrivial Zhu algebra**: `Examples/ZhuInstantiation.lean` treats only the trivial vertex operator
algebra, where `ω = 0` and `[ω] − h = −h` is semisimple for every `h`.  Anything else would be an
invented Zhu-algebra computation, so it is not attempted.  Note also that `hnd` is not merely
convenient: if `[ω]` *is* semisimple then `[ω] − h ∈ A(𝒱)([ω] − h)²` for every `h`, so `hnd` fails
and no logarithmic module comes out of this construction — as it must be (finite-dimensional `A(𝒱)`;
the equivalence is stated, not proved, here).

**Consequence for the acid test.**  What is established is the implication

  `C_{n+2}`-cofinite  +  DJ gate  +  `[ω]` non-semisimple at `h`  ⟹  a `LogVModule` with
  `L₀ⁿⁱˡ ≠ 0` and an explicit rank-two `L₀` Jordan block,

with every step of the implication proved and axiom-clean, and with the `W(2)` specialization
written out (`SympFerm.tripletW2Log`, `SympFerm.tripletW2Log_L0nil_ne_zero`,
`SympFerm.tripletW2Log_jordan_pair`).  What is **not** established is that `LogVModule` is
inhabited with `L₀ⁿⁱˡ ≠ 0` unconditionally: that still waits on input (4).

## Status

`sorry`-free; no `admit`, no `native_decide`, no new axiom.  `#print axioms` on all 40 declarations
of this file reports exactly `[propext, Classical.choice, Quot.sound]` — in particular no `pbw` and
no `sorryAx`.  (Audit run as `lake env lean -DmaxSynthPendingDepth=3`; a bare `lake env lean`
drops the lakefile option and reports spurious failures on these nested quotient/tensor carriers.)
No existing declaration is mutated and no other file is touched.

## References
Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826
(`math/0601626`), §4; Huang–Lepowsky–Zhang `arXiv:1012.4193`; McRae, *On rationality for
`C₂`-cofinite vertex operator algebras*, Def. 2.4; Gaberdiel–Kausch and Kausch for the `c = −2`
triplet and its logarithmic pair.  Repo cross-refs: `Modules.LogVModule`,
`Modules.ZhuVermaAnArchDJCarrierWeak` (`djCarrierWeak`, `djCWeight`),
`Modules.ZhuVermaAnArchDJCarrier` (`AmMod`, `DJPiece`, `djPieceMEquiv`),
`Modularity.HL0Scoped` (`genHL0`, the semisimple special case),
`Modularity.OmegaCentral` (`omega_central`, `zhuMul_omega_comm`),
`Modularity.Anm0FiniteDim` (`finiteDimensional_DJPiece`), `Examples.TripletW2` (`tripletW2`).
-/

namespace VOA

open scoped BigOperators TensorProduct
open VertexOperatorAlgebra
open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 `L₀` on `M(U)` -/

/-- **The level-`n` collapse `[ω ∗̄ⁿ₀ v] = [v ∗ⁿ₀ ω] + n·[v]` in `A_{n,0}(𝒱)`.** -/
theorem anmFull_omega_level (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (v : 𝒱) :
    mkAnmFull W n 0 (anmGen W n 0 n W.conformalVector v)
      = mkAnmFull W n 0 (anmRight W n 0 v W.conformalVector) + (n : ℂ) • mkAnmFull W n 0 v := by
  have resFull_zero_delta : ∀ Q : ℤ,
      resFull W 0 Q W.conformalVector v = W.smul W.conformalVector (-Q) v := by
    intro Q
    rw [resFull]
    have hsingle : ∀ l : ℤ, l ≠ -Q →
        cbz 0 (l + Q) • W.smul W.conformalVector l v = 0 := by
      intro l hl
      rw [cbz_zero_left, if_neg (show l + Q ≠ 0 by omega), zero_smul]
    rw [finsum_eq_single
      (fun l : ℤ => cbz (0 : ℤ) (l + Q) • W.smul W.conformalVector l v) (-Q) hsingle]
    change cbz 0 (-Q + Q) • W.smul W.conformalVector (-Q) v
      = W.smul W.conformalVector (-Q) v
    rw [show (-Q + Q : ℤ) = 0 by ring, cbz_zero, one_smul]
  have hres : resExp W 1 W.conformalVector v
      = W.smul W.conformalVector 0 v + W.smul W.conformalVector 1 v := by
    rw [resExp_eq_resFull, resFull_pascal W 1 0 W.conformalVector v,
      show (1 : ℤ) - 1 = 0 by ring, resFull_zero_delta 0, resFull_zero_delta (0 - 1),
      neg_zero, show (-(0 - 1) : ℤ) = 1 by ring]
  have hL1 : W.smul W.conformalVector (0 : ℤ) v = W.L (-1) v := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((-1 : ℤ) + 1) = (0 : ℤ) by ring]
  have hL0 : W.smul W.conformalVector (1 : ℤ) v = W.L 0 v := by
    rw [PreVertexAlgebra.smul_def, L_def, show ((0 : ℤ) + 1) = (1 : ℤ) by ring]
  have hresL : resExp W 1 W.conformalVector v - (n : ℂ) • v = anmLgen W n 0 v := by
    rw [hres, hL1, hL0, anmLgen]
    push_cast
    module
  have hmemOnm : anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
      - (n : ℂ) • v ∈ Onm W n 0 := by
    have h23 := dj23Comm_holds W 2 W.conformalVector W.conformalVector_mem_grading_two
      v 0 n 0 n (by push_cast; ring)
    rw [show ((2 : ℤ) - 1 + ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = (1 : ℤ) by norm_num,
      anmGen_eq_anmRight W n 0 v W.conformalVector] at h23
    have hcombine : anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
          - (n : ℂ) • v
        = (anmGen W n 0 n W.conformalVector v - anmRight W n 0 v W.conformalVector
            - resExp W 1 W.conformalVector v)
          + (resExp W 1 W.conformalVector v - (n : ℂ) • v) := by abel
    rw [hcombine, hresL]
    exact Submodule.add_mem _ h23 (anmLgen_mem_Onm W n 0 v)
  have hquot : mkAnmFull W n 0 (anmGen W n 0 n W.conformalVector v
      - anmRight W n 0 v W.conformalVector - (n : ℂ) • v) = 0 := by
    rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Onm_le_OnmFull W n 0 hmemOnm
  rw [map_sub, map_sub, map_smul] at hquot
  rw [← sub_eq_zero, ← hquot]
  abel

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`L₀ = ρ([ω]) + n` on `M(U)(n)` — the unconditional, `U`-agnostic grading law.** -/
theorem djModeZero_omega_tmul (U : AmMod W 0) (n : ℕ) (v : 𝒱) (w : U.carrier) :
    djModeZero W U 1 W.conformalVector
        (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))
      = DJCarrier.incl W U n (mkDJPiece W U n
            (mkAnmFull W n 0 v ⊗ₜ[ℂ] U.ρ (mkAnFull W 0 W.conformalVector) w))
        + (n : ℂ) • DJCarrier.incl W U n
            (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)) := by
  have hN : muTargetLevel (2 : ℤ) 1 n = ((n : ℕ) : ℤ) := by unfold muTargetLevel; ring
  have key : mkDJPiece W U n
        (mkAnmFull W n 0 (anmGen W n 0 n W.conformalVector v) ⊗ₜ[ℂ] w)
      = mkDJPiece W U n
          (mkAnmFull W n 0 v ⊗ₜ[ℂ] U.ρ (mkAnFull W 0 W.conformalVector) w)
        + (n : ℂ) • mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w) := by
    rw [anmFull_omega_level W n v, TensorProduct.add_tmul, map_add,
      ← TensorProduct.smul_tmul', map_smul, mkDJPiece_balance U n v W.conformalVector w]
  rw [djModeZero, djMode_apply_tmul U (djActionDescent_zero W) 1
    W.conformalVector_mem_grading_two hN v w, key, map_add, map_smul]


/-! ## §2 The nilpotent part of `L₀` -/

/-- **`ρ([ω]) − h` on the Zhu-algebra bottom `U`.** -/
noncomputable def amModOmegaNil (U : AmMod W 0) (h : ℂ) : Module.End ℂ U.carrier :=
  U.ρ (mkAnFull W 0 W.conformalVector) - h • 1

/-- `L₀ − (h+n)` on `M(U)(n)` is `1 ⊗ (ρ([ω]) − h)`. -/
theorem djModeZero_omega_sub_tmul (U : AmMod W 0) (h : ℂ) (n : ℕ) (v : 𝒱) (w : U.carrier) :
    (djModeZero W U 1 W.conformalVector - (h + (n : ℂ)) • 1)
        (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))
      = DJCarrier.incl W U n (mkDJPiece W U n
          (mkAnmFull W n 0 v ⊗ₜ[ℂ] amModOmegaNil U h w)) := by
  have hr : DJCarrier.incl W U n (mkDJPiece W U n
        (mkAnmFull W n 0 v ⊗ₜ[ℂ] amModOmegaNil U h w))
      = DJCarrier.incl W U n (mkDJPiece W U n
          (mkAnmFull W n 0 v ⊗ₜ[ℂ] U.ρ (mkAnFull W 0 W.conformalVector) w))
        - h • DJCarrier.incl W U n
            (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)) := by
    rw [amModOmegaNil, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      TensorProduct.tmul_sub, map_sub, map_sub, TensorProduct.tmul_smul, map_smul, map_smul]
  rw [hr, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    djModeZero_omega_tmul U n v w, add_smul]
  abel

/-- Iterating: `(L₀ − (h+n))^k` on `M(U)(n)` is `1 ⊗ (ρ([ω]) − h)^k`. -/
theorem djModeZero_omega_sub_pow_tmul (U : AmMod W 0) (h : ℂ) (n : ℕ) :
    ∀ (k : ℕ) (v : 𝒱) (w : U.carrier),
      ((djModeZero W U 1 W.conformalVector - (h + (n : ℂ)) • 1) ^ k)
          (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))
        = DJCarrier.incl W U n (mkDJPiece W U n
            (mkAnmFull W n 0 v ⊗ₜ[ℂ] ((amModOmegaNil U h ^ k) w))) := by
  intro k
  induction k with
  | zero => intro v w; simp
  | succ k ih =>
      intro v w
      rw [pow_succ, Module.End.mul_apply, djModeZero_omega_sub_tmul U h n v w, ih v _,
        pow_succ, Module.End.mul_apply]

/-- **The level-`n` piece lies in the generalized `L₀`-eigenspace of eigenvalue `h + n`.** -/
theorem djCarrier_deg_le_maxGenEigenspace (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0) (n : ℕ) :
    DJCarrier.deg W U n
      ≤ (djModeZero W U 1 W.conformalVector).maxGenEigenspace (h + (n : ℂ)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨k, ?_⟩
  have hmap : ((djModeZero W U 1 W.conformalVector - (h + (n : ℂ)) • 1) ^ k).comp
      (DJCarrier.incl W U n) = 0 := by
    refine djPiece_ext (fun v w => ?_)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [djModeZero_omega_sub_pow_tmul U h n k v w, hnil]
    simp
  have hy := LinearMap.congr_fun hmap y
  simpa using hy


/-! ## §3 The logarithmic module -/

/-- **Dong–Jiang's `M(U)` is a genuine `LogVModule`.** -/
noncomputable def djLogVModule (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n)) :
    LogVModule W (DJCarrier W U) where
  toWeakModule := djCarrierWeak W U
  weight := djCWeight W U h
  isInternal := djCWeight_isInternal W U h
  weight_le_maxGenEigenspace := by
    intro α
    by_cases hcase : ∃ n : ℕ, h + n = α
    · obtain ⟨n, rfl⟩ := hcase
      rw [djCWeight_cast U h n, djCarrierWeak_mode]
      exact djCarrier_deg_le_maxGenEigenspace U h k hnil n
    · rw [djCWeight_eq_bot U h (fun n hn => hcase ⟨n, hn⟩)]
      exact bot_le
  finrank := by
    intro α
    by_cases hcase : ∃ n : ℕ, h + n = α
    · obtain ⟨n, rfl⟩ := hcase
      rw [djCWeight_cast U h n]
      haveI := hfin n
      have hR : FiniteDimensional ℂ (LinearMap.range (DJCarrier.incl W U n)) := inferInstance
      exact hR
    · rw [djCWeight_eq_bot U h (fun n hn => hcase ⟨n, hn⟩)]
      infer_instance
  boundedBelow := djCWeight_boundedBelow U h

@[simp] theorem djLogVModule_weight (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n)) :
    (djLogVModule W U h k hnil hfin).weight = djCWeight W U h := rfl

theorem djLogVModule_L0op (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n)) :
    (djLogVModule W U h k hnil hfin).L0op = djModeZero W U 1 W.conformalVector :=
  djCarrierWeak_mode W U W.conformalVector 1

/-! ## §4 The nilpotent part is nonzero -/

/-- **`L₀` has a nonzero nilpotent part on `M(U)`.** -/
theorem djLogVModule_L0nil_ne_zero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n))
    (hgate : DJAnnEqAn W 0) (hne : amModOmegaNil U h ≠ 0) :
    (djLogVModule W U h k hnil hfin).L0nil ≠ 0 := by
  rw [Ne, ← LogVModule.isL0Semisimple_iff_L0nil_eq_zero]
  intro hss
  refine hne (LinearMap.ext (fun w => ?_))
  have hxmem : DJCarrier.incl W U 0
      (mkDJPiece W U 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] w)) ∈ djCWeight W U h h := by
    rw [djCWeight_zero U h]
    exact ⟨_, rfl⟩
  have hL0 := hss h _ hxmem
  rw [djLogVModule_L0op W U h k hnil hfin, djModeZero_omega_tmul U 0 W.vacuum w] at hL0
  simp only [Nat.cast_zero, zero_smul, add_zero] at hL0
  have h2 : DJCarrier.incl W U 0 (mkDJPiece W U 0
        (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] U.ρ (mkAnFull W 0 W.conformalVector) w))
      = DJCarrier.incl W U 0 (mkDJPiece W U 0
        (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] (h • w))) := by
    rw [TensorProduct.tmul_smul, map_smul, map_smul]
    exact hL0
  have h3 := congrArg (DJCarrier.proj W U 0) h2
  rw [DJCarrier.proj_incl_same, DJCarrier.proj_incl_same] at h3
  have h4 := congrArg (djPieceMEquiv W 0 hgate U) h3
  rw [djPieceMEquiv_mk, djPieceMEquiv_mk, U.ρ_one, Module.End.one_apply,
    Module.End.one_apply] at h4
  rw [amModOmegaNil, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h4,
    LinearMap.zero_apply, sub_self]


/-! ### The explicit Jordan pair at the bottom -/

/-- **`L₀ x_w = h·x_w + x_{(ρ([ω])−h)w}`** on the bottom `M(U)(0)`: the textbook logarithmic
pair, written with no hypothesis at all. -/
theorem djModeZero_omega_bottom (U : AmMod W 0) (h : ℂ) (w : U.carrier) :
    djModeZero W U 1 W.conformalVector
        (DJCarrier.incl W U 0 (mkDJPiece W U 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] w)))
      = h • DJCarrier.incl W U 0 (mkDJPiece W U 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] w))
        + DJCarrier.incl W U 0 (mkDJPiece W U 0
            (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] amModOmegaNil U h w)) := by
  have h0 := djModeZero_omega_sub_tmul U h 0 W.vacuum w
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h0
  simp only [Nat.cast_zero, add_zero] at h0
  rw [← h0]
  abel

/-- Under the Dong–Jiang gate `M(U)(0) ≅ U`, a nonzero `w` gives a nonzero bottom vector. -/
theorem djCarrier_bottom_ne_zero (U : AmMod W 0) (hgate : DJAnnEqAn W 0) {w : U.carrier}
    (hw : w ≠ 0) :
    DJCarrier.incl W U 0 (mkDJPiece W U 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] w)) ≠ 0 := by
  intro hz
  have h1 := congrArg (DJCarrier.proj W U 0) hz
  rw [DJCarrier.proj_incl_same, map_zero] at h1
  have h2 := congrArg (djPieceMEquiv W 0 hgate U) h1
  rw [djPieceMEquiv_mk, map_zero, U.ρ_one, Module.End.one_apply] at h2
  exact hw h2

/-- **An explicit rank-two Jordan block for `L₀`** inside the weight-`h` space: two vectors
`x`, `y` of weight `h` with `y ≠ 0` and `L₀ x = h·x + y`. -/
theorem djLogVModule_jordan_pair (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (h : ℂ) (k : ℕ)
    (hnil : amModOmegaNil U h ^ k = 0)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (DJPiece W U n))
    (hgate : DJAnnEqAn W 0) (hne : amModOmegaNil U h ≠ 0) :
    ∃ x y : DJCarrier W U,
      x ∈ (djLogVModule W U h k hnil hfin).weight h ∧
        y ∈ (djLogVModule W U h k hnil hfin).weight h ∧ y ≠ 0 ∧
        (djLogVModule W U h k hnil hfin).L0op x = h • x + y := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp hne
  rw [LinearMap.zero_apply] at hw
  refine ⟨DJCarrier.incl W U 0 (mkDJPiece W U 0 (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] w)),
    DJCarrier.incl W U 0 (mkDJPiece W U 0
      (mkAnmFull W 0 0 W.vacuum ⊗ₜ[ℂ] amModOmegaNil U h w)), ?_, ?_, ?_, ?_⟩
  · rw [djLogVModule_weight, djCWeight_zero U h]
    exact ⟨_, rfl⟩
  · rw [djLogVModule_weight, djCWeight_zero U h]
    exact ⟨_, rfl⟩
  · exact djCarrier_bottom_ne_zero U hgate hw
  · rw [djLogVModule_L0op W U h k hnil hfin]
    exact djModeZero_omega_bottom U h w

/-! ## §5 The canonical Jordan bottom `A(𝒱) ⧸ A(𝒱)·([ω]−h)²` -/

section Jordan

variable (W)

/-- The set of **left multiples** `A(𝒱)·p`, as a `ℂ`-subspace of `A(𝒱)`. -/
noncomputable def zhuLeftMul (p : A W) : Submodule ℂ (A W) :=
  LinearMap.range ((Amul (zhuRingData_holds W)).flip p)

theorem mem_zhuLeftMul {p q : A W} :
    q ∈ zhuLeftMul W p ↔ ∃ a : A W, Amul (zhuRingData_holds W) a p = q :=
  LinearMap.mem_range

theorem self_mem_zhuLeftMul (p : A W) : p ∈ zhuLeftMul W p :=
  (mem_zhuLeftMul W).mpr ⟨mk W W.vacuum, Amul_one_left _ p⟩

/-- `A(𝒱)·p` is a left ideal. -/
theorem zhuLeftMul_mul_mem (p a : A W) {q : A W} (hq : q ∈ zhuLeftMul W p) :
    Amul (zhuRingData_holds W) a q ∈ zhuLeftMul W p := by
  obtain ⟨b, rfl⟩ := (mem_zhuLeftMul W).mp hq
  exact (mem_zhuLeftMul W).mpr
    ⟨Amul (zhuRingData_holds W) a b, Amul_assoc (zhuRingData_holds W) a b p⟩

/-- The left `A(𝒱)`-action on `A(𝒱) ⧸ A(𝒱)·p`. -/
noncomputable def zhuQuotRho (p : A W) :
    A W →ₗ[ℂ] Module.End ℂ (A W ⧸ zhuLeftMul W p) :=
  (Submodule.mapQLinear (zhuLeftMul W p) (zhuLeftMul W p)).comp
    (LinearMap.codRestrict (Submodule.compatibleMaps (zhuLeftMul W p) (zhuLeftMul W p))
      (Amul (zhuRingData_holds W)) (fun a _q hq => zhuLeftMul_mul_mem W p a hq))

@[simp] theorem zhuQuotRho_apply (p a x : A W) :
    zhuQuotRho W p a (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (Amul (zhuRingData_holds W) a x) := rfl

/-- **`A(𝒱) ⧸ A(𝒱)·p` as a bundled `A(𝒱)`-module.** -/
noncomputable def zhuQuotAMod (p : A W) : AMod W where
  carrier := A W ⧸ zhuLeftMul W p
  ρ := zhuQuotRho W p
  ρ_one := by
    refine LinearMap.ext (fun x => ?_)
    refine Submodule.Quotient.induction_on _ x (fun y => ?_)
    rw [show (one W : A W) = mk W W.vacuum from rfl, zhuQuotRho_apply, Amul_one_left,
      Module.End.one_apply]
  ρ_mul u v := by
    refine LinearMap.ext (fun x => ?_)
    refine Submodule.Quotient.induction_on _ x (fun y => ?_)
    rw [zhuQuotRho_apply, Module.End.mul_apply, zhuQuotRho_apply, zhuQuotRho_apply,
      ← Amul_mk (zhuRingData_holds W) u v, Amul_assoc]

/-- **`[ω] − h` in `A(𝒱)`.** -/
noncomputable def omegaShift (h : ℂ) : A W :=
  mk W W.conformalVector - h • mk W W.vacuum

theorem Amul_omega_comm (q : A W) :
    Amul (zhuRingData_holds W) (mk W W.conformalVector) q
      = Amul (zhuRingData_holds W) q (mk W W.conformalVector) := by
  obtain ⟨v, rfl⟩ := mk_surjective W q
  rw [Amul_mk, Amul_mk, mk_eq_iff]
  exact zhuMul_omega_comm W v

/-- **`[ω] − h` is central in `A(𝒱)`** (Zhu's Lemma 2.1.3). -/
theorem omegaShift_central (h : ℂ) (q : A W) :
    Amul (zhuRingData_holds W) (omegaShift W h) q
      = Amul (zhuRingData_holds W) q (omegaShift W h) := by
  rw [omegaShift, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    Amul_one_left, map_sub, map_smul, Amul_one_right, Amul_omega_comm]

theorem zhuQuotRho_mul_apply (p a b x : A W) :
    (zhuQuotRho W p a * zhuQuotRho W p b) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (Amul (zhuRingData_holds W) a
          (Amul (zhuRingData_holds W) b x)) := rfl

/-- **`[ω]` has a nontrivial Jordan block at `h`** — the precise Zhu-algebra input.

Literally: the class `[ω] − h` is *not* a left multiple of `([ω] − h)²` in `A(𝒱)`.  Equivalently
(when `dim A(𝒱) < ∞`, which is not needed to state it): `[ω]`, which is always central
(`omega_central`), fails to be semisimple at the eigenvalue `h`.  It is exactly the negation of
`[ω] − h ∈ A(𝒱)·([ω] − h)²`, which holds for every `h` as soon as `[ω]` *is* semisimple.

This file does **not** prove it for any concrete vertex operator algebra; see the module
docstring. -/
def OmegaJordanAt (W : VertexOperatorAlgebra 𝒱) (h : ℂ) : Prop :=
  omegaShift W h ∉
    zhuLeftMul W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))

/-- **The Jordan bottom** `U_h = A(𝒱) ⧸ A(𝒱)·([ω]−h)²`. -/
noncomputable def omegaJordanAMod (h : ℂ) : AMod W :=
  zhuQuotAMod W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))

/-- The action of `[ω] − h`, split into its two pieces (with the ideal `p` kept abstract, so that
the rewrite stays type-correct). -/
theorem zhuQuotRho_omegaShift (p : A W) (h : ℂ) :
    zhuQuotRho W p (omegaShift W h)
      = zhuQuotRho W p (mk W W.conformalVector) - h • zhuQuotRho W p (mk W W.vacuum) := by
  rw [omegaShift, map_sub, map_smul]

theorem amModOmegaNil_omegaJordan (h : ℂ) :
    amModOmegaNil (omegaJordanAMod W h).toAmModZero h
      = zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
          (omegaShift W h) := by
  have h1 : ((omegaJordanAMod W h).toAmModZero).ρ (mkAnFull W 0 W.conformalVector)
      = zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
          (mk W W.conformalVector) := rfl
  have h2 : zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
      (mk W W.vacuum) = 1 :=
    (zhuQuotAMod W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))).ρ_one
  rw [zhuQuotRho_omegaShift, amModOmegaNil, h1, h2]
  rfl

/-- **`([ω]−h)² acts as `0`** on `A(𝒱) ⧸ A(𝒱)([ω]−h)²`: the square of the action of a *central*
element lands in the left ideal it generates. -/
theorem zhuQuotRho_omegaShift_sq (h : ℂ) :
    zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
        (omegaShift W h) ^ 2 = 0 := by
  refine LinearMap.ext (fun x => ?_)
  refine Submodule.Quotient.induction_on _ x (fun y => ?_)
  rw [LinearMap.zero_apply, pow_two, zhuQuotRho_mul_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_zhuLeftMul W).mpr ⟨y, ?_⟩
  rw [← Amul_assoc, ← omegaShift_central W h, ← omegaShift_central W h]

/-- **`[ω]−h` acts nonzero** on `A(𝒱) ⧸ A(𝒱)([ω]−h)²` exactly when `[ω]−h ∉ A(𝒱)([ω]−h)²`. -/
theorem zhuQuotRho_omegaShift_ne_zero (h : ℂ)
    (hnd : omegaShift W h ∉
      zhuLeftMul W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))) :
    zhuQuotRho W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))
        (omegaShift W h) ≠ 0 := by
  intro hz
  refine hnd ?_
  have hap := congrArg
    (fun f : Module.End ℂ
        (A W ⧸ zhuLeftMul W (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))) =>
      f (Submodule.Quotient.mk (mk W W.vacuum))) hz
  simp only [zhuQuotRho_apply] at hap
  rw [Amul_one_right] at hap
  exact (Submodule.Quotient.mk_eq_zero _).mp hap

/-- **`(ρ([ω]) − h)² = 0` on the Jordan bottom** — nilpotency, for free. -/
theorem omegaJordan_nil_sq (h : ℂ) :
    amModOmegaNil (omegaJordanAMod W h).toAmModZero h ^ 2 = 0 := by
  rw [amModOmegaNil_omegaJordan]
  exact zhuQuotRho_omegaShift_sq W h

/-- **`ρ([ω]) − h ≠ 0` on the Jordan bottom**, exactly when `[ω]−h ∉ A(𝒱)·([ω]−h)²`. -/
theorem omegaJordan_nil_ne_zero (h : ℂ) (hnd : OmegaJordanAt W h) :
    amModOmegaNil (omegaJordanAMod W h).toAmModZero h ≠ 0 := by
  rw [amModOmegaNil_omegaJordan]
  exact zhuQuotRho_omegaShift_ne_zero W h hnd

end Jordan


/-! ## §6 The canonical logarithmic module of a VOA with non-semisimple `[ω]` -/

/-- **`M(A(𝒱) ⧸ A(𝒱)([ω]−h)²)` is a logarithmic `𝒱`-module.**

The two carried inputs are pure finiteness data: `hAnm` is `C_{n+2}`-cofiniteness of `𝒱`
(`finiteDimensional_AnmFull_of_cofinite`) and `hA` is `dim A(𝒱) < ∞` (`C₂`-cofiniteness).
The Jordan structure itself — `(L₀ − h)² = 0` on the bottom — is unconditional. -/
noncomputable def omegaJordanLogVModule (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull W n 0))
    (hA : FiniteDimensional ℂ (A W)) :
    LogVModule W (DJCarrier W (omegaJordanAMod W h).toAmModZero) :=
  djLogVModule W (omegaJordanAMod W h).toAmModZero h 2 (omegaJordan_nil_sq W h)
    (fun n => finiteDimensional_DJPiece (omegaJordanAMod W h).toAmModZero n (hAnm n)
      (by
        haveI := hA
        have hq : FiniteDimensional ℂ
            (A W ⧸ zhuLeftMul W
              (Amul (zhuRingData_holds W) (omegaShift W h) (omegaShift W h))) := inferInstance
        exact hq))

/-- **Its `L₀` really has a Jordan block**: `L₀ⁿⁱˡ ≠ 0`, so `LogVModule` is strictly more
general than `OrdVModule` on this object. -/
theorem omegaJordanLogVModule_L0nil_ne_zero (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull W n 0))
    (hA : FiniteDimensional ℂ (A W)) (hgate : DJAnnEqAn W 0) (hnd : OmegaJordanAt W h) :
    (omegaJordanLogVModule W h hAnm hA).L0nil ≠ 0 :=
  djLogVModule_L0nil_ne_zero W (omegaJordanAMod W h).toAmModZero h 2
    (omegaJordan_nil_sq W h) _ hgate (omegaJordan_nil_ne_zero W h hnd)

/-- Equivalently: `L₀` is **not** semisimple, so this object is not an `OrdVModule`. -/
theorem omegaJordanLogVModule_not_isL0Semisimple (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull W n 0))
    (hA : FiniteDimensional ℂ (A W)) (hgate : DJAnnEqAn W 0) (hnd : OmegaJordanAt W h) :
    ¬ (omegaJordanLogVModule W h hAnm hA).IsL0Semisimple := by
  rw [LogVModule.isL0Semisimple_iff_L0nil_eq_zero]
  exact omegaJordanLogVModule_L0nil_ne_zero W h hAnm hA hgate hnd

/-- **An explicit rank-two `L₀` Jordan block on the canonical logarithmic module.** -/
theorem omegaJordanLogVModule_jordan_pair (W : VertexOperatorAlgebra 𝒱) (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull W n 0))
    (hA : FiniteDimensional ℂ (A W)) (hgate : DJAnnEqAn W 0) (hnd : OmegaJordanAt W h) :
    ∃ x y : DJCarrier W (omegaJordanAMod W h).toAmModZero,
      x ∈ (omegaJordanLogVModule W h hAnm hA).weight h ∧
        y ∈ (omegaJordanLogVModule W h hAnm hA).weight h ∧ y ≠ 0 ∧
        (omegaJordanLogVModule W h hAnm hA).L0op x = h • x + y :=
  djLogVModule_jordan_pair W (omegaJordanAMod W h).toAmModZero h 2 (omegaJordan_nil_sq W h) _
    hgate (omegaJordan_nil_ne_zero W h hnd)

/-! ## §7 The triplet `W(2)` -/

namespace SympFerm

/-- **Step 1, with NO hypotheses at all.**  The non-semisimple Zhu-algebra bottom
`A(W(2)) ⧸ A(W(2))([ω] − h)²` really does pass through Dong–Jiang's construction and produce a
weak `W(2)`-module.  (Whether its `L₀` has a nonzero nilpotent part is the content of
`tripletW2Log_L0nil_ne_zero`, and that is where the carried hypotheses enter.) -/
noncomputable def tripletW2LogWeak (h : ℂ) :
    WeakModule tripletW2 (DJCarrier tripletW2 (omegaJordanAMod tripletW2 h).toAmModZero) :=
  djCarrierWeak tripletW2 (omegaJordanAMod tripletW2 h).toAmModZero

/-- The `W(2)` logarithmic module, i.e. `§6` at `𝒱 = W(2)`. -/
noncomputable def tripletW2Log (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2)) :
    LogVModule tripletW2
      (DJCarrier tripletW2 (omegaJordanAMod tripletW2 h).toAmModZero) :=
  omegaJordanLogVModule tripletW2 h hAnm hA

/-- `L₀` on the `W(2)` module has a nonzero nilpotent part. -/
theorem tripletW2Log_L0nil_ne_zero (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2)) (hgate : DJAnnEqAn tripletW2 0)
    (hnd : OmegaJordanAt tripletW2 h) :
    (tripletW2Log h hAnm hA).L0nil ≠ 0 :=
  omegaJordanLogVModule_L0nil_ne_zero tripletW2 h hAnm hA hgate hnd

/-- The `W(2)` logarithmic pair: `L₀ x = h·x + y` with `y ≠ 0`, both of weight `h`. -/
theorem tripletW2Log_jordan_pair (h : ℂ)
    (hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull tripletW2 n 0))
    (hA : FiniteDimensional ℂ (A tripletW2)) (hgate : DJAnnEqAn tripletW2 0)
    (hnd : OmegaJordanAt tripletW2 h) :
    ∃ x y : DJCarrier tripletW2 (omegaJordanAMod tripletW2 h).toAmModZero,
      x ∈ (tripletW2Log h hAnm hA).weight h ∧ y ∈ (tripletW2Log h hAnm hA).weight h ∧
        y ≠ 0 ∧ (tripletW2Log h hAnm hA).L0op x = h • x + y :=
  omegaJordanLogVModule_jordan_pair tripletW2 h hAnm hA hgate hnd

end SympFerm

end VOA
