/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJCarrierGraded
import VOA.Modules.ZhuVermaAnArchMUFullMode
import VOA.Modules.ZhuVermaAnArchDJ48

/-!
# Dong–Jiang's `𝒱`-action on the balanced carrier `M(U) = ⨁ₙ A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`

Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826
(`math/0601626`), §4, define — immediately after `M(U) = ⨁_{n∈ℤ₊} A_{n,m}(V) ⊗_{A_m(V)} U` and just
before Lemma 4.6 — the operator `u_p : M(U)(n) → M(U)(wt u − p − 1 + n)` by

```
  u_p(v ⊗ w) = (u ∗^{wt u − p − 1 + n}_{m,n} v) ⊗ w   if  wt u − 1 − p + n ≥ 0,
             = 0                                      if  wt u − 1 − p + n < 0,
```

and then say: "We need to prove that `u_p` is well defined", producing **exactly two** obligations.

**(i) Descent through the ideal.**  "Let `v ∈ O_{n,m}(V)` and `w ∈ U`.  By Lemma 2.8,
`u ∗^{wtu−p−1+n}_{m,n} v ∈ V ∗^{wtu−p−1+n}_{m,n} O_{n,m}(V) ⊆ O_{wtu−p−1+n,m}(V)`, so we have
`u_p(v ⊗ w) = 0`."

**(ii) The balancing.**  "Now let `a ∈ A_m(V)`, `v ∈ A_{n,m}(V)`, `w ∈ U`.  Then
```
  u_p((v ∗ⁿ_m a) ⊗ w) = (u ∗^{wtu−p−1+n}_{m,n} (v ∗ⁿ_m a)) ⊗ w
                      = ((u ∗^{wtu−p−1+n}_{m,n} v) ∗^{wtu−p−1+n}_m a) ⊗ w
                      = (u ∗^{wtu−p−1+n}_{m,n} v) ⊗ a·w = u_p(v ⊗ a·w).
```
Thus `u_p` is well defined."

This file discharges both, on the **balanced, full-ideal, general-base-level** carrier
`DJCarrier W U = ⨁ₙ DJPiece W U n` of `ZhuVermaAnArchDJCarrier`/`…Graded`.

## What is proved

### §1 Obligation (i) — `DJLeftSlot`, DJ Lemma 2.8's left inclusion
`DJLeftSlot W N m n : Prop` is `∀ u, ∀ g ∈ O_{n,m}(𝒱), u ∗^N_{m,n} g ∈ O_{N,m}(𝒱)`, i.e. exactly
DJ's `V ∗^N_{m,n} O_{n,m}(V) ⊆ O_{N,m}(V)`.  It is supplied by the proved
`anmGen_OnmFull_left_of_leftGrading` from `LeftGradingResidual W N m n`, and is **unconditional at
base level `m = 0`** (`djLeftSlot_zero`, off the discharged `leftGradingResidual_zero_gen`).  The
bundled `DJActionDescent W m := ∀ N n, DJLeftSlot W N m n` is `djActionDescent_zero` at `m = 0`.
Given it, `AnmFull.leftGen` is the descended `[v] ↦ [u ∗^N_{m,n} v] : A_{n,m}(𝒱) → A_{N,m}(𝒱)`.

### §2 Obligation (ii) — the balancing, unconditionally
The identity DJ's middle step needs is
`(u ∗^N_{m,n} v) ∗^N_m a = u ∗^N_{m,n} (v ∗ⁿ_m a)` in `A_{N,m}(𝒱)`.  In `𝒱` the difference is the
`p₁ = m`, `p₂ = n`, `p₃ = N`, outer-`𝟙` element of DJ's associator span `O''_{N,m}(𝒱)` — a
**generator of the full ideal**, hence zero in `A_{N,m}(𝒱) = 𝒱 ⧸ O_{N,m}(𝒱)` **by construction**.
That is precisely why DJ quotient by the full ideal (`djAssocDefect_mem`,
`mkAnmFull_leftGen_anmRight`; via the proved `bareAssoc_mem_OnmFull`).  No hypothesis is used.

### §3 The action on the balanced piece
`djCoverAct` is `AnmFull.leftGen u ⊗ id` on the `ℂ`-cover; `djBalancing_le_ker_coverAct` is
obligation (ii) in kernel form, and `djPieceAct W U N n h u : DJPiece W U n →ₗ DJPiece W U N` is the
descended map — DJ's `v ⊗ w ↦ (u ∗^N_{m,n} v) ⊗ w` on the **balanced** tensor.

### §4 The mode `u_p` and the field `Y_{M(U)}(u,z)`
`djLevelIncl` is DJ's case split at target level `muTargetLevel k p n = wt u − p − 1 + n`
(the bookkeeping of `ZhuVermaAnArchMUFullMode`), `djMode W U hD p a : End ℂ (DJCarrier W U)` is the
mode extended over the grade decomposition of `a`, and `djYM` is `Y_{M(U)}(u,z) = ∑_p u_p z^{−p−1}`.

### §5 DJ Lemma 4.6, in full, at GENERAL base level `m`
* 4.6(1) `djMode_truncation` — lower truncation, so every `Y_{M(U)}(u,z)` is a field.
* 4.6(2) `djMode_vacuum` / `djYM_vacuum` — `𝟙_p = δ_{p,−1}·id`, i.e. `Y_{M(U)}(𝟙,z) = id`.
  DJ's binomial computation is carried out here at general `m` (not only the
  `m = 0` collapse): `anmGen_vacuum_scalar` evaluates `𝟙 ∗^N_{m,n} x = C(n−N−1, n−N) · x` by
  rewriting the coefficient with `cbz_neg_upper` and `cbz_symm` into a Vandermonde convolution and
  applying `vandermonde_range`; the scalar vanishes for `N ≠ n` and is `1` for `N = n`.
  (This is DJ's "`𝟙_p(v⊗w) = 0` if `p < −1`; `= v⊗w` if `p = −1`; `= 0` if `p ≥ n`; and `= 0` if
  `−1 < p < n` by the alternating binomial identity" — all four cases at once.)

### §6 DJ Lemma 4.7 (the commutator), INTERIOR regime, at general base level `m`
`anmGen_commutator_interior_gen` (representatives) and `djPieceAct_commutator_interior` (on the
balanced piece): `a_p b_q(v⊗w) − b_q a_p(v⊗w) = ∑ᵢ C(p,i)(a₍ᵢ₎b)_{p+q−i}(v⊗w)` whenever **both**
`wt a − p − 1 + n ≥ 0` and `wt b − q − 1 + n ≥ 0`.  unconditional: the two reassociations are the
`O''` generator again, the transport is DJ Lemma 2.8's right inclusion, and DJ Lemma 2.3 is the
proved `dj23Comm_holds` (whose base level is the *middle* index, so it is `m`-agnostic).

## What is NOT here (exact residual)

* DJ Lemma 4.7 is proved here **only in the interior regime**.  Its BOUNDARY regimes
  (`wt a − p − 1 + n < 0` or `wt b − q − 1 + n < 0`), where DJ invoke their Lemma `la4.8`, are NOT
  covered: `DJ48Bdry` (`ZhuVermaAnArchDJ23`) is an undischarged `Prop` in this repo.
* DJ **Lemma 4.8** (associativity / iterate) on this carrier is NOT proved.
* Consequently `DJCarrier W U` is **not** shown to be a `WeakModule`.  Nothing here claims
  otherwise.
* `DJLeftSlot W N m n` for `m ≥ 1` is carried, not discharged: it is DJ Lemma 2.8's left inclusion,
  reduced in `ZhuVermaAnArchDJ28Final` to the single open `LeftGradingResidual W N m n`.  At `m = 0`
  it is a theorem (`djActionDescent_zero`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing
declaration mutated.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.3, Lemma 2.6, Lemma 2.8,
Thm 2.9, Rmk 2.10), §4 (the definition of `u_p`, Lemma 4.6, Lemma 4.7, Lemma `la4.8`).
Repo: `ZhuVermaAnArchDJCarrier` (`DJPiece`, `mkDJPiece_balance`, `AmMod`),
`ZhuVermaAnArchDJCarrierGraded` (`DJCarrier`), `ZhuVermaAnArchDJ27` (`bareAssoc_mem_OnmFull`,
`anmGen_vacuum_diag`), `ZhuVermaAnArchDJ28Final` (`anmGen_OnmFull_left_of_leftGrading`),
`ZhuVermaAnArchLeftGradingResidualFull` (`leftGradingResidual_zero_gen`),
`ZhuVermaAnArchMUFullMode` (`muTargetLevel`, the mode-assembly idiom),
`ZhuRingResidue` (`vandermonde_range`, `reduce_homogeneous`), `ZhuMuIdentity` (`cbz_symm`),
`ZhuVermaAnArchDJ48` (`cbz_neg_upper`), `ZhuVermaAnArchDJ23` (`resExp`, `anmGen_resExp_left`,
`DJ48Bdry`), `ZhuVermaAnArchDJ23Final` (`dj23Comm_holds` = DJ Lemma 2.3, unconditional).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1 Obligation (i): the ideal descent `V ∗^N_{m,n} O_{n,m} ⊆ O_{N,m}` (DJ Lemma 2.8) -/

/-- **Dong–Jiang Lemma 2.8's LEFT inclusion at the level pair `(N, n)`**:
`V ∗^N_{m,n} O_{n,m}(V) ⊆ O_{N,m}(V)`.  This is exactly the first well-definedness obligation for
DJ's operator `u_p` on `M(U)(n) → M(U)(N)`. -/
def DJLeftSlot (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ) : Prop :=
  ∀ u : 𝒱, ∀ g ∈ OnmFull W n m, anmGen W N m n u g ∈ OnmFull W N m

/-- `DJLeftSlot` from the repo's single open DJ Lemma 2.8 residual `LeftGradingResidual`. -/
theorem djLeftSlot_of_leftGrading (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ)
    (hgrad : LeftGradingResidual W N m n) : DJLeftSlot W N m n :=
  fun u g hg => anmGen_OnmFull_left_of_leftGrading W N m n u hgrad g hg

/-- **At base level `m = 0` the ideal descent is unconditional** (the repo's discharged
`leftGradingResidual_zero_gen`). -/
theorem djLeftSlot_zero (W : VertexOperatorAlgebra 𝒱) (N n : ℕ) : DJLeftSlot W N 0 n :=
  djLeftSlot_of_leftGrading W N 0 n (leftGradingResidual_zero_gen W N n)

/-- The ideal descent at **every** level pair — the exact hypothesis DJ's `u_p` needs on all of
`M(U)`. -/
def DJActionDescent (W : VertexOperatorAlgebra 𝒱) (m : ℕ) : Prop :=
  ∀ N n : ℕ, DJLeftSlot W N m n

/-- **At base level `m = 0` the whole action descent is unconditional.** -/
theorem djActionDescent_zero (W : VertexOperatorAlgebra 𝒱) : DJActionDescent W 0 :=
  fun N n => djLeftSlot_zero W N n

/-- **The descended left product** `[v] ↦ [u ∗^N_{m,n} v] : A_{n,m}(𝒱) → A_{N,m}(𝒱)` — obligation
(i) in map form. -/
noncomputable def AnmFull.leftGen (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ)
    (h : DJLeftSlot W N m n) (u : 𝒱) : AnmFull W n m →ₗ[ℂ] AnmFull W N m :=
  (OnmFull W n m).mapQ (OnmFull W N m) (anmGenRightMap W N m n u) (by
    intro g hg
    rw [Submodule.mem_comap, anmGenRightMap_apply]
    exact h u g hg)

@[simp] theorem AnmFull.leftGen_mk (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ)
    (h : DJLeftSlot W N m n) (u v : 𝒱) :
    AnmFull.leftGen W N m n h u (mkAnmFull W n m v) = mkAnmFull W N m (anmGen W N m n u v) := rfl

/-! ## §2 Obligation (ii): the balancing identity, unconditionally

DJ's middle step `u ∗^N_{m,n} (v ∗ⁿ_m a) = (u ∗^N_{m,n} v) ∗^N_m a` holds in `A_{N,m}(𝒱)` because
the difference is the `(p₁, p₂, p₃) = (m, n, N)`, outer-`𝟙` generator of `O''_{N,m}(𝒱)`, a summand
of the full ideal.  This is the whole point of DJ's decision to quotient by `O' + O'' + O'''`. -/

/-- **The DJ associativity defect is a generator of the full ideal.**
`(u ∗^N_{m,n} v) ∗^N_m a − u ∗^N_{m,n} (v ∗ⁿ_m a) ∈ O_{N,m}(𝒱)` — DJ's `O''_{N,m}` generator with
`p₁ = m`, `p₂ = n`, `p₃ = N` and outer factor `𝟙` (`bareAssoc_mem_OnmFull`).  Unconditional. -/
theorem djAssocDefect_mem (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ) (u v a : 𝒱) :
    anmRight W N m (anmGen W N m n u v) a - anmGen W N m n u (anmRight W n m v a)
      ∈ OnmFull W N m := by
  have h := bareAssoc_mem_OnmFull W N m m n u v a
  simpa only [anmGen_eq_anmRight] using h

/-- **DJ's balancing step in `A_{N,m}(𝒱)`**: `[(u ∗^N_{m,n} v) ∗^N_m a] = [u ∗^N_{m,n} (v ∗ⁿ_m a)]`.
Unconditional (the defect is an `O''` generator). -/
theorem mkAnmFull_leftGen_anmRight (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ) (u v a : 𝒱) :
    mkAnmFull W N m (anmRight W N m (anmGen W N m n u v) a)
      = mkAnmFull W N m (anmGen W N m n u (anmRight W n m v a)) := by
  rw [← sub_eq_zero, ← map_sub, mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact djAssocDefect_mem W N m n u v a

/-! ## §3 The action on the balanced level piece `M(U)(n) = A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` -/

section Piece

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- Two `ℂ`-linear maps out of `M(U)(n)` agreeing on the images of the elementary tensors
`[v] ⊗ w` are equal (`mkDJPiece` is surjective, and the cover is generated by such tensors). -/
theorem djPiece_ext {U : AmMod W m} {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {f g : DJPiece W U n →ₗ[ℂ] M}
    (h : ∀ (v : 𝒱) (w : U.carrier),
      f (mkDJPiece W U n (mkAnmFull W n m v ⊗ₜ[ℂ] w))
        = g (mkDJPiece W U n (mkAnmFull W n m v ⊗ₜ[ℂ] w))) : f = g := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨z, rfl⟩ := mkDJPiece_surjective U n y
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul t w =>
      refine Submodule.Quotient.induction_on _ t fun v => ?_
      exact h v w
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

/-- **The action on the `ℂ`-cover**: `AnmFull.leftGen u ⊗ id`, i.e. `[v] ⊗ w ↦ [u ∗^N_{m,n} v] ⊗ w`
before the balancing is imposed. -/
noncomputable def djCoverAct (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (N n : ℕ)
    (h : DJLeftSlot W N m n) (u : 𝒱) : DJCover W U n →ₗ[ℂ] DJCover W U N :=
  TensorProduct.map (AnmFull.leftGen W N m n h u) LinearMap.id

@[simp] theorem djCoverAct_tmul (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (u v : 𝒱)
    (w : U.carrier) :
    djCoverAct W U N n h u (mkAnmFull W n m v ⊗ₜ[ℂ] w)
      = mkAnmFull W N m (anmGen W N m n u v) ⊗ₜ[ℂ] w := by
  rw [djCoverAct, TensorProduct.map_tmul, AnmFull.leftGen_mk, LinearMap.id_apply]

/-- **Obligation (ii), in kernel form**: the level-`n` balancing lands in the kernel of
`z ↦ [u ∗ z]` followed by the level-`N` projection.  On a generator this is exactly DJ's chain
`u_p((v ∗ⁿ_m a) ⊗ w) = ((u ∗^N_{m,n} v) ∗^N_m a) ⊗ w = (u ∗^N_{m,n} v) ⊗ a·w`. -/
theorem djBalancing_le_ker_coverAct (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (u : 𝒱) :
    djBalancing W U n ≤ LinearMap.ker ((mkDJPiece W U N).comp (djCoverAct W U N n h u)) := by
  rw [djBalancing, Submodule.span_le]
  rintro z ⟨x, a, w, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.comp_apply, LinearMap.comp_apply,
    djCoverAct_tmul, djCoverAct_tmul, sub_eq_zero, ← mkAnmFull_leftGen_anmRight W N m n u x a]
  exact mkDJPiece_balance U N (anmGen W N m n u x) a w

/-- **Dong–Jiang's operator on the balanced level piece**:
`u_p : M(U)(n) → M(U)(N)`, `v ⊗ w ↦ (u ∗^N_{m,n} v) ⊗ w`, with `N = wt u − p − 1 + n`.
Both well-definedness obligations are discharged: (i) the ideal descent `h : DJLeftSlot W N m n`
(DJ Lemma 2.8), and (ii) the balancing `djBalancing_le_ker_coverAct` (DJ's `O''` generator). -/
noncomputable def djPieceAct (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m) (N n : ℕ)
    (h : DJLeftSlot W N m n) (u : 𝒱) : DJPiece W U n →ₗ[ℂ] DJPiece W U N :=
  (djBalancing W U n).liftQ ((mkDJPiece W U N).comp (djCoverAct W U N n h u))
    (djBalancing_le_ker_coverAct U N n h u)

/-- The action commutes with the projection from the `ℂ`-cover. -/
theorem djPieceAct_mkDJPiece (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (u : 𝒱)
    (z : DJCover W U n) :
    djPieceAct W U N n h u (mkDJPiece W U n z) = mkDJPiece W U N (djCoverAct W U N n h u z) := rfl

@[simp] theorem djPieceAct_mk (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (u v : 𝒱)
    (w : U.carrier) :
    djPieceAct W U N n h u (mkDJPiece W U n (mkAnmFull W n m v ⊗ₜ[ℂ] w))
      = mkDJPiece W U N (mkAnmFull W N m (anmGen W N m n u v) ⊗ₜ[ℂ] w) := by
  rw [djPieceAct_mkDJPiece, djCoverAct_tmul]

theorem djPieceAct_add_acting (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (u₁ u₂ : 𝒱) :
    djPieceAct W U N n h (u₁ + u₂) = djPieceAct W U N n h u₁ + djPieceAct W U N n h u₂ := by
  refine djPiece_ext (fun v w => ?_)
  rw [LinearMap.add_apply, djPieceAct_mk, djPieceAct_mk, djPieceAct_mk, anmGen_add_left, map_add,
    TensorProduct.add_tmul, map_add]

theorem djPieceAct_smul_acting (U : AmMod W m) (N n : ℕ) (h : DJLeftSlot W N m n) (c : ℂ)
    (u : 𝒱) : djPieceAct W U N n h (c • u) = c • djPieceAct W U N n h u := by
  refine djPiece_ext (fun v w => ?_)
  rw [LinearMap.smul_apply, djPieceAct_mk, djPieceAct_mk, anmGen_smul_left, map_smul,
    ← TensorProduct.smul_tmul', map_smul]

end Piece

/-! ## §4 The vacuum coefficient of `∗^N_{m,n}` at general base level `m`

Dong–Jiang's Lemma 4.6(2) computation, carried out here for **arbitrary** `m` (the `m = 0`
collapse is `anmGen_vacuum_offdiag`).  Writing `d = N − n`, the coefficient of
`𝟙 ∗^N_{m,n} x` is `∑_{i=0}^{n} (−1)^i C(m+d+i, i) C(m, m+d+i)`.  Rewriting
`(−1)^i C(m+d+i, i) = C(−m−d−1, i)` (`cbz_neg_upper`) and `C(m, m+d+i) = C(m, −d−i)`
(`cbz_symm`) turns it into a Vandermonde convolution, which evaluates to `C(−d−1, −d)`. -/

/-- `resHom W m P 𝟙 x = C(m, P−1) • x`: the vacuum residue picks the single mode `ℓ = P − 1`. -/
theorem resHom_vacuum_dj (W : VertexOperatorAlgebra 𝒱) (m : ℕ) (P : ℤ) (x : 𝒱) :
    resHom W (m : ℤ) P W.vacuum x = cbz (m : ℤ) (P - 1) • x := by
  rw [resHom_homogeneous W (m : ℤ) P (vacuum_mem_grading_zero W) x, zero_add]
  have hterm : ∀ ℓ ∈ Finset.range ((m : ℤ).toNat + 1),
      cbz (m : ℤ) (ℓ : ℤ) • W.smul W.vacuum ((ℓ : ℤ) - P) x
        = (if (ℓ : ℤ) - P = -1 then cbz (m : ℤ) (ℓ : ℤ) • x else 0) := by
    intro ℓ _
    rw [show W.smul W.vacuum ((ℓ : ℤ) - P) x
          = PreVertexAlgebra.smul W.toPreVertexAlgebra W.vacuum ((ℓ : ℤ) - P) x from rfl,
        PreVertexAlgebra.smul_vacuum_left]
    split_ifs with h1
    · rfl
    · rw [smul_zero]
  rw [Finset.sum_congr rfl hterm]
  rcases le_or_gt 0 (P - 1) with hPnn | hPneg
  · rcases le_or_gt (P - 1) (m : ℤ) with hPle | hPgt
    · rw [Finset.sum_eq_single (P - 1).toNat]
      · rw [show (((P - 1).toNat : ℤ)) = P - 1 from Int.toNat_of_nonneg hPnn, if_pos (by ring)]
      · intro ℓ _ hℓ
        rw [if_neg]
        intro hc
        exact hℓ (by omega)
      · intro hmem
        exact absurd (by simp only [Finset.mem_range]; omega) hmem
    · rw [cbz_lt (by positivity) (by omega), zero_smul]
      refine Finset.sum_eq_zero fun ℓ hℓ => ?_
      simp only [Finset.mem_range] at hℓ
      rw [if_neg (by omega)]
  · rw [cbz_apply_neg (m : ℤ) hPneg, zero_smul]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    rw [if_neg (by omega)]

/-- **The vacuum coefficient of `∗^N_{m,n}`, at general base level `m`**:
`𝟙 ∗^N_{m,n} x = C(n − N − 1, n − N) · x`.  DJ Lemma 4.6(2)'s binomial computation, evaluated by
`cbz_neg_upper` + `cbz_symm` + `vandermonde_range`. -/
theorem anmGen_vacuum_scalar (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ) (x : 𝒱) :
    anmGen W N m n W.vacuum x = cbz ((n : ℤ) - (N : ℤ) - 1) ((n : ℤ) - (N : ℤ)) • x := by
  rw [anmGen]
  have hsq : ∀ i : ℕ, ((-1 : ℂ) ^ i) * ((-1 : ℂ) ^ i) = 1 := by
    intro i; rw [← mul_pow]; norm_num
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ i * cbz ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ)) (i : ℤ))
          • resHom W (m : ℤ) ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ) + 1) W.vacuum x
        = (cbz (-(m : ℤ) - ((N : ℤ) - (n : ℤ)) - 1) (i : ℤ)
            * cbz (m : ℤ) (((n : ℤ) - (N : ℤ)) - (i : ℤ))) • x := by
    intro i _
    rw [resHom_vacuum_dj W m _ x, smul_smul]
    congr 1
    have h1 : cbz ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ)) (i : ℤ)
        = (-1 : ℂ) ^ i * cbz (-(m : ℤ) - ((N : ℤ) - (n : ℤ)) - 1) (i : ℤ) := by
      rw [cbz_neg_upper ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ)) i]
      congr 2
      ring
    have h2 : cbz (m : ℤ) ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ) + 1 - 1)
        = cbz (m : ℤ) (((n : ℤ) - (N : ℤ)) - (i : ℤ)) := by
      rw [show ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ) + 1 - 1)
            = (m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ) from by ring,
        _root_.ZhuMu.cbz_symm m ((m : ℤ) + (N : ℤ) - (n : ℤ) + (i : ℤ))]
      congr 1
      ring
    rw [h1, h2, ← mul_assoc, hsq i, one_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul,
    ZhuRes.vandermonde_range (-(m : ℤ) - ((N : ℤ) - (n : ℤ)) - 1) (m : ℤ) ((n : ℤ) - (N : ℤ))
      (N := n + 1) (by push_cast; omega),
    show (-(m : ℤ) - ((N : ℤ) - (n : ℤ)) - 1) + (m : ℤ) = (n : ℤ) - (N : ℤ) - 1 from by ring]

/-- **The vacuum annihilates off the diagonal at general `m`**: `𝟙 ∗^N_{m,n} x = 0` for `N ≠ n`. -/
theorem anmGen_vacuum_offdiag_gen (W : VertexOperatorAlgebra 𝒱) (m : ℕ) {N n : ℕ} (h : N ≠ n)
    (x : 𝒱) : anmGen W N m n W.vacuum x = 0 := by
  rw [anmGen_vacuum_scalar W N m n x]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [cbz_lt (by omega) (by omega), zero_smul]
  · rw [cbz_apply_neg _ (by omega), zero_smul]

/-! ## §5 The mode `u_p`, the field `Y_{M(U)}(u,z)`, and DJ Lemma 4.6 -/

section Mode

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- The vacuum acts as `0` between distinct levels of the balanced carrier. -/
theorem djPieceAct_vacuum_offdiag (U : AmMod W m) {N n : ℕ} (hne : N ≠ n)
    (h : DJLeftSlot W N m n) : djPieceAct W U N n h W.vacuum = 0 := by
  refine djPiece_ext (fun v w => ?_)
  rw [LinearMap.zero_apply, djPieceAct_mk, anmGen_vacuum_offdiag_gen W m hne v, map_zero,
    TensorProduct.zero_tmul, map_zero]

/-- The vacuum acts as the identity on each level of the balanced carrier. -/
theorem djPieceAct_vacuum_diag (U : AmMod W m) (n : ℕ) (h : DJLeftSlot W n m n) :
    djPieceAct W U n n h W.vacuum = LinearMap.id := by
  refine djPiece_ext (fun v w => ?_)
  rw [LinearMap.id_apply, djPieceAct_mk, anmGen_vacuum_diag W n m v]

/-- **The level-`n` component of the mode `a_p`** for `a` homogeneous of weight `k`: DJ's defining
case split at the target level `wt a − p − 1 + n` (`muTargetLevel`). -/
noncomputable def djLevelIncl (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m)
    (hD : DJActionDescent W m) (k p : ℤ) (n : ℕ) (u : 𝒱) :
    DJPiece W U n →ₗ[ℂ] DJCarrier W U :=
  if 0 ≤ muTargetLevel k p n then
    (DJCarrier.incl W U (muTargetLevel k p n).toNat).comp
      (djPieceAct W U (muTargetLevel k p n).toNat n (hD _ n) u)
  else 0

theorem djLevelIncl_of_neg (U : AmMod W m) (hD : DJActionDescent W m) {k p : ℤ} {n : ℕ}
    (h : muTargetLevel k p n < 0) (u : 𝒱) : djLevelIncl W U hD k p n u = 0 := by
  simp only [djLevelIncl, if_neg (not_le.mpr h)]

theorem djLevelIncl_of_nonneg (U : AmMod W m) (hD : DJActionDescent W m) {k p : ℤ} {n : ℕ}
    (h : 0 ≤ muTargetLevel k p n) (u : 𝒱) :
    djLevelIncl W U hD k p n u
      = (DJCarrier.incl W U (muTargetLevel k p n).toNat).comp
          (djPieceAct W U (muTargetLevel k p n).toNat n (hD _ n) u) := by
  simp only [djLevelIncl, if_pos h]

/-- The level component with the target level named explicitly. -/
theorem djLevelIncl_eq_of_target (U : AmMod W m) (hD : DJActionDescent W m) {k p : ℤ} {n N : ℕ}
    (h : muTargetLevel k p n = (N : ℤ)) (u : 𝒱) :
    djLevelIncl W U hD k p n u
      = (DJCarrier.incl W U N).comp (djPieceAct W U N n (hD N n) u) := by
  have hA : (muTargetLevel k p n).toNat = N := by rw [h]; exact Int.toNat_natCast N
  have hnn : 0 ≤ muTargetLevel k p n := by rw [h]; positivity
  subst hA
  exact djLevelIncl_of_nonneg U hD hnn u

theorem djLevelIncl_add_acting (U : AmMod W m) (hD : DJActionDescent W m) (k p : ℤ) (n : ℕ)
    (u₁ u₂ : 𝒱) :
    djLevelIncl W U hD k p n (u₁ + u₂)
      = djLevelIncl W U hD k p n u₁ + djLevelIncl W U hD k p n u₂ := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [djLevelIncl_of_nonneg U hD h, djLevelIncl_of_nonneg U hD h, djLevelIncl_of_nonneg U hD h,
      djPieceAct_add_acting]
    exact LinearMap.comp_add _ _ _
  · rw [djLevelIncl_of_neg U hD (not_le.mp h), djLevelIncl_of_neg U hD (not_le.mp h),
      djLevelIncl_of_neg U hD (not_le.mp h), add_zero]

theorem djLevelIncl_smul_acting (U : AmMod W m) (hD : DJActionDescent W m) (k p : ℤ) (n : ℕ)
    (c : ℂ) (u : 𝒱) :
    djLevelIncl W U hD k p n (c • u) = c • djLevelIncl W U hD k p n u := by
  by_cases h : 0 ≤ muTargetLevel k p n
  · rw [djLevelIncl_of_nonneg U hD h, djLevelIncl_of_nonneg U hD h, djPieceAct_smul_acting]
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  · rw [djLevelIncl_of_neg U hD (not_le.mp h), djLevelIncl_of_neg U hD (not_le.mp h), smul_zero]

/-- The mode `a_p` for `a` homogeneous of weight `k`, assembled from the level components by the
universal property of `M(U) = ⨁ₙ M(U)(n)`. -/
noncomputable def djModeFamily (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m)
    (hD : DJActionDescent W m) (p k : ℤ) :
    (W.grading k) →ₗ[ℂ] Module.End ℂ (DJCarrier W U) where
  toFun ak := DirectSum.toModule ℂ ℕ (DJCarrier W U)
    (fun n => djLevelIncl W U hD k p n (ak : 𝒱))
  map_add' a b := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply, DirectSum.toModule_lof,
      Submodule.coe_add, djLevelIncl_add_acting]
  map_smul' c a := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.toModule_lof,
      SetLike.val_smul, djLevelIncl_smul_acting, RingHom.id_apply, LinearMap.smul_apply]

/-- **Dong–Jiang's mode `a_p` on the balanced carrier `M(U)`**, extended over the grade
decomposition of `a`. -/
noncomputable def djMode (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m)
    (hD : DJActionDescent W m) (p : ℤ) (a : 𝒱) : Module.End ℂ (DJCarrier W U) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (djModeFamily W U hD p)) (DirectSum.decompose W.grading a)

/-- On a homogeneous `a ∈ 𝒱_k` the mode collapses to the single weight-`k` slice. -/
theorem djMode_homogeneous (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    djMode W U hD p a
      = DirectSum.toModule ℂ ℕ (DJCarrier W U) (fun n => djLevelIncl W U hD k p n a) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : djMode W U hD p a = djModeFamily W U hD p k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (djModeFamily W U hD p)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (djModeFamily W U hD p) k ⟨a, ha⟩
  rw [hcollapse]; rfl

theorem djMode_add_acting (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) (a b : 𝒱) :
    djMode W U hD p (a + b) = djMode W U hD p a + djMode W U hD p b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (djModeFamily W U hD p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) a b

theorem djMode_smul_acting (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) (c : ℂ) (a : 𝒱) :
    djMode W U hD p (c • a) = c • djMode W U hD p a := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (djModeFamily W U hD p)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c a

@[simp] theorem djMode_zero_acting (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) :
    djMode W U hD p (0 : 𝒱) = 0 := by
  have := djMode_smul_acting U hD p (0 : ℂ) (0 : 𝒱)
  simpa using this

/-- **DJ's defining formula for `u_p`** on a homogeneous level-`n` vector. -/
theorem djMode_apply_incl (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (n : ℕ) (x : DJPiece W U n) :
    djMode W U hD p a (DJCarrier.incl W U n x) = djLevelIncl W U hD k p n a x := by
  rw [djMode_homogeneous U hD p ha]
  exact DirectSum.toModule_lof ℂ n x

/-- DJ's defining formula, spelled out on an elementary tensor at a nonnegative target level. -/
theorem djMode_apply_tmul (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) {n N : ℕ} (hN : muTargetLevel k p n = (N : ℤ)) (v : 𝒱)
    (w : U.carrier) :
    djMode W U hD p a (DJCarrier.incl W U n (mkDJPiece W U n (mkAnmFull W n m v ⊗ₜ[ℂ] w)))
      = DJCarrier.incl W U N
          (mkDJPiece W U N (mkAnmFull W N m (anmGen W N m n a v) ⊗ₜ[ℂ] w)) := by
  rw [djMode_apply_incl U hD p ha, djLevelIncl_eq_of_target U hD hN, LinearMap.comp_apply,
    djPieceAct_mk]

/-! ### DJ Lemma 4.6(1) — lower truncation -/

/-- The mode `a_p` annihilates level `n` once `p ≥ wt a + n` (DJ's case `wt a − 1 − p + n < 0`). -/
theorem djMode_incl_eq_zero (U : AmMod W m) (hD : DJActionDescent W m) {k p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) {n : ℕ} (hp : k + (n : ℤ) ≤ p) (x : DJPiece W U n) :
    djMode W U hD p a (DJCarrier.incl W U n x) = 0 := by
  rw [djMode_apply_incl U hD p ha n x]
  have hneg : muTargetLevel k p n < 0 := by simp only [muTargetLevel]; omega
  rw [djLevelIncl_of_neg U hD hneg]
  rfl

/-- **DJ Lemma 4.6(1)** — lower truncation: for every `u ∈ 𝒱` and `x ∈ M(U)` there is `N` with
`u_p x = 0` for all `p ≥ N`.  So each `Y_{M(U)}(u,z)` is a field. -/
theorem djMode_truncation (U : AmMod W m) (hD : DJActionDescent W m) (u : 𝒱)
    (x : DJCarrier W U) : ∃ N : ℤ, ∀ p : ℤ, N ≤ p → djMode W U hD p u x = 0 := by
  refine reduce_homogeneous W
    (P := fun u => ∃ N : ℤ, ∀ p : ℤ, N ≤ p → djMode W U hD p u x = 0) ?_ ?_ ?_ u
  · intro k a ha
    have key : ∀ y : DJCarrier W U, ∃ N : ℤ, ∀ p : ℤ, N ≤ p → djMode W U hD p a y = 0 := by
      intro y
      refine DirectSum.induction_on y ⟨0, fun p _ => map_zero _⟩ ?_ ?_
      · intro n z
        exact ⟨k + (n : ℤ), fun p hp => djMode_incl_eq_zero U hD ha hp z⟩
      · rintro y₁ y₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨max N₁ N₂, fun p hp => ?_⟩
        rw [map_add, h₁ p (le_trans (le_max_left _ _) hp), h₂ p (le_trans (le_max_right _ _) hp),
          add_zero]
    exact key x
  · exact ⟨0, fun p _ => by rw [djMode_zero_acting]; rfl⟩
  · rintro u₁ u₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun p hp => ?_⟩
    rw [djMode_add_acting, LinearMap.add_apply, h₁ p (le_trans (le_max_left _ _) hp),
      h₂ p (le_trans (le_max_right _ _) hp), add_zero]

/-! ### DJ Lemma 4.6(2) — `Y_{M(U)}(𝟙, z) = id`, at general base level `m` -/

/-- **DJ Lemma 4.6(2)** — `𝟙_p = δ_{p,−1}·id` on the balanced carrier `M(U)`, at **general** base
level `m`.  All four of DJ's cases (`p < −1`, `p = −1`, `p ≥ n`, and the alternating-binomial case
`−1 < p < n`) are subsumed by `anmGen_vacuum_scalar`. -/
theorem djMode_vacuum (U : AmMod W m) (hD : DJActionDescent W m) (p : ℤ) :
    djMode W U hD p W.vacuum
      = if p = -1 then (1 : Module.End ℂ (DJCarrier W U)) else 0 := by
  rw [djMode_homogeneous U hD p (vacuum_mem_grading_zero W)]
  refine DirectSum.linearMap_ext ℂ (fun n => ?_)
  refine LinearMap.ext (fun x => ?_)
  rw [LinearMap.comp_apply, DirectSum.toModule_lof]
  by_cases hp : p = -1
  · subst hp
    have hT : muTargetLevel 0 (-1) n = (n : ℤ) := by simp only [muTargetLevel]; ring
    rw [djLevelIncl_eq_of_target U hD hT, if_pos rfl, LinearMap.comp_apply,
      djPieceAct_vacuum_diag U n (hD n n)]
    rfl
  · rw [if_neg hp]
    by_cases hT : 0 ≤ muTargetLevel 0 p n
    · have hEq : muTargetLevel 0 p n = (((muTargetLevel 0 p n).toNat : ℕ) : ℤ) :=
        (Int.toNat_of_nonneg hT).symm
      have hne : (muTargetLevel 0 p n).toNat ≠ n := by
        simp only [muTargetLevel] at hT ⊢
        omega
      rw [djLevelIncl_eq_of_target U hD hEq, LinearMap.comp_apply,
        djPieceAct_vacuum_offdiag U hne (hD _ n)]
      simp
    · rw [djLevelIncl_of_neg U hD (not_le.mp hT)]
      simp

/-! ### The state–field correspondence `Y_{M(U)}(u,z)` -/

/-- **`Y_{M(U)}(u,z) = ∑_p u_p z^{−p−1}`** on Dong–Jiang's balanced carrier. -/
noncomputable def djYM (W : VertexOperatorAlgebra 𝒱) (U : AmMod W m)
    (hD : DJActionDescent W m) : 𝒱 →ₗ[ℂ] (Module.End ℂ (DJCarrier W U))⟦z^±⟧ where
  toFun a := fun j => djMode W U hD (-j - 1) a
  map_add' a b := by funext j; exact djMode_add_acting U hD (-j - 1) a b
  map_smul' c a := by funext j; exact djMode_smul_acting U hD (-j - 1) c a

/-- The `p`-th mode of `Y_{M(U)}(a,z)` is exactly `a_p`. -/
@[simp] theorem mode_djYM (U : AmMod W m) (hD : DJActionDescent W m) (a : 𝒱) (p : ℤ) :
    mode (djYM W U hD a) p = djMode W U hD p a := by
  change djMode W U hD (-(-p - 1) - 1) a = djMode W U hD p a
  congr 1
  ring

/-- **DJ Lemma 4.6(2), field form**: `Y_{M(U)}(𝟙, z) = id`. -/
theorem djYM_vacuum (U : AmMod W m) (hD : DJActionDescent W m) :
    djYM W U hD W.vacuum
      = (fun j : ℤ => if j = 0 then (1 : Module.End ℂ (DJCarrier W U)) else 0) := by
  funext j
  change djMode W U hD (-j - 1) W.vacuum = _
  rw [djMode_vacuum]
  by_cases hj : j = 0
  · rw [if_pos (by omega), if_pos hj]
  · rw [if_neg (by omega), if_neg hj]

end Mode

/-! ## §6 Dong–Jiang Lemma 4.7 (the commutator), INTERIOR regime, at general base level `m`

DJ's proof of Lemma 4.7 in the regime `wt a − p − 1 + n ≥ 0` **and** `wt b − q − 1 + n ≥ 0` is
exactly two reassociations plus DJ Lemma 2.3:
```
  a_p b_q (v ⊗ w) − b_q a_p (v ⊗ w)
    = ((a ∗^{N}_{n,n₁} b) ∗^{N}_{m,n} v) ⊗ w − ((b ∗^{N}_{n,n₂} a) ∗^{N}_{m,n} v) ⊗ w
    = ((Res_z (1+z)^p Y(a,z)b) ∗^{N}_{m,n} v) ⊗ w
    = ∑ᵢ C(p,i) (a₍ᵢ₎b)_{p+q−i} (v ⊗ w).
```
Both reassociations are the `O''`-generator (`bareAssoc_mem_OnmFull`, general `m`), the transport of
the DJ 2.3 difference through the outer product is DJ Lemma 2.8's RIGHT inclusion
(`anmGen_OnmFull_right_unconditional`, general `m`, unconditional), and DJ Lemma 2.3 itself is the
proved unconditional `dj23Comm_holds` — whose base level is the *middle* index `n`, not `m`.  So the
whole interior regime goes through at **general base level `m`** with **no hypothesis**.

The repo's `anmGen_commutator_interior` / `oFullU_commutator_interior_tmul` are the `m = 0`,
`⊗_ℂ`-carrier instances of exactly this; what follows is the general-`m`, balanced-carrier version.

⚠ The BOUNDARY regimes of DJ Lemma 4.7 (`wt a − p − 1 + n < 0` or `wt b − q − 1 + n < 0`, where DJ
invoke their Lemma `la4.8`) are NOT covered here — `DJ48Bdry` is an undischarged `Prop` in the repo.
So this is DJ 4.7's interior regime only, and `DJCarrier` is not a `WeakModule`. -/

/-- `a ∗ⁿ_{m,p} 0 = 0` (the general product is linear in the right slot). -/
private theorem anmGen_left_zero_dj (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (v : 𝒱) :
    anmGen W n m p 0 v = 0 := by
  have := anmGen_smul_left W n m p (0 : ℂ) 0 v
  simpa using this

/-- The commutator's OPE family has finite support, at general base level `m`. -/
theorem commSum_repr_support_finite_gen (W : VertexOperatorAlgebra 𝒱) (N m n : ℕ) (p : ℤ)
    (a b g : 𝒱) :
    (Function.support fun i : ℕ => gBinom p i • anmGen W N m n (W.smul a i b) g).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by rw [hNz i (by omega), anmGen_left_zero_dj, smul_zero])

/-- **Dong–Jiang Lemma 4.7, interior regime, on representatives, at GENERAL base level `m`** —
unconditional.  For homogeneous `a` of weight `K`, levels with `N = n₁ + n₂ − n` and
`p = K − 1 + n − n₂`,
```
  a ∗^N_{m,n₁}(b ∗^{n₁}_{m,n} g) − b ∗^N_{m,n₂}(a ∗^{n₂}_{m,n} g)
      ≡ ∑ᵢ C(p,i) · (a₍ᵢ₎b) ∗^N_{m,n} g    (mod O_{N,m}(𝒱)).
```
Ingredients: the two `O''` reassociations (`bareAssoc_mem_OnmFull`), DJ Lemma 2.3 at base level `n`
(`dj23Comm_holds`, unconditional), and DJ Lemma 2.8's right inclusion
(`anmGen_OnmFull_right_unconditional`, unconditional). -/
theorem anmGen_commutator_interior_gen (W : VertexOperatorAlgebra 𝒱) (m : ℕ)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ)) (g : 𝒱) :
    anmGen W N m n₁ a (anmGen W n₁ m n b g) - anmGen W N m n₂ b (anmGen W n₂ m n a g)
        - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
      ∈ OnmFull W N m := by
  have h₁ : anmGen W N m n₁ a (anmGen W n₁ m n b g)
      - anmGen W N m n (anmGen W N n n₁ a b) g ∈ OnmFull W N m := by
    have h := (OnmFull W N m).neg_mem (bareAssoc_mem_OnmFull W N m n n₁ a b g)
    rwa [neg_sub] at h
  have h₂ : anmGen W N m n₂ b (anmGen W n₂ m n a g)
      - anmGen W N m n (anmGen W N n n₂ b a) g ∈ OnmFull W N m := by
    have h := (OnmFull W N m).neg_mem (bareAssoc_mem_OnmFull W N m n n₂ b a g)
    rwa [neg_sub] at h
  have hD : anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b ∈ OnmFull W N n := by
    have h := dj23Comm_holds W K a ha b n n₁ n₂ N hN
    rw [← hp] at h
    exact Onm_le_OnmFull W N n h
  have h₃ : anmGen W N m n
      (anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b) g ∈ OnmFull W N m :=
    anmGen_OnmFull_right_unconditional W N m n g _ hD
  rw [show anmGen W N m n (anmGen W N n n₁ a b - anmGen W N n n₂ b a - resExp W p a b) g
      = anmGen W N m n (anmGen W N n n₁ a b) g - anmGen W N m n (anmGen W N n n₂ b a) g
        - anmGen W N m n (resExp W p a b) g from by
    have hs := (anmGenLeftMap W N m n g).map_sub
      (anmGen W N n n₁ a b - anmGen W N n n₂ b a) (resExp W p a b)
    have hs' := (anmGenLeftMap W N m n g).map_sub
      (anmGen W N n n₁ a b) (anmGen W N n n₂ b a)
    simp only [anmGenLeftMap_apply] at hs hs'
    rw [hs, hs'], anmGen_resExp_left] at h₃
  have hcomb : anmGen W N m n₁ a (anmGen W n₁ m n b g)
      - anmGen W N m n₂ b (anmGen W n₂ m n a g)
      - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g
    = (anmGen W N m n₁ a (anmGen W n₁ m n b g) - anmGen W N m n (anmGen W N n n₁ a b) g)
      - (anmGen W N m n₂ b (anmGen W n₂ m n a g) - anmGen W N m n (anmGen W N n n₂ b a) g)
      + (anmGen W N m n (anmGen W N n n₁ a b) g - anmGen W N m n (anmGen W N n n₂ b a) g
          - ∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g) := by abel
  rw [hcomb]
  exact (OnmFull W N m).add_mem ((OnmFull W N m).sub_mem h₁ h₂) h₃

section Comm

variable {W : VertexOperatorAlgebra 𝒱} {m : ℕ}

/-- **Dong–Jiang Lemma 4.7, interior regime, on the BALANCED level piece**, at general base
level `m`:
```
  a_p b_q ([g] ⊗ w) − b_q a_p ([g] ⊗ w) = ∑ᵢ C(p,i) · (a₍ᵢ₎b)_{p+q−i} ([g] ⊗ w)
```
with `n₁` the `b_q` target level, `n₂` the `a_p` target level, `N = n₁ + n₂ − n` the common target
and `p = wt a − 1 + n − n₂`.  Obtained from the representative-level
`anmGen_commutator_interior_gen` by pushing through `[·] ⊗ w` and the balancing quotient. -/
theorem djPieceAct_commutator_interior (U : AmMod W m)
    {K : ℤ} {a : 𝒱} (ha : a ∈ W.grading K) (b : 𝒱) {n n₁ n₂ N : ℕ} {p : ℤ}
    (hN : (N : ℤ) = (n₁ : ℤ) + (n₂ : ℤ) - (n : ℤ)) (hp : p = K - 1 + (n : ℤ) - (n₂ : ℤ))
    (h₁ : DJLeftSlot W N m n₁) (h₂ : DJLeftSlot W n₁ m n) (h₃ : DJLeftSlot W N m n₂)
    (h₄ : DJLeftSlot W n₂ m n) (h₅ : DJLeftSlot W N m n) (g : 𝒱) (w : U.carrier) :
    djPieceAct W U N n₁ h₁ a
        (djPieceAct W U n₁ n h₂ b (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
      - djPieceAct W U N n₂ h₃ b
        (djPieceAct W U n₂ n h₄ a (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
      = ∑ᶠ i : ℕ, gBinom p i •
          djPieceAct W U N n h₅ (W.smul a i b)
            (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)) := by
  -- the evaluation map `𝒱 → M(U)(N)`, `x ↦ [x] ⊗ w`
  let Φ : 𝒱 →ₗ[ℂ] DJPiece W U N :=
    ((mkDJPiece W U N).comp
      ((TensorProduct.mk ℂ (AnmFull W N m) U.carrier).flip w)).comp (mkAnmFull W N m)
  have hΦ : ∀ x : 𝒱, Φ x = mkDJPiece W U N (mkAnmFull W N m x ⊗ₜ[ℂ] w) := fun _ => rfl
  have hfin := commSum_repr_support_finite_gen W N m n p a b g
  have hL₁ : djPieceAct W U N n₁ h₁ a
      (djPieceAct W U n₁ n h₂ b (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
      = Φ (anmGen W N m n₁ a (anmGen W n₁ m n b g)) := by
    rw [djPieceAct_mk, djPieceAct_mk, hΦ]
  have hL₂ : djPieceAct W U N n₂ h₃ b
      (djPieceAct W U n₂ n h₄ a (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
      = Φ (anmGen W N m n₂ b (anmGen W n₂ m n a g)) := by
    rw [djPieceAct_mk, djPieceAct_mk, hΦ]
  have hR : (∑ᶠ i : ℕ, gBinom p i • djPieceAct W U N n h₅ (W.smul a i b)
        (mkDJPiece W U n (mkAnmFull W n m g ⊗ₜ[ℂ] w)))
      = Φ (∑ᶠ i : ℕ, gBinom p i • anmGen W N m n (W.smul a i b) g) := by
    rw [map_finsum Φ hfin]
    refine finsum_congr fun i => ?_
    rw [djPieceAct_mk, map_smul, hΦ]
  have hker : ∀ x ∈ OnmFull W N m, Φ x = 0 := by
    intro x hx
    have hz : mkAnmFull W N m x = 0 := by
      rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
    rw [hΦ, hz, TensorProduct.zero_tmul, map_zero]
  rw [hL₁, hL₂, hR, ← map_sub, ← sub_eq_zero, ← map_sub]
  exact hker _ (anmGen_commutator_interior_gen W m ha b hN hp g)

end Comm

/-! ## §7 The unconditional base-level `m = 0` specializations

At `m = 0` **both** obligations are theorems: (i) is `djActionDescent_zero`, (ii) is unconditional.
So `M(U)` carries Dong–Jiang's `𝒱`-modes with no hypothesis at all. -/

/-- The Dong–Jiang mode `a_p` on `M(U)` at base level `0` — **hypothesis-free**. -/
noncomputable def djModeZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (p : ℤ) (a : 𝒱) :
    Module.End ℂ (DJCarrier W U) :=
  djMode W U (djActionDescent_zero W) p a

/-- `Y_{M(U)}(u,z)` on `M(U)` at base level `0` — **hypothesis-free**. -/
noncomputable def djYMZero (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) :
    𝒱 →ₗ[ℂ] (Module.End ℂ (DJCarrier W U))⟦z^±⟧ :=
  djYM W U (djActionDescent_zero W)

/-- DJ Lemma 4.6(1) at base level `0`, hypothesis-free. -/
theorem djModeZero_truncation (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (u : 𝒱)
    (x : DJCarrier W U) : ∃ N : ℤ, ∀ p : ℤ, N ≤ p → djModeZero W U p u x = 0 :=
  djMode_truncation U (djActionDescent_zero W) u x

/-- DJ Lemma 4.6(2) at base level `0`, hypothesis-free. -/
theorem djModeZero_vacuum (W : VertexOperatorAlgebra 𝒱) (U : AmMod W 0) (p : ℤ) :
    djModeZero W U p W.vacuum = if p = -1 then (1 : Module.End ℂ (DJCarrier W U)) else 0 :=
  djMode_vacuum U (djActionDescent_zero W) p

end VOA
