/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuNormalization
import VOA.Modularity.ZhuRecursionProof

/-!
# The `q`-graded trace calculus  (the middle development for Zhu's recursion)

`trace_weightBlock_comm_shift` says that moving an operator around a trace displaces the *weight
degree*.  Zhu's recursion needs that statement not one degree at a time but as an identity between
whole formal `q`-series, together with the consequence of iterating it.  That is what this file
builds.

## The three steps

Write `𝒯(A)` for the graded trace `tr_M(A q^{L₀−c/24})` as a `FormalQSeries` (`gradedTraceOp`), and
say `A` **shifts by `s`** when `A : M_α → M_{α+s}` for every `α` (`WeightShift`).

1. **`q`-graded cyclicity** (`gradedTraceOp_comm_shift`).  If `A` shifts by `−s` and `B` by `+s`,
   then both `A·B` and `B·A` preserve weights, and

     `𝒯(A·B)(e) = 𝒯(B·A)(e + s)`,

   i.e. `𝒯(A·B) = q^{−s}·𝒯(B·A)` as `q`-series.  The **whole content** of the Eisenstein tail
   is this displacement: the two traces are numerically equal but sit in different `q`-degrees.

2. **The step equation** (`gradedTraceOp_commutator_step`).  Subtracting,

     `𝒯(B·A)(e + s) = 𝒯(B·A)(e) + 𝒯([A,B])(e)`,

   a first-order recurrence in the `q`-degree, driven by the *commutator* trace.  Since the
   commutator of modes is computed by Borcherds' formula (`mode_commutator`), the right-hand side is
   a sum of strictly simpler traces — this is the actual engine of the recursion.

3. **Geometric inversion** (`gradedTrace_telescope`, `gradedTrace_geomSolve`).  Solving that
   recurrence downwards is a telescope:

     `𝒯(B·A)(e) = Σ_{j = 1}^{n} 𝒯([A,B])(e − j·s)`   once   `𝒯(B·A)(e − n·s) = 0`,

   which the bounded-below grading always supplies.  **This sum over `j ≥ 1` is the geometric
   series**, and it is where the divisor structure is born: the shift `s` of a mode `u₍ᵢ₎` is
   `wt u − i − 1`, so summing over the mode index too gives a sum over *pairs* `(shift, j)` whose
   product is the total `q`-degree — literally `Nat.divisorsAntidiagonal`, hence `lambertCoeff`
   (`lambertCoeff_eq_sigma`), hence `zhuG` (`qConv_zhuG_eq`).

## Status
Proved, axiom-clean, `pbw`-free.  This is the `q`-degree bookkeeping layer; what it does **not**
yet do is carry out Zhu's specific expansion of `o(a[−1]v)`, which is the remaining residual (see
the end of the file).

## References
* Zhu, J. AMS 9 (1996), Prop. 4.3.2 and its proof; Gannon §5.3.5.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The graded trace of an operator -/

/-- **The graded trace** `𝒯(A) = tr_M(A·q^{L₀−c/24})`, as a formal `q`-series: the coefficient of
`q^e` is the trace of the `α`-diagonal block of `A`, with `α = e + c/24`.

This is `onePoint` with the zero mode `o(v)` replaced by an arbitrary operator — the extra
generality is exactly what Zhu's recursion needs, since the intermediate steps involve traces of
products of *non*-zero modes. -/
noncomputable def gradedTraceOp (N : OrdVModule W M) (A : Module.End ℂ M) : FormalQSeries :=
  fun e =>
    haveI := N.finrank (e + W.centralCharge / 24)
    LinearMap.trace ℂ _ (weightBlock N A (e + W.centralCharge / 24))

/-- The one-point function is the graded trace of the zero mode. -/
theorem gradedTraceOp_oMod (N : OrdVModule W M) (v : 𝒱) :
    gradedTraceOp N (oMod N v) = onePoint N v := rfl

@[simp] theorem gradedTraceOp_add (N : OrdVModule W M) (A B : Module.End ℂ M) :
    gradedTraceOp N (A + B) = gradedTraceOp N A + gradedTraceOp N B := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [gradedTraceOp, Pi.add_apply, weightBlock_add, map_add]

@[simp] theorem gradedTraceOp_smul (N : OrdVModule W M) (c : ℂ) (A : Module.End ℂ M) :
    gradedTraceOp N (c • A) = c • gradedTraceOp N A := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [gradedTraceOp, Pi.smul_apply, weightBlock_smul, map_smul]

theorem gradedTraceOp_sub (N : OrdVModule W M) (A B : Module.End ℂ M) :
    gradedTraceOp N (A - B) = gradedTraceOp N A - gradedTraceOp N B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, gradedTraceOp_add, gradedTraceOp_smul]
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-! ## Weight shifts -/

/-- **`A` shifts the weight by `s`**: `A : M_α → M_{α+s}` for every `α`.  Zero modes shift by `0`
(`weightShift_oMod`); the mode `u₍ᵢ₎` of a homogeneous `u ∈ 𝒱_β` shifts by `β − i − 1`
(`weightShift_mode`). -/
def WeightShift (N : OrdVModule W M) (A : Module.End ℂ M) (s : ℂ) : Prop :=
  ∀ α : ℂ, ∀ x ∈ N.weight α, A x ∈ N.weight (α + s)

/-- Zero modes preserve every weight space: they shift by `0`. -/
theorem weightShift_oMod (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) :
    WeightShift N (oMod N u) 0 := by
  intro α x hx
  rw [add_zero]
  exact oMod_mem_weight N hu hx

/-- **The shift of a mode**: `u₍ᵢ₎` moves `M_α` to `M_{α + β − i − 1}` for homogeneous
`u ∈ 𝒱_β`.  The dependence of the shift on the mode index `i` is what makes the geometric series of
step 3 into a *divisor* sum. -/
theorem weightShift_mode (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (i : ℤ) :
    WeightShift N (mode (N.YM u) i) ((β : ℂ) - (i : ℂ) - 1) := by
  intro α x hx
  have h := mode_mem_weight N hu hx i
  rwa [show α + (β : ℂ) - (i : ℂ) - 1 = α + ((β : ℂ) - (i : ℂ) - 1) from by ring] at h

/-! ## Step 1: `q`-graded cyclicity -/

/-- **`q`-graded cyclicity**: if `A` shifts by `−s` and `B` by `+s`, then

  `𝒯(A·B)(e) = 𝒯(B·A)(e + s)`,

that is, `𝒯(A·B) = q^{−s}·𝒯(B·A)`.  Both products preserve weights, so both traces are defined;
the point is that they are the **same number in different `q`-degrees**.  For `s = 0` this is
ordinary cyclicity (`trace_weightBlock_comm`); every Eisenstein coefficient in Zhu's recursion
comes from `s ≠ 0`. -/
theorem gradedTraceOp_comm_shift (N : OrdVModule W M) (A B : Module.End ℂ M) (s : ℂ)
    (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    gradedTraceOp N (A * B) e = gradedTraceOp N (B * A) (e + s) := by
  have hBα : ∀ x ∈ N.weight (e + W.centralCharge / 24),
      B x ∈ N.weight (e + s + W.centralCharge / 24) := by
    intro x hx
    have h := hB _ x hx
    rwa [show e + W.centralCharge / 24 + s = e + s + W.centralCharge / 24 from by ring] at h
  have hAα : ∀ x ∈ N.weight (e + s + W.centralCharge / 24),
      A x ∈ N.weight (e + W.centralCharge / 24) := by
    intro x hx
    have h := hA _ x hx
    rwa [show e + s + W.centralCharge / 24 + -s = e + W.centralCharge / 24 from by ring] at h
  haveI := N.finrank (e + W.centralCharge / 24)
  haveI := N.finrank (e + s + W.centralCharge / 24)
  exact trace_weightBlock_comm_shift N A B (e + W.centralCharge / 24)
    (e + s + W.centralCharge / 24) hAα hBα

/-! ## Step 2: the step equation driven by the commutator -/

/-- **The step equation**.  With `A` shifting by `−s` and `B` by `+s`,

  `𝒯(B·A)(e + s) = 𝒯(B·A)(e) + 𝒯(A·B − B·A)(e)`.

This is a first-order recurrence in the `q`-degree whose inhomogeneous term is the trace of the
**commutator** `[A, B]` — which Borcherds' formula (`mode_commutator`) rewrites as a sum of traces
of strictly simpler operators.  That is precisely how Zhu's recursion lowers complexity. -/
theorem gradedTraceOp_commutator_step (N : OrdVModule W M) (A B : Module.End ℂ M) (s : ℂ)
    (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    gradedTraceOp N (B * A) (e + s)
      = gradedTraceOp N (B * A) e + gradedTraceOp N (A * B - B * A) e := by
  rw [gradedTraceOp_sub, Pi.sub_apply, ← gradedTraceOp_comm_shift N A B s hA hB e]
  ring

/-! ## Step 3: geometric inversion (the telescope) -/

/-- **The telescope**, unconditionally: any solution of the step equation
`G(e + s) = G(e) + H(e)` satisfies

  `G(e) = G(e − n·s) + Σ_{j = 1}^{n} H(e − j·s)`   for every `n`.

Stated for bare `q`-series so that it can be applied with `G = 𝒯(B·A)` and `H = 𝒯([A,B])` without
carrying the module data through the induction. -/
theorem gradedTrace_telescope (G H : FormalQSeries) (s : ℂ)
    (hstep : ∀ e, G (e + s) = G e + H e) (e : ℂ) (n : ℕ) :
    G e = G (e - (n : ℂ) * s) + ∑ j ∈ Finset.range n, H (e - ((j : ℂ) + 1) * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hkey := hstep (e - ((n : ℂ) + 1) * s)
      rw [show e - ((n : ℂ) + 1) * s + s = e - (n : ℂ) * s from by ring] at hkey
      rw [ih, hkey, Finset.sum_range_succ]
      push_cast
      ring

/-- **Geometric inversion**: once the telescope reaches a degree where the trace vanishes —
which the bounded-below grading guarantees, since `𝒯` is supported in degrees bounded below — the
recurrence is *solved*:

  `G(e) = Σ_{j = 1}^{n} H(e − j·s)`.

This finite sum over `j ≥ 1` **is** the geometric series `Σ_j q^{j·s}` of Zhu's proof.  Combined
with the mode index — the shift `s` of `u₍ᵢ₎` being itself linear in `i` (`weightShift_mode`) — the
pairs `(i, j)` contributing to a fixed total degree are exactly the factorisations of that degree,
i.e. `Nat.divisorsAntidiagonal`, which is how `lambertCoeff`/`σ` and hence `zhuG` enter. -/
theorem gradedTrace_geomSolve (G H : FormalQSeries) (s : ℂ)
    (hstep : ∀ e, G (e + s) = G e + H e) (e : ℂ) (n : ℕ)
    (hvanish : G (e - (n : ℂ) * s) = 0) :
    G e = ∑ j ∈ Finset.range n, H (e - ((j : ℂ) + 1) * s) := by
  rw [gradedTrace_telescope G H s hstep e n, hvanish, zero_add]

/-- **The two steps combined**, in the form the recursion uses: for `A` shifting by `−s` and
`B` by `+s`, the graded trace of `B·A` is the geometric sum of commutator traces. -/
theorem gradedTraceOp_geomSolve (N : OrdVModule W M) (A B : Module.End ℂ M) (s : ℂ)
    (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) (n : ℕ)
    (hvanish : gradedTraceOp N (B * A) (e - (n : ℂ) * s) = 0) :
    gradedTraceOp N (B * A) e
      = ∑ j ∈ Finset.range n, gradedTraceOp N (A * B - B * A) (e - ((j : ℂ) + 1) * s) :=
  gradedTrace_geomSolve _ _ s (gradedTraceOp_commutator_step N A B s hA hB) e n hvanish

/-! ## The degenerate case, as a consistency check -/

/-- With `s = 0` the step equation degenerates to `𝒯([A,B]) = 0` — ordinary cyclicity, and exactly
the mechanism behind `zhuVanishing_holds`.  Sampling this degenerate case is what confirms the sign
convention in `gradedTraceOp_comm_shift`: no Eisenstein tail can appear when nothing is
displaced. -/
theorem gradedTraceOp_commutator_zero_shift (N : OrdVModule W M) (A B : Module.End ℂ M)
    (hA : WeightShift N A 0) (hB : WeightShift N B 0) (e : ℂ) :
    gradedTraceOp N (A * B - B * A) e = 0 := by
  have h := gradedTraceOp_commutator_step N A B 0 (by simpa using hA) hB e
  rw [add_zero] at h
  linear_combination -h

/-! ## The `a[m]` expansion of a one-point function

Zhu's recursion is a statement about `𝒵_M(a[−1]v)`.  Since `a[m]v` is by definition a `Σᶠ` over the
ordinary modes `a₍ᵢ₎v`, and the one-point function is linear, the one-point function of a
square-bracket mode is a `Σᶠ` of ordinary one-point functions.  That is the first structural step of
the assembly, and it is unconditional. -/

/-- The one-point function at a **fixed** `q`-degree, packaged as a `ℂ`-linear functional on `𝒱`.
This is what lets `Σᶠ` pass through `𝒵_M(−)` (`map_finsum`). -/
noncomputable def onePointAt (N : OrdVModule W M) (e : ℂ) : 𝒱 →ₗ[ℂ] ℂ where
  toFun v := onePoint N v e
  map_add' v w := congrFun (onePoint_add N v w) e
  map_smul' c v := congrFun (onePoint_smul N c v) e

@[simp] theorem onePointAt_apply (N : OrdVModule W M) (e : ℂ) (v : 𝒱) :
    onePointAt N e v = onePoint N v e := rfl

/-- **The square-bracket expansion of a one-point function**:

  `𝒵_M(a[m]v)(e) = Σᶠ_i c(k,m,i)·𝒵_M(a₍ᵢ₎v)(e)`.

Unconditional, for every `m` — in particular for the `m = −1` of Zhu's recursion, whose left-hand
side this is.  The finiteness of the `Σᶠ` is `sqModeZ_support_finite` (VA5 regularity plus the
lower-triangularity of the square-bracket coefficients). -/
theorem onePoint_vSqZ_expand (N : OrdVModule W M) (a v : 𝒱) (k : ℕ) (m : ℤ) (e : ℂ) :
    onePoint N (vSqZ W a k m v) e
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i * onePoint N (mode (W.Y a) i v) e := by
  have h : onePointAt N e (vSqZ W a k m v)
      = ∑ᶠ i : ℤ, onePointAt N e (sqBracketCoeffZ k m i • mode (W.Y a) i v) := by
    rw [vSqZ_apply, map_finsum (onePointAt N e) (sqModeZ_support_finite W a k m v)]
  simpa only [onePointAt_apply, map_smul, smul_eq_mul] using h

/-- The same for `torusOnePoint`, the `q`-series actually appearing in `ZhuRecursionAt`. -/
theorem torusOnePoint_vSqZ_expand (N : OrdVModule W M) (a v : 𝒱) (k : ℕ) (m : ℤ) (e : ℂ) :
    torusOnePoint N (vSqZ W a k m v) e
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i * torusOnePoint N (mode (W.Y a) i v) e :=
  onePoint_vSqZ_expand N a v k m e

/-- The two-point term of Zhu's recursion is a graded trace of a product of zero modes, so the whole
recursion is an identity between `gradedTraceOp`s — which is the form the calculus above acts on. -/
theorem torusTwoPoint_eq_gradedTraceOp (N : OrdVModule W M) (a v : 𝒱) :
    torusTwoPoint N a v = gradedTraceOp N (oMod N a * oMod N v) := rfl

/-! ## Discharging the vanishing hypothesis from `boundedBelow` -/

/-- A graded trace vanishes in any degree whose weight space is trivial. -/
theorem gradedTraceOp_eq_zero_of_weight_bot (N : OrdVModule W M) (A : Module.End ℂ M) (e : ℂ)
    (h : N.weight (e + W.centralCharge / 24) = ⊥) : gradedTraceOp N A e = 0 := by
  haveI := N.finrank (e + W.centralCharge / 24)
  haveI : Subsingleton (N.weight (e + W.centralCharge / 24)) := by
    rw [h]; infer_instance
  change LinearMap.trace ℂ _ (weightBlock N A (e + W.centralCharge / 24)) = 0
  rw [Subsingleton.elim (weightBlock N A (e + W.centralCharge / 24)) 0, map_zero]

/-- **Every graded trace is supported in degrees bounded below** — directly from `OrdVModule`'s
`boundedBelow`.  This is what makes the telescope of `gradedTrace_geomSolve` terminate. -/
theorem gradedTraceOp_eq_zero_of_re_lt (N : OrdVModule W M) (A : Module.End ℂ M) :
    ∃ B : ℝ, ∀ e : ℂ, (e + W.centralCharge / 24).re < B → gradedTraceOp N A e = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨B, fun e he => gradedTraceOp_eq_zero_of_weight_bot N A e ?_⟩
  by_contra hne
  exact absurd (hB _ hne) (not_le.mpr he)

/-- **Geometric inversion with the vanishing hypothesis discharged**: for a shift `s` with
`0 < Re s`, the telescope always terminates, so no hypothesis beyond `WeightShift` is needed.

The sign condition is genuine and is exactly where the grading's boundedness enters: stepping down
by `s` must *lower* the real part of the degree, which is what eventually leaves the support. -/
theorem exists_gradedTraceOp_vanish (N : OrdVModule W M) (A : Module.End ℂ M) {s : ℂ}
    (hs : 0 < s.re) (e : ℂ) : ∃ n : ℕ, gradedTraceOp N A (e - (n : ℂ) * s) = 0 := by
  obtain ⟨Bd, hBd⟩ := gradedTraceOp_eq_zero_of_re_lt N A
  obtain ⟨n, hn⟩ := exists_nat_gt ((e.re + (W.centralCharge / 24).re - Bd) / s.re)
  refine ⟨n, hBd _ ?_⟩
  have hlt : (e.re + (W.centralCharge / 24).re - Bd) < (n : ℝ) * s.re :=
    (div_lt_iff₀ hs).mp hn
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  linarith

theorem gradedTraceOp_geomSolve_of_re_pos (N : OrdVModule W M) (A B : Module.End ℂ M) {s : ℂ}
    (hs : 0 < s.re) (hA : WeightShift N A (-s)) (hB : WeightShift N B s) (e : ℂ) :
    ∃ n : ℕ, gradedTraceOp N (B * A) e
      = ∑ j ∈ Finset.range n, gradedTraceOp N (A * B - B * A) (e - ((j : ℂ) + 1) * s) := by
  obtain ⟨n, hn⟩ := exists_gradedTraceOp_vanish N (B * A) hs e
  exact ⟨n, gradedTraceOp_geomSolve N A B s hA hB e n hn⟩

/-! ## The compensating mode pair

A single mode `a₍ᵢ₎` shifts the weight, so its graded trace against `o(v)` vanishes identically —
`gradedTraceOp_eq_zero_of_shift` below.  The operators whose traces actually carry information are
**compensating pairs**: `a₍ᵢ₎` paired with the mode of `v` whose shift is exactly opposite.  For
`a ∈ 𝒱_{kₐ}` and `v ∈ 𝒱_ℓ` that partner is `v₍kₐ+ℓ−i−2₎`, and then — this is the point — Borcherds'
formula says their commutator is a sum of **zero modes**, i.e. of operators whose graded traces are
ordinary one-point functions.  Feeding that into `gradedTraceOp_geomSolve` turns the trace of the
pair into a geometric sum of one-point functions, which is Zhu's recursion in embryo. -/

/-- A weight-shifting operator has vanishing graded trace: only the diagonal contributes. -/
theorem gradedTraceOp_eq_zero_of_shift (N : OrdVModule W M) (A : Module.End ℂ M) {s : ℂ}
    (hs : s ≠ 0) (hA : WeightShift N A s) (e : ℂ) : gradedTraceOp N A e = 0 := by
  haveI := N.finrank (e + W.centralCharge / 24)
  exact trace_weightBlock_eq_zero_of_shift N A
    (show e + W.centralCharge / 24 + s ≠ e + W.centralCharge / 24 from by
      intro h; exact hs (by linear_combination h))
    (hA (e + W.centralCharge / 24))

/-- The `p`-support of `p ↦ C(i,p)·o(a₍ₚ₎v)` is finite: `C(i,p) = 0` for `p < 0` (`cbz_apply_neg`)
and `a₍ₚ₎v = 0` for large `p` (VA5 `regularity`). -/
theorem compensating_support_finite (N : OrdVModule W M) (a v : 𝒱) (i : ℤ) :
    (Function.support fun p : ℤ => cbz i p • oMod N (W.smul a p v)).Finite := by
  obtain ⟨Nb, hNb⟩ := W.regularity a v
  refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) (max 0 Nb)) (fun p hp => ?_)
  simp only [Function.mem_support, ne_eq] at hp
  simp only [Set.mem_Ico]
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact hp (by rw [cbz_apply_neg _ hc, zero_smul])
  · by_contra hc
    push_neg at hc
    refine hp ?_
    rw [show W.smul a p v = 0 from by
      rw [PreVertexAlgebra.smul_def]; exact hNb p (le_trans (le_max_right 0 Nb) hc),
      map_zero, smul_zero]

/-- **The compensating-pair commutator is a sum of zero modes**:

  `[a₍ᵢ₎, v₍kₐ+ℓ−i−2₎] = Σᶠ_p C(i,p)·o(a₍ₚ₎v)`.

The mode index `kₐ+ℓ−i−2` is exactly the one that makes the two shifts cancel, and — the reason this
identity exists at all — Borcherds' formula then produces the mode `kₐ+ℓ−2−p` of `a₍ₚ₎v`, which,
since `a₍ₚ₎v ∈ 𝒱_{kₐ+ℓ−p−1}`, *is* its zero mode.  `oMod_commutator` is the special case `i = kₐ−1`
(where the partner is `v₍ℓ−1₎ = o(v)`). -/
theorem mode_compensating_commutator (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (x : M) :
    mode (N.YM a) i (mode (N.YM v) (ka + l - i - 2) x)
        - mode (N.YM v) (ka + l - i - 2) (mode (N.YM a) i x)
      = ∑ᶠ p : ℤ, cbz i p • oMod N (W.smul a p v) x := by
  rw [mode_commutator N.toWeakModule a v x i (ka + l - i - 2)]
  refine finsum_congr (fun p => ?_)
  congr 1
  rw [oMod_of_mem_grading N (W.smul_mem_grading ha hv p)]
  congr 1
  ring

/-- The graded trace at a fixed degree, as a `ℂ`-linear functional on operators. -/
noncomputable def gradedTraceAt (N : OrdVModule W M) (e : ℂ) : Module.End ℂ M →ₗ[ℂ] ℂ where
  toFun A := gradedTraceOp N A e
  map_add' A B := congrFun (gradedTraceOp_add N A B) e
  map_smul' c A := congrFun (gradedTraceOp_smul N c A) e

@[simp] theorem gradedTraceAt_apply (N : OrdVModule W M) (e : ℂ) (A : Module.End ℂ M) :
    gradedTraceAt N e A = gradedTraceOp N A e := rfl

/-- The compensating-pair commutator, at operator level. -/
theorem mode_compensating_commutator_op (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) :
    mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
        - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i
      = ∑ᶠ p : ℤ, cbz i p • oMod N (W.smul a p v) := by
  refine LinearMap.ext (fun x => ?_)
  rw [show (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i) x
    = mode (N.YM a) i (mode (N.YM v) (ka + l - i - 2) x)
      - mode (N.YM v) (ka + l - i - 2) (mode (N.YM a) i x) from rfl,
    mode_compensating_commutator N ha hv i x]
  exact (map_finsum (LinearMap.applyₗ x) (compensating_support_finite N a v i)).symm

/-- **The trace of the compensating-pair commutator is a sum of one-point functions**:

  `𝒯([a₍ᵢ₎, v₍kₐ+ℓ−i−2₎])(e) = Σᶠ_p C(i,p)·𝒵_M(a₍ₚ₎v)(e)`.

Every term on the right is an honest one-point function — this is what makes the recursion
*recursive*. -/
theorem gradedTraceOp_compensating_commutator (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
        - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i) e
      = ∑ᶠ p : ℤ, cbz i p * onePoint N (W.smul a p v) e := by
  rw [mode_compensating_commutator_op N ha hv i]
  have h := map_finsum (gradedTraceAt N e) (compensating_support_finite N a v i)
  simpa only [gradedTraceAt_apply, map_smul, smul_eq_mul, gradedTraceOp_oMod] using h

/-- **The mechanism of Zhu's recursion**, assembled.  For homogeneous `a ∈ 𝒱_{kₐ}`,
`v ∈ 𝒱_ℓ` and any mode index `i`, writing `s = kₐ − i − 1` for the shift of `a₍ᵢ₎`:

  `𝒯(a₍ᵢ₎·v₍kₐ+ℓ−i−2₎)(e) = − Σ_{j=1}^{n} Σᶠ_p C(i,p)·𝒵_M(a₍ₚ₎v)(e − j·s)`.

The left side is a trace of a *product of modes*; the right side is a finite geometric sum of
**one-point functions** at `q`-degrees displaced by multiples of `s`.  That double sum over `(p, j)`
is the source of the divisor structure: `j` is the geometric index and `p` moves the mode, so a
fixed total displacement is achieved by all factorisations of it (`Nat.divisorsAntidiagonal`,
`lambertCoeff_eq_sigma`), which is why Eisenstein coefficients (`zhuG`) appear at the end.

The hypothesis is the same eventual vanishing as in `gradedTrace_geomSolve`. -/
theorem gradedTraceOp_mode_pair_geomSolve (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (e : ℂ) (n : ℕ)
    (hvanish : gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2))
      (e - (n : ℂ) * ((ka : ℂ) - (i : ℂ) - 1)) = 0) :
    gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) e
      = - ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * onePoint N (W.smul a p v)
            (e - ((j : ℂ) + 1) * ((ka : ℂ) - (i : ℂ) - 1)) := by
  set s : ℂ := (ka : ℂ) - (i : ℂ) - 1 with hs
  have hB : WeightShift N (mode (N.YM a) i) s := weightShift_mode N ha i
  have hA : WeightShift N (mode (N.YM v) (ka + l - i - 2)) (-s) := by
    have h := weightShift_mode N hv (ka + l - i - 2)
    rwa [show ((l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1) = -s from by rw [hs]; push_cast; ring] at h
  have hgeom := gradedTraceOp_geomSolve N _ _ s hA hB e n hvanish
  rw [hgeom, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i
      - mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2))
    = -(mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i) from (neg_sub _ _).symm,
    ← neg_one_smul ℂ (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i),
    gradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    gradedTraceOp_compensating_commutator N ha hv i]
  ring

/-- **The mechanism, with no carried hypothesis**: for a mode index `i < kₐ − 1` — exactly the
condition making the shift `s = kₐ − i − 1` positive, so that stepping down by `s` eventually leaves
the bounded-below support —

  `𝒯(a₍ᵢ₎·v₍kₐ+ℓ−i−2₎)(e) = − Σ_{j=1}^{n} Σᶠ_p C(i,p)·𝒵_M(a₍ₚ₎v)(e − j·s)`   for some `n`.

Every hypothesis of `gradedTraceOp_mode_pair_geomSolve` is discharged from the `OrdVModule` axioms
themselves (`boundedBelow` via `exists_gradedTraceOp_vanish`).  The `i < kₐ − 1` restriction is not
a gap: `i = kₐ − 1` is the zero mode `o(a)`, whose trace against `o(v)` is the two-point term
`torusTwoPoint` rather than a tail term, and `i > kₐ − 1` is handled by the mirror telescope. -/
theorem gradedTraceOp_mode_pair_geomSolve_of_lt (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) {i : ℤ} (hi : i < ka - 1) (e : ℂ) :
    ∃ n : ℕ, gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) e
      = - ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * onePoint N (W.smul a p v)
            (e - ((j : ℂ) + 1) * ((ka : ℂ) - (i : ℂ) - 1)) := by
  have hspos : 0 < ((ka : ℂ) - (i : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    have h : (i : ℝ) < (ka : ℝ) - 1 := by exact_mod_cast hi
    linarith
  obtain ⟨n, hn⟩ := exists_gradedTraceOp_vanish N
    (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) hspos e
  exact ⟨n, gradedTraceOp_mode_pair_geomSolve N ha hv i e n hn⟩

/-! ## The mirror telescope, and the trichotomy

The compensating partner of `a₍ᵢ₎` exists for **every** mode index `i`, and the shift
`s = kₐ − i − 1` changes sign across `i = kₐ − 1`.  The three regimes are genuinely different and
together they exhaust the expansion of `o(a[−1]v)`:

* `i < kₐ − 1` (`Re s > 0`): telescope **downwards** — `gradedTraceOp_mode_pair_geomSolve_of_lt`;
* `i = kₐ − 1` (`s = 0`): the pair *is* `o(a)·o(v)`, so its trace is the two-point term of Zhu's
  recursion — `gradedTraceOp_mode_pair_eq_torusTwoPoint`;
* `i > kₐ − 1` (`Re s < 0`): telescope **upwards** — `gradedTraceOp_mode_pair_geomSolve_of_gt`. -/

/-- The telescope run **upwards**, for shifts that lower the degree in the other direction. -/
theorem gradedTrace_telescope_up (G H : FormalQSeries) (s : ℂ)
    (hstep : ∀ e, G (e + s) = G e + H e) (e : ℂ) (n : ℕ) :
    G e = G (e + (n : ℂ) * s) - ∑ j ∈ Finset.range n, H (e + (j : ℂ) * s) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hkey := hstep (e + (n : ℂ) * s)
      rw [show e + (n : ℂ) * s + s = e + ((n : ℂ) + 1) * s from by ring] at hkey
      rw [Finset.sum_range_succ, ih]
      push_cast
      linear_combination -hkey

/-- Upward geometric inversion. -/
theorem gradedTrace_geomSolve_up (G H : FormalQSeries) (s : ℂ)
    (hstep : ∀ e, G (e + s) = G e + H e) (e : ℂ) (n : ℕ)
    (hvanish : G (e + (n : ℂ) * s) = 0) :
    G e = - ∑ j ∈ Finset.range n, H (e + (j : ℂ) * s) := by
  rw [gradedTrace_telescope_up G H s hstep e n, hvanish, zero_sub]

/-- The upward counterpart of `exists_gradedTraceOp_vanish`: for `Re s < 0`, stepping *up* by `s`
lowers the real part, so the support is left after finitely many steps. -/
theorem exists_gradedTraceOp_vanish_up (N : OrdVModule W M) (A : Module.End ℂ M) {s : ℂ}
    (hs : s.re < 0) (e : ℂ) : ∃ n : ℕ, gradedTraceOp N A (e + (n : ℂ) * s) = 0 := by
  obtain ⟨Bd, hBd⟩ := gradedTraceOp_eq_zero_of_re_lt N A
  obtain ⟨n, hn⟩ := exists_nat_gt ((e.re + (W.centralCharge / 24).re - Bd) / (-s.re))
  refine ⟨n, hBd _ ?_⟩
  have hlt : (e.re + (W.centralCharge / 24).re - Bd) < (n : ℝ) * (-s.re) :=
    (div_lt_iff₀ (neg_pos.mpr hs)).mp hn
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero]
  linarith

/-- **The `i = kₐ − 1` term is exactly Zhu's two-point term.**  At that index the compensating
partner of `a₍ᵢ₎ = o(a)` is `v₍ℓ−1₎ = o(v)`, so the pair is the product of zero modes and its graded
trace is `tr_M(o(a)o(v)q^{L₀−c/24})` — the summand `torusTwoPoint` of `ZhuRecursionAt`.

This is what identifies the *non*-tail term of the recursion, and it is why the geometric telescope
must exclude `s = 0`: there is nothing to displace, and the term survives untouched. -/
theorem gradedTraceOp_mode_pair_eq_torusTwoPoint (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) :
    gradedTraceOp N (mode (N.YM a) (ka - 1) * mode (N.YM v) (ka + l - (ka - 1) - 2))
      = torusTwoPoint N a v := by
  rw [show ka + l - (ka - 1) - 2 = l - 1 from by omega, torusTwoPoint_eq_gradedTraceOp,
    oMod_of_mem_grading N ha, oMod_of_mem_grading N hv]

/-- **The mirror mechanism**, for mode indices above the zero mode.  For `kₐ − 1 < i` — so
that `s = kₐ − i − 1` has negative real part — the telescope runs upwards and gives

  `𝒯(a₍ᵢ₎·v₍kₐ+ℓ−i−2₎)(e) = Σ_{j=0}^{n−1} Σᶠ_p C(i,p)·𝒵_M(a₍ₚ₎v)(e + j·s)`   for some `n`,

with no carried hypothesis.  Note the sign and the starting index differ from the `i < kₐ − 1` case
(`gradedTraceOp_mode_pair_geomSolve_of_lt`): the two regimes really are mirror images, not the same
formula. -/
theorem gradedTraceOp_mode_pair_geomSolve_of_gt (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) {i : ℤ} (hi : ka - 1 < i) (e : ℂ) :
    ∃ n : ℕ, gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) e
      = ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * onePoint N (W.smul a p v)
            (e + (j : ℂ) * ((ka : ℂ) - (i : ℂ) - 1)) := by
  set s : ℂ := (ka : ℂ) - (i : ℂ) - 1 with hs
  have hsneg : s.re < 0 := by
    rw [hs]
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    have h : (ka : ℝ) - 1 < (i : ℝ) := by exact_mod_cast hi
    linarith
  have hB : WeightShift N (mode (N.YM a) i) s := weightShift_mode N ha i
  have hA : WeightShift N (mode (N.YM v) (ka + l - i - 2)) (-s) := by
    have h := weightShift_mode N hv (ka + l - i - 2)
    rwa [show ((l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1) = -s from by rw [hs]; push_cast; ring] at h
  obtain ⟨n, hn⟩ := exists_gradedTraceOp_vanish_up N
    (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) hsneg e
  refine ⟨n, ?_⟩
  rw [gradedTrace_geomSolve_up _ _ s (gradedTraceOp_commutator_step N _ _ s hA hB) e n hn,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i
      - mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2))
    = -(mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i) from (neg_sub _ _).symm,
    ← neg_one_smul ℂ (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i),
    gradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    gradedTraceOp_compensating_commutator N ha hv i]
  ring

/-! ## Residual

The `q`-degree bookkeeping is complete, the left-hand side of the recursion is expanded
(`onePoint_vSqZ_expand`), and the trace of a compensating mode pair is reduced to a geometric sum of
one-point functions (`gradedTraceOp_mode_pair_geomSolve`).  What remains is Zhu's specific
rearrangement:

* **Identifying the two-point term.**  Among the `Σᶠ_i` produced by `onePoint_vSqZ_expand` at
  `m = −1`, isolate the part that reassembles `tr o(a)o(v)` (`torusTwoPoint_eq_gradedTraceOp`) and
  feed every remaining term to `gradedTraceOp_geomSolve` with `s` the shift of that mode
  (`weightShift_mode`).  This is the step that has not been carried out.
* **Collecting the divisor sum.**  Each term contributes `Σ_{j ≥ 1}` at degree shift `j·s` with
  `s = wt a − i − 1`; assembling over `i` and `j` and matching total degrees is what turns the
  double sum into `lambertCoeff`, and `qConv_zhuG_eq` then packages it as `zhuG`.  The
  normalisation is already pinned (`ZhuNormalization`), so this step has no convention risk left.
* **The vanishing hypothesis** `𝒯(B·A)(e − n·s) = 0` for large `n` — true because `N.boundedBelow`
  makes every graded trace supported in degrees bounded below, but it is carried as a hypothesis
  here rather than derived, since the derivation needs the sign of `Re s` pinned per term.
-/

end VOA
