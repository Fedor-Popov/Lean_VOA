/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqWeightSpanning
import VOA.Modules.ZeroModeMult

/-!
# Toward Zhu's recursion: the module commutator formula  (TASK B2)

Zhu's Prop. 4.3.2 rests on two structural inputs.  This file supplies the **first**, in the exact form
the recursion needs.

## The module commutator formula

The `ℓ = 0` case of the module Jacobi identity (`WeakModule.jacobi`) **is** the Borcherds commutator
formula:

  `[u₍ₘ₎, v₍ₙ₎] x = Σᶠ_i C(m,i)·(u₍ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x`     (`mode_commutator`)

Specialised to **zero modes** — `o(u) = u₍ₖ₋₁₎` for `u ∈ 𝒱ₖ`, `o(v) = v₍ₗ₋₁₎` for `v ∈ 𝒱ₗ` — the
right-hand side becomes `Σᶠ_i C(k−1,i)·(u₍ᵢ₎v)₍ₖ₊ₗ₋₂₋ᵢ₎`, and since `u₍ᵢ₎v ∈ 𝒱_{k+ℓ−i−1}` each term is
exactly `o(u₍ᵢ₎v)`.  Because `C(k−1,i)` is **precisely** the square-bracket coefficient
`c(k,0,i) = sqBracketCoeff k 0 i` (`sqBracketCoeff_zero`, proved early in `OnePointFunctions`), this
says

  `[o(u), o(v)] = o(u[0]v)`,

which with trace cyclicity gives the companion vanishing `𝒵_M(a[0]v) = 0` (`ZhuVanishingAt`).  That
identification of `C(k−1,i)` with `c(k,0,i)` is recorded here as `sqBracketCoeff_zero_binom`.

## Status
`ZhuVanishingAt` is proved (`zhuVanishing_holds`) — the companion half of Zhu Prop. 4.3.2 —
along with the whole chain leading to it: `mode_commutator`, `gBinom_natCast`,
`cbz_eq_sqBracketCoeffZ_zero`, `oMod_of_mem_grading`, `oMod_commutator`, `oMod_vSqZ_zero`
(`o(a[0]v) = [o(a), o(v)]`), `oMod_mem_weight`, `weightBlock_mul`, `trace_weightBlock_comm`.
Axiom-clean, `pbw`-free.  The **full** recursion `ZhuRecursionAt` (the `a[−1]` case, where the
Eisenstein tail appears) is the remaining residual.

## References
* Zhu, J. AMS 9 (1996), Prop. 4.3.2; Gannon §5.3.5; Borcherds' commutator formula.
-/

namespace VOA

open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The commutator formula (the `ℓ = 0` module Jacobi) -/

/-- **The module commutator (Borcherds) formula**:
`[u₍ₘ₎, v₍ₙ₎] x = Σᶠ_i C(m,i)·(u₍ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎ x`.
This is the `ℓ = 0` case of the module Jacobi identity: the left-hand `Σᶠ i` collapses at `i = 0`
(`cbz 0 i = δ_{i,0}`, `negOnePow 0 = 1`), leaving exactly the commutator. -/
theorem mode_commutator (A : WeakModule W M) (u v : 𝒱) (x : M) (m n : ℤ) :
    mode (A.YM u) m (mode (A.YM v) n x) - mode (A.YM v) n (mode (A.YM u) m x)
      = ∑ᶠ i : ℤ, cbz m i • mode (A.YM (W.smul u i v)) (m + n - i) x := by
  have hjac := A.jacobi u v x 0 m n
  have hlhs : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (A.YM u) (0 + m - i) (mode (A.YM v) (n + i) x)
          - negOnePow 0 • mode (A.YM v) (0 + n - i) (mode (A.YM u) (m + i) x)))
      = mode (A.YM u) m (mode (A.YM v) n x) - mode (A.YM v) n (mode (A.YM u) m x) := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [cbz_zero_left, mul_one, add_zero, zero_add, sub_zero,
      negOnePow, Even.zero, if_true, one_smul]
  rw [← hlhs, hjac]
  exact finsum_congr (fun i => by rw [zero_add])

/-! ## The coefficient bridge: the commutator weights ARE the square-bracket weights -/

/-- **`c(k,0,i) = C(k−1,i)`** — the `[0]`-square-bracket coefficients are exactly the binomial
weights appearing in the commutator formula (for `k ≥ 1`).  This is what turns
`[o(u), o(v)] = Σ_i C(k−1,i)·o(u₍ᵢ₎v)` into `[o(u), o(v)] = o(u[0]v)`. -/
theorem sqBracketCoeff_zero_binom (k i : ℕ) (hk : 1 ≤ k) :
    sqBracketCoeff k 0 i = ((k - 1).choose i : ℂ) :=
  sqBracketCoeff_zero k i hk

/-- The same, in the all-modes (`ℤ`-indexed) form used by `vSqZ`/`a[0]`: for `i ≥ 0`,
`sqBracketCoeffZ k 0 i = C(k−1, i)`. -/
theorem sqBracketCoeffZ_zero_binom (k : ℕ) (i : ℕ) (hk : 1 ≤ k) :
    sqBracketCoeffZ k 0 (i : ℤ) = ((k - 1).choose i : ℂ) := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, sqBracketCoeffZ_of_nonneg,
    sqBracketCoeff_zero_binom k i hk]

/-! ## `gBinom` on natural upper index is `Nat.choose` -/

/-- **The generalized binomial at a natural upper index is the ordinary one**:
`gBinom (N : ℤ) k = C(N,k)`.  Both satisfy the same Pascal recursion with the same base cases
(`gBinom_succ_pascal` vs `Nat.choose_succ_succ`). -/
theorem gBinom_natCast (N k : ℕ) : gBinom (N : ℤ) k = ((N.choose k : ℕ) : ℂ) := by
  induction N generalizing k with
  | zero =>
      cases k with
      | zero => simp [gBinom]
      | succ j =>
          have hz : gBinom ((0 : ℕ) : ℤ) (j + 1) = 0 := by
            rw [gBinom, Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos j))
              (show (((0 : ℕ) : ℤ) : ℂ) - ((0 : ℕ) : ℂ) = 0 from by push_cast; ring), zero_div]
          rw [hz, Nat.choose_eq_zero_of_lt (Nat.succ_pos j)]
          norm_num
  | succ n ih =>
      cases k with
      | zero => simp [gBinom]
      | succ j =>
          rw [show ((n + 1 : ℕ) : ℤ) = ((n : ℤ) + 1) from by push_cast; ring,
            gBinom_succ_pascal, show ((n : ℤ) + 1 - 1) = ((n : ℕ) : ℤ) from by push_cast; ring,
            ih, ih, Nat.choose_succ_succ]
          push_cast
          ring

/-- **The commutator weights ARE the `a[0]` weights**: `cbz (k−1) i = sqBracketCoeffZ k 0 i`
(for `k ≥ 1`, all `i : ℤ`).  This is the bridge that turns the commutator formula's binomials into the
square-bracket coefficients — i.e. `Σ_i C(k−1,i)·o(u₍ᵢ₎v)` into `o(u[0]v)`. -/
theorem cbz_eq_sqBracketCoeffZ_zero (k : ℕ) (hk : 1 ≤ k) (i : ℤ) :
    cbz ((k : ℤ) - 1) i = sqBracketCoeffZ k 0 i := by
  by_cases hi : 0 ≤ i
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [cbz_apply_nonneg _ hi, Int.toNat_natCast,
      show ((k : ℤ) - 1) = (((k - 1 : ℕ)) : ℤ) from by omega, gBinom_natCast,
      sqBracketCoeffZ_zero_binom k j hk]
  · push_neg at hi
    rw [cbz_apply_neg _ hi, sqBracketCoeffZ_of_lt k (by omega)]

/-! ## The zero mode on homogeneous vectors, and the zero-mode commutator -/

/-- **`o(u) = u₍ₖ₋₁₎` on a homogeneous `u ∈ 𝒱ₖ`** — the graded zero mode collapses to a single mode
(same collapse as `oMod_vacuum`). -/
theorem oMod_of_mem_grading (N : OrdVModule W M) {k : ℤ} {u : 𝒱} (hu : u ∈ W.grading k) :
    oMod N u = mode (N.YM u) (k - 1) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oMod N u = oModFamily N k ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (oModFamily N)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (oModFamily N) k ⟨u, hu⟩
  rw [hcollapse]
  rfl

/-- **The zero-mode commutator, term by term**: for homogeneous `u ∈ 𝒱ₖ`, `v ∈ 𝒱_ℓ`,
`[o(u), o(v)]x = Σᶠ_i C(k−1,i)·o(u₍ᵢ₎v) x`.
Each summand really is a *zero* mode: `u₍ᵢ₎v ∈ 𝒱_{k+ℓ−i−1}`, so its zero mode is the
`(k+ℓ−i−2)`-mode — exactly the index the commutator formula produces. -/
theorem oMod_commutator (N : OrdVModule W M) {k l : ℤ} {u v : 𝒱} (hu : u ∈ W.grading k)
    (hv : v ∈ W.grading l) (x : M) :
    oMod N u (oMod N v x) - oMod N v (oMod N u x)
      = ∑ᶠ i : ℤ, cbz (k - 1) i • oMod N (W.smul u i v) x := by
  rw [oMod_of_mem_grading N hu, oMod_of_mem_grading N hv,
    mode_commutator N.toWeakModule u v x (k - 1) (l - 1)]
  refine finsum_congr (fun i => ?_)
  congr 1
  rw [oMod_of_mem_grading N (W.smul_mem_grading hu hv i)]
  congr 1
  ring

/-- **`o(a[0]v) = [o(a), o(v)]`** (Zhu, the structural half of Prop. 4.3.2): the zero mode of the
square-bracket product `a[0]v` is exactly the **commutator** of zero modes.

This is the whole point of the `[0]`-bracket: by `cbz_eq_sqBracketCoeffZ_zero` the binomial weights of
the Borcherds commutator formula coincide with the square-bracket coefficients `c(k,0,i) = C(k−1,i)`,
so the commutator's expansion `Σ_i C(k−1,i)·o(a₍ᵢ₎v)` reassembles into a single zero mode. -/
theorem oMod_vSqZ_zero (N : OrdVModule W M) {k : ℕ} {l : ℤ} {a v : 𝒱} (hk : 1 ≤ k)
    (ha : a ∈ W.grading (k : ℤ)) (hv : v ∈ W.grading l) (x : M) :
    oMod N (vSqZ W a k 0 v) x = oMod N a (oMod N v x) - oMod N v (oMod N a x) := by
  rw [oMod_commutator N ha hv x]
  have hTapp : ∀ w : 𝒱,
      ((LinearMap.applyₗ x).comp (oMod N) : 𝒱 →ₗ[ℂ] M) w = oMod N w x := fun _ => rfl
  rw [← hTapp, vSqZ_apply,
    map_finsum ((LinearMap.applyₗ x).comp (oMod N) : 𝒱 →ₗ[ℂ] M)
      (sqModeZ_support_finite W a k 0 v)]
  refine finsum_congr (fun i => ?_)
  rw [map_smul, hTapp, cbz_eq_sqBracketCoeffZ_zero k hk i, PreVertexAlgebra.smul_def]

/-! ## Zero modes preserve the weight spaces, and trace cyclicity -/

section
variable {M' : Type u} [AddCommGroup M'] [Module ℂ M']

/-- **`o(u)` preserves every weight space**: for homogeneous `u ∈ 𝒱_β`, `o(u) = u₍β₋₁₎` shifts the
weight by `β − (β−1) − 1 = 0` (`ZeroModeMult.mode_mem_weight`).  This is why the graded trace of a
commutator of zero modes vanishes. -/
theorem oMod_mem_weight (N : OrdVModule W M') {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) {α : ℂ} {x : M'}
    (hx : x ∈ N.weight α) : oMod N u x ∈ N.weight α := by
  rw [oMod_of_mem_grading N hu]
  have h := mode_mem_weight N hu hx (β - 1)
  rwa [show (α + (β : ℂ) - (((β - 1 : ℤ)) : ℂ) - 1) = α from by push_cast; ring] at h

/-- **Blocks compose** when the right factor preserves the weight space. -/
theorem weightBlock_mul (N : OrdVModule W M') (A B : Module.End ℂ M') (α : ℂ)
    (hB : ∀ x ∈ N.weight α, B x ∈ N.weight α) :
    weightBlock N (A * B) α = weightBlock N A α * weightBlock N B α := by
  refine LinearMap.ext (fun y => ?_)
  have hBy : ((weightBlock N B α y : N.weight α) : M') = B (y : M') :=
    congrArg Subtype.val (internalProjTo_coe N.isInternal α ⟨B (y : M'), hB _ y.2⟩)
  apply Subtype.ext
  change ((internalProjTo N.isInternal α) (A (B (y : M'))) : M')
    = ((weightBlock N A α) (weightBlock N B α y) : M')
  rw [show (A (B (y : M'))) = A ((weightBlock N B α y : N.weight α) : M') from by rw [hBy]]
  rfl

/-- **Trace cyclicity on a weight block**, for operators preserving that weight space. -/
theorem trace_weightBlock_comm (N : OrdVModule W M') (A B : Module.End ℂ M') (α : ℂ)
    (hA : ∀ x ∈ N.weight α, A x ∈ N.weight α) (hB : ∀ x ∈ N.weight α, B x ∈ N.weight α) :
    haveI := N.finrank α
    LinearMap.trace ℂ _ (weightBlock N (A * B) α)
      = LinearMap.trace ℂ _ (weightBlock N (B * A) α) := by
  haveI := N.finrank α
  rw [weightBlock_mul N A B α hB, weightBlock_mul N B A α hA, LinearMap.trace_mul_comm]

/-- **Weight-shifting operators have vanishing diagonal blocks**: if `A : M_α → M_β` with `β ≠ α`,
then `weightBlock N A α = 0`.  This is the structural reason only *zero* modes contribute to a graded
trace — the mechanism behind both the vanishing and the recursion. -/
theorem weightBlock_eq_zero_of_shift (N : OrdVModule W M') (A : Module.End ℂ M') {α β : ℂ}
    (hne : β ≠ α) (hA : ∀ x ∈ N.weight α, A x ∈ N.weight β) : weightBlock N A α = 0 := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  refine LinearMap.ext (fun y => Subtype.ext ?_)
  have h := DirectSum.decompose_of_mem_ne N.weight (hA _ y.2) hne
  simpa [weightBlock, internalProjTo, ← DirectSum.apply_eq_component] using h

/-- The graded trace of a strictly weight-shifting operator vanishes. -/
theorem trace_weightBlock_eq_zero_of_shift (N : OrdVModule W M') (A : Module.End ℂ M') {α β : ℂ}
    (hne : β ≠ α) (hA : ∀ x ∈ N.weight α, A x ∈ N.weight β) :
    haveI := N.finrank α
    LinearMap.trace ℂ _ (weightBlock N A α) = 0 := by
  haveI := N.finrank α
  rw [weightBlock_eq_zero_of_shift N A hne hA, map_zero]

/-! ## The companion vanishing `𝒵_M(a[0]v) = 0` -/

/-- **`ZhuVanishingAt`** (Zhu Prop. 4.3.2, the companion half):
`𝒵_M(a[0]v; τ) = 0` for homogeneous `a`.

Proof: `o(a[0]v) = [o(a), o(v)]` (`oMod_vSqZ_zero`), both zero modes preserve every weight space
(`oMod_mem_weight`), and the graded trace of a commutator of weight-preserving operators vanishes by
cyclicity (`trace_weightBlock_comm`) on the finite-dimensional `M_α`. -/
theorem zhuVanishing_holds (N : OrdVModule W M') {k : ℕ} {l : ℤ} {a v : 𝒱} (hk : 1 ≤ k)
    (ha : a ∈ W.grading (k : ℤ)) (hv : v ∈ W.grading l) : ZhuVanishingAt N a v k := by
  have hop : oMod N (vSqZ W a k 0 v) = oMod N a * oMod N v - oMod N v * oMod N a :=
    LinearMap.ext (fun x => by rw [oMod_vSqZ_zero N hk ha hv x]; rfl)
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  change LinearMap.trace ℂ _
    (weightBlock N (oMod N (vSqZ W a k 0 v)) (e + W.centralCharge / 24)) = 0
  rw [hop, sub_eq_add_neg, ← neg_one_smul ℂ (oMod N v * oMod N a), weightBlock_add,
    weightBlock_smul, map_add, map_smul,
    trace_weightBlock_comm N (oMod N a) (oMod N v) _
      (fun _ hx => oMod_mem_weight N ha hx) (fun _ hx => oMod_mem_weight N hv hx)]
  simp

end

/-! ## Residual — what remains for `ZhuRecursionAt`

With `mode_commutator` and `sqBracketCoeffZ_zero_binom` banked, the companion vanishing
`𝒵_M(a[0]v) = 0` needs exactly two further steps:

1. **Zero-mode specialisation** `[o(u), o(v)] = o(u[0]v)`.  Instantiate `mode_commutator` at
   `m = k−1`, `n = ℓ−1` (`u ∈ 𝒱ₖ`, `v ∈ 𝒱_ℓ`) and observe that `u₍ᵢ₎v ∈ 𝒱_{k+ℓ−i−1}`
   (`W.smul_mem_grading`), so the `i`-th term `(u₍ᵢ₎v)₍ₖ₊ₗ₋₂₋ᵢ₎` *is* `oMod` applied to `u₍ᵢ₎v`; then
   `sqBracketCoeffZ_zero_binom` identifies the weights with those of `a[0]`, and linearity of `oMod`
   pulls the `Σᶠ` inside.  The bookkeeping is the grade-index matching, not new mathematics.
2. **Trace cyclicity on weight blocks**: `tr(weightBlock (AB) α) = tr(weightBlock (BA) α)` whenever
   `A`, `B` preserve `M_α` (then the blocks compose, and `LinearMap.trace_mul_comm` applies on the
   finite-dimensional `M_α`).  Zero modes do preserve the weight spaces (they commute with `L₀`),
   which is the graded statement `N.L0_weight`/`ZeroModeMult.L0_commutator`.

For the **full recursion** `ZhuRecursionAt`, step 1 generalises from `a[0]` to `a[−1]` (where the
commutator formula produces the `o(a)o(v)` term plus the tail), and the tail's `q`-expansion is what
assembles the Eisenstein coefficients — this is the genuinely deep half and is where the `E_{2k}`
vs `G_{2k}` normalisation gets pinned (`ZhuRecursionAt` keeps `G` a parameter for exactly that reason).
-/


/-! ## TASK 1b — `q`-graded cyclicity for WEIGHT-SHIFTING operators

This is the mechanism that produces the `q^{shift}` factors, hence the geometric series, hence the
Eisenstein coefficients.  If `B : M_α → M_β` and `A : M_β → M_α`, then `A·B` acts on `M_α` and `B·A`
on `M_β`, and the two blocks have the **same trace** — but sitting in **different `q`-degrees**.  In
`q`-series terms: moving an operator around the trace shifts the exponent by the weight shift. -/

section
variable {M' : Type u} [AddCommGroup M'] [Module ℂ M']

/-- Blocks compose **across a weight shift**. -/
theorem weightBlock_mul_shift (N : OrdVModule W M') (A B : Module.End ℂ M') (α β : ℂ)
    (hA : ∀ x ∈ N.weight β, A x ∈ N.weight α) (hB : ∀ x ∈ N.weight α, B x ∈ N.weight β) :
    weightBlock N (A * B) α = (LinearMap.restrict A hA) ∘ₗ (LinearMap.restrict B hB) := by
  refine LinearMap.ext (fun y => Subtype.ext ?_)
  have hmem : A (B (y : M')) ∈ N.weight α := hA _ (hB _ y.2)
  change ((internalProjTo N.isInternal α) (A (B (y : M'))) : M') = _
  rw [show ((internalProjTo N.isInternal α) (A (B (y : M'))) : M') = A (B (y : M')) from
    congrArg Subtype.val (internalProjTo_coe N.isInternal α ⟨A (B (y : M')), hmem⟩)]
  rfl

/-- **Shifted trace cyclicity**: `tr(A·B |_{M_α}) = tr(B·A |_{M_β})` when `B : M_α → M_β` and
`A : M_β → M_α`.  Note the two traces live in **different weight degrees** — that displacement is
exactly the `q^{β−α}` factor which, summed over the mode index, generates the Lambert/Eisenstein
series (`lambertCoeff`).  The weight-preserving case `β = α` is `trace_weightBlock_comm`. -/
theorem trace_weightBlock_comm_shift (N : OrdVModule W M') (A B : Module.End ℂ M') (α β : ℂ)
    (hA : ∀ x ∈ N.weight β, A x ∈ N.weight α) (hB : ∀ x ∈ N.weight α, B x ∈ N.weight β) :
    haveI := N.finrank α
    haveI := N.finrank β
    LinearMap.trace ℂ _ (weightBlock N (A * B) α)
      = LinearMap.trace ℂ _ (weightBlock N (B * A) β) := by
  haveI := N.finrank α
  haveI := N.finrank β
  rw [weightBlock_mul_shift N A B α β hA hB, weightBlock_mul_shift N B A β α hB hA,
    LinearMap.trace_comp_comm']

end

end VOA
