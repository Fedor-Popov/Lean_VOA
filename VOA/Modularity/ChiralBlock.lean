/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.Schwarzian

/-!
# `n`-point chiral blocks on the torus  (Gannon 5.3.17a)

GOAL D.  Gannon's `n`-point block is
`e^{2πiz₁k₁}⋯ tr_M Y_M(u¹, e^{2πiz₁})⋯Y_M(uⁿ, e^{2πizₙ}) q^{L₀−c/24}`,
periodic of period `1` in each `zᵢ`; the one-point block is the one-point function (5.3.17b).

## Design decision (the carrier)

`FormalQSeries = ℂ → ℂ` (`Modules/Character`) is a *single*-variable coefficient function and cannot
express the `zᵢ`-dependence.  **Carrier chosen:** `FormalNPoint n := (Fin n → ℤ) → FormalQSeries` —
the block is indexed by the `n` **Fourier/mode indices** `jᵢ ∈ ℤ` (the coefficient of
`e^{2πi j₁z₁}⋯e^{2πi jₙzₙ}`), and each coefficient is a formal `q`-series.  Periodicity in `zᵢ` is
then automatic (integer Fourier indices), which is exactly Gannon's stated property.

To make the `n = 1` case *literally* the one-point function, the operator inserted at slot `i` is the
**`jᵢ`-shifted graded zero mode** `o_j(v) = Σ_k (v_k)₍ₖ₋₁₊ⱼ₎` (`oModShift`), so that
`oModShift N 0 = oMod N` (`oModShift_zero`) — the conformal zero mode of `Modules/Character`.  This is
the honest Fourier decomposition of `Y_M(v, e^{2πiz})` against the `L₀`-grading.

## What is proved
* `oModShift`, `oModShift_zero` (recovers `oMod`), `oModShift_vacuum` (`o_j(𝟙) = δ_{j,0}·id`);
* `modeComposite` (the ordered product) and `modeComposite_cons` (peel the head slot);
* `chiralBlock` and `chiralBlock_one` — **the `n = 1` block is `chiralBlockOne`** (the correctness
  check);
* multilinearity in the head slot (`chiralBlock_cons_add`, `chiralBlock_cons_smul`) and the vacuum
  insertion `chiralBlock_cons_vacuum` (inserting `𝟙` at index `0` gives the `(n−1)`-point block);
* **full multilinearity in EVERY slot** (`chiralBlock_update_add`, `chiralBlock_update_smul`),
  by induction on the `Fin.cons` decomposition.

All formal (`q`-series level); no analysis.

## References
* Gannon §5.3.4, eq. (5.3.17a)–(5.3.17b); Zhu, J. AMS 9 (1996).
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- An **`n`-point formal object**: indexed by the `n` integer Fourier indices, valued in formal
`q`-series (Gannon 5.3.17a; periodicity in each `zᵢ` is automatic). -/
abbrev FormalNPoint (n : ℕ) : Type := (Fin n → ℤ) → FormalQSeries

/-! ## The shifted graded zero mode -/

/-- The weight-`k` slice of the `j`-shifted zero mode: `vₖ ↦ (vₖ)₍ₖ₋₁₊ⱼ₎`. -/
noncomputable def oModShiftFamily (N : OrdVModule W M) (j k : ℤ) : (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1 + j)).comp (N.YM.comp (W.grading k).subtype)

/-- **The `j`-shifted graded zero mode** `o_j(v) = Σ_k (v_k)₍ₖ₋₁₊ⱼ₎` — the `j`-th Fourier component
of `Y_M(v, e^{2πiz})` against the `L₀`-grading.  At `j = 0` it is `oMod` (`oModShift_zero`). -/
noncomputable def oModShift (N : OrdVModule W M) (j : ℤ) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oModShiftFamily N j)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- **`o_0 = o`** — the unshifted mode is the conformal zero mode of `Modules/Character`. -/
theorem oModShift_zero (N : OrdVModule W M) : oModShift N 0 = oMod N := by
  have hfam : oModShiftFamily N 0 = oModFamily N := by
    funext k
    rw [oModShiftFamily, oModFamily, add_zero]
  rw [oModShift, oMod, hfam]

/-- **`o_j(𝟙) = δ_{j,0}·id`** — the vacuum contributes only in the unshifted slot. -/
theorem oModShift_vacuum (N : OrdVModule W M) (j : ℤ) :
    oModShift N j W.vacuum = if j = 0 then (LinearMap.id : End ℂ M) else 0 := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oModShift N j W.vacuum = oModShiftFamily N j 0 ⟨W.vacuum, W.vacuum_mem⟩ := by
    change (DFinsupp.lsum ℂ (oModShiftFamily N j)) (DirectSum.decompose W.grading W.vacuum) = _
    rw [DirectSum.decompose_of_mem W.grading W.vacuum_mem]
    exact DFinsupp.lsum_single ℂ (oModShiftFamily N j) 0 ⟨W.vacuum, W.vacuum_mem⟩
  rw [hcollapse]
  change mode (N.YM (W.vacuum : 𝒱)) (0 - 1 + j) = _
  rw [N.vacuum_YM, mode_one]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos (show (0 : ℤ) - 1 + j = -1 by omega), Module.End.one_eq_id]
  · rw [if_neg hj, if_neg (show ¬((0 : ℤ) - 1 + j = -1) by omega)]

/-! ## The ordered mode composite and the block -/

/-- The **ordered product** `o_{j₀}(u₀)·o_{j₁}(u₁)⋯` of the shifted modes (order matters: `End M` is
noncommutative, and the block is the trace of the ordered product). -/
noncomputable def modeComposite (N : OrdVModule W M) {n : ℕ} (u : Fin n → 𝒱) (j : Fin n → ℤ) :
    End ℂ M :=
  (List.ofFn (fun i : Fin n => oModShift N (j i) (u i))).prod

@[simp] theorem modeComposite_zero (N : OrdVModule W M) (u : Fin 0 → 𝒱) (j : Fin 0 → ℤ) :
    modeComposite N u j = 1 := by
  rw [modeComposite]
  simp

/-- **Peel the head slot**: `o_{j₀}(a)` times the `(n−1)`-point composite. -/
theorem modeComposite_cons (N : OrdVModule W M) {n : ℕ} (a : 𝒱) (u : Fin n → 𝒱)
    (j : Fin (n + 1) → ℤ) :
    modeComposite N (Fin.cons a u) j
      = oModShift N (j 0) a * modeComposite N u (fun i => j i.succ) := by
  rw [modeComposite, modeComposite, List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- **The `n`-point chiral block on the torus** (Gannon 5.3.17a): the coefficient of
`e^{2πi j₁z₁}⋯e^{2πi jₙzₙ}` is the graded trace `tr_M(o_{j₁}(u¹)⋯o_{jₙ}(uⁿ)·q^{L₀−c/24})`. -/
noncomputable def chiralBlock (N : OrdVModule W M) {n : ℕ} (u : Fin n → 𝒱) : FormalNPoint n :=
  fun j e =>
    haveI := N.finrank (e + W.centralCharge / 24)
    LinearMap.trace ℂ _ (weightBlock N (modeComposite N u j) (e + W.centralCharge / 24))

/-- **Correctness check: the `1`-point block is the one-point function** `χ_M(τ,v)`
(Gannon 5.3.17b, "hence the name"). -/
theorem chiralBlock_one (N : OrdVModule W M) (v : 𝒱) :
    chiralBlock N ![v] (fun _ => 0) = chiralBlockOne N v := by
  funext e
  have hcomp : modeComposite N ![v] (fun _ : Fin 1 => (0 : ℤ)) = oMod N v := by
    rw [modeComposite]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, oModShift_zero]
  simp only [chiralBlock, chiralBlockOne, torusOnePoint, onePoint, hcomp]

/-- The `0`-point block is the partition function `𝒵(τ) = χ_M(τ)`. -/
theorem chiralBlock_zero (N : OrdVModule W M) (u : Fin 0 → 𝒱) (j : Fin 0 → ℤ) :
    chiralBlock N u j = torusPartition N := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [chiralBlock, modeComposite_zero, torusPartition, gradedDim, Module.End.one_eq_id,
    weightBlock_id, LinearMap.trace_id]

/-! ## Multilinearity and vacuum insertion (head slot) -/

/-- **Additivity in the head slot.** -/
theorem chiralBlock_cons_add (N : OrdVModule W M) {n : ℕ} (a b : 𝒱) (u : Fin n → 𝒱)
    (j : Fin (n + 1) → ℤ) :
    chiralBlock N (Fin.cons (a + b) u) j
      = chiralBlock N (Fin.cons a u) j + chiralBlock N (Fin.cons b u) j := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [chiralBlock, Pi.add_apply]
  rw [modeComposite_cons, modeComposite_cons, modeComposite_cons, map_add, add_mul,
    weightBlock_add, map_add]

/-- **Homogeneity in the head slot** (with additivity: `ℂ`-linearity). -/
theorem chiralBlock_cons_smul (N : OrdVModule W M) {n : ℕ} (c : ℂ) (a : 𝒱) (u : Fin n → 𝒱)
    (j : Fin (n + 1) → ℤ) :
    chiralBlock N (Fin.cons (c • a) u) j = c • chiralBlock N (Fin.cons a u) j := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [chiralBlock, Pi.smul_apply, smul_eq_mul]
  rw [modeComposite_cons, modeComposite_cons, map_smul, smul_mul_assoc, weightBlock_smul, map_smul,
    smul_eq_mul]

/-- **Vacuum insertion**: inserting `𝟙` in the (unshifted) head slot reduces the `n+1`-point block
to the `n`-point block. -/
theorem chiralBlock_cons_vacuum (N : OrdVModule W M) {n : ℕ} (u : Fin n → 𝒱) (j : Fin (n + 1) → ℤ)
    (hj : j 0 = 0) :
    chiralBlock N (Fin.cons W.vacuum u) j = chiralBlock N u (fun i => j i.succ) := by
  funext e
  simp only [chiralBlock]
  rw [modeComposite_cons, hj, oModShift_vacuum, if_pos rfl, ← Module.End.one_eq_id, one_mul]

/-! ## Multilinearity in EVERY slot

The head-slot lemmas above bootstrap the general slot by induction on the `Fin.cons` decomposition
(`Fin.cons_self_tail`, `Fin.update_cons_zero`, `Fin.cons_update`). -/

/-- **`modeComposite` is additive in every slot.** -/
theorem modeComposite_update_add (N : OrdVModule W M) :
    ∀ {n : ℕ} (u : Fin n → 𝒱) (j : Fin n → ℤ) (i : Fin n) (a b : 𝒱),
      modeComposite N (Function.update u i (a + b)) j
        = modeComposite N (Function.update u i a) j
          + modeComposite N (Function.update u i b) j := by
  intro n
  induction n with
  | zero => intro u j i; exact i.elim0
  | succ m ih =>
      intro u j i a b
      induction i using Fin.cases with
      | zero =>
          have hx : ∀ x : 𝒱, Function.update u 0 x = Fin.cons x (Fin.tail u) := by
            intro x
            conv_lhs => rw [← Fin.cons_self_tail u]
            exact Fin.update_cons_zero _ _ _
          rw [hx (a + b), hx a, hx b, modeComposite_cons, modeComposite_cons, modeComposite_cons,
            map_add, add_mul]
      | succ k =>
          have hx : ∀ x : 𝒱,
              Function.update u k.succ x = Fin.cons (u 0) (Function.update (Fin.tail u) k x) := by
            intro x
            conv_lhs => rw [← Fin.cons_self_tail u]
            exact (Fin.cons_update _ _ _ _).symm
          rw [hx (a + b), hx a, hx b, modeComposite_cons, modeComposite_cons, modeComposite_cons,
            ih (Fin.tail u) (fun l => j l.succ) k a b, mul_add]

/-- **`modeComposite` is homogeneous in every slot.** -/
theorem modeComposite_update_smul (N : OrdVModule W M) :
    ∀ {n : ℕ} (u : Fin n → 𝒱) (j : Fin n → ℤ) (i : Fin n) (c : ℂ) (a : 𝒱),
      modeComposite N (Function.update u i (c • a)) j
        = c • modeComposite N (Function.update u i a) j := by
  intro n
  induction n with
  | zero => intro u j i; exact i.elim0
  | succ m ih =>
      intro u j i c a
      induction i using Fin.cases with
      | zero =>
          have hx : ∀ x : 𝒱, Function.update u 0 x = Fin.cons x (Fin.tail u) := by
            intro x
            conv_lhs => rw [← Fin.cons_self_tail u]
            exact Fin.update_cons_zero _ _ _
          rw [hx (c • a), hx a, modeComposite_cons, modeComposite_cons, map_smul, smul_mul_assoc]
      | succ k =>
          have hx : ∀ x : 𝒱,
              Function.update u k.succ x = Fin.cons (u 0) (Function.update (Fin.tail u) k x) := by
            intro x
            conv_lhs => rw [← Fin.cons_self_tail u]
            exact (Fin.cons_update _ _ _ _).symm
          rw [hx (c • a), hx a, modeComposite_cons, modeComposite_cons,
            ih (Fin.tail u) (fun l => j l.succ) k c a, mul_smul_comm]

/-- **The chiral block is additive in EVERY slot** (Gannon 5.3.17a). -/
theorem chiralBlock_update_add (N : OrdVModule W M) {n : ℕ} (u : Fin n → 𝒱) (j : Fin n → ℤ)
    (i : Fin n) (a b : 𝒱) :
    chiralBlock N (Function.update u i (a + b)) j
      = chiralBlock N (Function.update u i a) j + chiralBlock N (Function.update u i b) j := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [chiralBlock, Pi.add_apply]
  rw [modeComposite_update_add, weightBlock_add, map_add]

/-- **The chiral block is `ℂ`-homogeneous in EVERY slot**; with `chiralBlock_update_add` this is
full multilinearity (Gannon 5.3.17a). -/
theorem chiralBlock_update_smul (N : OrdVModule W M) {n : ℕ} (u : Fin n → 𝒱) (j : Fin n → ℤ)
    (i : Fin n) (c : ℂ) (a : 𝒱) :
    chiralBlock N (Function.update u i (c • a)) j = c • chiralBlock N (Function.update u i a) j := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [chiralBlock, Pi.smul_apply, smul_eq_mul]
  rw [modeComposite_update_smul, weightBlock_smul, map_smul, smul_eq_mul]

/-! ## Residual

The remaining Gannon 5.3.17a content beyond the formal level (the analytic `zᵢ`-dependence, and the
double periodicity as *functions* rather than as Fourier indices) belongs with the deferred
`FormalQSeries → ℍ` convergence bridge.
-/

end VOA
