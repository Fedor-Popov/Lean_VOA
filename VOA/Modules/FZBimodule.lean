/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuModule
import VOA.Core.FLM
import VOA.Core.FieldCombinatorics

/-!
# The Frenkel–Zhu bimodule data `O(M)`, `a ∗ m`, `m ∗ a`, and the skew top-level identities

For a VOA `W` and a weak `W`-module `M`, Frenkel–Zhu (1992) define, for homogeneous `a ∈ W_p`:

* `a ∗ m = Res_z z⁻¹ (1+z)^p Y(a,z) m = ∑_{i ≤ p} C(p,i) a₍ᵢ₋₁₎ m`            (`fzLeft`);
* `m ∗ a = Res_z z⁻¹ (1+z)^{p−1} Y(a,z) m = ∑_{i ≤ p} C(p−1,i) a₍ᵢ₋₁₎ m`        (`fzRight`);
* `Res_z z^{−2−k} (1+z)^{p+k} Y(a,z) m = ∑_i C(p+k,i) a₍ᵢ₋₂₋ₖ₎ m`, `k ≥ 0`       (`fzRes`),

and `O(M)` is the span of the `k = 0` residues `a ∘ m`.  Here `fzO` is the span of
**all** `fzRes` (`k ≥ 0`, the library's `Pres` convention `(1+z)^{p+k}`).  By
Frenkel–Zhu's Lemma 2.1.2 (module version, *not formalized here*) this is the same
subspace as `span{a ∘ m}`; the expansion `(1+z)^{p+k} = ∑ C(k,l)(1+z)^p z^l` shows (by
induction on `k`, also not formalized) that the span is unchanged if `(1+z)^p` is used
instead of `(1+z)^{p+k}`.  In any case `span{a ∘ m} ⊆ fzO`, so the larger generating set
only makes the generation hypothesis `FZGenerated` *weaker*: generation proved with
`O(M) = span{a ∘ m}` implies `FZGenerated`.

(For `p = 0`, `fzRight` truncates `(1+z)^{−1}` at `i = 0`; since `W₀ = ℂ𝟙` and `𝟙₍ᵢ₋₁₎ = δᵢ₀`
this is the exact value.)

## Main results
* `fzLeft_sub_fzRight` — the **exact** identity `a ∗ m − m ∗ a = ∑_{i<p} C(p−1,i) a₍ᵢ₎ m`
  (no `O(M)` needed).
* `FZGenerated` — `M` is generated as an `A(W)`-bimodule by its weight-`h` space: every subspace
  containing `O(M)` and `M_h` and closed under `a ∗ ·`, `· ∗ a` is everything.
* `skew_master` — the transposed commutator computation: for **any** commutator-only
  intertwining data `A₃(r)B(n) − B(n)A₁(r) = ∑_{j<J} C(r,j) C_j(r+n−j)`,
  `∑_i (−1)^{N−i}C(N,i) B(n−i)A₁(i+s)`
  `= ∑_i (−1)^{N−i}C(N,i) A₃(i+s)B(n−i) − ∑_j C(s,j−N) C_j(n+s−j)`.
* `skew_left`, `skew_comm`, `skew_res` — the three **skew top-level identities**: if `B(n)m`
  is "top" (`B(r)m = 0` for `r > n`) and the commutator sum stops at `J = p`, then
  - `∑_{i≤p} (−1)^{p−i}C(p,i) B(n+p−i)A₁(i−1)m = A₃(p−1) B(n) m`            (left action),
  - `∑_{i<p} (−1)^{p−1−i}C(p−1,i) B(n+p−1−i)A₁(i)m = A₃(p−1)B(n)m − C_{p−1}(n)m` (commutator),
  - `∑_{i≤p+k} (−1)^{p+k−i}C(p+k,i) B(n+1+p+k−i)A₁(i−2−k)m = 0`            (`O(M)`).

  These are the Frenkel–Zhu top-level identities `o(a∗m) = o(a)o(m)`, `o(m∗a) = o(m)o(a)`,
  `o(O(M)) = 0` for the *transposed* intertwiner `m ↦ e^{zL₋₁}Y(·,−z)m`, read off at the top
  level — and they need **only the commutator formula**, not the intertwining Jacobi identity.
* `sign_coeff` — the sign bookkeeping `C(N,i)·(−1)^{c+N−i} = (−1)^c (−1)^{N−i}C(N,i)`.

## Status
`sorry`-free, no axioms beyond Lean's.  Not done (and not needed by the `KeyTopV` route, which
only uses closure of a subspace under `a ∗ ·`, `· ∗ a` for *all* `a ∈ W`): `O(W) ∗ M ⊆ O(M)`,
`M ∗ O(W) ⊆ O(M)` and the `A(W)`-bimodule structure on `M/O(M)`; these need the module
associativity formula, not the commutator formula.
-/

set_option linter.style.longLine false

namespace VOA.FZ

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## §1  The Frenkel–Zhu operations -/

/-- **Left action** `a ∗ m = ∑_{i ≤ p} C(p,i) a₍ᵢ₋₁₎ m` (for `a` of weight `p`). -/
noncomputable def fzLeft (N : WeakModule W M) (p : ℕ) (a : 𝒱) (m : M) : M :=
  ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • mode (N.YM a) ((i : ℤ) - 1) m

/-- **Right action** `m ∗ a = ∑_{i ≤ p} C(p−1,i) a₍ᵢ₋₁₎ m` (for `a` of weight `p`). -/
noncomputable def fzRight (N : WeakModule W M) (p : ℕ) (a : 𝒱) (m : M) : M :=
  ∑ i ∈ Finset.range (p + 1), cbz ((p : ℤ) - 1) (i : ℤ) • mode (N.YM a) ((i : ℤ) - 1) m

/-- **The residues** `Res_z z^{−2−k}(1+z)^{p+k} Y(a,z)m = ∑_i C(p+k,i) a₍ᵢ₋₂₋ₖ₎ m`. -/
noncomputable def fzRes (N : WeakModule W M) (p k : ℕ) (a : 𝒱) (m : M) : M :=
  ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) • mode (N.YM a) ((i : ℤ) - 2 - k) m

/-- Generators of `O(M)`: residues of homogeneous `a`. -/
def fzOgen (N : WeakModule W M) : Set M :=
  {x | ∃ (p k : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) ∧ ∃ m : M, x = fzRes N p k a m}

/-- **`O(M)`** (Frenkel–Zhu), spanned by all residues `fzRes`. -/
def fzO (N : WeakModule W M) : Submodule ℂ M := Submodule.span ℂ (fzOgen N)

theorem fzRes_mem_fzO (N : WeakModule W M) {p : ℕ} (k : ℕ) {a : 𝒱} (ha : a ∈ W.grading (p : ℤ))
    (m : M) : fzRes N p k a m ∈ fzO N :=
  Submodule.subset_span ⟨p, k, a, ha, m, rfl⟩

theorem fzLeft_add (N : WeakModule W M) (p : ℕ) (a : 𝒱) (m m' : M) :
    fzLeft N p a (m + m') = fzLeft N p a m + fzLeft N p a m' := by
  simp only [fzLeft, map_add, smul_add, Finset.sum_add_distrib]

theorem fzRight_add (N : WeakModule W M) (p : ℕ) (a : 𝒱) (m m' : M) :
    fzRight N p a (m + m') = fzRight N p a m + fzRight N p a m' := by
  simp only [fzRight, map_add, smul_add, Finset.sum_add_distrib]

/-- **The exact commutator identity** `a ∗ m − m ∗ a = ∑_{i<p} C(p−1,i) a₍ᵢ₎ m`. -/
theorem fzLeft_sub_fzRight (N : WeakModule W M) (p : ℕ) (a : 𝒱) (m : M) :
    fzLeft N p a m - fzRight N p a m
      = ∑ i ∈ Finset.range p, cbz ((p : ℤ) - 1) (i : ℤ) • mode (N.YM a) (i : ℤ) m := by
  rw [fzLeft, fzRight, ← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range (p + 1),
      cbz (p : ℤ) (i : ℤ) • mode (N.YM a) ((i : ℤ) - 1) m
        - cbz ((p : ℤ) - 1) (i : ℤ) • mode (N.YM a) ((i : ℤ) - 1) m
      = cbz ((p : ℤ) - 1) ((i : ℤ) - 1) • mode (N.YM a) ((i : ℤ) - 1) m := by
    intro i _
    rw [← sub_smul, cbz_pascal (p : ℤ) (i : ℤ)]
    congr 1
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_sub, cbz_apply_neg _ (show (-1 : ℤ) < 0 by norm_num), zero_smul,
    add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [show (i : ℤ) + 1 - 1 = i by ring]

/-- **Bimodule generation** of `M` by its weight-`h` space (the hypothesis of the
Frenkel–Zhu reduction).  Every subspace containing `O(M)` and `M_h`, closed under `a ∗ ·` and
`· ∗ a` for homogeneous `a`, is everything. -/
def FZGenerated (N : OrdVModule W M) (h : ℂ) : Prop :=
  ∀ S : Submodule ℂ M, fzO N.toWeakModule ≤ S → N.weight h ≤ S →
    (∀ (p : ℕ) (a : 𝒱), a ∈ W.grading (p : ℤ) → ∀ m ∈ S,
      fzLeft N.toWeakModule p a m ∈ S ∧ fzRight N.toWeakModule p a m ∈ S) → S = ⊤

/-- `o(a) = 0` on a lowest-weight space for `a ∈ O(W)` (from `O_le_ker_rhoLW`). -/
theorem oMod_eq_zero_of_mem_O {M' : Type u} [AddCommGroup M'] [Module ℂ M'] (N : OrdVModule W M')
    {h : ℂ} (hcw : IsLowestWeight N h) {a : 𝒱} (ha : a ∈ O W) {x : M'} (hx : x ∈ N.weight h) :
    oMod N a x = 0 := by
  have h0 := O_le_ker_rhoLW N hcw ha
  rw [LinearMap.mem_ker] at h0
  have := congrArg (fun f => ((f ⟨x, hx⟩ : N.weight h) : M')) h0
  simp only at this
  rw [rhoLW_apply_coe] at this
  exact this

/-! ## §2  Graded extension of a family of maps -/

section GradedExt

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Extend a family `f k : 𝒱 → X` (meant to be applied to `𝒱ₖ`) linearly over the grading. -/
noncomputable def gradedExt (W : VertexOperatorAlgebra 𝒱) (f : ℤ → 𝒱 →ₗ[ℂ] X) : 𝒱 →ₗ[ℂ] X :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (fun k => f k ∘ₗ (W.grading k).subtype)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem gradedExt_of_mem (W : VertexOperatorAlgebra 𝒱) (f : ℤ → 𝒱 →ₗ[ℂ] X) {k : ℤ} {v : 𝒱}
    (hv : v ∈ W.grading k) : gradedExt W f v = f k v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  change (DFinsupp.lsum ℂ (fun k => f k ∘ₗ (W.grading k).subtype))
    (DirectSum.decompose W.grading v) = _
  rw [DirectSum.decompose_of_mem W.grading hv]
  exact DFinsupp.lsum_single ℂ (fun k => f k ∘ₗ (W.grading k).subtype) k ⟨v, hv⟩

end GradedExt

/-! ## §3  Combinatorics -/

/-- `∑_i (−1)^{N−i} C(N,i) C(s+i, j) = C(s, j − N)` (finite difference, from `cbz_fd`). -/
theorem asgn_cbz_sum (N : ℕ) (s : ℤ) (j : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (asgn N i : ℂ) * gBinom ((i : ℤ) + s) j = cbz s ((j : ℤ) - N) := by
  rw [← cbz_fd N s (j : ℤ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, cbz_apply_nonneg _ (by positivity), Int.toNat_natCast, add_comm]

theorem negOnePow_add_fz (a b : ℤ) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  rw [negOnePow, negOnePow, negOnePow]
  by_cases ha : Even a <;> by_cases hb : Even b
  · rw [if_pos ha, if_pos hb, if_pos (ha.add hb)]; ring
  · rw [if_pos ha, if_neg hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_pos hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_neg hb, if_pos (by simp [Int.even_add, ha, hb])]; ring

/-- Sign bookkeeping: `C(N,i) (−1)^{c+N−i} = (−1)^c · (−1)^{N−i} C(N,i)` for `i ≤ N`. -/
theorem sign_coeff (N : ℕ) {i : ℕ} (hi : i ≤ N) (c : ℤ) :
    cbz (N : ℤ) (i : ℤ) * negOnePow (c + N - i) = negOnePow c * (asgn N i : ℂ) := by
  rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast,
    FieldCombinatorics.gBinom_natCast_eq_choose hi,
    show c + (N : ℤ) - i = c + ((N - i : ℕ) : ℤ) by push_cast [hi]; ring, negOnePow_add_fz,
    negOnePow_natCast, asgn]
  push_cast
  ring

/-! ## §4  The transposed commutator computation -/

section Skew

variable {M₁ M₃ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₃] [Module ℂ M₃]
variable (A₁ : ℤ → M₁ →ₗ[ℂ] M₁) (A₃ : ℤ → M₃ →ₗ[ℂ] M₃) (B : ℤ → M₁ →ₗ[ℂ] M₃)
  (C : ℕ → ℤ → M₁ →ₗ[ℂ] M₃) (J : ℕ)

/-- The commutator formula of commutator-only intertwining data. -/
def CommData : Prop :=
  ∀ (r n : ℤ) (m : M₁), A₃ r (B n m) - B n (A₁ r m)
    = ∑ j ∈ Finset.range J, gBinom r j • C j (r + n - j) m

variable {A₁ A₃ B C J}

/-- **The transposed commutator computation.** -/
theorem skew_master (hc : CommData A₁ A₃ B C J) (N : ℕ) (s n : ℤ) (m : M₁) :
    ∑ i ∈ Finset.range (N + 1), (asgn N i : ℂ) • B (n - i) (A₁ ((i : ℤ) + s) m)
      = ∑ i ∈ Finset.range (N + 1), (asgn N i : ℂ) • A₃ ((i : ℤ) + s) (B (n - i) m)
        - ∑ j ∈ Finset.range J, cbz s ((j : ℤ) - N) • C j (n + s - j) m := by
  have h1 : ∀ i ∈ Finset.range (N + 1), (asgn N i : ℂ) • B (n - i) (A₁ ((i : ℤ) + s) m)
      = (asgn N i : ℂ) • A₃ ((i : ℤ) + s) (B (n - i) m)
        - ∑ j ∈ Finset.range J, ((asgn N i : ℂ) * gBinom ((i : ℤ) + s) j) • C j (n + s - j) m := by
    intro i _
    have e := hc ((i : ℤ) + s) (n - i) m
    rw [show B (n - i) (A₁ ((i : ℤ) + s) m) = A₃ ((i : ℤ) + s) (B (n - i) m)
      - ∑ j ∈ Finset.range J, gBinom ((i : ℤ) + s) j • C j ((i : ℤ) + s + (n - i) - j) m by
        rw [← e]; abel]
    rw [smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, show (i : ℤ) + s + (n - i) - j = n + s - j by ring]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, asgn_cbz_sum]

/-- **Skew top-level identity, left action** (`o(a ∗ m) = o(a) o(m)` transposed). -/
theorem skew_left (p : ℕ) (hc : CommData A₁ A₃ B C p) (n : ℤ) (m : M₁)
    (hlow : ∀ r : ℤ, n < r → B r m = 0) :
    ∑ i ∈ Finset.range (p + 1), (asgn p i : ℂ) • B (n + p - i) (A₁ ((i : ℤ) - 1) m)
      = A₃ ((p : ℤ) - 1) (B n m) := by
  have h := skew_master hc p (-1) (n + p) m
  simp only [← sub_eq_add_neg] at h
  rw [h]
  rw [Finset.sum_eq_zero (s := Finset.range p) fun j hj => by
    rw [cbz_apply_neg _ (by simp at hj; omega), zero_smul], sub_zero]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
    rw [hlow _ (by simp at hi; omega), map_zero, smul_zero], zero_add]
  simp [asgn]

/-- **Skew top-level identity, commutator** (`o(m ∗ a) = o(m) o(a)` transposed, via
`fzLeft_sub_fzRight`). -/
theorem skew_comm (p : ℕ) (hp : 1 ≤ p) (hc : CommData A₁ A₃ B C p) (n : ℤ) (m : M₁)
    (hlow : ∀ r : ℤ, n < r → B r m = 0) :
    ∑ i ∈ Finset.range p, (asgn (p - 1) i : ℂ) • B (n + (p - 1 : ℕ) - i) (A₁ (i : ℤ) m)
      = A₃ ((p : ℤ) - 1) (B n m) - C (p - 1) n m := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h := skew_master hc q 0 (n + q) m
  simp only [add_zero, Nat.add_sub_cancel] at h ⊢
  have hC : ∑ x ∈ Finset.range (q + 1), cbz 0 ((x : ℤ) - q) • C x (n + q - x) m = C q n m := by
    rw [Finset.sum_eq_single q (fun j hj hjq => by
      rw [cbz_apply_neg _ (by simp at hj; omega), zero_smul]) (by simp)]
    simp
  have hA : ∑ x ∈ Finset.range (q + 1), (asgn q x : ℂ) • A₃ (x : ℤ) (B (n + q - x) m)
      = A₃ (q : ℤ) (B n m) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [hlow _ (by simp at hi; omega), map_zero, smul_zero], zero_add]
    simp [asgn]
  rw [h, hC, hA]
  push_cast
  ring_nf

/-- **Skew top-level identity, `O(M)`** (`o(O(M)) = 0` transposed). -/
theorem skew_res (p k : ℕ) (hc : CommData A₁ A₃ B C p) (n : ℤ) (m : M₁)
    (hlow : ∀ r : ℤ, n < r → B r m = 0) :
    ∑ i ∈ Finset.range (p + k + 1), (asgn (p + k) i : ℂ)
      • B (n + 1 + (p + k : ℕ) - i) (A₁ ((i : ℤ) - 2 - k) m) = 0 := by
  have h := skew_master hc (p + k) (-2 - k) (n + 1 + (p + k : ℕ)) m
  simp only [show ∀ i : ℕ, (i : ℤ) + (-2 - (k : ℤ)) = (i : ℤ) - 2 - k from fun i => by ring] at h
  rw [h]
  rw [Finset.sum_eq_zero (s := Finset.range p) fun j hj => by
    rw [cbz_apply_neg _ (by simp at hj; push_cast; omega), zero_smul], sub_zero]
  exact Finset.sum_eq_zero fun i hi => by
    rw [hlow _ (by simp at hi; push_cast; omega), map_zero, smul_zero]

end Skew

end VOA.FZ
