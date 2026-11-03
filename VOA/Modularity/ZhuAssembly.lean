/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GradedTrace
import VOA.Modularity.Schwarzian

/-!
# Assembling Zhu's recursion: the iterate formula  (Zhu Prop. 4.3.2, the `a[−1]` case)

`GradedTrace` evaluates the graded trace of a **compensated mode pair** `a₍ᵢ₎·v₍kₐ+ℓ−i−2₎` in all
three regimes.  `onePoint_vSqZ_expand` reduces the left-hand side of Zhu's recursion to a `Σᶠ` of
one-point functions `𝒵_M(a₍ᵢ₎v)`.  The missing link between them is the identity that turns a
one-point function of an **iterate** `a₍ᵢ₎v` into traces of **products of modes** — and that is the
`m = 0` case of the module Jacobi identity.

## The two specialisations of Jacobi

`WeakModule.jacobi` carries three integer parameters `ℓ, m, n`:

  `Σᶠ_i (−1)^i C(ℓ,i)·[ u₍ℓ₊ₘ₋ᵢ₎v₍ₙ₊ᵢ₎x − (−1)^ℓ v₍ℓ₊ₙ₋ᵢ₎u₍ₘ₊ᵢ₎x ] = Σᶠ_i C(m,i)·(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`

Both sides collapse when the corresponding binomial degenerates (`C(0,i) = δ_{i,0}`):

* **`ℓ = 0`** collapses the **left**, leaving the *commutator* formula — that is `mode_commutator`,
  which gave `[o(a), o(v)] = o(a[0]v)` and hence `zhuVanishing_holds`.
* **`m = 0`** collapses the **right**, leaving the *iterate* formula `mode_iterate` proved here.

The two are mirror images, and the recursion needs the second.

## Why the iterate formula is exactly the right tool

Apply it with `ℓ = i`, `n = kₐ + ℓ_v − i − 2`, so that its left-hand side `(a₍ᵢ₎v)₍ₙ₎` is precisely
the **zero mode** `o(a₍ᵢ₎v)` (because `a₍ᵢ₎v ∈ 𝒱_{kₐ+ℓ_v−i−1}`).  Then *every* term on the right
is a **compensated pair**, i.e. exactly the shape `GradedTrace` can evaluate:

* first family `a₍ᵢ₋ⱼ₎·v₍ₙ₊ⱼ₎`: writing `p = i − j`, the second index is `n + j = kₐ+ℓ_v−p−2`, so
  the pair is `a₍ₚ₎·v₍kₐ+ℓ_v−p−2₎` — the compensated pair at `p` on the nose;
* second family `v₍ᵢ₊ₙ₋ⱼ₎·a₍ⱼ₎`: the first index is `i + n − j = kₐ+ℓ_v−j−2`, so the pair is the
  **reversed** compensated pair at `j`, and `gradedTraceOp_comm_shift` turns it back around at the
  cost of one `q`-degree shift.

So the one-point function of an iterate is a (finite) combination of trichotomy-evaluable traces.
That is the content of `oMod_smul_eq_iterate` / `onePoint_smul_eq_pairs` below.

## Status
Proved, axiom-clean and `pbw`-free: the iterate formula; the reduction of `𝒵_M(a₍ᵢ₎v)` to
compensated-pair traces **for every mode index** (`onePoint_smul_eq_pairs_finset` — the `0 ≤ i`
restriction is *removed*, via uniform truncation on the finite-dimensional weight spaces); and the
identification of the non-tail summand — only `i = −1` contributes `tr o(a)o(v)q^{L₀−c/24}`, with
coefficient exactly `1` (`iterate_twoPoint_cancel`, `twoPoint_total_coeff_eq_one`).  The named
residual is the combinatorial collection of the resulting `(p, j)` double sums, for which the
divisor-regrouping engine is banked (`finsum_pow_mul_eq_lambert`).

## References
* Zhu, J. AMS 9 (1996), Prop. 4.3.2; Gannon §5.3.5; Frenkel–Huang–Lepowsky, the Jacobi identity.
-/

namespace VOA

open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The iterate formula — the `m = 0` Jacobi -/

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **The module iterate formula**:

  `(u₍ℓ₎v)₍ₙ₎ x = Σᶠ_i (−1)^i C(ℓ,i)·[ u₍ℓ₋ᵢ₎v₍ₙ₊ᵢ₎x − (−1)^ℓ v₍ℓ₊ₙ₋ᵢ₎u₍ᵢ₎x ]`.

This is the `m = 0` case of the module Jacobi identity: `C(0,i) = δ_{i,0}` collapses the *right*
`Σᶠ` to the single term `(u₍ℓ₎v)₍ₙ₎`.  It is the exact mirror of `mode_commutator`, which is the
`ℓ = 0` case collapsing the *left*-hand side to a commutator. -/
theorem mode_iterate (A : WeakModule W M) (u v : 𝒱) (x : M) (l n : ℤ) :
    mode (A.YM (W.smul u l v)) n x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz l i) •
          (mode (A.YM u) (l - i) (mode (A.YM v) (n + i) x)
            - negOnePow l • mode (A.YM v) (l + n - i) (mode (A.YM u) i x)) := by
  have hjac := A.jacobi u v x l 0 n
  have hrhs : (∑ᶠ i : ℤ, cbz 0 i • mode (A.YM (W.smul u (l + i) v)) (0 + n - i) x)
      = mode (A.YM (W.smul u l v)) n x := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, zero_smul])]
    rw [cbz_zero_left, if_pos rfl, one_smul, add_zero, zero_add, sub_zero]
  rw [← hrhs, ← hjac]
  exact finsum_congr (fun i => by rw [add_zero, zero_add])

end

/-! ## Finiteness of the iterate sum -/

/-- `C(i,j) = 0` for `0 ≤ i < j`: at a **natural** upper index the generalized binomial is the
ordinary one, which vanishes past the top row.  (For `i < 0` this fails — see
`cbz_neg_one_ne_zero`.) -/
theorem cbz_eq_zero_of_lt {i j : ℤ} (hi : 0 ≤ i) (hij : i < j) : cbz i j = 0 := by
  have hj : (0 : ℤ) ≤ j := by omega
  rw [cbz_apply_nonneg _ hj]
  obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega : i' < j.toNat)]
  norm_num

/-- **The iterate sum is finite for `0 ≤ i`**, at operator level: the weights `(−1)^j C(i,j)`
are supported in `0 ≤ j ≤ i`.  This discharges the finiteness hypothesis of
`onePoint_smul_eq_pairs` whenever the mode index is nonnegative. -/
theorem iterate_support_finite {i : ℤ} (hi : 0 ≤ i) {X : Type*} [AddCommGroup X] [Module ℂ X]
    (F : ℤ → X) :
    (Function.support fun j : ℤ => (negOnePow j * cbz i j) • F j).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) i) (fun j hj => ?_)
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact hj (by rw [cbz_apply_neg _ hc, mul_zero, zero_smul])
  · by_contra hc
    push_neg at hc
    exact hj (by rw [cbz_eq_zero_of_lt hi hc, mul_zero, zero_smul])

/-- ⚠ **The exceptional index.**  `C(−1,j) = (−1)^j` for every `j ≥ 0`, so at `i = −1` the iterate
weights **never** vanish and the operator-level sum of `mode_iterate` has infinite support.

This is not a defect of the statement — `mode_iterate` itself is pointwise and unconditional, and
for each fixed `x` the sum is finite by the field axiom.  It matters because `i = −1` is precisely
the **leading** index of the recursion's left-hand side: `c(k,−1,−1) = 1`, so `a[−1]v` genuinely
contains the term `a₍₋₁₎v`.  Passing from the pointwise identity to a `q`-degree identity there
therefore needs degree-wise finiteness rather than operator-wise, which is the remaining analytic
bookkeeping in the assembly (see the residual). -/
theorem cbz_neg_one {j : ℤ} (hj : 0 ≤ j) : cbz (-1) j = (-1 : ℂ) ^ j.toNat := by
  have hne : ((j.toNat.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos j.toNat).ne'
  rw [cbz_apply_nonneg _ hj, show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 from by norm_num,
    VertexOperatorAlgebra.gBinom_negsucc 0 j.toNat, Nat.factorial_zero, zero_add]
  push_cast
  field_simp

/-- Hence the iterate weights at `i = −1` never vanish. -/
theorem cbz_neg_one_ne_zero {j : ℤ} (hj : 0 ≤ j) : cbz (-1) j ≠ 0 := by
  rw [cbz_neg_one hj]
  exact pow_ne_zero _ (by norm_num)

/-! ## Where the two-point term comes from

In the iterate expansion of `o(a₍ᵢ₎v)` the compensated pair at `p = kₐ − 1` is the **zero-mode
pair** `o(a)·o(v)`, whose graded trace is Zhu's two-point term `torusTwoPoint`
(`gradedTraceOp_mode_pair_eq_torusTwoPoint`).  It is reached twice: from the first family at
`j = i − kₐ + 1` (where `i − j = kₐ − 1`) and from the second at `j = kₐ − 1`.  Since the second
family's shift there is `s_{kₐ−1} = 0`, both land in the **same** `q`-degree, so their coefficients
simply add — and the theorem below says that for `i ≥ 0` they **cancel**.

The consequence is sharp: **every `i ≥ 0` contributes no two-point term at all**, so the entire
`tr o(a)o(v)q^{L₀−c/24}` summand of Zhu's recursion comes from the single index `i = −1`, where the
iterate weights are `(−1)^j C(−1,j) = 1` (`cbz_neg_one`) and the square-bracket weight is
`c(k,−1,−1) = 1` (`sqBracketCoeffZ_neg_one_diag`).  That is exactly the coefficient `1` with which
`torusTwoPoint` appears in `ZhuRecursionAt`. -/

/-- **The two-point contributions cancel for every `i ≥ 0`.**

The two iterate weights reaching the zero-mode pair `p = kₐ − 1` are equal:
`(−1)^{i−kₐ+1}·C(i, i−kₐ+1)` and `(−1)^i·(−1)^{kₐ−1}·C(i, kₐ−1)`.  The signs agree because the
exponents differ by `2(kₐ−1)`, and the binomials agree by symmetry `C(i,r) = C(i,i−r)`.  Since they
enter the expansion with opposite signs, they cancel. -/
theorem iterate_twoPoint_cancel {i ka : ℤ} (hi : 0 ≤ i) (h1 : 1 ≤ ka) (hle : ka - 1 ≤ i) :
    negOnePow (i - ka + 1) * cbz i (i - ka + 1)
      = negOnePow i * (negOnePow (ka - 1) * cbz i (ka - 1)) := by
  have hsign : negOnePow (i - ka + 1) = negOnePow i * negOnePow (ka - 1) := by
    have hev : negOnePow (2 * (ka - 1)) = 1 := by
      rw [negOnePow, if_pos ⟨ka - 1, by ring⟩]
    have h3 := negOnePow_add (i - ka + 1) (2 * (ka - 1))
    rw [hev, mul_one, show i - ka + 1 + 2 * (ka - 1) = i + (ka - 1) from by ring,
      negOnePow_add] at h3
    exact h3.symm
  have hbin : cbz i (i - ka + 1) = cbz i (ka - 1) := by
    obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [cbz_apply_nonneg _ (by omega), cbz_apply_nonneg _ (by omega),
      gBinom_natCast, gBinom_natCast,
      show ((i' : ℤ) - ka + 1).toNat = i' - (ka - 1).toNat from by omega,
      Nat.choose_symm (by omega : (ka - 1).toNat ≤ i')]
  rw [hsign, hbin]
  ring

@[simp] theorem negOnePow_neg_one : negOnePow (-1) = -1 := by
  rw [negOnePow, if_neg (by decide)]

/-- **At `i = −1` every iterate weight is `1`**: `(−1)^j·C(−1,j) = 1` for `j ≥ 0`, since
`C(−1,j) = (−1)^j` (`cbz_neg_one`).  So the `i = −1` iterate is the plain normal-ordered sum, with
no signs and no binomials — which is why it, alone, produces the two-point term cleanly. -/
theorem iterate_weight_neg_one {j : ℤ} (hj : 0 ≤ j) : negOnePow j * cbz (-1) j = 1 := by
  obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rw [cbz_neg_one (by omega), negOnePow_natCast, Int.toNat_natCast, ← pow_add,
    show j' + j' = 2 * j' from by ring, pow_mul, neg_one_sq, one_pow]

/-- **The two-point term enters Zhu's recursion with coefficient exactly `1`.**

Putting the pieces together at the one index that contributes it, `i = −1`:

* the square-bracket weight is `c(k,−1,−1) = 1` (`sqBracketCoeffZ_neg_one_diag`);
* the iterate weight at `j = kₐ−1` is `(−1)^{kₐ−1}·C(−1,kₐ−1) = 1` (`iterate_weight_neg_one`);
* the second family carries the extra factor `−(−1)^i = −(−1)^{−1} = +1`.

Their product is `1`.  Together with `iterate_twoPoint_cancel` (no `i ≥ 0` contributes any two-point
term) this **pins the non-tail summand of `ZhuRecursionAt`**: it is `torusTwoPoint N a v`, with
coefficient one, and nothing else. -/
theorem twoPoint_total_coeff_eq_one (k : ℕ) {ka : ℤ} (h1 : 1 ≤ ka) :
    sqBracketCoeffZ k (-1) (-1) *
        (-negOnePow (-1) * (negOnePow (ka - 1) * cbz (-1) (ka - 1))) = 1 := by
  rw [sqBracketCoeffZ_neg_one_diag, iterate_weight_neg_one (by omega), negOnePow_neg_one]
  ring

/-! ## The zero mode of an iterate, as compensated pairs -/

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The zero mode of `a₍ᵢ₎v` as a sum of compensated mode pairs.**  For homogeneous
`a ∈ 𝒱_{kₐ}`, `v ∈ 𝒱_ℓ`:

  `o(a₍ᵢ₎v) x = Σᶠ_j (−1)^j C(i,j)·[ a₍ᵢ₋ⱼ₎v₍kₐ+ℓ−(i−j)−2₎x − (−1)^i v₍kₐ+ℓ−j−2₎a₍ⱼ₎x ]`.

Every term is a compensated pair (the first family at `p = i − j`, the second the reversal at `j`),
so `GradedTrace`'s trichotomy evaluates each of their graded traces.  This is the bridge from the
recursion's left-hand side to the machinery. -/
theorem oMod_smul_eq_iterate (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (x : M) :
    oMod N (W.smul a i v) x
      = ∑ᶠ j : ℤ, (negOnePow j * cbz i j) •
          (mode (N.YM a) (i - j) (mode (N.YM v) (ka + l - (i - j) - 2) x)
            - negOnePow i • mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) := by
  rw [oMod_of_mem_grading N (W.smul_mem_grading ha hv i),
    show ka + l - i - 1 - 1 = ka + l - i - 2 from by omega,
    mode_iterate N.toWeakModule a v x i (ka + l - i - 2)]
  refine finsum_congr (fun j => ?_)
  rw [show ka + l - i - 2 + j = ka + l - (i - j) - 2 from by omega,
    show i + (ka + l - i - 2) - j = ka + l - j - 2 from by omega]

/-- The one-point function of an iterate, as a combination of compensated-pair traces.
`gradedTraceAt` turns the operator identity `oMod_smul_eq_iterate` into a `q`-degree identity. -/
theorem onePoint_smul_eq_pairs (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (e : ℂ)
    (hfin : (Function.support fun j : ℤ => (negOnePow j * cbz i j) •
      ((mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)
        - negOnePow i • (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) :
          Module.End ℂ M))).Finite) :
    onePoint N (W.smul a i v) e
      = ∑ᶠ j : ℤ, (negOnePow j * cbz i j) *
          (gradedTraceOp N (mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)) e
            - negOnePow i *
              gradedTraceOp N (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) e) := by
  have hop : oMod N (W.smul a i v)
      = ∑ᶠ j : ℤ, (negOnePow j * cbz i j) •
          ((mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)
            - negOnePow i • (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) :
              Module.End ℂ M)) := by
    refine LinearMap.ext (fun x => ?_)
    rw [oMod_smul_eq_iterate N ha hv i x]
    exact (map_finsum (LinearMap.applyₗ x) hfin).symm
  rw [← gradedTraceOp_oMod, hop]
  have h := map_finsum (gradedTraceAt N e) hfin
  simpa only [gradedTraceAt_apply, map_smul, map_sub, smul_eq_mul, gradedTraceOp_smul,
    Pi.smul_apply] using h

/-! ## Degree-wise finiteness: truncation is **uniform** on a weight space

The obstruction recorded at `cbz_neg_one_ne_zero` is that at `i = −1` the iterate sum has infinite
support *at operator level*.  It does **not** have infinite support at any fixed `q`-degree, and the
reason is a `OrdVModule` axiom that has not been used for this purpose yet: every weight space is
**finite-dimensional** (`OrdVModule.finrank`).  The field axiom truncates each mode pointwise; on a
finite-dimensional space one may take the maximum over a basis and truncate **uniformly**.

That is what the next two lemmas do, and it is exactly the degree-wise finiteness the assembly needs
in order to drop the `0 ≤ i` hypothesis. -/

/-- **Uniform truncation on a weight space**: for each `u` and each `α` there is a single `N₀`
with `u₍ₘ₎ x = 0` for **all** `m ≥ N₀` and **all** `x ∈ M_α` simultaneously.

Pointwise this is the field axiom (`WeakModule.truncation`); the uniformity comes from
`OrdVModule.finrank` — take the maximum of the pointwise bounds over a basis of `M_α` and extend by
linearity. -/
theorem mode_eventually_zero_on_weight (N : OrdVModule W M) (u : 𝒱) (α : ℂ) :
    ∃ N₀ : ℤ, ∀ m : ℤ, N₀ ≤ m → ∀ x ∈ N.weight α, mode (N.YM u) m x = 0 := by
  haveI := N.finrank α
  set b := Module.finBasis ℂ (N.weight α) with hb
  obtain ⟨N₀, hN₀⟩ := Finite.exists_le
    (fun i : Fin (Module.finrank ℂ (N.weight α)) =>
      (N.truncation u ((b i : N.weight α) : M)).choose)
  refine ⟨N₀, fun m hm x hx => ?_⟩
  have hxy : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : N.weight α) : M) := by
    have h := congrArg (N.weight α).subtype (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at h
    simp only [map_smul] at h
    exact h.symm
  rw [hxy, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul, (N.truncation u ((b i : N.weight α) : M)).choose_spec m (le_trans (hN₀ i) hm),
    smul_zero]

/-- **A product whose right factor is a high mode has vanishing graded trace at a fixed
degree.**  Combined with `mode_eventually_zero_on_weight`, this is the degree-wise finiteness that
replaces the (false at `i = −1`) operator-level finiteness. -/
theorem gradedTraceOp_mul_mode_eventually_zero (N : OrdVModule W M) (A : Module.End ℂ M) (u : 𝒱)
    (e : ℂ) : ∃ N₀ : ℤ, ∀ m : ℤ, N₀ ≤ m → gradedTraceOp N (A * mode (N.YM u) m) e = 0 := by
  obtain ⟨N₀, hN₀⟩ := mode_eventually_zero_on_weight N u (e + W.centralCharge / 24)
  refine ⟨N₀, fun m hm => ?_⟩
  haveI := N.finrank (e + W.centralCharge / 24)
  have hblk : weightBlock N (A * mode (N.YM u) m) (e + W.centralCharge / 24) = 0 := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal _) (A (mode (N.YM u) m (y : M))) : M) = _
    rw [hN₀ m hm (y : M) y.2, map_zero, map_zero]
    simp
  change LinearMap.trace ℂ _
    (weightBlock N (A * mode (N.YM u) m) (e + W.centralCharge / 24)) = 0
  rw [hblk, map_zero]

/-- **The iterate expansion becomes a genuine `Finset` sum on each weight space** — for
**every** `i`, with no sign restriction.

The uniform truncation bounds both families at once: for large `j` the first family's inner mode
`v₍kₐ+ℓ−i+j−2₎` annihilates `M_α`, and the second family's inner mode `a₍ⱼ₎` does; below `j = 0` the
weights `C(i,j)` vanish.  So the support sits in `[0, J]`. -/
theorem oMod_smul_eq_iterate_finset (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (α : ℂ) :
    ∃ J : ℤ, ∀ x ∈ N.weight α,
      oMod N (W.smul a i v) x
        = ∑ j ∈ Finset.Icc (0 : ℤ) J, (negOnePow j * cbz i j) •
            (mode (N.YM a) (i - j) (mode (N.YM v) (ka + l - (i - j) - 2) x)
              - negOnePow i • mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) := by
  obtain ⟨Nv, hNv⟩ := mode_eventually_zero_on_weight N v α
  obtain ⟨Na, hNa⟩ := mode_eventually_zero_on_weight N a α
  refine ⟨max (Nv - ka - l + i + 2) Na, fun x hx => ?_⟩
  rw [oMod_smul_eq_iterate N ha hv i x]
  refine finsum_eq_sum_of_support_subset _ (fun j hj => ?_)
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Finset.coe_Icc, Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    exact hj (by rw [cbz_apply_neg _ hc, mul_zero, zero_smul])
  · by_contra hc
    push_neg at hc
    refine hj ?_
    rw [hNv (ka + l - (i - j) - 2) (by omega) x hx, map_zero,
      hNa j (by omega) x hx, map_zero, smul_zero, sub_zero, smul_zero]

/-- **The iterate reduction at a fixed `q`-degree, for EVERY mode index `i`.**

This is `onePoint_smul_eq_pairs_of_nonneg` with the `0 ≤ i` hypothesis **removed** — which matters
because `iterate_twoPoint_cancel` shows the excluded index `i = −1` is precisely the one carrying
Zhu's two-point term.  Degree-wise finiteness (`oMod_smul_eq_iterate_finset`) replaces the
operator-level finiteness that fails there (`cbz_neg_one_ne_zero`). -/
theorem onePoint_smul_eq_pairs_finset (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (i : ℤ) (e : ℂ) :
    ∃ J : ℤ, onePoint N (W.smul a i v) e
      = ∑ j ∈ Finset.Icc (0 : ℤ) J, (negOnePow j * cbz i j) *
          (gradedTraceOp N (mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)) e
            - negOnePow i *
              gradedTraceOp N (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) e) := by
  obtain ⟨J, hJ⟩ := oMod_smul_eq_iterate_finset N ha hv i (e + W.centralCharge / 24)
  refine ⟨J, ?_⟩
  set Op : Module.End ℂ M :=
    ∑ j ∈ Finset.Icc (0 : ℤ) J, (negOnePow j * cbz i j) •
      ((mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)
        - negOnePow i • (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) :
          Module.End ℂ M)) with hOp
  have hagree : ∀ x ∈ N.weight (e + W.centralCharge / 24), oMod N (W.smul a i v) x = Op x := by
    intro x hx
    rw [hJ x hx, hOp, LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => rfl)
  have hblk : weightBlock N (oMod N (W.smul a i v)) (e + W.centralCharge / 24)
      = weightBlock N Op (e + W.centralCharge / 24) := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal _) (oMod N (W.smul a i v) (y : M)) : M)
      = ((internalProjTo N.isInternal _) (Op (y : M)) : M)
    rw [hagree (y : M) y.2]
  have hlhs : onePoint N (W.smul a i v) e = gradedTraceOp N Op e := by
    haveI := N.finrank (e + W.centralCharge / 24)
    change LinearMap.trace ℂ _
      (weightBlock N (oMod N (W.smul a i v)) (e + W.centralCharge / 24)) = _
    rw [hblk]
    rfl
  rw [hlhs, hOp, ← gradedTraceAt_apply, map_sum]
  exact Finset.sum_congr rfl (fun j _ => by
    simp only [gradedTraceAt_apply, map_smul, map_sub, smul_eq_mul, gradedTraceOp_smul,
      Pi.smul_apply, gradedTraceOp_sub, Pi.sub_apply])

/-- The reversed pair, turned around by `q`-graded cyclicity: `𝒯(v₍kₐ+ℓ−j−2₎·a₍ⱼ₎)(e)` is the
compensated pair's trace one shift up.  This is what makes the *second* iterate family evaluable by
the same trichotomy as the first. -/
theorem gradedTraceOp_reversed_pair (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) (j : ℤ) (e : ℂ) :
    gradedTraceOp N (mode (N.YM v) (ka + l - j - 2) * mode (N.YM a) j) e
      = gradedTraceOp N (mode (N.YM a) j * mode (N.YM v) (ka + l - j - 2))
          (e + ((ka : ℂ) - (j : ℂ) - 1)) := by
  set s : ℂ := (ka : ℂ) - (j : ℂ) - 1 with hs
  have hB : WeightShift N (mode (N.YM a) j) s := weightShift_mode N ha j
  have hA : WeightShift N (mode (N.YM v) (ka + l - j - 2)) (-s) := by
    have h := weightShift_mode N hv (ka + l - j - 2)
    rwa [show ((l : ℂ) - ((ka + l - j - 2 : ℤ) : ℂ) - 1) = -s from by rw [hs]; push_cast; ring] at h
  exact gradedTraceOp_comm_shift N _ _ s hA hB e

/-- **The iterate reduction with its finiteness hypothesis discharged**, for `0 ≤ i`, and with
the second family already turned around by cyclicity (`gradedTraceOp_reversed_pair`).  Every trace
on the right is then a **compensated pair in the standard orientation** `a₍ₚ₎·v₍kₐ+ℓ−p−2₎`, i.e.
exactly what the `GradedTrace` trichotomy evaluates:

  `𝒵_M(a₍ᵢ₎v)(e) = Σᶠ_j (−1)^j C(i,j)·[ 𝒯(a₍ᵢ₋ⱼ₎v₍…₎)(e) − (−1)^i·𝒯(a₍ⱼ₎v₍…₎)(e + s_j) ]`,
  `s_j = kₐ − j − 1`.

This is the last structural step before the purely combinatorial collection. -/
theorem onePoint_smul_eq_pairs_of_nonneg (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l) {i : ℤ} (hi : 0 ≤ i) (e : ℂ) :
    onePoint N (W.smul a i v) e
      = ∑ᶠ j : ℤ, (negOnePow j * cbz i j) *
          (gradedTraceOp N (mode (N.YM a) (i - j) * mode (N.YM v) (ka + l - (i - j) - 2)) e
            - negOnePow i *
              gradedTraceOp N (mode (N.YM a) j * mode (N.YM v) (ka + l - j - 2))
                (e + ((ka : ℂ) - (j : ℂ) - 1))) := by
  rw [onePoint_smul_eq_pairs N ha hv i e (iterate_support_finite hi _)]
  exact finsum_congr (fun j => by rw [gradedTraceOp_reversed_pair N ha hv j e])

end

/-! ## Why the weight matching produces Bernoulli numbers

The one remaining step of the recursion is the **weight matching**: the `c(k,−1,i)` of the
expansion, the `(−1)^j C(i,j)` of the iterate and the `C(i,p)` of the compensating commutator must
combine into the coefficients of `zhuG`.  The reason those turn out to be `−B_{2m}/(2m)!` is not a
coincidence and is worth recording precisely, because it is the same statement the Heisenberg
computation pinned numerically (see `ZhuNormalization`).

Zhu's square bracket lives in the coordinate `z` with `w = e^z − 1`, i.e. `z = log(1+w)`.  The unit
that generates every square-bracket coefficient is `uSeries = log(1+w)/w = z/(e^z − 1)` — and
`z/(e^z − 1)` is, by definition, the **generating function of the Bernoulli numbers**.  So the
Bernoulli constants are not imported into the recursion from outside: they are what `uSeries` *is*,
read in the `z`-coordinate. -/

/-- **`u` is the Bernoulli generating function**, in the coordinate `z` where `w = e^z − 1`:
`B(z)·(e^z − 1) = z`, i.e. `B(z) = z/(e^z − 1)`, which is `uSeries` transported to that coordinate.

The repo's cylinder→torus map `expMinusOne` is literally Mathlib's `exp ℂ - 1`, so this is Mathlib's
`bernoulliPowerSeries_mul_exp_sub_one` on the nose. -/
theorem bernoulliPowerSeries_mul_expMinusOne :
    _root_.bernoulliPowerSeries ℂ * expMinusOne = PowerSeries.X := by
  rw [expMinusOne]
  exact _root_.bernoulliPowerSeries_mul_exp_sub_one ℂ

/-- The coefficients of that generating function are `B_n/n!`. -/
theorem coeff_bernoulliPowerSeries (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (_root_.bernoulliPowerSeries ℂ)
      = ((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ) := by
  rw [_root_.bernoulliPowerSeries, PowerSeries.coeff_mk, eq_ratCast]
  push_cast
  ring

/-- **The pinned Zhu constant is a Bernoulli generating-function coefficient.**

`G_{2j}` has constant term `−B_{2j}/(2j)!` (`zhuG_zero`, fixed by the Heisenberg computation), and
that number is exactly `−[z^{2j}]` of `z/(e^z − 1)`.  This closes the loop between the numerically
pinned normalisation and the algebra: the constants the recursion must produce are the coefficients
of the very unit `uSeries` out of which all the square-bracket weights are built.  It is the
identity the remaining weight matching rests on — not the matching itself. -/
theorem zhuG_zero_eq_neg_coeff_bernoulli (j : ℕ) :
    zhuG j 0 = -PowerSeries.coeff (R := ℂ) (2 * j) (_root_.bernoulliPowerSeries ℂ) := by
  rw [zhuG_zero, coeff_bernoulliPowerSeries]

/-! ## A genuine instance: Zhu's recursion at `v = 𝟙`

Everything above is machinery for the general case.  The **vacuum case** `v = 𝟙`, however, closes
completely, and it is a real instance of `ZhuRecursionAt` — not a special case that trivialises the
statement, but one that tests it: it forces the two-point term to be present with coefficient one
and the entire Eisenstein tail to be absent.

Three facts do it, all already available:
* `a[−1]𝟙 = a` — the coefficients `c(k,−1,i)` vanish for `i < −1` (lower-triangularity), `a₍ᵢ₎𝟙 = 0`
  for `i ≥ 0` (VA3 creation), so only `i = −1` survives, with weight `c(k,−1,−1) = 1`;
* `o(𝟙) = id`, so the two-point term is the one-point function of `a`;
* `a[2m−1]𝟙 = 0` for `m ≥ 1` — the surviving indices are `i ≥ 2m−1 ≥ 1 ≥ 0`, where creation kills
  `a₍ᵢ₎𝟙`.  So the tail vanishes identically. -/

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`a[−1]𝟙 = a`**: the square bracket, like the ordinary vertex operator, creates. -/
theorem vSqZ_neg_one_vacuum (k : ℕ) (a : 𝒱) : vSqZ W a k (-1) W.vacuum = a := by
  rw [vSqZ_apply, finsum_eq_single _ (-1 : ℤ) (fun i hi => ?_)]
  · rw [sqBracketCoeffZ_neg_one_diag, one_smul]
    exact W.smul_vacuum_neg_one a
  · by_cases hi0 : (0 : ℤ) ≤ i
    · rw [show mode (W.Y a) i W.vacuum = 0 from W.smul_vacuum_nonneg a hi0, smul_zero]
    · push_neg at hi0
      rw [sqBracketCoeffZ_of_lt k (by omega : i < -1), zero_smul]

/-- **`a[m]𝟙 = 0` for `m ≥ 0`**: every surviving index is `≥ m ≥ 0`, where creation kills the
vacuum.  In particular the whole Eisenstein tail of Zhu's recursion vanishes at `v = 𝟙`. -/
theorem vSqZ_nonneg_vacuum (k : ℕ) (a : 𝒱) {m : ℤ} (hm : 0 ≤ m) :
    vSqZ W a k m W.vacuum = 0 := by
  rw [vSqZ_apply]
  refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
  by_cases hi : m ≤ i
  · rw [show mode (W.Y a) i W.vacuum = 0 from W.smul_vacuum_nonneg a (by omega), smul_zero]
  · push_neg at hi
    rw [sqBracketCoeffZ_of_lt k hi, zero_smul]

/-- **Zhu's recursion at `v = 𝟙`**, for the pinned family `zhuG` (and in fact for any
coefficient family whatsoever, since the tail vanishes):

  `𝒵_M(a[−1]𝟙) = tr_M(o(a)o(𝟙)q^{L₀−c/24}) + 0`.

Both sides reduce to `𝒵_M(a)`.  This is a genuine instance of `ZhuRecursionAt`: the two-point term
appears with coefficient exactly one — as `twoPoint_total_coeff_eq_one` predicts — and the entire
Eisenstein tail is absent, which is what `vSqZ_nonneg_vacuum` forces. -/
theorem zhuRecursionAt_vacuum (N : OrdVModule W M) (G : ℕ → (ℕ → ℂ)) (a : 𝒱) (k : ℕ) :
    ZhuRecursionAt N G a W.vacuum k := by
  have htail : ∀ j : ℕ, qConv (G (j + 1))
      (torusOnePoint N (vSqZ W a k (2 * (j + 1) - 1 : ℤ) W.vacuum)) = 0 := by
    intro j
    rw [vSqZ_nonneg_vacuum k a (by omega : (0 : ℤ) ≤ 2 * (j + 1) - 1), torusOnePoint_zero,
      qConv_zero_right]
  have h2 : torusTwoPoint N a W.vacuum = torusOnePoint N a := by
    funext e
    haveI := N.finrank (e + W.centralCharge / 24)
    change LinearMap.trace ℂ _
      (weightBlock N ((oMod N a).comp (oMod N W.vacuum)) (e + W.centralCharge / 24)) = _
    rw [oMod_vacuum, LinearMap.comp_id]
    rfl
  rw [ZhuRecursionAt, vSqZ_neg_one_vacuum, h2, finsum_congr htail, finsum_zero, add_zero]

end

/-! ## Residual — what remains for `ZhuRecursionAt`

Every structural ingredient of Zhu Prop. 4.3.2 is proved and unconditional:

1. the left-hand side expands, `onePoint_vSqZ_expand`;
2. each `𝒵_M(a₍ᵢ₎v)` becomes compensated-pair traces **for every `i`**,
   `onePoint_smul_eq_pairs_finset`;
3. each pair trace is evaluated by the trichotomy of `GradedTrace` (telescope down / two-point /
   telescope up), with no carried hypotheses;
4. the non-tail summand is pinned — only `i = −1` produces it, with coefficient `1`
   (`iterate_twoPoint_cancel`, `twoPoint_total_coeff_eq_one`);
5. the tail's normalisation is pinned (`zhuG`, `qConv_zhuG_eq`).

What is left is the **combinatorial collection**, and its engine is banked:

* **The `(p, j)` regrouping.**  Each pair trace contributes `Σ_j` at degree shift `j·s` with
  `s = kₐ − p − 1`; summing over `p` too gives a sum over pairs whose *product* is the total
  displacement.  `finsum_pow_mul_eq_lambert` is exactly that regrouping — `Σ_{(d,j)} d^s F(d·j) =
  Σ_n σ_s(n) F(n)` — so this step is an application, not a development.
* **The weight matching** (the genuinely open step).  The `c(k,−1,i)` of the expansion, the
  `(−1)^j C(i,j)` of the iterate and the `C(i,p)` of the compensating commutator must combine into
  the coefficients of `zhuG`.  Its content is identified — those coefficients *are* the Bernoulli
  generating function `z/(e^z−1)`, which is `uSeries` in the `z`-coordinate
  (`zhuG_zero_eq_neg_coeff_bernoulli`) — and no convention risk attaches to it.  But carrying it out
  formally means relating the `w`-adic and `z`-adic expansions of `uSeries`, i.e. a **substitution**
  between the two coordinates.  The whole square-bracket development was deliberately built to avoid
  substitution (explicit residues in `w` only), so this is a genuine new ingredient rather than
  bookkeeping in the existing framework.
-/

end VOA
