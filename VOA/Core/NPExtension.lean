/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.NonlinearZeta

/-!
# The De Sole–Kac Lemma 3.2 interface: `NPExtension`

De Sole–Kac Lemma 3.2 ([DK] = Comm. Math. Phys. **254** (2005) 659–694, label
`extension`) produces the unique pair of maps

  `N : T(R) ⊗ T(R) → T(R)`  (normally ordered product),
  `P_λ : T(R) ⊗ T(R) → ℂ[λ] ⊗ T(R)`  (extended λ-bracket)

satisfying their equations (3.1)–(3.7), together with the grading bounds (3.8).
(Printed numbers throughout; the LaTeX source labels of those eight displays are
`1`–`8`.)  This file packages that pair **as a structure**,
`NPExtension D`, in the library's contract-first idiom (`GenFields`, `MIdeal`).  An instance
would be *constructed* by the [DK] recursion (induction on the ζ-degree of
`Core.NonlinearZeta`); everything downstream is parametrized over an arbitrary
`NP : NPExtension D`, so the framework compiles — and its consequences are theorems —
without the hard recursion, which is not formalised here.

## Slice conventions

The λ-polynomial `P_λ(A,B) = Σₙ λ⁽ⁿ⁾ · P(A,B)(n)` is carried by its `n`-th–product
slices `P A B : ℕ → TR ι`, with the divided-power normalization `λ⁽ⁿ⁾ = λⁿ/n!` used
throughout the library (`brk`).  The λ-calculus of [DK] then becomes:

* sesquilinearity `[TA_λ B] = -λ[A_λ B]`, `[A_λ TB] = (λ+T)[A_λ B]` is `P_Tleft`,
  `P_Tright`, literally the one-step operators `Lstep`, `Rstep` of
  `Core.NonlinearConformal` §5 — so the extension to divided powers is `brk`
  (`P_gv_eq_brk` below), by the very construction of `brk`;
* `∫₀ᵀ dλ λ⁽ⁿ⁾ = T⁽ⁿ⁺¹⁾` — the divided `T`-powers `Tdiv (n+1)` below;
* `e^{T∂_λ}` acts on slices as `f ↦ (n ↦ f (n+m))` against `Tdiv m`;
* `∫₀^λ dμ μ⁽ⁱ⁾ = λ⁽ⁱ⁺¹⁾` and `λ⁽ᵏ⁾λ⁽ʲ⁺¹⁾ = C(k+j+1, k)·λ⁽ᵏ⁺ʲ⁺¹⁾` produce the finite
  binomial convolutions in `wickLeft`;
* `∫₀^λ dμ μ⁽ⁱ⁾(λ-μ)⁽ʲ⁾ = λ⁽ⁱ⁺ʲ⁺¹⁾` (the Beta integral, in divided powers) produces the
  finite convolution in `wickRight`.

None of this is a *translation*: [DK] eq. (2.4) defines `[a_λ b] = Σ λ⁽ⁿ⁾ a₍ₙ₎b` with
`λ⁽ⁿ⁾ = λⁿ/n!`, so the divided-power normalization above is [DK]'s own, as are the
sesquilinearity signs, the `T`-derivation direction, and the Koszul sign
`p(a,b) = (-1)^{p(a)p(b)}` (their Definition 3.1 / Definition 2.1).  The single genuine
divergence is the choice of `ℂ[T]`-basis of `R`: [DK] take `T^k āⁱ`, the library takes
`gv (i,k) = T^k aⁱ/k!`.  That is a rescaling of the same free module, and it cancels
identically in every field below, each of which is stated in a slot where both sides are
linear.

⚠ **Renumbering trap.**  [DK] Definition 3.1 lists its two conditions as (1)
sesquilinearity, (2) grading condition.  The review [DSK-rev] (De Sole–Kac, Japan. J. Math.
**1** (2006)) §3 lists them in the **opposite**
order.  The citations `Definition 3.1(1)` / `3.1(2)` in this file and in
`Core.NonlinearZeta` follow **[DK]** and are correct as written; do not "fix" them
against the review.

Where an infinite `n`-sum appears in [DK] (`quasiAssoc`, the `e^{T∂_λ}` sums of
`wickRight`), the slice form needs the sum to terminate; since the second argument `C`
is an arbitrary element of `T(R)`, no *uniform* cutoff exists, so those two fields take
an explicit cutoff `m` together with the vanishing hypotheses that make the sum
stable — every cutoff beyond the vanishing threshold gives the same equation, and
`P_eventually_zero` (from the mandatory termination field `P_filt`) always supplies one.

## The two grading fields, and the termination bound

* `N_zfilt`, `P_zfilt` — [DK] (3.8): `Δ(N(A,B)) ≤ ΔA + ΔB` and the **strict** decrease
  `Δ(P_λ(A,B)) < ΔA + ΔB`, in the ζ-filtration (`deg T = 0`).
* `P_filt` — the **Δ-filtration termination bound** `P A B n ∈ filt (ΔA + ΔB - n - 1)`,
  in the *conformal-weight* filtration (`deg T = +1`), a different device from (3.8).
  It is the `T(R)`-extension of [DK] Example 6.2, eq. (6.2)
  `cw(a₍ₙ₎b) = cw(a) + cw(b) - n - 1`, which at the bottom letters is literally the
  library's own `OPEData.ope_wt`.  What [DK] leave implicit is only the *termination*
  it buys: their `P_λ` lands in `ℂ[λ] ⊗ T(R)` by fiat, whereas in slice form one must
  say why the slices stop.  This field is mandatory: without it the
  interface is unusable.

## `NPGraded`

Exact-weight gradedness of `N` and `P` under `OPEData.IsConformal` is **not** derivable
from the interface; it follows from the *uniqueness* half of the [DK] recursion
restricted to graded data.  It is therefore a separate `Prop` mixin, consumed downstream
as a named hypothesis (`hg : NPGraded NP`) — never silently folded into the base
structure.  The load-bearing vacuum-survival guard of `Core.VAPresentation` is
conditional on it.

## Honesty

⚠ **No instance of `NPExtension` is constructed in this file, or anywhere in the library.**
The existence–uniqueness theorem (`npExtension_existsUnique`) is not formalised; it is the
largest single missing piece of the nonlinear presentation layer.  Nothing here may be read
as claiming the De Sole–Kac existence theorem.  Consequently every downstream statement
quantified over `NP : NPExtension D` is a **conditional** whose antecedent nobody has
supplied; as Lean propositions such statements are vacuously true.  (The results of
`Core.NonlinearZeta` are *not* of this kind — they mention no `NP` and are unconditional.)

⚠ **Source-premise boundary.**  [DK] Definition 3.1 assumes that the seed
λ-bracket on `R` is parity-preserving.  The older `OPEData` structure stores the parity
of each generator but does not make that compatibility a field.  This file therefore
names the missing input as `OPEData.SeedParityCompatible` and proves that it propagates
from the bottom OPE table to all divided-power generators (`brk_mem_parPiece`).  It is a
hypothesis for a future constructor of an instance, not a field of an already-constructed
`NPExtension`: the recursion equations below state equalities but no parity-support
conclusion, so they cannot by themselves discharge this source premise.

There are **17**, not 18, fields in `NPExtension`: two maps; two halves of (3.1);
(3.2); two halves of (3.4); (3.5); two extended sesquilinearity laws; the `T`-Leibniz
law; (3.3), (3.6), and (3.7); two halves of (3.8); and the extra `P_filt`.  Thus 16
are [DK]-derived when `N` and `P` themselves are included, and `P_filt` is the one
non-DK slice-termination field.  The earlier 18-field inventory was an arithmetic
miscount.

⚠ **Six fields are exercised by nothing** — but they are *checked*.  `P_one_left`
([DK] (3.4), left half), `quasiAssoc` ([DK] (3.3)), `wickLeft` ((3.6)), `wickRight`
((3.7)), `N_zfilt` and `P_zfilt` ((3.8)) are consumed by **no** proof in the library, so a
transcription error in any of them would be
invisible to every gate and would surface only deep inside the [DK] recursion.  To
address that risk, **all 16 DK-derived fields of
`NPExtension`, including these six, were checked line by line against [DK] Lemma 3.2
and, for the three extended translation laws, §4 Lemma 4.2, and found to transcribe the
sources correctly**; `P_filt`, the one non-DK field, was checked for
term-by-term compatibility with the recursion equations rather than for source fidelity.
Its actual satisfiability remains part of the unproved [DK] existence theorem.  The
residual fact to keep in mind is only that nothing *exercises* these six — the [DK]
recursion would be their first consumer.

Two consistency checks were done by hand and should be redone after any edit to the
cutoff hypotheses of `quasiAssoc`/`wickRight`: at `w = 1` `quasiAssoc` collapses to
`N(gv p, C) = gv p · C` (via `N_one_left`, `P_one_left`, `Tdiv_one_eq_zero`); and
`wickRight` is consistent at `w = 1` **only because both** vanishing hypotheses share the
*same* cutoff `m` — with only the first, `m = 0` would force `P (gv p) C n = 0`
identically and the interface would be outright inconsistent.  That is a genuine
near-miss the current statement gets right.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/

namespace VOA.NonlinearConformal

open Module (End)

set_option maxRecDepth 4000

universe u

variable {ι : Type u}

/-! ## §1  Parity of words, and divided `T`-powers -/

/-- The parity of a word of `T(R)`: the sum of the parities of its letters (the
`T`-power of a letter does not change its parity). -/
def parWord (D : OPEData ι) (w : FreeMonoid (GenIdx ι)) : ZMod 2 :=
  (w.toList.map (fun p : GenIdx ι => D.par p.1)).sum

theorem parWord_one (D : OPEData ι) : parWord D (1 : FreeMonoid (GenIdx ι)) = 0 := rfl

theorem parWord_of (D : OPEData ι) (p : GenIdx ι) :
    parWord D (FreeMonoid.of p) = D.par p.1 := by
  change ((FreeMonoid.of p).toList.map (fun q : GenIdx ι => D.par q.1)).sum = D.par p.1
  rw [show (FreeMonoid.of p).toList = [p] from rfl, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem parWord_mul (D : OPEData ι) (v w : FreeMonoid (GenIdx ι)) :
    parWord D (v * w) = parWord D v + parWord D w := by
  change (((v * w).toList).map _).sum = _
  rw [show (v * w).toList = v.toList ++ w.toList from rfl, List.map_append, List.sum_append]
  rfl

/-! ### The source's parity-preserving seed hypothesis

[DK] Definition 3.1 requires the input λ-bracket `R ⊗ R → ℂ[λ] ⊗ T(R)` to
preserve parity.  Since `OPEData` records only its values on the bottom generators, the
condition says exactly that every `D.ope i j n` is supported on words of parity
`D.par i + D.par j`. -/

/-- The span of tensor words of a fixed parity. -/
noncomputable def parPiece (D : OPEData ι) (r : ZMod 2) : Submodule ℂ (TR ι) :=
  Submodule.span ℂ (wbasis ι '' {w | parWord D w = r})

/-- A basis word lies in its parity piece. -/
theorem wbasis_mem_parPiece (D : OPEData ι) (w : FreeMonoid (GenIdx ι)) :
    wbasis ι w ∈ parPiece D (parWord D w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

/-- Left concatenation by a generator adds its declared parity. -/
theorem gv_mul_mem_parPiece (D : OPEData ι) (p : GenIdx ι) {r : ZMod 2} {y : TR ι}
    (hy : y ∈ parPiece D r) : gv p * y ∈ parPiece D (D.par p.1 + r) := by
  rw [parPiece] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      change wbasis ι (FreeMonoid.of p) * wbasis ι w ∈ _
      rw [← wbasis_mul]
      refine Submodule.subset_span ⟨FreeMonoid.of p * w, ?_, rfl⟩
      change parWord D (FreeMonoid.of p * w) = D.par p.1 + r
      rw [parWord_mul, parWord_of, hw]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

/-- `T` preserves word parity. -/
theorem Ttr_wbasis_mem_parPiece (D : OPEData ι) (l : List (GenIdx ι)) :
    Ttr (wbasis ι (FreeMonoid.ofList l)) ∈ parPiece D (parWord D (FreeMonoid.ofList l)) := by
  induction l with
  | nil =>
      rw [show FreeMonoid.ofList ([] : List (GenIdx ι)) = 1 from rfl, wbasis_one, Ttr_one]
      exact Submodule.zero_mem _
  | cons p l ih =>
      have hsplit : FreeMonoid.ofList (p :: l) =
          FreeMonoid.of p * FreeMonoid.ofList l := rfl
      have hw : wbasis ι (FreeMonoid.ofList (p :: l)) =
          gv p * wbasis ι (FreeMonoid.ofList l) := by rw [hsplit, wbasis_mul, gv]
      have hpar : parWord D (FreeMonoid.ofList (p :: l)) =
          D.par p.1 + parWord D (FreeMonoid.ofList l) := by
        rw [hsplit, parWord_mul, parWord_of]
      rw [hw, Ttr_mul, hpar]
      refine Submodule.add_mem _ (gv_mul_mem_parPiece D p ih) ?_
      rw [Ttr_gv, smul_mul_assoc]
      exact Submodule.smul_mem _ _
        (gv_mul_mem_parPiece D (p.1, p.2 + 1) (wbasis_mem_parPiece D _))

/-- `T` preserves every parity piece. -/
theorem Ttr_mem_parPiece (D : OPEData ι) {r : ZMod 2} {x : TR ι}
    (hx : x ∈ parPiece D r) : Ttr x ∈ parPiece D r := by
  rw [parPiece] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hT := Ttr_wbasis_mem_parPiece D (FreeMonoid.toList w)
      rw [show FreeMonoid.ofList (FreeMonoid.toList w) = w from rfl, hw] at hT
      exact hT
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- The explicit seed compatibility omitted from the older `OPEData` bundle but required
by [DK] Definition 3.1: the bottom λ-bracket is parity-preserving. -/
def OPEData.SeedParityCompatible (D : OPEData ι) : Prop :=
  ∀ i j (n : ℕ), D.ope i j n ∈ parPiece D (D.par i + D.par j)

/-- The left sesquilinearity step preserves a fixed parity support. -/
theorem Lstep_mem_parPiece (D : OPEData ι) {f : ℕ → TR ι} {r : ZMod 2}
    (hf : ∀ n, f n ∈ parPiece D r) (n : ℕ) : Lstep f n ∈ parPiece D r :=
  Submodule.smul_mem _ _ (hf (n - 1))

/-- The right sesquilinearity step preserves a fixed parity support. -/
theorem Rstep_mem_parPiece (D : OPEData ι) {f : ℕ → TR ι} {r : ZMod 2}
    (hf : ∀ n, f n ∈ parPiece D r) (n : ℕ) : Rstep f n ∈ parPiece D r :=
  Submodule.add_mem _ (Ttr_mem_parPiece D (hf n)) (Submodule.smul_mem _ _ (hf (n - 1)))

/-- The seed parity condition propagates by sesquilinearity to the bracket on every
pair of divided-power generators. -/
theorem brk_mem_parPiece {D : OPEData ι} (hD : D.SeedParityCompatible)
    (p q : GenIdx ι) (n : ℕ) : brk D p q n ∈ parPiece D (D.par p.1 + D.par q.1) := by
  rw [brk]
  refine Submodule.smul_mem _ _ ?_
  have hR : ∀ l m, Rstep^[l] (D.ope p.1 q.1) m ∈
      parPiece D (D.par p.1 + D.par q.1) := by
    intro l
    induction l with
    | zero => simpa using hD p.1 q.1
    | succ l ih =>
        rw [Function.iterate_succ_apply']
        exact Rstep_mem_parPiece D ih
  have hL : ∀ k m, Lstep^[k] (Rstep^[q.2] (D.ope p.1 q.1)) m ∈
      parPiece D (D.par p.1 + D.par q.1) := by
    intro k
    induction k with
    | zero => simpa using hR q.2
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Lstep_mem_parPiece D ih
  exact hL p.2 n

/-- The divided `T`-power `T⁽ᵏ⁾ = Tᵏ/k!`, as a linear map.  This is `∫₀ᵀ dλ λ⁽ᵏ⁻¹⁾` for
`k ≥ 1`, and the coefficient of `∂_λᵏ` in `e^{T∂_λ}`. -/
noncomputable def Tdiv (k : ℕ) : TR ι →ₗ[ℂ] TR ι :=
  ((k.factorial : ℂ))⁻¹ • (((Ttr : End ℂ (TR ι)) ^ k : End ℂ (TR ι)) : TR ι →ₗ[ℂ] TR ι)

theorem Tdiv_apply (k : ℕ) (x : TR ι) :
    Tdiv k x = ((k.factorial : ℂ))⁻¹ • (((Ttr : End ℂ (TR ι)) ^ k) x) := rfl

@[simp] theorem Tdiv_zero_apply (x : TR ι) : Tdiv 0 x = x := by
  rw [Tdiv_apply]
  simp

/-- `T⁽ᵏ⁾` kills the unit word for `k ≥ 1`. -/
theorem Tdiv_one_eq_zero {k : ℕ} (hk : 0 < k) : Tdiv k (1 : TR ι) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Tdiv_apply, Ttr_pow_succ_one, smul_zero]

/-- `T⁽ᵏ⁾` on a basis letter is the divided power `dpow`: the interface's integral
operators reproduce the creation-half divided powers of `Core.NonlinearConformal` §7. -/
theorem Tdiv_gv (k : ℕ) (p : GenIdx ι) : Tdiv k (gv p) = dpow p k := by
  obtain ⟨i, j⟩ := p
  have hj : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [Tdiv_apply, Ttr_pow_gv, dpow, smul_smul]
  congr 1
  have hchoose : ((j + k).choose k : ℕ) * j.factorial * k.factorial = (j + k).factorial :=
    Nat.add_choose_mul_factorial_mul_factorial j k
  have hcast : (((j + k).choose k : ℕ) : ℂ) * (j.factorial : ℕ) * (k.factorial : ℕ)
      = (((j + k).factorial : ℕ) : ℂ) := by exact_mod_cast congrArg (fun t : ℕ => (t : ℂ)) hchoose
  rw [← hcast]
  field_simp

/-- `Lstep` commutes with scalars. -/
theorem Lstep_smul (c : ℂ) (f : ℕ → TR ι) : Lstep (c • f) = c • Lstep f := by
  funext n
  change -(n : ℂ) • (c • f (n - 1)) = c • (-(n : ℂ) • f (n - 1))
  rw [smul_comm]

/-- `Rstep` commutes with scalars. -/
theorem Rstep_smul (c : ℂ) (f : ℕ → TR ι) : Rstep (c • f) = c • Rstep f := by
  funext n
  change Ttr (c • f n) + (n : ℂ) • (c • f (n - 1))
      = c • (Ttr (f n) + (n : ℂ) • f (n - 1))
  rw [map_smul, smul_add, smul_comm]

theorem Lstep_iterate_smul (k : ℕ) (c : ℂ) (f : ℕ → TR ι) :
    Lstep^[k] (c • f) = c • Lstep^[k] f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Lstep_smul, ih (Lstep f),
        ← Function.iterate_succ_apply]

theorem Rstep_iterate_smul (l : ℕ) (c : ℂ) (f : ℕ → TR ι) :
    Rstep^[l] (c • f) = c • Rstep^[l] f := by
  induction l generalizing f with
  | zero => rfl
  | succ l ih =>
      rw [Function.iterate_succ_apply, Rstep_smul, ih (Rstep f),
        ← Function.iterate_succ_apply]

/-! ## §2  The interface -/

/-- **The De Sole–Kac Lemma 3.2 interface.**  A pair `(N, P)` on `T(R)` satisfying
[DK] equations (3.1)–(3.7) in slice form, the grading bounds (3.8), the `T`-Leibniz law
(their §4 Lemma 4.2, eq. (4.1)), and the slice-termination bound `P_filt`.

The λ-polynomial `P_λ(A,B) = Σₙ λⁿ/n! · P A B n`.  Each law field cites its [DK]
equation number.  The [DK] recursion would construct the (unique) instance; the library only consumes the
interface.  See the module docstring for the slice-form dictionary. -/
structure NPExtension (D : OPEData ι) where
  /-- The normally ordered product `N : T(R) ⊗ T(R) → T(R)`, bilinear. -/
  N : TR ι →ₗ[ℂ] TR ι →ₗ[ℂ] TR ι
  /-- The extended λ-bracket, in `n`-th–product slices: `P A B n` is the coefficient of
  `λⁿ/n!` in `P_λ(A,B)`.  Bilinear. -/
  P : TR ι →ₗ[ℂ] TR ι →ₗ[ℂ] (ℕ → TR ι)
  /-- [DK] (3.1), left half: `N(1, A) = A`. -/
  N_one_left : ∀ A : TR ι, N 1 A = A
  /-- [DK] (3.1), right half: `N(A, 1) = A`. -/
  N_one_right : ∀ A : TR ι, N A 1 = A
  /-- [DK] (3.2): for a generator `a ∈ R` (any divided power), `N(a, B) = a ⊗ B` —
  concatenation in the tensor algebra. -/
  N_gv : ∀ (p : GenIdx ι) (B : TR ι), N (gv p) B = gv p * B
  /-- [DK] (3.4), left half: `P_λ(1, A) = 0`. -/
  P_one_left : ∀ (A : TR ι) (n : ℕ), P 1 A n = 0
  /-- [DK] (3.4), right half: `P_λ(A, 1) = 0`. -/
  P_one_right : ∀ (A : TR ι) (n : ℕ), P A 1 n = 0
  /-- [DK] (3.5): on the bottom generators the bracket is the user's OPE table.  [DK] state
  (3.5) for all `a, b ∈ R`; the remaining divided powers are recovered from `P_Tleft` /
  `P_Tright` by `P_gv_eq_brk` below. -/
  P_bot : ∀ i j : ι, P (gv (i, 0)) (gv (j, 0)) = D.ope i j
  /-- Sesquilinearity in the left slot, slice form: `P_λ(TA, B) = -λ P_λ(A,B)` is one
  `Lstep` ([DK] §4 Lemma 4.2, eq. (4.2), source label `sesq1`; extends their Definition
  3.1(1) from `R` to all of `T(R)`). -/
  P_Tleft : ∀ A B : TR ι, P (Ttr A) B = Lstep (P A B)
  /-- Sesquilinearity in the right slot, slice form: `P_λ(A, TB) = (λ+T) P_λ(A,B)` is
  one `Rstep` ([DK] §4 Lemma 4.2, eq. (4.3), source label `sesq2`). -/
  P_Tright : ∀ A B : TR ι, P A (Ttr B) = Rstep (P A B)
  /-- `T` is a derivation of the normally ordered product ([DK] §4 Lemma 4.2, eq. (4.1),
  source label `leib`). -/
  Ttr_N : ∀ A B : TR ι, Ttr (N A B) = N (Ttr A) B + N A (Ttr B)
  /-- [DK] (3.3), **quasi-associativity**, slice form: for a letter `a = gv p`, a word
  `B = wbasis w`, and arbitrary `C`,

  `N(a⊗B, C) = N(a, N(B,C)) + Σₙ N(T⁽ⁿ⁺¹⁾a, P(B,C)(n)) + p(a,B)·Σₙ N(T⁽ⁿ⁺¹⁾B, P(a,C)(n))`.

  The sums are stated with an explicit cutoff `m` valid by the two vanishing
  hypotheses; `P_eventually_zero` always supplies one, and the equation is independent
  of the choice.

  **Editorial correction, verified against the sources [DK] and [DSK-rev].**
  The Koszul sign here reads `p(a,B)`, whereas [DK] (3.3) prints `p(a,b)`.  The printed
  sign is a typo and `p(a,B)` is correct, on four independent grounds: (i) no `b` occurs
  anywhere in (3.3), whose variables are `a`, `B`, `C`, so `p(a,b)` refers to an
  undeclared symbol; (ii) the proof of Lemma 3.2 itself expands `A = a ⊗ A'` with the
  sign `p(a,A')`, `A'` sitting in the slot `B` occupies; (iii) [DK] §4 defines
  `qa(A,B,C)` with the sign `p(A,B)` and remarks that `N` is *defined* by `qa(a,B,C) = 0`,
  which is (3.3) with sign `p(a,B)`; (iv) decisively, the same authors restate this lemma
  in [DSK-rev] §3 and print `p(a,B)`.  Do not "restore" the printed `p(a,b)`.

  Note also that this field is stated for `B` a basis **word** where [DK] state it for
  arbitrary `B ∈ T(R)`.  That is deliberate and in fact necessary: the `p(a,B)` prefactor
  makes the equation linear in `B` only on parity-homogeneous `B`.  A consumer wanting
  the general form must extend by linearity; no such lemma exists yet. -/
  quasiAssoc : ∀ (p : GenIdx ι) (w : FreeMonoid (GenIdx ι)) (C : TR ι) (m : ℕ),
    (∀ n, m ≤ n → P (wbasis ι w) C n = 0) →
    (∀ n, m ≤ n → P (gv p) C n = 0) →
    N (gv p * wbasis ι w) C
      = N (gv p) (N (wbasis ι w) C)
        + ∑ n ∈ Finset.range m, N (Tdiv (n + 1) (gv p)) (P (wbasis ι w) C n)
        + koszul (D.par p.1) (parWord D w) •
            ∑ n ∈ Finset.range m, N (Tdiv (n + 1) (wbasis ι w)) (P (gv p) C n)
  /-- [DK] (3.6), the **left Wick formula**, slice form: for letters `a = gv p`,
  `b = gv q` and arbitrary `C`,

  `P(a, b⊗C)(n) = N(P(a,b)(n), C) + p(a,b)·N(b, P(a,C)(n)) + Σ_{k<n} C(n,k)·P(P(a,b)(k), C)(n-1-k)`.

  The convolution comes from `∫₀^λ dμ P_μ(P_λ(a,b), C)` via `∫₀^λ μ⁽ⁱ⁾dμ = λ⁽ⁱ⁺¹⁾` and
  `λ⁽ᵏ⁾λ⁽ʲ⁺¹⁾ = C(k+j+1,k)λ⁽ᵏ⁺ʲ⁺¹⁾`; it is finite with no cutoff needed. -/
  wickLeft : ∀ (p q : GenIdx ι) (C : TR ι) (n : ℕ),
    P (gv p) (gv q * C) n
      = N (P (gv p) (gv q) n) C
        + koszul (D.par p.1) (D.par q.1) • N (gv q) (P (gv p) C n)
        + ∑ k ∈ Finset.range n,
            ((n.choose k : ℕ) : ℂ) • P (P (gv p) (gv q) k) C (n - 1 - k)
  /-- [DK] (3.7), the **right Wick formula**, slice form: for a letter `a = gv p`, a word
  `B = wbasis w`, and arbitrary `C`,

  `P(a⊗B, C)(n) = Σⱼ N(T⁽ʲ⁾a, P(B,C)(n+j))`
  `+ p(a,B)·(Σⱼ N(T⁽ʲ⁾B, P(a,C)(n+j)) + Σ_{j<n} P(B, P(a,C)(j))(n-1-j))`.

  The `e^{T∂_λ}` sums are cut off at `m` under the vanishing hypotheses; the last
  convolution comes from `∫₀^λ dμ P_μ(B, P_{λ-μ}(a,C))` via the divided-power Beta
  integral `∫₀^λ μ⁽ⁱ⁾(λ-μ)⁽ʲ⁾ dμ = λ⁽ⁱ⁺ʲ⁺¹⁾` and is finite. -/
  wickRight : ∀ (p : GenIdx ι) (w : FreeMonoid (GenIdx ι)) (C : TR ι) (n m : ℕ),
    (∀ k, m ≤ k → P (wbasis ι w) C k = 0) →
    (∀ k, m ≤ k → P (gv p) C k = 0) →
    P (gv p * wbasis ι w) C n
      = ∑ j ∈ Finset.range m, N (Tdiv j (gv p)) (P (wbasis ι w) C (n + j))
        + koszul (D.par p.1) (parWord D w) •
            (∑ j ∈ Finset.range m, N (Tdiv j (wbasis ι w)) (P (gv p) C (n + j))
              + ∑ j ∈ Finset.range n, P (wbasis ι w) (P (gv p) C j) (n - 1 - j))
  /-- [DK] (3.8), first half: `Δ(N(A,B)) ≤ ΔA + ΔB` in the ζ-filtration. -/
  N_zfilt : ∀ {dA dB : ℤ} {A B : TR ι}, A ∈ zfilt D.wt dA → B ∈ zfilt D.wt dB →
    N A B ∈ zfilt D.wt (dA + dB)
  /-- [DK] (3.8), second half: the **strict** decrease `Δ(P_λ(A,B)) < ΔA + ΔB`, i.e.
  `≤ ΔA + ΔB - 1` in the integer-graded ζ-filtration, uniformly in the slice. -/
  P_zfilt : ∀ {dA dB : ℤ} {A B : TR ι}, A ∈ zfilt D.wt dA → B ∈ zfilt D.wt dB →
    ∀ n : ℕ, P A B n ∈ zfilt D.wt (dA + dB - 1)
  /-- **Mandatory termination field.**  The conformal-weight bound
  `P A B n ∈ filt (ΔA + ΔB - n - 1)`: for `n` large the bound is negative and the slice
  vanishes (`filt_neg`), which is what makes every integral operator above — and the
  Jacobi expression `Jac` of the (unformalised) intertwining layer — a well-formed finite sum.  The bound itself is [DK] Example 6.2,
  eq. (6.2) (`cw(a₍ₙ₎b) = cw(a) + cw(b) - n - 1`) promoted from `R` to `T(R)`; at the
  bottom letters it is exactly `OPEData.ope_wt`.  What [DK] leave implicit is only that
  it forces termination, their `P_λ` being `ℂ[λ]`-polynomial by fiat.  Checked
  term-by-term compatible: all seven recursion equations above are homogeneous of the
  right conformal degree under this rule, so the [DK] recursion is expected to prove
  it rather than trip on it; no existence claim is made without that proof.
  (No `N_filt` companion is asserted, though the [DK] induction will need one
  internally — assuming less than one proves is sound.) -/
  P_filt : ∀ {dA dB : ℤ} {A B : TR ι}, A ∈ filt D.wt dA → B ∈ filt D.wt dB →
    ∀ n : ℕ, P A B n ∈ filt D.wt (dA + dB - n - 1)

namespace NPExtension

variable {D : OPEData ι} (NP : NPExtension D)

/-! ## §3  First consequences of the interface -/

/-- **The slices terminate**: for every `A, B` the λ-polynomial is genuinely
polynomial.  This is the termination bound made usable: it supplies the cutoff every `quasiAssoc` /
`wickRight` instance needs. -/
theorem P_eventually_zero (A B : TR ι) : ∃ m : ℕ, ∀ n : ℕ, m ≤ n → NP.P A B n = 0 := by
  obtain ⟨dA, hdA⟩ := filt_exhaustive D.wt A
  obtain ⟨dB, hdB⟩ := filt_exhaustive D.wt B
  refine ⟨(dA + dB).toNat, fun n hn => ?_⟩
  have hneg : dA + dB - (n : ℤ) - 1 < 0 := by omega
  have h := NP.P_filt hdA hdB n
  rwa [filt_neg D.wt hneg, Submodule.mem_bot] at h

/-- `P` against the vacuum on the right vanishes — bilinear restatement of `P_one_right`
for scalar multiples of the unit. -/
theorem P_smul_one (A : TR ι) (c : ℂ) (n : ℕ) : NP.P A (c • (1 : TR ι)) n = 0 := by
  have h : NP.P A (c • (1 : TR ι)) = c • NP.P A 1 := map_smul (NP.P A) c 1
  rw [h]
  change c • NP.P A 1 n = 0
  rw [NP.P_one_right, smul_zero]

/-- **The interface bracket extends `brk`**: on all divided powers of the
generators, `P` is the sesquilinear extension of the OPE table constructed in
`Core.NonlinearConformal` §5.  This is forced by `P_bot`, `P_Tleft`, `P_Tright`, and it
is why the L1 λ-bracket data feeds the L2 interface with no further input. -/
theorem P_gv_eq_brk (p q : GenIdx ι) : NP.P (gv p) (gv q) = brk D p q := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  -- Step 1: raise the right index.
  have hright : ∀ l : ℕ, NP.P (gv (i, 0)) (gv (j, l))
      = ((l.factorial : ℂ))⁻¹ • Rstep^[l] (D.ope i j) := by
    intro l
    induction l with
    | zero => rw [NP.P_bot]; simp
    | succ l ih =>
        have hgv : gv ((j, l + 1) : GenIdx ι) = (((l : ℂ) + 1))⁻¹ • Ttr (gv (j, l)) := by
          rw [Ttr_gv]
          change gv (j, l + 1) = (((l : ℂ) + 1))⁻¹ • (((l + 1 : ℕ) : ℂ) • gv (j, l + 1))
          rw [smul_smul]
          push_cast
          rw [inv_mul_cancel₀ (Nat.cast_add_one_ne_zero l), one_smul]
        have hmap : NP.P (gv (i, 0)) ((((l : ℂ) + 1))⁻¹ • Ttr (gv (j, l)))
            = (((l : ℂ) + 1))⁻¹ • NP.P (gv (i, 0)) (Ttr (gv (j, l))) :=
          map_smul (NP.P (gv (i, 0))) _ _
        rw [hgv, hmap, NP.P_Tright, ih, Rstep_smul, Function.iterate_succ_apply', smul_smul]
        congr 1
        rw [Nat.factorial_succ]
        push_cast
        have h1 : ((l.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
        field_simp
    -- Step 2: raise the left index.
  have hleft : ∀ k : ℕ, NP.P (gv (i, k)) (gv (j, l))
      = ((k.factorial : ℂ))⁻¹ • Lstep^[k] (NP.P (gv (i, 0)) (gv (j, l))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hgv : gv ((i, k + 1) : GenIdx ι) = (((k : ℂ) + 1))⁻¹ • Ttr (gv (i, k)) := by
          rw [Ttr_gv]
          change gv (i, k + 1) = (((k : ℂ) + 1))⁻¹ • (((k + 1 : ℕ) : ℂ) • gv (i, k + 1))
          rw [smul_smul]
          push_cast
          rw [inv_mul_cancel₀ (Nat.cast_add_one_ne_zero k), one_smul]
        have hmap : NP.P ((((k : ℂ) + 1))⁻¹ • Ttr (gv (i, k))) (gv (j, l))
            = (((k : ℂ) + 1))⁻¹ • NP.P (Ttr (gv (i, k))) (gv (j, l)) := by
          rw [map_smul]
          rfl
        rw [hgv, hmap, NP.P_Tleft, ih, Lstep_smul, Function.iterate_succ_apply', smul_smul]
        congr 1
        rw [Nat.factorial_succ]
        push_cast
        have h1 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
        field_simp
  rw [hleft, hright, Lstep_iterate_smul, smul_smul]
  funext n
  rw [brk]
  change (((k.factorial : ℂ))⁻¹ * ((l.factorial : ℂ))⁻¹)
        • Lstep^[k] (Rstep^[l] (D.ope i j)) n
      = (((k.factorial : ℂ)) * ((l.factorial : ℂ)))⁻¹
        • Lstep^[k] (Rstep^[l] (D.ope i j)) n
  rw [mul_inv]

/-- The interface bracket reproduces the OPE table on the bottom generators —
`P_gv_eq_brk` at `k = l = 0`. -/
theorem P_bot_eq_ope (i j : ι) (n : ℕ) :
    NP.P (gv (i, 0)) (gv (j, 0)) n = D.ope i j n := by
  rw [P_gv_eq_brk, brk_bot]

/-- The interface bracket of divided powers vanishes beyond the weight bound, like
`brk_vanish`. -/
theorem P_gv_vanish (p q : GenIdx ι) {n : ℕ}
    (h : wtIdx D.wt p + wtIdx D.wt q ≤ n) : NP.P (gv p) (gv q) n = 0 := by
  rw [P_gv_eq_brk]
  exact brk_vanish D p q h

/-! ## §4  The `NPGraded` mixin

Exact-weight gradedness of `N` and `P` for a conformal datum.  ⚠ **Not derivable from
the `NPExtension` fields**: it follows from the uniqueness half of the [DK]
recursion restricted to graded data, and until that recursion is formalised it is consumed strictly as
a named hypothesis.  (For `n` past the truncation range of `d₁ + d₂ - n - 1` the slice
already vanishes by `P_filt`, so the `ℕ`-subtraction imposes nothing — the
`IsConformal` precedent.) -/

/-- The graded refinement of the [DK] bounds for a conformal datum: `N` adds
exact weights, `P` at slice `n` has exact weight `d₁ + d₂ - n - 1`.  A `Prop` mixin,
deliberately separate from `NPExtension`; see the section docstring. -/
structure NPGraded (NP : NPExtension D) : Prop where
  /-- `N` maps `gr d₁ × gr d₂` into `gr (d₁ + d₂)`. -/
  N_gr : ∀ {d₁ d₂ : ℕ} {A B : TR ι}, A ∈ gr D.wt d₁ → B ∈ gr D.wt d₂ →
    NP.N A B ∈ gr D.wt (d₁ + d₂)
  /-- `P` at slice `n` maps `gr d₁ × gr d₂` into `gr (d₁ + d₂ - n - 1)`. -/
  P_gr : ∀ {d₁ d₂ : ℕ} {A B : TR ι}, A ∈ gr D.wt d₁ → B ∈ gr D.wt d₂ → ∀ n : ℕ,
    NP.P A B n ∈ gr D.wt (d₁ + d₂ - n - 1)

/-- Under the graded mixin, `N` maps anything against a positive-weight element into
the positive-weight span (right slot). -/
theorem N_mem_grPos_right {NP : NPExtension D} (hg : NPGraded NP) (A : TR ι) {x : TR ι}
    (hx : x ∈ grPos D.wt) : NP.N A x ∈ grPos D.wt := by
  rw [grPos] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      -- decompose `A` over the word basis
      have hA : A ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
        rw [(wbasis ι).span_eq]; trivial
      induction hA using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          have hmem := hg.N_gr (wbasis_mem_gr (wt := D.wt) (w := v) rfl)
            (wbasis_mem_gr (wt := D.wt) (w := w) rfl)
          exact gr_le_grPos (by omega) hmem
      | zero =>
          rw [map_zero]
          exact (Submodule.zero_mem _ : (0 : TR ι) ∈ grPos D.wt)
      | add a b _ _ ha hb =>
          have : NP.N (a + b) (wbasis ι w) = NP.N a (wbasis ι w) + NP.N b (wbasis ι w) := by
            rw [map_add]; rfl
          rw [this]
          exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
          have : NP.N (c • a) (wbasis ι w) = c • NP.N a (wbasis ι w) := by
            rw [map_smul]; rfl
          rw [this]
          exact Submodule.smul_mem _ c ha
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- Under the graded mixin, `N` maps a positive-weight element against anything into
the positive-weight span (left slot). -/
theorem N_mem_grPos_left {NP : NPExtension D} (hg : NPGraded NP) (A : TR ι) {x : TR ι}
    (hx : x ∈ grPos D.wt) : NP.N x A ∈ grPos D.wt := by
  rw [grPos] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hw
      have hA : A ∈ Submodule.span ℂ (Set.range (wbasis ι)) := by
        rw [(wbasis ι).span_eq]; trivial
      induction hA using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          have hmem := hg.N_gr (wbasis_mem_gr (wt := D.wt) (w := w) rfl)
            (wbasis_mem_gr (wt := D.wt) (w := v) rfl)
          exact gr_le_grPos (by omega) hmem
      | zero =>
          rw [map_zero]
          exact (Submodule.zero_mem _ : (0 : TR ι) ∈ grPos D.wt)
      | add a b _ _ ha hb =>
          rw [map_add]
          exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
          rw [map_smul]
          exact Submodule.smul_mem _ c ha
  | zero =>
      have : NP.N (0 : TR ι) A = 0 := by rw [map_zero]; rfl
      rw [this]
      exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
      have : NP.N (a + b) A = NP.N a A + NP.N b A := by rw [map_add]; rfl
      rw [this]
      exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
      have : NP.N (c • a) A = c • NP.N a A := by rw [map_smul]; rfl
      rw [this]
      exact Submodule.smul_mem _ c ha

end NPExtension

end VOA.NonlinearConformal
