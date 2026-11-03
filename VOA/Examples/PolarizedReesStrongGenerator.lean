/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.End
import VOA.Core.MinorPivots

/-!
# Polarized bi-Rees strong-generator interface and its finite-matrix payload

This file formalizes the strong-generator reduction of the polarized PBW-Rees
seam (the one-shape radial-metric argument) at
the same hypothesis-only level of honesty as
`VOA/Examples/ScreenedReesInterface.lean`.

## Status ladder (proven / packaged as hypothesis / not claimed)

**Proven (complete Lean proofs, no axioms beyond
`propext, Classical.choice, Quot.sound`):**

* `MinorPayload.sign_det_leadingPrincipal_pos` — the **main theorem**: the
  congruence-plus-sign normal form recorded by `MinorPayload.cross` (see its
  entry below for what that field does and does not encode of equation (9))
  forces, for every cumulative size `k`, the prescribed minor sign
  `0 < (-1)^(∑_{j<k} d j) · det (leadingPrincipal S k)`.  The exponent
  `∑_{j<k} d j` is the `a_k` of equation (13).  This signed-minor statement
  is the determinant-sign *gloss* of the layer statement (11); the
  `u`-valuation statement (12) (`ord_u det Gram = 2 ∑ j·m_j`) is **not**
  transcribed here — no `u`-valuation is formalized in this file.
* `MinorPayload.det_leadingPrincipal_ne_zero`,
  `MinorPayload.flag_restrict_nondegenerate` — every cumulative PBW subspace
  is nondegenerate (composition with
  `FlagMinors.nondegenerate_flag_iff_minors`).
* `MinorPayload.ratio_sign`,
  `schurOfLeading_posDef_of_ratios_of_pivot_ne_zero`,
  `schurOfLeading_negDef_of_ratios_of_pivot_ne_zero`,
  `MinorPayload.layer_schur_posDef_of_even`,
  `MinorPayload.layer_schur_negDef_of_odd`,
  `MinorPayload.layer_schur_definite` — the `(-1)^r`-definiteness of every
  constant-degree layer Schur complement, composed through the
  `Core.MinorPivots` machine (`posDef_of_det_leadingPrincipal_pos`,
  `leadingPrincipal_schurOfLeading`, `det_schurOfLeading_eq_div`,
  `det_leadingPrincipal_unitriangular_congr`).
* All witness lemmas of the final section (non-vacuity).

**Packaged as hypothesis (interface fields; NOT proven from VOA geometry):**

* `MinorPayload.cross` — the **load-bearing field**: an already-eliminated
  congruence-plus-sign normal form `Uᵀ * S * U = signDiag d * G` with `U`
  upper unitriangular and `G` positive definite.  This normal form is
  **intended** — expected, not formalized, not claimed — to be the output of
  the fraction-free block elimination of section 5 applied to equation (9):
  the opposite Rees factors `u^r (-u)^r = (-1)^r u^{2r}` should produce the
  diagonal sign `(-1)^{d i}`, and the positive-definite polarized Hodge side
  should produce `G`.  The elimination itself (the passage from the
  `u`-family (9) to this normal form, i.e. the Cauchy–Binet valuation
  argument (16)–(22)) is **not** formalized here.

  **Logical-distance disclosure**: over `ℝ`, `cross` is logically
  **equivalent** to the main theorem's minor-sign conclusion, not merely
  stronger.  Forward direction: the main theorem below (fully proven).
  Converse (elementary, **not** formalized in this file): if
  `0 < (-1)^(a_k) · D_k` for every `k`, then all leading minors are nonzero,
  symmetric Gaussian elimination (LDL) gives `Vᵀ S V = Δ` with `V`
  unitriangular and pivot `k` of sign `(-1)^(d k)` (since
  `a_{k+1} - a_k = d k`), and `U := V`, `G := signDiag d * Δ` (diagonal,
  positive definite) satisfies `cross`.  The main theorem is therefore an
  elementary repackaging of `cross` — frame invariance of the minors plus a
  diagonal sign factorization — at **no** logical distance; every genuine
  section-5 difficulty lives in producing `cross` for a concrete model,
  which this file does not do.
* All fields of `ReesVirasoroData` (the Rees Virasoro relations (32)) and of
  `ComparisonData` (the *shape* of items 1–4 of section 6.1 for the
  comparison Ψ of (33), including the reflected central coefficient (25) at
  the `[u²]`-coefficient level).  These are **interface-only**: no theorem
  in this file consumes them, exactly as the `Hypotheses` structure of
  `ScreenedReesInterface.lean` is interface-only.  Moreover the
  `ComparisonData` encoding of items 1–4 is **nominal**: the seam defines
  `grΨ`, `Lsharp` and `gen` in terms of `Ψ`, `L` and the vacuum, and this
  structure imposes none of those defining relations, so several hypothesis
  fields are trivially dischargeable independently of the rest — see the
  structure docstring for the explicit list (including the vacuity of
  `gr_bijective` under `grΨ := LinearMap.id`).  Field docstrings record
  intended readings, not relations the types impose.

**Not claimed:**

* No claim that any boundary Virasoro module satisfies `MinorPayload.cross`;
  producing that field for a concrete model is precisely the open polarized
  bi-Rees identity (9) of the seam document.
* No claim that the interface fields of `ReesVirasoroData`/`ComparisonData`
  imply `MinorPayload.cross`; section 6.1's graded-Nakayama argument from
  items 1–4 to (9) is **not** formalized.  `StrongGeneratorPackage` carries
  both groups of data side by side without deriving one from the other.
* No claim that instantiating `ComparisonData` certifies items 1–4 of
  section 6.1: as encoded the items are nominal (defining relations
  dropped), so an instance witnesses the *shape* of the data only.
* The LDL converse in the logical-distance disclosure above (minor signs ⟹
  `cross`) is **not** formalized; its status is: elementary standard linear
  algebra, stated here for honesty about what `cross` contains, used by no
  proof in this file.
* The witnesses instantiate the Virasoro interface only at central charge
  `c = 0` (a Rees–Witt action, noncommutative at `u = 1`) and with vanishing
  reflection pairing; no nonzero-central-charge representation is
  constructed.

## Load-bearing vs interface-only fields

For the main theorem the load-bearing fields are exactly
`MinorPayload.{S, d, U, G, hS, hU, hUdiag, hG, cross}`; the monotonicity
field `hd` and every field of `ReesVirasoroData`/`ComparisonData` are
interface data recording the section 6.1 reduction target.
-/

namespace VOA
namespace PolarizedRees

open VOA.FlagMinors
open Matrix

/-! ## §1  The Rees Virasoro relations (32) — interface only -/

/-- The Rees Virasoro relations, equation (32) of the seam document:
operators `L m` over a commutative ring `R` carrying the Rees parameter `u`,
with
`⁅L p, L q⁆ = u (p - q) • L (p+q) + u² · c (p³ - p)/12 · δ_{p,-q} • 1`.

The central coefficient `c (p³ - p)/12` is packaged integrally as a function
`central` with the defining relation `12 * central p = c * (p³ - p)`, so that
no division is postulated in `R`.

**Interface-only**: no theorem in this file consumes these fields; they are
the section 6.1 data a future construction must supply.  At `u = 0` the
relations degenerate to the commutative PBW-symbol algebra; at `u = 1` they
are the ordinary Virasoro relations. -/
structure ReesVirasoroData (R : Type*) (M : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] where
  /-- The Rees/PBW-length parameter `u`. -/
  u : R
  /-- The central charge. -/
  c : R
  /-- The integral packaging of `c (p³ - p)/12`. -/
  central : ℤ → R
  /-- The Rees Virasoro generators `𝖫_m = u L_m`. -/
  L : ℤ → Module.End R M
  /-- `12 · central p = c (p³ - p)`; the divided central coefficient without
  postulating `12⁻¹ ∈ R`. -/
  central_spec : ∀ p : ℤ, (12 : R) * central p = c * ((p : R) ^ 3 - (p : R))
  /-- Equation (32): the Rees Virasoro bracket, integral over `R`. -/
  bracket : ∀ p q : ℤ,
    L p * L q - L q * L p
      = (u * ((p : R) - (q : R))) • L (p + q)
        + (if p + q = 0 then u ^ 2 * central p else 0) • (1 : Module.End R M)

/-! ## §2  The comparison Ψ of (33), items 1–4 of section 6.1 — interface only -/

/-- The comparison map `Ψ : R_Hdg → Rees_PBW(V)^#` of equation (33), with
fields *shaped after* the four properties of section 6.1.

**Interface-only, and the encoding of items 1–4 is NOMINAL.**  No theorem in
this file consumes these fields.  The seam *defines* `grΨ` as the `u = 0`
specialization of `Ψ`, `Lsharp n` as the FHL/dual (`dualMap`) action of
`𝖫_n` on the PBW dual, and `gen m` as the strong-generator section
`u L₋ₘ 1`; this structure imposes **none** of those defining relations — the
fields are independent data whose docstrings record intended readings only.
Consequently, most hypothesis fields are trivially dischargeable
independently of the rest:

* `gr_bijective` is satisfied by `grΨ := LinearMap.id` for **any** `Ψ`, `u`,
  `c` — item 3 *as encoded here* carries no content about `Ψ`;
* `D := 0`, `Lsharp := 0` discharges `intertwines` and `reflect_adjoint`
  for any `Ψ`;
* `vacuum := Ψ extreme` discharges `extreme_to_vacuum` definitionally;
* `reflected_central` is the one exception at `c ≠ 0`: `gen := 0` or
  `pairing := 0` forces `c ((m:R)³ - m) = 0` for all `m ≥ 2` (over a
  characteristic-zero domain, `c = 0`).

Instantiating this structure therefore certifies almost none of section
6.1's content; a faithful formalization must carry a Rees
grading/specialization so the defining relations of `grΨ`, `Lsharp`, `gen`
can be *stated*.  That refinement is **not claimed** here; this structure is
the seam's reduction target recorded at the level of shape, exactly as
`ScreenedReesInterface.lean` records its hypotheses. -/
structure ComparisonData {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (V : ReesVirasoroData R M) (RH P : Type*)
    [AddCommGroup RH] [Module R RH] [AddCommGroup P] [Module R P] where
  /-- The comparison map (33). -/
  Ψ : RH →ₗ[R] P
  /-- The normalized Newton Ward operators `𝖣_m` on the Hodge Rees module
  (intended reading; no relation to `Ψ` or `V.L` is imposed by the type). -/
  D : ℤ → Module.End R RH
  /-- The `𝖫_m`-adjoint action on the Rees PBW dual, supplied as data
  (intended reading; it is *not* constructed here as an actual `dualMap` of
  `V.L`, and no relation to `V.L` is imposed by the type). -/
  Lsharp : ℤ → Module.End R P
  /-- The primitive extreme section. -/
  extreme : RH
  /-- The vacuum functional. -/
  vacuum : P
  /-- The special (`u = 0`) associated-graded comparison map (intended
  reading; the type imposes **no** relation to `Ψ`, so `gr_bijective` below
  is dischargeable by `grΨ := LinearMap.id` — see the structure
  docstring). -/
  grΨ : RH →ₗ[R] P
  /-- The reflected strong-generator sections, intended as `u L₋ₘ 1`
  (intended reading; no relation to `V.u`, `V.L` or a vacuum is imposed by
  the type). -/
  gen : ℤ → RH
  /-- The reflected FHL pairing, supplied directly at the level of its
  `[u²]` Rees coefficient on the strong-generator line, valued in `R`.  The
  `[u²]`-coefficient extraction itself (the "without dividing by `u`"
  content section 6.1 identifies as the missing work) is **not**
  formalized; this field is the already-extracted coefficient (intended
  reading; not imposed by the type). -/
  pairing : RH →ₗ[R] RH →ₗ[R] R
  /-- Item 1: `Ψ ∘ 𝖣_m = 𝖫_m^# ∘ Ψ`. -/
  intertwines : ∀ n : ℤ, Ψ.comp (D n) = (Lsharp n).comp Ψ
  /-- Item 2: `Ψ` sends the primitive extreme section to the
  vacuum functional. -/
  extreme_to_vacuum : Ψ extreme = vacuum
  /-- Item 3: the special associated-graded map is invertible
  (the Newton-selector map of the one-shape theorem). -/
  gr_bijective : Function.Bijective grΨ
  /-- Item 4, adjunction half: reflection sends `𝖣_n` to its
  FHL adjoint `𝖣_{-n}` against the reflected pairing. -/
  reflect_adjoint : ∀ (n : ℤ) (x y : RH),
    pairing ((D n) x) y = pairing x ((D (-n)) y)
  /-- Item 4, normalization half — the normalization equation, transcribed
  literally at the `[u²]`-coefficient level and stated integrally:
  `12 · [u²]B(u L₋ₘ 1, -u L₋ₙ 1) = -δ_{m,n} c (m³ - m)`.  There is
  deliberately **no** `u²` on the right-hand side: `pairing` is declared to
  be the `[u²]`-coefficient itself, and the seam's (25) reads
  `[u²]B = -δ_{m,n} c (m³ - m)/12` with no `u²`.  (A `u²`-multiplied form
  would be strictly weaker whenever `u` is not regular in `R` — e.g. it
  degenerates to `0 = 0` at `u = 0` — and would silently flatten the
  coefficient extraction that section 6.1 identifies as the missing work.)
  The smallest case `m = n = 2` gives `12 · pairing (gen 2) (gen 2) = -6c`,
  the `-c/2` coefficient normalization corresponding to (26)/(34). -/
  reflected_central : ∀ m n : ℤ, 2 ≤ m → 2 ≤ n →
    (12 : R) * pairing (gen m) (gen n)
      = if m = n then -(V.c * ((m : R) ^ 3 - (m : R))) else 0

/-! ## §3  The finite-matrix payload of the bi-Rees lemma (section 5) -/

/-- The diagonal sign matrix `diag ((-1)^(d 0), …, (-1)^(d (m-1)))` produced by
the opposite Rees factors `u^r (-u)^r = (-1)^r u^{2r}` of section 5. -/
def signDiag {n : ℕ} (d : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (-1 : ℝ) ^ d i

/-- The cumulative degree `∑_{j<k} d j` of the first `k` PBW basis vectors —
the exponent `a_k` of equation (13). -/
def cumulativeDegree {n : ℕ} (d : Fin n → ℕ) {k : ℕ} (hk : k ≤ n) : ℕ :=
  ∑ j : Fin k, d (Fin.castLE hk j)

/-- The finite-matrix payload of the polarized bi-Rees lemma of section 5.

The **load-bearing** field is `cross`: a congruence-plus-sign normal form
`Uᵀ S U = signDiag d · G` with `U` upper unitriangular (intended: the
regular, invertible-at-`u = 0` comparison frame) and `G` positive definite
(intended: the polarized Hodge side).  It is **intended** — expected, not
formalized — to be what the fraction-free block elimination of section 5
extracts from the cross-pairing identity (9); the elimination itself (the
Cauchy–Binet valuation argument (16)–(22)) is **not** formalized.
**Disclosure**: over `ℝ` this field is logically *equivalent* to the main
theorem's minor-sign conclusion (the converse is an elementary LDL argument,
not formalized here — see the module docstring), so the theorems below are
elementary repackagings of `cross`, at no logical distance from it.

`hd` (monotonicity of the PBW degree vector) is interface data recording the
degree-ordering of the basis; it is not consumed by the theorems, which take
the constant-degree window of each layer as an explicit hypothesis. -/
structure MinorPayload (n : ℕ) where
  /-- The PBW-degree-ordered vacuum-normalized real Gram (Shapovalov)
  matrix. -/
  S : Matrix (Fin n) (Fin n) ℝ
  /-- The PBW degree of each basis vector, in the fixed order. -/
  d : Fin n → ℕ
  /-- The unitriangular comparison frame (regular and invertible at
  `u = 0`). -/
  U : Matrix (Fin n) (Fin n) ℝ
  /-- The polarized Hodge Gram matrix (after the standard overall shift). -/
  G : Matrix (Fin n) (Fin n) ℝ
  /-- `S` is symmetric. -/
  hS : S.IsHermitian
  /-- The degree vector is monotone (the basis is degree-ordered).
  Interface-only for the theorems below. -/
  hd : Monotone d
  /-- `U` is upper triangular … -/
  hU : U.BlockTriangular id
  /-- … with unit diagonal. -/
  hUdiag : ∀ i, U i i = 1
  /-- The Hodge side is positive definite (Godfard polarization). -/
  hG : G.PosDef
  /-- **Load-bearing**: the congruence-plus-sign normal form, intended
  (expected, not formalized) as the eliminated content of the cross-pairing
  identity (9).  Over `ℝ` it is logically equivalent to the main theorem's
  minor-sign conclusion — see the structure and module docstrings. -/
  cross : Uᵀ * S * U = signDiag d * G

/-- Cutting the leading corner of a diagonal matrix gives the diagonal matrix
of the restricted entries. -/
theorem leadingPrincipal_diagonal {K : Type*} [Field K] {n : ℕ}
    (f : Fin n → K) {k : ℕ} (hk : k ≤ n) :
    leadingPrincipal (Matrix.diagonal f) hk
      = Matrix.diagonal fun j => f (Fin.castLE hk j) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [leadingPrincipal_apply]
  · rw [leadingPrincipal_apply,
      Matrix.diagonal_apply_ne _ fun hc => h (Fin.castLE_injective hk hc),
      Matrix.diagonal_apply_ne _ h]

/-- The leading `k`-minor of the sign matrix is `(-1)^(∑_{j<k} d j)`. -/
theorem det_leadingPrincipal_signDiag {n : ℕ} (d : Fin n → ℕ) {k : ℕ}
    (hk : k ≤ n) :
    (leadingPrincipal (signDiag d) hk).det
      = (-1 : ℝ) ^ cumulativeDegree d hk := by
  rw [signDiag, leadingPrincipal_diagonal, Matrix.det_diagonal,
    cumulativeDegree]
  exact Finset.prod_pow_eq_pow_sum _ _ _

namespace MinorPayload

variable {n : ℕ}

/-- **The main theorem**: the payload forces, for every cumulative size
`k`, the sign `0 < (-1)^(∑_{j<k} d j) · det (leadingPrincipal S k)`, the
exponent being the `a_k` of equation (13).  This is the determinant-sign
*gloss* of the layer statement (11); the `u`-valuation statement (12) is not
transcribed (same attribution as the module docstring — the two must be read
together).  **Logical status**: `cross` is equivalent over `ℝ` to this
conclusion (module docstring), so this theorem is the short, fully proven
forward direction of that equivalence, not a result at logical distance
from its hypothesis.

Proof: `det_leadingPrincipal_unitriangular_congr` (frame invariance of the
minors under the unitriangular comparison), then the leading corner of
`signDiag d · G` factors because the diagonal factor is triangular, giving
`det = (-1)^(∑ d) · det (leadingPrincipal G)` with the second factor positive
by Sylvester's easy direction for the positive-definite Hodge side. -/
theorem sign_det_leadingPrincipal_pos (Q : MinorPayload n) {k : ℕ}
    (hk : k ≤ n) :
    0 < (-1 : ℝ) ^ cumulativeDegree Q.d hk
        * (leadingPrincipal Q.S hk).det := by
  have hcongr := det_leadingPrincipal_unitriangular_congr Q.S Q.hU Q.hUdiag hk
  have htri : (signDiag Q.d)ᵀ.BlockTriangular id := by
    rw [signDiag, Matrix.diagonal_transpose]
    exact Matrix.blockTriangular_diagonal _
  have hsplit : leadingPrincipal (signDiag Q.d * Q.G) hk
      = leadingPrincipal (signDiag Q.d) hk * leadingPrincipal Q.G hk :=
    leadingPrincipal_mul_left_of_transpose_blockTriangular _ _ htri hk
  have hGpos : 0 < (leadingPrincipal Q.G hk).det :=
    (posDef_leadingPrincipal Q.hG hk).det_pos
  have key : (leadingPrincipal Q.S hk).det
      = (-1 : ℝ) ^ cumulativeDegree Q.d hk
        * (leadingPrincipal Q.G hk).det := by
    rw [← hcongr, Q.cross, hsplit, Matrix.det_mul,
      det_leadingPrincipal_signDiag]
  rw [key, ← mul_assoc]
  have hsq : (-1 : ℝ) ^ cumulativeDegree Q.d hk
      * (-1 : ℝ) ^ cumulativeDegree Q.d hk = 1 := by
    rcases Nat.even_or_odd (cumulativeDegree Q.d hk) with h | h <;>
      rw [h.neg_one_pow] <;> norm_num
  rw [hsq, one_mul]
  exact hGpos

/-- Every cumulative leading principal minor of the payload is nonzero. -/
theorem det_leadingPrincipal_ne_zero (Q : MinorPayload n) {k : ℕ}
    (hk : k ≤ n) : (leadingPrincipal Q.S hk).det ≠ 0 := by
  intro h0
  have h := Q.sign_det_leadingPrincipal_pos hk
  rw [h0, mul_zero] at h
  exact lt_irrefl 0 h

/-- Composition with `FlagMinors.nondegenerate_flag_iff_minors`: for any
flag refining a degree-ordered basis whose Gram matrix is the payload matrix
`S`, the form is nondegenerate on **every** step of the flag — every
cumulative PBW subspace is nondegenerate, the first conclusion of the
bi-Rees lemma of section 5. -/
theorem flag_restrict_nondegenerate (Q : MinorPayload n) {E : Type*}
    [AddCommGroup E] [Module ℝ E] {F : ℕ → Submodule ℝ E}
    {e : Module.Basis (Fin n) ℝ E} (h : RefinesBasis F e)
    (β : LinearMap.BilinForm ℝ E)
    (hβ : LinearMap.BilinForm.toMatrix e β = Q.S) :
    ∀ p, ((β.restrict (F p)).Nondegenerate) :=
  (nondegenerate_flag_iff_minors h β).mpr fun p => by
    rw [hβ]
    exact Q.det_leadingPrincipal_ne_zero (h.dim_le p)

end MinorPayload

/-! ### Layer definiteness through the `Core.MinorPivots` machine

The two lemmas below are the `MinorPivots` layer lemmas
(`schurOfLeading_posDef_of_sign_ratios` / `schurOfLeading_negDef_of_sign_ratios`)
with the pivot hypothesis relaxed from `0 < D_l` to `D_l ≠ 0` (the ratio
hypotheses already carry all the sign information); their proofs are the
`MinorPivots` proofs, composed from `posDef_of_det_leadingPrincipal_pos`,
`isHermitian_schurOfLeading`, `leadingPrincipal_schurOfLeading` and
`det_schurOfLeading_eq_div`.  The names carry the suffix
`…_of_ratios_of_pivot_ne_zero` precisely so they cannot be confused with the
Core names they relax.

**Consolidation note**: the Core layer lemmas carry the same relaxed
hypothesis `D_l ≠ 0`, so these two are duplicates of
`FlagMinors.schurOfLeading_posDef_of_sign_ratios` /
`FlagMinors.schurOfLeading_negDef_of_sign_ratios`, kept for their existing
callers. -/

/-- The layer lemma (positive case) with a nondegenerate — not necessarily
positive — leading pivot: if every relative minor ratio in `(l, l+j]` is
positive, the layer Schur complement is positive definite. -/
theorem schurOfLeading_posDef_of_ratios_of_pivot_ne_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (l j : ℕ)
    (hlj : l + j ≤ n) (hl : l ≤ n)
    (hDl : (leadingPrincipal M hl).det ≠ 0)
    (hratios : ∀ i (_ : 0 < i) (hli : l + i ≤ n), i ≤ j →
      0 < (leadingPrincipal M hli).det / (leadingPrincipal M hl).det) :
    (schurOfLeading M l j hlj).PosDef := by
  apply posDef_of_det_leadingPrincipal_pos
  · exact isHermitian_schurOfLeading hM l j hlj
  · intro i hi hi0
    have hli : l + i ≤ n := le_trans (by omega) hlj
    rw [leadingPrincipal_schurOfLeading M l i j hi hlj hli,
      det_schurOfLeading_eq_div M l i hli hl hDl]
    exact hratios i hi0 hli hi

/-- The layer lemma (negative case) with a nondegenerate — not necessarily
positive — leading pivot: if every relative minor ratio in `(l, l+j]` has the
alternating sign `(-1)^i`, the layer Schur complement is negative definite. -/
theorem schurOfLeading_negDef_of_ratios_of_pivot_ne_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (l j : ℕ)
    (hlj : l + j ≤ n) (hl : l ≤ n)
    (hDl : (leadingPrincipal M hl).det ≠ 0)
    (hratios : ∀ i (_ : 0 < i) (hli : l + i ≤ n), i ≤ j →
      0 < (-1 : ℝ) ^ i
        * ((leadingPrincipal M hli).det / (leadingPrincipal M hl).det)) :
    (-(schurOfLeading M l j hlj)).PosDef := by
  apply posDef_of_det_leadingPrincipal_pos
  · simpa using (isHermitian_schurOfLeading hM l j hlj).neg
  · intro i hi hi0
    have hli : l + i ≤ n := le_trans (by omega) hlj
    have hneg : leadingPrincipal (-(schurOfLeading M l j hlj)) hi
        = -(leadingPrincipal (schurOfLeading M l j hlj) hi) := rfl
    rw [hneg, Matrix.det_neg,
      leadingPrincipal_schurOfLeading M l i j hi hlj hli,
      det_schurOfLeading_eq_div M l i hli hl hDl]
    have hrat := hratios i hi0 hli hi
    rw [Fintype.card_fin]
    exact hrat.trans_eq (by ring)

namespace MinorPayload

variable {n : ℕ}

/-- The signed minor-ratio computation: on a window `[l, l+i)` of constant
PBW degree `r`, the relative minor ratio has the sign `(-1)^(i·r)` forced by
the opposite Rees factors. -/
theorem ratio_sign (Q : MinorPayload n) {l i r : ℕ}
    (hli : l + i ≤ n) (hl : l ≤ n)
    (hlayer : ∀ t : Fin i, Q.d (Fin.castLE hli (Fin.natAdd l t)) = r) :
    0 < (-1 : ℝ) ^ (i * r)
      * ((leadingPrincipal Q.S hli).det / (leadingPrincipal Q.S hl).det) := by
  have hsum : cumulativeDegree Q.d hli = cumulativeDegree Q.d hl + i * r := by
    have hsplit := Fin.sum_univ_add
      (f := fun j : Fin (l + i) => Q.d (Fin.castLE hli j))
    have hfirst : (∑ j : Fin l, Q.d (Fin.castLE hli (Fin.castAdd i j)))
        = ∑ j : Fin l, Q.d (Fin.castLE hl j) :=
      Finset.sum_congr rfl fun j _ => congrArg Q.d (Fin.ext rfl)
    have hsecond : (∑ t : Fin i, Q.d (Fin.castLE hli (Fin.natAdd l t)))
        = i * r := by
      calc (∑ t : Fin i, Q.d (Fin.castLE hli (Fin.natAdd l t)))
          = ∑ _t : Fin i, r := Finset.sum_congr rfl fun t _ => hlayer t
        _ = i * r := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul]
    unfold cumulativeDegree
    rw [hsplit, hfirst, hsecond]
  have h1 := Q.sign_det_leadingPrincipal_pos hl
  have h2 := Q.sign_det_leadingPrincipal_pos hli
  rw [hsum, pow_add] at h2
  set Dl := (leadingPrincipal Q.S hl).det with hDl
  set Dli := (leadingPrincipal Q.S hli).det with hDli
  have hfactor : (-1 : ℝ) ^ (i * r) * (Dli / Dl)
      = ((-1 : ℝ) ^ (i * r) * Dli) / Dl := by ring
  rw [hfactor]
  rcases Nat.even_or_odd (cumulativeDegree Q.d hl) with hpar | hpar
  · rw [hpar.neg_one_pow, one_mul] at h1 h2
    exact div_pos h2 h1
  · rw [hpar.neg_one_pow] at h1 h2
    have h1' : Dl < 0 := by nlinarith
    have h2' : (-1 : ℝ) ^ (i * r) * Dli < 0 := by nlinarith
    exact div_pos_iff.mpr (Or.inr ⟨h2', h1'⟩)

/-- **Layer definiteness, even case**: on a degree layer of even PBW
degree `r`, the layer Schur complement of the payload Gram matrix is
positive definite. -/
theorem layer_schur_posDef_of_even (Q : MinorPayload n) {l j r : ℕ}
    (hlj : l + j ≤ n) (hr : Even r)
    (hlayer : ∀ t : Fin j, Q.d (tailEmb l j hlj t) = r) :
    (schurOfLeading Q.S l j hlj).PosDef := by
  have hl : l ≤ n := le_trans (Nat.le_add_right l j) hlj
  apply schurOfLeading_posDef_of_ratios_of_pivot_ne_zero Q.S Q.hS l j hlj hl
    (Q.det_leadingPrincipal_ne_zero hl)
  intro i hi0 hli hij
  have hlayer' : ∀ t : Fin i, Q.d (Fin.castLE hli (Fin.natAdd l t)) = r := by
    intro t
    have h := hlayer ⟨t.1, lt_of_lt_of_le t.2 hij⟩
    have heq : Fin.castLE hli (Fin.natAdd l t)
        = tailEmb l j hlj ⟨t.1, lt_of_lt_of_le t.2 hij⟩ := Fin.ext rfl
    rw [heq]
    exact h
  have hratio := Q.ratio_sign hli hl hlayer'
  rwa [(hr.mul_left i).neg_one_pow, one_mul] at hratio

/-- **Layer definiteness, odd case**: on a degree layer of odd PBW degree
`r`, the layer Schur complement of the payload Gram matrix is negative
definite. -/
theorem layer_schur_negDef_of_odd (Q : MinorPayload n) {l j r : ℕ}
    (hlj : l + j ≤ n) (hr : Odd r)
    (hlayer : ∀ t : Fin j, Q.d (tailEmb l j hlj t) = r) :
    (-(schurOfLeading Q.S l j hlj)).PosDef := by
  have hl : l ≤ n := le_trans (Nat.le_add_right l j) hlj
  apply schurOfLeading_negDef_of_ratios_of_pivot_ne_zero Q.S Q.hS l j hlj hl
    (Q.det_leadingPrincipal_ne_zero hl)
  intro i hi0 hli hij
  have hlayer' : ∀ t : Fin i, Q.d (Fin.castLE hli (Fin.natAdd l t)) = r := by
    intro t
    have h := hlayer ⟨t.1, lt_of_lt_of_le t.2 hij⟩
    have heq : Fin.castLE hli (Fin.natAdd l t)
        = tailEmb l j hlj ⟨t.1, lt_of_lt_of_le t.2 hij⟩ := Fin.ext rfl
    rw [heq]
    exact h
  have hratio := Q.ratio_sign hli hl hlayer'
  rwa [mul_comm i r, pow_mul, hr.neg_one_pow] at hratio

/-- **The `(-1)^r`-definiteness of every degree layer** (equation (11)):
on a constant-degree window `[l, l+j)` of PBW degree `r`, the matrix
`(-1)^r · Schur_r(S)` is positive definite. -/
theorem layer_schur_definite (Q : MinorPayload n) {l j r : ℕ}
    (hlj : l + j ≤ n)
    (hlayer : ∀ t : Fin j, Q.d (tailEmb l j hlj t) = r) :
    (((-1 : ℝ) ^ r) • schurOfLeading Q.S l j hlj).PosDef := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_one_pow, one_smul]
    exact Q.layer_schur_posDef_of_even hlj hr hlayer
  · rw [hr.neg_one_pow, neg_one_smul]
    exact Q.layer_schur_negDef_of_odd hlj hr hlayer

end MinorPayload

/-! ## §4  The bundled strong-generator package -/

/-- The full section 6.1 package: the Rees Virasoro relations (32), the
comparison data (33) with items 1–4, and the finite-matrix payload of the
bi-Rees lemma.

The three groups of data sit side by side.  **No implication between them is
claimed**: the graded-Nakayama argument of section 6.1 deriving the payload's
`cross` field from the comparison fields is not formalized.  The theorems
below consume only `payload`. -/
structure StrongGeneratorPackage (R : Type*) [CommRing R]
    (M RH P : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup RH] [Module R RH] [AddCommGroup P] [Module R P]
    (dim : ℕ) where
  /-- The Rees Virasoro relations (32) — interface data. -/
  rees : ReesVirasoroData R M
  /-- The comparison (33) with items 1–4 of section 6.1 — interface data. -/
  comparison : ComparisonData rees RH P
  /-- The finite-matrix payload of the bi-Rees lemma — load-bearing. -/
  payload : MinorPayload dim

namespace StrongGeneratorPackage

variable {R : Type*} [CommRing R] {M RH P : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup RH] [Module R RH]
  [AddCommGroup P] [Module R P] {dim : ℕ}

/-- The package implies the minor-sign hypotheses consumed by
`Core.MinorPivots`, for every cumulative size `k`. -/
theorem sign_det_leadingPrincipal_pos
    (pkg : StrongGeneratorPackage R M RH P dim) {k : ℕ} (hk : k ≤ dim) :
    0 < (-1 : ℝ) ^ cumulativeDegree pkg.payload.d hk
        * (leadingPrincipal pkg.payload.S hk).det :=
  pkg.payload.sign_det_leadingPrincipal_pos hk

/-- The package implies the `(-1)^r`-definiteness of every degree layer. -/
theorem layer_schur_definite
    (pkg : StrongGeneratorPackage R M RH P dim) {l j r : ℕ}
    (hlj : l + j ≤ dim)
    (hlayer : ∀ t : Fin j, pkg.payload.d (tailEmb l j hlj t) = r) :
    (((-1 : ℝ) ^ r) • schurOfLeading pkg.payload.S l j hlj).PosDef :=
  pkg.payload.layer_schur_definite hlj hlayer

end StrongGeneratorPackage

/-! ## §5  Non-vacuity witnesses

The interfaces and the payload are instantiable, and the theorems'
conclusions are nontrivial on the instances.

* `wittEnd`/`wittRees`: the Rees–Witt action `𝖫_m = u L_m` with
  `(L_m f) k = (m - k) f (k - m)` on `ℤ → ℝ` (the coefficient action of
  `-t^{m+1} d/dt` on Laurent monomials), at `u = 1`, `c = 0`.  It satisfies
  (32) exactly and is genuinely noncommutative
  (`wittRees_L_noncommutative`) — the bracket field is not vacuous.
  **Honest limitation**: the central charge is `0`; no `c ≠ 0`
  representation is constructed.
* `wittComparison`: comparison data over `wittRees` with `Ψ = id` (so item 3
  is a genuine bijection) and vanishing reflection pairing (consistent since
  `c = 0`).
* `toyPayload`: an explicit `3 × 3` payload with degrees `(0, 1, 2)`, a
  nontrivial unitriangular frame, and Gram matrix
  `S = !![1, -1, 1; -1, 0, 0; 1, 0, 1]` whose cumulative minors are
  `(1, -1, -1)` — the main theorem's conclusion on it includes a **strictly
  negative** minor (`toyPayload_minor_two_neg`) and a **negative-definite**
  odd layer (`toyPayload_layer_one_negDef`), so the conclusions are not
  vacuously sign-positive. -/

/-- The Witt coefficient action on Laurent-monomial coefficient functions:
`(wittEnd m f) k = (m - k) · f (k - m)`. -/
def wittEnd (p : ℤ) : Module.End ℝ (ℤ → ℝ) where
  toFun f := fun k => ((p - k : ℤ) : ℝ) * f (k - p)
  map_add' f g := by
    funext k
    simp [mul_add]
  map_smul' a f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem wittEnd_apply (p : ℤ) (f : ℤ → ℝ) (k : ℤ) :
    wittEnd p f k = ((p - k : ℤ) : ℝ) * f (k - p) := rfl

/-- The Rees–Witt witness for `ReesVirasoroData`: `u = 1`, `c = 0`,
`L = wittEnd`.  The bracket (32) holds exactly (with vanishing central
term). -/
def wittRees : ReesVirasoroData ℝ (ℤ → ℝ) where
  u := 1
  c := 0
  central _ := 0
  L := wittEnd
  central_spec p := by simp
  bracket p q := by
    apply LinearMap.ext
    intro f
    funext k
    have hif : (if p + q = 0 then (1 : ℝ) ^ 2 * 0 else 0) = 0 := by
      split <;> ring
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, wittEnd_apply, hif, one_mul]
    have h1 : k - p - q = k - (p + q) := by ring
    have h2 : k - q - p = k - (p + q) := by ring
    rw [h1, h2]
    push_cast
    ring

/-- Every Witt operator is nonzero (evaluate on the delta function at `1`). -/
theorem wittEnd_ne_zero (p : ℤ) : wittEnd p ≠ 0 := by
  intro h
  have h1 := congrFun (LinearMap.congr_fun h
    (fun k => if k = 1 then (1 : ℝ) else 0)) (p + 1)
  have harg : p + 1 - p = (1 : ℤ) := by ring
  rw [wittEnd_apply, harg] at h1
  norm_num at h1

/-- The Rees–Witt witness is genuinely noncommutative at `u = 1`:
`𝖫₂ 𝖫₁ ≠ 𝖫₁ 𝖫₂`.  The bracket field of `ReesVirasoroData` is therefore not
satisfied for trivial reasons. -/
theorem wittRees_L_noncommutative :
    wittRees.L 2 * wittRees.L 1 ≠ wittRees.L 1 * wittRees.L 2 := by
  intro h
  have hb := wittRees.bracket 2 1
  rw [h, sub_self] at hb
  have hif : (if (2 : ℤ) + 1 = 0 then wittRees.u ^ 2 * wittRees.central 2
      else 0) = 0 := by norm_num
  rw [hif, zero_smul, add_zero] at hb
  have hcoeff : wittRees.u * (((2 : ℤ) : ℝ) - ((1 : ℤ) : ℝ)) = 1 := by
    have hu : wittRees.u = 1 := rfl
    rw [hu]
    norm_num
  rw [hcoeff, one_smul] at hb
  have h3 : (2 : ℤ) + 1 = 3 := by norm_num
  rw [h3] at hb
  exact wittEnd_ne_zero 3 hb.symm

/-- Comparison-data witness over `wittRees`: `Ψ = id` (item 3 is a genuine
bijection), Ward operators `D = Lsharp = wittRees.L`, delta-function extreme
section and vacuum functional, and vanishing reflection pairing — consistent
with equation (25) because the witness has `c = 0`. -/
def wittComparison : ComparisonData wittRees (ℤ → ℝ) (ℤ → ℝ) where
  Ψ := LinearMap.id
  D := wittRees.L
  Lsharp := wittRees.L
  extreme := fun k => if k = 0 then 1 else 0
  vacuum := fun k => if k = 0 then 1 else 0
  grΨ := LinearMap.id
  gen _ := 0
  pairing := 0
  intertwines n := by
    ext f
    rfl
  extreme_to_vacuum := rfl
  gr_bijective := Function.bijective_id
  reflect_adjoint n x y := by simp
  reflected_central p q hp hq := by
    simp only [LinearMap.zero_apply, mul_zero]
    split <;> simp [wittRees]

/-- The explicit `3 × 3` payload witness: degrees `(0, 1, 2)`, nontrivial
unitriangular frame `U`, Hodge side `G = 1`, and
`S = (U⁻¹)ᵀ · diag(1, -1, 1) · U⁻¹` written out.  Cumulative minors of `S`:
`(1, -1, -1)` — the signs `(-1)^0, (-1)^{0+1}, (-1)^{0+1+2}`. -/
def toyPayload : MinorPayload 3 where
  S := !![1, -1, 1; -1, 0, 0; 1, 0, 1]
  d := fun i => (i : ℕ)
  U := !![1, 1, 0; 0, 1, 1; 0, 0, 1]
  G := 1
  hS := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  hd := fun _ _ h => h
  hU := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  hUdiag := by
    intro i
    fin_cases i <;> norm_num
  hG := Matrix.PosDef.one
  cross := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [signDiag, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.diagonal_apply]

/-- The bundled package witness: the three groups of data are jointly
instantiable. -/
def toyPackage : StrongGeneratorPackage ℝ (ℤ → ℝ) (ℤ → ℝ) (ℤ → ℝ) 3 where
  rees := wittRees
  comparison := wittComparison
  payload := toyPayload

/-- Non-vacuity of the main theorem's conclusion: on the toy payload the
cumulative `2`-minor is **strictly negative** (the theorem forces a genuine
sign, not blanket positivity). -/
theorem toyPayload_minor_two_neg :
    (leadingPrincipal toyPayload.S (by omega : (2 : ℕ) ≤ 3)).det < 0 := by
  have h := toyPayload.sign_det_leadingPrincipal_pos
    (by omega : (2 : ℕ) ≤ 3)
  have hc : cumulativeDegree toyPayload.d (by omega : (2 : ℕ) ≤ 3) = 1 := by
    decide
  rw [hc, pow_one] at h
  linarith

/-- Non-vacuity of layer definiteness: the odd (degree `1`) layer of the toy
payload has **negative-definite** Schur complement. -/
theorem toyPayload_layer_one_negDef :
    (-(schurOfLeading toyPayload.S 1 1 (by omega))).PosDef :=
  toyPayload.layer_schur_negDef_of_odd (by omega) odd_one
    (fun t => by fin_cases t; rfl)

end PolarizedRees
end VOA
