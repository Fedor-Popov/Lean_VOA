/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
/-
Symmetry of the invariant bilinear form (complements Core/BilinearForm.lean).

Imports Core.BilinearForm and Core.SkewSymmetry.
Question: can ∀ B : InvariantForm W, IsSymmetric B be proved from skew + Virasoro-adjointness?

Answer: symmetry of a GENERAL InvariantForm is NOT derivable from
Virasoro-adjointness + skew alone — it needs the FULL generating-function invariance
(general-mode adjointness via e^{zL₁}(-z⁻²)^{L₀}).  What IS reachable axiom-clean-mod-skew:
the skew specialisations on 𝒱₁ (the (0)- and (1)-products), giving
  • zeroMode_antisymm_grading1 : u₍₀₎v + v₍₀₎u = 0 on 𝒱₁           (antisymmetry)
  • oneMode_symm_grading1     : u₍₁₎v = v₍₁₎u on 𝒱₁                (symmetry of the 𝒱₁ pairing)
and from the latter, the form-level partial symmetry on 𝒱₁ under the
normalisation hypothesis (u|v)=u₍₁₎v (5.1.12b):
  • isSymmetric_grading1_of_eval

## Status
Complete & `sorry`-free / axiom-free.  The file's targets — the 𝒱₁ skew
specialisations `zeroMode_antisymm_grading1`, `oneMode_symm_grading1`, and the conditional
form symmetry `isSymmetric_grading1_of_eval` — are all proved from skew-symmetry
(`Core.SkewSymmetry.skew_mode`), `#print axioms = [propext, Classical.choice, Quot.sound]`.
(The full form symmetry `∀ B, IsSymmetric B`, which needs full invariance, is reachable via
`Core.BilinearForm.InvariantForm.IsFullyInvariant`; it is outside this file's stated targets.)
-/
import VOA.Core.BilinearForm
import VOA.Core.SkewSymmetry

namespace VOA

open Module (End)
open scoped BigOperators

universe u

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Bridge: `(W.Y v) k u` as a `smul` -/

/-- `(W.Y v) k u = v₍-k-1₎ u`, i.e. the `z^k`-coefficient is the `(-k-1)`-mode. -/
theorem Y_apply_eq_smul (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) (k : ℤ) (u : 𝒱) :
    (W.Y v) k u = W.smul v (-k - 1) u := by
  rw [PreVertexAlgebra.smul_def, mode_apply, show (-(-k - 1) - 1 : ℤ) = k by ring]

/-! ## A vanishing helper: a `smul` from a `< 0`-grade vector is `0` -/

/-- If a vector lies in a negative grade, it is `0` (VOA4 positivity). -/
theorem eq_zero_of_mem_neg_grading (W : VertexOperatorAlgebra 𝒱) {k : ℤ} (hk : k < 0)
    {x : 𝒱} (hx : x ∈ W.grading k) : x = 0 := by
  rw [W.positivity k hk] at hx
  exact (Submodule.mem_bot ℂ).mp hx

/-! ## The skew finsum collapsed on 𝒱₁ at n = 0 and n = 1

For `u, v ∈ 𝒱₁`, `skew_mode` writes `u₍ₙ₎v = ∑ⱼ (1/j!) sgn(-n-1-j) Tʲ ((Y v)(-n-1-j) u)`,
with `(Y v)(-n-1-j) u = v₍n+j₎u ∈ 𝒱_{1+1-(n+j)-1} = 𝒱_{1-n-j}`.  Only finitely many `j`
survive (positivity + `T𝟙=0`).  We evaluate the finsum directly. -/

/-- The generic skew-finsum term for `u, v ∈ 𝒱₁`, at outer mode `n`, summand `j`. -/
private noncomputable def skewTerm (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (n : ℤ) (j : ℕ) : 𝒱 :=
  ((j.factorial : ℂ)⁻¹) • (sgn (-n - 1 - j)) •
    ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-n - 1 - j) u))

/-- For `u, v ∈ 𝒱₁`, the skew summand vanishes once the produced vector sits below grade 0.
Concretely `(Y v)(-n-1-j) u = v₍n+j₎u ∈ 𝒱_{1-n-j}`, which is `0` when `1 - n - j < 0`. -/
theorem skewTerm_eq_zero_of_lt (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) (n : ℤ) {j : ℕ} (hj : 1 - n - j < 0) :
    skewTerm W u v n j = 0 := by
  have hmem : (W.Y v) (-n - 1 - j) u ∈ W.grading (1 - n - (j : ℤ)) := by
    have h := W.smul_mem_grading hv hu (n + j)
    rw [show (1 + 1 - (n + (j : ℤ)) - 1 : ℤ) = 1 - n - j by ring] at h
    rw [Y_apply_eq_smul, show (-(-n - 1 - (j : ℤ)) - 1 : ℤ) = n + j by ring]
    exact h
  have hz : (W.Y v) (-n - 1 - j) u = 0 := eq_zero_of_mem_neg_grading W hj hmem
  rw [skewTerm, hz, map_zero, smul_zero, smul_zero]

/-! ### n = 0 on 𝒱₁ : `u₍₀₎v + v₍₀₎u = 0`

`skew_mode` at `n=0` gives `u₍₀₎v = ∑ⱼ skewTerm u v 0 j`.
- `j=0`: `(1/0!) sgn(-1) T⁰ ((Y v)(-1) u) = - v₍₀₎u`  (since `(Y v)(-1) u = v₍₀₎u`).
- `j=1`: `(1/1!) sgn(-2) T¹ ((Y v)(-2) u) = T(v₍₁₎u)`; but `v₍₁₎u ∈ 𝒱₀ = ℂ𝟙` and `T𝟙=0`
  — more directly, `1 - 0 - 1 = 0` is NOT `< 0`, so this term needs the `T𝟙=0` argument.
- `j≥2`: `1 - 0 - j < 0`, vanish by `skewTerm_eq_zero_of_lt`. -/

/-- The `j=1`, `n=0` skew term on 𝒱₁ vanishes: it is `T(v₍₁₎u)` with `v₍₁₎u ∈ 𝒱₀ = ℂ𝟙`
and `T𝟙 = L₋₁𝟙 = 0`.  We use `T` linearity + `vacuum_grade` (`𝒱₀ = ℂ∙𝟙`) + `T_vacuum`. -/
theorem skewTerm_n0_j1_eq_zero (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    skewTerm W u v 0 1 = 0 := by
  -- the produced vector lies in 𝒱₀ = ℂ∙𝟙
  have hmem : (W.Y v) (-0 - 1 - (1 : ℕ)) u ∈ W.grading 0 := by
    have h := W.smul_mem_grading hv hu (0 + 1)
    rw [show (1 + 1 - (0 + (1 : ℤ)) - 1 : ℤ) = 0 by ring] at h
    rw [Y_apply_eq_smul, show (-((-0 : ℤ) - 1 - (1 : ℕ)) - 1 : ℤ) = 0 + 1 by norm_num]
    exact h
  -- so it is a scalar multiple of the vacuum, and T kills it
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [skewTerm]
  have hT : (W.toPreVertexAlgebra.T ^ (1 : ℕ)) ((W.Y v) (-0 - 1 - (1 : ℕ)) u) = 0 := by
    rw [pow_one, ← hc, map_smul, PreVertexAlgebra.T_vacuum, smul_zero]
  rw [hT, smul_zero, smul_zero]

/-- **Antisymmetry of the `(0)`-product on 𝒱₁** (skew, Gannon 5.1.8 specialised):
`u₍₀₎v + v₍₀₎u = 0` for `u, v ∈ 𝒱₁`.  This is the coefficient form of skew the `𝒱₁`
Lie bracket consumes (`bracketV1_antisymm_of_skew`). -/
theorem zeroMode_antisymm_grading1 (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 0 v + W.smul v 0 u = 0 := by
  have hskew := skew_mode W u v 0
  -- collapse the finsum to the single j=0 term
  have hsupp : ∀ j : ℕ, j ≠ 0 → skewTerm W u v 0 j = 0 := by
    intro j hj0
    match j, hj0 with
    | 1, _ => exact skewTerm_n0_j1_eq_zero W hu hv
    | (Nat.succ (Nat.succ k)), _ =>
        refine skewTerm_eq_zero_of_lt W hu hv 0 ?_
        push_cast; omega
  have hcollapse :
      (∑ᶠ j : ℕ, skewTerm W u v 0 j) = skewTerm W u v 0 0 :=
    finsum_eq_single _ 0 hsupp
  -- rewrite hskew through skewTerm
  have hrw : (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-(0:ℤ) - 1 - j)) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(0:ℤ) - 1 - j) u)))
      = ∑ᶠ j : ℕ, skewTerm W u v 0 j := by
    refine finsum_congr fun j => by rw [skewTerm]
  rw [hrw, hcollapse, skewTerm] at hskew
  -- skewTerm u v 0 0 = (1/0!) sgn(-1) T⁰ ((Y v)(-1) u) = - v₍₀₎u
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    show (-(0:ℤ) - 1 - (0:ℕ)) = -1 by norm_num,
    show (sgn (-1 : ℤ)) = -1 by rw [sgn, if_neg (by decide)],
    Y_apply_eq_smul, show (-(-1 : ℤ) - 1) = 0 by ring, neg_one_smul] at hskew
  -- hskew : u₍₀₎v = - v₍₀₎u
  rw [hskew, neg_add_cancel]

/-! ### n = 1 on 𝒱₁ : `u₍₁₎v = v₍₁₎u` (symmetry of the (1)-pairing)

`skew_mode` at `n=1`: `u₍₁₎v = ∑ⱼ skewTerm u v 1 j`.
- `j=0`: `(1/0!) sgn(-2) T⁰ ((Y v)(-2) u) = + v₍₁₎u`  (`(Y v)(-2) u = v₍₁₎u`, `sgn(-2)=1`).
- `j≥1`: `1 - 1 - j = -j < 0`, vanish by `skewTerm_eq_zero_of_lt`. -/

/-- **Symmetry of the `(1)`-pairing on 𝒱₁** (skew, Gannon 5.1.8 specialised):
`u₍₁₎v = v₍₁₎u` for `u, v ∈ 𝒱₁`.  This is exactly the symmetry of Gannon's normalised
form `(u|v) = u₍₁₎v` (5.1.12b) **on 𝒱₁**, obtained from skew alone (no normalisation,
no simplicity needed). -/
theorem oneMode_symm_grading1 (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱}
    (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    W.smul u 1 v = W.smul v 1 u := by
  have hskew := skew_mode W u v 1
  have hsupp : ∀ j : ℕ, j ≠ 0 → skewTerm W u v 1 j = 0 := by
    intro j hj0
    refine skewTerm_eq_zero_of_lt W hu hv 1 ?_
    have : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    push_cast; omega
  have hcollapse : (∑ᶠ j : ℕ, skewTerm W u v 1 j) = skewTerm W u v 1 0 :=
    finsum_eq_single _ 0 hsupp
  have hrw : (∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-(1:ℤ) - 1 - j)) •
      ((W.toPreVertexAlgebra.T ^ j) ((W.Y v) (-(1:ℤ) - 1 - j) u)))
      = ∑ᶠ j : ℕ, skewTerm W u v 1 j := by
    refine finsum_congr fun j => by rw [skewTerm]
  rw [hrw, hcollapse, skewTerm] at hskew
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    show (-(1:ℤ) - 1 - (0:ℕ)) = -2 by norm_num,
    show (sgn (-2 : ℤ)) = 1 by rw [sgn, if_pos (by decide)], one_smul,
    Y_apply_eq_smul, show (-(-2 : ℤ) - 1) = 1 by ring] at hskew
  -- hskew : u₍₁₎v = v₍₁₎u
  exact hskew

/-! ## Form-level partial symmetry on 𝒱₁ (under the deferred 5.1.12b normalisation)

The genuine FORM symmetry `(u|v)=(v|u)` for a general `InvariantForm` is NOT reachable from
Virasoro-adjointness + skew (it needs the full invariance / `e^{zL₁}(-z⁻²)^{L₀}`
adjoint).  What IS reachable: ON 𝒱₁, if `B` is related to the `(1)`-product by the chosen
normalisation, then symmetry follows from `oneMode_symm_grading1`. -/

namespace InvariantForm

variable {W : VertexOperatorAlgebra 𝒱}

/-- A form `B` **evaluates by the `(1)`-product on 𝒱₁** if equality of its two scalar values is
equivalent to equality of the corresponding `(1)`-products.  This formulation is insensitive to
the global sign: for the unit normalisation one has `u₍₁₎v = -B(u,v)𝟙`, and the common minus
cancels when testing symmetry. -/
def EvalByOneMode (B : InvariantForm W) : Prop :=
  ∀ (u v : 𝒱), u ∈ W.grading 1 → v ∈ W.grading 1 →
    (B.form u v = B.form v u ↔ W.smul u 1 v = W.smul v 1 u)

/-- **Partial form symmetry on 𝒱₁** (conditional on the deferred 5.1.12b normalisation):
if `B` evaluates by the `(1)`-product on 𝒱₁ (`EvalByOneMode`), then `B` is symmetric on
𝒱₁.  The `(1)`-pairing symmetry `u₍₁₎v = v₍₁₎u` is supplied unconditionally by skew
(`oneMode_symm_grading1`); the `EvalByOneMode` bridge is the normalisation hypothesis. -/
theorem isSymmetric_grading1_of_eval (B : InvariantForm W) (heval : B.EvalByOneMode)
    {u v : 𝒱} (hu : u ∈ W.grading 1) (hv : v ∈ W.grading 1) :
    B.form u v = B.form v u :=
  (heval u v hu hv).mpr (oneMode_symm_grading1 W hu hv)

end InvariantForm

/-! ## The honest gap for FULL symmetry `∀ B, IsSymmetric B`

`∀ B, IsSymmetric B` is **NOT** provable from Virasoro-adjointness + skew alone.
The FHL symmetry argument needs the FULL generating-function invariance
`(Y(u,z)v|w) = (v|Y(e^{zL₁}(-z⁻²)^{L₀}u, z⁻¹)w)`, i.e. GENERAL-MODE adjointness — a form
adjoint for every `Y(a)`-mode, not only the `ω`-modes (`Lₙ`).  Virasoro-adjointness is the
`u = ω` slice of that and carries no bridge from skew's mode identities to `(u|v)` vs `(v|u)`
for general `u, v`.  The missing ingredient is the `e^{zL₁}(-z⁻²)^{L₀}` adjoint operator
(the locally-nilpotent `exp` + graded scalar action), the same infrastructure deferred in
`Core.Automorphism`.  We do NOT introduce a circular/vacuous predicate for it here; the gap
is reported, not stubbed.  What IS proved unconditionally-mod-skew above is the 𝒱₁ slice
(`oneMode_symm_grading1`, `zeroMode_antisymm_grading1`). -/

end VertexOperatorAlgebra

end VOA
