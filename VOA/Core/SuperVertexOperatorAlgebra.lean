/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperVertexAlgebra
import VOA.Core.VertexOperatorAlgebra

/-!
# Super vertex operator algebras  (VOA1–VOA4 with both generalizations)

`Core.VertexOperatorAlgebra`, generalized along the same two independent axes as
`Core.SuperVertexAlgebra`: a `ℂ`-valued conformal-weight grading (half-integer moding) and
a `ZMod 2` parity entering locality through the Koszul sign.  Again the two are *not*
linked by any structure field.

## What the generalization changes, and what it does not

* **VOA1 (Virasoro) is unchanged.**  The modes `Lₙ = ω₍ₙ₊₁₎` are indexed by `ℤ` whatever
  the conformal weights, so the Virasoro relation is verbatim the bosonic one.
* **VOA2 gets simpler.**  `L₀ v = h • v` for `v ∈ 𝒱_h`, with `h : ℂ` — no `(n : ℂ)` cast,
  because the grading index is already the eigenvalue.
* **VOA3 (translation) is unchanged.**
* **VOA4 changes shape.**  "`𝒱ₙ = 0` for `n < 0`" becomes "no weights of negative real
  part", which is the correct statement once weights are complex (Gannon Def. 5.1.3(c)
  asks for boundedness below in real part on the module side already).
* `ω` is required to be **even**; this is a genuine axiom, not a consequence, since
  spin–statistics is not assumed.

## Main definitions

* `SuperVertexOperatorAlgebra` — the generalized structure.
* `VertexOperatorAlgebra.toSuper` — every ordinary VOA is one, purely even with integer
  weights.
* `VertexOperatorAlgebra.toSuper_spinStatistics` — and it satisfies spin–statistics, which
  checks that the `SpinStatistics` predicate is not vacuous or malformed.

## References
* Gannon §5.1.3 (Def. 5.1.3a–c, VOA1–VOA4); Kac, *Vertex Algebras for Beginners*, §4.1.
-/

namespace VOA

open Module (End)

universe u

/-- A **super vertex operator algebra**: a `SuperVertexAlgebra` with a conformal vector,
satisfying VOA1–VOA4 with complex conformal weights.

The conformal vector is required to be even (`conformal_parity`); with spin–statistics
unassumed this does not follow from anything else. -/
structure SuperVertexOperatorAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends SuperVertexAlgebra 𝒱 where
  /-- The conformal vector `ω`. -/
  conformalVector : 𝒱
  /-- `ω` has conformal weight `2`. -/
  conformal_mem : conformalVector ∈ grading 2
  /-- `ω` is even.  An axiom, not a theorem: spin–statistics is not assumed. -/
  conformal_parity : conformalVector ∈ parity 0
  /-- The central charge `c ∈ ℂ`. -/
  centralCharge : ℂ
  /-- **VOA1 (conformal symmetry).**  Unchanged from the bosonic case: the mode index is
  `ℤ` whatever the conformal weights. -/
  virasoro : ∀ m n : ℤ,
      ⁅mode (Y conformalVector) (m + 1), mode (Y conformalVector) (n + 1)⁆
        = ((m : ℂ) - n) • mode (Y conformalVector) (m + n + 1)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * centralCharge) • (1 : End ℂ 𝒱)
             else 0)
  /-- **VOA2 (conformal weight).**  `L₀` acts on `𝒱_h` as multiplication by `h`.  With a
  `ℂ`-valued grading index this is `h • v`, with no cast. -/
  L0_grading : ∀ {h : ℂ} (v : 𝒱), v ∈ grading h → mode (Y conformalVector) 1 v = h • v
  /-- **VOA3 (translation generator).** `Y(L₋₁ v, z) = ∂_z Y(v,z)`. -/
  translation : ∀ v : 𝒱, Y (mode (Y conformalVector) 0 v) = deriv (Y v)
  /-- **VOA4 (CFT type), part 1.** `𝒱₀ = ℂ𝟙`. -/
  vacuum_grade : grading 0 = ℂ ∙ vacuum
  /-- **VOA4 (CFT type), part 2.**  No weights of negative real part.  This is the correct
  generalization of `𝒱ₙ = 0 for n < 0` once weights are complex. -/
  positivity : ∀ h : ℂ, h.re < 0 → grading h = ⊥

namespace SuperVertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The Virasoro modes `Lₙ := ω₍ₙ₊₁₎`.  Identical to the bosonic definition: the `+1` shift
and the `ℤ` index are unaffected by either generalization. -/
def L (W : SuperVertexOperatorAlgebra 𝒱) (n : ℤ) : End ℂ 𝒱 :=
  mode (W.Y W.conformalVector) (n + 1)

theorem L_def (W : SuperVertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.L n = mode (W.Y W.conformalVector) (n + 1) := rfl

/-- **VOA2 through `L`.**  `L₀` acts on the weight-`h` space as `h`.  With a `ℂ`-valued
grading index the eigenvalue *is* the index — no cast, unlike the bosonic statement. -/
theorem L0_eigenvalue (W : SuperVertexOperatorAlgebra 𝒱) {h : ℂ} {v : 𝒱}
    (hv : v ∈ W.grading h) : W.L 0 v = h • v := by
  show mode (W.Y W.conformalVector) (0 + 1) v = h • v
  rw [zero_add]
  exact W.L0_grading v hv

/-- **VOA1 through `L`**: the Virasoro relation, verbatim the bosonic one. -/
theorem virasoro_L (W : SuperVertexOperatorAlgebra 𝒱) (m n : ℤ) :
    ⁅W.L m, W.L n⁆ = ((m : ℂ) - n) • W.L (m + n)
      + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * W.centralCharge) • (1 : End ℂ 𝒱) else 0) :=
  W.virasoro m n

end SuperVertexOperatorAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Every ordinary vertex operator algebra is a super vertex operator algebra**: integer
weights read as complex ones, purely even parity.  So `SuperVertexOperatorAlgebra`
generalizes `VertexOperatorAlgebra`; it does not compete with it. -/
noncomputable def toSuper (W : VertexOperatorAlgebra 𝒱) : SuperVertexOperatorAlgebra 𝒱 where
  __ := W.toPreVertexAlgebra.toSuper
  conformalVector := W.conformalVector
  conformal_mem := by
    show W.conformalVector ∈ W.toPreVertexAlgebra.gradingC 2
    rw [show (2 : ℂ) = ((2 : ℤ) : ℂ) by norm_num, PreVertexAlgebra.gradingC_intCast]
    exact W.conformal_mem
  conformal_parity := by
    show W.conformalVector ∈ (ParityGrading.even 𝒱).parity 0
    simp
  centralCharge := W.centralCharge
  virasoro := W.virasoro
  L0_grading := by
    classical
    intro h v hv
    have hv' : v ∈ W.toPreVertexAlgebra.gradingC h := hv
    by_cases hh : ∃ n : ℤ, (n : ℂ) = h
    · obtain ⟨n, rfl⟩ := hh
      rw [PreVertexAlgebra.gradingC_intCast] at hv'
      exact W.L0_grading v hv'
    · rw [W.toPreVertexAlgebra.gradingC_of_not_int hh, Submodule.mem_bot] at hv'
      subst hv'
      simp
  translation := W.translation
  vacuum_grade := by
    show W.toPreVertexAlgebra.gradingC 0 = ℂ ∙ W.vacuum
    rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by norm_num, PreVertexAlgebra.gradingC_intCast]
    exact W.vacuum_grade
  positivity := by
    classical
    intro h hh
    show W.toPreVertexAlgebra.gradingC h = ⊥
    by_cases hex : ∃ n : ℤ, (n : ℂ) = h
    · obtain ⟨n, rfl⟩ := hex
      rw [PreVertexAlgebra.gradingC_intCast]
      refine W.positivity n ?_
      have : ((n : ℤ) : ℝ) < 0 := by simpa using hh
      exact_mod_cast this
    · exact W.toPreVertexAlgebra.gradingC_of_not_int hex

/-- An ordinary VOA, read as a super VOA, satisfies **spin–statistics**: its weights are
integers and it is purely even.  This is the sanity check that `SpinStatistics` is a
satisfiable predicate rather than a malformed one. -/
theorem toSuper_spinStatistics (W : VertexOperatorAlgebra 𝒱) :
    SpinStatistics W.toSuper.toSuperVertexAlgebra := by
  classical
  intro h p u hu hgr hpar
  constructor
  · intro _
    by_contra hp
    exact hu (ParityGrading.eq_zero_of_mem_even_of_ne hp hpar)
  · intro _
    by_contra hh
    exact hu (by
      have := W.toPreVertexAlgebra.gradingC_of_not_int hh
      rw [show (W.toSuper.toSuperVertexAlgebra).grading = W.toPreVertexAlgebra.gradingC from rfl,
        this, Submodule.mem_bot] at hgr
      exact hgr)

/-- The Virasoro modes are untouched by `toSuper`. -/
@[simp] theorem toSuper_L (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    W.toSuper.L n = W.L n := rfl

end VertexOperatorAlgebra

end VOA
