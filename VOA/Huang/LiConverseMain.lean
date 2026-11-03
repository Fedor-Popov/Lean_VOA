import VOA.Huang.LiConverseExtract
import VOA.Huang.LiConverseBimodule

/-! # Li's converse: every Frenkel–Zhu top datum comes from an intertwining operator

For an admissibly rational VOA with the regular-module PBW datum `Pr`, an ordinary module `M`
and irreducible lowest-weight modules `P₂, P₃`, every element `T ∈ fzSpace M P₂ P₃` is the top
component of an intertwining operator of type `(P₃ / M P₂)`:

* `scalarTopExtension_of_admissiblyRational : ScalarTopExtension A P₂ P₃`;
* `topMapFZ_surjective_of_admissiblyRational`;
* `insertionTopSurjectivity_of_stronglyRational` — the genus-one interface
  `InsertionTopSurjectivity`, with `Pr` supplied by the theorem `VOA.pbw`;
* `leading_realized_at_weight_of_stronglyRational_unconditional` — the genus-one
  leading-term realization with the Li-converse hypothesis discharged.

The construction (Li, math/9909007; Frenkel–Huang–Lepowsky §5.5 for the frame change) runs
through two regular representations: `D_{P(−1)}(M)` (source, `LiConverseSource`), the inversion
frame change on the restricted three-point identities (`LiConverseFrame`), and
`D_{P(−1)}(P₃')` (target, `LiConverseTarget`), whose translated three-way relation is the Jacobi
identity at `x = 1` (`LiConverseFinal`); the scalar modes are extracted in `LiConverseExtract`.

No `sorry`; axioms: Lean's three only.  The strongly rational corollaries use the theorem
`VOA.pbw`, which adds no axiom.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.Huang.LiFusion VOA.Huang.GenusOne VOA.Huang.LiConverse FusionTop VHat VHat.DLM3

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Li's scalar top extension** for an admissibly rational VOA. -/
theorem scalarTopExtension_of_admissiblyRational
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (A : OrdVModule W M) {P₂ P₃ : LWModule W}
    (hP₂ : P₂.IsIrreducibleLW) (hP₃ : P₃.IsIrreducibleLW) : ScalarTopExtension A P₂ P₃ :=
  fun T => ⟨Cmodes A T Pr hrat hP₃ hP₂, Cmodes_weightCompatible A T Pr hrat hP₃ hP₂,
    Cmodes_jacobi A T Pr hrat hP₃ hP₂, Cmodes_extendsTop A T Pr hrat hP₃ hP₂⟩

/-- **Every Frenkel–Zhu top datum is realized by an intertwining operator.** -/
theorem topMapFZ_surjective_of_admissiblyRational
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (A : OrdVModule W M) {P₂ P₃ : LWModule W}
    (hP₂ : P₂.IsIrreducibleLW) (hP₃ : P₃.IsIrreducibleLW) :
    Function.Surjective (topMapFZ A P₂ P₃) :=
  topMapFZ_surjective_of_scalarTopExtension
    (scalarTopExtension_of_admissiblyRational Pr hrat A hP₂ hP₃)

/-- **`InsertionTopSurjectivity` for a strongly rational VOA** (the PBW datum from the
theorem `VOA.pbw`). -/
theorem insertionTopSurjectivity_of_stronglyRational {ι : Type u} (hV : StronglyRational W)
    (A : OrdVModule W M) (P : ι → LWModule W) (hP : ∀ i, (P i).IsIrreducibleLW) :
    InsertionTopSurjectivity A P := fun i =>
  topMapFZ_surjective_of_admissiblyRational (voaPBWBottomProjection _) hV.rational A
    (hP i) (hP i)

/-- **Genus-one leading-term realization, with the Li converse discharged.** -/
theorem leading_realized_at_weight_of_stronglyRational_unconditional {ι : Type u} [Fintype ι]
    (hV : StronglyRational W) (A : OrdVModule W M) (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod))
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, S w b = ∑ i, trace (Y i) w b :=
  leading_realized_at_weight_of_stronglyRational A hV P hcomplete hP hne
    (insertionTopSurjectivity_of_stronglyRational hV A P hP) hsupp hS

end VOA.Huang.LiRegular
