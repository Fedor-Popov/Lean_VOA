/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SuperVOASubalgebra

/-!
# The even part of a super VOA as an honest bosonic vertex operator algebra

The `ℂ`-graded → `ℤ`-graded transfer.  `Core.SuperVOASubalgebra` already exhibits the even
part `𝒱₀̄` of a super near-VOA as a *super* near-VOA in its own right
(`SuperVOASubalgebra.evenPart`, `SuperVOASubalgebra.toSuperNearVOA`).  What is missing —
and what this file supplies — is the last step: turning that purely even, `ℂ`-graded object
into a `VertexOperatorAlgebra`, i.e. a genuinely **bosonic**, `ℤ`-graded structure, so that
the whole bosonic library (modules, Zhu algebra, characters, modularity) applies to it.

This is exactly the step `Modularity.Twisted`'s `orbifoldVOA` cannot perform: that
construction starts from a *bosonic* `ℤ`-graded VOA and an automorphism group, whereas the
input here is a super algebra with a `ℂ`-valued grading and no automorphism in sight.

## The one genuine hypothesis: integrality

Nothing forces the weights of a super vertex algebra to be integers, and nothing forces the
weights *of the even part* to be integers either — `SpinStatistics` is deliberately not an
axiom of `SuperVertexAlgebra`, and it genuinely fails for symplectic fermions (odd fields
of integer weight).  Two independent reasons why integrality has to be a hypothesis:

* the doublet-type examples have generators of weight `5/2`, so *half*-integer weights
  really do occur in the ambient algebra;
* even where the ambient algebra has integer weights, the statement we need is about the
  even part only, and it is that restricted statement which the transfer consumes.

So the integrality condition is carried as an **explicit hypothesis parameter**, spelled
"no non-integer weight occurs in the even part":

`∀ h : ℂ, (¬∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0`.

It is *not* derived, because it is false in general.  For symplectic fermions it is
discharged from `WEIGHTS`: every weight of `FockSF` is a non-negative integer in both
parities, so a fortiori in the even part.

## What is proved

* `isInternal_comp_of_bot` — an internal grading whose pieces vanish off the image of an
  injective reindexing restricts to an internal grading along that injection.  This is the
  formal content of "a `ℂ`-grading concentrated on `ℤ` *is* a `ℤ`-grading"; it is the exact
  converse of `SuperVertexAlgebra.isInternal_extend`, which pushes a `ℤ`-grading forward.
* `SuperNearVOA.gradingZ` and `SuperNearVOA.gradingZ_isInternal` — the transferred grading.
* `SuperNearVOA.local_Y` — for a **purely even** super near-VOA super-locality *is*
  ordinary locality: `koszul 0 0 = 1` and `localε_one_iff`.
* `SuperNearVOA.toPreVertexAlgebra` — a purely even super near-VOA with integral weights is a
  bosonic `PreVertexAlgebra`.
* `SuperNearVOA.toVOA` — and, given the two CFT-type conditions, a bosonic
  `VertexOperatorAlgebra`, with the same `Y`, vacuum, `ω`, central charge and Virasoro
  modes.
* `SuperNearVOA.evenPartVertexAlgebra` / `SuperNearVOA.evenPartVOA` — the two
  specialisations to `𝒱₀̄`, where purely-evenness is automatic and the CFT-type conditions
  are required **only on the even part**.  That restriction matters: the doublet's ambient
  algebra has states of negative weight, so `positivity` can only ever hold after passing
  to the subalgebra.
* `SuperVertexOperatorAlgebra.evenPartVOA` — the main corollary.  For a genuine super
  *VOA* both CFT-type conditions **are** inherited by the even part (`evenPart_vacuum_grade`
  needs only that the vacuum is even), so integrality is the sole remaining input.

## What is *not* claimed

No statement here says the even part is simple, or `C₂`-cofinite, or that its weights are
bounded below beyond what the hypotheses give.  `BoundedBelow` transfers trivially and is
recorded as `evenPart_boundedBelow`, but nothing stronger is asserted.

## References
* Kac, *Vertex Algebras for Beginners*, §4.1;
  `Core.SuperVOASubalgebra` for the subalgebra layer this file sits on top of.
-/

namespace VOA

open Module (End)

universe u

/-! ## Restricting an internal grading along an injection with `⊥` complement

The converse of `isInternal_extend` (`Core.SuperVertexAlgebra`), which pushes an internal
grading *forward* along an injection.  Here the grading is already indexed by the larger
type and is known to vanish outside the image; the conclusion is that its restriction is
again internal.  Stated for a bare family of submodules, since it is pure lattice theory. -/

section RestrictGrading

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **An internal grading concentrated on the image of an injection restricts to an
internal grading.**

With `f = ((↑·) : ℤ → ℂ)` this says precisely: a `ℂ`-grading all of whose non-integer
pieces vanish *is* a `ℤ`-grading.  That is the entire mathematical content of the
`ℂ`-graded → `ℤ`-graded transfer; everything else in this file is bookkeeping. -/
theorem isInternal_comp_of_bot {f : ι → κ} (hf : Function.Injective f)
    {A : κ → Submodule ℂ M} (hA : DirectSum.IsInternal A)
    (hbot : ∀ k : κ, (¬ ∃ i, f i = k) → A k = ⊥) :
    DirectSum.IsInternal (fun i => A (f i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
  obtain ⟨hindep, htop⟩ := hA
  constructor
  · -- independence is inherited: the competing supremum only shrinks under an injection
    refine iSupIndep_def.mpr fun i => ?_
    have h1 := iSupIndep_def.mp hindep (f i)
    rw [Submodule.disjoint_def] at h1 ⊢
    intro x hx hx'
    have hle : (⨆ (j : ι) (_ : j ≠ i), A (f j)) ≤ ⨆ (k : κ) (_ : k ≠ f i), A k :=
      iSup₂_le fun j hj =>
        le_iSup₂ (f := fun k (_ : k ≠ f i) => A k) (f j) (fun h => hj (hf h))
    exact h1 x hx (hle hx')
  · -- spanning: the pieces off the image contribute nothing
    refine le_antisymm le_top ?_
    rw [← htop]
    refine iSup_le fun k => ?_
    by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      exact le_iSup (fun i => A (f i)) i
    · rw [hbot k hk]
      exact bot_le

end RestrictGrading

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

/-! ## The two hypotheses of the transfer -/

/-- **Integral weights**: no weight outside `ℤ ⊆ ℂ` occurs.

An explicit hypothesis, never a theorem: `SuperVertexAlgebra` links weight and parity by no
axiom, and the doublet's ambient algebra genuinely carries weight-`5/2` states. -/
def IntegralWeights (V : SuperNearVOA 𝒱) : Prop :=
  ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → V.grading h = ⊥

/-- **Purely even**: every state is even.  True by construction for the even part, and the
condition under which super-locality collapses to ordinary locality. -/
def PurelyEven (V : SuperNearVOA 𝒱) : Prop := V.parity 0 = ⊤

theorem mem_parity_zero_of_purelyEven {V : SuperNearVOA 𝒱} (hV : V.PurelyEven) (u : 𝒱) :
    u ∈ V.parity 0 := by
  rw [hV]
  exact Submodule.mem_top

/-! ## Super-locality collapses to locality on a purely even algebra -/

/-- **On a purely even super near-VOA, VA4 *is* ordinary locality.**  Both slots are even,
so the Koszul sign is `koszul 0 0 = 1`, and `Localε 1` is `Local` by `localε_one_iff`. -/
theorem local_Y {V : SuperNearVOA 𝒱} (hV : V.PurelyEven) (u v : 𝒱) :
    Local (V.Y u) (V.Y v) := by
  have h := V.locality u (mem_parity_zero_of_purelyEven hV u) v
    (mem_parity_zero_of_purelyEven hV v)
  rw [koszul_zero_left] at h
  exact (localε_one_iff _ _).mp h

/-! ## The transferred `ℤ`-grading -/

/-- The `ℤ`-grading obtained by restricting the `ℂ`-grading to the integers. -/
def gradingZ (V : SuperNearVOA 𝒱) : ℤ → Submodule ℂ 𝒱 := fun n => V.grading (n : ℂ)

theorem gradingZ_apply (V : SuperNearVOA 𝒱) (n : ℤ) : V.gradingZ n = V.grading (n : ℂ) := rfl

/-- **The transferred grading is again an internal direct sum**, provided no non-integer
weight occurs.  This is the actual content of the transfer. -/
theorem gradingZ_isInternal (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) :
    DirectSum.IsInternal V.gradingZ :=
  isInternal_comp_of_bot (fun _ _ h => Int.cast_injective h) V.isInternal hV

/-- Positivity in the `ℂ`-form implies positivity in the `ℤ`-form. -/
theorem grading_intCast_eq_bot_of_neg (V : SuperNearVOA 𝒱)
    (hpos : ∀ h : ℂ, h.re < 0 → V.grading h = ⊥) (n : ℤ) (hn : n < 0) :
    V.grading (n : ℂ) = ⊥ := by
  refine hpos _ ?_
  rw [Complex.intCast_re]
  exact_mod_cast hn

/-! ## A purely even, integrally graded super near-VOA is a bosonic vertex algebra -/

/-- **The bosonic vertex algebra underlying a purely even super near-VOA with integral
weights.**  Same `Y`, same vacuum, same products; only the grading index and the locality
statement change shape. -/
noncomputable def toPreVertexAlgebra (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) : PreVertexAlgebra 𝒱 where
  grading := V.gradingZ
  isInternal := V.gradingZ_isInternal hint
  finrank n := V.finrank (n : ℂ)
  Y := V.Y
  vacuum := V.vacuum
  vacuum_mem := by
    change V.vacuum ∈ V.grading ((0 : ℤ) : ℂ)
    rw [Int.cast_zero]
    exact V.vacuum_mem
  grading_mode := by
    intro k l u hu v hv n
    have h := V.grading_mode u hu v hv n
    change mode (V.Y u) n v ∈ V.grading (((k + l - n - 1 : ℤ) : ℂ))
    rwa [show (((k + l - n - 1 : ℤ) : ℂ)) = (k : ℂ) + (l : ℂ) - (n : ℂ) - 1 by push_cast; ring]
  vacuum_Y := V.vacuum_Y
  creation := V.creation
  locality := local_Y heven
  regularity := V.regularity

@[simp] theorem toPreVertexAlgebra_Y (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) : (V.toPreVertexAlgebra heven hint).Y = V.Y := rfl

@[simp] theorem toPreVertexAlgebra_vacuum (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) : (V.toPreVertexAlgebra heven hint).vacuum = V.vacuum := rfl

@[simp] theorem toPreVertexAlgebra_smul (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (V.toPreVertexAlgebra heven hint).smul u n v = V.smul u n v := rfl

/-! ## …and, with the CFT-type conditions, a bosonic VOA -/

/-- **The bosonic vertex operator algebra underlying a purely even super near-VOA with
integral weights**, given the two CFT-type conditions in their `ℤ`-graded form.

VOA1 (Virasoro), VOA2 (`L₀`-grading) and VOA3 (translation) transfer verbatim: the mode
index of `Lₙ = ω₍ₙ₊₁₎` was always `ℤ`, and with a `ℂ`-valued grading index the `L₀`
eigenvalue *is* the index, so VOA2 becomes the bosonic `L₀ v = (n : ℂ) • v` on the nose. -/
noncomputable def toVOA (V : SuperNearVOA 𝒱) (heven : V.PurelyEven) (hint : V.IntegralWeights)
    (hvac : V.grading 0 = ℂ ∙ V.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) : VertexOperatorAlgebra 𝒱 where
  __ := V.toPreVertexAlgebra heven hint
  conformalVector := V.conformalVector
  conformal_mem := by
    change V.conformalVector ∈ V.grading ((2 : ℤ) : ℂ)
    rw [show (((2 : ℤ) : ℂ)) = 2 by norm_num]
    exact V.conformal_mem
  centralCharge := V.centralCharge
  virasoro := V.virasoro
  L0_grading := by
    intro n v hv
    exact V.L0_grading v hv
  translation := V.translation
  vacuum_grade := by
    change V.grading ((0 : ℤ) : ℂ) = ℂ ∙ V.vacuum
    rw [Int.cast_zero]
    exact hvac
  positivity := hpos

@[simp] theorem toVOA_Y (V : SuperNearVOA 𝒱) (heven : V.PurelyEven) (hint : V.IntegralWeights)
    (hvac : V.grading 0 = ℂ ∙ V.vacuum) (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) :
    (V.toVOA heven hint hvac hpos).Y = V.Y := rfl

@[simp] theorem toVOA_vacuum (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) (hvac : V.grading 0 = ℂ ∙ V.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) :
    (V.toVOA heven hint hvac hpos).vacuum = V.vacuum := rfl

@[simp] theorem toVOA_conformalVector (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) (hvac : V.grading 0 = ℂ ∙ V.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) :
    (V.toVOA heven hint hvac hpos).conformalVector = V.conformalVector := rfl

@[simp] theorem toVOA_centralCharge (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) (hvac : V.grading 0 = ℂ ∙ V.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) :
    (V.toVOA heven hint hvac hpos).centralCharge = V.centralCharge := rfl

/-- The Virasoro modes are untouched by the transfer, so every `Lₙ`-fact proved in the
super setting is available in the bosonic one. -/
@[simp] theorem toVOA_L (V : SuperNearVOA 𝒱) (heven : V.PurelyEven) (hint : V.IntegralWeights)
    (hvac : V.grading 0 = ℂ ∙ V.vacuum) (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥)
    (n : ℤ) : (V.toVOA heven hint hvac hpos).L n = V.L n := rfl

/-- The transferred grading is the old one read at integer weights. -/
@[simp] theorem toVOA_grading (V : SuperNearVOA 𝒱) (heven : V.PurelyEven)
    (hint : V.IntegralWeights) (hvac : V.grading 0 = ℂ ∙ V.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → V.grading (n : ℂ) = ⊥) (n : ℤ) :
    (V.toVOA heven hint hvac hpos).grading n = V.grading (n : ℂ) := rfl

end SuperNearVOA

/-! ## Specialisation to the even part -/

namespace SuperVOASubalgebra

variable {W : SuperNearVOA 𝒱}

/-- The even part is purely even as an algebra in its own right: every element of the
carrier `𝒱₀̄` is even. -/
theorem evenPart_purelyEven (W : SuperNearVOA 𝒱) :
    (evenPart W).toSuperNearVOA.PurelyEven :=
  eq_top_iff.mpr fun x _ => x.2

/-- A weight space of a subalgebra vanishes as soon as the ambient one does. -/
theorem gradingS_eq_bot_of_bot (S : SuperVOASubalgebra W) {h : ℂ} (hb : W.grading h = ⊥) :
    S.gradingS h = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' : (x : 𝒱) ∈ W.grading h := hx
  rw [hb, Submodule.mem_bot] at hx'
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext hx')

/-- **The integrality hypothesis, in the form the transfer consumes.**  "No non-integer
weight occurs in the even part" says exactly that the induced weight spaces of `𝒱₀̄` at
non-integer weights are trivial. -/
theorem evenPart_integralWeights (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    (evenPart W).toSuperNearVOA.IntegralWeights := by
  intro h hh
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' : (x : 𝒱) ∈ W.grading h := hx
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext (hint h hh (x : 𝒱) x.2 hx'))

/-- **VOA4, part 1, for the even part.**  Only the *even* weight-zero states need to be
multiples of the vacuum; the vacuum is even, so it is a legitimate element of the
subalgebra and the span is taken there. -/
theorem evenPart_vacuum_grade (W : SuperNearVOA 𝒱)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum) :
    (evenPart W).toSuperNearVOA.grading 0
      = ℂ ∙ (evenPart W).toSuperNearVOA.vacuum := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hx' : (x : 𝒱) ∈ W.grading 0 := hx
    obtain ⟨c, hc⟩ := hvac (x : 𝒱) x.2 hx'
    rw [Submodule.mem_span_singleton]
    exact ⟨c, Subtype.ext hc.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    change W.vacuum ∈ W.grading 0
    exact W.vacuum_mem

/-- **VOA4, part 2, for the even part.**  Only the *even* states of negative weight need to
vanish — which is what makes this usable for the doublet, whose ambient algebra has
negative weights in the odd sector. -/
theorem evenPart_positivity (W : SuperNearVOA 𝒱)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0) :
    ∀ n : ℤ, n < 0 → (evenPart W).toSuperNearVOA.grading (n : ℂ) = ⊥ := by
  intro n hn
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx' : (x : 𝒱) ∈ W.grading (n : ℂ) := hx
  exact (Submodule.mem_bot ℂ).mpr (Subtype.ext (hpos n hn (x : 𝒱) x.2 hx'))

/-- Bounded-belowness passes to the even part. -/
theorem evenPart_boundedBelow (W : SuperNearVOA 𝒱) (hW : W.BoundedBelow) :
    (evenPart W).toSuperNearVOA.BoundedBelow := by
  obtain ⟨B, hB⟩ := hW
  exact ⟨B, fun h hh => (evenPart W).gradingS_eq_bot_of_bot (hB h hh)⟩

end SuperVOASubalgebra

namespace SuperNearVOA

open SuperVOASubalgebra

/-- **The even part of a super near-VOA as a bosonic vertex algebra.**  The conformal layer
is not used here, so no CFT-type condition is needed — only integrality. -/
noncomputable def evenPartVertexAlgebra (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    PreVertexAlgebra (W.parity 0) :=
  (evenPart W).toSuperNearVOA.toPreVertexAlgebra (evenPart_purelyEven W)
    (evenPart_integralWeights W hint)

/-- **The even part of a super near-VOA as a bosonic vertex operator algebra.**

The three hypotheses are all restricted to the even part, which is what makes the statement
usable: for the doublet the ambient algebra has states of negative conformal weight, so
`positivity` is false there and can only ever be established after passing to `𝒱₀̄`. -/
noncomputable def evenPartVOA (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0) :
    VertexOperatorAlgebra (W.parity 0) :=
  (evenPart W).toSuperNearVOA.toVOA (evenPart_purelyEven W) (evenPart_integralWeights W hint)
    (evenPart_vacuum_grade W hvac) (evenPart_positivity W hpos)

@[simp] theorem evenPartVOA_centralCharge (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0) :
    (W.evenPartVOA hint hvac hpos).centralCharge = W.centralCharge := rfl

/-- The vertex operators of the even-part VOA are the ambient ones, restricted. -/
@[simp] theorem evenPartVOA_Y_coe (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0)
    (u : W.parity 0) (k : ℤ) (x : W.parity 0) :
    (((W.evenPartVOA hint hvac hpos).Y u k x : W.parity 0) : 𝒱) = W.Y u k x := rfl

/-- The `n`-th products of the even-part VOA are the ambient ones. -/
@[simp] theorem evenPartVOA_smul_coe (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0)
    (u : W.parity 0) (n : ℤ) (v : W.parity 0) :
    (((W.evenPartVOA hint hvac hpos).smul u n v : W.parity 0) : 𝒱)
      = mode (W.Y u) n v := rfl

/-- The vacuum of the even-part VOA is the ambient vacuum. -/
@[simp] theorem evenPartVOA_vacuum_coe (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0) :
    (((W.evenPartVOA hint hvac hpos).vacuum : W.parity 0) : 𝒱) = W.vacuum := rfl

/-- The conformal vector of the even-part VOA is the ambient `ω`, which is even by axiom. -/
@[simp] theorem evenPartVOA_conformalVector_coe (W : SuperNearVOA 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (hvac : ∀ x ∈ W.parity 0, x ∈ W.grading 0 → ∃ c : ℂ, x = c • W.vacuum)
    (hpos : ∀ n : ℤ, n < 0 → ∀ x ∈ W.parity 0, x ∈ W.grading (n : ℂ) → x = 0) :
    (((W.evenPartVOA hint hvac hpos).conformalVector : W.parity 0) : 𝒱)
      = W.conformalVector := rfl

end SuperNearVOA

/-! ## The main corollary: the even part of a super VOA -/

namespace SuperVertexOperatorAlgebra

open SuperVOASubalgebra

/-- **The even part of a super vertex operator algebra is a bosonic vertex operator
algebra**, on the sole extra hypothesis that every weight occurring in the even part is an
integer.

Both CFT-type conditions are *inherited* here, unlike in the near-VOA case: `positivity`
holds in the ambient algebra already, and `𝒱₀ = ℂ𝟙` restricts to the even part because the
vacuum is even.  So integrality is the only genuine input — and it is genuine: it fails for
the doublet's ambient algebra and has to be checked per example.

For symplectic fermions it is discharged from the fact that every weight of `FockSF` is a
non-negative integer in *both* parities (spin–statistics fails, but integrality holds). -/
noncomputable def evenPartVOA (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    VertexOperatorAlgebra (W.parity 0) :=
  W.toSuperNearVOA.evenPartVOA hint
    (by
      intro x _ hx
      have hx' : x ∈ ℂ ∙ W.vacuum := by rw [← W.vacuum_grade]; exact hx
      rw [Submodule.mem_span_singleton] at hx'
      obtain ⟨c, hc⟩ := hx'
      exact ⟨c, hc.symm⟩)
    (by
      intro n hn x _ hx
      have hb : W.grading ((n : ℤ) : ℂ) = ⊥ := by
        refine W.positivity _ ?_
        rw [Complex.intCast_re]
        exact_mod_cast hn
      have hx' : x ∈ W.grading ((n : ℤ) : ℂ) := hx
      rw [hb, Submodule.mem_bot] at hx'
      exact hx')

@[simp] theorem evenPartVOA_centralCharge (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    (W.evenPartVOA hint).centralCharge = W.centralCharge := rfl

/-- The vertex operators of the even part are the ambient ones. -/
@[simp] theorem evenPartVOA_Y_coe (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (u : W.parity 0) (k : ℤ) (x : W.parity 0) :
    (((W.evenPartVOA hint).Y u k x : W.parity 0) : 𝒱) = W.Y u k x := rfl

/-- The `n`-th products of the even part are the ambient ones. -/
@[simp] theorem evenPartVOA_smul_coe (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (u : W.parity 0) (n : ℤ) (v : W.parity 0) :
    (((W.evenPartVOA hint).smul u n v : W.parity 0) : 𝒱) = mode (W.Y u) n v := rfl

/-- The vacuum of the even part is the ambient vacuum. -/
@[simp] theorem evenPartVOA_vacuum_coe (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    (((W.evenPartVOA hint).vacuum : W.parity 0) : 𝒱) = W.vacuum := rfl

/-- The conformal vector of the even part is the ambient `ω`. -/
@[simp] theorem evenPartVOA_conformalVector_coe (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0) :
    (((W.evenPartVOA hint).conformalVector : W.parity 0) : 𝒱) = W.conformalVector := rfl

/-- The weight spaces of the even part are the even parts of the ambient weight spaces. -/
@[simp] theorem evenPartVOA_grading (W : SuperVertexOperatorAlgebra 𝒱)
    (hint : ∀ h : ℂ, (¬ ∃ n : ℤ, (n : ℂ) = h) → ∀ x ∈ W.parity 0, x ∈ W.grading h → x = 0)
    (n : ℤ) :
    (W.evenPartVOA hint).grading n
      = (W.grading (n : ℂ)).comap (W.parity 0).subtype := rfl

end SuperVertexOperatorAlgebra

end VOA

