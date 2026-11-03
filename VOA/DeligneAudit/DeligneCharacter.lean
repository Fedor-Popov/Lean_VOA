/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterInterface

/-!
# Type-generic Deligne character interface

For every Deligne type the character side of classical freeness is split at the Demazure sum

  `D_N = [q^N] ∑_n q^n Hilb_q D(1,nθ)/(q)_n`,

and `D_N` is compared with an explicit *target* series, the character of `L_k(g)`. This file
abstracts the A₂ interface (`A2CharacterInterface`) over:

* `hilb : ℕ → ℕ → ℕ`, the coefficient table `hilb n N = [q^N] Hilb_q D(1,nθ)`;
* `target : ℕ → ℕ`, the coefficient table of the target series.

Named inputs, all `Prop` structures:

* `StarIdentityFor hilb target`: the combinatorial identity `D_N = target N`;
* `TargetLowerBound W target`: the representation-theoretic half `target N ≤ dim W_N`;
* `DemazureBoundFor W hilb`: the character-side goal `D_N ≤ dim W_N`.

The A₂ objects are the instance `hilb := A2.demazureHilb`, `target := A2.productCoeff`
(`A2.demazureCoeff_eq_generic`, by `rfl`).
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra VOA.DeligneAudit.A2

universe uV uC

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- **The Demazure sum** `D_N` for a given table of Demazure Hilbert series. -/
def demazureSumCoeff (hilb : ℕ → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), conv (hilb n) (partitionsLe n) (N - n)

/-- The combinatorial identity `D_N = target_N` for all `N`. -/
structure StarIdentityFor (hilb : ℕ → ℕ → ℕ) (target : ℕ → ℕ) : Prop where
  eq : ∀ N, demazureSumCoeff hilb N = target N

/-- The lower half of the character identity of the VOA: `target_N ≤ dim W_N`. -/
structure TargetLowerBound (W : VertexOperatorAlgebra V) (target : ℕ → ℕ) : Prop where
  le : ∀ N : ℕ, target N ≤ Module.finrank ℂ (W.grading N)

/-- The character-side goal `D_N ≤ dim W_N`. -/
structure DemazureBoundFor (W : VertexOperatorAlgebra V) (hilb : ℕ → ℕ → ℕ) : Prop where
  le : ∀ N : ℕ, demazureSumCoeff hilb N ≤ Module.finrank ℂ (W.grading N)

theorem demazureBoundFor_of_inputs {W : VertexOperatorAlgebra V} {hilb : ℕ → ℕ → ℕ}
    {target : ℕ → ℕ} (hstar : StarIdentityFor hilb target) (hlow : TargetLowerBound W target) :
    DemazureBoundFor W hilb :=
  ⟨fun N => (hstar.eq N).le.trans (hlow.le N)⟩

/-- **Glue.** A carrier bounded by the Demazure sum, together with the character side, gives the
capstone's remaining inequality `CarrierCharacterLowerBound`. -/
theorem carrierCharacterLowerBound_of_demazureSum {W : VertexOperatorAlgebra V}
    {hilb : ℕ → ℕ → ℕ}
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)] [∀ p N, Module ℂ (Carrier p N)]
    (hcar : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤
      demazureSumCoeff hilb N)
    (hchr : DemazureBoundFor W hilb) :
    CarrierCharacterLowerBound W Carrier :=
  fun N => (hcar N).trans (hchr.le N)

/-! ## The A₂ instance -/

theorem A2_demazureCoeff_eq_generic (N : ℕ) :
    A2.demazureCoeff N = demazureSumCoeff A2.demazureHilb N := rfl

theorem A2_starIdentity_iff : A2.StarIdentity ↔ StarIdentityFor A2.demazureHilb A2.productCoeff :=
  ⟨fun h => ⟨h.eq⟩, fun h => ⟨h.eq⟩⟩

theorem A2_kacWakimoto_iff :
    A2.KacWakimotoLowerBound ↔ TargetLowerBound A2.W A2.productCoeff :=
  ⟨fun h => ⟨h.le⟩, fun h => ⟨h.le⟩⟩

theorem A2_demazureBound_iff :
    A2.DemazureCharacterBound ↔ DemazureBoundFor A2.W A2.demazureHilb :=
  ⟨fun h => ⟨h.le⟩, fun h => ⟨h.le⟩⟩

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.demazureBoundFor_of_inputs
#print axioms VOA.DeligneAudit.DeligneCharacter.carrierCharacterLowerBound_of_demazureSum
#print axioms VOA.DeligneAudit.DeligneCharacter.A2_starIdentity_iff
end AxiomAudit
