import VOA.Examples.InvariantSymbolBridge
import VOA.Examples.InvariantSymbolCyclic

/-!
# The leading-symbol input reduced to a cyclic evaluation of the leading cohomology

`LeadingInvariantSymbolBound S` (which, by `leadingInvariantSymbolDimension_of_bound`, already
implies the equality form `LeadingInvariantSymbolDimension S` used by the endpoint) is reduced
here to the existence of a **cyclic evaluation** of the actual leading cohomology:

`ev : H⁰(Q⁻)_{(2r,0)}(N) →ₗ C[a_1, a_2, …]`, injective, landing in oscillator weight
`N - r(r+1)`, and annihilated by the symmetric-center Cartan ideal through `modePairing`.

In the coset note this map is the composite of
1. the leading Koszul identification `H⁰(Q⁻)(N, r) ≅ ((gr_r A) ⊗ B)^{g[t]}_N`
   (abstractly `VOA.LeadingKoszul.leadCohomEquivInvariants`; concretely OPEN), and
2. evaluation `Φ ↦ Φ(w_r)` of the corresponding equivariant map `K_r = (gr_r A)^∨ → B` at the
   cyclic vector, read in the charge-`r` Fock sector `C[a_1, a_2, …] e^{rα}` of `L_1(sl₂)`
   (energy `r² + oscillator weight`, `h_m = 2m ∂/∂a_m`). Injectivity is cyclicity of `w_r`;
   the annihilation is relation (A1) for the highest Cartan algebra.

The algebra after that (inverse system, perfect pairing, symmetric-polynomial count, Gordon
shift) is `finrank_le_gapTwoCoefficient_of_cyclicEvaluation`, proved outright.

The fields of `LeadingCyclicEvaluation` are OPEN for the concrete endpoint geometry: no
construction of `gr_R A` as the restricted dual of the cyclic global module (input (A)), of the
lattice realization of `L_1(sl₂)` matching `BVOA`, or of the concrete Koszul identification
exists in the library.
-/

namespace VOA.ConcreteHodge

open VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly VOA.InvariantSymbol
open LeeYangShortcut VirGradedUnitarity LeeYang
open Module (finrank)

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- OPEN (leading Koszul identification + cyclic evaluation): the data reducing the leading
ghost-number-zero cohomology of `S` to the Cartan inverse system. -/
structure LeadingCyclicEvaluation (S : ConcreteKahlerGeometry) where
  /-- No ghost-number-zero leading cohomology at odd `2R`. -/
  odd_zero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ),
    finrank ℂ ((S.model n hp).leadCohom (2 * (p : ℤ) + 1, 0)) = 0
  /-- No ghost-number-zero leading cohomology at negative `2R`. -/
  neg_zero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (j : ℤ), j < 0 →
    finrank ℂ ((S.model n hp).leadCohom (j, 0)) = 0
  /-- The cyclic evaluation of the leading cohomology at `2R = 2r`. -/
  ev : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (r : ℕ),
    (S.model n hp).leadCohom (2 * (r : ℤ), 0) →ₗ[ℂ] MvPolynomial ℕ ℂ
  injective : ∀ n hp r, Function.Injective (ev n hp r)
  degree : ∀ n hp r x,
    MvPolynomial.IsWeightedHomogeneous modeWeightZ (ev n hp r x) (n - r * (r + 1))
  cartan : ∀ n hp r x (F : MvPolynomial ℕ ℂ), F ∈ cartanIdeal r →
    MvPolynomial.IsWeightedHomogeneous modeWeightZ F (n - r * (r + 1)) →
      modePairing F (ev n hp r x) = 0

theorem leadingCoefficient_even (n : ℤ) (r : ℕ) :
    leadingCoefficient n (2 * (r : ℤ)) = gapTwoCoefficient n r := by
  unfold leadingCoefficient
  rw [if_pos (by omega)]
  congr 1
  omega

/-- A cyclic evaluation of the leading cohomology gives the leading-symbol upper bound. -/
theorem leadingInvariantSymbolBound_of_cyclicEvaluation (S : ConcreteKahlerGeometry)
    (E : LeadingCyclicEvaluation S) : LeadingInvariantSymbolBound S := by
  intro n hp j
  by_cases hj : j < 0
  · rw [E.neg_zero n hp j hj]; exact Nat.zero_le _
  rcases Int.even_or_odd' j with ⟨r', hr | hr⟩
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [leadingCoefficient_even]
    exact finrank_le_gapTwoCoefficient_of_cyclicEvaluation n r (E.ev n hp r)
      (E.injective n hp r) (E.degree n hp r) (E.cartan n hp r)
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [E.odd_zero n hp r]; exact Nat.zero_le _

/-- **Affine GU ⇒ Lee–Yang GU**, with `symbols` replaced by a cyclic evaluation of the
leading cohomology. `#print axioms`-clean, conditional on `hA` (the hypothesis), `E`, and the
classical Rogers–Ramanujan lower bound `lower`. -/
theorem leeYang_gradedUnitary_of_affine_cyclicEvaluation
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (E : LeadingCyclicEvaluation (endpointKahler hA))
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_levelOne_rr_bound hA
    (leadingInvariantSymbolBound_of_cyclicEvaluation _ E) lower

end

end VOA.ConcreteHodge
