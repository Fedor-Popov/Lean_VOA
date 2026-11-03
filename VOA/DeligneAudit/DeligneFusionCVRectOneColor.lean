import VOA.DeligneAudit.DeligneFusionCVRectFamily
import VOA.DeligneAudit.DeligneFusionCVRectIdealMap

/-!
# The actual one-color end of the rectangular recursion

When no two-color site remains, swapping the two sets of finite
variables turns the right current into the selected current. The
unused zero current removes all dependence on its exponent. These are
equalities of the actual coefficient ideals and quotient equivalences.
-/

namespace VOA.DeligneAudit.A2.CVRectOneColor

open VOA.DeligneAudit.A2.CVRectFamily
open VOA.DeligneAudit.A2.CVRectSplit
open VOA.DeligneAudit.A2.CVRectZero
open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectIdealMap

noncomputable section

section Ideal

variable {R : Type*} [CommRing R]

theorem coefficientIdeal_swap (S T : PowerSeries R) (μ : ℕ → ℕ → ℕ) :
    coefficientIdeal T S μ = coefficientIdeal S T (fun a b => μ b a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨a, b, j, hj, rfl⟩
    exact Ideal.subset_span ⟨b, a, j, hj, by rw [mul_comm]⟩
  · apply Ideal.span_le.mpr
    rintro P ⟨a, b, j, hj, rfl⟩
    exact Ideal.subset_span ⟨b, a, j, hj, by rw [mul_comm]⟩

/-- A zero right current makes only the zero right exponent relevant. -/
theorem coefficientIdeal_zero_right_congr (S : PowerSeries R) (μ ν : ℕ → ℕ → ℕ)
    (h : ∀ a, μ a 0 = ν a 0) : coefficientIdeal S 0 μ = coefficientIdeal S 0 ν := by
  have hle (μ ν : ℕ → ℕ → ℕ) (h : ∀ a, μ a 0 ≤ ν a 0) :
      coefficientIdeal S 0 μ ≤ coefficientIdeal S 0 ν := by
    apply Ideal.span_le.mpr
    rintro P ⟨a, b, j, hj, rfl⟩
    cases b with
    | zero => exact Ideal.subset_span ⟨a, 0, j, hj.trans_le (h a), rfl⟩
    | succ b =>
        rw [zero_pow (Nat.succ_ne_zero _), mul_zero, map_zero]
        exact Ideal.zero_mem _
  exact le_antisymm (hle μ ν (fun a => (h a).le)) (hle ν μ (fun a => (h a).ge))

end Ideal

/-- Swap the two colors of the actual finite polynomial ring. -/
def swapVars (M N : ℕ) : Ring M N ≃ₐ[ℂ] Ring N M :=
  MvPolynomial.renameEquiv ℂ (Equiv.sumComm (Fin M) (Fin N))

theorem swap_reverseLeft (M N : ℕ) :
    PowerSeries.map (swapVars M N).toRingHom (reverseLeft M N) = reverseRight N M := by
  simp [reverseLeft, reverseRight, swapVars, MvPolynomial.renameEquiv_apply]

theorem swap_reverseRight (M N : ℕ) :
    PowerSeries.map (swapVars M N).toRingHom (reverseRight M N) = reverseLeft N M := by
  simp [reverseLeft, reverseRight, swapVars, MvPolynomial.renameEquiv_apply]

/-- The one-color family's actual ideal is transported to the selected
color presentation, with its other current equal to zero. -/
theorem oneColorIdeal_map (one : List ℕ) :
    Ideal.map (swapVars 0 one.length).toRingHom (ideal 0 one.length [] one) =
      ideal one.length 0 one [] := by
  unfold ideal
  rw [coefficientIdeal_map, swap_reverseLeft, swap_reverseRight, reverseRight_zero,
    coefficientIdeal_swap]
  apply coefficientIdeal_zero_right_congr
  intro a
  simp [familyOrder, excess]

/-- An actual quotient equivalence identifies the final one-color family
with the same selected-current model used by the checked recursion. -/
def oneColorEquiv (one : List ℕ) : Family [] one ≃ₐ[ℂ] Model one.length 0 one [] := by
  unfold Family
  rw [List.length_nil, Nat.zero_add]
  exact Ideal.quotientEquivAlg _ _ (swapVars 0 one.length) (oneColorIdeal_map one).symm

/-- A site for the absent right color contributes no extra relation. -/
theorem extraOneColorIdeal (two : List ℕ) (K : ℕ) :
    ideal two.length 0 two [K] = ideal two.length 0 two [] := by
  unfold ideal
  rw [reverseRight_zero]
  apply coefficientIdeal_zero_right_congr
  intro a
  simp [familyOrder, excess]

def extraOneColorEquiv (two : List ℕ) (K : ℕ) :
    Model two.length 0 two [K] ≃ₐ[ℂ] Model two.length 0 two [] :=
  Ideal.quotientEquivAlgOfEq ℂ (extraOneColorIdeal two K)

/-- The same checked polynomial recursion proves the actual one-color
dimension step after the finite color swap. -/
theorem one_color_dimension_step (one : List ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ one, k ≤ K)
    [FiniteDimensional ℂ (Family [] one)]
    [FiniteDimensional ℂ (Family [] ((K - 1) :: one))] :
    FiniteDimensional ℂ (Family [] (K :: one)) ∧
      Module.finrank ℂ (Family [] (K :: one)) ≤
        Module.finrank ℂ (Family [] ((K - 1) :: one)) +
        Module.finrank ℂ (Family [] one) := by
  haveI : FiniteDimensional ℂ (Model one.length 0 one []) :=
    (oneColorEquiv one).toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional ℂ (Model one.length 0 one [K]) :=
    (extraOneColorEquiv one K).toLinearEquiv.symm.finiteDimensional
  haveI : FiniteDimensional ℂ (Model (one.length + 1) 0 ((K - 1) :: one) []) :=
    (oneColorEquiv ((K - 1) :: one)).toLinearEquiv.finiteDimensional
  have hs := active_dimension_step one [] K 0 hK hmax
  haveI := hs.1
  refine ⟨(oneColorEquiv (K :: one)).toLinearEquiv.symm.finiteDimensional, ?_⟩
  have hb := hs.2
  have hsrc : Module.finrank ℂ (Family [] (K :: one)) =
      Module.finrank ℂ (Model (one.length + 1) 0 (K :: one) []) := by
    simpa only [List.length_cons] using (oneColorEquiv (K :: one)).toLinearEquiv.finrank_eq
  have hlo : Module.finrank ℂ (Family [] ((K - 1) :: one)) =
      Module.finrank ℂ (Model (one.length + 1) 0 ((K - 1) :: one) []) := by
    simpa only [List.length_cons] using
      (oneColorEquiv ((K - 1) :: one)).toLinearEquiv.finrank_eq
  rw [← hsrc, ← hlo,
    (extraOneColorEquiv one K).toLinearEquiv.finrank_eq,
    ← (oneColorEquiv one).toLinearEquiv.finrank_eq] at hb
  exact hb

end

end VOA.DeligneAudit.A2.CVRectOneColor

#print axioms VOA.DeligneAudit.A2.CVRectOneColor.coefficientIdeal_zero_right_congr
#print axioms VOA.DeligneAudit.A2.CVRectOneColor.oneColorEquiv
#print axioms VOA.DeligneAudit.A2.CVRectOneColor.extraOneColorEquiv
#print axioms VOA.DeligneAudit.A2.CVRectOneColor.one_color_dimension_step
