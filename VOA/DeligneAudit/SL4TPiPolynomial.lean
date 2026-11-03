import VOA.DeligneAudit.SL4TCell
import VOA.DeligneAudit.SL4TFlagExport
import Mathlib.RingTheory.Polynomial.Basic

/-! # The polynomial evaluation used by the pi-form cell lemma

The characteristic relation is explicit here. Deriving it from highest-weight relations
requires Garland with nonzero positive Cartan action; the existing `Garland.garland`
only treats zero positive Cartan action.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R V : Type*} [CommRing R] [Algebra ℂ R]
variable [AddCommGroup V] [Module ℂ V]

/-- The linear evaluation sending `a * t^s` to `F s (π a)`. -/
def piCurrentMap (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V) : R[X] →ₗ[ℂ] V :=
  Polynomial.lsum (fun s => (F s).comp π)

theorem piCurrentMap_monomial (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (s : ℕ) (a : R) : piCurrentMap F π (monomial s a) = F s (π a) := by
  simp [piCurrentMap, Polynomial.lsum, Polynomial.sum_monomial_index]

theorem piCurrentMap_C_mul_X_pow (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (a : R) (s : ℕ) : piCurrentMap F π (Polynomial.C a * X ^ s) = F s (π a) := by
  rw [C_mul_X_pow_eq_monomial, piCurrentMap_monomial]

/-- The shifted, coefficient-multiplied one-letter Garland relation. -/
def PiCharacteristic (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V) (P : R[X]) : Prop :=
  ∀ (a : R) (s : ℕ), piCurrentMap F π (Polynomial.C a * X ^ s * P) = 0

theorem PiCharacteristic.mul (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    {P : R[X]} (h : PiCharacteristic F π P) (q : R[X]) :
    piCurrentMap F π (q * P) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q q' hq hq' => rw [add_mul, map_add, hq, hq', add_zero]
  | monomial s a => simpa only [C_mul_X_pow_eq_monomial] using h a s

theorem piCurrentMap_truncation (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (M : ℕ) (h : ∀ s, M ≤ s → ∀ a, F s (π a) = 0) :
    PiCharacteristic F π (X ^ M) := by
  intro a s
  rw [mul_assoc, ← pow_add, piCurrentMap_C_mul_X_pow]
  exact h (s + M) (by omega) a

/-- The evaluator kills the complete relation ideal, not just its two generators. -/
theorem piCurrentMap_relationIdeal (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (P : R[X]) (M : ℕ) (hP : PiCharacteristic F π P)
    (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    {q : R[X]} (hq : q ∈ Ideal.span {P} ⊔ Ideal.span {X ^ M}) :
    piCurrentMap F π q = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨u', rfl⟩ := Ideal.mem_span_singleton.mp hu
  obtain ⟨v', rfl⟩ := Ideal.mem_span_singleton.mp hv
  rw [map_add, mul_comm P, mul_comm (X ^ M), PiCharacteristic.mul F π hP,
    PiCharacteristic.mul F π (piCurrentMap_truncation F π M hM), add_zero]

theorem piCurrentMap_ideal (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (I : Ideal R) (N : Submodule ℂ V)
    (hπ : ∀ a ∈ I, π a ∈ N) (hF : ∀ s, N ≤ N.comap (F s))
    {q : R[X]} (hq : q ∈ I.map Polynomial.C) : piCurrentMap F π q ∈ N := by
  change (q.sum fun s a => F s (π a)) ∈ N
  apply Submodule.sum_mem
  intro s _
  exact hF s (hπ _ (Ideal.mem_map_C_iff.mp hq s))

/-- A cell polynomial relation gives every lowering cutoff modulo the earlier module. -/
theorem piCurrentMap_cell (F : ℕ → Module.End ℂ V) (π : R →ₗ[ℂ] V)
    (I : Ideal R) (N : Submodule ℂ V) (P : R[X]) (M : ℕ)
    (hπ : ∀ a ∈ I, π a ∈ N) (hF : ∀ s, N ≤ N.comap (F s))
    (hP : PiCharacteristic F π P) (hM : ∀ s, M ≤ s → ∀ a, F s (π a) = 0)
    {a : R} {n : ℕ}
    (ha : Polynomial.C a * X ^ n ∈ I.map Polynomial.C ⊔
      (Ideal.span {P} ⊔ Ideal.span {X ^ M})) (s : ℕ) (hs : n ≤ s) :
    F s (π a) ∈ N := by
  have hrel := (I.map Polynomial.C ⊔
    (Ideal.span {P} ⊔ Ideal.span {X ^ M})).mul_mem_right (X ^ (s - n)) ha
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hs] at hrel
  obtain ⟨u, hu, v, hv, heq⟩ := Submodule.mem_sup.mp hrel
  rw [← piCurrentMap_C_mul_X_pow, ← heq, map_add,
    piCurrentMap_relationIdeal F π P M hP hM hv, add_zero]
  exact piCurrentMap_ideal F π I N hπ hF hu

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_monomial
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_C_mul_X_pow
#print axioms VOA.DeligneAudit.SL4T.PiCharacteristic.mul
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_truncation
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_relationIdeal
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_ideal
#print axioms VOA.DeligneAudit.SL4T.piCurrentMap_cell
