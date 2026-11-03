import VOA.Classification.COne.PlusSplitZhuCommutative
import VOA.Classification.COne.PlusSplitResonantLifts

/-! The original normal-form input is equivalent to three boundary memberships.
These memberships remain open; the equivalence does not assume semisimplicity. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuNormalForms
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance boundaryRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance boundaryAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

theorem omegaCount_ge_four (hm2 : 2 ≤ m) : 4 ≤ omegaCount m := by
  by_cases h4 : 4 ≤ m
  · have := wCount_le m
    unfold omegaCount
    omega
  · have hns : ¬ IsSquare m := by
      rintro ⟨n, hn⟩
      have hn2 : n < 2 := by nlinarith
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl <;> simp at hn <;> omega
    simp only [omegaCount, wCount, if_neg hns, Nat.sub_zero]
    omega

/-- Left omega stability follows from the two list-boundary memberships. -/
theorem omega_stable_of_boundaries (hm2 : 2 ≤ m)
    (ho : generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)))
    (hw : generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm))) :
    ∀ x ∈ Submodule.span ℂ (Set.range (monomial m hm)),
      generator m hm 0 * x ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rcases j with i | i | i
    · by_cases hi : i.val + 1 < omegaCount m
      · simpa only [monomial, pow_succ'] using omega_power_mem m hm (i.val + 1) hi
      · have he : i.val + 1 = omegaCount m := by have := i.isLt; omega
        simpa only [monomial, ← pow_succ', he] using ho
    · by_cases hi : i.val + 1 < wCount m
      · simpa only [monomial, pow_succ', mul_assoc] using omega_power_W_mem m hm (i.val + 1) hi
      · have he : i.val + 1 = wCount m := by have := i.isLt; omega
        simpa only [monomial, ← mul_assoc, ← pow_succ', he] using hw
    · exact omega_mul_E_monomial_mem m hm hm2 i
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hx

/-- Three boundary products suffice for all 3(m+7) original reductions. -/
theorem normalFormReductions_of_boundaries (hm2 : 2 ≤ m)
    (ho : generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)))
    (hw : generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)))
    (hee : generator m hm 2 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm))) :
    ∀ (i : Fin 3) (j : Index m), generator m hm i * monomial m hm j ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  let S := Submodule.span ℂ (Set.range (monomial m hm))
  have hs := omega_stable_of_boundaries m hm hm2 ho hw
  have hp (n : ℕ) (x : VOA.A (V2mPlus m hm)) (hx : x ∈ S) :
      generator m hm 0 ^ n * x ∈ S := by
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [pow_succ', mul_assoc] using hs _ ih
  have hw0 : generator m hm 1 ∈ S := by
    by_cases hz : wCount m = 0
    · simpa only [hz, pow_zero, one_mul] using hw
    · simpa using omega_power_W_mem m hm 0 (by omega)
  have hw2 : generator m hm 1 ^ 2 ∈ S := by
    rw [W_squared]
    have hcount := omegaCount_ge_four m hm2
    have h1 : generator m hm 0 ∈ S := by simpa using omega_power_mem m hm 1 (by omega)
    have h2 : generator m hm 0 ^ 2 ∈ S := omega_power_mem m hm 2 (by omega)
    have h3 : generator m hm 0 ^ 3 ∈ S := omega_power_mem m hm 3 (by omega)
    have hw1 : generator m hm 0 * generator m hm 1 ∈ S := by simpa using hp 1 _ hw0
    have hww2 := hp 2 _ hw0
    repeat first
      | apply Submodule.add_mem
      | apply Submodule.sub_mem
      | apply Submodule.smul_mem
      | assumption
  intro i j
  fin_cases i
  · exact hs _ (Submodule.subset_span ⟨j, rfl⟩)
  · rcases j with j | j | j
    · change generator m hm 1 * generator m hm 0 ^ j.val ∈ S
      rw [((omega_commute m hm (generator m hm 1)).pow_left j.val).eq.symm]
      exact hp _ _ hw0
    · change generator m hm 1 * (generator m hm 0 ^ j.val * generator m hm 1) ∈ S
      rw [← mul_assoc, ((omega_commute m hm (generator m hm 1)).pow_left j.val).eq.symm,
        mul_assoc, ← pow_two]
      exact hp _ _ hw2
    · exact W_mul_E_monomial_mem m hm hm2 j
  · rcases j with j | j | j
    · exact E_mul_omega_monomial_mem m hm hm2 j
    · exact E_mul_W_monomial_mem m hm hm2 j
    · change generator m hm 2 * (generator m hm 0 ^ j.val * generator m hm 2) ∈ S
      rw [← mul_assoc, ((omega_commute m hm (generator m hm 2)).pow_left j.val).eq.symm,
        mul_assoc, ← pow_two]
      exact hp _ _ hee

/-- The three residual memberships are necessary as well as sufficient. -/
theorem boundaries_of_normalFormReductions
    (hr : ∀ (i : Fin 3) (j : Index m), generator m hm i * monomial m hm j ∈
      Submodule.span ℂ (Set.range (monomial m hm))) :
    generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)) ∧
    generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) ∧
    generator m hm 2 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm)) := by
  have hop := omegaCount_pos m
  refine ⟨?_, ?_, ?_⟩
  · have h := hr 0 (.inl ⟨omegaCount m - 1, by omega⟩)
    simpa only [monomial, ← pow_succ', Nat.sub_add_cancel hop] using h
  · by_cases hz : wCount m = 0
    · have h := hr 1 (.inl ⟨0, hop⟩)
      simpa only [monomial, hz, pow_zero, mul_one, one_mul] using h
    · have h := hr 0 (.inr (.inl ⟨wCount m - 1, by omega⟩))
      simpa only [monomial, ← mul_assoc, ← pow_succ',
        Nat.sub_add_cancel (by omega : 1 ≤ wCount m)] using h
  · have h := hr 2 (.inr (.inr 0))
    simpa only [monomial, Fin.val_zero, pow_zero, one_mul, pow_two] using h

end VOA.Classification.COne.PlusZhuNormalForms

namespace VOA.Classification.COne
open PlusZhuNormalForms

/-- OPEN: the pure omega boundary, the W boundary (W itself for nonsquares),
and E². This is equivalent to the original normal-form input. -/
def V2mPlusZhuBoundaryReductions : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
    letI := instRingA (V2mPlus m hm)
    letI := instAlgebraA (V2mPlus m hm)
    generator m hm 0 ^ omegaCount m ∈ Submodule.span ℂ (Set.range (monomial m hm)) ∧
    generator m hm 0 ^ wCount m * generator m hm 1 ∈
      Submodule.span ℂ (Set.range (monomial m hm)) ∧
    generator m hm 2 ^ 2 ∈ Submodule.span ℂ (Set.range (monomial m hm))

theorem zhuNormalFormReductions_iff_boundaryReductions :
    V2mPlusZhuNormalFormReductions ↔ V2mPlusZhuBoundaryReductions := by
  constructor
  · intro hr m hm hm2
    exact boundaries_of_normalFormReductions m hm (hr m hm hm2)
  · intro hr m hm hm2
    obtain ⟨ho, hw, hee⟩ := hr m hm hm2
    exact normalFormReductions_of_boundaries m hm hm2 ho hw hee

theorem rationality_of_twistedTopModels_boundaryReductions_resonant
    (ht : V2mPlusTwistedTopModels)
    (hr : V2mPlusZhuBoundaryReductions)
    (hgen : V2mPlusResonantGeneratorComplements) : V2mPlusRationalFactGe2 :=
  rationality_of_twistedTopModels_normalForms_resonant ht
    (zhuNormalFormReductions_iff_boundaryReductions.mpr hr) hgen

end VOA.Classification.COne
