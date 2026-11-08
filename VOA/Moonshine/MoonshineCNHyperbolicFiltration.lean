import VOA.Moonshine.MoonshineCNHyperbolicSugawara

/-! # The b-count, b-level filtration

The lower subspace is defined by the actual monomial support. In particular,
the leading-term assertion below is a strict filtration estimate for the
existing Sugawara operator, not a new assumption on an abstract operator.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

def hypBCountWeight (v : ℕ × Fin 2) : ℕ := if v.2 = 1 then 1 else 0

def hypBLevelWeight (v : ℕ × Fin 2) : ℕ := if v.2 = 1 then v.1 + 1 else 0

def hypBHomogeneous (d w : ℕ) : Submodule ℂ hypFock :=
  weightedHomogeneousSubmodule ℂ hypBCountWeight d ⊓
    weightedHomogeneousSubmodule ℂ hypBLevelWeight w

/-- Strict lexicographic lower filtration: count first, then level. -/
def hypBFiltered (d w : ℕ) : Submodule ℂ hypFock :=
  Finsupp.supported ℂ ℂ {e : (ℕ × Fin 2) →₀ ℕ |
    Finsupp.weight hypBCountWeight e < d ∨
      (Finsupp.weight hypBCountWeight e = d ∧ Finsupp.weight hypBLevelWeight e < w)}

theorem hypBFiltered_mem (d w : ℕ) (p : hypFock) :
    p ∈ hypBFiltered d w ↔ ∀ e, coeff e p ≠ 0 →
      Finsupp.weight hypBCountWeight e < d ∨
        (Finsupp.weight hypBCountWeight e = d ∧ Finsupp.weight hypBLevelWeight e < w) := by
  change (∀ e ∈ p.support, Finsupp.weight hypBCountWeight e < d ∨
    (Finsupp.weight hypBCountWeight e = d ∧ Finsupp.weight hypBLevelWeight e < w)) ↔ _
  simp only [mem_support_iff]

theorem hypBFiltered_of_count_lt {d D w : ℕ} {p : hypFock}
    (hp : p.IsWeightedHomogeneous hypBCountWeight d) (hd : d < D) :
    p ∈ hypBFiltered D w := by
  rw [hypBFiltered_mem]
  intro e he
  exact Or.inl (by rw [hp he]; exact hd)

theorem hypBFiltered_of_homogeneous {d w D W : ℕ} {p : hypFock}
    (hp : p ∈ hypBHomogeneous d w) (h : d < D ∨ (d = D ∧ w < W)) :
    p ∈ hypBFiltered D W := by
  rw [hypBFiltered_mem]
  intro e he
  simpa only [hp.1 he, hp.2 he] using h

theorem hypBFiltered_mono {d w D W : ℕ} (h : d < D ∨ (d = D ∧ w ≤ W)) :
    hypBFiltered d w ≤ hypBFiltered D W := by
  intro p hp
  rw [hypBFiltered_mem] at hp ⊢
  intro e he
  have hs := hp e he
  omega

theorem hypBHomogeneous_monomial (e : (ℕ × Fin 2) →₀ ℕ) (c : ℂ) :
    monomial e c ∈ hypBHomogeneous
      (Finsupp.weight hypBCountWeight e) (Finsupp.weight hypBLevelWeight e) :=
  ⟨isWeightedHomogeneous_monomial _ _ _ rfl,
    isWeightedHomogeneous_monomial _ _ _ rfl⟩

theorem hypBHomogeneous_mul {d w D W : ℕ} {p q : hypFock}
    (hp : p ∈ hypBHomogeneous d w) (hq : q ∈ hypBHomogeneous D W) :
    p * q ∈ hypBHomogeneous (d + D) (w + W) :=
  ⟨hp.1.mul hq.1, hp.2.mul hq.2⟩

theorem hypBHomogeneous_X (v : ℕ × Fin 2) :
    (X v : hypFock) ∈ hypBHomogeneous (hypBCountWeight v) (hypBLevelWeight v) :=
  ⟨isWeightedHomogeneous_X ℂ _ _, isWeightedHomogeneous_X ℂ _ _⟩

/-- The raising derivation preserves the number of b oscillators. -/
theorem hypRaisingDerivation_preserves_bCount (n d : ℕ) (p : hypFock)
    (hp : p.IsWeightedHomogeneous hypBCountWeight d) :
    (hypRaisingDerivation n p).IsWeightedHomogeneous hypBCountWeight d := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial e c he =>
    rw [hypRaisingDerivation, mkDerivation_monomial]
    apply (weightedHomogeneousSubmodule ℂ hypBCountWeight d).smul_mem
    rw [Finsupp.sum]
    apply Submodule.sum_mem
    intro v hv
    change (monomial (e - Finsupp.single v 1) (e v : ℂ)) *
      ((v.1 + 1 : ℂ) • X (v.1 + n, v.2)) ∈ _
    rw [mul_smul_comm]
    apply Submodule.smul_mem
    have hm := (isWeightedHomogeneous_monomial hypBCountWeight
      (e - Finsupp.single v 1) (e v : ℂ) rfl).mul
        (isWeightedHomogeneous_X (R := ℂ) hypBCountWeight (v.1 + n, v.2))
    have hw := Finsupp.weight_sub_single_add (w := hypBCountWeight)
      (Finsupp.mem_support_iff.mp hv)
    rw [he] at hw
    change (e - Finsupp.single v 1).weight hypBCountWeight +
      hypBCountWeight (v.1 + n, v.2) = d at hw
    rwa [hw] at hm

/-- The concrete leading term, strictly above every remainder term in the
b-count, b-level order. -/
theorem hypSugawara_negative_leading_filtered (κ ell : ℂ) (j d w : ℕ)
    (p : hypFock) (hp : p ∈ hypBHomogeneous d w) :
    hypSugawara κ ell (-(j + 1 : ℤ)) p - κ • (X (j, 1) * p) ∈
      hypBFiltered (d + 1) (w + j + 1) := by
  rw [hypSugawara_negative_leading_formula]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply hypBFiltered_of_count_lt (d := d) _ (by omega)
      simpa [hypBCountWeight] using
        (isWeightedHomogeneous_X (R := ℂ) hypBCountWeight (j, 0)).mul hp.1
    · rw [Finset.sum_mul]
      apply Submodule.sum_mem
      intro k hk
      apply hypBFiltered_of_homogeneous
        ((hypBHomogeneous_mul (hypBHomogeneous_mul
          (hypBHomogeneous_X (j - 1 - k, 0)) (hypBHomogeneous_X (k, 1))) hp))
      have hk' := Finset.mem_range.mp hk
      simp only [hypBCountWeight, hypBLevelWeight, show (0 : Fin 2) ≠ 1 by decide,
        if_false, if_true, zero_add]
      exact Or.inr ⟨by omega, by omega⟩
  · exact hypBFiltered_of_count_lt
      (hypRaisingDerivation_preserves_bCount (j + 1) d p hp.1) (by omega)

end VOA.Moonshine.ConwayNorton
