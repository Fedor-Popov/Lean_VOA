import VOA.Classification.COne.OrbRat5UJ
import VOA.Classification.COne.OrbRat5Char
import VOA.Classification.COne.PlusRat4SignModel

/-! # `V₈⁺` in weights `≤ 4` and the cubic automorphism

* `low_fixed`: every vector of `V₈⁺` of weight `≤ 3` is fixed by every automorphism of the form
  "fixes `𝟙` and `ω`" — concretely by `plusCubic` (the weight-`≤ 3` space is spanned by
  `𝟙, ω, ω₍₀₎ω`).
* `four_decomp`: every weight-four vector of `V₈⁺` is `f + γ J + δ E` with `f` a combination of
  `ω₍₋₁₎ω` and `ω₍₀₎ω₍₀₎ω` (hence `plusCubic`-fixed).

Machine content: a classification of Fock monomials of weight four (`weight_eq_four`), the charge
analysis of `V₈` in weights `≤ 4`, the parity projection `½(1+σ)`, and five kernel certificates
(`neutralAction` of `OrbRat3Eval`) expressing the even Fock monomials through Virasoro descendants.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat5

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f LatMod
  OrbRat3

/-! ## §1 Fock monomials of weight four -/

section WeightFour

variable (r : ℕ)

theorem single_two {r : ℕ} (x : ℕ × Fin r) :
    Finsupp.single x 2 = Finsupp.single x 1 + Finsupp.single x 1 := by
  rw [← Finsupp.single_add]

theorem single_three {r : ℕ} (x : ℕ × Fin r) :
    Finsupp.single x 3 = Finsupp.single x 1 + Finsupp.single x 1 + Finsupp.single x 1 := by
  rw [← Finsupp.single_add, ← Finsupp.single_add]

theorem single_four {r : ℕ} (x : ℕ × Fin r) :
    Finsupp.single x 4 =
      Finsupp.single x 1 + Finsupp.single x 1 + Finsupp.single x 1 + Finsupp.single x 1 := by
  rw [← Finsupp.single_add, ← Finsupp.single_add, ← Finsupp.single_add]

theorem weight_eq_four (d : (ℕ × Fin r) →₀ ℕ) (h : Finsupp.weight weightFnN d = 4) :
    (∃ a : Fin r, d = Finsupp.single (3, a) 1) ∨
      (∃ a b : Fin r, d = Finsupp.single (2, a) 1 + Finsupp.single (0, b) 1) ∨
      (∃ a b : Fin r, d = Finsupp.single (1, a) 1 + Finsupp.single (1, b) 1) ∨
      (∃ a b c : Fin r, d = Finsupp.single (1, a) 1 + Finsupp.single (0, b) 1 +
        Finsupp.single (0, c) 1) ∨
      ∃ a b c e : Fin r, d = Finsupp.single (0, a) 1 + Finsupp.single (0, b) 1 +
        Finsupp.single (0, c) 1 + Finsupp.single (0, e) 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨⟨m, a⟩, hx⟩ := Finsupp.ne_iff.mp hd
  rw [Finsupp.coe_zero, Pi.zero_apply] at hx
  have hs : Finsupp.weight weightFnN d =
      d (m, a) * (m + 1) + Finsupp.weight weightFnN (d.erase (m, a)) :=
    weight_split r d (m, a)
  rw [h] at hs
  have h1 : d (m, a) ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : m + 1 ≤ d (m, a) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
  have hdecomp := Finsupp.single_add_erase (m, a) d
  have hn4 : d (m, a) ≤ 4 := by omega
  have hm3 : m ≤ 3 := by omega
  interval_cases hn : d (m, a)
  · exact absurd rfl hx
  · interval_cases m
    · rcases weight_eq_three r (d.erase (0, a)) (by omega) with
        ⟨b, hb⟩ | ⟨b, c, hb⟩ | ⟨b, c, e, hb⟩
      · right; left
        exact ⟨b, a, by rw [← hdecomp, hb, add_comm]⟩
      · right; right; right; left
        exact ⟨b, a, c, by rw [← hdecomp, hb]; abel⟩
      · right; right; right; right
        exact ⟨a, b, c, e, by rw [← hdecomp, hb]; abel⟩
    · rcases weight_eq_two r (d.erase (1, a)) (by omega) with ⟨b, hb⟩ | ⟨b, c, hb⟩
      · right; right; left
        exact ⟨a, b, by rw [← hdecomp, hb]⟩
      · right; right; right; left
        exact ⟨a, b, c, by rw [← hdecomp, hb]; abel⟩
    · obtain ⟨b, hb⟩ := weight_eq_one r (d.erase (2, a)) (by omega)
      right; left
      exact ⟨a, b, by rw [← hdecomp, hb]⟩
    · have he : d.erase (3, a) = 0 := weight_eq_zero_iff r _ (by omega)
      left; exact ⟨a, by rw [← hdecomp, he, add_zero]⟩
  · interval_cases m
    · rcases weight_eq_two r (d.erase (0, a)) (by omega) with ⟨b, hb⟩ | ⟨b, c, hb⟩
      · right; right; right; left
        exact ⟨b, a, a, by rw [← hdecomp, hb, single_two]; abel⟩
      · right; right; right; right
        exact ⟨a, a, b, c, by rw [← hdecomp, hb, single_two]; abel⟩
    · have he : d.erase (1, a) = 0 := weight_eq_zero_iff r _ (by omega)
      right; right; left
      exact ⟨a, a, by rw [← hdecomp, he, add_zero, single_two]⟩
    · omega
    · omega
  · interval_cases m
    · obtain ⟨b, hb⟩ := weight_eq_one r (d.erase (0, a)) (by omega)
      right; right; right; right
      refine ⟨a, a, a, b, ?_⟩
      rw [← hdecomp, hb, single_three]
    all_goals omega
  · interval_cases m
    · have he : d.erase (0, a) = 0 := weight_eq_zero_iff r _ (by omega)
      right; right; right; right
      refine ⟨a, a, a, a, ?_⟩
      rw [← hdecomp, he, add_zero, single_four]
    all_goals omega

end WeightFour

/-! ## §2 Rank-one Fock spans -/

/-- The oscillator `h(-k-1)` of `V₈`. -/
abbrev xx (k : ℕ) : FockN (rank (latP 4)) := X ((k : ℕ), a0 4)

theorem fin_eq_a0 (a : Fin (rank (latP 4))) : a = a0 4 := by
  apply Fin.ext
  have h1 := a.isLt
  have h2 : rank (latP 4) = 1 := rank_latP 4
  simp only [a0]
  omega

/-- A homogeneous Fock vector lies in every submodule containing its monomials. -/
theorem mem_of_monomials {w : ℕ} {S : Submodule ℂ (FockN (rank (latP 4)))}
    (hS : ∀ d : (ℕ × Fin (rank (latP 4))) →₀ ℕ, Finsupp.weight weightFnN d = w →
      (monomial d (1 : ℂ) : FockN (rank (latP 4))) ∈ S)
    {p : FockN (rank (latP 4))} (hp : p ∈ gradingWN (rank (latP 4)) w) : p ∈ S := by
  classical
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight weightFnN d = w := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [show monomial d (coeff d p) = coeff d p • (monomial d (1 : ℂ) : FockN (rank (latP 4))) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (hS d hw)

theorem monomial_two (u v : ℕ × Fin (rank (latP 4))) :
    (monomial (Finsupp.single u 1 + Finsupp.single v 1) (1 : ℂ) : FockN (rank (latP 4))) =
      X u * X v := by
  change _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
  rw [monomial_mul, mul_one]

theorem monomial_three (u v w : ℕ × Fin (rank (latP 4))) :
    (monomial (Finsupp.single u 1 + Finsupp.single v 1 + Finsupp.single w 1) (1 : ℂ) :
      FockN (rank (latP 4))) = X u * X v * X w := by
  change _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
  rw [monomial_mul, monomial_mul, mul_one, mul_one]

theorem monomial_four (u v w t : ℕ × Fin (rank (latP 4))) :
    (monomial (Finsupp.single u 1 + Finsupp.single v 1 + Finsupp.single w 1 +
      Finsupp.single t 1) (1 : ℂ) : FockN (rank (latP 4))) = X u * X v * X w * X t := by
  change _ = monomial _ (1 : ℂ) * monomial _ (1 : ℂ) * monomial _ (1 : ℂ) * monomial _ (1 : ℂ)
  rw [monomial_mul, monomial_mul, monomial_mul, mul_one, mul_one, mul_one]

/-- The monomials of weight `≤ 3`. -/
def lowMonomials : Set (FockN (rank (latP 4))) :=
  {1, xx 0, xx 1, xx 0 * xx 0, xx 2, xx 1 * xx 0, xx 0 * xx 0 * xx 0}

theorem fock_low_mem_span {k : ℕ} (hk : k ≤ 3) {p : FockN (rank (latP 4))}
    (hp : p ∈ gradingWN (rank (latP 4)) k) : p ∈ Submodule.span ℂ lowMonomials := by
  apply mem_of_monomials _ hp
  intro d hd
  have hmem : ∀ x ∈ lowMonomials, x ∈ Submodule.span ℂ lowMonomials :=
    fun x hx => Submodule.subset_span hx
  interval_cases k
  · rw [weight_eq_zero_iff _ d hd, monomial_zero', C_1]
    exact hmem _ (by simp [lowMonomials])
  · obtain ⟨a, rfl⟩ := weight_eq_one _ d hd
    rw [fin_eq_a0 a]
    exact hmem (xx 0) (by simp [lowMonomials])
  · rcases weight_eq_two _ d hd with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · rw [fin_eq_a0 a]; exact hmem (xx 1) (by simp [lowMonomials])
    · rw [fin_eq_a0 a, fin_eq_a0 b, monomial_two]; exact hmem _ (by simp [lowMonomials])
  · rcases weight_eq_three _ d hd with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩
    · rw [fin_eq_a0 a]; exact hmem (xx 2) (by simp [lowMonomials])
    · rw [fin_eq_a0 a, fin_eq_a0 b, monomial_two]; exact hmem _ (by simp [lowMonomials])
    · rw [fin_eq_a0 a, fin_eq_a0 b, fin_eq_a0 c, monomial_three]
      exact hmem _ (by simp [lowMonomials])

/-- The monomials of weight four. -/
def fourMonomials : Set (FockN (rank (latP 4))) :=
  {xx 3, xx 2 * xx 0, xx 1 * xx 1, xx 1 * xx 0 * xx 0, xx 0 * xx 0 * xx 0 * xx 0}

theorem fock_four_mem_span {p : FockN (rank (latP 4))}
    (hp : p ∈ gradingWN (rank (latP 4)) 4) : p ∈ Submodule.span ℂ fourMonomials := by
  apply mem_of_monomials _ hp
  intro d hd
  have hmem : ∀ x ∈ fourMonomials, x ∈ Submodule.span ℂ fourMonomials :=
    fun x hx => Submodule.subset_span hx
  rcases weight_eq_four _ d hd with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ |
      ⟨a, b, c, e, rfl⟩
  · rw [fin_eq_a0 a]; exact hmem (xx 3) (by simp [fourMonomials])
  · rw [fin_eq_a0 a, fin_eq_a0 b, monomial_two]; exact hmem _ (by simp [fourMonomials])
  · rw [fin_eq_a0 a, fin_eq_a0 b, monomial_two]; exact hmem _ (by simp [fourMonomials])
  · rw [fin_eq_a0 a, fin_eq_a0 b, fin_eq_a0 c, monomial_three]
    exact hmem _ (by simp [fourMonomials])
  · rw [fin_eq_a0 a, fin_eq_a0 b, fin_eq_a0 c, fin_eq_a0 e, monomial_four]
    exact hmem _ (by simp [fourMonomials])

/-! ## §3 The parity projection -/

/-- `½(1 + σ)` on the Fock space. -/
def evenPart : FockN (rank (latP 4)) →ₗ[ℂ] FockN (rank (latP 4)) :=
  (1 / 2 : ℂ) • (LinearMap.id + (sigmaN (rank (latP 4))).toLinearMap)

theorem evenPart_apply (p : FockN (rank (latP 4))) :
    evenPart p = (1 / 2 : ℂ) • (p + sigmaN (rank (latP 4)) p) := rfl

theorem evenPart_odd {p : FockN (rank (latP 4))} (h : sigmaN (rank (latP 4)) p = -p) :
    evenPart p = 0 := by
  rw [evenPart_apply, h, add_neg_cancel, smul_zero]

theorem evenPart_even {p : FockN (rank (latP 4))} (h : sigmaN (rank (latP 4)) p = p) :
    evenPart p = p := by
  rw [evenPart_apply, h, ← two_smul ℂ p, smul_smul]
  norm_num

theorem sigma_xx (k : ℕ) : sigmaN (rank (latP 4)) (xx k) = -xx k := sigmaN_X _ _

/-- The even low monomials. -/
def lowEven : Set (FockN (rank (latP 4))) := {1, xx 0 * xx 0, xx 1 * xx 0}

theorem evenPart_low_mem {p : FockN (rank (latP 4))} (hp : p ∈ Submodule.span ℂ lowMonomials) :
    evenPart p ∈ Submodule.span ℂ lowEven := by
  have h := Submodule.mem_map_of_mem (f := evenPart) hp
  rw [Submodule.map_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨x, hx, rfl⟩
  simp only [lowMonomials, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hm : ∀ y ∈ lowEven, y ∈ (Submodule.span ℂ lowEven : Set _) :=
    fun y hy => Submodule.subset_span hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [evenPart_even (sigmaN_one _)]; exact hm _ (by simp [lowEven])
  · rw [evenPart_odd (sigma_xx 0)]; exact Submodule.zero_mem _
  · rw [evenPart_odd (sigma_xx 1)]; exact Submodule.zero_mem _
  · rw [evenPart_even (by rw [sigmaN_mul, sigma_xx, neg_mul_neg])]
    exact hm _ (by simp [lowEven])
  · rw [evenPart_odd (sigma_xx 2)]; exact Submodule.zero_mem _
  · rw [evenPart_even (by rw [sigmaN_mul, sigma_xx, sigma_xx, neg_mul_neg])]
    exact hm _ (by simp [lowEven])
  · rw [evenPart_odd (by rw [sigmaN_mul, sigmaN_mul, sigma_xx]; ring)]
    exact Submodule.zero_mem _

/-- The even weight-four monomials. -/
def fourEven : Set (FockN (rank (latP 4))) :=
  {xx 2 * xx 0, xx 1 * xx 1, xx 0 * xx 0 * xx 0 * xx 0}

theorem evenPart_four_mem {p : FockN (rank (latP 4))}
    (hp : p ∈ Submodule.span ℂ fourMonomials) : evenPart p ∈ Submodule.span ℂ fourEven := by
  have h := Submodule.mem_map_of_mem (f := evenPart) hp
  rw [Submodule.map_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨x, hx, rfl⟩
  simp only [fourMonomials, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hm : ∀ y ∈ fourEven, y ∈ (Submodule.span ℂ fourEven : Set _) :=
    fun y hy => Submodule.subset_span hy
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · rw [evenPart_odd (sigma_xx 3)]; exact Submodule.zero_mem _
  · rw [evenPart_even (by rw [sigmaN_mul, sigma_xx, sigma_xx, neg_mul_neg])]
    exact hm _ (by simp [fourEven])
  · rw [evenPart_even (by rw [sigmaN_mul, sigma_xx, neg_mul_neg])]
    exact hm _ (by simp [fourEven])
  · rw [evenPart_odd (by rw [sigmaN_mul, sigmaN_mul, sigma_xx, sigma_xx]; ring)]
    exact Submodule.zero_mem _
  · rw [evenPart_even (by rw [sigmaN_mul, sigmaN_mul, sigmaN_mul, sigma_xx]; ring)]
    exact hm _ (by simp [fourEven])

end VOA.Classification.COne.OrbRat5
