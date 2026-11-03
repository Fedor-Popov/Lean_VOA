import VOA.Huang.UniformConvGeometric

/-!
# Separate equations stated as identities of double series

Consumers obtain differential equations as identities of formal double power series:
`D^s φ = Σ_{k<s} G_k · D^k φ`, where `D` acts diagonally and `·` is the Cauchy product.
`diagonalFuchsian_of_conv` converts such an identity into the coefficient form
`DiagonalFuchsian` (moving the constant terms of the `G_k` to the left).
`coeff_bound_of_summable` supplies the polydisc coefficient bounds of `SeparateSystem`
from absolute convergence of a coefficient series at a polyradius (Cauchy-type bound).
-/

noncomputable section
namespace VOA.Huang.UniformConv
open scoped BigOperators

/-- Cauchy product of two double coefficient arrays. -/
def conv (g c : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), g (m - i) (n - j) * c i j

/-- Diagonal action with eigenvalue `e`, iterated `k` times. -/
def diagPow (e : ℕ → ℕ → ℂ) (k : ℕ) (c : ℕ → ℕ → ℂ) (i j : ℕ) : ℂ := e i j ^ k * c i j

/-- Split a double sum over the box `[0,m]×[0,n]` into its corner and the rest. -/
theorem sum_box_split (F : ℕ → ℕ → ℂ) (m n : ℕ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), F i j =
      F m n + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        if i + j < m + n then F i j else 0 := by
  have hpt : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (n + 1),
      F i j = (if i = m ∧ j = n then F i j else 0) + (if i + j < m + n then F i j else 0) := by
    intro i hi j hj
    have him : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
    have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
    by_cases h : i = m ∧ j = n
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have hlt : i + j < m + n := by omega
      simp [h, hlt]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hpt i hi j hj]
  simp only [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single n]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

/-- **Series form ⇒ coefficient form.** An identity
`D^s φ = Σ_{k<s} G_k · D^k φ` of double series gives `DiagonalFuchsian`. -/
theorem diagonalFuchsian_of_conv {e : ℕ → ℕ → ℂ} {s : ℕ} {g : ℕ → ℕ → ℕ → ℂ}
    {c : ℕ → ℕ → ℂ}
    (h : ∀ m n, diagPow e s c m n =
      ∑ k ∈ Finset.range s, conv (g k) (diagPow e k c) m n) :
    DiagonalFuchsian e s g c := by
  intro m n
  have hmn := h m n
  simp only [diagPow, conv] at hmn
  -- exchange the `k`-sum with the box sum, then split off the corner
  have hswap : ∑ k ∈ Finset.range s, ∑ i ∈ Finset.range (m + 1),
      ∑ j ∈ Finset.range (n + 1), g k (m - i) (n - j) * (e i j ^ k * c i j) =
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range s, g k (m - i) (n - j) * e i j ^ k * c i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hswap, sum_box_split] at hmn
  simp only [Nat.sub_self] at hmn
  rw [sub_mul, Finset.sum_mul, hmn]
  ring

/-- **Polydisc coefficient bound.** Absolute convergence of the coefficient series at a
polyradius `(ρ₁, ρ₂)` bounds every coefficient by `G ρ₁^(-i) ρ₂^(-j)`. -/
theorem coeff_bound_of_summable {g : ℕ → ℕ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hs : Summable (fun p : ℕ × ℕ => ‖g p.1 p.2‖ * ρ₁ ^ p.1 * ρ₂ ^ p.2)) :
    ∀ i j, ‖g i j‖ ≤ (∑' p : ℕ × ℕ, ‖g p.1 p.2‖ * ρ₁ ^ p.1 * ρ₂ ^ p.2) *
      ρ₁⁻¹ ^ i * ρ₂⁻¹ ^ j := by
  intro i j
  have hle := hs.le_tsum (i, j) (fun p _ => by positivity)
  have hpos : 0 < ρ₁ ^ i * ρ₂ ^ j := by positivity
  have hinv : ρ₁⁻¹ ^ i * ρ₂⁻¹ ^ j = (ρ₁ ^ i * ρ₂ ^ j)⁻¹ := by
    rw [inv_pow, inv_pow, mul_inv]
  rw [mul_assoc, hinv, ← div_eq_mul_inv, le_div_iff₀ hpos]
  simpa [mul_assoc] using hle

end VOA.Huang.UniformConv
