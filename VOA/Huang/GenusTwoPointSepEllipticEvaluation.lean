import VOA.Huang.GenusTwoPointSepKernels

/-!
# Analytic evaluation of the formal elliptic coefficient arrays

The two lattice cones in the product chart are reindexed by the Fourier mode
and its geometric-series multiplicity. Absolute summability justifies the
reindexing and summation. This identifies the arrays with convergent Fourier
series on the full bidisc, without asserting a lattice-Weierstrass comparison.
-/

noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.HuangODEThree
open scoped BigOperators

/-- Positive Fourier modes, including the q-constant term. -/
def positiveEllipticArray (d i j : ℕ) : ℂ :=
  if i < j ∧ (j - i) ∣ i then ((j - i : ℕ) : ℂ) ^ d else 0

theorem ellipticArray_eq_positive_sub (d i j : ℕ) :
    ellipticArray d i j =
      positiveEllipticArray d i j - (-1 : ℂ) ^ d * positiveEllipticArray d j i := by
  unfold ellipticArray positiveEllipticArray
  split_ifs <;> first | omega | ring

theorem positiveEllipticArray_joint (d : ℕ) : JointSubexponential (positiveEllipticArray d) := by
  intro r hr
  obtain ⟨C, hC⟩ := subexponential_pow d r hr
  refine ⟨C, fun i j => le_trans ?_ (hC (i + j))⟩
  unfold positiveEllipticArray
  split_ifs
  · simp only [norm_pow, Complex.norm_natCast]
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast (show j - i ≤ i + j by omega)) _
  · simp only [norm_zero]; positivity

/-- The positive cone parametrization uses strictly positive Fourier modes. -/
def positiveFourierIndex (p : ℕ × ℕ) : ℕ × ℕ :=
  ((p.1 + 1) * p.2, (p.1 + 1) * (p.2 + 1))

theorem positiveFourierIndex_injective : Function.Injective positiveFourierIndex := by
  rintro ⟨r, l⟩ ⟨s, m⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [positiveFourierIndex] at h₁ h₂
  have hrs : r = s := by nlinarith
  subst s
  have hlm : l = m := by nlinarith
  subst m
  rfl

theorem positiveEllipticArray_index (d r l : ℕ) :
    positiveEllipticArray d ((r + 1) * l) ((r + 1) * (l + 1)) = (r + 1 : ℂ) ^ d := by
  have hlt : (r + 1) * l < (r + 1) * (l + 1) := by nlinarith
  have hsub : (r + 1) * (l + 1) - (r + 1) * l = r + 1 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_left]
  simp [positiveEllipticArray, hlt, hsub]

theorem positiveEllipticArray_support (d : ℕ) :
    Function.support (fun p : ℕ × ℕ => positiveEllipticArray d p.1 p.2) ⊆
      Set.range positiveFourierIndex := by
  rintro ⟨i, j⟩ hp
  have h : i < j ∧ (j - i) ∣ i := by
    by_contra h
    exact hp (by simp [positiveEllipticArray, h])
  obtain ⟨l, hl⟩ := h.2
  have hj : 0 < j - i := by omega
  have he : j - i - 1 + 1 = j - i := by omega
  refine ⟨(j - i - 1, l), ?_⟩
  apply Prod.ext
  · simpa only [positiveFourierIndex, he] using hl.symm
  · simp only [positiveFourierIndex, he]
    rw [Nat.mul_add, Nat.mul_one, ← hl]
    omega

theorem summable_positiveEllipticArray (d : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ => positiveEllipticArray d p.1 p.2 * x ^ p.1 * y ^ p.2) :=
  Summable.of_norm (summable_of_jointSubexponential (positiveEllipticArray_joint d) hx hy)

/-- One geometric row, with all sums interpreted analytically. -/
theorem positiveEllipticArray_row (d r : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' l : ℕ, positiveEllipticArray d ((r + 1) * l) ((r + 1) * (l + 1)) *
      x ^ ((r + 1) * l) * y ^ ((r + 1) * (l + 1))) =
      (r + 1 : ℂ) ^ d * y ^ (r + 1) / (1 - (x * y) ^ (r + 1)) := by
  have hxy : ‖x * y‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hp : ‖(x * y) ^ (r + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hxy (by omega)
  simp_rw [positiveEllipticArray_index]
  have he : ∀ l : ℕ,
      (r + 1 : ℂ) ^ d * x ^ ((r + 1) * l) * y ^ ((r + 1) * (l + 1)) =
      ((r + 1 : ℂ) ^ d * y ^ (r + 1)) * ((x * y) ^ (r + 1)) ^ l := by
    intro l
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul, mul_pow, pow_mul]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hp, div_eq_mul_inv]

/-- The positive cone evaluates to its convergent Fourier denominator series. -/
theorem positiveEllipticArray_eval (d : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' p : ℕ × ℕ, positiveEllipticArray d p.1 p.2 * x ^ p.1 * y ^ p.2) =
      ∑' r : ℕ, (r + 1 : ℂ) ^ d * y ^ (r + 1) / (1 - (x * y) ^ (r + 1)) := by
  have hs := summable_positiveEllipticArray d hx hy
  have hreindex := positiveFourierIndex_injective.tsum_eq
    (f := fun p : ℕ × ℕ => positiveEllipticArray d p.1 p.2 * x ^ p.1 * y ^ p.2) (by
      intro p hp
      apply positiveEllipticArray_support d
      intro hz
      exact hp (by simp [hz]))
  rw [← hreindex]
  have hprod := (hs.comp_injective positiveFourierIndex_injective).tsum_prod
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  exact tsum_congr fun r => positiveEllipticArray_row d r hx hy

/-- Absolute reindexing also proves summability of the Fourier-mode series. -/
theorem summable_positiveEllipticFourier (d : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun r : ℕ =>
      (r + 1 : ℂ) ^ d * y ^ (r + 1) / (1 - (x * y) ^ (r + 1))) := by
  have hs := ((summable_positiveEllipticArray d hx hy).comp_injective
    positiveFourierIndex_injective).prod
  exact hs.congr fun r => positiveEllipticArray_row d r hx hy

/-- The formal elliptic array is exactly the analytic two-oriented Fourier sum
on the whole product bidisc. This statement includes x=0 and y=0. -/
theorem ellipticSeries_eval_fourier (d : ℕ) {x y : ℂ}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    (∑' p : ℕ × ℕ, coeff (ellipticSeries d) p.1 p.2 * x ^ p.1 * y ^ p.2) =
      ∑' r : ℕ, (r + 1 : ℂ) ^ d *
        (y ^ (r + 1) - (-1 : ℂ) ^ d * x ^ (r + 1)) /
          (1 - (x * y) ^ (r + 1)) := by
  have hs := summable_positiveEllipticArray d hx hy
  have ht := (summable_positiveEllipticArray d hy hx).prod_symm
  simp only [Prod.fst_swap, Prod.snd_swap] at ht
  have he : ∀ p : ℕ × ℕ,
      coeff (ellipticSeries d) p.1 p.2 * x ^ p.1 * y ^ p.2 =
      positiveEllipticArray d p.1 p.2 * x ^ p.1 * y ^ p.2 -
        (-1 : ℂ) ^ d * (positiveEllipticArray d p.2 p.1 * y ^ p.2 * x ^ p.1) := by
    intro p
    simp only [ellipticSeries, coeff_ofArray, ellipticArray_eq_positive_sub]
    ring
  simp_rw [he]
  rw [hs.tsum_sub (ht.mul_left _), tsum_mul_left,
    positiveEllipticArray_eval d hx hy]
  have hswap : (∑' p : ℕ × ℕ, positiveEllipticArray d p.2 p.1 * y ^ p.2 * x ^ p.1) =
      ∑' p : ℕ × ℕ, positiveEllipticArray d p.1 p.2 * y ^ p.1 * x ^ p.2 := by
    simpa only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] using
      (Equiv.prodComm ℕ ℕ).tsum_eq
        (fun p : ℕ × ℕ => positiveEllipticArray d p.1 p.2 * y ^ p.1 * x ^ p.2)
  rw [hswap, positiveEllipticArray_eval d hy hx, mul_comm y x, ← tsum_mul_left,
    ← (summable_positiveEllipticFourier d hx hy).tsum_sub
      (by simpa [mul_comm y x] using
        ((summable_positiveEllipticFourier d hy hx).mul_left ((-1 : ℂ) ^ d)))]
  apply tsum_congr
  intro r
  ring

end VOA.Huang.GenusTwoPoint.Separate
