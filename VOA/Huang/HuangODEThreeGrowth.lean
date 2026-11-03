import VOA.Huang.FuchsianODE

/-! # A joint majorant theorem for two independent series indices

A triangular radial coefficient recurrence gives one bound in the total
degree, uniformly over both indices. Unlike convergence of every slice, this
bound proves absolute convergence on the bidisc. The recurrence is the estimate
to extract from a regular-singular three-intertwiner system; its VOA derivation
is not assumed to follow from the existing two-intertwiner equations.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open VOA Filter
open scoped BigOperators

/-- Uniform subexponential growth in the sum of the two degrees. -/
def JointSubexponential (c : ℕ → ℕ → ℂ) : Prop :=
  ∀ R : ℝ, 1 < R → ∃ K : ℝ, ∀ m n : ℕ, ‖c m n‖ ≤ K * R ^ (m + n)

/-- The strict lower-total-degree majorant supplied by a radial regular-singular
system. The divisor must grow; bounded nonvanishing alone is insufficient. -/
def RadialRecurrence (c : ℕ → ℕ → ℂ) : Prop :=
  ∃ (a p : ℕ → ℝ) (N : ℕ),
    (∀ k, 0 ≤ a k) ∧ Subexponential a ∧ Tendsto p atTop atTop ∧
    ∀ m n, N ≤ m + n → p (m + n) * ‖c m n‖ ≤
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        if i + j < m + n then a (m + n - (i + j)) * ‖c i j‖ else 0

private theorem geometric_reverse_bound {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), t ^ (m - i) ≤ (1 - t)⁻¹ := by
  have he : (∑ i ∈ Finset.range (m + 1), t ^ (m - i)) =
      ∑ i ∈ Finset.range (m + 1), t ^ i := by
    simpa using (Finset.sum_range_reflect (fun i => t ^ i) (m + 1))
  rw [he, ← tsum_geometric_of_lt_one ht₀ ht₁]
  exact (summable_geometric_of_lt_one ht₀ ht₁).sum_le_tsum _ (fun _ _ => pow_nonneg ht₀ _)

/-- A single radial recurrence controls both indices simultaneously. -/
theorem jointSubexponential_of_radialRecurrence {c : ℕ → ℕ → ℂ}
    (hc : RadialRecurrence c) : JointSubexponential c := by
  classical
  obtain ⟨a, p, N₀, ha₀, ha, hp, hrec⟩ := hc
  intro R hR
  have hR₀ : 0 < R := by linarith
  let σ : ℝ := (1 + R) / 2
  have hσ₁ : 1 < σ := by dsimp [σ]; linarith
  have hσR : σ < R := by dsimp [σ]; linarith
  have hσ₀ : 0 < σ := by linarith
  obtain ⟨D, hD⟩ := ha σ hσ₁
  have hD₀ : 0 ≤ D := le_trans (ha₀ 0) (by simpa using hD 0)
  let t := σ / R
  have ht₀ : 0 ≤ t := (div_pos hσ₀ hR₀).le
  have ht₁ : t < 1 := (div_lt_one hR₀).mpr hσR
  let L : ℝ := (1 - t)⁻¹
  have hL₀ : 0 ≤ L := inv_nonneg.mpr (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hp.eventually_ge_atTop (D * L ^ 2 + 1))
  let N := max N₀ N₁
  obtain ⟨B, hB⟩ := Finset.exists_le
    (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).image
      (fun q : ℕ × ℕ => ‖c q.1 q.2‖ / R ^ (q.1 + q.2)))
  let K := max B 0
  have hK₀ : 0 ≤ K := le_max_right _ _
  have hlow : ∀ m n, m + n < N → ‖c m n‖ ≤ K * R ^ (m + n) := by
    intro m n hmn
    have hmem : (m, n) ∈ (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)) := by
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    have hh := le_trans (hB _ (Finset.mem_image_of_mem _ hmem)) (le_max_left B 0)
    exact (div_le_iff₀ (pow_pos hR₀ _)).mp hh
  refine ⟨K, fun m n => ?_⟩
  have hall : ∀ l m n : ℕ, m + n = l → ‖c m n‖ ≤ K * R ^ (m + n) := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro m n he
      by_cases hmn : m + n < N
      · exact hlow m n hmn
      have hN : N ≤ m + n := by omega
      have hpn := hN₁ (m + n) (le_trans (le_max_right N₀ N₁) hN)
      have hpn₀ : 0 < p (m + n) := by nlinarith [sq_nonneg L]
      have hsum : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          if i + j < m + n then a (m + n - (i + j)) * ‖c i j‖ else 0) ≤
          D * K * R ^ (m + n) * L ^ 2 := by
        calc
          _ ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
              D * K * R ^ (m + n) * (t ^ (m - i) * t ^ (n - j)) := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            have him : i ≤ m := by simpa using hi
            have hjn : j ≤ n := by simpa using hj
            split_ifs with hij
            · have hci := ih (i + j) (by omega) i j rfl
              calc
                _ ≤ (D * σ ^ (m + n - (i + j))) * (K * R ^ (i + j)) :=
                  mul_le_mul (hD _) hci (norm_nonneg _) (by positivity)
                _ = _ := by
                  have hdiff : m + n - (i + j) = (m - i) + (n - j) := by omega
                  rw [hdiff, pow_add, pow_add, pow_add]
                  simp only [t, div_pow]
                  have hm : R ^ m = R ^ (m - i) * R ^ i := by
                    rw [← pow_add, Nat.sub_add_cancel him]
                  have hn : R ^ n = R ^ (n - j) * R ^ j := by
                    rw [← pow_add, Nat.sub_add_cancel hjn]
                  rw [hm, hn]
                  field_simp
            · positivity
          _ = D * K * R ^ (m + n) *
              ((∑ i ∈ Finset.range (m + 1), t ^ (m - i)) *
                ∑ j ∈ Finset.range (n + 1), t ^ (n - j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_comm
          _ ≤ _ := by
            gcongr
            simpa only [pow_two] using mul_le_mul
              (geometric_reverse_bound ht₀ ht₁ m) (geometric_reverse_bound ht₀ ht₁ n)
              (Finset.sum_nonneg fun j _ => pow_nonneg ht₀ _) hL₀
      have hbound := le_trans (hrec m n (le_trans (le_max_left N₀ N₁) hN)) hsum
      have hfactor : D * L ^ 2 ≤ p (m + n) := by linarith
      have hbound' : p (m + n) * ‖c m n‖ ≤ p (m + n) * (K * R ^ (m + n)) := by
        calc
          _ ≤ D * K * R ^ (m + n) * L ^ 2 := hbound
          _ = (D * L ^ 2) * (K * R ^ (m + n)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)
      exact (mul_le_mul_iff_right₀ hpn₀).mp hbound'
  exact hall (m + n) m n rfl

/-- Joint subexponential growth gives absolute convergence on the entire bidisc. -/
theorem summable_of_jointSubexponential {c : ℕ → ℕ → ℂ}
    (hc : JointSubexponential c) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun q : ℕ × ℕ => ‖c q.1 q.2 * x ^ q.1 * y ^ q.2‖) := by
  let r := max ‖x‖ ‖y‖
  have hr₀ : 0 ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr₁ : r < 1 := max_lt hx hy
  obtain ⟨R, hR, hRr⟩ : ∃ R : ℝ, 1 < R ∧ R * r < 1 := by
    by_cases hr : r = 0
    · exact ⟨2, by norm_num, by simp [hr]⟩
    have hri : 1 < r⁻¹ := (one_lt_inv₀ (lt_of_le_of_ne hr₀ (Ne.symm hr))).mpr hr₁
    obtain ⟨R, hR, hRi⟩ := exists_between hri
    exact ⟨R, hR, (lt_div_iff₀ (lt_of_le_of_ne hr₀ (Ne.symm hr))).mp
      (by simpa only [one_div] using hRi)⟩
  obtain ⟨K, hK⟩ := hc R hR
  have hK₀ : 0 ≤ K := le_trans (norm_nonneg (c 0 0)) (by simpa using hK 0 0)
  have hR₀ : 0 ≤ R := by linarith
  have hRx : R * ‖x‖ < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hR₀) hRr
  have hRy : R * ‖y‖ < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_max_right _ _) hR₀) hRr
  have hS := ((summable_geometric_of_lt_one (by positivity) hRx).mul_of_nonneg
    (summable_geometric_of_lt_one (by positivity) hRy)
    (fun _ => by positivity) (fun _ => by positivity)).mul_left K
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hS
  intro q
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ (K * R ^ (q.1 + q.2)) * ‖x‖ ^ q.1 * ‖y‖ ^ q.2 := by
      gcongr
      exact hK q.1 q.2
    _ = K * ((R * ‖x‖) ^ q.1 * (R * ‖y‖) ^ q.2) := by
      rw [pow_add, mul_pow, mul_pow]
      ring

/-- This implication supplies a joint norm bound, not just separate convergence. -/
theorem summable_of_radialRecurrence {c : ℕ → ℕ → ℂ} (hc : RadialRecurrence c)
    {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun q : ℕ × ℕ => ‖c q.1 q.2 * x ^ q.1 * y ^ q.2‖) :=
  summable_of_jointSubexponential (jointSubexponential_of_radialRecurrence hc) hx hy

end VOA.Huang.HuangODEThree
