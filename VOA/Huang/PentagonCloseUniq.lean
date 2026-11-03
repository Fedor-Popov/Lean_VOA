import VOA.Huang.AssocConverseAnalytic

/-! # Uniqueness of generalized power series on a real interval

A complex-indexed series `∑' w, b w * ρ^(w - c₀)` whose support lies in finitely
many progressions `h + ℕ` (possibly overlapping), absolutely convergent for
`0 < ρ < R`, vanishes on `(0, R)` only if every coefficient vanishes.
The proof reduces to the library's log-series uniqueness
`log_coeff_zero_of_real_interval`, attributing each exponent to one chosen
progression, so that overlapping progressions are never counted twice.
-/

noncomputable section
namespace VOA.Huang.PentagonClose
open VOA VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff VOA.Huang.AssocConverse
open scoped BigOperators
open Filter Topology

/-- The normalized core: convergence on `(0, 1]`, vanishing on `(0, 1)`. -/
theorem gps_coeff_zero_core (S : Finset ℂ) (c₀ : ℂ) (b : ℂ → ℂ)
    (hsupp : ∀ w, b w ≠ 0 → ∃ h ∈ S, ∃ n : ℕ, w = h + n)
    (hsum : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → Summable (fun w => b w * (ρ : ℂ) ^ (w - c₀)))
    (hz : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∑' w, b w * (ρ : ℂ) ^ (w - c₀) = 0) :
    ∀ w, b w = 0 := by
  classical
  -- the chosen progression owning each exponent
  let own : ℂ → ℂ := fun w => if h : ∃ h ∈ S, ∃ n : ℕ, w = h + n then h.choose else 0
  have own_spec (w : ℂ) (h : ∃ h ∈ S, ∃ n : ℕ, w = h + n) :
      own w ∈ S ∧ ∃ n : ℕ, w = own w + n := by
    simp only [own, dif_pos h]
    exact h.choose_spec
  let ι := {x // x ∈ S}
  let lam : ι → ℂ := fun j => (j : ℂ) - c₀
  let a : ι → ℕ → ℂ := fun j n => if own ((j : ℂ) + n) = j then b ((j : ℂ) + n) else 0
  let p : ι → ℕ → Polynomial ℂ := fun j n => Polynomial.C (a j n)
  -- boundedness from convergence at `ρ = 1`
  have hb1 : Summable (fun w => ‖b w‖) := by
    have := (hsum 1 one_pos le_rfl).norm
    refine this.congr fun w => ?_
    simp [Complex.one_cpow]
  set M : ℝ := ∑' w, ‖b w‖
  have hbM (w : ℂ) : ‖b w‖ ≤ M := hb1.le_tsum w (fun _ _ => norm_nonneg _)
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  have hp : ∀ j, LogGood (p j) := by
    intro j
    refine ⟨⟨0, fun n => by simp [p]⟩, fun k => ?_⟩
    intro r hr
    refine ⟨M, fun n => ?_⟩
    have h1 : ‖(p j n).coeff k‖ ≤ M := by
      simp only [p, Polynomial.coeff_C]
      split_ifs
      · simp only [a]; split_ifs
        · exact hbM _
        · simpa using hM
      · simpa using hM
    calc ‖(p j n).coeff k‖ ≤ M := h1
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * r ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ hr.le) hM
  -- the vanishing hypothesis in log-series form
  have hz' : ∀ t : ℝ, -1 < t → t < 0 → ∑ j, logFun (lam j) (p j) t = 0 := by
    intro t _ ht0
    set ρ : ℝ := Real.exp t with hρ
    have hρ0 : 0 < ρ := Real.exp_pos t
    have hρ1 : ρ < 1 := Real.exp_lt_one_iff.mpr ht0
    have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
    have hcp (z : ℂ) : (ρ : ℂ) ^ z = Complex.exp (z * t) := by
      rw [Complex.cpow_def_of_ne_zero hρne, ← Complex.ofReal_log hρ0.le, hρ, Real.log_exp,
        mul_comm]
    let f : ℂ → ℂ := fun w => b w * (ρ : ℂ) ^ (w - c₀)
    have hf : Summable f := hsum ρ hρ0 hρ1.le
    let g : ι → ℂ → ℂ := fun j w => if own w = j then f w else 0
    have hg (j : ι) : Summable (g j) := by
      refine Summable.of_norm_bounded hf.norm fun w => ?_
      simp only [g]; split_ifs
      · exact le_rfl
      · simp
    have hlog (j : ι) : logFun (lam j) (p j) t = ∑' w, g j w := by
      have hinj : Function.Injective (fun n : ℕ => (j : ℂ) + n) := by
        intro m n hmn; exact_mod_cast add_left_cancel hmn
      have hsub : Function.support (g j) ⊆ Set.range (fun n : ℕ => (j : ℂ) + n) := by
        intro w hw
        simp only [Function.mem_support, g] at hw
        split_ifs at hw with hown
        · have hbw : b w ≠ 0 := fun h0 => hw (by simp [f, h0])
          obtain ⟨_, n, hn⟩ := own_spec w (hsupp w hbw)
          exact ⟨n, by rw [hn, hown]⟩
        · exact absurd rfl hw
      rw [← hinj.tsum_eq hsub, logFun]
      apply tsum_congr
      intro n
      simp only [p, a, g, f, Polynomial.eval_C]
      split_ifs
      · rw [hcp, mul_comm]; congr 2; simp only [lam]; ring
      · simp
    have hsumg (w : ℂ) : ∑ j, g j w = f w := by
      by_cases hbw : b w = 0
      · simp [g, f, hbw]
      · obtain ⟨hS, _⟩ := own_spec w (hsupp w hbw)
        rw [Finset.sum_eq_single (⟨own w, hS⟩ : ι)]
        · simp [g]
        · intro j _ hj
          simp only [g]
          rw [if_neg]
          intro he; exact hj (Subtype.ext he.symm)
        · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hlog]
    rw [← Summable.tsum_finsetSum (fun j _ => hg j)]
    simp_rw [hsumg]
    exact hz ρ hρ0 hρ1
  have he := log_coeff_zero_of_real_interval lam p hp (a := -1) (by norm_num) hz'
  intro w
  by_contra hbw
  obtain ⟨hS, n₀, hn₀⟩ := own_spec w (hsupp w hbw)
  have hh := he (w - c₀) 0
  rw [Finset.sum_eq_single (⟨own w, hS⟩ : ι)] at hh
  · have hw' : w - c₀ = lam ⟨own w, hS⟩ + n₀ := by
      simp only [lam]; linear_combination hn₀
    rw [hw'] at hh
    simp only [p] at hh
    rw [exCoeff_C] at hh
    simp only [a, if_true] at hh
    rw [← hn₀, if_pos rfl] at hh
    exact hbw hh
  · intro j _ hj
    by_cases hex : ∃ n : ℕ, lam j + n = w - c₀
    · obtain ⟨n, hn⟩ := hex
      have hjn : (j : ℂ) + n = w := by simp only [lam] at hn; linear_combination hn
      rw [← hn]
      simp only [p]
      rw [exCoeff_C]
      simp only [a, if_true, hjn]
      rw [if_neg]
      intro he'; exact hj (Subtype.ext he'.symm)
    · exact exCoeff_of_forall_ne (fun n hn => hex ⟨n, hn⟩) _ _
  · intro h; exact absurd (Finset.mem_univ _) h


/-- **Uniqueness of generalized power series** on a real interval `(0, R)`:
finitely many (possibly overlapping) exponent progressions, complex exponents. -/
theorem gps_coeff_zero (S : Finset ℂ) (c₀ : ℂ) (a : ℂ → ℂ)
    (hsupp : ∀ w, a w ≠ 0 → ∃ h ∈ S, ∃ n : ℕ, w = h + n) {R : ℝ} (hR : 0 < R)
    (hsum : ∀ r : ℝ, 0 < r → r < R → Summable (fun w => a w * (r : ℂ) ^ (w - c₀)))
    (hz : ∀ r : ℝ, 0 < r → r < R → ∑' w, a w * (r : ℂ) ^ (w - c₀) = 0) :
    ∀ w, a w = 0 := by
  have hR2 : 0 < R / 2 := by linarith
  have hne : ((R / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR2.ne'
  let b : ℂ → ℂ := fun w => a w * ((R / 2 : ℝ) : ℂ) ^ (w - c₀)
  have hb (ρ : ℝ) (hρ : 0 ≤ ρ) (w : ℂ) :
      b w * (ρ : ℂ) ^ (w - c₀) = a w * (((R / 2 * ρ : ℝ)) : ℂ) ^ (w - c₀) := by
    simp only [b]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hR2.le hρ, mul_assoc]
  have hr (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : 0 < R / 2 * ρ ∧ R / 2 * ρ < R :=
    ⟨mul_pos hR2 h0, by nlinarith⟩
  have hcore := gps_coeff_zero_core S c₀ b
    (fun w hw => hsupp w (fun h0 => hw (by simp [b, h0])))
    (fun ρ h0 h1 => by
      simp_rw [hb ρ h0.le]
      exact hsum _ (hr ρ h0 h1).1 (hr ρ h0 h1).2)
    (fun ρ h0 h1 => by
      simp_rw [hb ρ h0.le]
      exact hz _ (hr ρ h0 h1.le).1 (hr ρ h0 h1.le).2)
  intro w
  have := hcore w
  simp only [b, mul_eq_zero] at this
  rcases this with h | h
  · exact h
  · exact absurd ((Complex.cpow_eq_zero_iff _ _).mp h).1 hne

end VOA.Huang.PentagonClose
