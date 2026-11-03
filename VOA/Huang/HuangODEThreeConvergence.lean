import VOA.Huang.HuangODEThreeFuchsian

/-! # Local radial solutions and finite spectral covers

The reindexing theorem permits overlapping progressions: each summand is
bounded by the sum of the indicators of the finitely many covering ranges.
No disjointness of lowest-weight cosets is assumed.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open scoped BigOperators

/-- A local rescaling of a formal radial Fuchsian solution. This is a sufficient
analytic criterion, not a claimed automatic property of arbitrary VOA charts. -/
def LocalRadialSolution (t : ℕ → ℕ → ℂ) : Prop :=
  ∃ (c : ℕ → ℕ → ℂ) (x y lam : ℂ) (s : ℕ)
    (g : ℕ → ℕ → ℕ → ℂ) (b : ℕ → ℝ),
    ‖x‖ < 1 ∧ ‖y‖ < 1 ∧ 1 ≤ s ∧ (∀ l, 0 ≤ b l) ∧ VOA.Subexponential b ∧
    (∀ k < s, ∀ i j, ‖g k i j‖ ≤ b (i + j)) ∧ RadialFuchsian lam s g c ∧
    ∀ m n, t m n = c m n * x ^ m * y ^ n

/-- Local radial differential equations give absolute double convergence. -/
theorem LocalRadialSolution.summable_norm {t : ℕ → ℕ → ℂ}
    (ht : LocalRadialSolution t) : Summable (fun q : ℕ × ℕ => ‖t q.1 q.2‖) := by
  obtain ⟨c, x, y, lam, s, g, b, hx, hy, hs, hb₀, hb, hg, heq, ht⟩ := ht
  simpa only [ht] using summable_of_radialFuchsian hs hb₀ hb hg heq hx hy

/-- Uniform coefficient growth after a local rescaling of both variables.
Unlike separate convergence, this has one bound for both grading indices. -/
def LocalJointGrowth (t : ℕ → ℕ → ℂ) : Prop :=
  ∃ (c : ℕ → ℕ → ℂ) (x y : ℂ), ‖x‖ < 1 ∧ ‖y‖ < 1 ∧
    JointSubexponential c ∧ ∀ m n, t m n = c m n * x ^ m * y ^ n

theorem LocalJointGrowth.summable_norm {t : ℕ → ℕ → ℂ}
    (ht : LocalJointGrowth t) : Summable (fun q : ℕ × ℕ => ‖t q.1 q.2‖) := by
  obtain ⟨c, x, y, hx, hy, hc, ht⟩ := ht
  simpa only [ht] using summable_of_jointSubexponential hc hx hy

/-- An explicit sufficient differential-equation criterion for the joint bound. -/
theorem LocalRadialSolution.localJointGrowth {t : ℕ → ℕ → ℂ}
    (ht : LocalRadialSolution t) : LocalJointGrowth t := by
  obtain ⟨c, x, y, lam, s, g, b, hx, hy, hs, hb₀, hb, hg, heq, ht⟩ := ht
  exact ⟨c, x, y, hx, hy,
    jointSubexponential_of_radialRecurrence (radialRecurrence_of_fuchsian hs hb₀ hb hg heq), ht⟩

/-- Finite covers by injective parametrizations preserve absolute summability,
even when the covering ranges overlap. -/
theorem summable_norm_of_finite_cover {α β ι : Type*} (f : α → ℂ)
    (S : Finset ι) (g : ι → β → α)
    (hinj : ∀ i ∈ S, Function.Injective (g i))
    (hcover : ∀ a, f a ≠ 0 → ∃ i ∈ S, a ∈ Set.range (g i))
    (hs : ∀ i ∈ S, Summable (fun b => ‖f (g i b)‖)) : Summable (fun a => ‖f a‖) := by
  classical
  let H : ι → α → ℝ := fun i => (Set.range (g i)).indicator (fun a => ‖f a‖)
  have hH : ∀ i ∈ S, Summable (H i) := by
    intro i hi
    apply (hinj i hi).summable_iff (fun a ha => Set.indicator_of_notMem ha _ ) |>.mp
    simpa [H, Function.comp_def] using hs i hi
  have hnonneg : ∀ i a, 0 ≤ H i a := fun i a => Set.indicator_nonneg (fun _ _ => norm_nonneg _) a
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (summable_sum hH)
  intro a
  by_cases ha : f a = 0
  · simp only [ha, norm_zero]
    exact Finset.sum_nonneg (fun i _ => hnonneg i a)
  · obtain ⟨i, hi, hai⟩ := hcover a ha
    calc
      ‖f a‖ = H i a := (Set.indicator_of_mem hai (fun a => ‖f a‖)).symm
      _ ≤ ∑ i ∈ S, H i a := Finset.single_le_sum (fun j _ => hnonneg j a) hi

end VOA.Huang.HuangODEThree
