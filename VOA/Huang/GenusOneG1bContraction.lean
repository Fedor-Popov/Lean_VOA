import VOA.Huang.GenusOneG1bSeries

/-!
# The Laurent Euler-system majorant

Step 4 of the iterate-transport argument: the analogue of `GenusOneWard.geo2_of_euler_system`
for a system whose spatial coefficients are LAURENT (a bounded pole `X^{-M}` after
clearing) and only weighted-`ℓ¹` bounded at a radius `r ≤ 1`:

  `(λ + n) X^M Γ_f(n) = Σ_g Σ_{p ≤ n} X^{s_{fg}} K_{fgp} Γ_g(n − p)`.

If `‖K_{fgp}‖_r ≤ A a₁^p` and every row `Γ_f(n)` is bounded in the weighted sup norm
`sup_i ‖Γ_f(n)_i‖ r^i`, then for every `a > a₁` the rows are `O(a^n)` in that norm,
uniformly. Proof: at level `n` the system bounds the weighted sup of row `n` by
`(r^M ‖λ + n‖)⁻¹ · card · A · (X + C a^n Σ_p (a₁/a)^p)`; above a threshold this is a
contraction `X ↦ X/2 + C a^n / 2`, iterated from the crude row bound.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open scoped BigOperators

/-- Coefficient bound for a product, weighted-`ℓ¹` against weighted-sup. -/
theorem coeff_mul_le {r α β : ℝ} (hr : 0 ≤ r) {K G : PowerSeries ℂ} (hK : NormLe r K α)
    (hG : ∀ b, ‖PowerSeries.coeff b G‖ * r ^ b ≤ β) (j : ℕ) :
    ‖PowerSeries.coeff j (K * G)‖ * r ^ j ≤ α * β := by
  have hβ : 0 ≤ β := le_trans (by positivity) (hG 0)
  rw [PowerSeries.coeff_mul]
  calc ‖∑ kl ∈ Finset.antidiagonal j, PowerSeries.coeff kl.1 K * PowerSeries.coeff kl.2 G‖ *
        r ^ j
      ≤ (∑ kl ∈ Finset.antidiagonal j,
          ‖PowerSeries.coeff kl.1 K‖ * ‖PowerSeries.coeff kl.2 G‖) * r ^ j := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ = ∑ kl ∈ Finset.antidiagonal j, (‖PowerSeries.coeff kl.1 K‖ * r ^ kl.1) *
          (‖PowerSeries.coeff kl.2 G‖ * r ^ kl.2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        rw [Finset.mem_antidiagonal] at hkl
        rw [← hkl, pow_add]; ring
    _ ≤ ∑ kl ∈ Finset.antidiagonal j, (‖PowerSeries.coeff kl.1 K‖ * r ^ kl.1) * β :=
        Finset.sum_le_sum fun kl _ => mul_le_mul_of_nonneg_left (hG _) (by positivity)
    _ = (∑ k ∈ Finset.range (j + 1), ‖PowerSeries.coeff k K‖ * r ^ k) * β := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
    _ ≤ α * β := mul_le_mul_of_nonneg_right (hK _) hβ

section System
variable {κ : Type*} [Fintype κ] {lam : ℂ} {Γ : κ → ℕ → PowerSeries ℂ}
  {K : κ → κ → ℕ → PowerSeries ℂ} {s : κ → κ → ℕ} {M : ℕ}

/-- The level-`n` estimate read off from the coefficient of `X^{M+i}`. -/
theorem level_estimate {r A a₁ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hsys : ∀ f (n : ℕ), (lam + n) • (PowerSeries.X ^ M * Γ f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), PowerSeries.X ^ (s f g) * (K f g p * Γ g (n - p)))
    (hK : ∀ f g p, NormLe r (K f g p) (A * a₁ ^ p))
    (n : ℕ) (β : κ → ℕ → ℝ)
    (hβ : ∀ g m, m ≤ n → ∀ i, ‖PowerSeries.coeff i (Γ g m)‖ * r ^ i ≤ β g m)
    (f : κ) (i : ℕ) :
    r ^ M * (‖lam + n‖ * (‖PowerSeries.coeff i (Γ f n)‖ * r ^ i)) ≤
      ∑ g, ∑ p ∈ Finset.range (n + 1), A * a₁ ^ p * β g (n - p) := by
  have hc := congrArg (PowerSeries.coeff (M + i)) (hsys f n)
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
    show M + i - M = i by omega, map_sum] at hc
  simp only [map_sum, PowerSeries.coeff_X_pow_mul'] at hc
  have hterm : ∀ g, ∀ p ∈ Finset.range (n + 1),
      r ^ M * r ^ i * ‖(if s f g ≤ M + i then
        PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p)) else 0)‖ ≤
        A * a₁ ^ p * β g (n - p) := by
    intro g p hp
    rw [Finset.mem_range] at hp
    split_ifs with hs
    · have h1 := coeff_mul_le hr0.le (hK f g p) (hβ g (n - p) (by omega)) (M + i - s f g)
      have h2 : r ^ M * r ^ i ≤ r ^ (M + i - s f g) := by
        rw [← pow_add]
        exact pow_le_pow_of_le_one hr0.le hr1 (by omega)
      calc r ^ M * r ^ i * ‖PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p))‖
          ≤ r ^ (M + i - s f g) *
              ‖PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p))‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ A * a₁ ^ p * β g (n - p) := by rw [mul_comm]; exact h1
    · rw [norm_zero, mul_zero]
      have h1 := coeff_mul_le hr0.le (hK f g p) (hβ g (n - p) (by omega)) 0
      exact le_trans (by positivity) h1
  calc r ^ M * (‖lam + n‖ * (‖PowerSeries.coeff i (Γ f n)‖ * r ^ i))
      = r ^ M * r ^ i * ‖(lam + n) * PowerSeries.coeff i (Γ f n)‖ := by
        rw [norm_mul]; ring
    _ = r ^ M * r ^ i * ‖∑ g, ∑ p ∈ Finset.range (n + 1), (if s f g ≤ M + i then
          PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p)) else 0)‖ := by
        rw [smul_eq_mul] at hc; rw [hc]
    _ ≤ r ^ M * r ^ i * ∑ g, ∑ p ∈ Finset.range (n + 1), ‖(if s f g ≤ M + i then
          PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p)) else 0)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => norm_sum_le _ _)
    _ = ∑ g, ∑ p ∈ Finset.range (n + 1), r ^ M * r ^ i * ‖(if s f g ≤ M + i then
          PowerSeries.coeff (M + i - s f g) (K f g p * Γ g (n - p)) else 0)‖ := by
        rw [Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun p hp => hterm g p hp

/-- **Laurent Euler-system majorant.** -/
theorem euler_laurent_bound {r A a₁ a : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ha₁ : 0 ≤ a₁)
    (ha : a₁ < a)
    (hsys : ∀ f (n : ℕ), (lam + n) • (PowerSeries.X ^ M * Γ f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), PowerSeries.X ^ (s f g) * (K f g p * Γ g (n - p)))
    (hK : ∀ f g p, NormLe r (K f g p) (A * a₁ ^ p))
    (hrow : ∀ f n, ∃ B : ℝ, ∀ i, ‖PowerSeries.coeff i (Γ f n)‖ * r ^ i ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f n i, ‖PowerSeries.coeff i (Γ f n)‖ * r ^ i ≤ C * a ^ n := by
  classical
  have ha0 : 0 < a := lt_of_le_of_lt ha₁ ha
  by_cases hκ : IsEmpty κ
  · exact ⟨0, le_rfl, fun f => (hκ.false f).elim⟩
  have hA : 0 ≤ A := by
    rw [not_isEmpty_iff] at hκ
    obtain ⟨f⟩ := hκ
    have := (hK f f 0).nonneg
    simpa using this
  set ρ := a₁ / a with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg ha₁ ha0.le
  have hρ1 : ρ < 1 := (div_lt_one ha0).2 ha
  set G := (1 - ρ)⁻¹ with hG
  have hG0 : 0 ≤ G := inv_nonneg.mpr (by linarith)
  set Q := (Fintype.card κ : ℝ) * A with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hrM : 0 < r ^ M := pow_pos hr0 M
  -- threshold
  set N₀ : ℕ := ⌈(2 * Q * (1 + G) + 1) / r ^ M + ‖lam‖⌉₊ with hN₀
  have hthr : ∀ n : ℕ, N₀ ≤ n → 2 * Q * (1 + G) + 1 ≤ r ^ M * ‖lam + n‖ := by
    intro n hn
    have h1 : (2 * Q * (1 + G) + 1) / r ^ M + ‖lam‖ ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : (n : ℝ) - ‖lam‖ ≤ ‖lam + n‖ := by
      have := norm_sub_norm_le ((n : ℂ)) (-lam)
      rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at this
      exact this
    have h3 : (2 * Q * (1 + G) + 1) / r ^ M ≤ ‖lam + n‖ := by linarith
    rw [div_le_iff₀ hrM] at h3
    linarith
  -- low-level constant
  choose B hB using hrow
  set C := ∑ p ∈ (Finset.univ : Finset κ) ×ˢ Finset.range N₀, max (B p.1 p.2) 0 / a ^ p.2
    with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun p _ => div_nonneg (le_max_right _ _) (by positivity)
  have hlowC : ∀ n < N₀, ∀ f i, ‖PowerSeries.coeff i (Γ f n)‖ * r ^ i ≤ C * a ^ n := by
    intro n hn f i
    have hle : max (B f n) 0 / a ^ n ≤ C :=
      Finset.single_le_sum (f := fun p : κ × ℕ => max (B p.1 p.2) 0 / a ^ p.2) (a := (f, n))
        (fun p _ => div_nonneg (le_max_right _ _) (by positivity))
        (Finset.mem_product.mpr ⟨Finset.mem_univ f, Finset.mem_range.mpr hn⟩)
    have han : 0 < a ^ n := pow_pos ha0 n
    calc ‖PowerSeries.coeff i (Γ f n)‖ * r ^ i ≤ B f n := hB f n i
      _ ≤ max (B f n) 0 := le_max_left _ _
      _ = max (B f n) 0 / a ^ n * a ^ n := by field_simp
      _ ≤ C * a ^ n := mul_le_mul_of_nonneg_right hle han.le
  refine ⟨C, hC0, ?_⟩
  have hall : ∀ n : ℕ, ∀ f i, ‖PowerSeries.coeff i (Γ f n)‖ * r ^ i ≤ C * a ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < N₀
      · exact hlowC n hn
      push Not at hn
      set B' := ∑ g : κ, max (B g n) 0 with hB'
      have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun g _ => le_max_right _ _
      have hcrude : ∀ g i, ‖PowerSeries.coeff i (Γ g n)‖ * r ^ i ≤ C * a ^ n + B' := by
        intro g i
        have : B g n ≤ B' := (le_max_left _ _).trans
          (Finset.single_le_sum (f := fun g : κ => max (B g n) 0)
            (fun g _ => le_max_right _ _) (Finset.mem_univ g))
        have := hB g n i
        have : 0 ≤ C * a ^ n := by positivity
        linarith
      -- the contraction step
      have hstep : ∀ X : ℝ, 0 ≤ X →
          (∀ g i, ‖PowerSeries.coeff i (Γ g n)‖ * r ^ i ≤ X) →
          ∀ g i, ‖PowerSeries.coeff i (Γ g n)‖ * r ^ i ≤ X / 2 + C * a ^ n / 2 := by
        intro X hX0 hX g i
        set β : κ → ℕ → ℝ := fun g m => if m = n then X else C * a ^ m with hβdef
        have hβ : ∀ g m, m ≤ n → ∀ i, ‖PowerSeries.coeff i (Γ g m)‖ * r ^ i ≤ β g m := by
          intro g m hm i
          simp only [hβdef]
          split_ifs with h
          · subst h; exact hX g i
          · exact ih m (by omega) g i
        have hest := level_estimate hr0 hr1 hsys hK n β hβ g i
        -- bound the right side
        have hsum : ∀ g' : κ, ∑ p ∈ Finset.range (n + 1), A * a₁ ^ p * β g' (n - p) ≤
            A * (X + C * a ^ n * G) := by
          intro g'
          rw [Finset.sum_range_succ']
          simp only [hβdef, Nat.sub_zero, if_true, pow_zero, mul_one]
          have hgeo : ∑ p ∈ Finset.range n, A * a₁ ^ (p + 1) *
              (if n - (p + 1) = n then X else C * a ^ (n - (p + 1))) ≤ A * (C * a ^ n * G) := by
            have hle : ∀ p ∈ Finset.range n, A * a₁ ^ (p + 1) *
                (if n - (p + 1) = n then X else C * a ^ (n - (p + 1))) =
                A * (C * a ^ n) * ρ ^ (p + 1) := by
              intro p hp
              rw [Finset.mem_range] at hp
              rw [if_neg (by omega)]
              have han : a ^ n = a ^ (n - (p + 1)) * a ^ (p + 1) := by
                rw [← pow_add]; congr 1; omega
              rw [han, hρ, div_pow]
              have : a ^ (p + 1) ≠ 0 := (pow_pos ha0 _).ne'
              field_simp
            rw [Finset.sum_congr rfl hle, ← Finset.mul_sum]
            have hgs : ∑ p ∈ Finset.range n, ρ ^ (p + 1) ≤ G := by
              have := (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum (Finset.range n)
                (fun i _ => pow_nonneg hρ0 i)
              rw [tsum_geometric_of_lt_one hρ0 hρ1] at this
              calc ∑ p ∈ Finset.range n, ρ ^ (p + 1) = ρ * ∑ p ∈ Finset.range n, ρ ^ p := by
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
                _ ≤ 1 * G := mul_le_mul hρ1.le this (Finset.sum_nonneg fun p _ => by positivity)
                    zero_le_one
                _ = G := one_mul _
            calc A * (C * a ^ n) * ∑ p ∈ Finset.range n, ρ ^ (p + 1)
                ≤ A * (C * a ^ n) * G := mul_le_mul_of_nonneg_left hgs (by positivity)
              _ = A * (C * a ^ n * G) := by ring
          linarith
        have hrhs : ∑ g', ∑ p ∈ Finset.range (n + 1), A * a₁ ^ p * β g' (n - p) ≤
            Q * (X + C * a ^ n * G) := by
          calc _ ≤ ∑ _g' : κ, A * (X + C * a ^ n * G) := Finset.sum_le_sum fun g' _ => hsum g'
            _ = Q * (X + C * a ^ n * G) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hQ]; ring
        have hth := hthr n hn
        set y := ‖PowerSeries.coeff i (Γ g n)‖ * r ^ i with hy
        have hy0 : 0 ≤ y := by positivity
        have h1 : y * (2 * Q * (1 + G) + 1) ≤ Q * (X + C * a ^ n * G) := by
          calc y * (2 * Q * (1 + G) + 1) ≤ y * (r ^ M * ‖lam + n‖) :=
                mul_le_mul_of_nonneg_left hth hy0
            _ = r ^ M * (‖lam + n‖ * y) := by ring
            _ ≤ _ := hest.trans hrhs
        have hCa : 0 ≤ C * a ^ n := by positivity
        -- conclude y ≤ X/2 + C a^n/2
        by_contra hcon
        push Not at hcon
        have h2 : Q * (X + C * a ^ n * G) ≤ (X / 2 + C * a ^ n / 2) * (2 * Q * (1 + G)) := by
          nlinarith [mul_nonneg hQ0 hX0, mul_nonneg hQ0 hCa, mul_nonneg (mul_nonneg hQ0 hX0) hG0,
            mul_nonneg (mul_nonneg hQ0 hCa) hG0]
        have h3 : (X / 2 + C * a ^ n / 2) * (2 * Q * (1 + G) + 1) <
            y * (2 * Q * (1 + G) + 1) :=
          mul_lt_mul_of_pos_right hcon (by positivity)
        nlinarith
      have hiter : ∀ j : ℕ, ∀ g i, ‖PowerSeries.coeff i (Γ g n)‖ * r ^ i ≤
          C * a ^ n + B' / 2 ^ j := by
        intro j
        induction j with
        | zero => simpa using hcrude
        | succ j ihj =>
          intro g i
          have h := hstep (C * a ^ n + B' / 2 ^ j) (by positivity) ihj g i
          refine h.trans (le_of_eq ?_)
          rw [pow_succ]; field_simp; ring
      intro f i
      have hlim : Filter.Tendsto (fun j : ℕ => C * a ^ n + B' / 2 ^ j) Filter.atTop
          (nhds (C * a ^ n + 0)) := by
        refine tendsto_const_nhds.add ?_
        have : Filter.Tendsto (fun j : ℕ => B' * ((1 : ℝ) / 2) ^ j) Filter.atTop
            (nhds (B' * 0)) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul B'
        rw [mul_zero] at this
        refine this.congr fun j => ?_
        rw [one_div, inv_pow, div_eq_mul_inv]
      rw [add_zero] at hlim
      exact ge_of_tendsto' hlim fun j => hiter j f i
  exact fun f n i => hall n f i

end System

end VOA.Huang.GenusOneG1b
