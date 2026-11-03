import VOA.Huang.HuangODEThreeConvergence

/-!
# Joint coefficient bounds from SEPARATE regular-singular equations

Huang's convergence theorems for products of intertwining operators (genus zero:
math/0206206, Thms 1.6 and 2.5; genus one: math/0303049) produce, for each variable
separately, a monic differential equation whose coefficients are holomorphic in all
variables near the boundary point. They do not produce one equation in the radial
Euler operator `x∂x + y∂y`.

This file proves that two such separate equations already give the joint majorant
used throughout the library (`RadialRecurrence`, hence `JointSubexponential`).
The equation for a two-index array `c` in an operator `D` acting diagonally with
eigenvalue `e m n` on the `(m,n)` coefficient is
`D^s φ = Σ_{k<s} G_k(x,y) D^k φ`, with `G_k = Σ g k i j x^i y^j`.
At total degree `N` one uses an equation whose eigenvalue is at least `κN`; its
indicial factor is of size `N^s`, while the right-hand side is of size `N^(s-1)` times
strictly lower total degree terms. Two linearly independent Euler operators always
leave one such equation available (`dominance_of_linear`).

The VOA derivation of the separate equations is NOT part of this file.
-/

noncomputable section
namespace VOA.Huang.UniformConv
open VOA Filter VOA.Huang.HuangODEThree
open scoped BigOperators

/-- Coefficient form of a monic equation `D^s φ = Σ_{k<s} G_k D^k φ`, where `D` acts
diagonally with eigenvalue `e i j` on the `(i,j)` coefficient and `G_k = Σ g k i j x^i y^j`.
The constant terms `g k 0 0` are moved to the left (indicial polynomial). Resonances are
allowed: nothing is assumed about the vanishing of the left factor. -/
def DiagonalFuchsian (e : ℕ → ℕ → ℂ) (s : ℕ) (g : ℕ → ℕ → ℕ → ℂ)
    (c : ℕ → ℕ → ℂ) : Prop :=
  ∀ m n, (e m n ^ s - ∑ k ∈ Finset.range s, g k 0 0 * e m n ^ k) * c m n =
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      if i + j < m + n then
        ∑ k ∈ Finset.range s, g k (m - i) (n - j) * e i j ^ k * c i j else 0

/-- The strictly-lower-total-degree majorant sum appearing in `RadialRecurrence`. -/
def lowerSum (a : ℕ → ℝ) (c : ℕ → ℕ → ℂ) (m n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    if i + j < m + n then a (m + n - (i + j)) * ‖c i j‖ else 0

theorem lowerSum_mono {a a' : ℕ → ℝ} (h : ∀ l, a l ≤ a' l) (c : ℕ → ℕ → ℂ) (m n : ℕ) :
    lowerSum a c m n ≤ lowerSum a' c m n := by
  unfold lowerSum
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact mul_le_mul_of_nonneg_right (h _) (norm_nonneg _)
  · exact le_rfl

/-- Norm form of one equation: indicial factor times the coefficient is bounded by a
power `s-1` of the eigenvalue scale times the lower-degree sum. -/
theorem norm_indicial_mul_le {e : ℕ → ℕ → ℂ} {s : ℕ} {g : ℕ → ℕ → ℕ → ℂ}
    {c : ℕ → ℕ → ℂ} {b : ℕ → ℝ} {B : ℝ} (hB : 1 ≤ B) (hb₀ : ∀ l, 0 ≤ b l)
    (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ b (i + j))
    (he : ∀ i j, ‖e i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ)))
    (heq : DiagonalFuchsian e s g c) (m n : ℕ) :
    ‖e m n ^ s - ∑ k ∈ Finset.range s, g k 0 0 * e m n ^ k‖ * ‖c m n‖ ≤
      (B * (1 + ((m + n : ℕ) : ℝ))) ^ (s - 1) *
        lowerSum (fun l => (s : ℝ) * b l) c m n := by
  set T : ℝ := B * (1 + ((m + n : ℕ) : ℝ)) with hTdef
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℝ) ≤ 1 + ((m + n : ℕ) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (m + n); linarith
    nlinarith
  rw [← norm_mul, heq m n, lowerSum, Finset.mul_sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.mul_sum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
  have him : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
  have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  split_ifs with hij
  · have hdiff : m - i + (n - j) = m + n - (i + j) := by omega
    have heij : ‖e i j‖ ≤ T := by
      refine le_trans (he i j) ?_
      have hc : ((i + j : ℕ) : ℝ) ≤ ((m + n : ℕ) : ℝ) := by exact_mod_cast hij.le
      have hB0 : (0 : ℝ) ≤ B := by linarith
      rw [hTdef]; gcongr
    have hterm : ∀ k ∈ Finset.range s,
        ‖g k (m - i) (n - j) * e i j ^ k * c i j‖ ≤
          T ^ (s - 1) * (b (m + n - (i + j)) * ‖c i j‖) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hpow : ‖e i j‖ ^ k ≤ T ^ (s - 1) :=
        le_trans (pow_le_pow_left₀ (norm_nonneg _) heij k)
          (pow_le_pow_right₀ hT1 (by omega))
      have hg' := hg k hk' (m - i) (n - j)
      rw [hdiff] at hg'
      simp only [norm_mul, norm_pow]
      calc
        _ ≤ b (m + n - (i + j)) * T ^ (s - 1) * ‖c i j‖ := by
          gcongr
          exact hb₀ _
        _ = _ := by ring
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (by ring)
  · simp

/-- Lower bound for a monic indicial factor at a large eigenvalue. -/
theorem half_pow_le_norm_indicial {s : ℕ} (hs : 1 ≤ s) {g : ℕ → ℂ} {G : ℝ}
    (hg : ∀ k < s, ‖g k‖ ≤ G) {E : ℂ} (hE1 : 1 ≤ ‖E‖)
    (hEG : 2 * (s : ℝ) * G ≤ ‖E‖) :
    ‖E‖ ^ s / 2 ≤ ‖E ^ s - ∑ k ∈ Finset.range s, g k * E ^ k‖ := by
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hg 0 (by omega))
  have hsum : ‖∑ k ∈ Finset.range s, g k * E ^ k‖ ≤ (s : ℝ) * G * ‖E‖ ^ (s - 1) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range s, ‖g k * E ^ k‖ ≤ G * ‖E‖ ^ (s - 1) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hg k hk') (pow_le_pow_right₀ hE1 (by omega))
        (by positivity) hG0
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hpow : ‖E‖ ^ s = ‖E‖ * ‖E‖ ^ (s - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hE0 : 0 ≤ ‖E‖ ^ (s - 1) := by positivity
  have hkey : (s : ℝ) * G * ‖E‖ ^ (s - 1) ≤ ‖E‖ ^ s / 2 := by
    rw [hpow]
    have : (s : ℝ) * G ≤ ‖E‖ / 2 := by linarith
    nlinarith
  have htri : ‖E ^ s‖ - ‖∑ k ∈ Finset.range s, g k * E ^ k‖ ≤
      ‖E ^ s - ∑ k ∈ Finset.range s, g k * E ^ k‖ := norm_sub_norm_le _ _
  rw [norm_pow] at htri
  linarith

/-- One dominant equation at one index gives the radial majorant inequality there. -/
theorem step_of_dominant {e : ℕ → ℕ → ℂ} {s S : ℕ} {g : ℕ → ℕ → ℕ → ℂ}
    {c : ℕ → ℕ → ℂ} {b : ℕ → ℝ} {B ρ : ℝ} (hs : 1 ≤ s) (hsS : s ≤ S)
    (hb₀ : ∀ l, 0 ≤ b l) (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ b (i + j)) (hB : 1 ≤ B)
    (he : ∀ i j, ‖e i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ)))
    (heq : DiagonalFuchsian e s g c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {m n : ℕ}
    (hE1 : 1 ≤ ‖e m n‖) (hEG : 2 * (s : ℝ) * b 0 ≤ ‖e m n‖)
    (hEρ : ρ * (B * (1 + ((m + n : ℕ) : ℝ))) ≤ ‖e m n‖) :
    ρ ^ S * (B * (1 + ((m + n : ℕ) : ℝ))) / 2 * ‖c m n‖ ≤
      lowerSum (fun l => (S : ℝ) * b l) c m n := by
  set T : ℝ := B * (1 + ((m + n : ℕ) : ℝ)) with hTdef
  have hT1 : 1 ≤ T := by
    have h1 : (1 : ℝ) ≤ 1 + ((m + n : ℕ) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (m + n); linarith
    nlinarith
  have hT0 : 0 < T ^ (s - 1) := pow_pos (by linarith) _
  have hA := norm_indicial_mul_le hB hb₀ hg he heq m n
  rw [← hTdef] at hA
  have hL : lowerSum (fun l => (s : ℝ) * b l) c m n ≤
      lowerSum (fun l => (S : ℝ) * b l) c m n :=
    lowerSum_mono (fun l => mul_le_mul_of_nonneg_right (by exact_mod_cast hsS) (hb₀ l)) c m n
  have hP := half_pow_le_norm_indicial hs (g := fun k => g k 0 0) (G := b 0)
    (fun k hk => by simpa using hg k hk 0 0) hE1 hEG
  -- `ρ^S T T^(s-1) ≤ (ρT)^s ≤ ‖e‖^s`
  have hρT : ρ ^ S * T * T ^ (s - 1) ≤ ‖e m n‖ ^ s := by
    have h1 : ρ ^ S ≤ ρ ^ s := pow_le_pow_of_le_one hρ0 hρ1 hsS
    have h2 : T * T ^ (s - 1) = T ^ s := by rw [← pow_succ']; congr 1; omega
    calc ρ ^ S * T * T ^ (s - 1) = ρ ^ S * T ^ s := by rw [mul_assoc, h2]
      _ ≤ ρ ^ s * T ^ s := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (ρ * T) ^ s := (mul_pow ρ T s).symm
      _ ≤ ‖e m n‖ ^ s := pow_le_pow_left₀ (by positivity) hEρ s
  have hmain : T ^ (s - 1) * (ρ ^ S * T / 2 * ‖c m n‖) ≤
      T ^ (s - 1) * lowerSum (fun l => (S : ℝ) * b l) c m n := by
    calc T ^ (s - 1) * (ρ ^ S * T / 2 * ‖c m n‖)
        = (ρ ^ S * T * T ^ (s - 1)) / 2 * ‖c m n‖ := by ring
      _ ≤ ‖e m n‖ ^ s / 2 * ‖c m n‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ _ := hA
      _ ≤ _ := mul_le_mul_of_nonneg_left hL hT0.le
  exact le_of_mul_le_mul_left hmain hT0

/-- **Two separate equations give the radial majorant.** No radial equation is
assumed: at each large total degree one of the two equations is dominant. -/
theorem radialRecurrence_of_separate
    {c : ℕ → ℕ → ℂ} {e₁ e₂ : ℕ → ℕ → ℂ} {s₁ s₂ : ℕ} {g₁ g₂ : ℕ → ℕ → ℕ → ℂ}
    {b : ℕ → ℝ} {B κ D : ℝ}
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hb₀ : ∀ l, 0 ≤ b l) (hb : Subexponential b)
    (hg₁ : ∀ k < s₁, ∀ i j, ‖g₁ k i j‖ ≤ b (i + j))
    (hg₂ : ∀ k < s₂, ∀ i j, ‖g₂ k i j‖ ≤ b (i + j))
    (hB : 1 ≤ B) (he₁ : ∀ i j, ‖e₁ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ)))
    (he₂ : ∀ i j, ‖e₂ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ))) (hκ : 0 < κ)
    (hdom : ∀ m n, κ * ((m + n : ℕ) : ℝ) ≤ ‖e₁ m n‖ + D ∨
      κ * ((m + n : ℕ) : ℝ) ≤ ‖e₂ m n‖ + D)
    (heq₁ : DiagonalFuchsian e₁ s₁ g₁ c) (heq₂ : DiagonalFuchsian e₂ s₂ g₂ c) :
    RadialRecurrence c := by
  set S : ℕ := s₁ + s₂ with hSdef
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'κ : κ' ≤ κ := min_le_left _ _
  set ε : ℝ := κ' / 2 with hεdef
  have hε0 : 0 < ε := by positivity
  set ρ : ℝ := ε / (2 * B) with hρdef
  have hB0 : 0 < B := by linarith
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one (by positivity)]
    linarith
  have hb00 : 0 ≤ b 0 := hb₀ 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge
    (2 * |D| / κ' + 1 / ε + 2 * (S : ℝ) * b 0 / ε + 1)
  refine ⟨fun l => (S : ℝ) * b l, fun N => ρ ^ S * (B * (1 + (N : ℝ))) / 2, N₀,
    fun l => mul_nonneg (Nat.cast_nonneg _) (hb₀ l),
    hb.const_mul (Nat.cast_nonneg _), ?_, ?_⟩
  · have hc : 0 < ρ ^ S * B / 2 := by
      have : 0 < ρ := by positivity
      positivity
    have h1 : Tendsto (fun N : ℕ => 1 + (N : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    refine (h1.const_mul_atTop hc).congr fun N => ?_
    ring
  · intro m n hmn
    set N : ℝ := ((m + n : ℕ) : ℝ) with hNdef
    have hN : (N₀ : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hmn
    have hD1 : 2 * |D| / κ' ≤ N := by
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 2 * (S : ℝ) * b 0 / ε := by positivity
      linarith
    have hN1 : 1 ≤ N := by
      have : 0 ≤ 2 * |D| / κ' := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 2 * (S : ℝ) * b 0 / ε := by positivity
      linarith
    have hεN1 : 1 ≤ ε * N := by
      have h : 1 / ε ≤ N := by
        have : 0 ≤ 2 * |D| / κ' := by positivity
        have : 0 ≤ 2 * (S : ℝ) * b 0 / ε := by positivity
        linarith
      rw [div_le_iff₀ hε0] at h; linarith
    have hεNS : 2 * (S : ℝ) * b 0 ≤ ε * N := by
      have h : 2 * (S : ℝ) * b 0 / ε ≤ N := by
        have : 0 ≤ 2 * |D| / κ' := by positivity
        have : 0 ≤ 1 / ε := by positivity
        linarith
      rw [div_le_iff₀ hε0] at h; linarith
    have hDN : |D| ≤ ε * N := by
      rw [div_le_iff₀ hκ'0] at hD1
      rw [hεdef]; linarith
    have hρT : ρ * (B * (1 + N)) ≤ ε * N := by
      rw [hρdef]
      have : ε / (2 * B) * (B * (1 + N)) = ε * (1 + N) / 2 := by
        field_simp
      rw [this]
      nlinarith
    -- the dominant eigenvalue is at least `εN`
    have hdom' : ∀ E : ℝ, κ * N ≤ E + D → ε * N ≤ E := by
      intro E hE
      have h1 : κ' * N ≤ κ * N := mul_le_mul_of_nonneg_right hκ'κ (by linarith)
      have h2 : D ≤ |D| := le_abs_self D
      have h3 : κ' * N = 2 * (ε * N) := by rw [hεdef]; ring
      linarith
    have hsum : ∀ l : ℕ, l ≤ S → 2 * (l : ℝ) * b 0 ≤ 2 * (S : ℝ) * b 0 := by
      intro l hl
      have : (l : ℝ) ≤ S := by exact_mod_cast hl
      nlinarith
    rcases hdom m n with h | h
    · have hE := hdom' _ h
      exact step_of_dominant hs₁ (by omega) hb₀ hg₁ hB he₁ heq₁ hρ0 hρ1
        (by linarith) (le_trans (hsum s₁ (by omega)) (le_trans hεNS hE))
        (le_trans hρT hE)
    · have hE := hdom' _ h
      exact step_of_dominant hs₂ (by omega) hb₀ hg₂ hB he₂ heq₂ hρ0 hρ1
        (by linarith) (le_trans (hsum s₂ (by omega)) (le_trans hεNS hE))
        (le_trans hρT hE)

/-- **Joint subexponential growth from two separate regular-singular equations.** -/
theorem jointSubexponential_of_separate
    {c : ℕ → ℕ → ℂ} {e₁ e₂ : ℕ → ℕ → ℂ} {s₁ s₂ : ℕ} {g₁ g₂ : ℕ → ℕ → ℕ → ℂ}
    {b : ℕ → ℝ} {B κ D : ℝ}
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (hb₀ : ∀ l, 0 ≤ b l) (hb : Subexponential b)
    (hg₁ : ∀ k < s₁, ∀ i j, ‖g₁ k i j‖ ≤ b (i + j))
    (hg₂ : ∀ k < s₂, ∀ i j, ‖g₂ k i j‖ ≤ b (i + j))
    (hB : 1 ≤ B) (he₁ : ∀ i j, ‖e₁ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ)))
    (he₂ : ∀ i j, ‖e₂ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ))) (hκ : 0 < κ)
    (hdom : ∀ m n, κ * ((m + n : ℕ) : ℝ) ≤ ‖e₁ m n‖ + D ∨
      κ * ((m + n : ℕ) : ℝ) ≤ ‖e₂ m n‖ + D)
    (heq₁ : DiagonalFuchsian e₁ s₁ g₁ c) (heq₂ : DiagonalFuchsian e₂ s₂ g₂ c) :
    JointSubexponential c :=
  jointSubexponential_of_radialRecurrence
    (radialRecurrence_of_separate hs₁ hs₂ hb₀ hb hg₁ hg₂ hB he₁ he₂ hκ hdom heq₁ heq₂)

end VOA.Huang.UniformConv
