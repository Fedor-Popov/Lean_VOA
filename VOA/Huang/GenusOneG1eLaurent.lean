import VOA.Huang.GenusOneG1eRow

/-!
# The bracket-coordinate (Laurent) expansion of a genus-one iterate — no mass bound

Step (5e) of the proof of (G1).

For an iterate channel `e^{αu} Tr_N Y₃(Y₄(x, e^u − 1) y, 1) q^{L₀−c/24}` (ANY irreducible inner
module `Q`, ANY outer intertwiner `Y₃`) and any `κ'` with `κ' − α − β + N₀ = D ∈ ℕ`:

`e^{αu} iterF = Σ_s e^{c' log u} u^s · traceFunction Y₃ h_N (bracketModes Y₄ n_s x y) τ`,
`c' = h_Q − κ' − N₀`, `n_s = κ' − 1 − h_Q − (s − N₀)`,

absolutely convergent for `‖u‖ < δ(τ)`, `Re(e^u − 1) > 0`. The coefficient vectors are the explicit
formal bracket modes (`IntCoord.bracketModes`); they depend only on `(Y₄, x, y)`.

**Why no square-trace-mass bound is needed.** The plane rows `T_k(τ)` (traces of the plane modes
`Y₄_{(α+β−1−h_Q−k)} x y`) are grouped by the power of `u` FIRST: the `u^s` coefficient is a FINITE
combination of `T_k`, `k ≤ s`, which is the trace of the single vector `bracketModes Y₄ n_s x y`
(linearity of the trace). Absolute convergence of the regrouping only needs the geometric growth of
`‖T_k‖` (from the proved sewing radius) against the majorant `psMass(E^{c'}) (ρ · psMass E ρ)^k`
of the scalar factors (`GenusOneG1eSeries`). The square-weight decomposition of the plane
coefficients (an alternative route, which needs `Σ_n ‖Z(P_n a_k)‖ ≤ C B^k`) is never formed;
`L[0]`-homogeneity of `bracketModes` is the separate ALGEBRAIC statement
`IntCoord.NormalizedIntertwinerSubstitution` (via `transportedModes_weight`).

* `cpow_mul_split` — `(uE)^{c'+m} = e^{c' log u} E^{c'} u^m E^m` (`Re u, Re E > 0`);
* `pair_laurent` — the expansion for one pair of homogeneous vectors.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang Complex
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (exponentialUnit exponentialUnitPower bracketCoeff bracketModes
  bracketModes_eq_sum_range)
open VOA.Huang.GenusOneG1c (iterF)
open VOA.Huang.GenusTwoPoint (IterateSewingSummable)
open scoped BigOperators

universe u

/-- `(uE)^{c+m} = e^{c log u} E^c u^m E^m` for `u, E` in the right half-plane. -/
theorem cpow_mul_split {u E : ℂ} (hu : 0 < u.re) (hE : 0 < E.re) (c : ℂ) (m : ℕ) :
    (u * E) ^ (c + (m : ℂ)) = exp (c * log u) * E ^ c * (u ^ m * E ^ m) := by
  have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; exact lt_irrefl _ hu
  have hE0 : E ≠ 0 := fun h => by rw [h, Complex.zero_re] at hE; exact lt_irrefl _ hE
  have huE : u * E ≠ 0 := mul_ne_zero hu0 hE0
  have ha1 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have ha2 := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hE))
  have hlog : log (u * E) = log u + log E := by
    rw [Complex.log_mul_eq_add_log_iff hu0 hE0]
    constructor <;> linarith [Real.pi_pos]
  rw [Complex.cpow_add _ _ huE, Complex.cpow_natCast, mul_pow,
    Complex.cpow_def_of_ne_zero huE, Complex.cpow_def_of_ne_zero hE0, hlog, add_mul, exp_add]
  ring

theorem re_pos_of_exp_sub_one {w : ℂ} (h : 0 < (exp w - 1).re) : 0 < w.re := by
  have h1 : 1 < (exp w).re := by rw [Complex.sub_re, Complex.one_re] at h; linarith
  have h2 : (exp w).re ≤ ‖exp w‖ := Complex.re_le_norm _
  rw [Complex.norm_exp] at h2
  have h3 : 1 < Real.exp w.re := lt_of_lt_of_le h1 h2
  by_contra hn
  push Not at hn
  have := Real.exp_le_one_iff.mpr hn
  linarith

/-- `Re E(u) > 0` for `‖u‖ ≤ 1/3`. -/
theorem re_unit_pos {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    0 < (psEval exponentialUnit u).re := by
  have h := (norm_psEval_unit_sub_one_le hρ (by linarith) hu).trans (ratio_le_half hρ hρ3)
  have h2 := Complex.abs_re_le_norm (psEval exponentialUnit u - 1)
  rw [Complex.sub_re, Complex.one_re] at h2
  have := (abs_le.mp (h2.trans h)).1
  linarith

/-- `‖E(u)‖ ≤ psMass E ρ`. -/
theorem norm_unit_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    ‖psEval exponentialUnit u‖ ≤ psMass exponentialUnit ρ :=
  (norm_tsum_le_tsum_norm (summable_norm_of_conv (conv_unit hρ hρ1).1 hu)).trans
    (tsum_norm_le_psMass (conv_unit hρ hρ1).1 hu)

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The plane row coefficient `T_k(τ)`. -/
def rowT (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (x : P₁.carrier) (y : P₂.carrier)
    (α β : ℂ) (τ : UpperHalfPlane) (k : ℕ) : ℂ :=
  traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ

/-- Geometric growth of the rows, from the proved sewing radius. -/
theorem rowT_geometric (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {y : P₂.carrier}
    {α β : ℂ} (hx : x ∈ P₁.isMod.weight α) (hy : y ∈ P₂.isMod.weight β) (τ : UpperHalfPlane) :
    ∃ t δs : ℝ, 0 < t ∧ 0 < δs ∧ t < δs ∧
      Summable (fun k : ℕ => ‖rowT Y₃ Y₄ x y α β τ k‖ * t ^ k) ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ < δs → IterateSewingSummable Y₃ Y₄ x y α β z 1 τ := by
  obtain ⟨δs, hδs, -, hs⟩ := GenusOneG1b.exists_iterateSewingRadius_holds hV i₁ i₂ iN iQ
    Y₃ Y₄ hx hy τ
  have hsz : ∀ z : ℂ, z ≠ 0 → ‖z‖ < δs → IterateSewingSummable Y₃ Y₄ x y α β z 1 τ :=
    fun z hz hn => hs z 1 hz one_ne_zero (by simpa using hn)
  set t : ℝ := δs / 2 with ht
  have ht0 : 0 < t := by positivity
  have htl : t < δs := by linarith
  refine ⟨t, δs, ht0, hδs, htl, ?_, hsz⟩
  have htn : ‖(t : ℂ)‖ < δs := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]; exact htl
  have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hrows := (iterF_hasSum_rows Y₃ Y₄ hx hy τ (t : ℂ) (hsz _ ht0' htn)).2
  have hc : 0 < t ^ ((Q.h - α - β).re) := Real.rpow_pos_of_pos ht0 _
  refine (hrows.div_const (t ^ ((Q.h - α - β).re))).congr fun k => ?_
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  have hre : ((Q.h + k) - α - β).re = (Q.h - α - β).re + k := by simp; ring
  rw [hre, Real.rpow_add ht0, Real.rpow_natCast]
  unfold rowT
  field_simp

/-! ## The scalar regrouping -/

/-- The double series indexed by `(k, r)` (plane row `k`, scalar Taylor index `r`). -/
def fTerm (α c' : ℂ) (D : ℕ) (T : ℕ → ℂ) (u : ℂ) (p : ℕ × ℕ) : ℂ :=
  PowerSeries.coeff p.2 (bracketFactor α c' (p.1 + D)) * u ^ (p.1 + p.2 + D) * T p.1

/-- The same series indexed by `(s, r)` (total power `s` of `u`). -/
def gTerm (α c' : ℂ) (D : ℕ) (T : ℕ → ℂ) (u : ℂ) (p : ℕ × ℕ) : ℂ :=
  if D + p.2 ≤ p.1 then
    PowerSeries.coeff p.2 (bracketFactor α c' (p.1 - p.2)) * u ^ p.1 * T (p.1 - p.2 - D)
  else 0

/-- The reindexing map `(k, r) ↦ (k + r + D, r)`. -/
def reidx (D : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + p.2 + D, p.2)

theorem reidx_injective (D : ℕ) : Function.Injective (reidx D) := by
  intro p q h
  simp only [reidx, Prod.mk.injEq] at h
  ext <;> omega

theorem gTerm_reidx (α c' : ℂ) (D : ℕ) (T : ℕ → ℂ) (u : ℂ) (p : ℕ × ℕ) :
    gTerm α c' D T u (reidx D p) = fTerm α c' D T u p := by
  simp only [gTerm, reidx, fTerm]
  rw [if_pos (by omega), show p.1 + p.2 + D - p.2 = p.1 + D by omega,
    show p.1 + D - D = p.1 by omega]

theorem gTerm_support (α c' : ℂ) (D : ℕ) (T : ℕ → ℂ) (u : ℂ) :
    Function.support (gTerm α c' D T u) ⊆ Set.range (reidx D) := by
  intro p hp
  simp only [Function.mem_support, gTerm] at hp
  split_ifs at hp with h
  · exact ⟨(p.1 - p.2 - D, p.2), by simp only [reidx]; ext <;> simp; omega⟩
  · exact absurd rfl hp

/-- **The scalar regrouping**, with absolute convergence. -/
theorem laurent_core (α c' : ℂ) (D : ℕ) (T : ℕ → ℂ) {ρ t : ℝ} (hρ : 0 ≤ ρ) (hρ3 : ρ ≤ 1 / 3)
    (hρt : ρ * psMass exponentialUnit ρ ≤ t)
    (hT : Summable (fun k => ‖T k‖ * t ^ k)) {u : ℂ} (hu : ‖u‖ ≤ ρ) :
    HasSum (fun k => psEval (bracketFactor α c' (k + D)) u * u ^ (k + D) * T k)
      (∑' s, ∑ r ∈ Finset.range (s + 1), gTerm α c' D T u (s, r)) ∧
    Summable (fun s => ‖∑ r ∈ Finset.range (s + 1), gTerm α c' D T u (s, r)‖) := by
  have hρ1 : ρ < 1 := by linarith
  set ME := psMass exponentialUnit ρ with hME
  have hME0 : 0 ≤ ME := psMass_nonneg _ hρ
  set C := Real.exp (‖α‖ * ρ) * psMass (exponentialUnitPower c') ρ with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (psMass_nonneg _ hρ)
  have hBF := fun m => conv_bracketFactor α c' m hρ hρ3
  -- norm bound on f
  have hfb : ∀ p : ℕ × ℕ, ‖fTerm α c' D T u p‖ ≤
      (‖PowerSeries.coeff p.2 (bracketFactor α c' (p.1 + D))‖ * ρ ^ p.2) *
        (ρ ^ (p.1 + D) * ‖T p.1‖) := by
    intro p
    simp only [fTerm]
    rw [norm_mul, norm_mul, norm_pow, show p.1 + p.2 + D = p.2 + (p.1 + D) by ring, pow_add]
    have h1 : ‖u‖ ^ p.2 ≤ ρ ^ p.2 := pow_le_pow_left₀ (norm_nonneg u) hu _
    have h2 : ‖u‖ ^ (p.1 + D) ≤ ρ ^ (p.1 + D) := pow_le_pow_left₀ (norm_nonneg u) hu _
    have := mul_le_mul h1 h2 (pow_nonneg (norm_nonneg u) _) (pow_nonneg hρ _)
    calc ‖PowerSeries.coeff p.2 (bracketFactor α c' (p.1 + D))‖ *
          (‖u‖ ^ p.2 * ‖u‖ ^ (p.1 + D)) * ‖T p.1‖
        ≤ ‖PowerSeries.coeff p.2 (bracketFactor α c' (p.1 + D))‖ *
          (ρ ^ p.2 * ρ ^ (p.1 + D)) * ‖T p.1‖ := by gcongr
      _ = _ := by ring
  set Fb : ℕ × ℕ → ℝ := fun p => (‖PowerSeries.coeff p.2 (bracketFactor α c' (p.1 + D))‖ *
      ρ ^ p.2) * (ρ ^ (p.1 + D) * ‖T p.1‖) with hFb
  have hFb0 : ∀ p, 0 ≤ Fb p := fun p => mul_nonneg (mul_nonneg (norm_nonneg _)
    (pow_nonneg hρ _)) (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _))
  have hrowb : ∀ k, ∑' r, Fb (k, r) ≤ C * (ρ * ME) ^ D * (‖T k‖ * t ^ k) := by
    intro k
    simp only [hFb]
    rw [tsum_mul_right]
    have hm := (hBF (k + D)).2
    have hpk : (ρ * ME) ^ k ≤ t ^ k :=
      pow_le_pow_left₀ (mul_nonneg hρ hME0) hρt k
    calc psMass (bracketFactor α c' (k + D)) ρ * (ρ ^ (k + D) * ‖T k‖)
        ≤ (C * ME ^ (k + D)) * (ρ ^ (k + D) * ‖T k‖) := by
          gcongr
      _ = C * (ρ * ME) ^ D * ((ρ * ME) ^ k * ‖T k‖) := by ring
      _ ≤ C * (ρ * ME) ^ D * (t ^ k * ‖T k‖) := by gcongr
      _ = C * (ρ * ME) ^ D * (‖T k‖ * t ^ k) := by ring
  have hFbs : Summable Fb := by
    refine (summable_prod_of_nonneg hFb0).mpr ⟨fun k => ?_, ?_⟩
    · exact ((hBF (k + D)).1.mul_right (ρ ^ (k + D) * ‖T k‖)).congr fun r => rfl
    · exact (hT.mul_left (C * (ρ * ME) ^ D)).of_nonneg_of_le
        (fun k => tsum_nonneg fun r => hFb0 _) hrowb
  have hfs : Summable (fun p => ‖fTerm α c' D T u p‖) :=
    hFbs.of_nonneg_of_le (fun p => norm_nonneg _) hfb
  have hf : Summable (fTerm α c' D T u) := hfs.of_norm
  -- rows of f
  have hrowv : ∀ k, ∑' r, fTerm α c' D T u (k, r) =
      psEval (bracketFactor α c' (k + D)) u * u ^ (k + D) * T k := by
    intro k
    have h := (hasSum_psEval (hBF (k + D)).1 hu).mul_right (u ^ (k + D) * T k)
    rw [mul_assoc, ← h.tsum_eq]
    refine tsum_congr fun r => ?_
    simp only [fTerm]
    rw [show k + r + D = r + (k + D) by ring, pow_add]; ring
  -- g
  have hgs : Summable (fun p => ‖gTerm α c' D T u p‖) := by
    rw [← (reidx_injective D).summable_iff]
    · exact hfs.congr fun p => by simp only [Function.comp_apply, gTerm_reidx]
    · intro p hp
      have : gTerm α c' D T u p = 0 := by
        by_contra hne
        exact hp (gTerm_support α c' D T u hne)
      simp [this]
  have hg : Summable (gTerm α c' D T u) := hgs.of_norm
  have hfg : ∑' p, fTerm α c' D T u p = ∑' p, gTerm α c' D T u p := by
    rw [← (reidx_injective D).tsum_eq (gTerm_support α c' D T u)]
    exact tsum_congr fun p => (gTerm_reidx α c' D T u p).symm
  have hgrow : ∀ s, ∑' r, gTerm α c' D T u (s, r) =
      ∑ r ∈ Finset.range (s + 1), gTerm α c' D T u (s, r) := by
    intro s
    refine tsum_eq_sum fun r hr => ?_
    rw [Finset.mem_range, not_lt] at hr
    simp only [gTerm]
    rw [if_neg (by omega)]
  refine ⟨?_, ?_⟩
  · have h1 : HasSum (fun k => ∑' r, fTerm α c' D T u (k, r)) (∑' p, fTerm α c' D T u p) := by
      rw [hf.tsum_prod]; exact hf.prod.hasSum
    rw [hfg, hg.tsum_prod] at h1
    simp only [hgrow] at h1
    exact h1.congr_fun fun k => (hrowv k).symm
  · refine (hgs.prod).of_nonneg_of_le (fun s => norm_nonneg _) fun s => ?_
    rw [← hgrow s]
    exact norm_tsum_le_tsum_norm (hgs.prod_factor s)

/-! ## The iterate -/

/-- The `u^s` coefficient vector: the formal bracket mode. -/
theorem gTerm_sum_eq (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {y : P₂.carrier}
    {α β : ℂ} (hx : x ∈ P₁.isMod.weight α) (hy : y ∈ P₂.isMod.weight β) (κ' : ℂ) (N0 D : ℕ)
    (hD : κ' - α - β + N0 = D) (τ : UpperHalfPlane) (u : ℂ) (s : ℕ) :
    ∑ r ∈ Finset.range (s + 1), gTerm α (Q.h - κ' - N0) D (rowT Y₃ Y₄ x y α β τ) u (s, r) =
      u ^ s * traceFunction Y₃ N.h
        (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0)) x y) τ := by
  set n : ℂ := κ' - 1 - Q.h - ((s : ℂ) - N0) with hn
  have hK : ∀ r : ℕ, s + 1 ≤ r → Y₄.val (n + r) x y = 0 := by
    intro r hr
    refine mode_eq_zero_below Y₄ hx hy (n + r) (r + D - s - 1) ?_
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    linear_combination (-1 : ℂ) * hD
  rw [bracketModes_eq_sum_range Y₄ hx n y (s + 1) hK]
  rw [← tfLin_apply hC2 iQ Y₃ (LWModule.hasConformalWeight N), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [map_smul, tfLin_apply, smul_eq_mul]
  simp only [gTerm]
  split_ifs with h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    have h1 : s - r = k + D := by omega
    rw [h1, show k + D - D = k by omega]
    have hc : bracketCoeff α n r = PowerSeries.coeff r (bracketFactor α (Q.h - κ' - N0) (k + D)) :=
      bracketCoeff_eq α n _ (k + D) r (by
        rw [hn, hk]; push_cast; ring)
    have hm : n + r = (α + β - 1 - Q.h) - k := by
      rw [hn, hk]; push_cast; linear_combination hD
    rw [hc, hm]
    unfold rowT
    ring
  · have hz : Y₄.val (n + r) x y = 0 := by
      refine mode_eq_zero_below Y₄ hx hy (n + r) (r + D - s - 1) ?_
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      linear_combination (-1 : ℂ) * hD
    rw [hz, traceFunction_zero, mul_zero, mul_zero]

/-- **The Laurent expansion of one homogeneous pair in the torus coordinate.** -/
theorem pair_laurent (hV : StronglyRational W) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {y : P₂.carrier}
    {α β : ℂ} (hx : x ∈ P₁.isMod.weight α) (hy : y ∈ P₂.isMod.weight β) (κ' : ℂ) (N0 D : ℕ)
    (hD : κ' - α - β + N0 = D) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      HasSum (fun s : ℕ => exp ((Q.h - κ' - N0) * log u) * u ^ s *
          traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0)) x y) τ)
        (exp (α * u) * iterF Y₃ Y₄ x y α β τ (exp u - 1)) ∧
      Summable (fun s : ℕ => ‖exp ((Q.h - κ' - N0) * log u) * u ^ s *
          traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0)) x y) τ‖) := by
  obtain ⟨t, δs, ht0, hδs, htl, hT, hsew⟩ := rowT_geometric hV i₁ i₂ iN iQ Y₃ Y₄ hx hy τ
  set ρ : ℝ := min (1 / 3) (t / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ3 : ρ ≤ 1 / 3 := min_le_left _ _
  have hρt2 : ρ ≤ t / 2 := min_le_right _ _
  have hρ1 : ρ < 1 := by linarith
  have hME : psMass exponentialUnit ρ ≤ 3 / 2 := by
    have := (conv_unit hρ0.le hρ1).2
    have := ratio_le_half hρ0.le hρ3
    linarith
  have hρt : ρ * psMass exponentialUnit ρ ≤ t := by
    have h0 := psMass_nonneg exponentialUnit hρ0.le
    nlinarith
  refine ⟨ρ, hρ0, fun u hu hre => ?_⟩
  have hu' : ‖u‖ ≤ ρ := hu.le
  set c' : ℂ := Q.h - κ' - N0 with hc'
  set E : ℂ := psEval exponentialUnit u with hE
  have hzE : exp u - 1 = u * E := (psEval_unit_mul hρ0.le hρ1 hu').symm
  have hpu := re_pos_of_exp_sub_one hre
  have hEre : 0 < E.re := re_unit_pos hρ0.le hρ3 hu'
  have hz0 : exp u - 1 ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre
  have hzn : ‖exp u - 1‖ < δs := by
    rw [hzE, norm_mul]
    have := norm_unit_le hρ0.le hρ1 hu'
    calc ‖u‖ * ‖E‖ ≤ ρ * psMass exponentialUnit ρ :=
          mul_le_mul hu' this (norm_nonneg _) hρ0.le
      _ ≤ t := hρt
      _ < δs := htl
  have hrows := (iterF_hasSum_rows Y₃ Y₄ hx hy τ _ (hsew _ hz0 hzn)).1
  have hrows' := hrows.mul_left (exp (α * u))
  have hterm : ∀ k : ℕ, exp (α * u) * ((exp u - 1) ^ ((Q.h + k) - α - β) *
      traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ) =
      exp (c' * log u) * (psEval (bracketFactor α c' (k + D)) u * u ^ (k + D) *
        rowT Y₃ Y₄ x y α β τ k) := by
    intro k
    have hexp : (Q.h + k) - α - β = c' + ((k + D : ℕ) : ℂ) := by
      rw [hc']; push_cast; linear_combination hD
    rw [hexp, hzE, cpow_mul_split hpu hEre c' (k + D),
      psEval_bracketFactor α c' (k + D) hρ0.le hρ3 hu']
    unfold rowT
    rw [← hE]
    ring
  have hcore := laurent_core α c' D (rowT Y₃ Y₄ x y α β τ) hρ0.le hρ3 hρt hT hu'
  have hval : exp (α * u) * iterF Y₃ Y₄ x y α β τ (exp u - 1) =
      exp (c' * log u) * ∑' s, ∑ r ∈ Finset.range (s + 1),
        gTerm α c' D (rowT Y₃ Y₄ x y α β τ) u (s, r) :=
    (hrows'.congr_fun fun k => (hterm k).symm).unique (hcore.1.mul_left _)
  have hS : ∀ s : ℕ, ∑ r ∈ Finset.range (s + 1), gTerm α c' D (rowT Y₃ Y₄ x y α β τ) u (s, r) =
      u ^ s * traceFunction Y₃ N.h (bracketModes Y₄ (κ' - 1 - Q.h - ((s : ℂ) - N0)) x y) τ :=
    gTerm_sum_eq hV.c2Cofinite iQ Y₃ Y₄ hx hy κ' N0 D hD τ u
  have hsum := hcore.2
  simp only [hS] at hsum hval
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact (hsum.of_norm.hasSum.mul_left _).congr_fun fun s => by ring
  · refine (hsum.mul_left ‖exp (c' * log u)‖).congr fun s => ?_
    simp only [norm_mul]; ring

end VOA.Huang.GenusOneG1e
