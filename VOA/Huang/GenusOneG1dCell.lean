import VOA.Huang.GenusOneG1Cycles
import VOA.Huang.GenusOneG1cAnalytic

/-!
# The genus-one product channel on its strip, and continuation across the period cell

Step (4a) of the proof of (G1): the
geometric content of Huang's relation `T_B ∘ S = S ∘ T_A` (Prop. 4.5).

In the torus coordinate `u = ℓ₁ − ℓ₂` (difference of the logarithms of the two insertion points;
lattice `2πi(ℤ + τℤ)`) the product channel is a single-valued holomorphic function on the strip
`Σ(τ) = {0 < Re u < 2π Im τ}` between the two lattice lines through `0` and `−2πiτ`.

* `cellF` — the product channel normalised by `e^{α₁ u}`, as a function of `u` alone;
  `exp_mul_prodLift` — translation invariance:
  `e^{α₁ℓ₁ + α₂ℓ₂} prodLift(ℓ₁, ℓ₂) = cellF(ℓ₁ − ℓ₂)` (termwise, from the mode bookkeeping
  `sMode + rMode = α₁ + α₂ − 2`).
* `cellF_differentiableOn` — `cellF` is holomorphic on the whole strip `Σ(τ)` (Weierstrass
  M-test on open rectangles; domination by the absolutely convergent real points).
* `cell τ = Σ(τ) ∩ τ · Σ(S τ)` — the open period parallelogram with vertices `0, 2πi, −2πiτ,
  2πi − 2πiτ`; `isOpen_cell`, `convex_cell`.
* `cell_eqOn` — the identity theorem on the cell: if `G'(u/τ) = c · G(u)` on a nonempty open
  subset of the cell (in practice: near the corner `0`, where both are vacuum channels and the
  near-collision S-covariance applies), then on the whole cell, in particular near the corner
  `−2πiτ`, where `G` is the B-transported channel at modulus `τ` and `G'(·/τ)` is the A-transported
  channel at modulus `S τ`.
* `exists_small_re_exp` — small points with `Re(e^{u} − 1) > 0` and `Re(e^{u·w} − 1) > 0`
  (non-vacuity of the sectors used below).

No VOA input beyond the product-channel convergence; no axioms beyond Lean's three and those of
the imported convergence theorems.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1d

open VOA VOA.Huang Complex Filter Topology
open VOA.Huang.GenusOneWard (liftTerm prodLift liftTerm_eq_exp summable_liftTerm sMode rMode)

universe u

/-! ## §1 Normalisation and translation invariance -/

section Channel

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}
  (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- The product channel in the torus coordinate `u = ℓ₁ − ℓ₂`, normalised by `e^{α₁ u}`. -/
def cellF (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ τ u : ℂ) : ℂ :=
  exp (α₁ * u) * prodLift Y₁ Y₂ x y α₁ α₂ u 0 τ

/-- Shifting the first logarithm multiplies a term by an exponential. -/
theorem liftTerm_shift (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ d ℓ₂ τ : ℂ) (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ (ℓ₁ + d) ℓ₂ τ p =
      exp (d * (-sMode N Q α₁ p.1 p.2 - 1)) * liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p := by
  unfold liftTerm
  rw [add_mul, exp_add]
  ring

/-- Termwise translation invariance. -/
theorem exp_mul_liftTerm (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) (p : ℕ × ℕ) :
    exp (α₁ * ℓ₁ + α₂ * ℓ₂) * liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p =
      exp (α₁ * (ℓ₁ - ℓ₂)) * liftTerm Y₁ Y₂ x y α₁ α₂ (ℓ₁ - ℓ₂) 0 τ p := by
  unfold liftTerm
  have h : exp (α₁ * ℓ₁ + α₂ * ℓ₂) * exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1)) *
        exp (ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1)) =
      exp (α₁ * (ℓ₁ - ℓ₂)) * exp ((ℓ₁ - ℓ₂) * (-sMode N Q α₁ p.1 p.2 - 1)) *
        exp (0 * (-rMode N Q α₂ p.1 p.2 - 1)) := by
    simp only [← exp_add]
    congr 1
    unfold sMode rMode
    ring
  linear_combination (GenusOneWard.tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 *
    exp (2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1))) * h

/-- **Translation invariance of the normalised product channel.** -/
theorem exp_mul_prodLift (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) :
    exp (α₁ * ℓ₁ + α₂ * ℓ₂) * prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ =
      cellF Y₁ Y₂ x y α₁ α₂ τ (ℓ₁ - ℓ₂) := by
  unfold cellF prodLift
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun p => exp_mul_liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p

/-! ## §2 Holomorphy on the strip -/

/-- The open strip `{0 < Re u < 2π Im τ}`. -/
def strip (τ : UpperHalfPlane) : Set ℂ := {u | 0 < u.re ∧ u.re < 2 * Real.pi * τ.im}

theorem isOpen_strip (τ : UpperHalfPlane) : IsOpen (strip τ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem convex_strip (τ : UpperHalfPlane) : Convex ℝ (strip τ) :=
  (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt _)

/-- An open rectangle. -/
def rect (a b M : ℝ) : Set ℂ := {u | a < u.re ∧ u.re < b ∧ |u.im| < M}

theorem isOpen_rect (a b M : ℝ) : IsOpen (rect a b M) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))

theorem exp_le_add_of_mem {a b t r : ℝ} (h₁ : a ≤ t) (h₂ : t ≤ b) :
    Real.exp ((t - a) * r) ≤ 1 ∨ Real.exp ((t - b) * r) ≤ 1 := by
  rcases le_or_gt 0 r with hr | hr
  · right; rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hr
  · left; rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hr.le

theorem im_sMode (α₁ : ℂ) (p : ℕ × ℕ) :
    (-sMode N Q α₁ p.1 p.2 - 1).im = (-sMode N Q α₁ 0 0 - 1).im := by
  unfold sMode
  simp

/-- Domination on a rectangle by the two real points `a`, `b`. -/
theorem norm_liftTerm_le (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ τ : ℂ) {a b M : ℝ}
    (p : ℕ × ℕ) {u : ℂ} (hu : u ∈ rect a b M) :
    ‖liftTerm Y₁ Y₂ x y α₁ α₂ u 0 τ p‖ ≤
      (‖liftTerm Y₁ Y₂ x y α₁ α₂ a 0 τ p‖ + ‖liftTerm Y₁ Y₂ x y α₁ α₂ b 0 τ p‖) *
        Real.exp (M * |(-sMode N Q α₁ 0 0 - 1).im|) := by
  obtain ⟨ha, hb, hM⟩ := hu
  set E : ℂ := -sMode N Q α₁ p.1 p.2 - 1 with hE
  have hEim : E.im = (-sMode N Q α₁ 0 0 - 1).im := im_sMode (N := N) (Q := Q) α₁ p
  -- the real part
  have hre : liftTerm Y₁ Y₂ x y α₁ α₂ u 0 τ p =
      exp (((u.im : ℂ) * I) * E) * liftTerm Y₁ Y₂ x y α₁ α₂ (u.re : ℂ) 0 τ p := by
    have := liftTerm_shift Y₁ Y₂ x y α₁ α₂ (u.re : ℂ) ((u.im : ℂ) * I) 0 τ p
    rw [Complex.re_add_im] at this
    exact this
  have himpart : ‖exp (((u.im : ℂ) * I) * E)‖ ≤ Real.exp (M * |E.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (((u.im : ℂ) * I) * E).re = -(u.im * E.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this]
    have h1 : -(u.im * E.im) ≤ |u.im| * |E.im| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h2 : |u.im| * |E.im| ≤ M * |E.im| :=
      mul_le_mul_of_nonneg_right hM.le (abs_nonneg _)
    linarith
  -- the real point between `a` and `b`
  have hshift : ∀ s : ℝ, liftTerm Y₁ Y₂ x y α₁ α₂ (u.re : ℂ) 0 τ p =
      exp (((u.re - s : ℝ) : ℂ) * E) * liftTerm Y₁ Y₂ x y α₁ α₂ (s : ℂ) 0 τ p := by
    intro s
    have := liftTerm_shift Y₁ Y₂ x y α₁ α₂ (s : ℂ) ((u.re - s : ℝ) : ℂ) 0 τ p
    rw [show (s : ℂ) + ((u.re - s : ℝ) : ℂ) = (u.re : ℂ) by push_cast; ring] at this
    exact this
  have hnorm : ∀ s : ℝ, ‖exp (((u.re - s : ℝ) : ℂ) * E)‖ = Real.exp ((u.re - s) * E.re) := by
    intro s
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hreal : ‖liftTerm Y₁ Y₂ x y α₁ α₂ (u.re : ℂ) 0 τ p‖ ≤
      ‖liftTerm Y₁ Y₂ x y α₁ α₂ a 0 τ p‖ + ‖liftTerm Y₁ Y₂ x y α₁ α₂ b 0 τ p‖ := by
    rcases exp_le_add_of_mem (r := E.re) ha.le hb.le with h | h
    · rw [hshift a, norm_mul, hnorm a]
      have := mul_le_mul_of_nonneg_right h (norm_nonneg (liftTerm Y₁ Y₂ x y α₁ α₂ a 0 τ p))
      rw [one_mul] at this
      linarith [norm_nonneg (liftTerm Y₁ Y₂ x y α₁ α₂ b 0 τ p)]
    · rw [hshift b, norm_mul, hnorm b]
      have := mul_le_mul_of_nonneg_right h (norm_nonneg (liftTerm Y₁ Y₂ x y α₁ α₂ b 0 τ p))
      rw [one_mul] at this
      linarith [norm_nonneg (liftTerm Y₁ Y₂ x y α₁ α₂ a 0 τ p)]
  rw [hre, norm_mul, mul_comm, ← hEim]
  exact mul_le_mul hreal himpart (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Every term is entire in the first logarithm. -/
theorem differentiable_liftTerm (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ τ : ℂ) (p : ℕ × ℕ) :
    Differentiable ℂ fun u => liftTerm Y₁ Y₂ x y α₁ α₂ u 0 τ p := by
  have h : (fun u => liftTerm Y₁ Y₂ x y α₁ α₂ u 0 τ p) = fun u =>
      exp (u * (-sMode N Q α₁ p.1 p.2 - 1)) * liftTerm Y₁ Y₂ x y α₁ α₂ 0 0 τ p := by
    funext u
    have := liftTerm_shift Y₁ Y₂ x y α₁ α₂ 0 u 0 τ p
    rwa [zero_add] at this
  rw [h]
  fun_prop

/-- **The product channel is holomorphic on the whole strip.** -/
theorem prodLift_differentiableOn (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (fun u => prodLift Y₁ Y₂ x y α₁ α₂ u 0 τ) (strip τ) := by
  have hq : ∀ t : ℝ, t < 2 * Real.pi * τ.im → ‖qParam τ‖ * Real.exp t < Real.exp (0 : ℂ).re := by
    intro t ht
    have hqn : ‖qParam τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [qParam, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hqn, ← Real.exp_add, Complex.zero_re]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsum : ∀ t : ℝ, 0 < t → t < 2 * Real.pi * τ.im →
      Summable fun p => ‖liftTerm Y₁ Y₂ x y α₁ α₂ (t : ℂ) 0 τ p‖ := by
    intro t ht0 ht1
    refine summable_norm_iff.mpr (summable_liftTerm Y₁ Y₂ hV i₁ i₂ iN hx hy (t : ℂ) 0 τ
      (by simpa using ht0) ?_)
    simpa using hq t ht1
  intro u₀ hu₀
  obtain ⟨h0, h1⟩ := hu₀
  set a : ℝ := u₀.re / 2
  set b : ℝ := (u₀.re + 2 * Real.pi * τ.im) / 2
  set M : ℝ := |u₀.im| + 1
  have ha0 : 0 < a := by positivity
  have hab : a < u₀.re := by simp only [a]; linarith
  have hbu : u₀.re < b := by simp only [b]; linarith
  have hb1 : b < 2 * Real.pi * τ.im := by simp only [b]; linarith
  have hmem : u₀ ∈ rect a b M := ⟨hab, hbu, by simp only [M]; linarith⟩
  have hD : DifferentiableOn ℂ (fun u => ∑' p, liftTerm Y₁ Y₂ x y α₁ α₂ u 0 τ p) (rect a b M) :=
    differentiableOn_tsum_of_summable_norm
      (((hsum a ha0 (by linarith)).add (hsum b (by linarith) hb1)).mul_right
        (Real.exp (M * |(-sMode N Q α₁ 0 0 - 1).im|)))
      (fun p => (differentiable_liftTerm Y₁ Y₂ x y α₁ α₂ τ p).differentiableOn)
      (isOpen_rect a b M) (fun p u hu => norm_liftTerm_le Y₁ Y₂ x y α₁ α₂ τ p hu)
  exact ((hD u₀ hmem).differentiableAt ((isOpen_rect a b M).mem_nhds hmem)).differentiableWithinAt

/-- **`cellF` is holomorphic on the strip.** -/
theorem cellF_differentiableOn (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (cellF Y₁ Y₂ x y α₁ α₂ τ) (strip τ) := by
  have h := prodLift_differentiableOn Y₁ Y₂ hV i₁ i₂ iN hx hy τ
  exact (differentiable_exp.comp
    (differentiable_const α₁ |>.mul differentiable_id)).differentiableOn.mul h

end Channel

/-! ## §3 The period cell and the identity theorem -/

/-- The open period parallelogram: `u ∈ Σ(τ)` and `u/τ ∈ Σ(S τ)`. -/
def cell (τ : UpperHalfPlane) : Set ℂ :=
  {u | u ∈ strip τ ∧ u / (τ : ℂ) ∈ strip (ModularGroup.S • τ)}

theorem isOpen_cell (τ : UpperHalfPlane) : IsOpen (cell τ) :=
  (isOpen_strip τ).inter ((isOpen_strip _).preimage (continuous_id.div_const _))

theorem convex_cell (τ : UpperHalfPlane) : Convex ℝ (cell τ) := by
  have hB : Convex ℝ (((LinearMap.lsmul ℂ ℂ ((τ : ℂ)⁻¹)).restrictScalars ℝ) ⁻¹'
      strip (ModularGroup.S • τ)) := (convex_strip _).linear_preimage _
  have heq : cell τ = strip τ ∩ (((LinearMap.lsmul ℂ ℂ ((τ : ℂ)⁻¹)).restrictScalars ℝ) ⁻¹'
      strip (ModularGroup.S • τ)) := by
    ext u
    simp only [cell, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, smul_eq_mul, div_eq_mul_inv,
      mul_comm]
  rw [heq]
  exact (convex_strip τ).inter hB

/-- `S τ = −1/τ` as a complex number. -/
theorem coe_S_smul (τ : UpperHalfPlane) : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / τ := by
  rw [UpperHalfPlane.modular_S_smul]
  rw [UpperHalfPlane.coe_mk, inv_neg, neg_div, one_div]

/-- `S (S τ) = τ`. -/
theorem S_smul_S_smul (τ : UpperHalfPlane) : ModularGroup.S • ModularGroup.S • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, coe_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

/-- **Continuation across the period cell (identity theorem).** If `G'(u/τ) = c · G(u)` on a
nonempty open subset of the cell, with `G` holomorphic on `Σ(τ)` and `G'` on `Σ(S τ)`, the identity
holds on the whole cell. -/
theorem cell_eqOn {G G' : ℂ → ℂ} {τ : UpperHalfPlane} (c : ℂ)
    (hG : DifferentiableOn ℂ G (strip τ))
    (hG' : DifferentiableOn ℂ G' (strip (ModularGroup.S • τ)))
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) (hUsub : U ⊆ cell τ)
    (heq : ∀ u ∈ U, G' (u / τ) = c * G u) :
    ∀ u ∈ cell τ, G' (u / τ) = c * G u := by
  have h1 : DifferentiableOn ℂ (fun u => G' (u / τ)) (cell τ) :=
    hG'.comp (differentiable_id.div_const _).differentiableOn fun u hu => hu.2
  have h2 : DifferentiableOn ℂ (fun u => c * G u) (cell τ) :=
    (hG.mono fun u hu => hu.1).const_mul c
  obtain ⟨u₀, hu₀⟩ := hUne
  have hev : (fun u => G' (u / τ)) =ᶠ[𝓝 u₀] fun u => c * G u :=
    Filter.eventually_of_mem (hU.mem_nhds hu₀) heq
  exact fun u hu => (h1.analyticOnNhd (isOpen_cell τ)).eqOn_of_preconnected_of_eventuallyEq
    (h2.analyticOnNhd (isOpen_cell τ)) (convex_cell τ).isPreconnected (hUsub hu₀) hev hu

/-! ## §4 Small points in a prescribed direction -/

/-- If `Re v > 0`, then `Re(e^{r v} − 1) > 0` for all small `r > 0`. -/
theorem re_exp_sub_one_pos {v : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r * ‖v‖ ≤ 1)
    (hr2 : r * ‖v‖ ^ 2 < v.re) : 0 < (exp ((r : ℂ) * v) - 1).re := by
  have hn : ‖(r : ℂ) * v‖ = r * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hb := Complex.norm_exp_sub_one_sub_id_le (x := (r : ℂ) * v) (by rw [hn]; exact hr1)
  have hre : ((r : ℂ) * v).re = r * v.re := by simp [Complex.mul_re]
  have h1 : |(exp ((r : ℂ) * v) - 1 - (r : ℂ) * v).re| ≤ ‖(r : ℂ) * v‖ ^ 2 :=
    (Complex.abs_re_le_norm _).trans hb
  rw [hn] at h1
  have h2 : (exp ((r : ℂ) * v) - 1).re =
      (exp ((r : ℂ) * v) - 1 - (r : ℂ) * v).re + r * v.re := by
    rw [Complex.sub_re _ ((r : ℂ) * v), hre]; ring
  have h3 := neg_abs_le (exp ((r : ℂ) * v) - 1 - (r : ℂ) * v).re
  have h4 : (r * ‖v‖) ^ 2 < r * v.re := by
    rw [mul_pow]
    have : r ^ 2 * ‖v‖ ^ 2 = r * (r * ‖v‖ ^ 2) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left hr2 hr
  linarith

/-- For `Re v > 0` and `Re (v w) > 0`, arbitrarily small points `u = r v` have
`Re(e^u − 1) > 0` and `Re(e^{u w} − 1) > 0`. -/
theorem exists_small_re_exp {v w : ℂ} (hv : 0 < v.re) (hvw : 0 < (v * w).re) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ‖(r : ℂ) * v‖ < δ ∧ 0 < (exp ((r : ℂ) * v) - 1).re ∧
      0 < (exp ((r : ℂ) * v * w) - 1).re := by
  have hv0 : 0 < ‖v‖ := by
    have := Complex.abs_re_le_norm v
    rw [abs_of_pos hv] at this; linarith
  have hvw0 : 0 < ‖v * w‖ := by
    have := Complex.abs_re_le_norm (v * w)
    rw [abs_of_pos hvw] at this; linarith
  -- choose `r` below each threshold
  set r : ℝ := min (min (1 / ‖v‖) (1 / ‖v * w‖)) (min (min (v.re / ‖v‖ ^ 2)
    ((v * w).re / ‖v * w‖ ^ 2)) (δ / ‖v‖)) / 2 with hr
  have hpos : 0 < min (min (1 / ‖v‖) (1 / ‖v * w‖)) (min (min (v.re / ‖v‖ ^ 2)
      ((v * w).re / ‖v * w‖ ^ 2)) (δ / ‖v‖)) := by
    refine lt_min (lt_min (by positivity) (by positivity))
      (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  have hr0 : 0 < r := by rw [hr]; positivity
  set m := min (min (1 / ‖v‖) (1 / ‖v * w‖)) (min (min (v.re / ‖v‖ ^ 2)
    ((v * w).re / ‖v * w‖ ^ 2)) (δ / ‖v‖)) with hm
  have hrm : r < m := by rw [hr]; linarith
  have hle1 : r < 1 / ‖v‖ := lt_of_lt_of_le hrm ((min_le_left _ _).trans (min_le_left _ _))
  have hle2 : r < 1 / ‖v * w‖ := lt_of_lt_of_le hrm ((min_le_left _ _).trans (min_le_right _ _))
  have hle3 : r < v.re / ‖v‖ ^ 2 :=
    lt_of_lt_of_le hrm ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hle4 : r < (v * w).re / ‖v * w‖ ^ 2 :=
    lt_of_lt_of_le hrm ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hle5 : r < δ / ‖v‖ := lt_of_lt_of_le hrm ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r, hr0, ?_, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    rwa [lt_div_iff₀ hv0] at hle5
  · refine re_exp_sub_one_pos hr0 ?_ ?_
    · rw [lt_div_iff₀ hv0] at hle1; linarith
    · rwa [lt_div_iff₀ (by positivity)] at hle3
  · rw [mul_assoc]
    refine re_exp_sub_one_pos hr0 ?_ ?_
    · rw [lt_div_iff₀ hvw0] at hle2; linarith
    · rwa [lt_div_iff₀ (by positivity)] at hle4

end VOA.Huang.GenusOneG1d
