import VOA.Huang.GenusOneG1dAssembly
import VOA.Huang.GenusOneG1cSCovariance

/-!
# (N1) from the sharp bracket-coordinate expansion

`GenusOneG1c.VacuumChannelBracketExpansion` (the named input for step (b)) only
asserts EXISTENCE of a prefactor `P(z₀)` and of exponents `κ_m`, for `L(0)`-homogeneous
insertions. That is too weak for the assembly: with an arbitrary `P` the identity at the point
`u/τ` (modulus `S τ`) and at `u` (modulus `τ`) cannot be compared (`P(z₀') ≠ P(z₀)`), and with
non-constant `κ_m` the S-transform `bracketChannel_S` rescales each term by its own `e^{κ_m L}`,
so it is NOT a multiple of the original channel. Both defects are absent in the mathematics:
for `L[0]`-homogeneous insertions, in the torus frame (`e^{α_{a,i} u}` per component) the
prefactor is `1` and `κ = ω_a + ω_b` is constant.

* `VacuumChannelBracketSharp` — the sharp form (TRUE; it is exactly what Zhu's coordinate change
  for intertwining operators gives, and what `VOA/Huang/GenusOneIntCoord*.lean` is formalising):
  `vacF c ins x τ u = Σ_m coef_m u^{n_m − κ} traceFun x (v_m) τ`, `v_m ∈ V_[n_m]`, absolutely
  convergent, for small `u` with `Re(e^u − 1) > 0`.
* `vacuumSCovariance_of_sharp` — (N1) follows, by `bracketChannel_S` (Zhu's theorem, termwise)
  and `log(u/τ) = log u − log τ` (`log_div_of_re_pos`).
* `vacuumChannelTransportInput_of_bracket` — (G1) from the sharp bracket expansion and
  (N2)–(N4); `fusionEigenInput_of_bracket` — Huang's Thm 5.2 from the same.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1d

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion
  VOA.Huang.GenusOneG1c CategoryTheory Complex VOA.Classification.COne VOA.Huang.ZhuModData
open scoped BigOperators MatrixGroups

universe u w

/-- `log(u/τ) = log u − log τ` when `u` and `u/τ` are in the right half-plane and `τ ∈ ℍ`. -/
theorem log_div_of_re_pos (τ : UpperHalfPlane) {u : ℂ} (hu : 0 < u.re) (hut : 0 < (u / τ).re) :
    log (u / τ) = log u - log τ := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; exact lt_irrefl _ hu
  have hut0 : u / τ ≠ 0 := div_ne_zero hu0 hτ
  have hexp : exp (log (u / τ) + log τ) = exp (log u) := by
    rw [exp_add, exp_log hut0, exp_log hτ, exp_log hu0, div_mul_cancel₀ _ hτ]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hk
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, Complex.intCast_re,
    Complex.intCast_im, zero_add] at him
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)).re = 2 * Real.pi := by
    rw [show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [h2pi, Complex.log_im, Complex.log_im, Complex.log_im] at him
  have ha1 : |(u / τ).arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hut)
  have ha2 : |u.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have ha3 : 0 ≤ (τ : ℂ).arg := Complex.arg_nonneg_iff.mpr τ.im_pos.le
  have ha4 : (τ : ℂ).arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr τ.im_pos.ne')
  have hk0 : k = 0 := by
    have hpi := Real.pi_pos
    have h1 := abs_lt.mp ha1
    have h2 := abs_lt.mp ha2
    have hk1 : (-1 : ℝ) < k := by nlinarith
    have hk2 : (k : ℝ) < 1 := by nlinarith
    have : (-1 : ℤ) < k := by exact_mod_cast hk1
    have : k < 1 := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul, add_zero] at hk
  rw [← hk]; ring

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) {D : VOA.ModularData W ι} {a b : ι}

/-- **The sharp bracket-coordinate expansion of the vacuum channel** (TRUE: Zhu's coordinate
change for the intertwiner `Y^e`; the prefactor `(1 + z₀)^{−α_a}` of
`VacuumChannelBracketExpansion` is absorbed by the torus normalisation `e^{α_{a,i} u}`, and for an
`L[0]`-homogeneous insertion every bracket component `v_m = (w_a)[k] w_b` has `n_m − κ = −k − 1`
with the SAME `κ = ω_a + ω_b`). -/
def VacuumChannelBracketSharp (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b) : Prop :=
  ∀ ins : Insertion D a b, ∃ (coef : ℕ → ℂ) (v : ℕ → 𝒱) (n : ℕ → ℕ),
    (∀ m, v m ∈ sqWeightSpace W (n m : ℂ)) ∧
    ∀ τ : UpperHalfPlane, ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (u : ℂ), ‖u‖ < δ →
      0 < (exp u - 1).re →
      Summable (fun m => coef m * exp (((n m : ℂ) - ins.κ) * log u) *
        traceFun D.Mfam D.h x (v m) τ) ∧
      vacF F hv c ins x τ u = bracketChannel D coef v n (fun _ => ins.κ) x (log u) τ

/-- **(N1) from the sharp bracket expansion** and Zhu's modularity. -/
theorem vacuumSCovariance_of_sharp (hZ : ZhuModularityAnalytic D) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (h : VacuumChannelBracketSharp F hv c) :
    VacuumSCovariance F hv c := by
  intro ins τ
  obtain ⟨coef, v, n, hvn, hE⟩ := h ins
  obtain ⟨δ₁, hδ₁, h₁⟩ := hE τ
  obtain ⟨δ₂, hδ₂, h₂⟩ := hE (ModularGroup.S • τ)
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hτn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hτ
  refine ⟨min δ₁ (δ₂ * ‖(τ : ℂ)‖), lt_min hδ₁ (mul_pos hδ₂ hτn), fun u hu hre hre' x => ?_⟩
  have hn1 : ‖u‖ < δ₁ := lt_of_lt_of_le hu (min_le_left _ _)
  have hn2 : ‖u / τ‖ < δ₂ := by
    rw [norm_div, div_lt_iff₀ hτn]; exact lt_of_lt_of_le hu (min_le_right _ _)
  rw [(h₂ x (u / τ) hn2 hre').2,
    log_div_of_re_pos τ (re_pos_of_re_exp_sub_one_pos hre) (re_pos_of_re_exp_sub_one_pos hre')]
  have hsum : ∀ y, Summable fun m => coef m * exp (ins.κ * log τ) *
      exp (((n m : ℂ) - ins.κ) * log u) * traceFun D.Mfam D.h y (v m) τ := by
    intro y
    have := ((h₁ y u hn1 hre).1).mul_left (exp (ins.κ * log τ))
    convert this using 1
    funext m; ring
  rw [bracketChannel_S D hZ coef v n (fun _ => ins.κ) hvn x (log u) (log τ) τ (exp_log hτ) hsum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [(h₁ y u hn1 hre).2]
  unfold bracketChannel
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-- The sharp bracket expansion for every instance. -/
def VacuumBracketSharpInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0),
        VacuumChannelBracketSharp F hv c

/-- (N1) for every instance, from the sharp bracket expansion. -/
theorem vacuumSCovarianceInput_of_bracket (h : VacuumBracketSharpInput.{u, w}) :
    VacuumSCovarianceInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp F a b c hv
  exact vacuumSCovariance_of_sharp F hZ hv c (h 𝒱 W hNice ι D hZ hirr hcomp F a b c hv)

/-- **(G1) from the sharp bracket-coordinate expansion and (N2)–(N4).** -/
theorem vacuumChannelTransportInput_of_bracket (h1 : VacuumBracketSharpInput.{u, w})
    (h2 : ConjugationInputAll.{u, w}) (h3 : ChannelSStabilityInput.{u, w})
    (h4 : ChannelIndependenceInput.{u, w}) : VacuumChannelTransportInput.{u, w} :=
  vacuumChannelTransportInput_of_genusOneInputs (vacuumSCovarianceInput_of_bracket h1) h2 h3 h4

/-- **Huang's Thm 5.2 from the sharp bracket-coordinate expansion and (N2)–(N4).** -/
theorem fusionEigenInput_of_bracket (h1 : VacuumBracketSharpInput.{u, w})
    (h2 : ConjugationInputAll.{u, w}) (h3 : ChannelSStabilityInput.{u, w})
    (h4 : ChannelIndependenceInput.{u, w}) : VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_genusOneInputs (vacuumSCovarianceInput_of_bracket h1) h2 h3 h4

end VOA.Huang.GenusOneG1d
