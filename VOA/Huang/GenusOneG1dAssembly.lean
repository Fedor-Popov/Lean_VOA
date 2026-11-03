import VOA.Huang.GenusOneG1dCorner
import VOA.Huang.VerlindeTransportHeadline

/-!
# Assembly of (G1) from the four named genus-one inputs

Step (4d) of the proof of (G1).

Huang's Prop. 4.5 (`T_B ∘ S = S ∘ T_A`) is realised here WITHOUT an abstract function space: the
geometric identity is the continuation of the `S`-covariance of the product channel across the
period cell (`cell_eqOn`), evaluated at the corner `−2πiτ`, where the left side is the
B-transported channel at modulus `τ` (`prodN_bcorner`) and the right side is the A-transported
channel at modulus `S τ` (`prodN_acorner`). With

* (N1) `VacuumSCovariance` at `τ` (corner `0`, to start the continuation) and at `S τ` (to return
  from modulus `S τ` to `τ`, using `S(S τ) = τ` and the inverse `T = S P_σ` of `S`),
* (N2) `ConjugationInput` (reversed pair → vacuum channel traced over the conjugate),
* (N3) `ChannelSStability` (the A-remainder at modulus `S τ` lands in `Rspan`),

one gets the germ relation `germ_relation`:
`Σ_z (e^{2πi h_b} Ω_x S_xz − μ (S·B)_xz) vacF (σ z) ≡ 0 mod Rspan`,
and (N4) `ChannelIndependence` (Huang Prop. 2.11) turns it into `S·B = diag(e^{2πi h_b} Ω/μ)·S`.

* `vacuumChannelTransport_of_inputs` — the per-instance statement;
* `vacuumChannelTransportInput_of_genusOneInputs : VacuumSCovarianceInput →
  ConjugationInputAll → ChannelSStabilityInput → ChannelIndependenceInput →
  VacuumChannelTransportInput`;
* `fusionEigenInput_of_genusOneInputs` — Huang's Thm 5.2 from the same four inputs.

The A-cycle eigenvalue `Ω_{v0} ≠ 0` is the proved `aCycleScalar_vacuum_ne_zero`; the B-cycle
matrix is the concrete `transferMatrix c β`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1d

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.GenusOneG1c CategoryTheory
  Complex VOA.Classification.COne VOA.Huang.ZhuModData
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

/-! ## §1 Elementary lemmas -/

theorem re_pos_of_re_exp_sub_one_pos {w : ℂ} (h : 0 < (exp w - 1).re) : 0 < w.re := by
  have h1 : 1 < (exp w).re := by rw [Complex.sub_re, Complex.one_re] at h; linarith
  have h2 : (exp w).re ≤ ‖exp w‖ := Complex.re_le_norm _
  rw [Complex.norm_exp] at h2
  have h3 : 1 < Real.exp w.re := lt_of_lt_of_le h1 h2
  by_contra hn
  push Not at hn
  have := Real.exp_le_one_iff.mpr hn
  linarith

/-- `log τ + log (S τ) = iπ` on the upper half-plane. -/
theorem log_add_log_S (τ : UpperHalfPlane) :
    log (τ : ℂ) + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = (Real.pi : ℂ) * I := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hexp : exp (log (τ : ℂ) + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) =
      exp ((Real.pi : ℂ) * I) := by
    rw [exp_add, exp_log hτ, exp_log hS, coe_S_smul, Complex.exp_pi_mul_I]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hb : ∀ z : ℂ, 0 < z.im → 0 ≤ (log z).im ∧ (log z).im < Real.pi := by
    intro z hz
    rw [Complex.log_im]
    exact ⟨Complex.arg_nonneg_iff.mpr hz.le, Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩
  have h1 := hb (τ : ℂ) τ.im_pos
  have h2 := hb _ (ModularGroup.S • τ).im_pos
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, Complex.intCast_re,
    Complex.intCast_im, zero_add] at him
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)).re = 2 * Real.pi := by
    rw [show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [h2pi] at him
  have hn0 : n = 0 := by
    have hpi := Real.pi_pos
    have hlo : (0 : ℝ) ≤ Real.pi + n * (2 * Real.pi) := by linarith
    have hhi : Real.pi + n * (2 * Real.pi) < 2 * Real.pi := by linarith
    have hn1 : (-1 : ℝ) < n := by nlinarith
    have hn2 : (n : ℝ) < 1 := by nlinarith
    have : (-1 : ℤ) < n := by exact_mod_cast hn1
    have : n < 1 := by exact_mod_cast hn2
    omega
  rw [hn, hn0]
  simp

theorem exists_pos_le_fintype {κ : Type*} [Finite κ] (f : κ → ℝ) (hf : ∀ k, 0 < f k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ f k := by
  have := Fintype.ofFinite κ
  obtain ⟨δ, hδ, h⟩ := exists_pos_le_fin
    (fun j : Fin (Fintype.card κ) => f ((Fintype.equivFin κ).symm j)) (fun j => hf _)
  exact ⟨δ, hδ, fun k => by simpa using h (Fintype.equivFin κ k)⟩

section Chain

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

theorem prodN_differentiableOn (hV : StronglyRational W) (c : TransferChoice F D a b) (x : ι)
    (ins : Insertion D a b) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (prodN F H c x ins τ) (strip τ) := by
  unfold prodN
  refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
    DifferentiableOn.fun_sum fun k _ => ?_
  exact cellF_differentiableOn _ _ hV (lwOf_irreducible D a) (lwOf_irreducible D b)
    (lwOf_irreducible D x) (ins.hwa i) (ins.hwb j) τ

/-- **The S-covariance of the product channel on the whole period cell**, from (N1) near the
corner `0` and the identity theorem. -/
theorem cell_identity (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (hS : VacuumSCovariance F hv c) (x : ι) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∀ q ∈ cell τ, prodN F H c x ins (ModularGroup.S • τ) (q / τ) =
      exp (ins.κ * log τ) * ∑ y, D.repS x y * prodN F H c y ins τ q := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hτn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hτ
  obtain ⟨δ1, hδ1, h1⟩ := hS ins τ
  obtain ⟨δ2, hδ2, h2⟩ := prodN_eq_vacF F H hV hv c x ins (ModularGroup.S • τ)
  have hY : ∀ y, ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      prodN F H c y ins τ u = vacF F hv c ins y τ u := fun y =>
    prodN_eq_vacF F H hV hv c y ins τ
  choose δY hδY hY using hY
  obtain ⟨δ3, hδ3, hδ3le⟩ := exists_pos_le_fintype δY hδY
  have hSim : 0 < (ModularGroup.S • τ).im := (ModularGroup.S • τ).im_pos
  have him : 0 < τ.im := τ.im_pos
  set δ0 : ℝ := min (min δ1 (δ2 * ‖(τ : ℂ)‖)) (min δ3 (min (2 * Real.pi * τ.im)
    (2 * Real.pi * (ModularGroup.S • τ).im * ‖(τ : ℂ)‖))) with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0]
    refine lt_min (lt_min hδ1 (by positivity)) (lt_min hδ3 (lt_min (by positivity)
      (by positivity)))
  set U : Set ℂ := {u : ℂ | ‖u‖ < δ0} ∩ ({u : ℂ | 0 < (exp u - 1).re} ∩
    {u : ℂ | 0 < (exp (u / τ) - 1).re}) with hU
  have hUo : IsOpen U := by
    have o1 : IsOpen {u : ℂ | ‖u‖ < δ0} := isOpen_lt continuous_norm continuous_const
    have o2 : IsOpen {u : ℂ | 0 < (exp u - 1).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_exp.sub continuous_const))
    have o3 : IsOpen {u : ℂ | 0 < (exp (u / τ) - 1).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp
        ((continuous_exp.comp (continuous_id.div_const _)).sub continuous_const))
    exact o1.inter (o2.inter o3)
  -- nonempty
  have hUne : U.Nonempty := by
    have hre : |(τ : ℂ).re| < ‖(τ : ℂ)‖ :=
      Complex.abs_re_lt_norm.mpr (by intro h0; rw [UpperHalfPlane.coe_im] at h0; linarith)
    set v : ℂ := (‖(τ : ℂ)‖ : ℂ) + τ with hv'
    have hv1 : 0 < v.re := by
      rw [hv', Complex.add_re, Complex.ofReal_re]; linarith [neg_abs_le (τ : ℂ).re]
    have hv2 : 0 < (v * (τ : ℂ)⁻¹).re := by
      have : v * (τ : ℂ)⁻¹ = (‖(τ : ℂ)‖ : ℂ) / τ + 1 := by rw [hv']; field_simp
      rw [this, Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, zero_div, add_zero, Complex.normSq_eq_norm_sq]
      have h1 : ‖(τ : ℂ)‖ * (τ : ℂ).re / ‖(τ : ℂ)‖ ^ 2 = (τ : ℂ).re / ‖(τ : ℂ)‖ := by
        field_simp
      rw [h1]
      have : -1 < (τ : ℂ).re / ‖(τ : ℂ)‖ := by
        rw [lt_div_iff₀ hτn]; linarith [neg_abs_le (τ : ℂ).re]
      linarith
    obtain ⟨r, hr0, hrn, hr1, hr2⟩ := exists_small_re_exp hv1 hv2 hδ0pos
    refine ⟨(r : ℂ) * v, hrn, hr1, ?_⟩
    change 0 < (exp ((r : ℂ) * v / τ) - 1).re
    rwa [div_eq_mul_inv]
  -- inside the cell
  have hUsub : U ⊆ cell τ := by
    intro u hu
    obtain ⟨hn, hr1, hr2⟩ := hu
    have hp1 := re_pos_of_re_exp_sub_one_pos hr1
    have hp2 := re_pos_of_re_exp_sub_one_pos hr2
    have hnu : ‖u‖ < 2 * Real.pi * τ.im :=
      lt_of_lt_of_le hn ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hnu' : ‖u‖ < 2 * Real.pi * (ModularGroup.S • τ).im * ‖(τ : ℂ)‖ :=
      lt_of_lt_of_le hn ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨⟨hp1, lt_of_le_of_lt (Complex.re_le_norm u) hnu⟩, hp2, ?_⟩
    calc (u / τ).re ≤ ‖u / τ‖ := Complex.re_le_norm _
      _ = ‖u‖ / ‖(τ : ℂ)‖ := norm_div _ _
      _ < 2 * Real.pi * (ModularGroup.S • τ).im := by rwa [div_lt_iff₀ hτn]
  refine cell_eqOn (G := fun q => ∑ y, D.repS x y * prodN F H c y ins τ q)
    (G' := prodN F H c x ins (ModularGroup.S • τ)) _
    (DifferentiableOn.fun_sum fun y _ => (prodN_differentiableOn F H hV c y ins τ).const_mul _)
    (prodN_differentiableOn F H hV c x ins _) hUo hUne hUsub ?_
  intro u hu
  obtain ⟨hn, hr1, hr2⟩ := hu
  have hnδ1 : ‖u‖ < δ1 := lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_left _ _))
  have hnδ2 : ‖u / τ‖ < δ2 := by
    rw [norm_div, div_lt_iff₀ hτn]
    exact lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_right _ _))
  have hnδ3 : ∀ y, ‖u‖ < δY y := fun y =>
    lt_of_lt_of_le (lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))) (hδ3le y)
  rw [h2 (u / τ) hnδ2 hr2, h1 u hnδ1 hr1 hr2 x]
  congr 1
  exact Finset.sum_congr rfl fun y _ => by rw [hY y u (hnδ3 y) hr1]

/-- `(−u − 2πiτ)/τ = −u/τ − 2πi`. -/
theorem bpoint_div (τ : UpperHalfPlane) (u : ℂ) :
    (-u - 2 * (Real.pi : ℂ) * I * τ) / τ = -u / τ - 2 * (Real.pi : ℂ) * I := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

/-- `(−u/τ)/(S τ) = u`. -/
theorem div_S (τ : UpperHalfPlane) (u : ℂ) :
    (-u / τ) / ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = u := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [coe_S_smul]
  field_simp

/-- **The germ relation** (Huang Prop. 4.5 at the level of functions): on a small sector,
`e^{2πi h_b} Ω_x Σ_z S_xz vacF(σ z) + e^{2πi h_b} e^{iπκ} τ^{−κ} Σ_k aRem_k(S τ, −u/τ)
 = μ Σ_y S_xy Σ_z B_yz vacF(σ z) + e^{iπκ} Σ_y S_xy Σ_{j,k} bRem_{yjk}(u)`. -/
theorem germ_relation (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    {r : ℕ} (lab : Fin r → ι)
    (i : ∀ k, famObj D (lab k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' (D.h b) Ω)
    {r' : ℕ} (lab' : Fin r' → ι)
    (i' : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
    (p' : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
    (htot' : ∑ k, p' k ≫ i' k = 𝟙 _)
    (hS : VacuumSCovariance F hv c) {σ : ι → ι} (hσ : Function.Bijective σ) {μ : ℂ}
    (hconj : ∀ (ins : Insertion D a b) (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧
      ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ z,
        revF F hv π ins z τ u = μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * vacF F hv c ins (σ z) τ u)
    {T : ι → ι → ℂ} (hTS : ∀ w z, ∑ y, T w y * D.repS y z = if w = z then 1 else 0)
    (hTσ : ∀ y z, T y (σ z) = D.repS y z) (x : ι) (ins : Insertion D a b) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ sector τ δ,
      exp (2 * (Real.pi : ℂ) * I * D.h b) * Ω x * ∑ z, D.repS x z * vacF F hv c ins (σ z) τ u +
        exp (2 * (Real.pi : ℂ) * I * D.h b) * (exp ((Real.pi : ℂ) * I * ins.κ) *
          exp (-(ins.κ * log τ)) * ∑ k, (aRemChannel F H c hη' (D.h b) x lab' i' p' k).eval
            ins (ModularGroup.S • τ) (-u / τ)) =
      μ * ∑ y, D.repS x y * ∑ z, transferMatrix c β y z * vacF F hv c ins (σ z) τ u +
        exp ((Real.pi : ℂ) * I * ins.κ) * ∑ y, D.repS x y *
          ∑ j, ∑ k, (bRemChannel F H c hπ y lab i p j k).eval ins τ u := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hτn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hτ
  have him : 0 < τ.im := τ.im_pos
  have hSim : 0 < (ModularGroup.S • τ).im := (ModularGroup.S • τ).im_pos
  have hcell := cell_identity F H hV hv c hS x ins τ
  have hBy : ∀ y, ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
      prodN F H c y ins τ (-u - 2 * (Real.pi : ℂ) * I * τ) =
        ∑ z, transferMatrix c β y z * revF F hv π ins z τ u +
          ∑ j, ∑ k, (bRemChannel F H c hπ y lab i p j k).eval ins τ u := fun y =>
    prodN_bcorner F H hV hv c hβ hπ lab i p htot y ins τ
  choose δB hδB hB using hBy
  obtain ⟨δB0, hδB0, hδB0le⟩ := exists_pos_le_fintype δB hδB
  obtain ⟨δA, hδA, hA⟩ := prodN_acorner F H hV hv c hη' hΩ lab' i' p' htot' x ins
    (ModularGroup.S • τ)
  obtain ⟨δN, hδN, hN⟩ := hS ins (ModularGroup.S • τ)
  obtain ⟨δC, hδC, hC⟩ := hconj ins τ
  set δ : ℝ := min (min δB0 δC) (min (‖(τ : ℂ)‖ * min δA δN) (min (2 * Real.pi * τ.im)
    (2 * Real.pi * (ModularGroup.S • τ).im * ‖(τ : ℂ)‖))) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (lt_min hδB0 hδC) (lt_min (mul_pos hτn (lt_min hδA hδN))
      (lt_min (by positivity) (by positivity)))
  refine ⟨δ, hδpos, fun u hu => ?_⟩
  obtain ⟨hn, hre, hre'⟩ := hu
  have hnB : ∀ y, ‖u‖ < δB y := fun y =>
    lt_of_lt_of_le (lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_left _ _))) (hδB0le y)
  have hnC : ‖u‖ < δC := lt_of_lt_of_le hn ((min_le_left _ _).trans (min_le_right _ _))
  have hnv : ‖-u / (τ : ℂ)‖ < min δA δN := by
    rw [norm_div, norm_neg, div_lt_iff₀ hτn, mul_comm]
    exact lt_of_lt_of_le hn ((min_le_right _ _).trans (min_le_left _ _))
  have hn1 : ‖u‖ < 2 * Real.pi * τ.im :=
    lt_of_lt_of_le hn ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hn2 : ‖u‖ < 2 * Real.pi * (ModularGroup.S • τ).im * ‖(τ : ℂ)‖ :=
    lt_of_lt_of_le hn ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpu := re_pos_of_re_exp_sub_one_pos hre
  have hpv := re_pos_of_re_exp_sub_one_pos hre'
  -- the B-corner point lies in the cell
  have hmem : (-u - 2 * (Real.pi : ℂ) * I * τ) ∈ cell τ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : (-u - 2 * (Real.pi : ℂ) * I * τ).re = -u.re + 2 * Real.pi * τ.im := by
        simp [Complex.mul_re, Complex.mul_im, UpperHalfPlane.coe_im]
      rw [this]; linarith [Complex.re_le_norm u]
    · have : (-u - 2 * (Real.pi : ℂ) * I * τ).re = -u.re + 2 * Real.pi * τ.im := by
        simp [Complex.mul_re, Complex.mul_im, UpperHalfPlane.coe_im]
      rw [this]; linarith
    · rw [bpoint_div]
      have hre2 : (-u / τ - 2 * (Real.pi : ℂ) * I).re = (-u / τ).re := by simp
      refine ⟨by rw [hre2]; exact hpv, ?_⟩
      rw [hre2]
      calc (-u / τ).re ≤ ‖-u / (τ : ℂ)‖ := Complex.re_le_norm _
        _ = ‖u‖ / ‖(τ : ℂ)‖ := by rw [norm_div, norm_neg]
        _ < 2 * Real.pi * (ModularGroup.S • τ).im := by rwa [div_lt_iff₀ hτn]
  have hc := hcell _ hmem
  rw [bpoint_div, hA (-u / τ) (lt_of_lt_of_le hnv (min_le_left _ _)) hre'] at hc
  simp only [fun y => hB y u (hnB y) hre] at hc
  -- N1 at the base `S τ`, inverted with `T`
  have hN1 : ∀ w, vacF F hv c ins w τ u =
      exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) *
      ∑ y, D.repS w y * vacF F hv c ins y (ModularGroup.S • τ) (-u / τ) := by
    intro w
    have h := hN (-u / τ) (lt_of_lt_of_le hnv (min_le_right _ _)) hre' (by rw [div_S]; exact hre) w
    rwa [S_smul_S_smul, div_S] at h
  have hinv : vacF F hv c ins x (ModularGroup.S • τ) (-u / τ) =
      exp (-(ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ))) *
        ∑ z, D.repS x z * vacF F hv c ins (σ z) τ u := by
    have h1 : ∑ w, T x w * vacF F hv c ins w τ u =
        exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) *
          vacF F hv c ins x (ModularGroup.S • τ) (-u / τ) := by
      calc ∑ w, T x w * vacF F hv c ins w τ u =
            ∑ w, T x w * (exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) *
              ∑ y, D.repS w y * vacF F hv c ins y (ModularGroup.S • τ) (-u / τ)) :=
            Finset.sum_congr rfl fun w _ => by rw [hN1 w]
        _ = ∑ y, exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) *
              (∑ w, T x w * D.repS w y) * vacF F hv c ins y (ModularGroup.S • τ) (-u / τ) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => by ring
        _ = _ := by
            simp only [hTS, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
              Finset.mem_univ, if_true]
    have h2 : ∑ w, T x w * vacF F hv c ins w τ u =
        ∑ z, D.repS x z * vacF F hv c ins (σ z) τ u := by
      rw [← Function.Bijective.sum_comp hσ (fun w => T x w * vacF F hv c ins w τ u)]
      exact Finset.sum_congr rfl fun z _ => by rw [hTσ]
    rw [← h2, h1, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
  -- N2
  have hsum : ∑ y, D.repS x y * (∑ z, transferMatrix c β y z * revF F hv π ins z τ u +
      ∑ j, ∑ k, (bRemChannel F H c hπ y lab i p j k).eval ins τ u) =
      μ * exp (-((Real.pi : ℂ) * I * ins.κ)) *
          ∑ y, D.repS x y * ∑ z, transferMatrix c β y z * vacF F hv c ins (σ z) τ u +
        ∑ y, D.repS x y * ∑ j, ∑ k, (bRemChannel F H c hπ y lab i p j k).eval ins τ u := by
    simp only [fun z => hC u hnC hre z, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  rw [hsum, hinv] at hc
  -- exponentials
  have hLL : log (τ : ℂ) + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
      (Real.pi : ℂ) * I := log_add_log_S τ
  have hP : exp ((Real.pi : ℂ) * I * ins.κ) = exp (ins.κ * log (τ : ℂ)) *
      exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) := by
    rw [← exp_add, ← mul_add, hLL, mul_comm]
  have hPm : exp (-((Real.pi : ℂ) * I * ins.κ)) = (exp (ins.κ * log (τ : ℂ)) *
      exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)))⁻¹ := by
    rw [exp_neg, hP]
  rw [hPm, exp_neg] at hc
  rw [hP, exp_neg]
  have hQ0 : exp (ins.κ * log (τ : ℂ)) ≠ 0 := exp_ne_zero _
  have hQ0' : exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) ≠ 0 := exp_ne_zero _
  generalize exp (ins.κ * log (τ : ℂ)) = Q at hc hQ0 ⊢
  generalize exp (ins.κ * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) = Q' at hc hQ0' ⊢
  field_simp at hc ⊢
  linear_combination hc

/-- The coefficients of the final relation. -/
def relCoef (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ) (σ : ι → ι) (Ω : ι → ℂ)
    (μ : ℂ) (x w : ι) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I * D.h b) * Ω x * D.repS x (σ w) -
    μ * ∑ y, D.repS x y * transferMatrix c β y (σ w)

/-- **The vacuum channels satisfy Huang's relation modulo the non-vacuum span.** -/
theorem relation_mem_Rspan (hV : StronglyRational W) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b)
    {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    {π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject} (hπ : c.η ≫ π = 𝟙 _)
    {r : ℕ} (lab : Fin r → ι)
    (i : ∀ k, famObj D (lab k) ⟶ tensorObj F (famObj D b) (famObj D a))
    (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab k))
    (htot : ∑ k, p k ≫ i k = 𝟙 _)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (hη' : η' ≫ c.ε = 𝟙 _) {Ω : ι → ℂ} (hΩ : IsACycleScalar F H c η' (D.h b) Ω)
    {r' : ℕ} (lab' : Fin r' → ι)
    (i' : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D a) (famObj D b))
    (p' : ∀ k, tensorObj F (famObj D a) (famObj D b) ⟶ famObj D (lab' k))
    (htot' : ∑ k, p' k ≫ i' k = 𝟙 _)
    (hS : VacuumSCovariance F hv c) {σ : ι → ι} (hσσ : ∀ x, σ (σ x) = x) {μ : ℂ}
    (hconj : ∀ (ins : Insertion D a b) (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧
      ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ z,
        revF F hv π ins z τ u = μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * vacF F hv c ins (σ z) τ u)
    (hstab : ChannelSStability F η' c.η)
    {T : ι → ι → ℂ} (hTS : ∀ w z, ∑ y, T w y * D.repS y z = if w = z then 1 else 0)
    (hTσ : ∀ y z, T y (σ z) = D.repS y z) (x : ι) :
    (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
      ∑ w, relCoef F c β σ Ω μ x w * vacF F hv c ins w τ u) ∈ Rspan η' c.η := by
  have hσ : Function.Bijective σ := Function.Involutive.bijective hσσ
  set e : ℂ := exp (2 * (Real.pi : ℂ) * I * D.h b) with he
  -- the B part
  set Bpart : FunSpace D a b := fun ins τ u => ∑ y, D.repS x y * ∑ j, ∑ k,
    exp ((Real.pi : ℂ) * I * ins.κ) * (bRemChannel F H c hπ y lab i p j k).eval ins τ u
    with hBpart
  have hBmem : Bpart ∈ Rspan η' c.η := by
    have hgen : ∀ y j k, (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
        exp ((Real.pi : ℂ) * I * ins.κ) * (bRemChannel F H c hπ y lab i p j k).eval ins τ u) ∈
        Rspan η' c.η := fun y j k =>
      Submodule.mem_sup_left (Submodule.subset_span (Set.mem_union_right _
        ⟨bRemChannel F H c hπ y lab i p j k, rfl⟩))
    have heq : Bpart = ∑ y, D.repS x y • ∑ j, ∑ k,
        (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
          exp ((Real.pi : ℂ) * I * ins.κ) * (bRemChannel F H c hπ y lab i p j k).eval ins τ u) := by
      funext ins τ u
      simp only [hBpart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => hgen y j k)
  -- the A part
  set Apart : FunSpace D a b := fun ins τ u => e * ∑ k, (exp ((Real.pi : ℂ) * I * ins.κ) *
    exp (-(ins.κ * log τ)) * (aRemChannel F H c hη' (D.h b) x lab' i' p' k).eval ins
      (ModularGroup.S • τ) (-u / τ)) with hApart
  have hAmem : Apart ∈ Rspan η' c.η := by
    have heq : Apart = e • ∑ k, (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
        exp ((Real.pi : ℂ) * I * ins.κ) * exp (-(ins.κ * log τ)) *
          (aRemChannel F H c hη' (D.h b) x lab' i' p' k).eval ins (ModularGroup.S • τ)
            (-u / τ)) := by
      funext ins τ u
      simp only [hApart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => hstab _)
  -- the germ part
  set g : FunSpace D a b := fun ins τ u => ∑ w, relCoef F c β σ Ω μ x w * vacF F hv c ins w τ u
    with hg
  have hZ : g - Bpart + Apart ∈ germZero D a b := by
    intro ins τ
    obtain ⟨δ, hδ, h⟩ := germ_relation F H hV hv c hβ hπ lab i p htot hη' hΩ lab' i' p' htot'
      hS hσ hconj hTS hTσ x ins τ
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have hrel := h u hu
    have hgv : g ins τ u = e * Ω x * ∑ z, D.repS x z * vacF F hv c ins (σ z) τ u -
        μ * ∑ y, D.repS x y * ∑ z, transferMatrix c β y z * vacF F hv c ins (σ z) τ u := by
      simp only [hg]
      rw [← Function.Bijective.sum_comp hσ (fun w => relCoef F c β σ Ω μ x w *
        vacF F hv c ins w τ u)]
      simp only [relCoef, hσσ, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      · simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
    have hBv : Bpart ins τ u = exp ((Real.pi : ℂ) * I * ins.κ) * ∑ y, D.repS x y *
        ∑ j, ∑ k, (bRemChannel F H c hπ y lab i p j k).eval ins τ u := by
      simp only [hBpart, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => by ring
    have hAv : Apart ins τ u = e * (exp ((Real.pi : ℂ) * I * ins.κ) * exp (-(ins.κ * log τ)) *
        ∑ k, (aRemChannel F H c hη' (D.h b) x lab' i' p' k).eval ins (ModularGroup.S • τ)
          (-u / τ)) := by
      simp only [hApart, Finset.mul_sum]
    change g ins τ u - Bpart ins τ u + Apart ins τ u = 0
    rw [hgv, hBv, hAv]
    linear_combination hrel
  have hsplit : g = (g - Bpart + Apart) + Bpart - Apart := by abel
  change g ∈ Rspan η' c.η
  rw [hsplit]
  exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.mem_sup_right hZ) hBmem) hAmem

/-- **(G1) for one instance, from the four named inputs.** -/
theorem vacuumChannelTransport_of_inputs (hNice : Nice W) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (c : TransferChoice F D a b) {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
    (hS : ∀ hv : W.vacuum ≠ 0, VacuumSCovariance F hv c)
    (hconj : ∀ (hv : W.vacuum ≠ 0) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject),
      c.η ≫ π = 𝟙 _ → ∀ σ : ι → ι, (∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) →
        ConjugationInput F hv c π σ)
    (hstab : ∀ η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b),
      η' ≫ c.ε = 𝟙 _ → ChannelSStability F η' c.η)
    (hind : ∀ (hv : W.vacuum ≠ 0)
      (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)),
      η' ≫ c.ε = 𝟙 _ → ChannelIndependence F hv c η') :
    ∃ Ω : ι → ℂ, Ω v0 ≠ 0 ∧
      ∀ x z, ∑ y, D.repS x y * transferMatrix c β y z = Ω x * D.repS x z := by
  have hV : StronglyRational W := hNice.1
  have hv : W.vacuum ≠ 0 := hV.toStronglyFinite.vacuum_ne_zero
  -- charge conjugation and the inverse of `S`
  obtain ⟨σ, T, hσσ, hTS, -, hTσ, hdual, -⟩ :=
    rho_setup VerlindeRho.rhoNegOneInput_pbw hNice D hZ hirr hcomp v0 hv0
  obtain ⟨σ₂, hP₂, hdual₂⟩ := VerlindeVacuum.chargeConjugationInput_of_rhoNegOne
    VerlindeRho.rhoNegOneInput_pbw 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hσeq : σ₂ = σ := by
    funext x
    have h1 := hdual x (σ₂ x)
    rw [hdual₂ x (σ₂ x), if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  have hP : ∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0 := by rw [← hσeq]; exact hP₂
  have hTS' : ∀ w z, ∑ y, T w y * D.repS y z = if w = z then 1 else 0 := by
    intro w z
    have := congrFun (congrFun hTS w) z
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.of_apply] using this
  -- the genus-zero choices
  obtain ⟨π, hπ⟩ := exists_vacuumRetraction F hNice hcomp v0 hv0 c.η c.η_ne
  obtain ⟨r, lab, i, p, htot⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D b) (famObj D a))
  obtain ⟨η', hη'⟩ := exists_vacuumSection F hNice hcomp v0 hv0 c.ε c.ε_ne
  obtain ⟨r', lab', i', p', htot'⟩ :=
    exists_split hNice.1 D hcomp (tensorObj F (famObj D a) (famObj D b))
  obtain ⟨Ω, hΩ⟩ := exists_aCycleScalar F H c η' (D.h b)
  have hΩ0 : Ω v0 ≠ 0 := aCycleScalar_vacuum_ne_zero F H hirr v0 hv0 c hη' hΩ
  obtain ⟨μ, hμ, hconj'⟩ := hconj hv π hπ σ hP
  -- the relation and independence
  have hrel : ∀ x, relCoef F c β σ Ω μ x = 0 := fun x =>
    hind hv η' hη' _ (relation_mem_Rspan F H hV hv c hβ hπ lab i p htot hη' hΩ lab' i' p' htot'
      (hS hv) hσσ hconj' (hstab η' hη') hTS' hTσ x)
  set e : ℂ := exp (2 * (Real.pi : ℂ) * I * D.h b) with he
  have he0 : e ≠ 0 := exp_ne_zero _
  refine ⟨fun x => e * Ω x / μ, div_ne_zero (mul_ne_zero he0 hΩ0) hμ, fun x z => ?_⟩
  have h := congrFun (hrel x) (σ z)
  simp only [relCoef, hσσ, Pi.zero_apply] at h
  field_simp
  linear_combination -h

end Chain

/-! ## §2 The global inputs and the headline -/

/-- (N1) for every instance. -/
def VacuumSCovarianceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0),
        VacuumSCovariance F hv c

/-- (N2) for every instance. -/
def ConjugationInputAll : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
        (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject), c.η ≫ π = 𝟙 _ →
        ∀ σ : ι → ι, (∀ x y, D.rep (-1) x y = if y = σ x then 1 else 0) →
          ConjugationInput F hv c π σ

/-- (N3) for every instance. -/
def ChannelSStabilityInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b)
        (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)),
        η' ≫ c.ε = 𝟙 _ → ChannelSStability F η' c.η

/-- (N4) for every instance (Huang Prop. 2.11). -/
def ChannelIndependenceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (F : FusionChoice W) (a b : ι) (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
        (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)),
        η' ≫ c.ε = 𝟙 _ → ChannelIndependence F hv c η'

/-- **(G1) from the four named genus-one inputs.** The B-cycle/A-cycle transports, the
continuation across the period cell, `Ω_{v0} ≠ 0` and all convergence are proved; the inputs are
(N1) near-collision S-covariance, (N2) the conjugation identity, (N3) S-stability of the
non-vacuum span, (N4) Huang's Prop. 2.11. -/
theorem vacuumChannelTransportInput_of_genusOneInputs
    (h1 : VacuumSCovarianceInput.{u, w}) (h2 : ConjugationInputAll.{u, w})
    (h3 : ChannelSStabilityInput.{u, w}) (h4 : ChannelIndependenceInput.{u, w}) :
    VacuumChannelTransportInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c β hβ
  exact vacuumChannelTransport_of_inputs F H hNice hZ hirr hcomp v0 hv0 c hβ
    (fun hv => h1 𝒱 W hNice ι D hZ hirr hcomp F a b c hv)
    (fun hv π hπ σ hP => h2 𝒱 W hNice ι D hZ hirr hcomp F a b c hv π hπ σ hP)
    (fun η' hη' => h3 𝒱 W hNice ι D hZ hirr hcomp F a b c η' hη')
    (fun hv η' hη' => h4 𝒱 W hNice ι D hZ hirr hcomp F a b c hv η' hη')

/-- **Huang's Theorem 5.2 (`FusionEigenInput`) from the four named genus-one inputs.** -/
theorem fusionEigenInput_of_genusOneInputs
    (h1 : VacuumSCovarianceInput.{u, w}) (h2 : ConjugationInputAll.{u, w})
    (h3 : ChannelSStabilityInput.{u, w}) (h4 : ChannelIndependenceInput.{u, w}) :
    VerlindeEigen.FusionEigenInput.{u, w} :=
  fusionEigenInput_of_genusOne (vacuumChannelTransportInput_of_genusOneInputs h1 h2 h3 h4)

end VOA.Huang.GenusOneG1d
