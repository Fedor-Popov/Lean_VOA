/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGammaZeroCosets
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# From `Γ₁(M)` to `Γ₀(M)`: the bridge `ConwayNortonGammaOne → CompletelyReplicable → ConwayNorton`

Blueprint: the `Γ₀` upgrade argument of `Notes/moonshine/MOON_MONSTER.md`, from the asymptotic
comparison to the bridge.

* `affine_eq_of_normalized` (asymptotic comparison): two normalised functions with
  `f (a τ + b) = f′ τ + c`, `a > 0`, force `a = 1`, `b ∈ ℤ`, `c = 0`.
* `replicate_eq_and_diamond_mem`: in the `Γ₁` setting with replication at a prime `p > M`,
  the replicate equals `f` and `σ_p ∈ Γ` or `-σ_p ∈ Γ`.
* `gamma0_le_adjoinNegOne_of_replicable`: Dirichlet's theorem then gives `Γ₀(M) ≤ ±Γ`;
  `IsNormalizedHauptmodul.adjoinNegOne` transfers the Hauptmodul property to `±Γ`.
* `conwayNorton_of_gammaOne`: the headline bridge.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology CongruenceSubgroup Matrix Matrix.SpecialLinearGroup AutMonster
open scoped MatrixGroups Manifold

/-! ### The `q`-parameter -/

lemma norm_inv_qPar (τ : ℍ) : ‖(qPar τ)⁻¹‖ = Real.exp (2 * Real.pi * τ.im) := by
  rw [norm_inv, qPar, Function.Periodic.norm_qParam, div_one, ← Real.exp_neg,
    UpperHalfPlane.coe_im]
  congr 1
  ring

lemma tendsto_norm_inv_qPar_atTop :
    Tendsto (fun τ : ℍ => ‖(qPar τ)⁻¹‖) atImInfty atTop := by
  simp only [norm_inv_qPar]
  exact Real.tendsto_exp_atTop.comp
    ((tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop).const_mul_atTop
      (by positivity))

lemma qPar_glUpperUnipotent_one (τ : ℍ) : qPar (glUpperUnipotent 1 • τ) = qPar τ := by
  simp only [qPar, Function.Periodic.qParam, coe_glUpperUnipotent_smul, Complex.ofReal_one,
    div_one, mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I]

/-- McKay–Thompson series are `1`-periodic. -/
lemma mckayThompsonFun_periodic (g : AutVnat) (τ : ℍ) :
    mckayThompsonFun g (glUpperUnipotent 1 • τ) = mckayThompsonFun g τ := by
  simp only [mckayThompsonFun, qPar_glUpperUnipotent_one]

/-! ### Asymptotic comparison -/

lemma abs_sub_le_abs_exp_sub_exp {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u - v| ≤ |Real.exp u - Real.exp v| := by
  rcases le_total v u with h | h
  · have e1 : u - v + 1 ≤ Real.exp (u - v) := Real.add_one_le_exp _
    have e2 : 1 ≤ Real.exp v := Real.one_le_exp hv
    have e3 : Real.exp u = Real.exp (u - v) * Real.exp v := by
      rw [← Real.exp_add, sub_add_cancel]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by rw [e3]; nlinarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr e2) (show 0 ≤ Real.exp (u - v) - 1 by linarith)]
  · have e1 : v - u + 1 ≤ Real.exp (v - u) := Real.add_one_le_exp _
    have e2 : 1 ≤ Real.exp u := Real.one_le_exp hu
    have e3 : Real.exp v = Real.exp (v - u) * Real.exp u := by
      rw [← Real.exp_add, sub_add_cancel]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by rw [e3]; nlinarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr e2) (show 0 ≤ Real.exp (v - u) - 1 by linarith)]

/-- **Asymptotic comparison.** If `f` and `f′` are normalised (`f - q⁻¹ → 0` at `i∞`) and
`f (a τ + b) = f′ τ + c` with `a > 0`, then `a = 1`, `b ∈ ℤ` and `c = 0`. -/
theorem affine_eq_of_normalized {f f' : ℍ → ℂ}
    (hf : Tendsto (fun τ : ℍ => f τ - (qPar τ)⁻¹) atImInfty (𝓝 0))
    (hf' : Tendsto (fun τ : ℍ => f' τ - (qPar τ)⁻¹) atImInfty (𝓝 0))
    {φ : ℍ → ℍ} {a b : ℝ} (ha : 0 < a) (hφ : ∀ τ : ℍ, (φ τ : ℂ) = a * τ + b) {c : ℂ}
    (heq : ∀ τ : ℍ, f (φ τ) = f' τ + c) :
    a = 1 ∧ (∃ k : ℤ, b = k) ∧ c = 0 := by
  have hφim : ∀ τ : ℍ, (φ τ).im = a * τ.im := by
    intro τ
    have := congrArg Complex.im (hφ τ)
    simpa using this
  have himlim : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hφlim : Tendsto φ atImInfty atImInfty := by
    refine tendsto_comap_iff.mpr ?_
    have : (UpperHalfPlane.im ∘ φ) = fun τ => a * τ.im := funext hφim
    rw [this]
    exact himlim.const_mul_atTop ha
  set E : ℍ → ℂ := fun τ => (qPar (φ τ))⁻¹ - (qPar τ)⁻¹ with hEdef
  have hE : Tendsto E atImInfty (𝓝 c) := by
    have := (((hf.comp hφlim).neg.add hf').add_const c)
    simp only [neg_zero, add_zero, zero_add] at this
    refine this.congr fun τ => ?_
    simp only [Function.comp_apply, hEdef, heq τ]
    ring
  have hEnorm : ¬ Tendsto (fun τ => ‖E τ‖) atImInfty atTop := fun h =>
    not_tendsto_nhds_of_tendsto_atTop h _ hE.norm
  -- `a = 1`
  have ha1 : a = 1 := by
    by_contra ha1
    apply hEnorm
    have hpos : 0 < 2 * Real.pi * |a - 1| := by
      have : 0 < |a - 1| := abs_pos.mpr (sub_ne_zero.mpr ha1)
      positivity
    refine tendsto_atTop_mono (fun τ => ?_) (himlim.const_mul_atTop hpos)
    have h1 : |‖(qPar (φ τ))⁻¹‖ - ‖(qPar τ)⁻¹‖| ≤ ‖E τ‖ := abs_norm_sub_norm_le _ _
    rw [norm_inv_qPar, norm_inv_qPar, hφim] at h1
    have h2 := abs_sub_le_abs_exp_sub_exp (u := 2 * Real.pi * (a * τ.im))
      (v := 2 * Real.pi * τ.im) (by have := τ.im_pos; positivity) (by have := τ.im_pos; positivity)
    have h3 : |2 * Real.pi * (a * τ.im) - 2 * Real.pi * τ.im| = 2 * Real.pi * |a - 1| * τ.im := by
      rw [show 2 * Real.pi * (a * τ.im) - 2 * Real.pi * τ.im = (2 * Real.pi * τ.im) * (a - 1) by
          ring, abs_mul, abs_of_pos (by have := τ.im_pos; positivity)]
      ring
    linarith
  subst ha1
  -- the phase `ω = e^{2πib}`
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * b) with hωdef
  have hqφ : ∀ τ : ℍ, qPar (φ τ) = qPar τ * ω := by
    intro τ
    simp only [qPar, Function.Periodic.qParam, hφ τ, Complex.ofReal_one, one_mul, div_one,
      mul_add, Complex.exp_add, hωdef]
  have hEω : ∀ τ : ℍ, E τ = (qPar τ)⁻¹ * (ω⁻¹ - 1) := by
    intro τ
    simp only [hEdef, hqφ τ, mul_inv]
    ring
  by_cases hω : ω = 1
  · refine ⟨rfl, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hω
      refine ⟨k, ?_⟩
      have h2 : (b : ℂ) * (2 * Real.pi * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [← hk]
        ring
      have := mul_right_cancel₀ Complex.two_pi_I_ne_zero h2
      exact_mod_cast this
    · have hE0 : Tendsto E atImInfty (𝓝 0) := by
        refine tendsto_const_nhds.congr fun τ => ?_
        rw [hEω, hω, inv_one, sub_self, mul_zero]
      exact tendsto_nhds_unique hE hE0
  · exfalso
    apply hEnorm
    have hpos : 0 < ‖ω⁻¹ - 1‖ := by
      refine norm_pos_iff.mpr fun h => hω ?_
      rw [sub_eq_zero, inv_eq_one] at h
      exact h
    refine (tendsto_norm_inv_qPar_atTop.atTop_mul_const hpos).congr fun τ => ?_
    rw [hEω, norm_mul]

/-! ### The diamond lift lies in `±Γ` -/

/-- **The replicate equals the Hauptmodul, and `σ_p ∈ ±Γ`.** Let `f` be a normalised Hauptmodul of
`Γ ⊇ Γ₁(M)` (`Γ ≤ SL₂(ℝ)`), `p > M` a prime, `m p - n M = 1`, and `f′` a holomorphic, `1`-periodic,
normalised function with `Φ (f τ) = Σ_{j<p} f ((τ + j)/p) + f′ (p τ)`. Then `f′ = f`, and
`σ = (m n; M p)` or `-σ` lies in `Γ`. -/
theorem replicate_eq_and_diamond_mem {Γ : Subgroup (GL (Fin 2) ℝ)} {f f' : ℍ → ℂ}
    {Φ : ℂ → ℂ} {M p : ℕ} (hH : IsNormalizedHauptmodul Γ f) (hdet : Γ.HasDetOne)
    (hΓ1 : gamma1GL M ≤ Γ) (hM : 0 < M) (hp : p.Prime) (hMp : M < p) {m n : ℤ}
    (hmn : m * p - n * M = 1) (hf'hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f')
    (hf'per : ∀ τ : ℍ, f' (glUpperUnipotent 1 • τ) = f' τ)
    (hf'norm : Tendsto (fun τ : ℍ => f' τ - (qPar τ)⁻¹) atImInfty (𝓝 0))
    (hrep : ∀ τ : ℍ, Φ (f τ) = ∑ j ∈ Finset.range p, f (heckePoint 1 p j one_pos hp.pos τ) +
      f' (heckePoint p 1 0 hp.pos one_pos τ)) :
    f' = f ∧ (mapGL ℝ (diamondLift M p m n hmn) ∈ Γ ∨ -mapGL ℝ (diamondLift M p m n hmn) ∈ Γ) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hf : ∀ γ ∈ Gamma1 M, ∀ τ : ℍ, f (mapGL ℝ γ • τ) = f τ := fun γ hγ τ =>
    hH.invariant _ (hΓ1 (Subgroup.mem_map_of_mem _ hγ)) τ
  obtain ⟨c, hc⟩ :=
    diamond_eq_replicate_add_const hM hp hMp hmn hH.holomorphic hf hf'hol hf'per hrep
  set σ := mapGL ℝ (diamondLift M p m n hmn) with hσdef
  -- `σ ∞` is `Γ`-equivalent to `∞`
  have horbit : ∃ γ ∈ Γ, γ • cuspInfty = σ • cuspInfty := by
    by_contra! hne
    have hcusp : IsCusp (σ • cuspInfty) Γ := by
      have h0 : IsCusp (σ • cuspInfty) 𝒮ℒ := isCusp_SL2Z_iff'.mpr ⟨_, rfl⟩
      exact ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (gamma1GL M)).mpr h0).mono hΓ1
    obtain ⟨w, hw⟩ := hH.cuspFinite _ ⟨hcusp, hne⟩
    have hlim := hw σ ⟨by simp [σ], rfl⟩
    have hq : Tendsto (fun τ : ℍ => (qPar τ)⁻¹) atImInfty (𝓝 (w - c - 0)) := by
      refine ((hlim.sub_const c).sub hf'norm).congr fun τ => ?_
      simp only [hc]
      ring
    exact not_tendsto_nhds_of_tendsto_atTop tendsto_norm_inv_qPar_atTop _ hq.norm
  obtain ⟨γ, hγ, hγσ⟩ := horbit
  -- `δ = γ⁻¹ σ` fixes `∞`
  set δ := γ⁻¹ * σ with hδdef
  have hδinf : δ • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty := by
    rw [hδdef, mul_smul, ← hγσ, inv_smul_smul]
  have hδ10 : δ 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hδinf
  have hδdet : δ.det = 1 := by
    rw [hδdef, map_mul, map_inv, Subgroup.HasDetOne.det_eq hγ, hσdef, det_mapGL, inv_one,
      one_mul]
  have hδdet' : δ 0 0 * δ 1 1 = 1 := by
    have := congrArg Units.val hδdet
    rw [GeneralLinearGroup.val_det_apply, det_fin_two, hδ10, mul_zero, sub_zero] at this
    simpa using this
  have hσγδ : σ = γ * δ := by rw [hδdef, mul_inv_cancel_left]
  have hfσ : ∀ τ : ℍ, f (σ • τ) = f (δ • τ) := fun τ => by
    rw [hσγδ, mul_smul, hH.invariant γ hγ]
  have h00 : δ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hδdet'
  have h11 : δ 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hδdet'
  have hδpos : 0 < δ.det.val := by rw [hδdet, Units.val_one]; exact one_pos
  have hδact : ∀ τ : ℍ,
      ((δ • τ : ℍ) : ℂ) = ((δ 0 0 ^ 2 : ℝ) : ℂ) * τ + ((δ 0 0 * δ 0 1 : ℝ) : ℂ) := by
    intro τ
    rw [coe_smul_of_det_pos hδpos]
    simp only [num, denom, hδ10, Complex.ofReal_zero, zero_mul, zero_add]
    rw [div_eq_iff (Complex.ofReal_ne_zero.mpr h11)]
    have hC : ((δ 0 0 : ℝ) : ℂ) * (δ 1 1 : ℂ) = 1 := by exact_mod_cast hδdet'
    push_cast
    linear_combination (-(((δ 0 0 : ℝ) : ℂ) * τ + (δ 0 1 : ℂ))) * hC
  have hsq : 0 < δ 0 0 ^ 2 := by positivity
  obtain ⟨ha1, ⟨k, hk⟩, hc0⟩ := affine_eq_of_normalized hH.normalized hf'norm hsq hδact
    (fun τ => (hfσ τ).symm.trans (hc τ))
  have h11eq : δ 1 1 = δ 0 0 := by linear_combination (-δ 1 1) * ha1 + δ 0 0 * hδdet'
  have h01eq : δ 0 1 = δ 0 0 * k := by linear_combination (-δ 0 1) * ha1 + δ 0 0 * hk
  have hpm : δ 0 0 = 1 ∨ δ 0 0 = -1 := by
    have : (δ 0 0 - 1) * (δ 0 0 + 1) = 0 := by linear_combination ha1
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hTmem : mapGL ℝ (upperSL k) ∈ Γ := hΓ1 (Subgroup.mem_map_of_mem _ (upperSL_mem_Gamma1 M k))
  have hfT : ∀ τ : ℍ, f (mapGL ℝ (upperSL k) • τ) = f τ := hf _ (upperSL_mem_Gamma1 M k)
  rcases hpm with h1 | h1
  · have hδT : δ = mapGL ℝ (upperSL k) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperSL, h1, h11eq, h01eq, hδ10]
    refine ⟨funext fun τ => ?_, Or.inl ?_⟩
    · have := hc τ
      rw [hfσ, hδT, hfT, hc0, add_zero] at this
      exact this.symm
    · rw [hσγδ, hδT]
      exact Γ.mul_mem hγ hTmem
  · have hδT : δ = -mapGL ℝ (upperSL k) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperSL, h1, h11eq, h01eq, hδ10]
    refine ⟨funext fun τ => ?_, Or.inr ?_⟩
    · have := hc τ
      rw [hfσ, hδT, UpperHalfPlane.neg_smul, hfT, hc0, add_zero] at this
      exact this.symm
    · rw [hσγδ, hδT, mul_neg, neg_neg]
      exact Γ.mul_mem hγ hTmem

/-! ### `Γ₀(M) ≤ ±Γ` -/

/-- The replication hypothesis at a prime `p`, for a fixed `f` and replicate `f′`. -/
def ReplicatesAtPrime (f f' : ℍ → ℂ) (p : ℕ) (hp : p.Prime) : Prop :=
  ∃ Φ : ℂ → ℂ, ∀ τ : ℍ, Φ (f τ) = ∑ j ∈ Finset.range p, f (heckePoint 1 p j one_pos hp.pos τ) +
    f' (heckePoint p 1 0 hp.pos one_pos τ)

/-- **`Γ₀(M) ≤ ±Γ`** (Dirichlet's theorem on primes in progressions). -/
theorem gamma0_le_adjoinNegOne_of_replicable {Γ : Subgroup (GL (Fin 2) ℝ)} {f : ℍ → ℂ} {M : ℕ}
    (hH : IsNormalizedHauptmodul Γ f) (hdet : Γ.HasDetOne) (hΓ1 : gamma1GL M ≤ Γ) (hM : 0 < M)
    (hrep : ∀ (p : ℕ) (hp : p.Prime), M < p → ∃ f' : ℍ → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f' ∧ (∀ τ : ℍ, f' (glUpperUnipotent 1 • τ) = f' τ) ∧
      Tendsto (fun τ : ℍ => f' τ - (qPar τ)⁻¹) atImInfty (𝓝 0) ∧ ReplicatesAtPrime f f' p hp) :
    gamma0GL M ≤ Γ.adjoinNegOne := by
  haveI : NeZero M := ⟨hM.ne'⟩
  intro x hx
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hx
  have hc0 : ((δ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hδ
  have hδdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := δ.prop
    rwa [det_fin_two] at this
  have hdM : ((δ 0 0 : ℤ) : ZMod M) * ((δ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod M) hδdet
    push_cast at this
    rwa [hc0, mul_zero, sub_zero] at this
  have hunit : IsUnit ((δ 1 1 : ℤ) : ZMod M) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hdM)
  obtain ⟨p, hMp, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit M
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr
    (Nat.not_dvd_of_pos_of_lt hM hMp)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hmn : u * p - (-v) * M = 1 := by linear_combination huv
  obtain ⟨f', hf'hol, hf'per, hf'norm, Φ, hΦ⟩ := hrep p hp hMp
  obtain ⟨-, hσ⟩ := replicate_eq_and_diamond_mem hH hdet hΓ1 hM hp hMp hmn hf'hol hf'per hf'norm hΦ
  -- `δ = ε σ` with `ε ∈ Γ₁(M)`
  set a := δ 0 0
  set b := δ 0 1
  set c := δ 1 0
  set d := δ 1 1
  have hεdet : (a * p - b * M) * (d * u - c * (-v)) - (b * u - a * (-v)) * (c * p - d * M) = 1 := by
    linear_combination (u * p - (-v) * M) * hδdet + hmn
  have hmM : (u : ZMod M) * p = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod M) hmn
    push_cast at this
    rwa [ZMod.natCast_self, mul_zero, sub_zero] at this
  have hε : slOfDetOne (a * p - b * M) (b * u - a * (-v)) (c * p - d * M) (d * u - c * (-v)) hεdet
      ∈ Gamma1 M := by
    refine slOfDetOne_mem_Gamma1 _ ?_ ?_ ?_
    · push_cast
      rw [ZMod.natCast_self, mul_zero, sub_zero, hpd]
      exact hdM
    · push_cast
      rw [hc0, zero_mul, sub_zero, ← hpd, mul_comm]
      exact hmM
    · push_cast
      rw [hc0, ZMod.natCast_self, zero_mul, mul_zero, sub_zero]
  have hεσ : slOfDetOne (a * p - b * M) (b * u - a * (-v)) (c * p - d * M) (d * u - c * (-v))
      hεdet * diamondLift M p u (-v) hmn = δ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diamondLift, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination a * hmn
    · linear_combination b * hmn
    · linear_combination c * hmn
    · linear_combination d * hmn
  have hεmem : mapGL ℝ (slOfDetOne (a * p - b * M) (b * u - a * (-v)) (c * p - d * M)
      (d * u - c * (-v)) hεdet) ∈ Γ := hΓ1 (Subgroup.mem_map_of_mem _ hε)
  rw [Subgroup.mem_adjoinNegOne_iff, ← hεσ, map_mul]
  rcases hσ with hσ | hσ
  · exact Or.inl (Γ.mul_mem hεmem hσ)
  · exact Or.inr (by rw [← mul_neg]; exact Γ.mul_mem hεmem hσ)

/-! ### Transfer to `±Γ` -/

lemma neg_smul_cuspInfty (g : GL (Fin 2) ℝ) : (-g) • cuspInfty = g • cuspInfty := by
  simp only [cuspInfty, OnePoint.smul_infty_eq_ite, Units.val_neg, Matrix.neg_apply, neg_eq_zero,
    neg_div_neg_eq]

lemma isOtherCusp_adjoinNegOne_iff {Γ : Subgroup (GL (Fin 2) ℝ)} {c : OnePoint ℝ} :
    IsOtherCusp Γ.adjoinNegOne c ↔ IsOtherCusp Γ c := by
  unfold IsOtherCusp
  rw [(Γ.commensurable_adjoinNegOne_self).isCusp_iff]
  refine and_congr_right fun _ => ⟨fun h γ hγ => h γ (Γ.le_adjoinNegOne hγ), fun h γ hγ => ?_⟩
  rcases hγ with hγ | hγ
  · exact h γ hγ
  · rw [← neg_smul_cuspInfty]
    exact h _ hγ

/-- The normalised Hauptmodul property passes from `Γ` to `±Γ = Γ ∪ -Γ`. -/
theorem IsNormalizedHauptmodul.adjoinNegOne {Γ : Subgroup (GL (Fin 2) ℝ)} {f : ℍ → ℂ}
    (hH : IsNormalizedHauptmodul Γ f) : IsNormalizedHauptmodul Γ.adjoinNegOne f where
  holomorphic := hH.holomorphic
  invariant γ hγ τ := by
    rcases hγ with hγ | hγ
    · exact hH.invariant γ hγ τ
    · rw [← UpperHalfPlane.neg_smul]
      exact hH.invariant _ hγ τ
  normalized := hH.normalized
  cuspFinite c hc := hH.cuspFinite c (isOtherCusp_adjoinNegOne_iff.mp hc)
  injective τ σ h := by
    obtain ⟨γ, hγ, h⟩ := hH.injective τ σ h
    exact ⟨γ, Γ.le_adjoinNegOne hγ, h⟩
  cuspValue_not_attained c w hc := hH.cuspValue_not_attained c w
    (isOtherCusp_adjoinNegOne_iff.mp hc)
  cuspValue_injective c c' w hc hc' hw hw' := by
    obtain ⟨γ, hγ, h⟩ := hH.cuspValue_injective c c' w (isOtherCusp_adjoinNegOne_iff.mp hc)
      (isOtherCusp_adjoinNegOne_iff.mp hc') hw hw'
    exact ⟨γ, Γ.le_adjoinNegOne hγ, h⟩
  surjective w := by
    rcases hH.surjective w with h | ⟨c, hc, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, isOtherCusp_adjoinNegOne_iff.mpr hc, hw⟩

lemma hasDetOne_adjoinNegOne {Γ : Subgroup (GL (Fin 2) ℝ)} (hdet : Γ.HasDetOne) :
    Γ.adjoinNegOne.HasDetOne :=
  (Subgroup.hasDetOne_adjoinNegOne_iff (by simp)).mpr hdet

/-- **`Γ₀` from `Γ₁` and replication.** The `Γ₁` data plus replication at every prime `p > M`
(each with a holomorphic, `1`-periodic, normalised replicate) give a moonshine group
`±Γ ⊇ Γ₀(M)` for `f`. -/
theorem isMoonshineGroup_adjoinNegOne_of_replicable {Γ : Subgroup (GL (Fin 2) ℝ)} {f : ℍ → ℂ}
    {M : ℕ} (hH : IsNormalizedHauptmodul Γ f) (hdet : Γ.HasDetOne) (hΓ1 : gamma1GL M ≤ Γ)
    (hM : 0 < M) (hcomm : Subgroup.Commensurable Γ 𝒮ℒ)
    (hrep : ∀ (p : ℕ) (hp : p.Prime), M < p → ∃ f' : ℍ → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f' ∧ (∀ τ : ℍ, f' (glUpperUnipotent 1 • τ) = f' τ) ∧
      Tendsto (fun τ : ℍ => f' τ - (qPar τ)⁻¹) atImInfty (𝓝 0) ∧ ReplicatesAtPrime f f' p hp) :
    IsMoonshineGroup Γ.adjoinNegOne M ∧ IsNormalizedHauptmodul Γ.adjoinNegOne f :=
  ⟨⟨hM, hasDetOne_adjoinNegOne hdet, gamma0_le_adjoinNegOne_of_replicable hH hdet hΓ1 hM hrep,
    (Γ.commensurable_adjoinNegOne_self).trans hcomm⟩, hH.adjoinNegOne⟩

/-! ### Replication at a prime, from `CompletelyReplicable` -/

/-- `heckePoint` without proof arguments (`τ` outside the positive range). -/
noncomputable def heckePointAux (a d b : ℕ) (τ : ℍ) : ℍ :=
  if h : 0 < a ∧ 0 < d then heckePoint a d b h.1 h.2 τ else τ

lemma heckePointAux_eq {a d : ℕ} (b : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    heckePointAux a d b τ = heckePoint a d b ha hd τ :=
  dif_pos ⟨ha, hd⟩

/-- At a prime `m = p` the replicate Hecke sum has two blocks: `a = 1` and `a = p`. -/
lemma heckeSum_prime (F : ℕ → ℍ → ℂ) {p : ℕ} (hp : p.Prime) (τ : ℍ) :
    ∑ a ∈ p.divisors.attach, ∑ b ∈ Finset.range (p / a),
        F a (heckePoint a (p / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) =
      ∑ j ∈ Finset.range p, F 1 (heckePoint 1 p j one_pos hp.pos τ) +
        F p (heckePoint p 1 0 hp.pos one_pos τ) := by
  have hsum : ∀ a ∈ p.divisors.attach, ∑ b ∈ Finset.range (p / a),
      F a (heckePoint a (p / a) b (Nat.pos_of_mem_divisors a.2)
        (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ) =
      (fun k : ℕ => ∑ b ∈ Finset.range (p / k), F k (heckePointAux k (p / k) b τ)) a := by
    intro a _
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [heckePointAux_eq]
  rw [Finset.sum_congr rfl hsum, Finset.sum_attach p.divisors
    (fun k : ℕ => ∑ b ∈ Finset.range (p / k), F k (heckePointAux k (p / k) b τ)),
    Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
  simp only [Nat.div_one, Nat.div_self hp.pos, Finset.range_one, Finset.sum_singleton]
  rw [heckePointAux_eq _ hp.pos one_pos]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [heckePointAux_eq _ one_pos hp.pos]

/-- Complete replicability of `g` at a prime `p`, in two-block form. -/
lemma replicatesAtPrime_of_replication {g : AutVnat} {p : ℕ} (hp : p.Prime)
    (h : ∃ P : Polynomial ℂ, ∀ τ : ℍ, P.eval (mckayThompsonFun g τ) =
      ∑ a ∈ p.divisors.attach, ∑ b ∈ Finset.range (p / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (p / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)) :
    ReplicatesAtPrime (mckayThompsonFun g) (mckayThompsonFun (g ^ p)) p hp := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun x => P.eval x, fun τ => ?_⟩
  have := (hP τ).trans (heckeSum_prime (fun k => mckayThompsonFun (g ^ k)) hp τ)
  simpa only [pow_one] using this

/-! ### The bridge -/

/-- Complete replicability, required only for automorphisms of finite order. -/
def CompletelyReplicableOfFinOrder : Prop :=
  ∀ (g : AutVnat), IsOfFinOrder g → ∀ m : ℕ, 0 < m → ∃ P : Polynomial ℂ, P.Monic ∧
    P.natDegree = m ∧ ∀ τ : ℍ, P.eval (mckayThompsonFun g τ) =
      ∑ a ∈ m.divisors.attach, ∑ b ∈ Finset.range (m / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (m / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)

lemma completelyReplicableOfFinOrder_of_completelyReplicable (hrep : CompletelyReplicable) :
    CompletelyReplicableOfFinOrder :=
  fun g _ m hm => hrep g m hm

/-- **Conway–Norton for one automorphism**, from the `Γ₁` theorem and replication of `g` at every
prime (with any polynomial, monic or not). -/
theorem conwayNortonFor_of_gammaOne (h1 : ConwayNortonGammaOne) {g : AutVnat}
    (hg : IsOfFinOrder g)
    (hrep : ∀ p : ℕ, p.Prime → ∃ P : Polynomial ℂ, ∀ τ : ℍ, P.eval (mckayThompsonFun g τ) =
      ∑ a ∈ p.divisors.attach, ∑ b ∈ Finset.range (p / a),
        mckayThompsonFun (g ^ (a : ℕ)) (heckePoint a (p / a) b (Nat.pos_of_mem_divisors a.2)
          (Nat.div_pos (Nat.divisor_le a.2) (Nat.pos_of_mem_divisors a.2)) τ)) :
    ConwayNortonFor g := by
  obtain ⟨Γ, M, hM, hdet, hΓ1, hcomm, hH⟩ := h1 g hg
  refine ⟨Γ.adjoinNegOne, M, (isMoonshineGroup_adjoinNegOne_of_replicable hH hdet hΓ1 hM hcomm
    fun p hp _ => ?_).1, hH.adjoinNegOne⟩
  obtain ⟨Γ', M', -, -, -, -, hH'⟩ := h1 (g ^ p) hg.pow
  exact ⟨mckayThompsonFun (g ^ p), hH'.holomorphic, mckayThompsonFun_periodic (g ^ p),
    hH'.normalized, replicatesAtPrime_of_replication hp (hrep p hp)⟩

/-- **The bridge, weak form**: the `Γ₁` theorem and complete replicability of the finite-order
automorphisms give the Conway–Norton conjecture, given that every automorphism has finite order. -/
theorem conwayNorton_of_gammaOne_of_finOrder (hfin : ∀ g : AutVnat, IsOfFinOrder g)
    (h1 : ConwayNortonGammaOne) (hrep : CompletelyReplicableOfFinOrder) :
    ConwayNortonConjecture := fun g =>
  conwayNortonFor_of_gammaOne h1 (hfin g) fun p hp => by
    obtain ⟨P, -, -, hP⟩ := hrep g (hfin g) p hp.pos
    exact ⟨P, hP⟩

/-- **The bridge** `ConwayNortonGammaOne → CompletelyReplicable → ConwayNortonConjecture`,
given that every automorphism of `V♮` has finite order. -/
theorem conwayNorton_of_gammaOne (hfin : ∀ g : AutVnat, IsOfFinOrder g)
    (h1 : ConwayNortonGammaOne) (hrep : CompletelyReplicable) : ConwayNortonConjecture :=
  conwayNorton_of_gammaOne_of_finOrder hfin h1
    (completelyReplicableOfFinOrder_of_completelyReplicable hrep)

end VOA.Moonshine.ConwayNorton
