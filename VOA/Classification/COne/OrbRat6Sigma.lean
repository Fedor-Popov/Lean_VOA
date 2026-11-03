import VOA.Classification.COne.OrbRat6Nine

/-! # Conjugating the cubic rotation into the torus, and `W ↪ V₁₈`

* `sig = exp(a e₀) exp(b f₀)` with `a = −(1+i)√3/6`, `b = (1+√3)(1−i)/2` satisfies
  `sig ∘ rotC = charU ζ ∘ sig`, `ζ = (−1+i√3)/2` (`sig_conj`).
* Hence `sig` maps the tetrahedral model `W = cubicModel ⊂ V₂` into the `charU ζ`-fixed points,
  i.e. into the image of `scaleMorph 1 3 : V₁₈ → V₂` (`range_scaleMorph`), and
  `iotaW : W → V₁₈` (`= scaleMorph⁻¹ ∘ sig`) is a homomorphism of VOAs preserving `ω`
  (`iotaW_hom`, `iotaW_omega`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen OrbC2b OrbRat2 OrbRat5 VertexOperatorAlgebra ConverseUniverse

theorem eps1_eq_one : eps1 = 1 := PlusCharacterTable.rankOne_cocycle 1 _ _

/-- `√3 ∈ ℂ`. -/
abbrev s3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

theorem s3_sq : s3 ^ 2 = 3 := by
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem s3_pow3 : s3 ^ 3 = 3 * s3 := by rw [pow_succ, s3_sq]
theorem s3_pow4 : s3 ^ 4 = 9 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, s3_sq]; norm_num
theorem s3_pow5 : s3 ^ 5 = 9 * s3 := by rw [pow_succ, s3_pow4]
theorem s3_pow6 : s3 ^ 6 = 27 := by rw [pow_succ, s3_pow5]; ring_nf; rw [s3_sq]; norm_num
theorem s3_pow7 : s3 ^ 7 = 27 * s3 := by rw [pow_succ, s3_pow6]
theorem s3_pow8 : s3 ^ 8 = 81 := by rw [pow_succ, s3_pow7]; ring_nf; rw [s3_sq]; norm_num

theorem s3_ne : s3 ≠ 0 := by
  intro h; have := s3_sq; rw [h] at this; norm_num at this

/-- `ζ = (−1 + i√3)/2`. -/
def zc : ℂ := (-1 + s3 * I) / 2

theorem zc_ne : zc ≠ 0 := by
  intro h
  have h1 : s3 * I = 1 := by unfold zc at h; linear_combination 2 * h
  have h2 : (s3 * I) ^ 2 = 1 := by rw [h1]; norm_num
  rw [mul_pow, s3_sq, I_sq] at h2
  norm_num at h2

/-- `ζ` as a unit. -/
def zU : ℂˣ := Units.mk0 zc zc_ne

theorem zc_cube : zc ^ 3 = 1 := by
  unfold zc
  ring_nf
  rw [s3_sq, s3_pow3, I_sq, I_pow_three]
  ring

theorem zc_ne_one : zc ≠ 1 := by
  intro h
  have h1 : s3 * I = 3 := by unfold zc at h; linear_combination 2 * h
  have h2 : (s3 * I) ^ 2 = 9 := by rw [h1]; norm_num
  rw [mul_pow, s3_sq, I_sq] at h2
  norm_num at h2

theorem zc_sq_ne_one : zc ^ 2 ≠ 1 := by
  intro h
  have h3 := zc_cube
  rw [pow_succ, h, one_mul] at h3
  exact zc_ne_one h3

/-- The conjugator `exp(a e₀) exp(b f₀)`. -/
def sig : Aut V1 :=
  expE (-(1 + I) * s3 / 6) * expF ((1 + s3) * (1 - I) / 2)

theorem sig_xyz (a b c : ℂ) :
    sig (xyz a b c) = vec3 (latP 1) (a1 1)
      ((a + I * b) - 2 * (-(1 + I) * s3 / 6) * (c - (1 + s3) * (1 - I) / 2 * (a + I * b)) -
        (-(1 + I) * s3 / 6) ^ 2 * ((a - I * b) + 2 * ((1 + s3) * (1 - I) / 2) * c -
          ((1 + s3) * (1 - I) / 2) ^ 2 * (a + I * b)))
      ((c - (1 + s3) * (1 - I) / 2 * (a + I * b)) + (-(1 + I) * s3 / 6) *
        ((a - I * b) + 2 * ((1 + s3) * (1 - I) / 2) * c -
          ((1 + s3) * (1 - I) / 2) ^ 2 * (a + I * b)))
      ((a - I * b) + 2 * ((1 + s3) * (1 - I) / 2) * c -
        ((1 + s3) * (1 - I) / 2) ^ 2 * (a + I * b)) := by
  rw [sig, Aut.mul_apply, xyz, eps1_eq_one]
  rw [rootExp_vec3_neg _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root latP1_root',
    rootExp_vec3_pos _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root]
  simp only [cocycle_eq_eps1, eps1_eq_one]
  apply vec3_congr <;> ring

theorem zc_inv : zc⁻¹ = zc ^ 2 :=
  (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, zc_cube])).symm

/-- `sig ∘ rotC = charU ζ ∘ sig`. -/
theorem sig_conj : sig * rotC = charU 1 le_rfl zU * sig := by
  apply aut_ext_xyz
  intro a b c
  simp only [Aut.mul_apply, rotC_xyz]
  rw [sig_xyz, sig_xyz, charU_vec3]
  simp only [zU, Units.val_mk0, zc_inv]
  apply vec3_congr <;>
  · try unfold zc
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, Ipow8,
      s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6, s3_pow7, s3_pow8]
    ring_nf
    try simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, Ipow8,
      s3_sq, s3_pow3, s3_pow4, s3_pow5, s3_pow6, s3_pow7, s3_pow8]
    try ring_nf

/-! ## The fixed points of `charU ζ` and the embedding `W ↪ V₁₈` -/

/-- `V₁₈ = V_{√18 ℤ}`. -/
abbrev V18 := V2m (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3)
/-- Its carrier. -/
abbrev Sp9 := LatModuleGen (latP (1 * 3 ^ 2))
/-- `V₁₈ → V₂`, `α' ↦ 3β`. -/
abbrev sm : Sp9 →ₗ[ℂ] Sp := scaleMorph 1 3

theorem zc_zpow_eq_one {n : ℤ} (h : zc ^ n = 1) : (3 : ℤ) ∣ n := by
  have hr := Int.emod_add_mul_ediv n 3
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hz : zc ^ n = zc ^ (n % 3) := by
    conv_lhs => rw [← hr]
    rw [zpow_add₀ zc_ne, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast,
      zc_cube, one_zpow, mul_one]
  rw [hz] at h
  rcases hcases with h0 | h1 | h2
  · exact Int.dvd_of_emod_eq_zero h0
  · rw [h1, zpow_one] at h; exact absurd h zc_ne_one
  · rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    exact absurd h zc_sq_ne_one

theorem mem_range_sm {x : Sp} (hx : charU 1 le_rfl zU x = x) : x ∈ LinearMap.range sm := by
  rw [range_scaleMorph 1 le_rfl 3]
  change ∀ g ∈ (cycHom 1 le_rfl 3).range, g x = x
  rw [fix_cyc_iff]
  intro k hk
  have hc := congrArg (coordEα (latP 1) k) hx
  rw [coordEα_charU] at hc
  have h2 : (((zU ^ ci 1 k : ℂˣ) : ℂ) - 1) • coordEα (latP 1) k x = 0 := by
    rw [sub_smul, hc, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hk
    rw [sub_eq_zero, Units.val_zpow_eq_zpow_val] at h3
    exact_mod_cast zc_zpow_eq_one h3
  · exact h3

/-- The underlying `V₂` vector of an element of the tetrahedral model. -/
def bar : (orbifold (Subgroup.zpowers kleinCubic)).carrier →ₗ[ℂ] Sp :=
  (orbifold klein).carrier.subtype ∘ₗ (orbifold (Subgroup.zpowers kleinCubic)).carrier.subtype

theorem bar_apply (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    bar w = ((w : (orbifold klein).carrier) : Sp) := rfl

theorem sig_bar_fixed (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    charU 1 le_rfl zU (sig (bar w)) = sig (bar w) := by
  have h := congrArg (fun g : Aut V1 => g (bar w)) sig_conj
  simp only [Aut.mul_apply] at h
  rw [← h, bar_apply, bar_rotC]

/-- The `V₁₈`-valued map. -/
def iotaW : (orbifold (Subgroup.zpowers kleinCubic)).carrier →ₗ[ℂ] Sp9 :=
  (LinearEquiv.ofInjective sm (scaleMorph_injective 1 le_rfl 3)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range sm) (sig.toLinearEquiv.toLinearMap ∘ₗ bar)
      (fun w => mem_range_sm (sig_bar_fixed w))

theorem sm_iotaW (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    sm (iotaW w) = sig (bar w) := by
  have h := (LinearEquiv.ofInjective sm (scaleMorph_injective 1 le_rfl 3)).apply_symm_apply
    ⟨sig (bar w), mem_range_sm (sig_bar_fixed w)⟩
  exact congrArg Subtype.val h

theorem sm_hom : IsVOAHom V18 V1 sm := scaleMorph_isVOAHom 1 le_rfl 3

theorem iotaW_hom : IsVOAHom cubicModel V18 iotaW := by
  constructor
  · apply scaleMorph_injective 1 le_rfl 3
    change sm _ = sm _
    rw [sm_iotaW, sm_hom.map_vacuum]
    exact sig.map_vacuum
  · intro u n v
    apply scaleMorph_injective 1 le_rfl 3
    change sm _ = sm _
    rw [sm_iotaW, sm_hom.map_smul, sm_iotaW, sm_iotaW]
    exact sig.map_smul _ _ _

theorem iotaW_omega : iotaW cubicModel.conformalVector = V18.conformalVector := by
  apply scaleMorph_injective 1 le_rfl 3
  change sm _ = sm _
  rw [sm_iotaW, scaleMorph_omega 1 le_rfl 3]
  exact sig.map_omega

end VOA.Classification.COne.OrbRat6
