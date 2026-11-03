import VOA.Classification.COne.OrbRat6Top

/-! # The doubled pair at weight `9/4`

`W = cubicModel = (V₂^{Klein})^{rotC}` acts on the `V₂`-module `M = V_{ℤβ+β/2}` by restriction.
The operator `φ = P F P` (`F` the lift of `rotC`, `P` the even-sector projection) commutes with
every mode of `W`.  For `s² = 3` the vector `y_s = 2is q₁ + q₃` (weight `9/4`) is a
`φ`-eigenvector with eigenvalue `λ_s = (−i+s)/2`; there is no such eigenvector in lower weight,
and in weight `9/4` the eigenspace is the line `ℂ y_s`.  Hence `y_s` is a top eigenline of `M`
as a weak `W`-module and gives a character `χ_s` of `A(W)` with `χ_s[ω] = 9/4`.

The tetrahedral weight-nine vector `aT = −120 v₁ + v₅ ∈ W` acts on `y_s` by `20 i s κ`
(`κ ≠ 0`), so `χ_{√3} ≠ χ_{−√3}`.

`cubicDoubledPair_nine_four : OrbRat5.CubicDoubledPair (9 / 4)`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen OrbC2b OrbRat2 OrbRat5 VertexOperatorAlgebra PlusSplitting
  PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusUnitary

/-! ## §1 `aT` lies in the tetrahedral orbifold -/

theorem thetaM_aT : thetaM 1 le_rfl aT = aT := by
  rcases eps1_cases with he | he
  · have hzC : charU 1 le_rfl (-1) * rotC = rotC * thetaM 1 le_rfl := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    have h := congrArg (fun g : Aut V1 => g aT) hzC
    simp only [Aut.mul_apply, rotC_aT, charU_neg_aT] at h
    apply rotC.toLinearEquiv.injective
    change rotC _ = rotC aT
    rw [rotC_aT]; exact h.symm
  · have hzC : charU 1 le_rfl (-1) * rotC =
        rotC * (thetaM 1 le_rfl * charU 1 le_rfl (-1)) := by
      apply aut_ext_xyz
      intro a b c
      simp only [Aut.mul_apply, charU_neg_one_xyz, rotC_xyz, thetaM1_xyz, he]
      apply xyz_congr <;> ring
    have h := congrArg (fun g : Aut V1 => g aT) hzC
    simp only [Aut.mul_apply, rotC_aT, charU_neg_aT] at h
    apply rotC.toLinearEquiv.injective
    change rotC _ = rotC aT
    rw [rotC_aT]; exact h.symm

theorem aT_klein : aT ∈ (orbifold klein).carrier :=
  (klein_fixed_iff aT).mpr ⟨charU_neg_aT, thetaM_aT⟩

/-- `aT` in the Klein orbifold. -/
def aK : (orbifold klein).carrier := ⟨aT, aT_klein⟩

theorem kleinCubic_aK : kleinCubic aK = aK := Subtype.ext rotC_aT

/-- `aT` as an element of the tetrahedral model. -/
def aW : (orbifold (Subgroup.zpowers kleinCubic)).carrier :=
  ⟨aK, (mem_orbifold_zpowers_iff kleinCubic aK).mpr kleinCubic_aK⟩

theorem vv_grading (k : ℕ) (hk : k ≤ 6) : vv k ∈ V1.grading 9 := by
  have h := bigradα_le_gradingLatGen (latP 1) _ _ (vv_bigrad k)
  convert h using 2
  rw [halfNorm_latP1]
  simp only [ci]
  have hk' : (k : ℤ) ≤ 6 := by exact_mod_cast hk
  push_cast
  ring

theorem aT_grading : aT ∈ V1.grading 9 := by
  simp only [aT, R7, zero_smul, zero_add, add_zero, one_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (vv_grading 1 (by norm_num)))
    (vv_grading 5 (by norm_num))

theorem aW_mem : aW ∈ cubicModel.grading 9 := aT_grading

/-! ## §2 The restricted module -/

/-- `V_{ℤβ+β/2}` as a weak module of the tetrahedral model. -/
abbrev Acub : WeakModule cubicModel Sp :=
  (orbifold (Subgroup.zpowers kleinCubic)).restrictWeakModule
    ((orbifold klein).restrictWeakModule Mo.toWeakModule)

theorem Acub_YM (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    Acub.YM w = Mo.YM ((w : (orbifold klein).carrier) : Sp) := rfl

theorem bar_rotC (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    rotC ((w : (orbifold klein).carrier) : Sp) = ((w : (orbifold klein).carrier) : Sp) := by
  have h := (mem_orbifold_zpowers_iff kleinCubic (w : (orbifold klein).carrier)).mp w.2
  exact congrArg Subtype.val h

theorem bar_klein (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    charU 1 le_rfl (-1) ((w : (orbifold klein).carrier) : Sp) =
      ((w : (orbifold klein).carrier) : Sp) :=
  ((klein_fixed_iff _).mp (w : (orbifold klein).carrier).2).1

theorem bar_grading {k : ℤ} {w : (orbifold (Subgroup.zpowers kleinCubic)).carrier}
    (hw : w ∈ cubicModel.grading k) :
    ((w : (orbifold klein).carrier) : Sp) ∈ (V2m 1 le_rfl).grading k := hw

theorem phi_mode_cub (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) (n : ℤ) (x : Sp) :
    phi (mode (Acub.YM w) n x) = mode (Acub.YM w) n (phi x) :=
  phi_mode (bar_klein w) (bar_rotC w) n x

/-! ## §3 The eigenlines -/

section Eigen

variable {s : ℂ}

/-- `y_s = 2is q₁ + q₃`. -/
def ys9 (s : ℂ) : Sp := Q 0 (2 * I * s) 0 1

/-- `λ_s = (−i + s)/2`. -/
def lam9 (s : ℂ) : ℂ := (-I + s) / 2

theorem lam9_ne_zero (hs : s * s = 3) : lam9 s ≠ 0 := by
  intro h
  have h1 : s = I := by unfold lam9 at h; linear_combination 2 * h
  rw [h1, I_mul_I] at hs
  norm_num at hs

theorem lam9_ne_I (hs : s * s = 3) : lam9 s ≠ I := by
  intro h
  have h1 : s = 3 * I := by unfold lam9 at h; linear_combination 2 * h
  rw [h1] at hs
  have : (3 * I) * (3 * I) = -9 := by
    rw [show (3 * I) * (3 * I) = 9 * (I * I) by ring, I_mul_I]; ring
  rw [this] at hs
  norm_num at hs

theorem phi_ys9 (hs : s * s = 3) : phi (ys9 s) = lam9 s • ys9 s := by
  rw [ys9, phi_Q, Q_smul, lam9]
  have hI : I * I = -1 := I_mul_I
  apply Q_congr
  · ring
  · linear_combination (-I) * hs
  · ring
  · linear_combination (-s / 2) * hI

theorem qv1_weight : qv 1 ∈ Mo.weight ((9 / 4 : ℚ) : ℂ) := by
  have h := mem_weight (w := 2) (n := 0) (by norm_num) qv_Sd1
  convert h using 2
  push_cast; norm_num

theorem qv3_weight : qv 3 ∈ Mo.weight ((9 / 4 : ℚ) : ℂ) := by
  have h := mem_weight (w := 0) (n := -2) (by norm_num) qv_Sd3
  convert h using 2
  push_cast; norm_num

theorem ys9_weight : ys9 s ∈ Mo.weight ((9 / 4 : ℚ) : ℂ) := by
  rw [ys9, Q]
  simp only [zero_smul, zero_add, add_zero, one_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ qv1_weight) qv3_weight

theorem ys9_ne_zero : ys9 s ≠ 0 := by
  intro h
  rw [ys9, Q] at h
  simp only [zero_smul, zero_add, add_zero, one_smul] at h
  have h' : (2 * I * s) • qv 1 = -qv 3 := eq_neg_of_add_eq_zero_left h
  have hH : Hm ((2 * I * s) • qv 1) = Hm (-qv 3) := by rw [h']
  rw [map_smul, map_neg, Hm_Sd qv_Sd1, Hm_Sd qv_Sd3, smul_smul,
    show ((2 * (0 : ℤ) + 1 : ℤ) : ℂ) = 1 by norm_num, mul_one, h',
    show ((2 * (-2 : ℤ) + 1 : ℤ) : ℂ) = -3 by norm_num] at hH
  have h3 : qv 3 = (-3 : ℂ) • qv 3 := neg_inj.mp hH
  have h4 : (4 : ℂ) • qv 3 = 0 := by
    rw [show (4 : ℂ) • qv 3 = qv 3 - (-3 : ℂ) • qv 3 by module, ← h3, sub_self]
  rcases smul_eq_zero.mp h4 with h5 | h5
  · norm_num at h5
  · exact qv_ne 3 le_rfl h5

theorem ys9_Omega (hs : s * s = 3) : ys9 s ∈ Omega Acub := by
  intro β v hv n hn
  rw [Acub_YM]
  set x := mode (Mo.YM ((v : (orbifold klein).carrier) : Sp)) n (ys9 s) with hxdef
  have hx := mode_mem_weight Mo (bar_grading hv) (ys9_weight (s := s)) n
  have hphi : phi x = lam9 s • x := by
    rw [hxdef]
    have := phi_mode_cub v n (ys9 s)
    rw [Acub_YM] at this
    rw [this, phi_ys9 hs, map_smul]
  have hk : (1 : ℤ) ≤ n + 1 - β := by omega
  have hw : ((9 / 4 : ℚ) : ℂ) + (β : ℂ) - (n : ℂ) - 1 = ((9 / 4 - (n + 1 - β : ℤ) : ℚ) : ℂ) := by
    push_cast; ring
  rw [hw] at hx
  exact eigen_low (lam9_ne_zero hs) (lam9_ne_I hs) hk hx hphi

theorem ys9_line (hs : s * s = 3) (k : ℤ) (a : (orbifold (Subgroup.zpowers kleinCubic)).carrier)
    (ha : a ∈ cubicModel.grading k) :
    ∃ c : ℂ, mode (Acub.YM a) (k - 1) (ys9 s) = c • ys9 s := by
  rw [Acub_YM]
  have hx := mode_mem_weight Mo (bar_grading ha) (ys9_weight (s := s)) (k - 1)
  rw [show ((9 / 4 : ℚ) : ℂ) + (k : ℂ) - ((k - 1 : ℤ) : ℂ) - 1 = ((9 / 4 : ℚ) : ℂ) by
    push_cast; ring] at hx
  have hphi : phi (mode (Mo.YM ((a : (orbifold klein).carrier) : Sp)) (k - 1) (ys9 s)) =
      lam9 s • mode (Mo.YM ((a : (orbifold klein).carrier) : Sp)) (k - 1) (ys9 s) := by
    have := phi_mode_cub a (k - 1) (ys9 s)
    rw [Acub_YM] at this
    rw [this, phi_ys9 hs, map_smul]
  obtain ⟨α, γ, hxe, h1, h2⟩ := eigen94 (lam9_ne_zero hs) (lam9_ne_I hs) hx hphi
  refine ⟨γ, ?_⟩
  rw [hxe, ys9, Q_smul]
  have hI : I * I = -1 := I_mul_I
  have hα : α = 2 * I * s * γ := by
    unfold lam9 at h2
    linear_combination (-4 * I) * h2 + α * hI
  apply Q_congr
  · ring
  · rw [hα]; ring
  · ring
  · ring

end Eigen

/-! ## §4 Characters -/

@[reducible] local instance zhuRingCubic6 : Ring (VOA.A cubicModel) := instRingA _
@[reducible] local instance zhuAlgebraCubic6 : Algebra ℂ (VOA.A cubicModel) := instAlgebraA _

theorem oa_ys9 (s : ℂ) (hs : s * s = 3) :
    mode (Mo.YM aT) 8 (ys9 s) = (20 * I * s * κ) • ys9 s := by
  simp only [ys9, Q, zero_smul, zero_add, add_zero, one_smul, map_add, map_smul]
  rw [oa_q1, oa_q3, smul_add, smul_smul, smul_smul]
  have hI : I * I = -1 := I_mul_I
  have e2 : (-120 * κ) = 20 * I * s * κ * (2 * I * s) := by
    linear_combination (-40 * κ * I * I) * hs + (-120 * κ) * hI
  rw [e2]
  module

theorem exists_character_nine (s : ℂ) (hs : s * s = 3) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel aW) = 20 * I * s * κ ∧
      χ (VOA.mk cubicModel cubicModel.conformalVector) = ((9 / 4 : ℚ) : ℂ) := by
  obtain ⟨χ, hχ⟩ := exists_character_of_top_line Acub (ys9_Omega hs) ys9_ne_zero
    (ys9_line hs)
  refine ⟨χ, ?_, ?_⟩
  · have e := hχ (VOA.mk cubicModel aW)
    rw [topEvaluation_mk, oLevW_homogeneous _ 0 aW_mem,
      show (9 : ℤ) - 1 + 0 = 8 by norm_num, Acub_YM] at e
    change mode (Mo.YM aT) 8 (ys9 s) = _ at e
    rw [oa_ys9 s hs] at e
    have h := sub_eq_zero.mpr e
    rw [← sub_smul] at h
    rcases smul_eq_zero.mp h with h' | h'
    · exact (sub_eq_zero.mp h').symm
    · exact absurd h' ys9_ne_zero
  · refine character_omega_of_top Acub (ys9_Omega hs) ys9_ne_zero ?_ χ hχ
    rw [Acub_YM]
    exact Mo.L0_weight _ _ ys9_weight

theorem sqrt3_mul' : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- **The doubled pair at weight `9/4`.** -/
theorem cubicDoubledPair_nine_four : CubicDoubledPair (9 / 4) := by
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  have hs : s * s = 3 := sqrt3_mul'
  have hs' : (-s) * (-s) = 3 := by rw [neg_mul_neg, hs]
  obtain ⟨χ₁, ha₁, hω₁⟩ := exists_character_nine s hs
  obtain ⟨χ₂, ha₂, hω₂⟩ := exists_character_nine (-s) hs'
  refine ⟨χ₁, χ₂, ?_, hω₁, hω₂⟩
  intro heq
  rw [heq, ha₂] at ha₁
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  have : (40 * I * κ) * s = 0 := by linear_combination -ha₁
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · norm_num at h''
      · exact I_ne_zero h''
    · exact κ_ne h'
  · exact hs0 h

end VOA.Classification.COne.OrbRat6
