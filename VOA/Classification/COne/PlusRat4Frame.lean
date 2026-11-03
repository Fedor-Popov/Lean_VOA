import VOA.Classification.COne.PlusRat4Charged

/-! # Reusable pieces of the gap-two argument (any quotient row)

* `lowWeights`: in an extension with kernel bottom `h + 2` and quotient bottom `h`, no generalized
  weight has real part below `h`.
* `exists_top_lift`: a quotient-bottom lift `x` with `x ∈ Ω`.
* `quad_relations`: for top data with `o(H⁴) = a₄`, `o(H⁶) = a₆`, `p₂ = c₂ L(-1)x`,
  `p₃ = c₃ L(-1)x`, and top vectors `w₂ = Q₂ - a₂R - b₂Q₁`, `w₃ = Q₃ - a₃R - b₃Q₁` of weight
  `h + 2` on which `o(H⁴), o(H⁶)` vanish: the `L(1), L(2)` equations for `(a_t, b_t)` and the
  three vector relations.
* `E_deg2_zero`: the `E`-obstruction vanishes when the virtual eigenvalue is nonzero.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusCharacterTable PlusSplitting
  PlusRatTelescope PlusZhuSchur PlusZhuNormalForms PlusResonantPairs PlusRatSign PlusRat2
  VOA.Huang.LogRemovalAdmissible ABDWeakAdmissible PlusRat3

section Frame
variable (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) {M : Type} [AddCommGroup M] [Module ℂ M]
  (A : WeakModule (V2mPlus m hm) M)

theorem lowWeights {P : Submodule (modeAlg A) M} {h : ℂ} (hb : FactorBottom A ⊥ P (h + 2))
    (ht : FactorBottom A P ⊤ h) :
    ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0 := by
  have hre : (h + 2).re = h.re + 2 := by simp
  intro μ hμ v hv
  have hvP : v ∈ P := by
    by_contra hc
    have hw : FactorWeight A P ⊤ μ := fun hT => hc (hT ⟨Submodule.mem_top, hv⟩)
    have := ht.2 μ hw
    linarith
  exact kernel_generalized_below_bottom_eq_zero A P _ hb hvP hv (by rw [hre]; linarith)

theorem exists_top_lift {P : Submodule (modeAlg A) M} (hP : IsAtom P) {h : ℂ}
    (hb : FactorBottom A ⊥ P (h + 2)) (ht : FactorBottom A P ⊤ h) :
    ∃ x : M, L0 A x = h • x ∧ x ∉ P ∧ x ≠ 0 ∧ x ∈ Omega A := by
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift (V2mPlus_c2Cofinite m hm) A P hP
    (show h + 2 ≠ h by intro hc; have := congrArg (· - h) hc; simp at this) hb ht
  have hx0 : x ≠ 0 := fun h => hxP (h ▸ P.zero_mem)
  have hxg : x ∈ (L0 A).maxGenEigenspace h :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  refine ⟨x, hxL, hxP, hx0, ?_⟩
  intro β v hv n hn
  apply lowWeights m hm A hb ht _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
  have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
  rw [Complex.add_re, Complex.intCast_re]
  linarith

variable {x : M} {h a4 a6 c2 c3 : ℂ}

include hm2 in
/-- The `L(1)`, `L(2)` equations and the three vector relations. -/
theorem quad_relations (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (hx0 : x ≠ 0)
    (hLx0 : mode (A.YM (V2mPlus m hm).conformalVector) 0 x ≠ 0)
    (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x) (h6 : mode (A.YM (HP m hm 3)) 5 x = a6 • x)
    (hp2 : mode (A.YM (HP m hm 2)) 2 x = c2 • mode (A.YM (HP m hm 1)) 0 x)
    (hp3 : mode (A.YM (HP m hm 3)) 4 x = c3 • mode (A.YM (HP m hm 1)) 0 x)
    (hker : ∀ w : M, w ∈ Omega A → L0 A w = (h + 2) • w →
      mode (A.YM (HP m hm 2)) 3 w = 0 ∧ mode (A.YM (HP m hm 3)) 5 w = 0)
    {a2 b2 a3 b3 : ℂ}
    (hw2 : mode (A.YM (HP m hm 2)) 1 x -
      a2 • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
      b2 • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∈ Omega A)
    (hw3 : mode (A.YM (HP m hm 3)) 3 x -
      a3 • mode (A.YM (V2mPlus m hm).conformalVector) 0 (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) -
      b3 • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x ∈ Omega A) :
    (5 * c2 + 1 / 3 - a2 * (4 * h + 2) - b2 * 3 = 0 ∧
      8 * a4 + 4 * h - a2 * (6 * h) - b2 * (4 * h + 1 / 2) = 0) ∧
    (7 * c3 + 9 / 2 * c2 + 1 / 10 - a3 * (4 * h + 2) - b3 * 3 = 0 ∧
      12 * a6 + 36 * a4 + 6 * h - a3 * (6 * h) - b3 * (4 * h + 1 / 2) = 0) ∧
    ((a4 - 1) • mode (A.YM (HP m hm 2)) 1 x + (6 : ℂ) • mode (A.YM (HP m hm 3)) 3 x -
      a2 • ((a4 + 6 * c2) • mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) + (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) -
      b2 • ((a4 + 2) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x +
        (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) = 0) ∧
    ((3 / 2 : ℂ) • mode (A.YM (HP m hm 2)) 1 x + (a4 - 5) • mode (A.YM (HP m hm 3)) 3 x +
        (6 : ℂ) • mode (A.YM (HP m hm 4)) 5 x -
      a3 • ((a4 + 6 * c2) • mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) + (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) -
      b3 • ((a4 + 2) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x +
        (6 : ℂ) • mode (A.YM (HP m hm 2)) 1 x) = 0) ∧
    ((a6 - 3) • mode (A.YM (HP m hm 2)) 1 x + (10 / 3 : ℂ) • mode (A.YM (HP m hm 3)) 3 x +
        (10 : ℂ) • mode (A.YM (HP m hm 4)) 5 x -
      a2 • ((a6 + 10 * c3) • mode (A.YM (V2mPlus m hm).conformalVector) 0
        (mode (A.YM (V2mPlus m hm).conformalVector) 0 x) + (20 : ℂ) • mode (A.YM (HP m hm 3)) 3 x) -
      b2 • ((a6 + 2) • mode (A.YM (V2mPlus m hm).conformalVector) (-1) x +
        (15 : ℂ) • mode (A.YM (HP m hm 2)) 1 x + (10 : ℂ) • mode (A.YM (HP m hm 3)) 3 x) = 0) := by
  have hg2 := HP_mem_grading m hm 2 (by norm_num) (by norm_num)
  have hg3 := HP_mem_grading m hm 3 (by norm_num) (by norm_num)
  have q1L1 := L1_Q1 m hm A hxΩ hm2
  have q1L2 := L2_Q1 m hm A hxΩ hxL hm2
  have q2L1 := L1_Q2 m hm A hxΩ hp2
  have q2L2 := L2_Q2 m hm A hxΩ hxL h4
  have q3L1 := L1_Q3 m hm A hxΩ hp2 hp3
  have q3L2 := L2_Q3 m hm A hxΩ hxL h4 h6
  have rL1 := L1_R A hxΩ hxL
  have rL2 := L2_R A hxΩ hxL
  rw [HP_one] at q1L1 q1L2 q2L1 q3L1
  have hw2L := L0_wv A hxL hg2 a2 b2
  have hw3L := L0_wv A hxL hg3 a3 b3
  simp only [TopData.wv] at hw2L hw3L
  rw [show ((2 * 2 : ℕ) : ℤ) - 3 = 1 by norm_num] at hw2L
  rw [show ((2 * 3 : ℕ) : ℤ) - 3 = 3 by norm_num] at hw3L
  have hO1 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus m hm).conformalVector) 2 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num)
  have hO2 : ∀ w : M, w ∈ Omega A → mode (A.YM (V2mPlus m hm).conformalVector) 3 w = 0 :=
    fun w hw => Omega_mode_vanish hw (V2mPlus m hm).conformal_mem (by norm_num)
  have g1 := hO1 _ hw2
  have g2 := hO2 _ hw2
  have g3 := hO1 _ hw3
  have g4 := hO2 _ hw3
  rw [map_sub, map_sub, map_smul, map_smul, q2L1, rL1, q1L1] at g1
  rw [map_sub, map_sub, map_smul, map_smul, q2L2, rL2, q1L2] at g2
  rw [map_sub, map_sub, map_smul, map_smul, q3L1, rL1, q1L1] at g3
  rw [map_sub, map_sub, map_smul, map_smul, q3L2, rL2, q1L2] at g4
  have eQ2 := oH4_Q2 m hm A h4
  have eQ3 := oH4_Q3 m hm A h4
  have eR := oH4_R m hm A h4 hp2
  have eQ1 := oH4_Q1 m hm A h4
  have fQ2 := oH6_Q2 m hm A h6
  have fR := oH6_R m hm A h6 hp3
  have fQ1 := oH6_Q1 m hm A h6
  rw [HP_one] at eR eQ1 fR fQ1
  obtain ⟨o4, o6⟩ := hker _ hw2 hw2L
  obtain ⟨o4', -⟩ := hker _ hw3 hw3L
  rw [map_sub, map_sub, map_smul, map_smul, eQ2, eR, eQ1] at o4
  rw [map_sub, map_sub, map_smul, map_smul, eQ3, eR, eQ1] at o4'
  rw [map_sub, map_sub, map_smul, map_smul, fQ2, fR, fQ1] at o6
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, o4, o4', o6⟩
  · have : (5 * c2 + 1 / 3 - a2 * (4 * h + 2) - b2 * 3) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g1
    exact (smul_eq_zero.mp this).resolve_right hLx0
  · have : (8 * a4 + 4 * h - a2 * (6 * h) - b2 * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) g2
    exact (smul_eq_zero.mp this).resolve_right hx0
  · have : (7 * c3 + 9 / 2 * c2 + 1 / 10 - a3 * (4 * h + 2) - b3 * 3) •
        mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) g3
    exact (smul_eq_zero.mp this).resolve_right hLx0
  · have : (12 * a6 + 36 * a4 + 6 * h - a3 * (6 * h) - b3 * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) g4
    exact (smul_eq_zero.mp this).resolve_right hx0

include hm2 in
/-- The `E`-obstruction vanishes when the virtual eigenvalue is nonzero. -/
theorem E_deg2_zero (hxΩ : x ∈ Omega A) (hxL : L0 A x = h • x) (hx0 : x ≠ 0)
    (hLx0 : mode (A.YM (V2mPlus m hm).conformalVector) 0 x ≠ 0) (h14 : 4 * h - 1 ≠ 0)
    (h4 : mode (A.YM (HP m hm 2)) 3 x = a4 • x)
    (hE0 : mode (A.YM (EP m hm)) ((m : ℤ) - 1) x = 0)
    (hE1 : mode (A.YM (EP m hm)) ((m : ℤ) - 2) x = 0)
    (hker : ∀ w : M, w ∈ Omega A → L0 A w = (h + 2) • w → mode (A.YM (HP m hm 2)) 3 w = 0)
    (hTr : ∃ a b : ℂ, TopData.wv A x (EP m hm) (m : ℤ) a b ∈ Omega A)
    (hlam : (2 * (2 * (m : ℂ)) ^ 2 - 5 * (2 * (m : ℂ)) + 2) * a4 +
      4 * (((m : ℂ) - 2) ^ 2 - 4 * m * h) ≠ 0) :
    mode (A.YM (EP m hm)) ((m : ℤ) - 3) x = 0 := by
  have q1L1 := L1_Q1 m hm A hxΩ hm2
  have q1L2 := L2_Q1 m hm A hxΩ hxL hm2
  have rL1 := L1_R A hxΩ hxL
  have rL2 := L2_R A hxΩ hxL
  rw [HP_one] at q1L1 q1L2
  obtain ⟨aE, bE, hwE⟩ := hTr
  have hwEL := L0_wv A hxL (EP_mem_grading m hm) aE bE
  simp only [TopData.wv] at hwE hwEL
  have g5 := Omega_mode_vanish hwE (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 2 by norm_num)
  have g6 := Omega_mode_vanish hwE (V2mPlus m hm).conformal_mem (show (2 : ℤ) ≤ 3 by norm_num)
  rw [map_sub, map_sub, map_smul, map_smul, L1_v m hm A hxΩ hE1, rL1, q1L1] at g5
  rw [map_sub, map_sub, map_smul, map_smul, L2_v m hm A hxΩ hE0, rL2, q1L2] at g6
  have f5 : aE * (4 * h + 2) + bE * 3 = 0 := by
    have : (aE * (4 * h + 2) + bE * 3) • mode (A.YM (V2mPlus m hm).conformalVector) 0 x = 0 := by
      linear_combination (norm := module) -g5
    exact (smul_eq_zero.mp this).resolve_right hLx0
  have f6 : aE * (6 * h) + bE * (4 * h + 1 / 2) = 0 := by
    have : (aE * (6 * h) + bE * (4 * h + 1 / 2)) • x = 0 := by
      linear_combination (norm := module) -g6
    exact (smul_eq_zero.mp this).resolve_right hx0
  obtain ⟨rfl, rfl⟩ := kac_zero h14 aE bE f5 f6
  simp only [zero_smul, sub_zero] at hwE hwEL
  have o := hker _ hwE hwEL
  have ev := oH4_v2 m hm A hxΩ hxL h4 hE0 hE1
  rw [o, smul_zero] at ev
  exact (smul_eq_zero.mp ev.symm).resolve_left hlam

end Frame

end VOA.Classification.COne.PlusRat4
