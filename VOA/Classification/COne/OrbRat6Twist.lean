import VOA.Classification.COne.OrbRat6Sigma

/-! # The twisted characters of the tetrahedral model from `V₁₈`-modules

Pull the `V₁₈`-modules `V_{L+λ_j}` (`L = √18 ℤ`, `|j| < 9`, lowest weight `j²/36`) back along
`iotaW : W → V₁₈`.  The lowest-weight vector `e^{λ_j}` spans the lowest weight space, so it is a
top eigenline for `W` and gives a character `χ_j` of `A(W)` with `χ_j[ω] = j²/36`
(`exists_character_twisted`).  The weights `j²/36`, `j ∈ {1,5,7,2,4,8}`, are exactly the six
twisted doubled weights `1/36, 25/36, 49/36, 1/9, 4/9, 16/9`.

Distinctness `χ_j ≠ χ_{−j}` follows once the zero mode of `iotaW aT` separates the two tops
(`TwistedTopSeparation`, a closed statement about explicit `V₁₈`-modules):

  `cubicTwistedDoubledPairs_of_sep : TwistedTopSeparation → CubicTwistedDoubledPairs`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial VOA.LatGen.Screen OrbC2b OrbRat2 OrbRat5 VertexOperatorAlgebra ConverseUniverse
  PlusSplitting PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible PlusUnitary

/-- The `V₁₈`-module `V_{L+λ_j}`. -/
abbrev Nj (j : ℤ) : OrdVModule V18 Sp9 := latticeModule (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j

/-- Its lowest-weight vector `e^{λ_j}`. -/
abbrev top9 : Sp9 := latVacuumGen (latP (1 * 3 ^ 2))

/-- The lowest weight `j²/36`. -/
abbrev hj (j : ℤ) : ℂ := ((((j : ℝ) ^ 2 / (4 * ((1 * 3 ^ 2 : ℕ) : ℝ)) : ℝ)) : ℂ)

theorem top9_mem (j : ℤ) : top9 ∈ (Nj j).weight (hj j) :=
  latticeModule_vacuum_mem (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j

theorem top9_ne : top9 ≠ 0 := latVacuumGen_ne_zero (latP (1 * 3 ^ 2))

theorem Nj_lowest {j : ℤ} (hj9 : |j| ≤ 9) : IsLowestWeight (Nj j) (hj j) :=
  latticeModule_isLowestWeight (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j (by simpa using hj9)

theorem fiber_zero {j : ℤ} (hj9 : |j| < 9) (w n : ℤ) (hw0 : 0 ≤ w)
    (h : ((((w.toNat : ℕ) : ℝ) + ((2 * ((1 * 3 ^ 2 : ℕ) : ℤ) * n + j : ℤ) : ℝ) ^ 2 /
      (4 * ((1 * 3 ^ 2 : ℕ) : ℝ)) : ℝ) : ℂ) = hj j) : w = 0 ∧ n = 0 := by
  have hre : ((w.toNat : ℕ) : ℝ) + ((2 * ((1 * 3 ^ 2 : ℕ) : ℤ) * n + j : ℤ) : ℝ) ^ 2 /
      (4 * ((1 * 3 ^ 2 : ℕ) : ℝ)) = (j : ℝ) ^ 2 / (4 * ((1 * 3 ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast h
  have hw : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hw0
  rw [hw] at hre
  have hint : 36 * w + (18 * n + j) ^ 2 = j ^ 2 := by
    have : ((36 * w + (18 * n + j) ^ 2 : ℤ) : ℝ) = ((j ^ 2 : ℤ) : ℝ) := by
      push_cast at hre ⊢
      field_simp at hre
      linarith
    exact_mod_cast this
  have hj1 : -9 < j := by rw [abs_lt] at hj9; exact hj9.1
  have hj2 : j < 9 := by rw [abs_lt] at hj9; exact hj9.2
  have hn : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · nlinarith
  refine ⟨?_, hn⟩
  rw [hn] at hint; nlinarith

/-- The lowest weight space is the line `ℂ e^{λ_j}` (`|j| < 9`). -/
theorem Nj_weight_top {j : ℤ} (hj9 : |j| < 9) : (Nj j).weight (hj j) ≤ ℂ ∙ top9 := by
  change shiftWeightSpace (latP (1 * 3 ^ 2)) (glueLat (1 * 3 ^ 2) j) (glueIota (1 * 3 ^ 2) j)
    (glueDelta (1 * 3 ^ 2) j) (hj j) ≤ _
  refine iSup_le fun p => iSup_le fun hp => ?_
  obtain ⟨hp0, hpw⟩ := hp
  rw [shiftWeight_rankOne (1 * 3 ^ 2) (one_le_mn2 1 le_rfl 3) j] at hpw
  obtain ⟨hw0, hn0⟩ := fiber_zero hj9 p.1 p.2 hp0 hpw
  obtain ⟨w, n⟩ := p
  simp only at hw0 hn0
  subst hw0 hn0
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (fock_zero hq)
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  rw [mkEα_apply]
  exact (latStateGen_csmul _ c 1 _).symm

/-- `V_{L+λ_j}` as a weak module of the tetrahedral model. -/
abbrev Bj (j : ℤ) : WeakModule cubicModel Sp9 := pullWeak iotaW_hom (Nj j).toWeakModule

theorem Bj_YM (j : ℤ) (w : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    (Bj j).YM w = (Nj j).YM (iotaW w) := rfl

theorem iota_grading {k : ℤ} {w : (orbifold (Subgroup.zpowers kleinCubic)).carrier}
    (hw : w ∈ cubicModel.grading k) : iotaW w ∈ V18.grading k :=
  voaHom_map_grading iotaW_hom iotaW_omega hw

theorem top9_Omega {j : ℤ} (hj9 : |j| ≤ 9) : top9 ∈ Omega (Bj j) := by
  intro β v hv n hn
  rw [Bj_YM]
  exact mode_lowering_vanish (Nj j) (Nj_lowest hj9) (iota_grading hv) (top9_mem j) hn

theorem top9_line {j : ℤ} (hj9 : |j| < 9) (k : ℤ)
    (a : (orbifold (Subgroup.zpowers kleinCubic)).carrier) (ha : a ∈ cubicModel.grading k) :
    ∃ c : ℂ, mode ((Bj j).YM a) (k - 1) top9 = c • top9 := by
  rw [Bj_YM]
  have hx := mode_mem_weight (Nj j) (iota_grading ha) (top9_mem j) (k - 1)
  rw [show hj j + (k : ℂ) - ((k - 1 : ℤ) : ℂ) - 1 = hj j by push_cast; ring] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Nj_weight_top hj9 hx)
  exact ⟨c, hc.symm⟩

theorem top9_eight {j : ℤ} (hj9 : |j| < 9) :
    ∃ c : ℂ, mode ((Nj j).YM (iotaW aW)) 8 top9 = c • top9 := by
  have := top9_line hj9 9 aW aW_mem
  rwa [show (9 : ℤ) - 1 = 8 by norm_num] at this

/-- The eigenvalue of `o(iotaW aT)` on `e^{λ_j}`. -/
def topVal (j : ℤ) : ℂ :=
  if hj9 : |j| < 9 then (top9_eight hj9).choose else 0

theorem topVal_spec {j : ℤ} (hj9 : |j| < 9) :
    mode ((Nj j).YM (iotaW aW)) 8 top9 = topVal j • top9 := by
  rw [topVal, dif_pos hj9]
  exact (top9_eight hj9).choose_spec

@[reducible] local instance zhuRingCubic7 : Ring (VOA.A cubicModel) := instRingA _
@[reducible] local instance zhuAlgebraCubic7 : Algebra ℂ (VOA.A cubicModel) := instAlgebraA _

/-- The character of `A(W)` from the top of `V_{L+λ_j}`. -/
theorem exists_character_twisted {j : ℤ} (hj9 : |j| < 9) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) = hj j ∧
      χ (VOA.mk cubicModel aW) = topVal j := by
  have hΩ := top9_Omega (j := j) hj9.le
  obtain ⟨χ, hχ⟩ := exists_character_of_top_line (Bj j) hΩ top9_ne (top9_line hj9)
  refine ⟨χ, ?_, ?_⟩
  · refine character_omega_of_top (Bj j) hΩ top9_ne ?_ χ hχ
    rw [Bj_YM, iotaW_omega]
    exact (Nj j).L0_weight _ _ (top9_mem j)
  · have e := hχ (VOA.mk cubicModel aW)
    rw [topEvaluation_mk, oLevW_homogeneous _ 0 aW_mem,
      show (9 : ℤ) - 1 + 0 = 8 by norm_num, Bj_YM, topVal_spec hj9] at e
    have h := sub_eq_zero.mpr e
    rw [← sub_smul] at h
    rcases smul_eq_zero.mp h with h' | h'
    · exact (sub_eq_zero.mp h').symm
    · exact absurd h' top9_ne

/-- OPEN (closed statement about explicit `V₁₈`-modules): the zero mode of `iotaW aT`
separates the tops of `V_{L+λ_j}` and `V_{L−λ_j}` for the six twisted labels. -/
def TwistedTopSeparation : Prop :=
  ∀ j ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ), topVal j ≠ topVal (-j)

/-- The label `j` of the twisted pair `k` (`cubicPairWeight k = j²/36`). -/
def pairLabel : Fin 8 → ℤ := ![0, 0, 1, 5, 7, 2, 4, 8]

theorem pairLabel_weight : ∀ k : Fin 8, 2 ≤ k.val →
    (cubicPairWeight k : ℚ) = (pairLabel k : ℚ) ^ 2 / 36 := by
  decide +kernel

theorem pairLabel_mem : ∀ k : Fin 8, 2 ≤ k.val → pairLabel k ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ) := by
  decide +kernel

theorem hj_eq (j : ℤ) : hj j = (((j : ℚ) ^ 2 / 36 : ℚ) : ℂ) := by
  rw [hj]
  push_cast
  norm_num

/-- The six twisted doubled pairs, from the top separation. -/
theorem cubicTwistedDoubledPairs_of_sep (hsep : TwistedTopSeparation) :
    CubicTwistedDoubledPairs := by
  intro k hk
  set j := pairLabel k
  have hjm := pairLabel_mem k hk
  have hall : ∀ x ∈ ({1, 2, 4, 5, 7, 8} : Finset ℤ), |x| < 9 := by decide
  have hj9 : |j| < 9 := hall j hjm
  have hj9' : |(-j)| < 9 := by rwa [abs_neg]
  obtain ⟨χ₁, hω₁, ha₁⟩ := exists_character_twisted hj9
  obtain ⟨χ₂, hω₂, ha₂⟩ := exists_character_twisted hj9'
  have hw : ((cubicPairWeight k : ℚ) : ℂ) = (((j : ℚ) ^ 2 / 36 : ℚ) : ℂ) := by
    rw [pairLabel_weight k hk]
  refine ⟨χ₁, χ₂, ?_, ?_, ?_⟩
  · intro heq
    apply hsep j hjm
    rw [← ha₁, ← ha₂, heq]
  · rw [hω₁, hj_eq, hw]
  · rw [hω₂, hj_eq, hw]
    push_cast
    ring

end VOA.Classification.COne.OrbRat6
