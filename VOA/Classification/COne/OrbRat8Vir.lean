/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbRat8Frame
import VOA.Classification.COne.OrbRat3Inner
import VOA.Classification.COne.OrbRat5Wt
import VOA.Classification.COne.OrbRat5Four
import VOA.Classification.COne.PlusRat4Words
import VOA.Classification.COne.PlusRat3Iterate

/-!
# The Virasoro obstruction of the pair `(4 ↘ 1)` vanishes

Tetrahedral model `W = cubicModel`, `C₂`-cofinite, `dim A(W) ≤ 21`.  Let `A` be a weak
`W`-module with no generalized weights below `1`, and `u ∈ Ω(A)` with `L(0) u = u`.  Let

  `S = 2 L₋₃ - 4 L₋₂ L₋₁ + L₋₁³`

be the level-three singular vector of the `c = 1` Verma module `M(1)`.

* `cubic_U_low`: `U₍₈₎u = U₍₇₎u = U₍₆₎u = 0` (`U = cubicU`, weight nine).
* `cubic_singular_eq_zero`: `S u = 0`.

Proof.  The weight-one character is unique in the table, so `u` and the sign vector `h(-1)𝟙` of
`V₈⁻` (restricted to `W`) carry the same top character.  In `V₈⁻`: `U₍ₖ₎h(-1)𝟙 = 0` for
`k = 6, 7, 8` (`OrbRat3.inner_6/7/8`) and `S h(-1)𝟙 = 0` (`cert_S`, a Fock computation).  Word
transfer (`PlusRat4.word_transfer`, no top vectors at weights `2, 3` by the table) gives the three
vanishings and `S u ∈ Ω(A)` at weight `4`.  Since `U` is primary of weight `9`,
`[ω₍ₚ₎, U₍ₙ₎] = (8p - n) U₍ₚ₊ₙ₋₁₎`, and the coefficient of `U₍₅₎u` in `U₍₈₎ S u` is
`2·24 - 4·96 + 336 = 0` (for a weight-`w` primary it is `(w-1)(w-4)(w-9)`), so `U₍₈₎ (S u) = 0`.
Both weight-four characters of the table take nonzero values on `U` (`four_U_ne`), so the top
vector `S u` of weight `4` vanishes (`top_eq_zero_of_table`).

Consequence (`topCyclicVanishing_one_four`): the residual `TopCyclicVanishing cubicModel 1 4` of
`OrbRat8Frame` reduces to the sharper `TopCyclicFourOneResidual`, which may additionally assume
`S u = 0` and `U₍₆₎u = U₍₇₎u = U₍₈₎u = 0`: a non-split `(4 ↘ 1)` extension cannot come from the
Virasoro algebra; its kernel bottom must be produced by non-Virasoro words.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat8

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible PlusRatTelescope OrbRat2 PlusRat4

/-! ## §1 Generic: a top vector of a unique-weight row carries that row's character -/

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem top_scalar_of_unique (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    (A : WeakModule W M) {y : M} (hy : y ∈ Omega A) {c : ℂ} (hL : L0 A y = c • y)
    {i : Fin n} (huniq : ∀ j, wt j = c → j = i) :
    ∀ r, topEvaluation A y hy r = χ i r • y := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨ε, hsum, hmul, hmul'⟩ := charTable_idempotents hC2 hdim χ hχ
  have hfω : topEvaluation A y hy (VOA.mk W W.conformalVector - algebraMap ℂ _ c) = 0 := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, PlusRatSign.topEvaluation_one]
    change oLevW A 0 W.conformalVector y - c • y = 0
    rw [oLevW_homogeneous A 0 W.conformal_mem]
    change L0 A y - c • y = 0
    rw [hL, sub_self]
  have hz : ∀ j, j ≠ i → topEvaluation A y hy (ε j) = 0 := by
    intro j hj
    obtain ⟨e, he⟩ := VOA.mk_surjective W (ε j)
    have h1 : topEvaluation A y hy (ε j * (VOA.mk W W.conformalVector - algebraMap ℂ _ c)) = 0 := by
      rw [← he, topEvaluation_mk_mul, hfω, map_zero]
    rw [mul_sub, hmul', Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, hω,
      ← sub_smul, map_smul] at h1
    have hne : wt j - c ≠ 0 := sub_ne_zero.mpr (fun h => hj (huniq j h))
    exact (smul_eq_zero.mp h1).resolve_left hne
  have hyi : topEvaluation A y hy (ε i) = y := by
    conv_rhs => rw [← PlusRatSign.topEvaluation_one A y hy, ← hsum]
    rw [map_sum, Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)]
  intro r
  have hr : r = ∑ j, r * ε j := by rw [← Finset.mul_sum, hsum, mul_one]
  conv_lhs => rw [hr]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [hmul, map_smul, hyi]
  · intro j _ hj
    rw [hmul, map_smul, hz j hj, smul_zero]
  · simp

end Generic

/-! ## §2 The tetrahedral model -/

section Cubic

open OrbRat3 OrbRat5 OrbC2e OrbC2f PlusCharacterTable PlusC2Eval PlusC2 VOA.LatGen
  VOA.LatGen.Triplet VOA.SparseRational

attribute [local instance] instRingA instAlgebraA

theorem tetra_rows_low : ∀ j : Fin 21, tetraWeightQ j ≠ 2 ∧ tetraWeightQ j ≠ 3 := by
  decide +kernel

theorem tetra_rows_four : ∀ j : Fin 21, tetraWeightQ j = 4 → j = 2 ∨ j = 3 := by
  decide +kernel

theorem tetraWeight_ne_low (j : Fin 21) (k : ℕ) (hk0 : 0 < k) (hk : k < 3) :
    tetraWeight j ≠ 1 + (k : ℂ) := by
  intro h
  have hq : ((tetraWeightQ j : ℚ) : ℂ) = (((1 + k : ℕ) : ℚ) : ℂ) := by
    rw [show tetraWeight j = ((tetraWeightQ j : ℚ) : ℂ) from rfl] at h
    rw [h]; push_cast; ring
  have hq' : tetraWeightQ j = ((1 + k : ℕ) : ℚ) := by exact_mod_cast hq
  interval_cases k
  · exact (tetra_rows_low j).1 (by rw [hq']; norm_num)
  · exact (tetra_rows_low j).2 (by rw [hq']; norm_num)

theorem tetraWeight_four (j : Fin 21) (h : tetraWeight j = 4) : j = 2 ∨ j = 3 := by
  apply tetra_rows_four
  have : ((tetraWeightQ j : ℚ) : ℂ) = ((4 : ℚ) : ℂ) := by
    rw [show tetraWeight j = ((tetraWeightQ j : ℚ) : ℂ) from rfl] at h
    rw [h]; norm_num
  exact_mod_cast this

/-! ### The weight-four characters do not vanish on `U` -/

theorem four_values (s : ℂ) (hs : s * s = 3) {χ₁ χ₂ : VOA.A cubicModel →ₐ[ℂ] ℂ}
    (h₁ : ∀ z, topEvaluation plusAdj (ys s) (ys_mem_Omega hs) z = χ₁ z • ys s)
    (h₂ : ∀ z, topEvaluation plusAdj (ys (-s)) (ys_mem_Omega (by rw [neg_mul_neg]; exact hs)) z =
      χ₂ z • ys (-s)) :
    χ₁ (VOA.mk cubicModel cubicU) + χ₂ (VOA.mk cubicModel cubicU) = 0 ∧
      (3 * s * Complex.I) * (χ₂ (VOA.mk cubicModel cubicU) - χ₁ (VOA.mk cubicModel cubicU)) =
        -21600 := by
  set l₁ := χ₁ (VOA.mk cubicModel cubicU)
  set l₂ := χ₂ (VOA.mk cubicModel cubicU)
  have e₁ := h₁ (VOA.mk cubicModel cubicU)
  have e₂ := h₂ (VOA.mk cubicModel cubicU)
  rw [topEvaluation_mk, oLevW_homogeneous _ 0 cubicU_mem,
    show (9 : ℤ) - 1 + 0 = 8 by norm_num] at e₁ e₂
  have c₁ := congrArg (fun v : VP 4 four_ge_one => (v : LatModuleGen (latP 4))) e₁
  have c₂ := congrArg (fun v : VP 4 four_ge_one => (v : LatModuleGen (latP 4))) e₂
  simp only [plusAdj_U, Submodule.coe_smul, ys_coe] at c₁ c₂
  have hsum : (V2m 4 four_ge_one).smul Uc 8 ((2 : ℂ) • Jc) =
      l₁ • (Jc - (3 * s * Complex.I) • Ec) + l₂ • (Jc - (3 * -s * Complex.I) • Ec) := by
    have : (2 : ℂ) • Jc =
        (Jc - (3 * s * Complex.I) • Ec) + (Jc - (3 * -s * Complex.I) • Ec) := by module
    rw [this, PreVertexAlgebra.smul_add_right, c₁, c₂]
  rw [PreVertexAlgebra.smul_smul_right, U_eight_J] at hsum
  have h := indep_JE (a := -(l₁ + l₂))
      (b := (3 * s * Complex.I) * l₁ - (3 * s * Complex.I) * l₂ - 21600) (by
    have : (2 : ℂ) • ((-10800 : ℂ) • Ec) -
        (l₁ • (Jc - (3 * s * Complex.I) • Ec) + l₂ • (Jc - (3 * -s * Complex.I) • Ec)) = 0 := by
      rw [hsum, sub_self]
    rw [← this]; module)
  exact ⟨by linear_combination -h.1, by linear_combination -h.2⟩

theorem four_U_ne (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (χ : Fin 21 → (VOA.A cubicModel →ₐ[ℂ] ℂ)) (hχ : Function.Injective χ)
    (hω : ∀ i, χ i (VOA.mk cubicModel cubicModel.conformalVector) = tetraWeight i) :
    ∀ i, tetraWeight i = 4 → χ i (VOA.mk cubicModel cubicU) ≠ 0 := by
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  obtain ⟨χ₁, h₁, hω₁⟩ := exists_character_y (s := s) sqrt3_mul
  obtain ⟨χ₂, h₂, hω₂⟩ := exists_character_y (s := -s) neg_sqrt3_mul
  obtain ⟨hs1, hs2⟩ := four_values s sqrt3_mul h₁ h₂
  have hl₁ : χ₁ (VOA.mk cubicModel cubicU) ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hs1
    rw [h0, hs1] at hs2
    norm_num at hs2
  have hl₂ : χ₂ (VOA.mk cubicModel cubicU) ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hs1
    rw [h0, hs1] at hs2
    norm_num at hs2
  have hne : χ₁ ≠ χ₂ := by
    intro he
    rw [he] at hs1
    apply hl₂
    linear_combination hs1 / 2
  obtain ⟨j₁, hj₁⟩ := exists_table_eq hC2 hdim χ hχ χ₁
  obtain ⟨j₂, hj₂⟩ := exists_table_eq hC2 hdim χ hχ χ₂
  have hw₁ : tetraWeight j₁ = 4 := by rw [← hω j₁, ← hj₁, hω₁]
  have hw₂ : tetraWeight j₂ = 4 := by rw [← hω j₂, ← hj₂, hω₂]
  have hj12 : j₁ ≠ j₂ := by
    intro h; apply hne; rw [hj₁, hj₂, h]
  intro i hi
  have hcases : i = j₁ ∨ i = j₂ := by
    rcases tetraWeight_four i hi with h | h <;>
    rcases tetraWeight_four j₁ hw₁ with h1 | h1 <;>
    rcases tetraWeight_four j₂ hw₂ with h2 | h2 <;>
    first
      | exact Or.inl (h.trans h1.symm)
      | exact Or.inr (h.trans h2.symm)
      | exact absurd (h1.trans h2.symm) hj12
  rcases hcases with rfl | rfl
  · rw [← hj₁]; exact hl₁
  · rw [← hj₂]; exact hl₂

/-! ### The sign vector of `V₈⁻` -/

abbrev eS : (signSubmodule 4 four_ge_one).carrier := signVector 4 four_ge_one

theorem cubicSign_U_low (k : ℤ) (hk : k = 6 ∨ k = 7 ∨ k = 8) :
    mode (cubicSign.YM cubicU) k eS = 0 := by
  apply Subtype.ext
  rw [cubicSign_act_U]
  change (V2m 4 four_ge_one).smul Uc k hV = 0
  rcases hk with rfl | rfl | rfl
  · rw [inner_6]; simp [Z6, evalSt_cons, sector, PlusUnitary.evRc_nil, latStateGen_zero_boson]
  · rw [inner_7]; simp [Z7, evalSt_cons, sector, PlusUnitary.evRc_nil, latStateGen_zero_boson]
  · rw [inner_8]; simp [Z8, evalSt_cons, sector, PlusUnitary.evRc_nil, latStateGen_zero_boson]

theorem cubicSign_omega_mode (p : ℤ) (x : (signSubmodule 4 four_ge_one).carrier) :
    ((mode (cubicSign.YM cubicModel.conformalVector) p x : (signSubmodule 4 four_ge_one).carrier) :
      LatModuleGen (latP 4)) = (V2m 4 four_ge_one).smul ωc p (x : LatModuleGen (latP 4)) := by
  rw [cubicSign_YM, fixedEquivKlein_symm_omega]
  rfl

theorem hV_eq_st : hV = st (liftR [(1, [0])]) := by
  rw [st_liftR]
  exact bosonState_eq_evR 4

theorem cert_S :
    normR (scaleR 2 (neutralAction omR (-2) 0 (liftR [(1, [0])])) ++
      scaleR (-4) (neutralAction omR (-1) 0 (neutralAction omR 0 0 (liftR [(1, [0])]))) ++
      neutralAction omR 0 0 (neutralAction omR 0 0 (neutralAction omR 0 0 (liftR [(1, [0])])))) =
      [] := by
  decide +kernel

/-! ### `U` is primary: the commutator with `ω` -/

theorem cubicU_omega_high (i : ℤ) (hi : 2 ≤ i) :
    cubicModel.smul cubicModel.conformalVector i cubicU = 0 := by
  have h0 := fixedNine_nonzero_primary.2.2 (i - 1) (by omega)
  rw [VertexOperatorAlgebra.L_def, show i - 1 + 1 = i by ring] at h0
  have h1 := fixedEquivKlein_hom.map_smul
    (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector i fixedNine
  have h2 : (orbifoldVOA (Subgroup.zpowers plusCubic)).smul
      (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector i fixedNine = 0 := h0
  rw [h2, LinearMap.map_zero, LinearEquiv.coe_coe, fixedEquivKlein_omega] at h1
  exact h1.symm

theorem cubicU_omega_one :
    cubicModel.smul cubicModel.conformalVector 1 cubicU = (9 : ℂ) • cubicU := by
  have h := cubicModel.L0_grading cubicU cubicU_mem
  change mode (cubicModel.Y cubicModel.conformalVector) 1 cubicU = _
  rw [h]; norm_num

theorem cubicU_omega_zero :
    cubicModel.smul cubicModel.conformalVector 0 cubicU = cubicModel.L (-1) cubicU := by
  rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  norm_num

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- `[ω₍ₚ₎, U₍ₙ₎] = (8p - n) U₍ₚ₊ₙ₋₁₎` on every weak module. -/
theorem omega_U_comm (A : WeakModule cubicModel M) (p n : ℤ) (x : M) :
    mode (A.YM cubicModel.conformalVector) p (mode (A.YM cubicU) n x) =
      mode (A.YM cubicU) n (mode (A.YM cubicModel.conformalVector) p x) +
        ((8 * p - n : ℤ) : ℂ) • mode (A.YM cubicU) (p + n - 1) x := by
  have hc := mode_commutator A cubicModel.conformalVector cubicU x p n
  have hsupp : (Function.support fun i : ℤ => cbz p i • mode (A.YM
      (cubicModel.smul cubicModel.conformalVector i cubicU)) (p + n - i) x) ⊆
      ((({0, 1} : Finset ℤ)) : Set ℤ) := by
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    apply hi
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [cubicU_omega_high i (by omega), map_zero]
      simp
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num)] at hc
  rw [cbz_zero, one_smul, cubicU_omega_zero, PlusRat3.T_mode A, PlusRat3.cbz_one', cubicU_omega_one,
    map_smul] at hc
  have e1 : p + n - 0 - 1 = p + n - 1 := by ring
  rw [e1, show p + n - 0 = p + n by ring] at hc
  rw [← sub_eq_iff_eq_add', hc]
  simp only [LinearMap.smul_apply, mode_smul]
  push_cast
  module

theorem U_omega_comm (A : WeakModule cubicModel M) (p n k : ℤ) (hk : k = p + n - 1) (x : M) :
    mode (A.YM cubicU) n (mode (A.YM cubicModel.conformalVector) p x) =
      mode (A.YM cubicModel.conformalVector) p (mode (A.YM cubicU) n x) -
        ((8 * p - n : ℤ) : ℂ) • mode (A.YM cubicU) k x := by
  rw [omega_U_comm A p n x, hk]; abel

/-- The level-three singular combination `S u = 2 L₋₃u - 4 L₋₂L₋₁u + L₋₁³u`. -/
def virS (A : WeakModule cubicModel M) (u : M) : M :=
  (2 : ℂ) • mode (A.YM cubicModel.conformalVector) (-2) u -
    (4 : ℂ) • mode (A.YM cubicModel.conformalVector) (-1)
      (mode (A.YM cubicModel.conformalVector) 0 u) +
    mode (A.YM cubicModel.conformalVector) 0 (mode (A.YM cubicModel.conformalVector) 0
      (mode (A.YM cubicModel.conformalVector) 0 u))

/-- The `U₍₅₎`-coefficient cancels: `U₍₈₎ S u = 0` once `U₍₈₎u = U₍₇₎u = U₍₆₎u = 0`. -/
theorem U_eight_virS (A : WeakModule cubicModel M) {u : M}
    (h8 : mode (A.YM cubicU) 8 u = 0) (h7 : mode (A.YM cubicU) 7 u = 0)
    (h6 : mode (A.YM cubicU) 6 u = 0) : mode (A.YM cubicU) 8 (virS A u) = 0 := by
  have e1 : mode (A.YM cubicU) 8 (mode (A.YM cubicModel.conformalVector) (-2) u) =
      (24 : ℂ) • mode (A.YM cubicU) 5 u := by
    rw [U_omega_comm A (-2) 8 5 (by norm_num), h8, map_zero,
      show ((8 * -2 - 8 : ℤ) : ℂ) = -24 by norm_num]
    module
  have e2 : mode (A.YM cubicU) 8 (mode (A.YM cubicModel.conformalVector) 0 u) = 0 := by
    rw [U_omega_comm A 0 8 7 (by norm_num), h8, h7, map_zero, smul_zero, sub_zero]
  have e3 : mode (A.YM cubicU) 6 (mode (A.YM cubicModel.conformalVector) 0 u) =
      (6 : ℂ) • mode (A.YM cubicU) 5 u := by
    rw [U_omega_comm A 0 6 5 (by norm_num), h6, map_zero,
      show ((8 * 0 - 6 : ℤ) : ℂ) = -6 by norm_num]
    module
  have e4 : mode (A.YM cubicU) 8 (mode (A.YM cubicModel.conformalVector) (-1)
      (mode (A.YM cubicModel.conformalVector) 0 u)) = (96 : ℂ) • mode (A.YM cubicU) 5 u := by
    rw [U_omega_comm A (-1) 8 6 (by norm_num), e2, map_zero, e3,
      show ((8 * -1 - 8 : ℤ) : ℂ) = -16 by norm_num]
    module
  have e5 : mode (A.YM cubicU) 7 (mode (A.YM cubicModel.conformalVector) 0 u) = 0 := by
    rw [U_omega_comm A 0 7 6 (by norm_num), h7, h6, map_zero, smul_zero, sub_zero]
  have e6 : mode (A.YM cubicU) 8 (mode (A.YM cubicModel.conformalVector) 0
      (mode (A.YM cubicModel.conformalVector) 0 u)) = 0 := by
    rw [U_omega_comm A 0 8 7 (by norm_num), e2, e5, map_zero, smul_zero, sub_zero]
  have e7 : mode (A.YM cubicU) 7 (mode (A.YM cubicModel.conformalVector) 0
      (mode (A.YM cubicModel.conformalVector) 0 u)) = (42 : ℂ) • mode (A.YM cubicU) 5 u := by
    rw [U_omega_comm A 0 7 6 (by norm_num), e5, e3, map_zero,
      show ((8 * 0 - 7 : ℤ) : ℂ) = -7 by norm_num]
    module
  have e8 : mode (A.YM cubicU) 8 (mode (A.YM cubicModel.conformalVector) 0
      (mode (A.YM cubicModel.conformalVector) 0 (mode (A.YM cubicModel.conformalVector) 0 u))) =
      (336 : ℂ) • mode (A.YM cubicU) 5 u := by
    rw [U_omega_comm A 0 8 7 (by norm_num), e6, e7, map_zero,
      show ((8 * 0 - 8 : ℤ) : ℂ) = -8 by norm_num]
    module
  simp only [virS, map_add, map_sub, map_smul]
  rw [e1, e4, e8]
  module

/-! ### Word transfer from the sign vector -/

/-- A `U`-letter. -/
noncomputable abbrev LU (k : ℤ) : HomogeneousLetter cubicModel := ⟨cubicU, 9, k, cubicU_mem⟩

/-- An `ω`-letter. -/
noncomputable abbrev Lw (p : ℤ) : HomogeneousLetter cubicModel :=
  ⟨cubicModel.conformalVector, 2, p, cubicModel.conformal_mem⟩

/-- The word combination of `S`. -/
noncomputable def FS : WComb cubicModel := [((2 : ℂ), [Lw (-2)]), ((-4 : ℂ), [Lw (-1), Lw 0]),
  ((1 : ℂ), [Lw 0, Lw 0, Lw 0])]

theorem FS_deg : WDeg FS ((3 : ℕ) : ℤ) := by
  intro p hp
  simp only [FS, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [homogeneousDegree]

theorem evalW_FS (A : WeakModule cubicModel M) (u : M) : evalW A FS u = virS A u := by
  simp only [evalW, FS, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    homogeneousWord, LinearMap.comp_apply, LinearMap.id_apply, virS]
  module

theorem evalW_LU (A : WeakModule cubicModel M) (k : ℤ) (u : M) :
    evalW A [((1 : ℂ), [LU k])] u = mode (A.YM cubicU) k u := by
  simp [evalW, homogeneousWord]

theorem LU_deg (k : ℤ) (d : ℕ) (hd : (d : ℤ) = 8 - k) : WDeg [((1 : ℂ), [LU k])] (d : ℤ) := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  simp [homogeneousDegree, hd]
  ring

theorem cubicSign_FS : evalW cubicSign FS eS = 0 := by
  rw [evalW_FS]
  apply Subtype.ext
  simp only [virS, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    cubicSign_omega_mode, ZeroMemClass.coe_zero]
  change (2 : ℂ) • (V2m 4 four_ge_one).smul ωc (-2) hV -
    (4 : ℂ) • (V2m 4 four_ge_one).smul ωc (-1) ((V2m 4 four_ge_one).smul ωc 0 hV) +
    (V2m 4 four_ge_one).smul ωc 0 ((V2m 4 four_ge_one).smul ωc 0
      ((V2m 4 four_ge_one).smul ωc 0 hV)) = 0
  rw [hV_eq_st]
  simp only [smul_ω_st]
  have h := st_eq_of_normR (P := scaleR 2 (neutralAction omR (-2) 0 (liftR [(1, [0])])) ++
      scaleR (-4) (neutralAction omR (-1) 0 (neutralAction omR 0 0 (liftR [(1, [0])]))) ++
      neutralAction omR 0 0 (neutralAction omR 0 0 (neutralAction omR 0 0 (liftR [(1, [0])]))))
    (Q := []) (by rw [cert_S]; rfl)
  rw [st_append, st_append, st_scaleR, st_scaleR] at h
  have h0 : st ([] : RawPoly ℕ) = 0 := by
    simp [st, PlusUnitary.evRc_nil, sector, latStateGen_zero_boson]
  rw [h0] at h
  rw [← h]
  push_cast
  module

/-- The three low `U`-vanishings, and `S u` is a top vector of weight four. -/
theorem cubic_low_transfer (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (A : WeakModule cubicModel M) {u : M} (hu : u ∈ Omega A) (hL : L0 A u = (1 : ℂ) • u)
    (hlow : ∀ μ : ℂ, μ.re < (1 : ℂ).re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0) :
    mode (A.YM cubicU) 8 u = 0 ∧ mode (A.YM cubicU) 7 u = 0 ∧ mode (A.YM cubicU) 6 u = 0 ∧
      virS A u ∈ Omega A ∧ L0 A (virS A u) = (4 : ℂ) • virS A u := by
  obtain ⟨χ, hχ, hω⟩ := OrbRat6.cubicZhuCharacterTable_holds
  have hχx := top_scalar_of_unique hC2 hdim χ hχ hω A hu hL (i := 1) tetraWeight_eq_one
  have hχe := top_scalar_of_unique hC2 hdim χ hχ hω cubicSign signVector_mem_Omega_cubic
    cubicSign_L0 (i := 1) tetraWeight_eq_one
  have hmid : ∀ k : ℕ, 0 < k → k < 3 → ∀ v : M, v ∈ Omega A →
      L0 A v = (1 + (k : ℂ)) • v → v = 0 := fun k hk0 hk v hv hvL =>
    top_eq_zero_of_table hC2 hdim χ hχ hω A hv hvL 0 (map_zero _)
      (fun i hi => absurd hi (tetraWeight_ne_low i k hk0 hk))
  have WT := word_transfer A cubicSign (fun r => χ 1 r) hu signVector_mem_Omega_cubic hχx hχe
    hL cubicSign_L0 signVector_ne_zero' hlow 3 hmid
  have hU : ∀ (k : ℤ) (d : ℕ), (d : ℤ) = 8 - k → d < 3 → (k = 6 ∨ k = 7 ∨ k = 8) →
      mode (A.YM cubicU) k u = 0 := by
    intro k d hd hd3 hk
    have h := (WT d hd3.le _ (LU_deg k d hd) (by rw [evalW_LU]; exact cubicSign_U_low k hk)).2 hd3
    rwa [evalW_LU] at h
  refine ⟨hU 8 0 (by norm_num) (by norm_num) (by norm_num),
    hU 7 1 (by norm_num) (by norm_num) (by norm_num),
    hU 6 2 (by norm_num) (by norm_num) (by norm_num), ?_, ?_⟩
  · have h := (WT 3 le_rfl FS FS_deg cubicSign_FS).1
    rwa [evalW_FS] at h
  · have h := evalW_eigen A hL FS FS_deg
    rw [evalW_FS] at h
    rw [h]; norm_num

/-- **The Virasoro obstruction vanishes**: on every weight-one top vector of a weak
`cubicModel`-module with no generalized weights below one, `S u = 0`. -/
theorem cubic_singular_eq_zero (hC2 : C2Cofinite cubicModel) (hdim : CubicZhuDimensionBound)
    (A : WeakModule cubicModel M) {u : M} (hu : u ∈ Omega A) (hL : L0 A u = (1 : ℂ) • u)
    (hlow : ∀ μ : ℂ, μ.re < (1 : ℂ).re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0) :
    virS A u = 0 := by
  obtain ⟨χ, hχ, hω⟩ := OrbRat6.cubicZhuCharacterTable_holds
  obtain ⟨h8, h7, h6, hSΩ, hSL⟩ := cubic_low_transfer hC2 hdim A hu hL hlow
  refine top_eq_zero_of_table hC2 hdim χ hχ hω A hSΩ hSL (VOA.mk cubicModel cubicU) ?_
    (four_U_ne hC2 hdim χ hχ hω)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 cubicU_mem, show (9 : ℤ) - 1 + 0 = 8 by norm_num]
  exact U_eight_virS A h8 h7 h6

/-! ### The sharpened residual -/

/-- OPEN: `TopCyclicVanishing cubicModel 1 4`, with the proved Virasoro and low-`U` facts
available as hypotheses. -/
def TopCyclicFourOneResidual : Prop :=
  ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule cubicModel M) (u v : M),
    u ∈ Omega A → L0 A u = (1 : ℂ) • u →
    (∀ μ : ℂ, μ.re < (1 : ℂ).re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0) →
    virS A u = 0 → mode (A.YM cubicU) 8 u = 0 → mode (A.YM cubicU) 7 u = 0 →
    mode (A.YM cubicU) 6 u = 0 →
    v ∈ Omega A → L0 A v = (4 : ℂ) • v → v ∈ PlusRational.cyclic A u → v = 0

/-- The `(4 ↘ 1)` cyclic statement from the sharpened residual. -/
theorem topCyclicVanishing_one_four (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (h : TopCyclicFourOneResidual) :
    TopCyclicVanishing cubicModel 1 4 := by
  intro M _ _ A u v hu hL hlow hv hvL hvc
  obtain ⟨h8, h7, h6, -, -⟩ := cubic_low_transfer hC2 hdim A hu hL hlow
  exact h A u v hu hL hlow (cubic_singular_eq_zero hC2 hdim A hu hL hlow) h8 h7 h6 hv hvL hvc

/-- `CubicNonVacuumPairs` from the sharpened `(4 ↘ 1)` residual and the `(9/4 ↘ 1/4)`
cyclic statement. -/
theorem cubicNonVacuumPairs_of_residuals (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (h41 : TopCyclicFourOneResidual)
    (h94 : TopCyclicVanishing cubicModel (1 / 4) (9 / 4)) : CubicNonVacuumPairs :=
  cubicNonVacuumPairs_of_topCyclic hC2 ⟨topCyclicVanishing_one_four hC2 hdim h41, h94⟩

/-- Rationality-from-`C₂` of the tetrahedral model from the Zhu dimension bound and the two
residuals. -/
theorem cubicModelRationalOfC2_of_residuals (hdim : CubicZhuDimensionBound)
    (h41 : TopCyclicFourOneResidual) (h94 : TopCyclicVanishing cubicModel (1 / 4) (9 / 4)) :
    CubicModelRationalOfC2 := fun hC2 =>
  OrbRat7.cubicModelRationalOfC2_of_dim hdim
    (cubicNonVacuumPairs_of_residuals hC2 hdim h41 h94) hC2

end Cubic

end VOA.Classification.COne.OrbRat8
