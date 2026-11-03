import VOA.Classification.COne.OrbRat5Wt
import VOA.Classification.COne.OrbRat5Reduce

/-! # The two weight-four characters of the tetrahedral model

`g = plusCubic` acts on `V₈⁺`; on `span {J, E}` it has the eigenvalues `ζ, ζ̄` (primitive cube
roots of unity) with eigenvectors `y_s = J - 3 s i E`, `s = ±√3`.  The `ζ`-eigenspace of `g` in
`V₈⁺` is a weak module for `W = (V₈⁺)^g`; it has nothing below weight four (`low_fixed`) and its
weight-four part is the line `ℂ y_s` (`eigen_line`).  Hence `y_s` is a top eigenline and defines a
character `χ_s` of `A(W)` with `[ω] ↦ 4` (`exists_character_y`).  The two characters differ on
the weight-nine generator: `χ_{√3} = χ_{-√3}` would force `U₍₈₎ J ∈ ℂ J`, but `U₍₈₎ J = -10800 E`
(`U_eight_J`, kernel certificate).

`cubicDoubledPair_four : CubicDoubledPair 4`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat5

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2b LatMod
  OrbRat3 OrbRat2 PlusSplitting Complex

/-! ## §1 Vectors of `V₈⁺` -/

local notation "VPf" => VP 4 four_ge_one

/-- `J` and `E` as `V₈⁺` vectors. -/
abbrev J' : VPf := J 4 four_ge_one
abbrev E' : VPf := EP 4 four_ge_one
/-- `ω` of `V₈⁺`. -/
abbrev ω' : VPf := (V2mPlus 4 four_ge_one).conformalVector
abbrev L' : VPf := (V2mPlus 4 four_ge_one).smul ω' 0 ω'
abbrev A' : VPf := (V2mPlus 4 four_ge_one).smul ω' (-1) ω'
abbrev B' : VPf := (V2mPlus 4 four_ge_one).smul ω' 0 L'

theorem coe_J' : ((J' : VPf) : LatModuleGen (latP 4)) = Jc := Jc_eq
theorem coe_E' : ((E' : VPf) : LatModuleGen (latP 4)) = Ec := rfl

theorem coord_one_Jc : coordEα (latP 4) ((1 : ℤ) : (latP 4).carrier) Jc = 0 := by
  change coordEα (latP 4) _ (_ ⊗ₜ[ℂ] eGen (latP 4) 0) = 0
  rw [coordEα_apply, if_neg (fun h => by have : (1 : ℤ) = 0 := h; omega)]

theorem coord_one_Ec : coordEα (latP 4) ((1 : ℤ) : (latP 4).carrier) Ec = 1 := by
  rw [Ec, map_add]
  change coordEα (latP 4) _ (_ ⊗ₜ[ℂ] eGen (latP 4) _) +
    coordEα (latP 4) _ (_ ⊗ₜ[ℂ] eGen (latP 4) _) = 1
  rw [coordEα_apply, coordEα_apply, if_pos rfl,
    if_neg (fun h => by have : (1 : ℤ) = -1 := h; omega), add_zero]
  rfl

theorem Ec_ne_zero : Ec ≠ 0 := by
  intro h
  have := coord_one_Ec
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem g_J : plusCubic J' = (-1/2 : ℂ) • J' + (9/2 : ℂ) • E' := plusCubic_generators.1
theorem g_E : plusCubic E' = (-1/6 : ℂ) • J' + (-1/2 : ℂ) • E' := plusCubic_generators.2

theorem Jc_ne_zero : Jc ≠ 0 := by
  intro h
  have hJ : J' = 0 := Subtype.ext (by rw [coe_J', h]; rfl)
  have hg := g_J
  rw [hJ, map_zero, smul_zero, zero_add] at hg
  have hE : ((9/2 : ℂ) • E' : VPf) = 0 := hg.symm
  rcases smul_eq_zero.mp hE with h9 | h9
  · norm_num at h9
  · exact Ec_ne_zero (by rw [← coe_E', h9]; rfl)

/-- `J, E` are linearly independent in `V₈`. -/
theorem indep_JE {a b : ℂ} (h : a • Jc + b • Ec = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    have h1 := congrArg (coordEα (latP 4) ((1 : ℤ) : (latP 4).carrier)) h
    rw [map_add, map_smul, map_smul, coord_one_Jc, coord_one_Ec, smul_zero, zero_add,
      map_zero] at h1
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 one_ne_zero
  subst hb
  rw [zero_smul, add_zero] at h
  refine ⟨?_, rfl⟩
  rcases smul_eq_zero.mp h with h2 | h2
  · exact h2
  · exact absurd h2 Jc_ne_zero

theorem indep_JE' {a b : ℂ} (h : a • J' + b • E' = 0) : a = 0 ∧ b = 0 := by
  apply indep_JE
  have := congrArg (fun v : VPf => (v : LatModuleGen (latP 4))) h
  simpa [coe_J', coe_E'] using this

/-! ## §2 Fixed vectors -/

theorem g_ω : plusCubic ω' = ω' := plusCubic.map_omega
theorem g_vac : plusCubic (V2mPlus 4 four_ge_one).vacuum = (V2mPlus 4 four_ge_one).vacuum :=
  plusCubic.map_vacuum

theorem g_smul (a b : VPf) (n : ℤ) :
    plusCubic ((V2mPlus 4 four_ge_one).smul a n b) =
      (V2mPlus 4 four_ge_one).smul (plusCubic a) n (plusCubic b) := plusCubic.map_smul' a n b

theorem g_L : plusCubic L' = L' := by rw [g_smul, g_ω]
theorem g_A : plusCubic A' = A' := by rw [g_smul, g_ω]
theorem g_B : plusCubic B' = B' := by rw [g_smul, g_ω, g_L]

/-- `V₈⁺` in weights `≤ 3` is fixed by `plusCubic`. -/
theorem low_fixed {k : ℕ} (hk : k ≤ 3) {w : VPf}
    (hw : w ∈ (V2mPlus 4 four_ge_one).grading (k : ℤ)) : plusCubic w = w := by
  have hmem := plus_low_mem_span hk hw
  obtain ⟨c₁, z, hz, hcz⟩ := Submodule.mem_span_insert.mp hmem
  obtain ⟨c₂, c₃, rfl⟩ := Submodule.mem_span_pair.mp hz
  have hw' : w = c₁ • (V2mPlus 4 four_ge_one).vacuum + (c₂ • ω' + c₃ • L') := by
    apply Subtype.ext
    rw [hcz]
    rfl
  rw [hw', map_add, map_add, map_smul, map_smul, map_smul, g_vac, g_ω, g_L]

/-- Weight-four vectors of `V₈⁺`: a fixed part plus `γ J + δ E`. -/
theorem four_decomp {w : VPf} (hw : w ∈ (V2mPlus 4 four_ge_one).grading 4) :
    ∃ f : VPf, plusCubic f = f ∧ ∃ γ δ : ℂ, w = f + γ • J' + δ • E' := by
  obtain ⟨α, β, γ, δ, h⟩ := plus_four_mem hw
  refine ⟨α • A' + β • B', by rw [map_add, map_smul, map_smul, g_A, g_B], γ, δ, ?_⟩
  apply Subtype.ext
  rw [h]
  simp only [Submodule.coe_add, Submodule.coe_smul, coe_J', coe_E']
  rfl

/-! ## §3 The eigenline -/

section Eigen

variable {s : ℂ}

/-- The cube root of unity `(-1 + s i)/2` (`s² = 3`). -/
def zeta (s : ℂ) : ℂ := (-1 + s * I) / 2

/-- The eigenvector `J - 3 s i E`. -/
def ys (s : ℂ) : VPf := J' - (3 * s * I) • E'

theorem zeta_ne_one (hs : s * s = 3) : zeta s ≠ 1 := by
  intro h
  have h1 : s * I = 3 := by unfold zeta at h; linear_combination 2 * h
  have h2 : (s * I) * (s * I) = 9 := by rw [h1]; norm_num
  have h3 : (s * I) * (s * I) = -3 := by
    rw [show (s * I) * (s * I) = (s * s) * (I * I) by ring, hs, I_mul_I]; norm_num
  rw [h2] at h3
  norm_num at h3

theorem g_ys (hs : s * s = 3) : plusCubic (ys s) = zeta s • ys s := by
  rw [ys, map_sub, map_smul, g_J, g_E, zeta]
  have hI : I * I = -1 := I_mul_I
  have e1 : (9 / 2 : ℂ) + 3 * s * I / 2 = -(3 * s * I) * ((-1 + s * I) / 2) := by
    linear_combination (3 / 2 * I * I) * hs + (9 / 2) * hI
  calc (-1/2 : ℂ) • J' + (9/2 : ℂ) • E' - (3 * s * I) • ((-1/6 : ℂ) • J' + (-1/2 : ℂ) • E')
      = ((-1 + s * I) / 2) • J' + ((9 / 2 : ℂ) + 3 * s * I / 2) • E' := by module
    _ = ((-1 + s * I) / 2) • J' + (-(3 * s * I) * ((-1 + s * I) / 2)) • E' := by rw [e1]
    _ = ((-1 + s * I) / 2) • (J' - (3 * s * I) • E') := by module

theorem ys_mem : ys s ∈ (V2mPlus 4 four_ge_one).grading 4 :=
  Submodule.sub_mem _ (J_mem_grading_four 4 four_ge_one)
    (Submodule.smul_mem _ _ (EP_mem_grading 4 four_ge_one))

theorem ys_coe : ((ys s : VPf) : LatModuleGen (latP 4)) = Jc - (3 * s * I) • Ec := by
  rw [ys, Submodule.coe_sub, Submodule.coe_smul, coe_J', coe_E']

theorem ys_ne_zero : ys s ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : VPf => (v : LatModuleGen (latP 4))) h
  simp only [ys_coe, Submodule.coe_zero] at h1
  have := (indep_JE (a := 1) (b := -(3 * s * I)) (by rw [← h1]; module)).1
  exact one_ne_zero this

/-- The weight-four `ζ`-eigenspace of `plusCubic` is the line `ℂ y_s`. -/
theorem eigen_line (hs : s * s = 3) {w : VPf} (hw : w ∈ (V2mPlus 4 four_ge_one).grading 4)
    (hg : plusCubic w = zeta s • w) : ∃ c : ℂ, w = c • ys s := by
  obtain ⟨f, hf, γ, δ, rfl⟩ := four_decomp hw
  set ζ := zeta s with hζdef
  set u₁ : ℂ := ζ * γ + γ / 2 + δ / 6
  set u₂ : ℂ := ζ * δ - 9 / 2 * γ + δ / 2
  rw [map_add, map_add, map_smul, map_smul, hf, g_J, g_E] at hg
  have h1 : (1 - ζ) • f = u₁ • J' + u₂ • E' := by
    linear_combination (norm := module) hg
  have h2 := congrArg plusCubic h1
  rw [map_smul, hf, map_add, map_smul, map_smul, g_J, g_E, h1] at h2
  have h3 : (u₁ * (3 / 2) + u₂ / 6) • J' + (u₂ * (3 / 2) - 9 / 2 * u₁) • E' = 0 := by
    linear_combination (norm := module) h2
  obtain ⟨c1, c2⟩ := indep_JE' h3
  have hu₁ : u₁ = 0 := by linear_combination (1 / 2) * c1 - (1 / 18) * c2
  have hu₂ : u₂ = 0 := by linear_combination (3 / 2) * c1 + (1 / 2) * c2
  have hf0 : f = 0 := by
    rw [hu₁, hu₂, zero_smul, zero_smul, add_zero] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm (zeta_ne_one hs)
    · exact h
  have hδ : δ = -(3 * s * I) * γ := by
    have : u₁ = 0 := hu₁
    simp only [u₁, hζdef, zeta] at this
    linear_combination 6 * this
  refine ⟨γ, ?_⟩
  rw [hf0, hδ, ys]
  module

end Eigen

/-! ## §4 The eigenspace module and its character -/

section Character

open OrbRat3 ConverseUniverse PlusCharacterTable

@[reducible] local instance zhuRingCubic4 : Ring (VOA.A cubicModel) := instRingA _
@[reducible] local instance zhuAlgebraCubic4 : Algebra ℂ (VOA.A cubicModel) := instAlgebraA _

/-- `V₈⁺` as a weak module of the tetrahedral model. -/
abbrev plusAdj : WeakModule cubicModel VPf :=
  cubicRestrict (adjointWeakModule (V2mPlus 4 four_ge_one))

theorem plusAdj_mode (v : (orbifold (Subgroup.zpowers kleinCubic)).carrier) (n : ℤ) (x : VPf) :
    mode (plusAdj.YM v) n x = (V2mPlus 4 four_ge_one).smul
      ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) : VPf) n x :=
  rfl

theorem symm_fixed (v : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    plusCubic ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
      VPf) = (fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :=
  (mem_orbifold_zpowers_iff plusCubic _).mp (fixedEquivKlein.symm v).2

/-- Modes of fixed vectors preserve `g`-eigenvectors. -/
theorem g_mode_eigen {b x : VPf} (hb : plusCubic b = b) {ζ : ℂ} (hx : plusCubic x = ζ • x)
    (n : ℤ) : plusCubic ((V2mPlus 4 four_ge_one).smul b n x) =
      ζ • (V2mPlus 4 four_ge_one).smul b n x := by
  rw [g_smul, hb, hx, PreVertexAlgebra.smul_smul_right]

theorem ys_mem_Omega (hs : s * s = 3) : ys s ∈ Omega plusAdj := by
  intro β v hv n hn
  rw [plusAdj_mode]
  set b : VPf := ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
    VPf)
  have hb := cubic_grading_symm hv
  have hx : (V2mPlus 4 four_ge_one).smul b n (ys s) ∈ (V2mPlus 4 four_ge_one).grading
      (β + 4 - n - 1) := (V2mPlus 4 four_ge_one).grading_mode b hb (ys s) ys_mem n
  have hgx := g_mode_eigen (symm_fixed v) (g_ys hs) n
  by_cases hneg : β + 4 - n - 1 < 0
  · rw [(V2mPlus 4 four_ge_one).positivity _ hneg] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  · have hk : β + 4 - n - 1 = (((β + 4 - n - 1).toNat : ℕ) : ℤ) := by omega
    rw [hk] at hx
    have hfix := low_fixed (by omega) hx
    rw [hfix] at hgx
    have h0 : (zeta s - 1) • (V2mPlus 4 four_ge_one).smul b n (ys s) = 0 := by
      rw [sub_smul, ← hgx, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) (zeta_ne_one hs)
    · exact h

/-- The weight-four eigen-top gives a character of `A(W)` with `[ω] ↦ 4`. -/
theorem exists_character_y (hs : s * s = 3) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ, (∀ z, topEvaluation plusAdj (ys s) (ys_mem_Omega hs) z =
      χ z • ys s) ∧ χ (VOA.mk cubicModel cubicModel.conformalVector) = 4 := by
  obtain ⟨χ, hχ⟩ := exists_character_of_top_line plusAdj (ys_mem_Omega hs) ys_ne_zero (by
    intro k a ha
    rw [plusAdj_mode]
    set b : VPf := ((fixedEquivKlein.symm a : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
      VPf)
    have hb := cubic_grading_symm ha
    have hx := (V2mPlus 4 four_ge_one).grading_mode b hb (ys s) ys_mem (k - 1)
    rw [show k + 4 - (k - 1) - 1 = 4 by ring] at hx
    exact eigen_line hs hx (g_mode_eigen (symm_fixed a) (g_ys hs) _))
  refine ⟨χ, hχ, character_omega_of_top _ (ys_mem_Omega hs) ys_ne_zero ?_ χ hχ⟩
  rw [plusAdj_mode, fixedEquivKlein_symm_omega]
  have := (V2mPlus 4 four_ge_one).L0_grading (ys s) ys_mem
  rw [show ((4 : ℤ) : ℂ) = 4 by norm_num] at this
  exact this

/-- The weight-nine generator acts through the `V₈` modes of `weightNine`. -/
theorem plusAdj_U (x : VPf) :
    ((mode (plusAdj.YM cubicU) 8 x : VPf) : LatModuleGen (latP 4)) =
      (V2m 4 four_ge_one).smul Uc 8 (x : LatModuleGen (latP 4)) := by
  rw [plusAdj_mode, cubicU, LinearEquiv.symm_apply_apply]
  rfl

theorem sqrt3_mul : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem neg_sqrt3_mul : (-((Real.sqrt 3 : ℝ) : ℂ)) * (-((Real.sqrt 3 : ℝ) : ℂ)) = 3 := by
  rw [neg_mul_neg, sqrt3_mul]

/-- The doubled pair at weight four. -/
theorem cubicDoubledPair_four : CubicDoubledPair 4 := by
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  obtain ⟨χ₁, h₁, hω₁⟩ := exists_character_y (s := s) sqrt3_mul
  obtain ⟨χ₂, h₂, hω₂⟩ := exists_character_y (s := -s) neg_sqrt3_mul
  refine ⟨χ₁, χ₂, ?_, by rw [hω₁]; norm_num, by rw [hω₂]; norm_num⟩
  intro heq
  subst heq
  set l := χ₁ (VOA.mk cubicModel cubicU)
  have e₁ := h₁ (VOA.mk cubicModel cubicU)
  have e₂ := h₂ (VOA.mk cubicModel cubicU)
  rw [topEvaluation_mk, oLevW_homogeneous _ 0 cubicU_mem,
    show (9 : ℤ) - 1 + 0 = 8 by norm_num] at e₁ e₂
  have c₁ := congrArg (fun v : VPf => (v : LatModuleGen (latP 4))) e₁
  have c₂ := congrArg (fun v : VPf => (v : LatModuleGen (latP 4))) e₂
  simp only [plusAdj_U, Submodule.coe_smul, ys_coe] at c₁ c₂
  have hsum : (V2m 4 four_ge_one).smul Uc 8 ((2 : ℂ) • Jc) = (2 * l) • Jc := by
    have : (2 : ℂ) • Jc = (Jc - (3 * s * I) • Ec) + (Jc - (3 * -s * I) • Ec) := by module
    rw [this, PreVertexAlgebra.smul_add_right, c₁, c₂]
    module
  rw [PreVertexAlgebra.smul_smul_right, U_eight_J] at hsum
  have := (indep_JE (a := -(2 * l)) (b := 2 * (-10800 : ℂ)) (by
    rw [← sub_eq_zero.mpr hsum]; module)).2
  norm_num at this

end Character

/-- The table reduced to the `9/4` pair and the six twisted pairs. -/
theorem cubicZhuCharacterTable_of_remaining (h94 : CubicDoubledPair (9 / 4))
    (ht : CubicTwistedDoubledPairs) : CubicZhuCharacterTable :=
  cubicZhuCharacterTable_of_pairs ⟨cubicDoubledPair_four, h94⟩ ht

end VOA.Classification.COne.OrbRat5
