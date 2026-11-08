import VOA.Moonshine.AutFaithfulVnat
import VOA.Moonshine.SigmaTopSigma
import VOA.Moonshine.SigmaTopTT

/-!
# Explicit norm-four Ising vectors

The cocycle sign is retained: the parameter satisfies `s ^ 2 * ε(α, -α) = 1`.
All quadratic letters use the repository's orthonormal `chargeCoord` normalisation.
`isingQuad (chargeCoord leech α) (chargeCoord leech β)` equals `dV α β`, whose underlying
lattice state is exactly `quadH`. No `lv` coordinates or implicit cocycle-sign choices occur.

This proves the Ising-vector identities and spanning results of `MOON_MONSTER`. The explicit
spans use the stronger results already extracted in `SigmaTopSource` and `SigmaTopTT`.
Spectral annihilation and rigidity are not asserted here.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.Moonshine.TrialityTw VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.SigmaExist
open scoped TensorProduct

/-- Minimal Leech vectors have these seven possible inner products. -/
theorem leech_form_cases_of_normFour {α β : leech.carrier}
    (hα : leech.form α α = 4) (hβ : leech.form β β = 4) :
    leech.form α β = -4 ∨ leech.form α β = -2 ∨ leech.form α β = -1 ∨
      leech.form α β = 0 ∨ leech.form α β = 1 ∨ leech.form α β = 2 ∨
      leech.form α β = 4 := by
  have hs := LinearMap.BilinForm.isSymm_def.mp leech.isSymm β α
  have hsub : leech.form (α - β) (α - β) = 8 - 2 * leech.form α β := by
    simp only [map_sub, LinearMap.sub_apply, hα, hβ, hs]
    ring
  have hadd : leech.form (α + β) (α + β) = 8 + 2 * leech.form α β := by
    simp only [map_add, LinearMap.add_apply, hα, hβ, hs]
    ring
  have hn : ∀ v : leech.carrier, 0 ≤ leech.form v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (leech_posDef v hv).le
  have hm := hn (α - β)
  have hp := hn (α + β)
  have hrm := leech_no_roots (α - β)
  have hrp := leech_no_roots (α + β)
  omega

/-- Equality in the positive extreme characterises equal minimal vectors. -/
theorem leech_form_four_iff_of_normFour {α β : leech.carrier}
    (hα : leech.form α α = 4) (hβ : leech.form β β = 4) :
    leech.form α β = 4 ↔ β = α := by
  constructor
  · intro h
    by_contra hne
    have hp := leech_posDef (β - α) (sub_ne_zero.mpr hne)
    have hs := LinearMap.BilinForm.isSymm_def.mp leech.isSymm β α
    simp only [map_sub, LinearMap.sub_apply, hα, hβ, hs, h] at hp
    omega
  · rintro rfl
    exact hα

/-- Equality in the negative extreme characterises opposite minimal vectors. -/
theorem leech_form_neg_four_iff_of_normFour {α β : leech.carrier}
    (hα : leech.form α α = 4) (hβ : leech.form β β = 4) :
    leech.form α β = -4 ↔ β = -α := by
  have h := leech_form_four_iff_of_normFour hα (β := -β)
    (by simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hβ)
  simpa only [map_neg, neg_eq_iff_eq_neg, neg_inj] using h

/-- The self-product keeps the cocycle coefficient, without choosing its sign. -/
theorem frameX0P_one_frameX0P_self {α : leech.carrier} (hα : leech.form α α = 4) :
    leechVOAPlus.smul (frameX0P α) 1 (frameX0P α) =
      latticeCocycle leech α (-α) • (dV α α : VPlus) := by
  apply Subtype.ext
  rw [plus_smul_coe]
  change leechVOA.smul (latChargeGen leech α + latChargeGen leech (-α)) 1
    (latChargeGen leech α + latChargeGen leech (-α)) =
      latticeCocycle leech α (-α) • quadH leech leech_even leech_posDef α α
  have hee := LatticeTwisted.smul_echg_echg leech leech_even leech_posDef α α 1
  have hef := LatticeTwisted.smul_echg_echg leech leech_even leech_posDef α (-α) 1
  have hfe := LatticeTwisted.smul_echg_echg leech leech_even leech_posDef (-α) α 1
  have hff := LatticeTwisted.smul_echg_echg leech leech_even leech_posDef (-α) (-α) 1
  simp only [map_neg, LinearMap.neg_apply, neg_neg, hα] at hee hef hfe hff
  rw [if_neg (by norm_num), TensorProduct.zero_tmul, smul_zero] at hee hff
  rw [if_pos (by norm_num), show (-1 - 1 - -4 : ℤ).toNat = 2 from rfl,
    add_neg_cancel] at hef
  rw [if_pos (by norm_num), show (-1 - 1 - -4 : ℤ).toNat = 2 from rfl,
    neg_add_cancel] at hfe
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right]
  change (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _ +
    (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _ +
    ((latticeVOAGen leech leech_even leech_posDef).smul _ 1 _ +
      (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _) = _
  rw [hee, hef, hfe, hff, zero_add, add_zero, latticeCocycle_neg_self_comm,
    ← smul_add, ← TensorProduct.add_tmul, quadH_self, vSchur_two, vSchur_two,
    WpC2.vVar_neg', WpC2.vVar_neg', neg_mul_neg]
  congr 2
  module

/-- The leading product at inner product minus two. -/
theorem frameX0P_one_frameX0P_of_form_neg_two {α β : leech.carrier}
    (h : leech.form α β = -2) :
    leechVOAPlus.smul (frameX0P α) 1 (frameX0P β) =
      latticeCocycle leech α β • frameX0P (α + β) := by
  simpa [h] using frameX0P_smul_frameX0P_of_neg α β (by omega)

/-- The leading product at inner product two, with the charge written as `β - α`. -/
theorem frameX0P_one_frameX0P_of_form_two {α β : leech.carrier}
    (h : leech.form α β = 2) :
    leechVOAPlus.smul (frameX0P α) 1 (frameX0P β) =
      latticeCocycle leech α (-β) • frameX0P (β - α) := by
  have hn : frameX0P (-β) = frameX0P β := by
    apply Subtype.ext
    change latChargeGen leech (-β) + latChargeGen leech (- -β) = _
    rw [neg_neg, add_comm]
    rfl
  have hx : frameX0P (α + -β) = frameX0P (β - α) := by
    apply Subtype.ext
    change latChargeGen leech (α + -β) + latChargeGen leech (-(α + -β)) = _
    rw [show α + -β = -(β - α) by abel, neg_neg, add_comm]
    rfl
  simpa only [hn, hx] using
    frameX0P_one_frameX0P_of_form_neg_two (α := α) (β := -β) (by rw [map_neg, h])

/-- Inner products zero or plus/minus one give zero Griess product. -/
theorem frameX0P_one_frameX0P_of_form_small {α β : leech.carrier}
    (hlo : -1 ≤ leech.form α β) (hhi : leech.form α β ≤ 1) :
    leechVOAPlus.smul (frameX0P α) 1 (frameX0P β) = 0 := by
  apply Subtype.ext
  rw [plus_smul_coe]
  change leechVOA.smul (latChargeGen leech α + latChargeGen leech (-α)) 1
    (latChargeGen leech β + latChargeGen leech (-β)) = 0
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right]
  rw [leechVOA_smul_latChargeGen_eq_zero α β (by omega),
    leechVOA_smul_latChargeGen_eq_zero α (-β) (by simp only [map_neg]; omega),
    leechVOA_smul_latChargeGen_eq_zero (-α) β
      (by simp only [map_neg, LinearMap.neg_apply]; omega),
    leechVOA_smul_latChargeGen_eq_zero (-α) (-β)
      (by simp only [map_neg, LinearMap.neg_apply, neg_neg]; omega)]
  simp

/-- Quadratic letters acting on any charged vacuum pair. -/
theorem quadH_one_frameX0P (u v β : leech.carrier) :
    leechVOAPlus.smul (dV u v : VPlus) 1 (frameX0P β) =
      ((leech.form u β : ℂ) * (leech.form v β : ℂ)) • frameX0P β :=
  actV_dV u v β

/-- Commutativity on the weight-two untwisted block. -/
theorem plus_one_comm {x y : VPlus} (hx : x ∈ leechVOAPlus.grading 2)
    (hy : y ∈ leechVOAPlus.grading 2) :
    leechVOAPlus.smul x 1 y = leechVOAPlus.smul y 1 x := by
  have hx' : ((x, 0) : Vnat) ∈ VnatVOA.grading 2 := by
    rw [VnatVOA_grading, mem_gradingNat]
    exact ⟨hx, Submodule.zero_mem _⟩
  have hy' : ((y, 0) : Vnat) ∈ VnatVOA.grading 2 := by
    rw [VnatVOA_grading, mem_gradingNat]
    exact ⟨hy, Submodule.zero_mem _⟩
  have h := congrArg (fun z : VnatVOA.grading 2 => (z : Vnat).1)
    (VnatVOA.griessMul_comm_of_grading1_eq_bot VnatVOA_grading_one ⟨(x, 0), hx'⟩
      ⟨(y, 0), hy'⟩)
  simpa only [VertexOperatorAlgebra.griessMul_coe, VnatVOA_smul_inl] using h

/-- Charged minimal vectors acting on quadratic letters. -/
theorem frameX0P_one_quadH {α : leech.carrier} (hα : leech.form α α = 4)
    (u v : leech.carrier) :
    leechVOAPlus.smul (frameX0P α) 1 (dV u v : VPlus) =
      ((leech.form u α : ℂ) * (leech.form v α : ℂ)) • frameX0P α := by
  rw [plus_one_comm (frameX0P_mem_grading_two hα) (dV_mem_grading u v)]
  exact quadH_one_frameX0P u v α

/-- The four contractions in the quadratic Griess product. -/
theorem quadState_one_quadState (a b c d : Fin (rank leech)) :
    leechVOAPlus.smul (qP a b) 1 (qP c d) =
      (if b = c then qP a d else 0) + (if b = d then qP a c else 0) +
      (if a = c then qP b d else 0) + (if a = d then qP b c else 0) := by
  classical
  apply Subtype.ext
  rw [plus_smul_coe, qP_coe]
  have hq : ∀ i j, ((qP i j : VPlus) : LatModuleGen leech) =
      latStateGen leech (MvPolynomial.X (0, i) * MvPolynomial.X (0, j)) 0 := by
    intro i j
    exact quadSt_eq leech leech_even leech_posDef i j
  rw [hq]
  change (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _ = _
  rw [smul_quadState_one]
  have hvars : ∀ z ∈ (MvPolynomial.X (0, c) * MvPolynomial.X (0, d) :
      FockN (rank leech)).vars, z.1 < 1 := by
    intro z hz
    have hz' := MvPolynomial.vars_mul _ _ hz
    simp only [Finset.mem_union, MvPolynomial.vars_X, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl <;> omega
  rw [nprod_currentN_neg_two a b _ 1 hvars]
  simp only [chargeCoord_zero, zero_mul, zero_smul, zero_add, Finset.sum_range_one,
    Nat.cast_zero, one_smul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  simp only [Submodule.coe_add, Submodule.coe_zero, apply_ite Subtype.val, hq]
  simp only [Pi.single_apply, Prod.mk.injEq, true_and]
  simp only [latStateGen, mul_add, mul_ite, ite_mul, one_mul,
    mul_one, mul_zero, zero_mul, TensorProduct.add_tmul,
    apply_ite (fun p : FockN (rank leech) => p ⊗ₜ[ℂ] eGen leech 0),
    TensorProduct.zero_tmul]
  simp only [eq_comm, add_assoc]

/-- A quadratic row in orthonormal Heisenberg coordinates. -/
noncomputable def isingQuadRow (u : Fin (rank leech) → ℂ) (b : Fin (rank leech)) :
    VPlus := ∑ a, u a • qP a b

/-- `Q(u,v)` for arbitrary complex Heisenberg coordinates. -/
noncomputable def isingQuad (u v : Fin (rank leech) → ℂ) : VPlus :=
  ∑ b, v b • isingQuadRow u b

/-- Lattice quadratic states agree with the coordinate bilinear construction. -/
theorem isingQuad_chargeCoord (α β : leech.carrier) :
    isingQuad (chargeCoord leech α) (chargeCoord leech β) = (dV α β : VPlus) := by
  classical
  rw [dV_eq_sum]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [isingQuad, Finset.sum_comm]
  simp only [isingQuadRow, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
    rw [mul_comm]
    rfl

/-- Four contractions with an arbitrary quadratic state in the left slot. -/
theorem isingQuad_one_qP (u v : Fin (rank leech) → ℂ) (c d : Fin (rank leech)) :
    leechVOAPlus.smul (isingQuad u v) 1 (qP c d) =
      v c • isingQuadRow u d + v d • isingQuadRow u c +
      u c • isingQuadRow v d + u d • isingQuadRow v c := by
  classical
  simp only [isingQuad, isingQuadRow, smul_sum_left,
    PreVertexAlgebra.smul_smul_left, quadState_one_quadState, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  simp only [smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero]
  simp only [mul_comm]

/-- The four-contraction formula for arbitrary complex Heisenberg coordinates. -/
theorem isingQuad_one_isingQuad (u v w z : Fin (rank leech) → ℂ) :
    leechVOAPlus.smul (isingQuad u v) 1 (isingQuad w z) =
      (∑ c, w c * v c) • isingQuad u z +
      (∑ d, z d * v d) • isingQuad u w +
      (∑ c, w c * u c) • isingQuad v z +
      (∑ d, z d * u d) • isingQuad v w := by
  classical
  have hrow : ∀ d, leechVOAPlus.smul (isingQuad u v) 1 (isingQuadRow w d) =
      (∑ c, w c * v c) • isingQuadRow u d +
      v d • isingQuad u w +
      (∑ c, w c * u c) • isingQuadRow v d + u d • isingQuad v w := by
    intro d
    conv_lhs => arg 4; rw [isingQuadRow]
    simp only [smul_sum_right', PreVertexAlgebra.smul_smul_right,
      isingQuad_one_qP, smul_add, smul_smul, Finset.sum_add_distrib]
    simp only [← Finset.sum_smul]
    simp only [isingQuad, Finset.smul_sum, smul_smul, mul_comm]
  conv_lhs => arg 4; rw [isingQuad]
  rw [smul_sum_right']
  simp only [PreVertexAlgebra.smul_smul_right, hrow, smul_add, smul_smul,
    Finset.sum_add_distrib]
  simp only [← Finset.sum_smul]
  simp only [isingQuad, Finset.smul_sum, smul_smul, mul_comm]

/-- The complex quadratic construction is symmetric. -/
theorem isingQuad_symm (u v : Fin (rank leech) → ℂ) :
    isingQuad u v = isingQuad v u := by
  classical
  have hq : ∀ a b, qP a b = qP b a := by
    intro a b
    apply Subtype.ext
    change quadSt leech leech_even leech_posDef a b =
      quadSt leech leech_even leech_posDef b a
    rw [quadSt_eq, quadSt_eq, mul_comm]
  simp only [isingQuad, isingQuadRow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [mul_comm, hq]

/-- The quadratic zero-mode action, with arbitrary complex Heisenberg coordinates. -/
theorem quadH_one_isingQuad (α : leech.carrier) (u v : Fin (rank leech) → ℂ) :
    leechVOAPlus.smul (dV α α : VPlus) 1 (isingQuad u v) =
      (2 * ∑ a, u a * chargeCoord leech α a) •
        isingQuad (chargeCoord leech α) v +
      (2 * ∑ a, v a * chargeCoord leech α a) •
        isingQuad u (chargeCoord leech α) := by
  rw [← isingQuad_chargeCoord, isingQuad_one_isingQuad]
  rw [isingQuad_symm (chargeCoord leech α) u]
  module

/-- Every complex quadratic letter has weight two. -/
theorem isingQuad_mem_grading_two (u v : Fin (rank leech) → ℂ) :
    isingQuad u v ∈ leechVOAPlus.grading 2 := by
  classical
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (qP_mem_grading a b))

/-- Quadratic action on charged pairs, extended complex bilinearly. -/
theorem isingQuad_one_frameX0P (u v : Fin (rank leech) → ℂ) (β : leech.carrier) :
    leechVOAPlus.smul (isingQuad u v) 1 (frameX0P β) =
      ((∑ a, u a * chargeCoord leech β a) * (∑ b, v b * chargeCoord leech β b)) •
        frameX0P β := by
  classical
  simp only [isingQuad, isingQuadRow, smul_sum_left,
    PreVertexAlgebra.smul_smul_left, smul_qP_frameX0P, Finset.smul_sum, smul_smul]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  ring

/-- Charged minimal vectors act on all complex quadratic letters by the same scalar. -/
theorem frameX0P_one_isingQuad {α : leech.carrier} (hα : leech.form α α = 4)
    (u v : Fin (rank leech) → ℂ) :
    leechVOAPlus.smul (frameX0P α) 1 (isingQuad u v) =
      ((∑ a, u a * chargeCoord leech α a) * (∑ b, v b * chargeCoord leech α b)) •
        frameX0P α := by
  rw [plus_one_comm (frameX0P_mem_grading_two hα) (isingQuad_mem_grading_two u v)]
  exact isingQuad_one_frameX0P u v α

/-- The quadratic self-product has coefficient sixteen at norm four. -/
theorem quadH_one_quadH_self {α : leech.carrier} (hα : leech.form α α = 4) :
    leechVOAPlus.smul (dV α α : VPlus) 1 (dV α α : VPlus) =
      (16 : ℂ) • (dV α α : VPlus) := by
  have h := isingQuad_one_isingQuad (chargeCoord leech α) (chargeCoord leech α)
    (chargeCoord leech α) (chargeCoord leech α)
  rw [isingQuad_chargeCoord, sum_chargeCoord leech leech_posDef, hα] at h
  norm_num at h
  exact h.trans (by module)

/-- The Ising candidate in `V♮`; normalisation is imposed on `s` in theorems. -/
noncomputable def isingVec (α : leech.carrier) (s : ℂ) : Vnat :=
  ((1 / 16 : ℂ) • (dV α α : VPlus) + (s / 4) • frameX0P α, 0)

/-- The Ising candidate has weight two for every scalar parameter. -/
theorem isingVec_mem_grading_two {α : leech.carrier} (hα : leech.form α α = 4)
    (s : ℂ) : isingVec α s ∈ VnatVOA.grading 2 := by
  rw [VnatVOA_grading, mem_gradingNat]
  exact ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ (dV_mem_grading α α))
    (Submodule.smul_mem _ _ (frameX0P_mem_grading_two hα)), Submodule.zero_mem _⟩

/-- The normalised Ising candidate satisfies `o(e)e = 2e`. -/
theorem isingVec_one_self {α : leech.carrier} (hα : leech.form α α = 4) (s : ℂ)
    (hs : s ^ 2 * latticeCocycle leech α (-α) = 1) :
    VnatVOA.smul (isingVec α s) 1 (isingVec α s) = (2 : ℂ) • isingVec α s := by
  have hqx : leechVOAPlus.smul (dV α α : VPlus) 1 (frameX0P α) =
      (16 : ℂ) • frameX0P α := by
    rw [quadH_one_frameX0P, hα]
    norm_num
  have hxq : leechVOAPlus.smul (frameX0P α) 1 (dV α α : VPlus) =
      (16 : ℂ) • frameX0P α := by
    rw [frameX0P_one_quadH hα, hα]
    norm_num
  rw [isingVec, VnatVOA_smul_inl, map_zero, Prod.smul_mk, smul_zero]
  congr 1
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    quadH_one_quadH_self hα, hqx, hxq, frameX0P_one_frameX0P_self hα,
    smul_add, smul_smul]
  have hcoeff : s / 4 * (s / 4 * latticeCocycle leech α (-α)) = (1 / 16 : ℂ) := by
    linear_combination hs / 16
  rw [hcoeff]
  module

/-- Explicit spanning letters for the untwisted weight-two space. -/
theorem leechVOAPlus_grading_two_eq_span :
    leechVOAPlus.grading 2 = Submodule.span ℂ
      (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2) ∪
        frameX0P '' {α : leech.carrier | leech.form α α = 4}) := by
  apply le_antisymm
  · intro x hx
    let xp := (1 / 2 : ℂ) • (x + plusFrameAut x)
    let xm := (1 / 2 : ℂ) • (x - plusFrameAut x)
    have hf : plusFrameAut (plusFrameAut x) = x := plusFrame_plusFrame x
    have hp : xp ∈ frameSector 0 := by
      rw [mem_frameSector', Extraspecial.sgn_zero, one_smul]
      change plusFrameAut ((1 / 2 : ℂ) • (x + plusFrameAut x)) = _
      rw [Aut.map_smul_c, map_add, hf, add_comm]
    have hm : xm ∈ frameSector 1 := by
      rw [mem_frameSector', Extraspecial.sgn_one, neg_one_smul]
      change plusFrameAut ((1 / 2 : ℂ) • (x - plusFrameAut x)) = _
      rw [Aut.map_smul_c, map_sub, hf]
      change (1 / 2 : ℂ) • (plusFrameAut x - x) =
        -((1 / 2 : ℂ) • (x - plusFrameAut x))
      module
    have hfx : plusFrameAut x ∈ leechVOAPlus.grading 2 :=
      plusFrameAut.map_grading hx
    have hp2 : xp ∈ leechVOAPlus.grading 2 :=
      Submodule.smul_mem _ _ (Submodule.add_mem _ hx hfx)
    have hm2 : xm ∈ leechVOAPlus.grading 2 :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hx hfx)
    have hpS := grading_two_V0_le_span hp hp2
    have hmS := OmegaV3_le_span (show xm ∈ OmegaV3 from ⟨hm, hm2⟩)
    have hpS' : xp ∈ Submodule.span ℂ
        (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2) ∪
          frameX0P '' {α : leech.carrier | leech.form α α = 4}) := by
      apply Submodule.span_mono _ hpS
      exact Set.union_subset_union_right _
        (Set.image_mono fun α hα => (mem_halfFourChi hα).1)
    have hmS' : xm ∈ Submodule.span ℂ
        (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2) ∪
          frameX0P '' {α : leech.carrier | leech.form α α = 4}) := by
      apply Submodule.span_mono _ hmS
      exact Set.Subset.trans
        (Set.image_mono fun α hα => (mem_halfFourChi hα).1) Set.subset_union_right
    have hsum : xp + xm = x := by dsimp [xp, xm]; module
    rw [← hsum]
    exact Submodule.add_mem _ hpS' hmS'
  · rw [Submodule.span_le]
    rintro x (⟨⟨a, b⟩, rfl⟩ | ⟨α, hα, rfl⟩)
    · exact qP_mem_grading a b
    · exact frameX0P_mem_grading_two hα

/-- Explicit spanning letters for the twisted weight-two space. -/
theorem twistedPlus_grading_two_eq_span :
    plusModule.weight (2 : ℂ) = Submodule.span ℂ
      {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), y = hP v t} := by
  apply le_antisymm
  · intro y hy
    have hg : (y : Tw) ∈ TwistedSector.twGrading 24 leechT 1 := by
      have hmem : (y : Tw) ∈ (plusModule.weight ((2 : ℚ) : ℂ)).map TP.subtype :=
        ⟨y, by simpa using hy, rfl⟩
      rw [map_plusModule_weight] at hmem
      have h := TwistedSector.twWeight_levelT 24 leechT 1
      have h1 : TwistedHeisenberg.levelT 24 1 = (2 : ℚ) := by
        norm_num [TwistedSector.levelT_24]
      rw [h1] at h
      rw [← h]
      exact hmem.2
    have hs := twGrading_one_le_span hg
    have hS : {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), y = hT v t} =
        TP.subtype '' {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), y = hP v t} := by
      ext w
      constructor
      · rintro ⟨v, t, rfl⟩
        exact ⟨hP v t, ⟨v, t, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, t, rfl⟩, rfl⟩
        exact ⟨v, t, rfl⟩
    rw [hS, Submodule.span_image] at hs
    obtain ⟨y', hy', heq⟩ := hs
    rwa [show y' = y from Subtype.ext heq] at hy'
  · rw [Submodule.span_le]
    rintro _ ⟨v, t, rfl⟩
    exact hP_mem_weight v t

end VOA.Moonshine.ConwayNorton.M8
