/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNMonsterFinalAudit
import VOA.Moonshine.MoonshineCNMonsterActionLift
import VOA.Moonshine.MoonshineLRFiniteAut
import VOA.Moonshine.MonsterGriess.ProductInvariance
import VOA.Moonshine.MonsterGriess.TrialityBasis
import VOA.Moonshine.MoonshineCNRationalSchur
import VOA.Moonshine.MoonshineCNRationalTraces

/-!
# Every automorphism of `V♮` is rational on `V♮₂`, given the commutant of `Gmat`

`Notes/monster_aut/RATIONALITY.md`, §2.5–§2.8. For every `h ∈ Aut V♮` and `u ∈ SpaceB` there is
`u' ∈ SpaceB` with `h (griessNat u) = griessNat u'` (`autVnat_rational_of_commutant`), assuming one
named input about Axiom's rational Monster, `GmatCommutantScalar`: every `ℚ`-linear endomorphism of
`SpaceB` commuting with the generated group `Gmat = ⟨Gvis, tauB⟩` is `a + b·P₀`, where `P₀` is the
`bform`-orthogonal projection onto the line of `e₁ = (I, 0, 0)` (`griessUnitProj`). Equivalently,
`Gmat` is absolutely irreducible on the `196883`-dimensional complement of `e₁`.

No group theory beyond this input is used: no Tits theorem, no `Gmat = AutO`, no order of the
Monster. The arithmetic input is the rationality of all weight-two traces
(`ConwayNorton.exists_rat_gradedAutTrace_two`, from moonshine's own Galois invariance).

## The argument
* **The unit.** `oneB = (I/4, 0, 0)` is the unit of Axiom's algebra (`gmul_oneB_left`), so
  `griessNat e₁` acts on `V♮₂` by `4`; the conformal vector `ω` acts by `L(0) = 2`; commutativity
  of the Griess product gives `griessNat e₁ = 2ω` (`griessNat_griessIdentityVec`). Hence every
  automorphism of `V♮` fixes `griessNat e₁` (`autVnat_apply_griessNat_identityVec`), every
  element of `Gmat` fixes `e₁` (`gmat_apply_identityVec`), and `P₀` commutes with `Gmat`
  (`griessUnitProj_apply_gmat`).
* **Finiteness.** `Gmat` embeds in `Aut V♮` (`gmatLift`), which is finite, so `Gmat` is finite
  (`finite_gmat`).
* **Schur span.** In the dictionary bases (`griessBasisQ`, `griessBasisC`), `σ = gmatMatrixRep` is
  a rational representation of `Gmat`, `E = 1 − P₀` is a rational idempotent commuting with it,
  and the commutant input makes `σ` scalar on the image of `E`. For `H` the matrix of `h|_{V♮₂}`:
  `P₀H = P₀` and `HP₀ = P₀` (the form `natForm` is `Aut V♮`-invariant and `h` fixes `griessNat e₁`);
  the traces `tr(σ(s⁻¹) E H) = tr((s⁻¹h)|_{V♮₂}) − tr(σ(s⁻¹)P₀)` are rational. The rationality
  criterion `Rationality.eq_map_ratCast_of_rational_traces` then shows `E H E` is rational, and
  `H = P₀ + E H E`.

## Main results
* `gmul_oneB_left`, `griessIdentityVec`, `gmul_griessIdentityVec`, `bform_griessIdentityVec_self`.
* ⭐ `griessNat_griessIdentityVec`, ⭐ `autVnat_apply_griessNat_identityVec`.
* `griessUnitProj` (`P₀`), `griessUnitProj_apply`, `griessUnitProj_apply_gmat`,
  ⭐ `GmatCommutantScalar` (the named input), `gmat_commute_griessUnitProj`.
* `gmatLift`, `gmatLift_injective`, ⭐ `finite_gmat`.
* `griessLinear`, `toMatrix_griessLinear`, `gmatMatrixRep`.
* ⭐ `autVnat_rational_of_commutant`.
* ⭐ `autVnat_mulEquiv_liftable_of_commutant` (`Aut V♮ ≃* liftableSubgroup`),
  ⭐ `autVnat_mulEquiv_autO_of_commutant_of_Gmat` (`Aut V♮ ≃* AutO` given `Gmat = AutO`).
-/

namespace VOA.Moonshine.MonsterAction

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess
open scoped TensorProduct

/-! ## §1  The unit of Axiom's Griess algebra and the vector `e₁ = (I, 0, 0)` -/

section Unit

theorem gmulA_oneB (u : SpaceB) : gmulA oneB u = MonsterGriess.Am u := by
  have h1 : MonsterGriess.Am oneB = (4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := rfl
  have h2 : MonsterGriess.xs oneB = 0 := rfl
  have h3 : MonsterGriess.Nm oneB = 0 := rfl
  rw [gmulA, h1, h2, h3]
  simp only [Pi.zero_apply, zero_mul, zero_smul, Finset.sum_const_zero, smul_zero,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, zero_div,
    add_zero, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  module

theorem gmulX_oneB (u : SpaceB) (c : ShortIdx) : gmulX oneB u c = MonsterGriess.xs u c := by
  have h1 : MonsterGriess.Am oneB = (4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := rfl
  have h2 : MonsterGriess.xs oneB = 0 := rfl
  have h3 : MonsterGriess.Nm oneB = 0 := rfl
  have hq : qf c ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ)) = 8 := by
    rw [qf, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, uQ_dotProduct_self,
      smul_eq_mul]
    norm_num
  rw [gmulX, h1, h2, h3, hq]
  simp only [qf, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.trace_zero, Matrix.zero_mulVec, dotProduct_zero, zero_div,
    sub_zero, add_zero]
  ring

theorem gmulW_oneB (u : SpaceB) : gmulW oneB u = MonsterGriess.Nm u := by
  have h1 : MonsterGriess.Am oneB = (4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := rfl
  have h2 : MonsterGriess.xs oneB = 0 := rfl
  have h3 : MonsterGriess.Nm oneB = 0 := rfl
  rw [gmulW, gmulWHalf, gmulWHalf, h1, h2, h3]
  have htr : Matrix.trace ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ)) = 6 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    norm_num
  rw [htr]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, smul_zero, Matrix.mul_zero,
    Matrix.zero_mul, sub_zero, add_zero, Matrix.mul_smul, Matrix.mul_one]
  module

/-- **`oneB = (I/4, 0, 0)` is the unit of Axiom's Griess algebra**: `oneB · u = u`. -/
theorem gmul_oneB_left (u : SpaceB) : gmul oneB u = u := by
  rw [gmul_apply, gmulFun]
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · exact gmulA_oneB u
  · exact funext (gmulX_oneB u)
  · exact gmulW_oneB u

/-- The vector `e₁ = (I, 0, 0)` of `SpaceB`: the identity matrix in the `symMat` block. -/
noncomputable def griessIdentityVec : SpaceB :=
  (⟨1, mem_symMat.2 Matrix.transpose_one⟩, 0, 0)

/-- `e₁ = 4 · oneB`. -/
theorem griessIdentityVec_eq_smul_oneB : griessIdentityVec = (4 : ℚ) • oneB := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change (1 : Matrix (Fin 24) (Fin 24) ℚ)
      = (4 : ℚ) • ((4 : ℚ)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ))
    rw [smul_smul]
    norm_num
  · change (0 : SpaceX) = (4 : ℚ) • (0 : SpaceX)
    rw [smul_zero]
  · change (0 : SpaceW) = (4 : ℚ) • (0 : SpaceW)
    rw [smul_zero]

/-- `e₁ · u = 4u` in Axiom's Griess algebra. -/
theorem gmul_griessIdentityVec (u : SpaceB) : gmul griessIdentityVec u = (4 : ℚ) • u := by
  rw [griessIdentityVec_eq_smul_oneB, map_smul, LinearMap.smul_apply, gmul_oneB_left]

/-- `bform(e₁, e₁) = tr(I) = 24`. -/
theorem bform_griessIdentityVec_self : bform griessIdentityVec griessIdentityVec = 24 := by
  rw [bform_apply]
  change Matrix.trace ((1 : Matrix (Fin 24) (Fin 24) ℚ) * 1)
      + ∑ c, (0 : SpaceX) c * (0 : SpaceX) c + ∑ j, ∑ i, (0 : SpaceW) j i * (0 : SpaceW) j i = 24
  simp [Matrix.trace_one]

end Unit

/-! ## §2  `griessNat e₁ = 2ω`, fixed by every automorphism of `V♮` -/

section FixedLine

/-- The conformal vector `ω` of `V♮`, as an element of `V♮₂`. -/
noncomputable def vnatConformalTwo : VnatVOA.grading 2 :=
  ⟨VnatVOA.conformalVector, VnatVOA.conformalVector_mem_grading_two⟩

/-- `ω × x = L(0) x = 2x` on `V♮₂`. -/
theorem griessMul_vnatConformalTwo (x : VnatVOA.grading 2) :
    VnatVOA.griessMul vnatConformalTwo x = (2 : ℂ) • x := by
  apply Subtype.ext
  have h := VnatVOA.L0_grading (x : Vnat) x.2
  rw [Submodule.coe_smul]
  exact h.trans (by norm_num)

/-- `griessNat e₁ × x = 4x` on `V♮₂`. -/
theorem griessMul_griessIdentityVec (x : VnatVOA.grading 2) :
    VnatVOA.griessMul (griessNat griessIdentityVec) x = (4 : ℂ) • x := by
  have hlin : ConwayNorton.M8.vnatGriessBilin (griessNat griessIdentityVec)
      = (4 : ℂ) • LinearMap.id := by
    refine linearMap_ext_griessNat fun v => ?_
    rw [ConwayNorton.M8.vnatGriessBilin_apply, ← griessNat_gmul, gmul_griessIdentityVec,
      griessNat_smul, LinearMap.smul_apply, LinearMap.id_apply]
    norm_num
  exact LinearMap.congr_fun hlin x

/-- ⭐ **The image of `e₁ = (I, 0, 0)` is twice the conformal vector**: `griessNat e₁ = 2ω`. -/
theorem griessNat_griessIdentityVec :
    griessNat griessIdentityVec = (2 : ℂ) • vnatConformalTwo := by
  have h1 := griessMul_griessIdentityVec vnatConformalTwo
  rw [vnat_griessMul_comm, griessMul_vnatConformalTwo] at h1
  have h2 : (2 : ℂ) • griessNat griessIdentityVec = (2 : ℂ) • ((2 : ℂ) • vnatConformalTwo) := by
    rw [h1, smul_smul]
    norm_num
  exact smul_right_injective _ (two_ne_zero : (2 : ℂ) ≠ 0) h2

/-- ⭐ **Every automorphism of `V♮` fixes `griessNat (I, 0, 0)`** (it is `2ω`). -/
theorem autVnat_apply_griessNat_identityVec (h : AutVnat) :
    h (griessNat griessIdentityVec : Vnat) = griessNat griessIdentityVec := by
  rw [griessNat_griessIdentityVec, Submodule.coe_smul, autVnat_map_smul]
  congr 1
  exact h.map_omega

end FixedLine

/-! ## §3  The generated group `Gmat`: lift, finiteness, the fixed vector `e₁` -/

section Gmat

/-- `Gmat = ⟨Gvis, tauB⟩` lies in the liftable subgroup of `AutO`. -/
noncomputable def gmatToLiftable : Generated.Gmat →* liftableSubgroup where
  toFun g := ⟨⟨g, Generated.Gmat_le_AutO g.2⟩,
    mem_liftableSubgroup.2 (ConwayNorton.isVnatLiftable_of_mem_gmat _ g.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The lift `Gmat →* Aut V♮`**: `g ↦` the automorphism of `V♮` acting on `V♮₂` as `ℂ ⊗ g`. -/
noncomputable def gmatLift : Generated.Gmat →* AutVnat := monsterLift.comp gmatToLiftable

theorem gmatLift_injective : Function.Injective gmatLift := by
  intro g g' hgg'
  have h := monsterLift_injective (a₁ := gmatToLiftable g) (a₂ := gmatToLiftable g') hgg'
  exact Subtype.ext
    (congrArg (fun x : liftableSubgroup => ((x : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) h)

theorem gmatLift_apply_griessNat (g : Generated.Gmat) (u : SpaceB) :
    gmatLift g (griessNat u : Vnat) = griessNat ((g : SpaceB ≃ₗ[ℚ] SpaceB) u) :=
  monsterLift_apply_griessNat (gmatToLiftable g) u

/-- ⭐ **`Gmat` is finite**: it embeds in the finite group `Aut V♮`. -/
theorem finite_gmat : Finite Generated.Gmat := by
  haveI := ConwayNorton.M8.finite_autVnat
  exact Finite.of_injective _ gmatLift_injective

/-- Every element of `Gmat` fixes `e₁ = (I, 0, 0)`. -/
theorem gmat_apply_identityVec {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Generated.Gmat) :
    g griessIdentityVec = griessIdentityVec := by
  have h1 := gmatLift_apply_griessNat ⟨g, hg⟩ griessIdentityVec
  rw [autVnat_apply_griessNat_identityVec] at h1
  exact (griessNat_coe_injective h1).symm

end Gmat

/-! ## §4  The projection `P₀` and the commutant input -/

section Projection

/-- **The projection `P₀`**: `P₀ u = (bform(u, e₁) / 24) · e₁`, the `bform`-orthogonal projection of
`SpaceB` onto the line `ℚ e₁` of `e₁ = (I, 0, 0)` (`bform(e₁, e₁) = 24`). -/
noncomputable def griessUnitProj : SpaceB →ₗ[ℚ] SpaceB :=
  LinearMap.smulRight ((24 : ℚ)⁻¹ • bform.flip griessIdentityVec) griessIdentityVec

theorem griessUnitProj_apply (u : SpaceB) :
    griessUnitProj u = (bform u griessIdentityVec / 24) • griessIdentityVec := by
  rw [griessUnitProj, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul,
    div_eq_inv_mul]
  rfl

theorem griessUnitProj_identityVec : griessUnitProj griessIdentityVec = griessIdentityVec := by
  rw [griessUnitProj_apply, bform_griessIdentityVec_self, div_self (by norm_num : (24 : ℚ) ≠ 0),
    one_smul]

theorem griessUnitProj_mul_self : griessUnitProj * griessUnitProj = griessUnitProj :=
  LinearMap.ext fun u => by
    rw [Module.End.mul_apply, griessUnitProj_apply u, map_smul, griessUnitProj_identityVec]

theorem trace_griessUnitProj : LinearMap.trace ℚ SpaceB griessUnitProj = 1 := by
  rw [griessUnitProj, LinearMap.trace_smulRight, LinearMap.smul_apply, smul_eq_mul]
  change (24 : ℚ)⁻¹ * bform griessIdentityVec griessIdentityVec = 1
  rw [bform_griessIdentityVec_self]
  norm_num

/-- `P₀` commutes with every element of `Gmat`. -/
theorem griessUnitProj_apply_gmat {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Generated.Gmat)
    (u : SpaceB) : griessUnitProj (g u) = g (griessUnitProj u) := by
  have hb : bform (g u) griessIdentityVec = bform u griessIdentityVec := by
    have := (mem_AutO.1 (Generated.Gmat_le_AutO hg)).2 u griessIdentityVec
    rwa [gmat_apply_identityVec hg] at this
  rw [griessUnitProj_apply, griessUnitProj_apply, hb, map_smul, gmat_apply_identityVec hg]

/-- ⭐ **The commutant of `Gmat` on `SpaceB` is spanned by `1` and `P₀`** (the named input; the
commutant lemma of `Notes/monster_aut/RATIONALITY.md`, §2.5): every `ℚ`-linear endomorphism `T` of
`SpaceB` commuting with every element of `Generated.Gmat` is `a · 1 + b · P₀`. Equivalently, `Gmat`
is absolutely irreducible on the `bform`-orthogonal complement of `e₁ = (I, 0, 0)`. -/
def GmatCommutantScalar : Prop :=
  ∀ T : SpaceB →ₗ[ℚ] SpaceB, (∀ g ∈ Generated.Gmat, ∀ u : SpaceB, T (g u) = g (T u)) →
    ∃ a b : ℚ, T = a • LinearMap.id + b • griessUnitProj

/-- Conversely, every `a · 1 + b · P₀` commutes with `Gmat`: the commutant contains the span of
`1` and `P₀`, so `GmatCommutantScalar` asserts equality. -/
theorem gmat_commute_griessUnitProj (a b : ℚ) {g : SpaceB ≃ₗ[ℚ] SpaceB}
    (hg : g ∈ Generated.Gmat) (u : SpaceB) :
    (a • LinearMap.id + b • griessUnitProj : SpaceB →ₗ[ℚ] SpaceB) (g u)
      = g ((a • LinearMap.id + b • griessUnitProj : SpaceB →ₗ[ℚ] SpaceB) u) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    griessUnitProj_apply_gmat hg, map_add, map_smul]

end Projection

/-! ## §5  Matrices in the dictionary bases -/

section Matrices

/-- The `ℂ`-linear endomorphism `griessIso ∘ (ℂ ⊗ G) ∘ griessIso⁻¹` of `V♮₂` induced by a `ℚ`-linear
endomorphism `G` of `SpaceB`. -/
noncomputable def griessLinear (G : SpaceB →ₗ[ℚ] SpaceB) :
    VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2 :=
  griessIso.toLinearMap ∘ₗ G.baseChange ℂ ∘ₗ griessIso.symm.toLinearMap

theorem griessLinear_griessNat (G : SpaceB →ₗ[ℚ] SpaceB) (u : SpaceB) :
    griessLinear G (griessNat u) = griessNat (G u) := by
  simp only [griessLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, ← griessIso_tmul,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

/-- The coordinates of `griessNat u` in `griessBasisC` are the rational coordinates of `u`. -/
theorem griessBasisC_repr_griessNat (u : SpaceB) (i : Fin (Module.finrank ℚ SpaceB)) :
    griessBasisC.repr (griessNat u) i = (griessBasisQ.repr u i : ℂ) := by
  have hsum : griessNat u = ∑ k, ((griessBasisQ.repr u k : ℚ) : ℂ) • griessBasisC k := by
    conv_lhs => rw [← griessBasisQ.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [griessNat_smul, griessBasisC_apply]
  rw [hsum, griessBasisC.repr_sum_self]

/-- **The matrix of `griessLinear G` is the rational matrix of `G`**, read in `ℂ`. -/
theorem toMatrix_griessLinear (G : SpaceB →ₗ[ℚ] SpaceB) :
    LinearMap.toMatrix griessBasisC griessBasisC (griessLinear G)
      = (LinearMap.toMatrix griessBasisQ griessBasisQ G).map (Rat.castHom ℂ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, griessBasisC_apply,
    griessLinear_griessNat, griessBasisC_repr_griessNat, Rat.coe_castHom]

/-- The rational representation of `Gmat` in the basis `griessBasisQ`. -/
noncomputable def gmatMatrixRep :
    Generated.Gmat →*
      Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℚ where
  toFun g := LinearMap.toMatrix griessBasisQ griessBasisQ
    ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB)
  map_one' := by
    rw [show (((1 : Generated.Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = LinearMap.id
      from LinearMap.ext fun _ => rfl]
    exact LinearMap.toMatrix_id griessBasisQ
  map_mul' g g' := by
    rw [← LinearMap.toMatrix_mul]
    congr 1

theorem gmatMatrixRep_apply (g : Generated.Gmat) :
    gmatMatrixRep g = LinearMap.toMatrix griessBasisQ griessBasisQ
      ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) := rfl

theorem vnatWeightTwoRestrict_gmatLift (g : Generated.Gmat) :
    (vnatWeightTwoRestrict (gmatLift g) : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
      = griessLinear ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) :=
  linearMap_ext_griessNat fun u => by
    rw [griessLinear_griessNat]
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, vnatWeightTwoRestrict_apply_coe, gmatLift_apply_griessNat]
    rfl

/-- The complex matrix of `σ(g)` is the matrix of the lift of `g` on `V♮₂`. -/
theorem gmatMatrixRep_map (g : Generated.Gmat) :
    (Rat.castHom ℂ).mapMatrix (gmatMatrixRep g)
      = LinearMap.toMatrix griessBasisC griessBasisC
          (vnatWeightTwoRestrict (gmatLift g) : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2) := by
  rw [vnatWeightTwoRestrict_gmatLift, toMatrix_griessLinear]
  rfl

/-- The trace of `h|_{V♮₂}` is the graded trace at weight two. -/
theorem trace_vnatWeightTwoRestrict (k : AutVnat) :
    LinearMap.trace ℂ (VnatVOA.grading 2)
        (vnatWeightTwoRestrict k : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
      = ConwayNorton.gradedAutTrace VnatVOA k 2 := by
  unfold ConwayNorton.gradedAutTrace
  congr 1

/-- **Weight-two traces are rational** (`ConwayNorton.exists_rat_gradedAutTrace_two`). -/
theorem exists_rat_trace_vnatWeightTwoRestrict (k : AutVnat) :
    ∃ r : ℚ, LinearMap.trace ℂ (VnatVOA.grading 2)
        (vnatWeightTwoRestrict k : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2) = r := by
  obtain ⟨r, hr⟩ := ConwayNorton.exists_rat_gradedAutTrace_two k
  exact ⟨r, by rw [trace_vnatWeightTwoRestrict, hr]⟩

/-- `P₀` on `V♮₂`: `x ↦ (natForm(x, griessNat e₁) / 48) · griessNat e₁`. -/
theorem griessLinear_griessUnitProj_apply (x : VnatVOA.grading 2) :
    griessLinear griessUnitProj x
      = ((48 : ℂ)⁻¹ * SimpleNat.natForm (x : Vnat) (griessNat griessIdentityVec : Vnat)) •
          griessNat griessIdentityVec := by
  have hlin : griessLinear griessUnitProj = LinearMap.smulRight ((48 : ℂ)⁻¹ •
      (SimpleNat.natForm.flip (griessNat griessIdentityVec : Vnat) ∘ₗ (VnatVOA.grading 2).subtype))
      (griessNat griessIdentityVec) := by
    refine linearMap_ext_griessNat fun v => ?_
    rw [griessLinear_griessNat, griessUnitProj_apply, griessNat_smul, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      show (SimpleNat.natForm.flip (griessNat griessIdentityVec : Vnat)) (griessNat v : Vnat)
        = SimpleNat.natForm (griessNat v : Vnat) (griessNat griessIdentityVec : Vnat) from rfl,
      griessNat_form, smul_eq_mul]
    congr 1
    push_cast
    ring
  rw [hlin, LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, smul_eq_mul]
  rfl

/-- `P₀ H = P₀` on `V♮₂`: `natForm` is `Aut V♮`-invariant and `h` fixes `griessNat e₁`. -/
theorem griessLinear_griessUnitProj_mul_restrict (h : AutVnat) :
    griessLinear griessUnitProj *
        (vnatWeightTwoRestrict h : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
      = griessLinear griessUnitProj := by
  refine LinearMap.ext fun x => ?_
  have key := natForm_autRestrict h x (griessNat griessIdentityVec)
  rw [autVnat_apply_griessNat_identityVec h] at key
  have key' : SimpleNat.natForm
      (((vnatWeightTwoRestrict h : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2) x :
        VnatVOA.grading 2) : Vnat) (griessNat griessIdentityVec : Vnat)
      = SimpleNat.natForm (x : Vnat) (griessNat griessIdentityVec : Vnat) := key
  rw [Module.End.mul_apply, griessLinear_griessUnitProj_apply, griessLinear_griessUnitProj_apply,
    key']

/-- `H P₀ = P₀` on `V♮₂`: `h` fixes `griessNat e₁`. -/
theorem restrict_mul_griessLinear_griessUnitProj (h : AutVnat) :
    (vnatWeightTwoRestrict h : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2) *
        griessLinear griessUnitProj
      = griessLinear griessUnitProj := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, griessLinear_griessUnitProj_apply, map_smul]
  congr 1
  apply Subtype.ext
  rw [LinearEquiv.coe_coe, vnatWeightTwoRestrict_apply_coe]
  exact autVnat_apply_griessNat_identityVec h

end Matrices

/-! ## §6  The Schur-span data in the dictionary bases -/

section SchurData

/-- The matrix of `P₀` in the basis `griessBasisQ`. -/
noncomputable def griessUnitMatrix :
    Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℚ :=
  LinearMap.toMatrix griessBasisQ griessBasisQ griessUnitProj

/-- The matrix of `1 − P₀`: the idempotent cutting out the `bform`-complement of `e₁`. -/
noncomputable def griessComplMatrix :
    Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℚ :=
  1 - griessUnitMatrix

theorem griessUnitMatrix_mul_self : griessUnitMatrix * griessUnitMatrix = griessUnitMatrix := by
  rw [griessUnitMatrix, ← LinearMap.toMatrix_mul, griessUnitProj_mul_self]

theorem griessUnitMatrix_commute (s : Generated.Gmat) :
    griessUnitMatrix * gmatMatrixRep s = gmatMatrixRep s * griessUnitMatrix := by
  rw [griessUnitMatrix, gmatMatrixRep_apply, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  exact LinearMap.ext fun v => griessUnitProj_apply_gmat s.2 v

theorem griessComplMatrix_mul_unit : griessComplMatrix * griessUnitMatrix = 0 := by
  rw [griessComplMatrix, Matrix.sub_mul, Matrix.one_mul, griessUnitMatrix_mul_self, sub_self]

theorem griessComplMatrix_mul_self :
    griessComplMatrix * griessComplMatrix = griessComplMatrix := by
  rw [griessComplMatrix, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    griessUnitMatrix_mul_self, sub_self, sub_zero]

theorem griessComplMatrix_commute (s : Generated.Gmat) :
    griessComplMatrix * gmatMatrixRep s = gmatMatrixRep s * griessComplMatrix := by
  rw [griessComplMatrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    griessUnitMatrix_commute]

/-- `tr(1 − P₀) = 196884 − 1 = 196883`. -/
theorem trace_griessComplMatrix : griessComplMatrix.trace = 196883 := by
  have hcard : ((Fintype.card (Fin (Module.finrank ℚ SpaceB)) : ℕ) : ℚ) = 196884 := by
    rw [Fintype.card_fin, finrank_B]
    norm_num
  have hPtr : griessUnitMatrix.trace = 1 := by
    rw [griessUnitMatrix, ← LinearMap.trace_eq_matrix_trace, trace_griessUnitProj]
  rw [griessComplMatrix, Matrix.trace_sub, Matrix.trace_one, hcard, hPtr]
  norm_num

theorem trace_griessComplMatrix_ne_zero : griessComplMatrix.trace ≠ 0 := by
  rw [trace_griessComplMatrix]
  norm_num

/-- **The commutant input in matrix form**: every rational matrix commuting with `σ(Gmat)` is a
scalar on the image of `1 − P₀`. -/
theorem griessComplMatrix_commutant (hcomm : GmatCommutantScalar)
    (T : Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℚ)
    (hT : ∀ s, T * gmatMatrixRep s = gmatMatrixRep s * T) :
    ∃ a : ℚ, griessComplMatrix * T * griessComplMatrix = a • griessComplMatrix := by
  have hT' : ∀ g ∈ Generated.Gmat, ∀ v : SpaceB,
      Matrix.toLin griessBasisQ griessBasisQ T (g v)
        = g (Matrix.toLin griessBasisQ griessBasisQ T v) := by
    intro g hg v
    have hm : Matrix.toLin griessBasisQ griessBasisQ T * (g : SpaceB →ₗ[ℚ] SpaceB)
        = (g : SpaceB →ₗ[ℚ] SpaceB) * Matrix.toLin griessBasisQ griessBasisQ T := by
      apply (LinearMap.toMatrix griessBasisQ griessBasisQ).injective
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin]
      exact hT ⟨g, hg⟩
    exact LinearMap.congr_fun hm v
  obtain ⟨a, β, hab⟩ := hcomm _ hT'
  have hTm : T = a • 1 + β • griessUnitMatrix := by
    have := congrArg (LinearMap.toMatrix griessBasisQ griessBasisQ) hab
    rw [LinearMap.toMatrix_toLin, map_add, map_smul, map_smul, LinearMap.toMatrix_id] at this
    exact this
  refine ⟨a, ?_⟩
  rw [hTm]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    griessComplMatrix_mul_self, griessComplMatrix_mul_unit, smul_zero, add_zero]

end SchurData

section ComplexData

/-- The matrix of `h|_{V♮₂}` in the basis `griessBasisC`. -/
noncomputable def vnatMatrix (h : AutVnat) :
    Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℂ :=
  LinearMap.toMatrix griessBasisC griessBasisC
    (vnatWeightTwoRestrict h : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)

theorem griessUnitMatrix_map :
    (Rat.castHom ℂ).mapMatrix griessUnitMatrix
      = LinearMap.toMatrix griessBasisC griessBasisC (griessLinear griessUnitProj) := by
  rw [griessUnitMatrix, toMatrix_griessLinear]
  rfl

/-- `P₀ H = P₀`. -/
theorem griessUnitMatrix_map_mul_vnatMatrix (h : AutVnat) :
    (Rat.castHom ℂ).mapMatrix griessUnitMatrix * vnatMatrix h
      = (Rat.castHom ℂ).mapMatrix griessUnitMatrix := by
  rw [griessUnitMatrix_map, vnatMatrix, ← LinearMap.toMatrix_mul,
    griessLinear_griessUnitProj_mul_restrict h]

/-- `H P₀ = P₀`. -/
theorem vnatMatrix_mul_griessUnitMatrix_map (h : AutVnat) :
    vnatMatrix h * (Rat.castHom ℂ).mapMatrix griessUnitMatrix
      = (Rat.castHom ℂ).mapMatrix griessUnitMatrix := by
  rw [griessUnitMatrix_map, vnatMatrix, ← LinearMap.toMatrix_mul,
    restrict_mul_griessLinear_griessUnitProj h]

theorem vnatWeightTwoRestrict_mul_coe (a b : AutVnat) :
    (vnatWeightTwoRestrict (a * b) : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
      = (vnatWeightTwoRestrict a : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
        * (vnatWeightTwoRestrict b : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2) :=
  LinearMap.ext fun _ => rfl

theorem vnatMatrix_mul (a b : AutVnat) : vnatMatrix (a * b) = vnatMatrix a * vnatMatrix b := by
  unfold vnatMatrix
  rw [vnatWeightTwoRestrict_mul_coe]
  exact LinearMap.toMatrix_mul griessBasisC _ _

theorem gmatMatrixRep_map_mul_vnatMatrix (s : Generated.Gmat) (h : AutVnat) :
    (Rat.castHom ℂ).mapMatrix (gmatMatrixRep s) * vnatMatrix h = vnatMatrix (gmatLift s * h) := by
  rw [gmatMatrixRep_map, vnatMatrix_mul]
  rfl

/-- **The traces `tr(σ(s⁻¹)(1 − P₀) H)` are rational**: `tr((s⁻¹h)|_{V♮₂}) − tr(σ(s⁻¹) P₀)`. -/
theorem exists_rat_trace_gmat_compl_vnatMatrix (s : Generated.Gmat) (h : AutVnat) :
    ∃ q : ℚ, ((gmatMatrixRep s⁻¹ * griessComplMatrix).map (Rat.castHom ℂ) * vnatMatrix h).trace
      = (q : ℂ) := by
  obtain ⟨r, hr⟩ := exists_rat_trace_vnatWeightTwoRestrict (gmatLift s⁻¹ * h)
  refine ⟨r - (gmatMatrixRep s⁻¹ * griessUnitMatrix).trace, ?_⟩
  have h1 : (gmatMatrixRep s⁻¹ * griessComplMatrix).map (Rat.castHom ℂ) * vnatMatrix h
      = (Rat.castHom ℂ).mapMatrix (gmatMatrixRep s⁻¹) * vnatMatrix h
        - (Rat.castHom ℂ).mapMatrix (gmatMatrixRep s⁻¹ * griessUnitMatrix) := by
    rw [← RingHom.mapMatrix_apply, griessComplMatrix, map_mul, map_mul, map_sub, map_one,
      Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, griessUnitMatrix_map_mul_vnatMatrix,
      Matrix.mul_sub]
  have h3 : ((Rat.castHom ℂ).mapMatrix (gmatMatrixRep s⁻¹ * griessUnitMatrix)).trace
      = (((gmatMatrixRep s⁻¹ * griessUnitMatrix).trace : ℚ) : ℂ) :=
    (AddMonoidHom.map_trace (Rat.castHom ℂ) _).symm
  rw [h1, Matrix.trace_sub, gmatMatrixRep_map_mul_vnatMatrix, vnatMatrix,
    ← LinearMap.trace_eq_matrix_trace ℂ griessBasisC, hr, h3, Rat.cast_sub]

end ComplexData

/-! ## §7  Rationality -/

/-- **The matrix of every `h|_{V♮₂}` is rational**, given the commutant input: Schur's span formula
for `σ(Gmat)` on the image of `1 − P₀` (`Rationality.eq_map_ratCast_of_rational_traces`) and
`H = P₀ + (1 − P₀) H (1 − P₀)`. -/
theorem exists_vnatMatrix_eq_map_of_commutant (hcomm : GmatCommutantScalar) (h : AutVnat) :
    ∃ Z : Matrix (Fin (Module.finrank ℚ SpaceB)) (Fin (Module.finrank ℚ SpaceB)) ℚ,
      vnatMatrix h = Z.map (Rat.castHom ℂ) := by
  letI : Fintype Generated.Gmat := @Fintype.ofFinite _ finite_gmat
  choose q hq using fun s : Generated.Gmat => exists_rat_trace_gmat_compl_vnatMatrix s h
  have hEHE := Rationality.eq_map_ratCast_of_rational_traces gmatMatrixRep griessComplMatrix
    griessComplMatrix_mul_self griessComplMatrix_commute trace_griessComplMatrix_ne_zero
    (griessComplMatrix_commutant hcomm) (vnatMatrix h) q hq
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (Module.finrank ℚ SpaceB))
      (Fin (Module.finrank ℚ SpaceB)) ℚ,
      Z = (griessComplMatrix.trace / Fintype.card Generated.Gmat) •
        ∑ s, q s • (gmatMatrixRep s * griessComplMatrix) := ⟨_, rfl⟩
  rw [← hZ] at hEHE
  have hEc : griessComplMatrix.map (Rat.castHom ℂ)
      = 1 - (Rat.castHom ℂ).mapMatrix griessUnitMatrix := by
    rw [← RingHom.mapMatrix_apply, griessComplMatrix, map_sub, map_one]
  have hPP : (Rat.castHom ℂ).mapMatrix griessUnitMatrix * (Rat.castHom ℂ).mapMatrix griessUnitMatrix
      = (Rat.castHom ℂ).mapMatrix griessUnitMatrix := by
    rw [← map_mul, griessUnitMatrix_mul_self]
  have key : (1 - (Rat.castHom ℂ).mapMatrix griessUnitMatrix) * vnatMatrix h
        * (1 - (Rat.castHom ℂ).mapMatrix griessUnitMatrix)
      = vnatMatrix h - (Rat.castHom ℂ).mapMatrix griessUnitMatrix := by
    rw [Matrix.sub_mul, Matrix.one_mul, griessUnitMatrix_map_mul_vnatMatrix, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      vnatMatrix_mul_griessUnitMatrix_map, hPP, sub_self, sub_zero]
  rw [hEc, key] at hEHE
  refine ⟨griessUnitMatrix + Z, ?_⟩
  calc vnatMatrix h = (Rat.castHom ℂ).mapMatrix griessUnitMatrix
        + (vnatMatrix h - (Rat.castHom ℂ).mapMatrix griessUnitMatrix) := by abel
    _ = (Rat.castHom ℂ).mapMatrix griessUnitMatrix + (Rat.castHom ℂ).mapMatrix Z := by
        rw [hEHE]
        rfl
    _ = (griessUnitMatrix + Z).map (Rat.castHom ℂ) :=
        (map_add (Rat.castHom ℂ).mapMatrix griessUnitMatrix Z).symm

/-- ⭐ **Every automorphism of `V♮` is rational on `V♮₂`**, given the commutant input
`GmatCommutantScalar`: for every `h ∈ Aut V♮` and `u ∈ SpaceB` there is `u' ∈ SpaceB` with
`h (griessNat u) = griessNat u'`. -/
theorem autVnat_rational_of_commutant (hcomm : GmatCommutantScalar) :
    ∀ h : AutVnat, ∀ u : SpaceB, ∃ u' : SpaceB, h (griessNat u : Vnat) = griessNat u' := by
  intro h u
  obtain ⟨Z, hZ⟩ := exists_vnatMatrix_eq_map_of_commutant hcomm h
  have hlin : (vnatWeightTwoRestrict h : VnatVOA.grading 2 →ₗ[ℂ] VnatVOA.grading 2)
      = griessLinear (Matrix.toLin griessBasisQ griessBasisQ Z) := by
    apply (LinearMap.toMatrix griessBasisC griessBasisC).injective
    rw [toMatrix_griessLinear, LinearMap.toMatrix_toLin]
    exact hZ
  refine ⟨Matrix.toLin griessBasisQ griessBasisQ Z u, ?_⟩
  have hx := congrArg Subtype.val (LinearMap.congr_fun hlin (griessNat u))
  rw [griessLinear_griessNat] at hx
  exact hx

/-! ## §8  Corollaries -/

/-- **Every automorphism of `V♮` is a lift**, given the commutant input. -/
theorem monsterLift_surjective_of_commutant (hcomm : GmatCommutantScalar) :
    Function.Surjective monsterLift := fun h =>
  isVnatLiftable_of_rational h (autVnat_rational_of_commutant hcomm h)

/-- ⭐ **`Aut V♮ ≃* liftableSubgroup`**, given the commutant input: the inverse of the bijective
lift `monsterLift`. -/
noncomputable def autVnat_mulEquiv_liftable_of_commutant (hcomm : GmatCommutantScalar) :
    AutVnat ≃* liftableSubgroup :=
  (MulEquiv.ofBijective monsterLift
    ⟨monsterLift_injective, monsterLift_surjective_of_commutant hcomm⟩).symm

theorem autVnat_mulEquiv_liftable_of_commutant_symm_apply (hcomm : GmatCommutantScalar)
    (g : liftableSubgroup) :
    (autVnat_mulEquiv_liftable_of_commutant hcomm).symm g = monsterLift g := by
  simp only [autVnat_mulEquiv_liftable_of_commutant, MulEquiv.symm_symm,
    MulEquiv.ofBijective_apply]

/-- `Aut V♮ ≃* liftableSubgroup`, as a proposition, given the commutant input. -/
theorem nonempty_autVnat_mulEquiv_liftable_of_commutant (hcomm : GmatCommutantScalar) :
    Nonempty (AutVnat ≃* liftableSubgroup) :=
  ⟨autVnat_mulEquiv_liftable_of_commutant hcomm⟩

/-- ⭐ **`Aut V♮ ≃* AutO`**, given the commutant input and CFSG's generation theorem
`Generated.Gmat = AutO`. -/
theorem autVnat_mulEquiv_autO_of_commutant_of_Gmat (hcomm : GmatCommutantScalar)
    (hGmat : Generated.Gmat = AutO) : Nonempty (AutVnat ≃* AutO) :=
  autVnat_mulEquiv_autO_of_liftable_of_rational
    (fun g => ConwayNorton.isVnatLiftable_of_mem_gmat g (by rw [hGmat]; exact g.2))
    (autVnat_rational_of_commutant hcomm)

end VOA.Moonshine.MonsterAction
