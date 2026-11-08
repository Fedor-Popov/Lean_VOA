import VOA.Moonshine.MoonshineLRLiftVisible
import VOA.Moonshine.MoonshineCNMonsterActionExtra

/-!
# Cancelling the extraspecial discrepancy of a visible lift

The spin operator basis detects the conjugation signs of any nonzero residual matrix.
After cancelling that basis matrix, the residual commutes with every matrix and is scalar;
orthogonality makes the scalar a sign. Thus the relative charge is `±Qμ`.

Extraspecial VOA lifts realize both signs: the central `W` sign is the square of a lift
whose spin matrix squares to `-1`. Cancelling the resulting correction and applying
`liftVisParity_ext` proves liftability of every visible pair and every member of `Gvis`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.MonsterGriess.ScalarKernel
open VOA.Moonshine.MonsterGriess.Visible VOA.Moonshine.MonsterGriess.Parity
open Matrix

/-- The commutation sign of two unphased spin matrices. -/
def liftVisRSign (p q : Code.C × Cocode) : ℚ :=
  sgnR ℚ (pair q.1 p.2 + pair p.1 q.2)

theorem liftVisRSign_sq (p q : Code.C × Cocode) :
    liftVisRSign p q * liftVisRSign p q = 1 := sgnR_mul_self _

theorem liftVisRTDR_comm (p q : Code.C × Cocode) :
    TDR ℚ p * TDR ℚ q = liftVisRSign p q • (TDR ℚ q * TDR ℚ p) := by
  simp only [TDR_eq_qmatR, qmatR_mul, zero_add, liftVisRSign, sgnR_smul_qmatR]
  rw [add_assoc, zmod2_add_self, add_zero, add_comm p.1 q.1, add_comm p.2 q.2]

theorem liftVisRTrace_nonzero (D : Matrix SpinIdx SpinIdx ℚ) (hD : D ≠ 0) :
    ∃ p : Code.C × Cocode, trace ((TDR ℚ p)ᵀ * D) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hD
  rw [eq_sum_trace_smul_TDR D]
  simp only [h, zero_div, zero_smul, Finset.sum_const_zero]

theorem liftVisRTrace_sign (A B D : Matrix SpinIdx SpinIdx ℚ) (c e : ℚ)
    (hB : Bᵀ * B = 1) (hc : c * c = 1)
    (hA : A * B = c • (B * A)) (hD : D * B = e • (B * D))
    (ht : trace (Aᵀ * D) ≠ 0) : e = c := by
  have hBB := mul_eq_one_comm.mp hB
  have hleft : trace ((A * B)ᵀ * (D * B)) = trace (Aᵀ * D) := by
    rw [transpose_mul, ← Matrix.mul_assoc, trace_mul_cycle,
      ← Matrix.mul_assoc B, hBB, Matrix.one_mul]
  rw [hA, hD, transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, Matrix.mul_assoc Aᵀ, hB, Matrix.mul_one,
    trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at hleft
  have he : c * e = 1 := by
    apply mul_right_cancel₀ ht
    simpa only [mul_assoc, one_mul] using hleft
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hc) (he.trans hc.symm)

theorem liftVisRTDR_transpose (p : Code.C × Cocode) :
    (TDR ℚ p)ᵀ = sgnR ℚ (pair p.1 p.2) • TDR ℚ p := by
  rw [TDR_eq_qmatR, qmatR_transpose, zero_add, sgnR_smul_qmatR, add_zero]

/-- A rational orthogonal operator fixing every spin label up to sign is extraspecial. -/
theorem liftVisRExtraspecial (D : Matrix SpinIdx SpinIdx ℚ) (hD : Dᵀ * D = 1)
    (hcomm : ∀ q : Code.C × Cocode, ∃ e : ℚ,
      D * TDR ℚ q = e • (TDR ℚ q * D)) :
    ∃ (p : Code.C × Cocode) (c : ℚ), (c = 1 ∨ c = -1) ∧ D = c • TDR ℚ p := by
  classical
  have hne : D ≠ 0 := by
    intro h
    rw [h, transpose_zero, Matrix.zero_mul] at hD
    exact zero_ne_one hD
  obtain ⟨p, hp⟩ := liftVisRTrace_nonzero D hne
  have hsign (q : Code.C × Cocode) :
      D * TDR ℚ q = liftVisRSign p q • (TDR ℚ q * D) := by
    obtain ⟨e, he⟩ := hcomm q
    have heq := liftVisRTrace_sign (TDR ℚ p) (TDR ℚ q) D
      (liftVisRSign p q) e
      (by rw [TDR_eq_qmatR]; exact qmatR_transpose_mul_self _ _ _)
      (liftVisRSign_sq p q) (liftVisRTDR_comm p q) he hp
    rwa [heq] at he
  let E := D * (TDR ℚ p)ᵀ
  have hE (q : Code.C × Cocode) : E * TDR ℚ q = TDR ℚ q * E := by
    dsimp only [E]
    rw [liftVisRTDR_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, liftVisRTDR_comm p q, Matrix.mul_smul,
      ← Matrix.mul_assoc D, hsign q, Matrix.smul_mul]
    simp only [smul_smul, mul_assoc, liftVisRSign_sq, mul_one, Matrix.mul_smul]
  have hEY (Y : Matrix SpinIdx SpinIdx ℚ) : E * Y = Y * E := by
    rw [eq_sum_trace_smul_TDR Y, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [Matrix.mul_smul, Matrix.smul_mul, hE]
  obtain ⟨c, hc⟩ := (mem_range_scalar_iff_commute_single' (M := E)).mpr
    (fun i j => (hEY _).symm)
  have hscalar : E = c • (1 : Matrix SpinIdx SpinIdx ℚ) := by
    rw [← hc, scalar_apply, smul_one_eq_diagonal]
  have hDp : D = c • TDR ℚ p := by
    have h := congrArg (fun M => M * TDR ℚ p) hscalar
    dsimp only [E] at h
    rw [Matrix.mul_assoc, TDR_eq_qmatR, qmatR_transpose_mul_self,
      Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h
    simpa only [TDR_eq_qmatR] using h
  have hc2 : c * c = 1 := by
    rw [hDp, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      TDR_eq_qmatR, qmatR_transpose_mul_self] at hD
    have h := congrArg (fun M : Matrix SpinIdx SpinIdx ℚ =>
      M spinIdxBase spinIdxBase) hD
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h
  exact ⟨p, c, mul_self_eq_one_iff.mp hc2, hDp⟩

theorem liftVisRCoord_surjective :
    Function.Surjective (fun α : leech.carrier => coordOfRed (red leech α)) :=
  latRedEquiv.symm.surjective.comp (red_surjective leech)

theorem liftVisRRelative_intertwine (p : Pvis) (D : Matrix SpinIdx SpinIdx ℚ)
    (hD : ∀ v : SpinRep,
      liftVisRelativeCharge p v = D.map (Rat.castHom ℂ) *ᵥ v)
    (α : leech.carrier) :
    D * liftMonoQmat α =
      (liftMonoWeight (liftVisIsometry p.1.2) α * liftVisWeight p α) •
        (liftMonoQmat α * D) := by
  have hmap (w : ℚ) (M : Matrix SpinIdx SpinIdx ℚ) :
      (w • M).map (Rat.castHom ℂ) = (w : ℂ) • M.map (Rat.castHom ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
      Rat.cast_mul]
  suffices h : (D * liftMonoQmat α).map (Rat.castHom ℂ) =
      ((liftMonoWeight (liftVisIsometry p.1.2) α * liftVisWeight p α) •
        (liftMonoQmat α * D)).map (Rat.castHom ℂ) from
    Matrix.map_injective (Rat.cast_injective (α := ℂ)) h
  rw [Matrix.map_mul (f := Rat.castHom ℂ), hmap, Matrix.map_mul (f := Rat.castHom ℂ)]
  ext i j
  have h := liftVisRelativeCharge_intertwine p α (Pi.single j 1)
  rw [hD, hD] at h
  have hi := congrFun h i
  change (D.map (Rat.castHom ℂ) *ᵥ
      ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ Pi.single j 1)) i =
    ((liftMonoWeight (liftVisIsometry p.1.2) α * liftVisWeight p α : ℚ) : ℂ) *
      ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ
        (D.map (Rat.castHom ℂ) *ᵥ Pi.single j 1)) i at hi
  simp only [Matrix.mulVec_single_one] at hi
  exact hi

/-- The actual relative charge is an extraspecial spin matrix, including its sign. -/
theorem liftVisRRelative (p : Pvis) :
    ∃ (μ : leech.carrier) (c : ℚ), (c = 1 ∨ c = -1) ∧ ∀ v : SpinRep,
      liftVisRelativeCharge p v = (c • liftMonoQmat μ).map (Rat.castHom ℂ) *ᵥ v := by
  obtain ⟨σ, ε, h⟩ := liftVisRelativeCharge_signed p
  obtain ⟨q, c, hc, hq⟩ := liftVisRExtraspecial (liftGenSignedMatrix σ ε)
    (liftGenSignedMatrix_orthogonal σ ε) (fun q => by
      obtain ⟨α, hα⟩ := liftVisRCoord_surjective q
      refine ⟨liftMonoWeight (liftVisIsometry p.1.2) α * liftVisWeight p α, ?_⟩
      simpa only [liftMonoQmat, hα, ← TDR_eq_qmatR] using
        liftVisRRelative_intertwine p _ h α)
  obtain ⟨μ, hμ⟩ := liftVisRCoord_surjective q
  refine ⟨μ, c, hc, fun v => ?_⟩
  rw [h, hq]
  simp only [liftMonoQmat, hμ, TDR_eq_qmatR]

/-- The normalized chosen charge differs from the prescribed spin matrix by `±Qμ`. -/
theorem liftVisRCharge (p : Pvis) :
    ∃ (μ : leech.carrier) (c : ℚ), (c = 1 ∨ c = -1) ∧ ∀ v : SpinRep,
      (liftWScalar (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) : ℂ) •
        liftWSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v =
          ((p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * (c • liftMonoQmat μ)).map
            (Rat.castHom ℂ) *ᵥ v := by
  obtain ⟨μ, c, hc, h⟩ := liftVisRRelative p
  refine ⟨μ, c, hc, fun v => ?_⟩
  have hv := congrArg (liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)) (h v)
  change (liftVisMatrixEquiv _ (liftVisSpinOrthogonal p))
    ((liftVisMatrixEquiv _ (liftVisSpinOrthogonal p)).symm
      (liftSpinCharge (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) v)) = _ at hv
  rw [LinearEquiv.apply_symm_apply, liftVisMatrixEquiv_apply,
    Matrix.mulVec_mulVec, ← Matrix.map_mul (f := Rat.castHom ℂ)] at hv
  exact hv

/-- A lift fixing the symmetric block and acting on `W` by left multiplication. -/
def liftVisRBlocks (g : AutO) (D : Matrix SpinIdx SpinIdx ℚ) : Prop :=
  IsParityAut (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
    ∀ u : SpaceB, ((g : SpaceB ≃ₗ[ℚ] SpaceB) u).1 = u.1 ∧
      ((g : SpaceB ≃ₗ[ℚ] SpaceB) u).2.2 = D * u.2.2

theorem liftVisRParity_mul (g h : AutO)
    (hg : IsParityAut (g : SpaceB ≃ₗ[ℚ] SpaceB))
    (hh : IsParityAut (h : SpaceB ≃ₗ[ℚ] SpaceB)) :
    IsParityAut ((g * h : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  refine ⟨(g * h).property.1, (g * h).property.2, fun u => ?_⟩
  change (g : SpaceB ≃ₗ[ℚ] SpaceB) ((h : SpaceB ≃ₗ[ℚ] SpaceB) (xB u)) = _
  rw [hh.map_xB, hg.map_xB]
  rfl

theorem liftVisRBlocks_mul (g h : AutO) (D E : Matrix SpinIdx SpinIdx ℚ)
    (hg : liftVisRBlocks g D) (hh : liftVisRBlocks h E) :
    liftVisRBlocks (g * h) (D * E) := by
  refine ⟨liftVisRParity_mul g h hg.1 hh.1, fun u => ?_⟩
  change ((g : SpaceB ≃ₗ[ℚ] SpaceB) ((h : SpaceB ≃ₗ[ℚ] SpaceB) u)).1 = u.1 ∧ _
  refine ⟨(hg.2 _).1.trans (hh.2 u).1, ?_⟩
  change ((g : SpaceB ≃ₗ[ℚ] SpaceB) ((h : SpaceB ≃ₗ[ℚ] SpaceB) u)).2.2 = _
  rw [(hg.2 _).2, (hh.2 u).2, Matrix.mul_assoc]

theorem liftVisRExtra (μ : leech.carrier) :
    liftVisRBlocks (extraLiftable μ : AutO) (extraSign μ • liftMonoQmat μ) := by
  refine ⟨⟨(extraLiftable μ).val.property.1,
    (extraLiftable μ).val.property.2, fun u => ?_⟩, fun u => ?_⟩
  · rw [xB_apply, extraLiftable_apply, extraLiftable_apply, xB_apply]
    simp only [Matrix.mul_neg]
  · rw [extraLiftable_apply]
    exact ⟨rfl, rfl⟩

/-- The central `W` sign is the square of an extraspecial lift of odd quadratic norm. -/
theorem liftVisRCentral :
    ∃ g : liftableSubgroup, liftVisRBlocks (g : AutO) (-1) := by
  obtain ⟨μ, hμ⟩ := liftVisRCoord_surjective
    (ΩC, Submodule.Quotient.mk (Pi.single 0 1))
  have hQ : liftMonoQmat μ * liftMonoQmat μ = -1 := by
    simp only [liftMonoQmat, hμ, qmatR_mul, zero_add, pair_ΩC_mk_single,
      Code.add_self_C, add_self_cocode]
    exact neg_one_eq_qmatR.symm
  have hs : extraSign μ * extraSign μ = 1 := by
    rcases extraSign_eq_one_or μ with h | h <;> rw [h] <;> norm_num
  refine ⟨extraLiftable μ * extraLiftable μ, ?_⟩
  have h := liftVisRBlocks_mul _ _ _ _ (liftVisRExtra μ) (liftVisRExtra μ)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, hQ] at h
  exact h

theorem liftVisRScalar (c : ℚ) (hc : c = 1 ∨ c = -1) :
    ∃ g : liftableSubgroup, liftVisRBlocks (g : AutO) (c • 1) := by
  rcases hc with rfl | rfl
  · refine ⟨1, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · intro u v; rfl
    · intro u v; rfl
    · intro u; rfl
    · intro u
      change u.1 = u.1 ∧ u.2.2 = (1 : ℚ) • (1 : Matrix SpinIdx SpinIdx ℚ) * u.2.2
      simp only [one_smul, Matrix.one_mul, and_self]
  · simpa only [neg_one_smul] using liftVisRCentral

/-- Every signed unphased spin matrix occurs as the `W` block of a liftable element. -/
theorem liftVisRSpinLift (μ : leech.carrier) (c : ℚ) (hc : c = 1 ∨ c = -1) :
    ∃ g : liftableSubgroup, liftVisRBlocks (g : AutO) (c • liftMonoQmat μ) := by
  have hs := extraSign_eq_one_or μ
  have hcs : c * extraSign μ = 1 ∨ c * extraSign μ = -1 := by
    rcases hc with rfl | rfl <;> rcases hs with hs | hs <;> rw [hs] <;> norm_num
  obtain ⟨g, hg⟩ := liftVisRScalar (c * extraSign μ) hcs
  have hs2 : extraSign μ * extraSign μ = 1 := by
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  refine ⟨g * extraLiftable μ, ?_⟩
  have h := liftVisRBlocks_mul _ _ _ _ hg (liftVisRExtra μ)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_assoc, hs2, mul_one] at h
  exact h

/-- The chosen lift has the prescribed lattice block and an extraspecial discrepancy. -/
theorem liftVisRChosen (p : Pvis) :
    ∃ (μ : leech.carrier) (c : ℚ) (g : liftableSubgroup),
      (c = 1 ∨ c = -1) ∧ ∀ u : SpaceB,
        ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
          (thetaA (mat p.1.2) u.1,
            griessTrX (liftSignX (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2)
              (griessTrX u.2.1)),
            (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * (c • liftMonoQmat μ) *
              u.2.2 * mat p.1.2) := by
  obtain ⟨μ, c, hc, hcharge⟩ := liftVisRCharge p
  obtain ⟨g, _, hg⟩ := liftLiftableOfChargeMatrix (liftVisIsometry p.1.2)
    (liftVisIsometry_form p.1.2) (liftVisIsometry_surjective p.1.2) _ hcharge
  refine ⟨μ, c, g, hc, fun u => ?_⟩
  rw [hg]
  refine Prod.ext (liftVisSymMat _ _) (Prod.ext rfl ?_)
  rw [liftVisBlockMatrix, Matrix.transpose_transpose]

theorem liftVisRFactor (p : Pvis) (D : Matrix SpinIdx SpinIdx ℚ)
    (X : SpaceX → SpaceX) (g e : AutO)
    (hg : ∀ u : SpaceB, (g : SpaceB ≃ₗ[ℚ] SpaceB) u =
      (thetaA (mat p.1.2) u.1, X u.2.1,
        (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * D * u.2.2 * mat p.1.2))
    (he : liftVisRBlocks e D) : g = liftVisAut p * e := by
  have hpar : IsParityAut (g : SpaceB ≃ₗ[ℚ] SpaceB) := by
    refine ⟨g.property.1, g.property.2, fun u => ?_⟩
    rw [xB_apply, hg, hg, xB_apply]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  apply Subtype.ext
  apply liftVisParity_ext hpar (liftVisRParity_mul _ _ (liftVisParity p) he.1)
  · apply LinearMap.ext
    intro A
    change ((g : SpaceB ≃ₗ[ℚ] SpaceB) (inA A)).1 =
      (thetaEquiv p ((e : SpaceB ≃ₗ[ℚ] SpaceB) (inA A))).1
    rw [hg, thetaEquiv_apply, theta_apply]
    change thetaA (mat p.1.2) A =
      thetaA (mat p.1.2) (((e : SpaceB ≃ₗ[ℚ] SpaceB) (inA A)).1)
    rw [(he.2 _).1]
  · apply LinearMap.ext
    intro N
    change ((g : SpaceB ≃ₗ[ℚ] SpaceB) (inW N)).2.2 =
      (thetaEquiv p ((e : SpaceB ≃ₗ[ℚ] SpaceB) (inW N))).2.2
    rw [hg, thetaEquiv_apply, theta_apply]
    change (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * D * N * mat p.1.2 =
      thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2)
        (((e : SpaceB ≃ₗ[ℚ] SpaceB) (inW N)).2.2)
    rw [(he.2 _).2, thetaW_apply]
    exact congrArg (fun M => M * mat p.1.2) (Matrix.mul_assoc _ _ _)

/-- Every visible pair lifts to an automorphism of the moonshine module. -/
theorem liftVisRLiftable (p : Pvis) : IsVnatLiftable (liftVisAut p) := by
  obtain ⟨μ, c, g, hc, hg⟩ := liftVisRChosen p
  obtain ⟨e, he⟩ := liftVisRSpinLift μ c hc
  have heq := liftVisRFactor p _
    (fun x => griessTrX
      (liftSignX (liftVisIsometry p.1.2) (liftVisIsometry_form p.1.2) (griessTrX x)))
    (g : AutO) (e : AutO) hg he
  have hcancel : (g : AutO) * (e : AutO)⁻¹ = liftVisAut p := by
    rw [heq, mul_inv_cancel_right]
  rw [← hcancel]
  exact (mem_liftableSubgroup.mp g.property).mul
    (mem_liftableSubgroup.mp e.property).inv

/-- The visible subgroup, in the precise `AutO` liftability formulation. -/
theorem liftVisRGvis (g : AutO) (hg : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis) :
    IsVnatLiftable g := by
  obtain ⟨p, hp⟩ := mem_Gvis.mp hg
  have h : liftVisAut p = g := Subtype.ext hp
  rw [← h]
  exact liftVisRLiftable p

/-- Membership in `Gvis` supplies the proof needed to regard a visible map as `AutO`. -/
theorem liftVisRAllVisible : ∀ (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Gvis),
    IsVnatLiftable ⟨g, Gvis_le_AutO hg⟩ := by
  intro g hg
  exact liftVisRGvis ⟨g, Gvis_le_AutO hg⟩ hg

/-- Each visible action is the underlying orthogonal action of a liftable element. -/
theorem liftVisRExists (p : Pvis) :
    ∃ h : liftableSubgroup, (h : AutO) = liftVisAut p :=
  ⟨⟨liftVisAut p, mem_liftableSubgroup.mpr (liftVisRLiftable p)⟩, rfl⟩

/-- The resulting Monster lift restricts to exactly the specified visible action. -/
theorem liftVisRRestrict (p : Pvis) :
    ∃ h : liftableSubgroup,
      vnatWeightTwoRestrict (monsterLift h) = griessConj (thetaEquiv p) := by
  obtain ⟨h, hh⟩ := liftVisRExists p
  refine ⟨h, ?_⟩
  rw [monsterLift_restrict, hh]
  rfl

end VOA.Moonshine.ConwayNorton.M8
