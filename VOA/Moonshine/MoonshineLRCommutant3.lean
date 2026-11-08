import VOA.Moonshine.MoonshineLRCommutant2
import VOA.Moonshine.MoonshineLRLiftXi
import VOA.Moonshine.MonsterGriess.ParityEqualsVisible

/-!
# Lattice actions linking the rational Griess commutant
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.SpinLattice VOA.Moonshine.MonsterGriess.Visible
open VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.MonsterGriess.ScalarKernel
open Matrix
open scoped BigOperators

/-- Block-preserving rational lattice lifts belong to the visible subgroup. -/
theorem commutL_mem_Gvis (g : AutO) (A : symMat → symMat) (X : SpaceX → SpaceX)
    (R : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hg : ∀ u : SpaceB, (g : SpaceB ≃ₗ[ℚ] SpaceB) u =
      (A u.1, X u.2.1, R * u.2.2 * M)) :
    (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
  apply (Parity.rational_parity_centralizer_equals_visible.1 _).mp
  refine ⟨g.property.1, g.property.2, fun u => ?_⟩
  rw [xB_apply, hg, hg, xB_apply]
  simp only [Matrix.mul_neg, Matrix.neg_mul]

/-- Rational normalized charge coordinates give visible lifts with all three blocks. -/
theorem commutL_charge_blocks (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (hsurj : Function.Surjective ι) (R : Matrix SpinIdx SpinIdx ℚ)
    (hR : ∀ v : SpinRep, liftSpinCharge ι hι v = R.map (Rat.castHom ℂ) *ᵥ v) :
    ∃ g : liftableSubgroup,
      monsterLift g = liftTwVnatAut ι hι hsurj ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Generated.Gmat ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
        (liftBlockSymMat ι u.1, griessTrX (liftSignX ι hι (griessTrX u.2.1)),
          R * u.2.2 * (liftBlockMatrix ι)ᵀ) := by
  obtain ⟨g, hg, hb⟩ := liftLiftableOfChargeMatrix ι hι hsurj R hR
  have hv := commutL_mem_Gvis (g : AutO) (liftBlockSymMat ι)
    (fun x => griessTrX (liftSignX ι hι (griessTrX x))) R (liftBlockMatrix ι)ᵀ hb
  exact ⟨g, hg, hv, Generated.Hmat_le_Gmat hv, hb⟩

/-- Coordinate matrices can be identified on the integral lattice. -/
theorem commutL_blockMatrix (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : ∀ α : leech.carrier,
      ratVec (leechEquiv (ι α)) = M *ᵥ ratVec (leechEquiv α)) :
    liftBlockMatrix ι = M := by
  ext i j
  have h := congrFun (hM (conwayAxis (piPerm.symm j))) i
  have he : ratVec (leechEquiv (conwayAxis (piPerm.symm j))) =
      (8 : ℚ) • Pi.single j 1 := by
    funext k
    change ((vec (conwayAxis (piPerm.symm j)) (piPerm.symm k) : ℤ) : ℚ) = _
    rw [vec_conwayAxis]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Equiv.apply_eq_iff_eq, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
      Int.cast_one, Int.cast_zero]
  rw [he, Matrix.mulVec_smul, Matrix.mulVec_single_one] at h
  change _ / 8 = M i j
  change (vec (ι (conwayAxis (piPerm.symm j))) (piPerm.symm i) : ℚ) =
    (8 : ℚ) * M i j at h
  rw [h]
  simp

/-- The oscillator matrix of a coordinate permutation uses the inverse permutation. -/
theorem commutL_mathieu_matrix (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) :
    liftBlockMatrix (liftGenMathieu σ hσ) = Equiv.Perm.permMatrix ℚ σ.symm := by
  apply commutL_blockMatrix
  intro α
  rw [Matrix.permMatrix_mulVec]
  funext i
  have h := congrFun (liftGenMathieu_coordinates σ hσ α) i
  exact congrArg (fun z : ℤ => (z : ℚ)) h

/-- Every code-preserving coordinate permutation has a visible rational lift. -/
theorem commutL_mathieu_blocks (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) :
    ∃ g : liftableSubgroup,
      monsterLift g = liftTwVnatAut (liftGenMathieu σ hσ)
        (liftGenMathieu_isometry σ hσ) (liftGenMathieu_surjective σ hσ) ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Generated.Gmat ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
        (thetaA (σ.permMatrix ℚ) u.1,
          griessTrX (liftSignX (liftGenMathieu σ hσ)
            (liftGenMathieu_isometry σ hσ) (griessTrX u.2.1)),
          liftGenSignedMatrix (liftSpinMathieuPerm σ hσ) (liftSpinMathieuSigns σ hσ) *
            u.2.2 * σ.permMatrix ℚ) := by
  obtain ⟨g, hg, hv, hm, hb⟩ := commutL_charge_blocks (liftGenMathieu σ hσ)
    (liftGenMathieu_isometry σ hσ) (liftGenMathieu_surjective σ hσ) _
    (liftSpinSigned_spec _ _ (fun _ h => liftSpinMathieu_frame σ hσ h))
  refine ⟨g, hg, hv, hm, fun u => ?_⟩
  rw [hb]
  simp only [liftBlockSymMat, commutL_mathieu_matrix, Matrix.transpose_permMatrix,
    Equiv.Perm.inv_def, Equiv.symm_symm, thetaA]
  rfl

/-- The nonmonomial oscillator matrix agrees with its explicit rational matrix. -/
theorem commutL_xi_matrix : liftBlockMatrix liftXi = liftXiMatrix :=
  commutL_blockMatrix liftXi liftXiMatrix liftXiMatrix_coordinates

/-- The nonmonomial lift is visible and has explicit rational block actions. -/
theorem commutL_xi_blocks :
    ∃ g : liftableSubgroup,
      monsterLift g = liftTwVnatAut liftXi liftXi_isometry liftXi_surjective ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis ∧
      ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Generated.Gmat ∧
      ∀ u : SpaceB, ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) u =
        (thetaA liftXiMatrixᵀ u.1,
          griessTrX (liftSignX liftXi liftXi_isometry (griessTrX u.2.1)),
          liftXiSpinMatrix * u.2.2 * liftXiMatrixᵀ) := by
  obtain ⟨g, hg, hv, hm, hb⟩ := commutL_charge_blocks liftXi liftXi_isometry
    liftXi_surjective liftXiSpinMatrix liftXiSpinMatrix_spec
  refine ⟨g, hg, hv, hm, fun u => ?_⟩
  rw [hb]
  simp only [liftBlockSymMat, commutL_xi_matrix, thetaA, Matrix.transpose_transpose]
  rfl

/-- The transferred signed short-coordinate action fixes zero. -/
theorem commutL_short_zero (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β) :
    griessTrX (liftSignX ι hι (griessTrX 0)) = 0 := by
  funext c
  simp [griessTrX, liftSignX, liftBlockShortX]

/-- A commuting column diagonal commutes with the lattice matrix of a visible action. -/
theorem commutL_column_matrix (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Generated.Gmat)
    (R : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hR : Rᵀ * R = 1) (hW : ∀ N : SpaceW, g (0, 0, N) = (0, 0, R * N * M)) :
    M * Matrix.diagonal (commutOddScalar T 0) =
      Matrix.diagonal (commutOddScalar T 0) * M := by
  have hc := (commutB_Gmat_columns T h).1
  have he (N : SpaceW) :
      N * (M * Matrix.diagonal (commutOddScalar T 0)) =
        N * (Matrix.diagonal (commutOddScalar T 0) * M) := by
    have e := h g hg (0, 0, N)
    rw [hW, hc, hc, hW] at e
    have e' := congrArg (fun u : SpaceB => Rᵀ * u.2.2) e
    simpa only [← Matrix.mul_assoc, hR, Matrix.one_mul] using e'
  ext i j
  have e := congrArg (fun N : SpaceW => N spinIdxBase j)
    (he (Matrix.single spinIdxBase i 1))
  simpa only [Matrix.single_mul_apply_same, one_mul] using e

/-- Code-preserving coordinate permutations identify the corresponding column scalars. -/
theorem commutL_column_perm (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) (i : Fin 24) :
    commutOddScalar T 0 (σ i) = commutOddScalar T 0 i := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_mathieu_blocks σ hσ
  have he := commutL_column_matrix T h _ hg _ (σ.permMatrix ℚ)
    (liftGenSignedMatrix_orthogonal (liftSpinMathieuPerm σ hσ)
      (liftSpinMathieuSigns σ hσ)) (fun N => by
        rw [hb]
        simp only [map_zero, commutL_short_zero])
  have e := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℚ => M i (σ i)) he
  simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul,
    PEquiv.toMatrix_toPEquiv_apply, Pi.single_eq_same, one_mul, mul_one] using e

/-- The column diagonal also commutes with the nonmonomial lattice matrix. -/
theorem commutL_column_xi (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    liftXiMatrixᵀ * Matrix.diagonal (commutOddScalar T 0) =
      Matrix.diagonal (commutOddScalar T 0) * liftXiMatrixᵀ := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_xi_blocks
  apply commutL_column_matrix T h _ hg liftXiSpinMatrix liftXiMatrixᵀ
    liftXiSpinMatrix_orthogonal
  intro N
  rw [hb]
  simp only [map_zero, commutL_short_zero]

/-- Checking a permutation and its inverse on the twelve basis words suffices. -/
theorem commutL_preservesCode_basis (σ : Equiv.Perm (Fin 24))
    (hf : ∀ i, permLin (ZMod 2) σ (B i) ∈ Code.C)
    (hb : ∀ i, permLin (ZMod 2) σ.symm (B i) ∈ Code.C) :
    liftGenPreservesCode σ := by
  have hm (τ : Equiv.Perm (Fin 24)) (hτ : ∀ i, permLin (ZMod 2) τ (B i) ∈ Code.C)
      (x : Fin 24 → ZMod 2) (hx : x ∈ Code.C) : permLin (ZMod 2) τ x ∈ Code.C := by
    rw [eq_comb_of_mem_C hx, map_sum]
    exact Code.C.sum_mem fun i _ => by
      rw [map_smul]
      exact Code.C.smul_mem _ (hτ i)
  intro x
  refine ⟨fun hx => ?_, hm σ hf x⟩
  have he : permLin (ZMod 2) σ.symm (permLin (ZMod 2) σ x) = x := by
    ext i
    simp [permLin_apply]
  simpa only [he] using hm σ.symm hb _ hx

/-- An explicit Golay coordinate permutation used for point transitivity. -/
def commutL_pointPermA : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15,
    8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15,
    8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  left_inv := by decide
  right_inv := by decide

theorem commutL_pointPermA_code : liftGenPreservesCode commutL_pointPermA := by
  apply commutL_preservesCode_basis <;> decide

/-- An explicit Golay coordinate permutation used for point transitivity. -/
def commutL_pointPermB : Equiv.Perm (Fin 24) where
  toFun := ![8, 10, 11, 9, 14, 12, 13, 15, 20, 22, 23, 21,
    18, 16, 17, 19, 7, 5, 4, 6, 1, 3, 2, 0]
  invFun := ![23, 20, 22, 21, 18, 17, 19, 16, 0, 3, 1, 2,
    5, 6, 4, 7, 13, 14, 12, 15, 8, 11, 9, 10]
  left_inv := by decide
  right_inv := by decide

theorem commutL_pointPermB_code : liftGenPreservesCode commutL_pointPermB := by
  apply commutL_preservesCode_basis <;> decide

/-- The two coordinate permutations have one orbit on the twenty-four points. -/
theorem commutL_point_transitive {K : Type*} (d : Fin 24 → K)
    (hA : ∀ i, d (commutL_pointPermA i) = d i)
    (hB : ∀ i, d (commutL_pointPermB i) = d i) (i : Fin 24) : d i = d 0 := by
  have h0 : d 0 = d 0 := rfl
  have h8 : d 8 = d 0 := (hB 0).trans h0
  have h12 : d 12 = d 0 := (hA 8).trans h8
  have h20 : d 20 = d 0 := (hB 8).trans h8
  have h18 : d 18 = d 0 := (hB 12).trans h12
  have h16 : d 16 = d 0 := (hA 20).trans h20
  have h1 : d 1 = d 0 := (hB 20).trans h20
  have h22 : d 22 = d 0 := (hA 18).trans h18
  have h4 : d 4 = d 0 := (hB 18).trans h18
  have h7 : d 7 = d 0 := (hB 16).trans h16
  have h10 : d 10 = d 0 := (hB 1).trans h1
  have h2 : d 2 = d 0 := (hB 22).trans h22
  have h14 : d 14 = d 0 := (hB 4).trans h4
  have h15 : d 15 = d 0 := (hB 7).trans h7
  have h23 : d 23 = d 0 := (hB 10).trans h10
  have h11 : d 11 = d 0 := (hB 2).trans h2
  have h17 : d 17 = d 0 := (hB 14).trans h14
  have h19 : d 19 = d 0 := (hB 15).trans h15
  have h21 : d 21 = d 0 := (hB 11).trans h11
  have h5 : d 5 = d 0 := (hB 17).trans h17
  have h6 : d 6 = d 0 := (hB 19).trans h19
  have h3 : d 3 = d 0 := (hB 21).trans h21
  have h13 : d 13 = d 0 := (hB 6).trans h6
  have h9 : d 9 = d 0 := (hB 3).trans h3
  fin_cases i <;> assumption

/-- The generated-group commutant has a single spin-column scalar. -/
theorem commutL_columns_equal (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (i : Fin 24) :
    commutOddScalar T 0 i = commutOddScalar T 0 0 :=
  commutL_point_transitive (commutOddScalar T 0)
    (commutL_column_perm T h commutL_pointPermA commutL_pointPermA_code)
    (commutL_column_perm T h commutL_pointPermB commutL_pointPermB_code) i

/-- One scalar acts on the entire spin-tensor space and every odd short line. -/
theorem commutL_spin_odd_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    (∀ N : SpaceW, T (0, 0, N) =
      commutOddScalar T 0 0 • ((0, 0, N) : SpaceB)) ∧
    ∀ (c : C₀) (i : Fin 24), T (0, Xlift (rOdd c i), 0) =
      commutOddScalar T 0 0 • ((0, Xlift (rOdd c i), 0) : SpaceB) := by
  obtain ⟨hW, hX⟩ := commutB_Gmat_columns T h
  refine ⟨fun N => ?_, fun c i => ?_⟩
  · rw [hW]
    ext
    · simp
    · simp
    · simp only [Matrix.mul_diagonal, Prod.smul_snd, Matrix.smul_apply,
        smul_eq_mul, commutL_columns_equal T h, mul_comm]
  · rw [hX, commutL_columns_equal T h]

/-- The transferred short-coordinate action is a signed permutation. -/
theorem commutL_short_signed (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β) (c : ShortIdx) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ ∀ x : SpaceX,
      griessTrX (liftSignX ι hι (griessTrX x)) (liftSignPerm ι hι c) = ε * x c := by
  let ε := griessTrSign (liftSignPerm ι hι c) * liftSignWeight ι hι c * griessTrSign c
  refine ⟨ε, ?_, fun x => ?_⟩
  · rcases griessTrSign_cases (liftSignPerm ι hι c) with h₁ | h₁ <;>
      rcases liftSignWeight_sign ι hι c with h₂ | h₂ <;>
      rcases griessTrSign_cases c with h₃ | h₃ <;>
      simp only [ε, h₁, h₂, h₃] <;> norm_num
  · change griessTrSign (liftSignPerm ι hι c) *
      liftSignX ι hι (griessTrX x) (liftSignPerm ι hι c) = _
    rw [liftSignX_apply]
    change _ * (_ * (_ * x c)) = _
    dsimp only [ε]
    ring

/-- Commuting group actions transport scalar eigenvectors along signed lines. -/
theorem commutL_eigen_transport (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Generated.Gmat)
    (v w : SpaceB) (a ε : ℚ) (hε : ε ≠ 0)
    (hv : T v = a • v) (hvw : g v = ε • w) : T w = a • w := by
  have e := h g hg v
  rw [hvw, map_smul, hv, map_smul, hvw, smul_comm a ε] at e
  exact smul_right_injective _ hε e

/-- Commutation descends to the symmetric-matrix block. -/
theorem commutL_symMat_commute (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Generated.Gmat)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hA : ∀ A : symMat, g (A, 0, 0) = (thetaA M A, 0, 0)) (A : symMat) :
    (T (thetaA M A, 0, 0)).1 = thetaA M (T (A, 0, 0)).1 := by
  have e := h g hg (A, 0, 0)
  rw [hA, commutPreservesA T (fun r => h _ (commutRho_mem_Gmat r)) A, hA] at e
  exact congrArg Prod.fst e

/-- The matrix restriction commutes with every code-preserving permutation congruence. -/
theorem commutL_symMat_perm (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) (A : symMat) :
    (T (thetaA (σ.permMatrix ℚ) A, 0, 0)).1 =
      thetaA (σ.permMatrix ℚ) (T (A, 0, 0)).1 := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_mathieu_blocks σ hσ
  apply commutL_symMat_commute T h _ hg _ _ A
  intro A
  rw [hb]
  simp only [commutL_short_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- The matrix restriction commutes with the nonmonomial congruence. -/
theorem commutL_symMat_xi (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat) :
    (T (thetaA liftXiMatrixᵀ A, 0, 0)).1 =
      thetaA liftXiMatrixᵀ (T (A, 0, 0)).1 := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_xi_blocks
  apply commutL_symMat_commute T h _ hg _ _ A
  intro A
  rw [hb]
  simp only [commutL_short_zero, Matrix.mul_zero, Matrix.zero_mul]

end VOA.Moonshine.ConwayNorton.M8
