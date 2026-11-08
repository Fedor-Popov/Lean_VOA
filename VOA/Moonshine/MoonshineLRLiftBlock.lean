import VOA.Moonshine.MoonshineCNGriessUntwisted
import VOA.Moonshine.MoonshineLRLiftTwisted3
import VOA.Moonshine.MoonshineLRLiftExtraAut

/-!
# Untwisted blocks of the lattice and extraspecial lifts

The oscillator action uses column vectors. The momentum action retains the comparison
coboundary, and the extraspecial action is the integral pairing character.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.Moonshine.TrialityTw VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.LatGen VOA.IntegralLattice HeisenbergN MvPolynomial Matrix
open scoped TensorProduct

theorem liftBlockQuad_coe (u v : Fin (rank leech) → ℂ) :
    (isingQuad u v : LatModuleGen leech) = latStateGen leech
      ((∑ a, u a • X (0, a)) * (∑ b, v b • X (0, b))) 0 := by
  simp only [isingQuad, isingQuadRow, Submodule.coe_sum, Submodule.coe_smul,
    qP, qL, quadSt_eq, latStateGen, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  simp only [← TensorProduct.sum_tmul, TensorProduct.smul_tmul']

/-- Arbitrary quadratic oscillator states transform by the oscillator matrix. -/
theorem liftBlockLat_quad (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (u v : Fin (rank leech) → ℂ) :
    latMorph leech leech ι (isingQuad u v : LatModuleGen leech) =
      (isingQuad (oscMatrix leech leech ι *ᵥ u)
        (oscMatrix leech leech ι *ᵥ v) : LatModuleGen leech) := by
  rw [liftBlockQuad_coe, liftBlockQuad_coe, latMorph_latStateGen, latCob_zero,
    map_zero, one_smul, map_mul, fockMap_Xcomb _ _ _ rfl,
    fockMap_Xcomb _ _ _ rfl]

/-- The two opposite charges have the same comparison coboundary. -/
theorem liftBlockLat_frameX0P (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (α : leech.carrier) :
    latMorph leech leech ι (frameX0P α : LatModuleGen leech) =
      latCob leech leech ι α • (frameX0P (ι α) : LatModuleGen leech) := by
  change latMorph leech leech ι
    (latChargeGen leech α + latChargeGen leech (-α)) = _
  simp only [map_add, latMorph, latMorphC_latChargeGen, latCob_neg, map_neg]
  exact (smul_add _ _ _).symm

/-- Expansion of a matrix congruence into its column rank-one terms. -/
theorem liftBlockMatrix_expand {m n : Type*} [Fintype n]
    (Q : Matrix m n ℂ) (M : Matrix n n ℂ) :
    Q * M * Qᵀ = ∑ i, ∑ j, M i j • vecMulVec (fun a => Q a i) (fun b => Q b j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The elementary frame quadratic is a rank-one coordinate quadratic. -/
theorem liftBlockQuad_single (a b : Fin (rank leech)) :
    isingQuad (Pi.single a 1) (Pi.single b 1) = qP a b := by
  classical
  simp [isingQuad, isingQuadRow]

/-- Rational matrix of the lattice map in rational coordinates, acting on column vectors. -/
def liftBlockMatrix (ι : leech.carrier →ₗ[ℤ] leech.carrier) :
    Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => (vec (ι (conwayAxis (piPerm.symm j))) (piPerm.symm i) : ℚ) / 8

/-- Its rational entries give precisely the action on the rational lattice coordinates. -/
theorem liftBlockMatrix_vec (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (β : leech.carrier) :
    liftBlockMatrix ι *ᵥ (fun j => (vec β (piPerm.symm j) : ℚ)) =
      fun i => (vec (ι β) (piPerm.symm i) : ℚ) := by
  funext i
  have h := congrArg (fun α => vecHom (ι α) (piPerm.symm i))
    (eight_smul_eq_sum_conwayAxis β)
  simp only [map_zsmul, map_sum, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] at h
  change (8 : ℤ) * vec (ι β) (piPerm.symm i) =
    ∑ j, vec β j * vec (ι (conwayAxis j)) (piPerm.symm i) at h
  have hq : (8 : ℚ) * (vec (ι β) (piPerm.symm i) : ℚ) =
      ∑ j, (vec β j : ℚ) * (vec (ι (conwayAxis j)) (piPerm.symm i) : ℚ) := by
    exact_mod_cast h
  simp only [Matrix.mulVec, dotProduct, liftBlockMatrix]
  rw [Equiv.sum_comp piPerm.symm (fun j =>
    (vec (ι (conwayAxis j)) (piPerm.symm i) : ℚ) / 8 * (vec β j : ℚ))]
  calc
    _ = (∑ j, (vec β j : ℚ) *
        (vec (ι (conwayAxis j)) (piPerm.symm i) : ℚ)) / 8 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [← hq]; ring

/-- The rational coordinate matrix agrees with the oscillator action after the frame change. -/
theorem liftBlockMatrix_frame (ι : leech.carrier →ₗ[ℤ] leech.carrier) :
    conwayFrame * axiomToConway (liftBlockMatrix ι) =
      oscMatrix leech leech ι * conwayFrame := by
  ext a j
  have h := congrFun (oscMatrix_chargeCoord leech leech leech_posDef ι (conwayAxis j)) a
  change _ = ∑ b, oscMatrix leech leech ι a b * chargeCoord leech (conwayAxis j) b
  rw [show (∑ b, oscMatrix leech leech ι a b * chargeCoord leech (conwayAxis j) b) =
    chargeCoord leech (ι (conwayAxis j)) a from h]
  simp only [Matrix.mul_apply, axiomToConway_apply, liftBlockMatrix,
    Equiv.symm_apply_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat,
    conwayFrame, Matrix.of_apply]
  calc
    _ = (∑ i, (vec (ι (conwayAxis j)) i : ℂ) *
        chargeCoord leech (conwayAxis i) a) / 8 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by rw [sum_vec_mul_chargeCoord]; ring

/-- Pull coefficients back along the permutation and multiply by its rational weights. -/
def liftBlockShortX (p : Equiv.Perm ShortIdx) (r : ShortIdx → ℚ) (x : SpaceX) : SpaceX :=
  fun d => r (p.symm d) * x (p.symm d)

section Isometry

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
  (hsurj : Function.Surjective ι)

theorem liftBlockPlus_quad (u v : Fin (rank leech) → ℂ) :
    leechPlusLatMorphAut ι hι hsurj (isingQuad u v) =
      isingQuad (oscMatrix leech leech ι *ᵥ u) (oscMatrix leech leech ι *ᵥ v) :=
  Subtype.ext (liftBlockLat_quad ι u v)

/-- The frame matrix transforms by `Q M Qᵀ`. -/
theorem liftBlockPlus_frameQuad
    (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    leechPlusLatMorphAut ι hι hsurj (frameQuad M) =
      frameQuad (oscMatrix leech leech ι * M * (oscMatrix leech leech ι)ᵀ) := by
  rw [liftBlockMatrix_expand]
  simp only [map_sum, map_smul, ← isingQuad_eq_frameQuad]
  rw [frameQuad_apply]
  simp only [map_sum, map_smul, ← liftBlockQuad_single, liftBlockPlus_quad,
    Matrix.mulVec_single_one]
  rfl

/-- The rational matrix block is conjugated in the column-vector convention. -/
theorem liftBlockPlus_matDict (M : Matrix (Fin 24) (Fin 24) ℚ) :
    leechPlusLatMorphAut ι hι hsurj (matDict M) =
      matDict (liftBlockMatrix ι * M * (liftBlockMatrix ι)ᵀ) := by
  simp only [matDict_apply, conwayQuad_apply, liftBlockPlus_frameQuad,
    conwayToFrame_apply, axiomToConway_mul, axiomToConway_transpose,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 2
  have ht := congrArg Matrix.transpose (liftBlockMatrix_frame ι)
  simp only [Matrix.transpose_mul] at ht
  calc
    _ = (oscMatrix leech leech ι * conwayFrame) * axiomToConway M *
        (conwayFrameᵀ * (oscMatrix leech leech ι)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = (conwayFrame * axiomToConway (liftBlockMatrix ι)) * axiomToConway M *
        ((axiomToConway (liftBlockMatrix ι))ᵀ * conwayFrameᵀ) := by
      rw [← liftBlockMatrix_frame, ← ht]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The rational congruence preserves symmetric matrices. -/
def liftBlockSymMat (A : symMat) : symMat :=
  ⟨liftBlockMatrix ι * (A : Matrix (Fin 24) (Fin 24) ℚ) * (liftBlockMatrix ι)ᵀ,
    mem_symMat.mpr (by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, mem_symMat.mp A.2,
        Matrix.mul_assoc])⟩

/-- The matrix block formula inside the weight-two part of `V♮`. -/
theorem liftBlockNat_symBlock (ζ : ShortIdx → ℂ) (A : symMat) :
    liftTwVnatAut ι hι hsurj (untwistedDictNat ζ (symBlock A) : Vnat) =
      (untwistedDictNat ζ (symBlock (liftBlockSymMat ι A)) : Vnat) := by
  change liftTwVnatAut ι hι hsurj ((untwistedDict ζ (symBlock A), 0) : Vnat) =
    ((untwistedDict ζ (symBlock (liftBlockSymMat ι A)), 0) : Vnat)
  simp only [liftTwVnatAut_apply, untwistedDict_symBlock, liftBlockPlus_matDict, map_zero]
  rfl

theorem liftBlockPlus_frameX0P (α : leech.carrier) :
    leechPlusLatMorphAut ι hι hsurj (frameX0P α) =
      latCob leech leech ι α • frameX0P (ι α) :=
  Subtype.ext (liftBlockLat_frameX0P ι α)

/-- The unreindexed short block, with its exact phase and coboundary factors. -/
theorem liftBlockPlus_shortDict (ζ : ShortIdx → ℂ) (x : SpaceX) :
    leechPlusLatMorphAut ι hι hsurj (shortDict ζ x) =
      ∑ c, ((x c : ℂ) * ζ c * latCob leech leech ι (shortVec c)) •
        frameX0P (ι (shortVec c)) := by
  simp only [shortDict_apply, map_sum, map_smul,
    liftBlockPlus_frameX0P, smul_smul]

/-- The unreindexed short block inside `V♮₂`. -/
theorem liftBlockNat_shortBlock_sum (ζ : ShortIdx → ℂ) (x : SpaceX) :
    liftTwVnatAut ι hι hsurj (untwistedDictNat ζ (shortBlock x) : Vnat) =
      ((∑ c, ((x c : ℂ) * ζ c * latCob leech leech ι (shortVec c)) •
        frameX0P (ι (shortVec c)), 0) : Vnat) := by
  change liftTwVnatAut ι hι hsurj ((untwistedDict ζ (shortBlock x), 0) : Vnat) = _
  simp only [liftTwVnatAut_apply, untwistedDict_shortBlock, liftBlockPlus_shortDict, map_zero]

/-- Reindexing is valid once the representative permutation and rational phase ratios exist.
The sign in the representative choice contributes no extra factor because `x_{-α} = x_α`. -/
theorem liftBlockPlus_shortDict_reindex (ζ : ShortIdx → ℂ) (x : SpaceX)
    (p : Equiv.Perm ShortIdx)
    (hp : ∀ c, ι (shortVec c) = shortVec (p c) ∨ ι (shortVec c) = -shortVec (p c))
    (r : ShortIdx → ℚ)
    (hr : ∀ c, (r c : ℂ) * ζ (p c) = ζ c * latCob leech leech ι (shortVec c)) :
    leechPlusLatMorphAut ι hι hsurj (shortDict ζ x) =
      shortDict ζ (liftBlockShortX p r x) := by
  rw [liftBlockPlus_shortDict, shortDict_apply]
  rw [← Equiv.sum_comp p (fun d =>
    ((liftBlockShortX p r x d : ℂ) * ζ d) • frameX0P (shortVec d))]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hx : frameX0P (ι (shortVec c)) = frameX0P (shortVec (p c)) := by
    rcases hp c with h | h
    · rw [h]
    · rw [h, frameX0P_neg_eq]
  rw [hx]
  simp only [liftBlockShortX, Equiv.symm_apply_apply, Rat.cast_mul]
  congr 1
  calc
    _ = (x c : ℂ) * (ζ c * latCob leech leech ι (shortVec c)) := by ring
    _ = _ := by rw [← hr]; ring

/-- Explicitly, the rational rescaling is the phase ratio times the coboundary. -/
theorem liftBlockShort_ratio (ζ : ShortIdx → ℂ) (p : Equiv.Perm ShortIdx)
    (r : ShortIdx → ℚ)
    (hr : ∀ c, (r c : ℂ) * ζ (p c) = ζ c * latCob leech leech ι (shortVec c))
    (c : ShortIdx) (hz : ζ (p c) ≠ 0) :
    (r c : ℂ) = ζ c * latCob leech leech ι (shortVec c) / ζ (p c) :=
  (eq_div_iff hz).mpr (hr c)

/-- The same rational reindexing in the weight-two dictionary of `V♮`. -/
theorem liftBlockNat_shortBlock_reindex (ζ : ShortIdx → ℂ) (x : SpaceX)
    (p : Equiv.Perm ShortIdx)
    (hp : ∀ c, ι (shortVec c) = shortVec (p c) ∨ ι (shortVec c) = -shortVec (p c))
    (r : ShortIdx → ℚ)
    (hr : ∀ c, (r c : ℂ) * ζ (p c) = ζ c * latCob leech leech ι (shortVec c)) :
    liftTwVnatAut ι hι hsurj (untwistedDictNat ζ (shortBlock x) : Vnat) =
      (untwistedDictNat ζ (shortBlock (liftBlockShortX p r x)) : Vnat) := by
  change liftTwVnatAut ι hι hsurj ((untwistedDict ζ (shortBlock x), 0) : Vnat) =
    ((untwistedDict ζ (shortBlock (liftBlockShortX p r x)), 0) : Vnat)
  simp only [liftTwVnatAut_apply, untwistedDict_shortBlock,
    liftBlockPlus_shortDict_reindex ι hι hsurj ζ x p hp r hr, map_zero]

end Isometry

/-- Extraspecial elements fix every oscillator quadratic state. -/
theorem liftBlockExtra_quad (μ : leech.carrier) (u v : Fin (rank leech) → ℂ) :
    extraLeechPlusAut μ (isingQuad u v) = isingQuad u v := by
  apply Subtype.ext
  change chiLat leech (extraPairChar leech μ) (isingQuad u v : LatModuleGen leech) = _
  rw [liftBlockQuad_coe, chiLat_latStateGen, chiSign_zero, one_smul]

theorem liftBlockExtra_frameX0P (μ α : leech.carrier) :
    extraLeechPlusAut μ (frameX0P α) =
      (-1 : ℂ) ^ (leech.form μ α) • frameX0P α := by
  apply Subtype.ext
  change chiLat leech (extraPairChar leech μ)
    (latChargeGen leech α + latChargeGen leech (-α)) = _
  simp only [map_add, latChargeGen, chiLat_latStateGen, chiSign_neg,
    extraPairChar_sign]
  exact (smul_add _ _ _).symm

theorem liftBlockExtra_matDict (μ : leech.carrier)
    (M : Matrix (Fin 24) (Fin 24) ℚ) :
    extraLeechPlusAut μ (matDict M) = matDict M := by
  simp only [matDict_apply, conwayQuad_eq_sum_dV, ← isingQuad_chargeCoord,
    map_smul, map_sum, liftBlockExtra_quad]

/-- The rational diagonal action on the short coordinates, with integer exponents. -/
def liftBlockExtraX (μ : leech.carrier) (x : SpaceX) : SpaceX :=
  fun c => (-1 : ℚ) ^ (leech.form μ (shortVec c)) * x c

theorem liftBlockExtra_shortDict (μ : leech.carrier) (ζ : ShortIdx → ℂ)
    (x : SpaceX) :
    extraLeechPlusAut μ (shortDict ζ x) = shortDict ζ (liftBlockExtraX μ x) := by
  simp only [shortDict_apply, map_sum, map_smul,
    liftBlockExtra_frameX0P, smul_smul, liftBlockExtraX]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  push_cast
  ring

/-- The matrix block of the weight-two dictionary is fixed in `V♮`. -/
theorem liftBlockExtraNat_symBlock (μ : leech.carrier) (ζ : ShortIdx → ℂ)
    (A : symMat) :
    extraVnatAut μ (untwistedDictNat ζ (symBlock A) : Vnat) =
      (untwistedDictNat ζ (symBlock A) : Vnat) := by
  change extraVnatAut μ ((untwistedDict ζ (symBlock A), 0) : Vnat) =
    ((untwistedDict ζ (symBlock A), 0) : Vnat)
  simp only [extraVnatAut_apply, untwistedDict_symBlock, liftBlockExtra_matDict, map_zero]

/-- The short block of the weight-two dictionary acquires the pairing signs in `V♮`. -/
theorem liftBlockExtraNat_shortBlock (μ : leech.carrier) (ζ : ShortIdx → ℂ)
    (x : SpaceX) :
    extraVnatAut μ (untwistedDictNat ζ (shortBlock x) : Vnat) =
      (untwistedDictNat ζ (shortBlock (liftBlockExtraX μ x)) : Vnat) := by
  change extraVnatAut μ ((untwistedDict ζ (shortBlock x), 0) : Vnat) =
    ((untwistedDict ζ (shortBlock (liftBlockExtraX μ x)), 0) : Vnat)
  simp only [extraVnatAut_apply, untwistedDict_shortBlock, liftBlockExtra_shortDict, map_zero]

end VOA.Moonshine.ConwayNorton.M8
