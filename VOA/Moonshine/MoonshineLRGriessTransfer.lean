import VOA.Moonshine.MoonshineCNGriessIso
import VOA.Moonshine.MoonshineLRLiftSign
import VOA.Moonshine.MoonshineLRSigmaBlock3

/-!
# Transfer of the untwisted automorphism formulas to the full Griess dictionary

The change of short coordinates is the rational involution `griessTrX`.
Its diagonal entries are exactly the diagonal lattice cocycle, not an assumed
normalisation of that cocycle by the norm.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.SigmaExist
open VOA.LatGen VOA.IntegralLattice
open scoped TensorProduct

/-- The rational sign of the diagonal cocycle in the chosen lattice basis. -/
def griessTrSign (c : ShortIdx) : ℚ := MonsterGriess.sgn (cocycleExp c.1 c.1)

theorem griessTrSign_cast (c : ShortIdx) :
    (griessTrSign c : ℂ) = latticeCocycle leech (shortVec c) (shortVec c) := by
  rw [griessTrSign, ratSgn_cast, latticeCocycle_shortVec]

theorem griessTrSign_cases (c : ShortIdx) :
    griessTrSign c = 1 ∨ griessTrSign c = -1 := by
  unfold griessTrSign MonsterGriess.sgn
  split_ifs <;> simp

theorem griessTrSign_mul_self (c : ShortIdx) : griessTrSign c * griessTrSign c = 1 := by
  rcases griessTrSign_cases c with h | h <;> rw [h] <;> norm_num

/-- The diagonal Gram contribution omitted from the chosen cocycle exponent. -/
def griessTrDiagonal (c : ShortIdx) : ℤ :=
  ∑ i, leech.form (latticeBasis leech i) (latticeBasis leech i) *
    (latticeBasis leech).repr (shortVec c) i * (latticeBasis leech).repr (shortVec c) i

theorem griessTrDiagonal_eq (c : ShortIdx) :
    2 * cocExp leech (latticeBasis leech) (shortVec c) (shortVec c) +
      griessTrDiagonal c = 4 := by
  have h := cocExp_add_swap leech (latticeBasis leech) (shortVec c) (shortVec c)
  rw [shortVec_norm] at h
  change _ + _ = 4 - griessTrDiagonal c at h
  omega

/-- An integer formula for the exact sign; norm four does not discard the basis term. -/
theorem griessTrCocycle_zpow (c : ShortIdx) :
    latticeCocycle leech (shortVec c) (shortVec c) =
      (-1 : ℂ) ^ ((4 - griessTrDiagonal c) / 2) := by
  change (-1 : ℂ) ^ cocExp leech (latticeBasis leech) (shortVec c) (shortVec c) = _
  congr 1
  have h := griessTrDiagonal_eq c
  omega

/-- The exact divisibility criterion for an unchanged short coordinate. -/
theorem griessTrCocycle_eq_one_iff (c : ShortIdx) :
    latticeCocycle leech (shortVec c) (shortVec c) = 1 ↔ 4 ∣ griessTrDiagonal c := by
  have hd := griessTrDiagonal_eq c
  change (-1 : ℂ) ^ cocExp leech (latticeBasis leech) (shortVec c) (shortVec c) = 1 ↔ _
  constructor
  · intro h
    obtain ⟨k, hk⟩ := two_dvd_of_neg_one_zpow_eq_one h
    exact ⟨1 - k, by omega⟩
  · rintro ⟨k, hk⟩
    have he : 2 ∣ cocExp leech (latticeBasis leech) (shortVec c) (shortVec c) :=
      ⟨1 - k, by omega⟩
    exact (even_iff_two_dvd.mpr he).neg_one_zpow

/-- The exact diagonal change between the old and full short coordinates. -/
def griessTrX (x : SpaceX) : SpaceX := fun c => griessTrSign c * x c

theorem griessTrX_involutive (x : SpaceX) : griessTrX (griessTrX x) = x := by
  funext c
  rw [griessTrX, griessTrX, ← mul_assoc, griessTrSign_mul_self, one_mul]

theorem griessTrX_zero : griessTrX 0 = 0 := by
  funext c
  exact mul_zero _

theorem griessTrShortDict (x : SpaceX) :
    shortDict fullShortSign x = shortDict griessShortSign (griessTrX x) := by
  simp only [shortDict_apply]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [fullShortSign_eq, griessTrX, Rat.cast_mul, griessTrSign_cast]
  ring

/-- First derive the phase change at the rational dictionary, before transferring actions. -/
theorem griessTrNat (A : symMat) (x : SpaceX) :
    griessNat (A, x, 0) = untwistedDictNat griessShortSign (A, griessTrX x, 0) := by
  apply Subtype.ext
  rw [griessNat_coe]
  change (untwistedDict fullShortSign (A, x, 0), spinDict 0) =
    (untwistedDict griessShortSign (A, griessTrX x, 0), (0 : TP))
  rw [map_zero]
  congr 1
  exact congrArg (fun y => matDict A + y) (griessTrShortDict x)

theorem griessTrIso (A : symMat) (x : SpaceX) :
    griessIso (1 ⊗ₜ[ℚ] (A, x, 0)) =
      untwistedDictNat griessShortSign (A, griessTrX x, 0) := by
  rw [griessIso_tmul, griessTrNat]

/-- The old dictionary ignores the twisted coordinate of its argument. -/
theorem griessTrOld (u : SpaceB) :
    untwistedDictNat griessShortSign u =
      griessIso (1 ⊗ₜ[ℚ] (u.1, griessTrX u.2.1, 0)) := by
  rw [griessTrIso, griessTrX_involutive]
  rfl

theorem griessTrFull {u : SpaceB} (hu : u.2.2 = 0) :
    griessIso (1 ⊗ₜ[ℚ] u) = untwistedDictNat fullShortSign u := by
  apply Subtype.ext
  exact griessIso_tmul_untwisted hu

section Isometry

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
  (hsurj : Function.Surjective ι)

/-- Co₀ lifts: matrix congruence and the conjugated signed permutation `D P D`. -/
theorem griessTrLiftSignNat_untwisted (A : symMat) (x : SpaceX) :
    liftTwVnatAut ι hι hsurj (griessIso (1 ⊗ₜ[ℚ] (A, x, 0)) : Vnat) =
      (griessIso (1 ⊗ₜ[ℚ]
        (liftBlockSymMat ι A, griessTrX (liftSignX ι hι (griessTrX x)), 0)) : Vnat) := by
  rw [griessTrIso, liftSignNat_untwisted, griessTrOld]

/-- The new short coefficient at the image of `c`, with all phase factors explicit. -/
theorem griessTrLiftX_apply (x : SpaceX) (c : ShortIdx) :
    griessTrX (liftSignX ι hι (griessTrX x)) (liftSignPerm ι hι c) =
      griessTrSign (liftSignPerm ι hι c) * liftSignWeight ι hι c *
        griessTrSign c * x c := by
  change griessTrSign _ * liftSignX ι hι (griessTrX x) _ = _
  rw [liftSignX_apply, griessTrX]
  ring

theorem griessTrLiftBlockNat_symBlock (A : symMat) :
    liftTwVnatAut ι hι hsurj (griessIso (1 ⊗ₜ[ℚ] symBlock A) : Vnat) =
      (griessIso (1 ⊗ₜ[ℚ] symBlock (liftBlockSymMat ι A)) : Vnat) := by
  rw [griessTrFull (show (symBlock A).2.2 = 0 from rfl),
    griessTrFull (show (symBlock (liftBlockSymMat ι A)).2.2 = 0 from rfl)]
  exact liftBlockNat_symBlock ι hι hsurj fullShortSign A

end Isometry

theorem griessTrExtraNat_symBlock (μ : leech.carrier) (A : symMat) :
    extraVnatAut μ (griessIso (1 ⊗ₜ[ℚ] symBlock A) : Vnat) =
      (griessIso (1 ⊗ₜ[ℚ] symBlock A) : Vnat) := by
  rw [griessTrFull (show (symBlock A).2.2 = 0 from rfl)]
  exact liftBlockExtraNat_symBlock μ fullShortSign A

/-- Extraspecial short coefficients remain `(-1)^(μ, α_c) x_c`. -/
theorem griessTrExtraNat_shortBlock (μ : leech.carrier) (x : SpaceX) :
    extraVnatAut μ (griessIso (1 ⊗ₜ[ℚ] shortBlock x) : Vnat) =
      (griessIso (1 ⊗ₜ[ℚ] shortBlock (liftBlockExtraX μ x)) : Vnat) := by
  rw [griessTrFull (show (shortBlock x).2.2 = 0 from rfl),
    griessTrFull (show (shortBlock (liftBlockExtraX μ x)).2.2 = 0 from rfl)]
  exact liftBlockExtraNat_shortBlock μ fullShortSign x

/-- Triality in full coordinates: apply the old even formula between two diagonal changes. -/
theorem griessTrSigmaBlockOFull_nat (A : symMat) (x : SpaceX)
    (hx : ∀ c, sigmaBlockParity c ≠ 0 → x c = 0) :
    sigmaAut (griessIso (1 ⊗ₜ[ℚ] (A, x, 0)) : Vnat) =
      (griessIso (1 ⊗ₜ[ℚ]
        ((sigmaBlockOFull (A, griessTrX x, 0)).1,
          griessTrX (sigmaBlockOFull (A, griessTrX x, 0)).2.1, 0)) : Vnat) := by
  have hx' : ∀ c, sigmaBlockParity c ≠ 0 → griessTrX x c = 0 := by
    intro c hc
    rw [griessTrX, hx c hc, mul_zero]
  rw [griessTrIso, sigmaBlockOFull_nat A (griessTrX x) hx', griessTrOld]

end VOA.Moonshine.ConwayNorton.M8
