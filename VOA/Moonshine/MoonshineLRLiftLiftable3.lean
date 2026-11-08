import VOA.Moonshine.MoonshineLRLiftLiftable2

/-!
# Monomial lattice generators and finite spin tests

The Golay coordinate sign changes are constructed as integral Leech isometries.
Code-preserving coordinate permutations are constructed in the same model.
The spin intertwining test is reduced to the 24 canonical lattice basis vectors.
For signed permutation matrices orthogonality is automatic, and the matrix test
is reduced to one permutation identity and one rational sign identity per row.

This file does not supply the spin permutations or their signs for nontrivial
Golay or Mathieu generators. The conclusions named `liftable_of_basis` retain
that explicit hypothesis; neither family is asserted liftable unconditionally.
The generator `ξ` is not treated.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch
open scoped Matrix

/-- Negate exactly the coordinates selected by a binary word. -/
def liftGenSign (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => if c i = 0 then u i else -u i

theorem liftGenSign_formula (c : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) (i : Fin 24) :
    liftGenSign c u i = u i - 2 * bitLift (c i) * u i := by
  rcases zmod_two_cases (c i) with h | h
  · simp [liftGenSign, h, bitLift]
  · simp only [liftGenSign, h, one_ne_zero, if_false, bitLift_one]
    ring

theorem liftGenSign_add (c : Fin 24 → ZMod 2) (u v : Fin 24 → ℤ) :
    liftGenSign c (u + v) = liftGenSign c u + liftGenSign c v := by
  funext i
  simp only [liftGenSign, Pi.add_apply]
  split_ifs <;> ring

theorem liftGenSign_involutive (c : Fin 24 → ZMod 2) :
    Function.Involutive (liftGenSign c) := by
  intro u
  funext i
  simp only [liftGenSign]
  split_ifs <;> simp

/-- The sum over a Golay support is divisible by four on every Leech vector. -/
theorem liftGenSign_support_sum (c : MonsterGriess.Code.C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    4 ∣ ∑ i, bitLift (c.val i) * u i := by
  obtain ⟨m, _, d, hd, hud, _⟩ := hu
  let k : Fin 24 → ℤ := fun i => (u i - m - 2 * bitLift (d i)) / 4
  have huk (i : Fin 24) : u i = m + 2 * bitLift (d i) + 4 * k i := by
    have h := hud i
    dsimp [k]
    unfold Int.ModEq at h
    omega
  obtain ⟨a, ha⟩ := MonsterGriess.Code.four_dvd_wt c.property
  obtain ⟨b, hb⟩ := MonsterGriess.Code.two_dvd_hammingNorm_mul c.property hd
  have hc : (∑ i, bitLift (c.val i)) = 4 * (a : ℤ) := by
    rw [MonsterGriess.Code.sum_bitLift, ha]
    norm_cast
  have hcd : (∑ i, bitLift (c.val i) * bitLift (d i)) = 2 * (b : ℤ) := by
    simp only [← SpinLattice.bitLift_mul]
    change (∑ i, bitLift ((c.val * d) i)) = _
    rw [MonsterGriess.Code.sum_bitLift, hb]
    norm_cast
  have he : (∑ i, bitLift (c.val i) * u i) =
      m * (∑ i, bitLift (c.val i)) +
        2 * (∑ i, bitLift (c.val i) * bitLift (d i)) +
        4 * (∑ i, bitLift (c.val i) * k i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [huk]
    ring
  rw [he, hc, hcd]
  exact ⟨m * a + b + ∑ i, bitLift (c.val i) * k i, by ring⟩

/-- Every Golay sign change preserves the integral Conway model of the Leech lattice. -/
theorem liftGenSign_mem (c : MonsterGriess.Code.C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    liftGenSign c u ∈ codeLattice MonsterGriess.Code.C := by
  obtain ⟨k, hk⟩ := liftGenSign_support_sum c hu
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  have hsum : (∑ i, liftGenSign c.val u i) = ∑ i, u i - 8 * k := by
    simp only [liftGenSign_formula, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum, hk]
    ring
  rcases hm with rfl | rfl
  · refine ⟨0, Or.inl rfl, d, hd, fun i => ?_, ?_⟩
    · have h := hud i
      have hb := bitLift_zero_or_one (d i)
      unfold Int.ModEq at h ⊢
      dsimp only [liftGenSign]
      split_ifs <;> omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega
  · refine ⟨1, Or.inr rfl, d + c.val,
      MonsterGriess.Code.C.add_mem hd c.property, fun i => ?_, ?_⟩
    · have h := hud i
      have hb := bitLift_zero_or_one (d i)
      rcases zmod_two_cases (c.val i) with hc | hc
      · simpa [liftGenSign, hc] using h
      · simp only [liftGenSign, hc, one_ne_zero, if_false, Pi.add_apply, bitLift_add_one]
        unfold Int.ModEq at h ⊢
        omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega

/-- The sign change as an additive automorphism of the code lattice. -/
def liftGenSignEquiv (c : MonsterGriess.Code.C) :
    codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C ≃+
      codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C where
  toFun u := ⟨liftGenSign c.val u.val, liftGenSign_mem c u.property⟩
  invFun u := ⟨liftGenSign c.val u.val, liftGenSign_mem c u.property⟩
  left_inv u := Subtype.ext (liftGenSign_involutive c.val u.val)
  right_inv u := Subtype.ext (liftGenSign_involutive c.val u.val)
  map_add' u v := Subtype.ext (liftGenSign_add c.val u.val v.val)

/-- The integral Leech isometry associated with any Golay codeword. -/
def liftGenGolay (c : MonsterGriess.Code.C) : leech.carrier →ₗ[ℤ] leech.carrier :=
  ((leechEquiv.trans (liftGenSignEquiv c)).trans leechEquiv.symm).toAddMonoidHom.toIntLinearMap

theorem liftGenGolay_coordinates (c : MonsterGriess.Code.C) (α : leech.carrier) :
    (leechEquiv (liftGenGolay c α) : Fin 24 → ℤ) =
      liftGenSign c.val (leechEquiv α) := by
  exact congrArg Subtype.val (leechEquiv.apply_symm_apply _)

theorem liftGenGolay_surjective (c : MonsterGriess.Code.C) :
    Function.Surjective (liftGenGolay c) :=
  ((leechEquiv.trans (liftGenSignEquiv c)).trans leechEquiv.symm).surjective

theorem liftGenGolay_isometry (c : MonsterGriess.Code.C) (α β : leech.carrier) :
    leech.form (liftGenGolay c α) (liftGenGolay c β) = leech.form α β := by
  have h : (leechEquiv (liftGenGolay c α) : Fin 24 → ℤ) ⬝ᵥ
      (leechEquiv (liftGenGolay c β) : Fin 24 → ℤ) =
      (leechEquiv α : Fin 24 → ℤ) ⬝ᵥ (leechEquiv β : Fin 24 → ℤ) := by
    rw [liftGenGolay_coordinates, liftGenGolay_coordinates]
    apply Finset.sum_congr rfl
    intro i _
    simp only [liftGenSign]
    split_ifs <;> ring
  rw [leechEquiv_dotProduct, leechEquiv_dotProduct] at h
  omega

/-- A coordinate permutation preserving the binary Golay code preserves the Leech lattice. -/
theorem liftGenPerm_mem (σ : Equiv.Perm (Fin 24))
    (hσ : ∀ d ∈ MonsterGriess.Code.C, permLin (ZMod 2) σ d ∈ MonsterGriess.Code.C)
    {u : Fin 24 → ℤ} (hu : u ∈ codeLattice MonsterGriess.Code.C) :
    permLin ℤ σ u ∈ codeLattice MonsterGriess.Code.C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  exact ⟨m, hm, permLin (ZMod 2) σ d, hσ d hd, fun i => hud (σ.symm i),
    by rwa [sum_permLin]⟩

/-- The code-preservation condition defining the coordinate permutation group. -/
def liftGenPreservesCode (σ : Equiv.Perm (Fin 24)) : Prop :=
  ∀ d, permLin (ZMod 2) σ d ∈ MonsterGriess.Code.C ↔ d ∈ MonsterGriess.Code.C

theorem liftGenPreservesCode_symm (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) : liftGenPreservesCode σ.symm := by
  intro d
  have h := hσ (permLin (ZMod 2) σ.symm d)
  have he : permLin (ZMod 2) σ (permLin (ZMod 2) σ.symm d) = d := by
    ext i
    simp [permLin_apply]
  rw [he] at h
  exact h.symm

/-- Mathieu coordinate permutations on the code lattice, with no chosen generating set. -/
def liftGenPermEquiv (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) :
    codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C ≃+
      codeLatticeSubgroup MonsterGriess.Code.allOnes_mem_C where
  toFun u := ⟨permLin ℤ σ u.val, liftGenPerm_mem σ (fun d hd => (hσ d).2 hd) u.property⟩
  invFun u := ⟨permLin ℤ σ.symm u.val,
    liftGenPerm_mem σ.symm (fun d hd => (liftGenPreservesCode_symm σ hσ d).2 hd)
      u.property⟩
  left_inv u := by
    apply Subtype.ext
    ext i
    simp [permLin_apply]
  right_inv u := by
    apply Subtype.ext
    ext i
    simp [permLin_apply]
  map_add' u v := Subtype.ext ((permLin ℤ σ).map_add u.val v.val)

/-- The integral Leech isometry attached to a code-preserving coordinate permutation. -/
def liftGenMathieu (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) :
    leech.carrier →ₗ[ℤ] leech.carrier :=
  ((leechEquiv.trans (liftGenPermEquiv σ hσ)).trans
    leechEquiv.symm).toAddMonoidHom.toIntLinearMap

theorem liftGenMathieu_coordinates (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) (α : leech.carrier) :
    (leechEquiv (liftGenMathieu σ hσ α) : Fin 24 → ℤ) = permLin ℤ σ (leechEquiv α) :=
  congrArg Subtype.val (leechEquiv.apply_symm_apply _)

theorem liftGenMathieu_surjective (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) : Function.Surjective (liftGenMathieu σ hσ) :=
  ((leechEquiv.trans (liftGenPermEquiv σ hσ)).trans leechEquiv.symm).surjective

theorem liftGenMathieu_isometry (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) (α β : leech.carrier) :
    leech.form (liftGenMathieu σ hσ α) (liftGenMathieu σ hσ β) = leech.form α β := by
  have h : (leechEquiv (liftGenMathieu σ hσ α) : Fin 24 → ℤ) ⬝ᵥ
      (leechEquiv (liftGenMathieu σ hσ β) : Fin 24 → ℤ) =
      (leechEquiv α : Fin 24 → ℤ) ⬝ᵥ (leechEquiv β : Fin 24 → ℤ) := by
    rw [liftGenMathieu_coordinates, liftGenMathieu_coordinates, dotProduct_permLin]
  rw [leechEquiv_dotProduct, leechEquiv_dotProduct] at h
  omega

/-- Matrix form of the phased intertwining equation at one lattice vector. -/
def liftGenIntertwines (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (R : Matrix SpinIdx SpinIdx ℂ) (α : leech.carrier) : Prop :=
  R * spinOp (coordOfRed (red leech α)) =
    latCob leech leech ι α • (spinOp (coordOfRed (red leech (ι α))) * R)

section BasisTest

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
  (R : Matrix SpinIdx SpinIdx ℂ)

theorem liftGenIntertwines_zero : liftGenIntertwines ι R 0 := by
  simp [liftGenIntertwines, latCob_zero, coordOfRed_zero, spinOp_zero]

theorem liftGenRed_neg (α : leech.carrier) : red leech (-α) = red leech α := by
  rw [map_neg]
  ext i
  exact CharTwo.neg_eq _

theorem liftGenIntertwines_neg {α : leech.carrier} (hα : liftGenIntertwines ι R α) :
    liftGenIntertwines ι R (-α) := by
  unfold liftGenIntertwines
  rw [liftGenRed_neg, map_neg, liftGenRed_neg, latCob_neg]
  exact hα

include hι in
/-- Intertwining propagates under addition by the cocycle comparison identity. -/
theorem liftGenIntertwines_add {α β : leech.carrier}
    (hα : liftGenIntertwines ι R α) (hβ : liftGenIntertwines ι R β) :
    liftGenIntertwines ι R (α + β) := by
  unfold liftGenIntertwines at hα hβ ⊢
  apply smul_right_injective (Matrix SpinIdx SpinIdx ℂ) (latticeCocycle_ne_zero leech α β)
  dsimp only
  calc
    latticeCocycle leech α β • (R * spinOp (coordOfRed (red leech (α + β)))) =
        R * (spinOp (coordOfRed (red leech α)) *
          spinOp (coordOfRed (red leech β))) := by
            rw [spinOp_red_mul, Matrix.mul_smul]
    _ = (latCob leech leech ι α * latCob leech leech ι β) •
        ((spinOp (coordOfRed (red leech (ι α))) *
          spinOp (coordOfRed (red leech (ι β)))) * R) := by
            rw [← Matrix.mul_assoc, hα, Matrix.smul_mul, Matrix.mul_assoc, hβ,
              Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    _ = _ := by
      rw [spinOp_red_mul, Matrix.smul_mul, smul_smul, smul_smul,
        mul_comm _ (latticeCocycle leech (ι α) (ι β)),
        latticeCocycle_map_mul_latCob leech leech leech_even leech_even ι hι,
        map_add ι]

include hι in
/-- Only the 24 canonical lattice basis vectors need to be checked. -/
theorem liftGenIntertwines_of_basis
    (hB : ∀ j, liftGenIntertwines ι R (latticeBasis leech j)) (α : leech.carrier) :
    liftGenIntertwines ι R α := by
  let S : AddSubgroup leech.carrier :=
    { carrier := {α | liftGenIntertwines ι R α}
      zero_mem' := liftGenIntertwines_zero ι R
      add_mem' := liftGenIntertwines_add ι hι R
      neg_mem' := liftGenIntertwines_neg ι R }
  have hs : Submodule.span ℤ (Set.range (latticeBasis leech)) ≤ S.toIntSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hB j
  rw [(latticeBasis leech).span_eq] at hs
  exact hs (Submodule.mem_top : α ∈ (⊤ : Submodule ℤ leech.carrier))

end BasisTest

/-- The canonical basis test has exactly 24 lattice inputs. -/
theorem liftGenBasis_card : Fintype.card (Fin leech.bRank) = 24 := by
  rw [Fintype.card_fin, bRank_eq_rank, leech_rank]

/-- A rational orthogonal matrix needs the unphased equation only on a lattice basis. -/
theorem liftGenOfBasisIntertwiner (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (hsurj : Function.Surjective ι) (R : Matrix SpinIdx SpinIdx ℚ)
    (horth : Rᵀ * R = 1)
    (hB : ∀ j, R * liftMonoQmat (latticeBasis leech j) =
      liftMonoWeight ι (latticeBasis leech j) •
        (liftMonoQmat (ι (latticeBasis leech j)) * R)) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  apply liftLiftableOfRationalIntertwiner ι hι hsurj R horth
  have hb (j) : liftGenIntertwines ι (R.map (Rat.castHom ℂ)) (latticeBasis leech j) := by
    let α := latticeBasis leech j
    have hmap (r : ℚ) (M : Matrix SpinIdx SpinIdx ℚ) :
        (r • M).map (Rat.castHom ℂ) = (r : ℂ) • M.map (Rat.castHom ℂ) := by
      ext i k
      simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
        Rat.cast_mul]
    have hC := congrArg (fun M => M.map (Rat.castHom ℂ)) (hB j)
    dsimp only at hC
    rw [Matrix.map_mul (f := Rat.castHom ℂ), hmap,
      Matrix.map_mul (f := Rat.castHom ℂ), liftMonoQmat_map, liftMonoQmat_map] at hC
    unfold liftGenIntertwines
    rw [spinOp, spinOp, Matrix.mul_smul, hC, smul_smul,
      mul_comm (signRefinement _), liftMonoWeight_phase ι hι,
      Matrix.smul_mul, smul_smul]
  intro α s
  have h := liftGenIntertwines_of_basis ι hι (R.map (Rat.castHom ℂ)) hb α
  simpa only [liftGenIntertwines, Matrix.mulVec_mulVec, Matrix.smul_mulVec] using
    congrArg (fun M => M *ᵥ s) h

/-- A signed permutation matrix on the rational spin module. -/
def liftGenSignedMatrix (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2) :
    Matrix SpinIdx SpinIdx ℚ := spm ℚ σ ε

theorem liftGenSignedMatrix_transpose (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2) :
    (liftGenSignedMatrix σ ε)ᵀ = liftGenSignedMatrix σ.symm (ε ∘ σ.symm) := by
  ext i j
  simp only [liftGenSignedMatrix, Matrix.transpose_apply, spm_apply,
    Function.comp_apply]
  by_cases h : i = σ j
  · have hj : j = σ.symm i := by rw [h, σ.symm_apply_apply]
    rw [if_pos h, if_pos hj, ← hj]
  · have hj : j ≠ σ.symm i := by
      intro hj
      apply h
      rw [hj, σ.apply_symm_apply]
    rw [if_neg h, if_neg hj]

/-- Orthogonality is automatic for every rational signed permutation matrix. -/
theorem liftGenSignedMatrix_orthogonal (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2) :
    (liftGenSignedMatrix σ ε)ᵀ * liftGenSignedMatrix σ ε = 1 := by
  rw [liftGenSignedMatrix_transpose, liftGenSignedMatrix, liftGenSignedMatrix, spm_mul_spm]
  apply spm_eq_one
  · intro i
    exact σ.apply_symm_apply i
  · intro i
    exact zmod2_add_self (ε (σ.symm i))

/-- Intertwining signed permutations is exactly a permutation identity and a sign identity. -/
theorem liftGenSignedMatrix_intertwine (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2) (α : leech.carrier)
    (hperm : ∀ i,
      qPerm (coordOfRed (red leech α)).1 (coordOfRed (red leech α)).2 (σ i) =
        σ (qPerm (coordOfRed (red leech (ι α))).1 (coordOfRed (red leech (ι α))).2 i))
    (hsign : ∀ i,
      sgnR ℚ (ε i + qSign 0 (coordOfRed (red leech α)).1
        (coordOfRed (red leech α)).2 (σ i)) =
      liftMonoWeight ι α * sgnR ℚ
        (qSign 0 (coordOfRed (red leech (ι α))).1 (coordOfRed (red leech (ι α))).2 i +
          ε (qPerm (coordOfRed (red leech (ι α))).1
            (coordOfRed (red leech (ι α))).2 i))) :
    liftGenSignedMatrix σ ε * liftMonoQmat α =
      liftMonoWeight ι α • (liftMonoQmat (ι α) * liftGenSignedMatrix σ ε) := by
  unfold liftGenSignedMatrix liftMonoQmat qmatR
  rw [spm_mul_spm, spm_mul_spm]
  ext i j
  simp only [spm_apply, Matrix.smul_apply, Function.comp_apply, smul_eq_mul,
    hperm, hsign, mul_ite, mul_zero]

/-- A finite certificate for a signed spin permutation gives a liftable VOA automorphism. -/
theorem liftGenOfSignedBasis (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (hsurj : Function.Surjective ι) (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2)
    (hperm : ∀ j i,
      let p := coordOfRed (red leech (latticeBasis leech j))
      let q := coordOfRed (red leech (ι (latticeBasis leech j)))
      qPerm p.1 p.2 (σ i) = σ (qPerm q.1 q.2 i))
    (hsign : ∀ j i,
      let α := latticeBasis leech j
      let p := coordOfRed (red leech α)
      let q := coordOfRed (red leech (ι α))
      sgnR ℚ (ε i + qSign 0 p.1 p.2 (σ i)) =
        liftMonoWeight ι α * sgnR ℚ (qSign 0 q.1 q.2 i + ε (qPerm q.1 q.2 i))) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  apply liftGenOfBasisIntertwiner ι hι hsurj (liftGenSignedMatrix σ ε)
    (liftGenSignedMatrix_orthogonal σ ε)
  intro j
  exact liftGenSignedMatrix_intertwine ι σ ε (latticeBasis leech j) (hperm j) (hsign j)

/-- The remaining Golay spin certificate: only basis vectors, not all lattice vectors. -/
theorem liftGenGolay_liftable_of_basis (c : MonsterGriess.Code.C)
    (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (hB : ∀ j, R * liftMonoQmat (latticeBasis leech j) =
      liftMonoWeight (liftGenGolay c) (latticeBasis leech j) •
        (liftMonoQmat (liftGenGolay c (latticeBasis leech j)) * R)) :
    ∃ g : liftableSubgroup, monsterLift g =
      liftTwVnatAut (liftGenGolay c) (liftGenGolay_isometry c) (liftGenGolay_surjective c) :=
  liftGenOfBasisIntertwiner _ (liftGenGolay_isometry c) (liftGenGolay_surjective c) R horth hB

/-- The remaining Mathieu spin certificate, for any code-preserving coordinate permutation. -/
theorem liftGenMathieu_liftable_of_basis (σ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) (R : Matrix SpinIdx SpinIdx ℚ) (horth : Rᵀ * R = 1)
    (hB : ∀ j, R * liftMonoQmat (latticeBasis leech j) =
      liftMonoWeight (liftGenMathieu σ hσ) (latticeBasis leech j) •
        (liftMonoQmat (liftGenMathieu σ hσ (latticeBasis leech j)) * R)) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut (liftGenMathieu σ hσ)
      (liftGenMathieu_isometry σ hσ) (liftGenMathieu_surjective σ hσ) :=
  liftGenOfBasisIntertwiner _ (liftGenMathieu_isometry σ hσ) (liftGenMathieu_surjective σ hσ)
    R horth hB

end VOA.Moonshine.ConwayNorton.M8
