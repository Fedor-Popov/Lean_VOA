/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessSpinModule

/-!
# The frame involution of `T` is diagonal on Axiom's halves `C₀ × {0}`, `C₀ × {1}`

`V♮` is built with the frame involution `J = c⁻¹ e_w` on `T` (`frameJ`, `w = frameW = 8e₀`); its
eigenspaces `T₀`, `T₁` give the frame sectors `T_s⁺` used by the triality `σ`.  Axiom's spin index is
`SpinIdx = ZMod 2 × C₀`, and the two halves `C₀ × {0}`, `C₀ × {1}` of `SpinIdx` are the halves of
`SpaceW` permuted by Axiom's triality `tauB`.  This file proves that the isomorphism
`spinIso : ℂ^SpinIdx ≅ T` of `MoonshineCNGriessSpinModule` carries one to the other:

* the class of `w = 8e₀` in `Λ/2Λ` has Axiom coordinates `(Ω, thetaD Ω)` (`coordOfRed_red_frameW`):
  `phi0 (Ω, thetaD Ω) = lamX Ω = [(2²⁴)]`, and `(2²⁴) − 8e₀ = 2·(−3, 1²³)`;
* `θ(Ω, ·) = 0` on the Golay code (`θ_ΩC_eq_zero`, checked on the 12 basis words by a kernel
  computation on bit masks), so the spin matrix of `(Ω, thetaD Ω)` is the diagonal sign matrix
  `D = diag((−1)^{i.1})` (`qmatR_ΩC_thetaD`);
* hence ⭐ `spinIso_frameJ`: `J ∘ Ψ = κ · Ψ ∘ D` with `κ = frameSign`, `κ² = 1`
  (`frameSign_mul_self`), and ⭐ `spinIso_frameJ_of_support`: `Ψ` maps the half `C₀ × {t}` into the
  `J`-eigenspace of eigenvalue `κ·(−1)^t`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.AutMonster VOA.Moonshine.FrameT
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.Code
open VOA.Moonshine.MonsterGriess.LeechMatch (leechEquiv leechEquiv_apply)
open Matrix

/-! ## §1  `θ(Ω, ·) = 0`, by a computation on bit masks -/

/-- `β` on the basis words, as a computation on bit masks. -/
def βPopc (i j : Fin 12) : ZMod 2 :=
  if i < j then 0 else if i = j then ((popc 24 (Bmask i) / 4 : ℕ) : ZMod 2)
  else ((popc 24 (Bmask i &&& Bmask j) / 2 : ℕ) : ZMod 2)

/-- `A` on three basis words, as a computation on bit masks. -/
def abPopc (i j k : Fin 12) : ZMod 2 := ((popc 24 (Bmask i &&& Bmask j &&& Bmask k) : ℕ) : ZMod 2)

/-- The cocycle `θc` with bit-mask structure constants. -/
def θcPopc (μ ν : Fin 12 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, μ i * ν j * βPopc i j + ∑ i, ∑ j, ∑ k, lt01 i j * μ i * μ j * ν k * abPopc i j k

theorem β_eq_βPopc (i j : Fin 12) : β i j = βPopc i j := by
  simp only [β, βPopc, P, K_eq, B_eq_bvec, ← bvec_and, hammingNorm_bvec]

theorem Ab_eq_abPopc (i j k : Fin 12) : Code.Ab i j k = abPopc i j k := by
  simp only [Code.Ab, abPopc, Code.A]
  rw [supp_inter, supp_inter, card_supp, B_eq_bvec, B_eq_bvec, B_eq_bvec,
    ← bvec_and, ← bvec_and, hammingNorm_bvec]

theorem θc_eq_θcPopc (μ ν : Fin 12 → ZMod 2) : θc μ ν = θcPopc μ ν := by
  rw [θc_eq, θcPopc]
  simp only [β_eq_βPopc, Ab_eq_abPopc]

/-- The kernel check on the 12 basis words: `θc(ψ Ω, eᵢ) = 0`. -/
theorem θcPopc_ψΩ_single : ∀ i : Fin 12, θcPopc (ψ Ω) (Pi.single i 1) = 0 := by
  decide +kernel

/-- **`θ(Ω, f) = 0` for every Golay codeword `f`.** -/
theorem θ_ΩC_eq_zero (f : MonsterGriess.Code.C) : θ ΩC f = 0 := by
  refine eq_zero_of_additive (θ ΩC) (θ_add_right ΩC) (fun i => ?_) f
  have hr : (basisC.repr ΩC : Fin 12 → ZMod 2) = ψ Ω := funext fun j => repr_apply ΩC j
  rw [θ, basisC.repr_self, Finsupp.single_eq_pi_single, hr, θc_eq_θcPopc]
  exact θcPopc_ψΩ_single i

/-! ## §2  The Axiom coordinates of the frame vector `w = 8e₀` -/

theorem leechEquiv_frameW :
    (leechEquiv frameW : Fin 24 → ℤ) = (8 : ℤ) • (Pi.single 0 1 : Fin 24 → ℤ) := by
  funext j
  rw [leechEquiv_apply]
  revert j
  decide

/-- `(−3, 1²³)`, the half of `(2²⁴) − 8e₀`. -/
def oddFrameVec : Fin 24 → ℤ := fun i => if i = 0 then -3 else 1

theorem oddFrameVec_mem : oddFrameVec ∈ codeLattice MonsterGriess.Code.C := by
  refine ⟨1, .inr rfl, 0, Submodule.zero_mem _, fun i => ?_, ?_⟩
  · simp only [oddFrameVec, Pi.zero_apply, bitLift, ZMod.val_zero, Nat.cast_zero, mul_zero,
      add_zero]
    unfold Int.ModEq
    split_ifs <;> decide
  · unfold Int.ModEq
    decide

theorem lamCode_Ω : SpinLattice.lamCode Ω = fun _ => 2 := by
  have hP : P Ω = 0 := by decide
  funext k
  simp only [SpinLattice.lamCode, SpinLattice.Pint, hP, Ω]
  rfl

/-- `phi0 (Ω, thetaD Ω)` is the class of `w = 8e₀`. -/
theorem phi0_ΩC_thetaD :
    SpinLattice.phi0 (ΩC, thetaD ΩC) = Submodule.Quotient.mk (leechEquiv frameW) := by
  rw [SpinLattice.phi0_apply, SpinLattice.lamT, add_assoc, ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  change Submodule.Quotient.mk (⟨SpinLattice.lamCode Ω, _⟩ : codeLatticeSubgroup allOnes_mem_C)
    = Submodule.Quotient.mk (leechEquiv frameW)
  rw [Submodule.Quotient.eq, mem_two_range_iff]
  refine ⟨⟨oddFrameVec, oddFrameVec_mem⟩, ?_⟩
  change (2 : ℤ) • oddFrameVec = SpinLattice.lamCode Ω - (leechEquiv frameW : Fin 24 → ℤ)
  rw [lamCode_Ω, leechEquiv_frameW]
  funext i
  simp only [oddFrameVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

/-- **The frame vector has Axiom coordinates `(Ω, thetaD Ω)`.** -/
theorem coordOfRed_red_frameW : coordOfRed (red leech frameW) = (ΩC, thetaD ΩC) := by
  apply latRedEquiv.injective
  change latRedLin (coordOfRed (red leech frameW)) = latRedLin (ΩC, thetaD ΩC)
  rw [latRedLin_coordOfRed, latRedLin_apply, phi0_ΩC_thetaD, axiomRed_mk,
    AddEquiv.symm_apply_apply]

/-! ## §3  The spin matrix of the frame vector is diagonal -/

theorem π₀_ΩC_eq : π₀ ΩC = 0 := by
  apply Subtype.ext
  rw [coe_π₀, μ₀_ΩC, one_smul, add_self_C]
  rfl

theorem shift_ΩC_eq (c : C₀) : shift ΩC c = c := by
  rw [shift, map_add, π₀_coe, π₀_ΩC_eq, add_zero]

/-- The diagonal sign matrix `D = diag((−1)^{i.1})` on `SpinIdx = ZMod 2 × C₀`. -/
noncomputable def frameDiag : Matrix SpinIdx SpinIdx ℂ := Matrix.diagonal fun i => sgnR ℂ i.1

/-- **`R(0, Ω, thetaD Ω) = diag((−1)^{i.1})`.** -/
theorem qmatR_ΩC_thetaD : qmatR ℂ 0 ΩC (thetaD ΩC) = frameDiag := by
  ext i j
  rw [qmatR_apply, frameDiag, Matrix.diagonal_apply]
  have hperm : qPerm ΩC (thetaD ΩC) i = i := by
    simp only [qPerm, pair_thetaD, θ_ΩC_eq_zero, add_zero, shift_ΩC_eq]
  have hsign : qSign 0 ΩC (thetaD ΩC) i = i.1 := by
    simp only [qSign, μ₀_ΩC, mul_one, zero_add, shift_ΩC_eq, pair_thetaD, θ_ΩC_eq_zero, add_zero]
  rw [hperm, hsign]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem frameDiag_mulVec_frameDiag_mulVec (v : SpinIdx → ℂ) : frameDiag *ᵥ (frameDiag *ᵥ v) = v := by
  funext i
  rw [frameDiag, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal, ← mul_assoc, ← sgnR_add,
    zmod2_add_self, sgnR_zero, one_mul]

theorem frameDiag_mulVec_of_support {t : ZMod 2} {v : SpinIdx → ℂ}
    (hv : ∀ i : SpinIdx, i.1 ≠ t → v i = 0) : frameDiag *ᵥ v = sgnR ℂ t • v := by
  funext i
  rw [frameDiag, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases h : i.1 = t
  · rw [h]
  · rw [hv i h, mul_zero, mul_zero]

/-! ## §4  `J ∘ Ψ = κ Ψ ∘ D` -/

theorem spinIso_smul (c : ℂ) (v : SpinRep) : spinIso (c • v) = c • spinIso v :=
  spinIso.toLinearMap.map_smul_of_tower c v

/-- The sign `κ = c⁻¹ Z(Ω, thetaD Ω)` relating `J` and `D`. -/
noncomputable def frameSign : ℂ := (sqrtEps leech frameW)⁻¹ * signRefinement (ΩC, thetaD ΩC)

/-- ⭐ **The frame involution of `T` is `κ·D` in the spin model**: `J(Ψ v) = κ Ψ(D v)`. -/
theorem spinIso_frameJ (v : SpinRep) :
    frameJL (spinIso v) = frameSign • spinIso (frameDiag *ᵥ (v : SpinIdx → ℂ) : SpinIdx → ℂ) := by
  have h := spinIso_spinOp frameW v
  rw [coordOfRed_red_frameW, spinOp, qmatR_ΩC_thetaD, Matrix.smul_mulVec] at h
  have h2 := spinIso_smul (signRefinement (ΩC, thetaD ΩC)) (frameDiag *ᵥ (v : SpinIdx → ℂ) : SpinIdx → ℂ)
  change (sqrtEps leech frameW)⁻¹ • eT leech leech_even leech_isUnit_det_gramMat frameW (spinIso v) = _
  rw [← h]
  erw [h2]
  rw [smul_smul]
  rfl

/-- `κ² = 1`. -/
theorem frameSign_mul_self : frameSign * frameSign = 1 := by
  classical
  set v : SpinRep := (Pi.single ((0 : ZMod 2), (0 : C₀)) (1 : ℂ) : SpinIdx → ℂ)
  have hv : v ≠ 0 := by
    intro h
    have := congrFun (show (v : SpinIdx → ℂ) = 0 from h) ((0 : ZMod 2), (0 : C₀))
    simp [v] at this
    exact one_ne_zero this
  have h1 := frameJ_frameJ leech leech_even leech_isUnit_det_gramMat frameW (spinIso v)
  change frameJL (frameJL (spinIso v)) = spinIso v at h1
  rw [spinIso_frameJ, map_smul, spinIso_frameJ, smul_smul] at h1
  erw [frameDiag_mulVec_frameDiag_mulVec] at h1
  have h3 : (frameSign * frameSign - 1) • spinIso v = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.1 h3 with h4 | h4
  · exact sub_eq_zero.1 h4
  · exact absurd (spinIso.map_eq_zero_iff.1 h4) hv

/-- ⭐ **Block compatibility on `T`**: `Ψ` maps the half `C₀ × {t}` of `ℂ^SpinIdx` into the
eigenspace of the frame involution `J` with eigenvalue `κ·(−1)^t`. -/
theorem spinIso_frameJ_of_support {t : ZMod 2} {v : SpinRep}
    (hv : ∀ i : SpinIdx, i.1 ≠ t → (v : SpinIdx → ℂ) i = 0) :
    frameJL (spinIso v) = (frameSign * sgnR ℂ t) • spinIso v := by
  rw [spinIso_frameJ, frameDiag_mulVec_of_support hv]
  erw [spinIso_smul]
  rw [smul_smul]

end VOA.Moonshine.GriessDictionary
