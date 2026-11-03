/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeTransportGenusZero
import VOA.Huang.VerlindeRhoComplete
import VOA.Classification.COne.MainVerlindeEigen

/-!
# Huang's Thm 5.2 from the genus-one transport input alone

With the genus-zero half proved (`genusZeroTransferInput_pbw`) and `ρ(−1) = C` proved
(`VerlindeRho.rhoNegOneInput_pbw`), the only remaining input of Huang's Theorem 5.2 is the
genus-one statement `VacuumChannelTransportInput` (G1):

* `fusionEigenInput_of_genusOne : VacuumChannelTransportInput → FusionEigenInput`;
* `huangTransportInput_of_genusOne`, `huangVerlindeFusionInput_of_genusOne`;
* `VOA.Classification.COne.gannonRayhaun_genusOne` — the forward Gannon–Rayhaun headline
  with `FusionEigenInput` replaced by (G1).

**Exact strength of (G1)** (machine-checked, both directions, given the proved genus zero and
`ρ(−1) = C`): `VacuumChannelTransportInput ↔ FusionEigenInput ∧ ZigzagNonzeroInput`
(`vacuumChannelTransportInput_iff`). `ZigzagNonzeroInput` (the zig-zag
`λ⁻¹ ≫ (η ▷ M_b) ≫ α ≫ (M_b ◁ ε) ≫ ρ` of the vacuum pairings is nonzero) is the categorical form of
Huang's Prop. 5.1 and holds in any rigid monoidal category (it is the zig-zag identity, up to the
normalisation of `ε`, `η`); rigidity of the module category of such `W` is Huang's later theorem
(Huang, *Rigidity and modularity of vertex tensor categories*, CCM 10 (2008)). Hence (G1) is TRUE,
and it is not vacuous (`transferChoiceExists_pbw` supplies its data for every label).

## Status
No `sorry`, no new axioms; the headlines use the theorem `VOA.pbw`.
-/

noncomputable section

namespace VOA.Huang.VerlindeTransport

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeEigen VOA.Huang.VerlindeEigenMatrix VOA.Huang.VerlindeVacuum
  VOA.Huang.TensorCat CategoryTheory Matrix

universe u w

/-- **Huang Prop. 5.1, categorical form**: the zig-zag of nonzero vacuum pairings
`ε : M_a ⊠ M_b → V`, `η : V → M_b ⊠ M_a` is nonzero. TRUE for nice `W` (rigidity: Huang,
*Rigidity and modularity of vertex tensor categories*, 2008); implied by (G1)
(`zigzagNonzeroInput_of_genusOne`). -/
def ZigzagNonzeroInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
      ∀ (F : FusionChoice W) (H : OrdinaryFourPointInput F) (a b : ι)
        (c : TransferChoice F D a b), zigzag F H c ≠ 0

/-- **Huang Thm 5.2 from the genus-one input alone.** -/
theorem fusionEigenInput_of_genusOne (h1 : VacuumChannelTransportInput.{u, w}) :
    FusionEigenInput.{u, w} :=
  fusionEigenInput_of_split h1 genusZeroTransferInput_pbw VerlindeRho.rhoNegOneInput_pbw

/-- **`huangTransportInput_of_split`, with the proved inputs plugged in.** -/
theorem huangTransportInput_of_split_pbw (h1 : VacuumChannelTransportInput.{u, w})
    (h0 : GenusZeroTransferInput.{u, w}) : HuangTransportInput.{u, w} :=
  huangTransportInput_of_split h1 h0 VerlindeRho.rhoNegOneInput_pbw

/-- Huang Cor. 4.7 (Prop. 4.5 convention) from the genus-one input alone. -/
theorem huangTransportInput_of_genusOne (h1 : VacuumChannelTransportInput.{u, w}) :
    HuangTransportInput.{u, w} :=
  huangTransportInput_of_split_pbw h1 genusZeroTransferInput_pbw

/-- The Verlinde package from the genus-one input alone. -/
theorem huangVerlindeFusionInput_of_genusOne (h1 : VacuumChannelTransportInput.{u, w}) :
    HuangVerlindeFusionInput.{u, w} :=
  huangVerlindeFusionInput_of_eigen_rho (fusionEigenInput_of_genusOne h1)
    VerlindeRho.rhoNegOneInput_pbw

/-- (G1) implies the categorical Prop. 5.1: if the zig-zag vanished, the B-cycle matrix would
vanish and a row of the invertible `S` would be zero. -/
theorem zigzagNonzeroInput_of_genusOne (h1 : VacuumChannelTransportInput.{u, w}) :
    ZigzagNonzeroInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c hz
  obtain ⟨σ, T, -, -, hST, -, -, -⟩ :=
    rho_setup VerlindeRho.rhoNegOneInput_pbw hNice D hZ hirr hcomp v0 hv0
  choose β hβ using fun x j => endo_scalar D (c.lab x j) (bTransfer F H c x j)
  obtain ⟨Ω, hΩ, hrow⟩ := h1 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c β hβ
  have hs : zigzag F H c = (0 : ℂ) • 𝟙 (famObj D b) := by rw [hz, zero_smul]
  have hzero : ∀ z, D.repS v0 z = 0 := by
    intro z
    have h := hrow v0 z
    simp only [transferMatrix_eq_zigzag_scalar hNice D hirr F H c β hβ 0 hs, zero_mul,
      mul_zero, Finset.sum_const_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hΩ
  have h1' := congrFun (congrFun hST v0) v0
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1'
  simp only [Matrix.of_apply, hzero, zero_mul, Finset.sum_const_zero] at h1'
  exact zero_ne_one h1'

/-- **The converse**: Thm 5.2 and the categorical Prop. 5.1 give (G1). So (G1) is TRUE (Huang 2008,
Thm 5.2; Huang's rigidity theorem) and of exactly the strength of `FusionEigenInput ∧
ZigzagNonzeroInput`. -/
theorem vacuumChannelTransportInput_of_eigen_zigzag (hE : FusionEigenInput.{u, w})
    (hzz : ZigzagNonzeroInput.{u, w}) : VacuumChannelTransportInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c β hβ
  obtain ⟨σ, T, hσσ, hTS, hST, hTσ, hdual, hSσ⟩ :=
    rho_setup VerlindeRho.rhoNegOneInput_pbw hNice D hZ hirr hcomp v0 hv0
  obtain ⟨s, hs⟩ := endo_scalar D b (zigzag F H c)
  have hs0 : s ≠ 0 := by
    intro h0
    apply hzz 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c
    rw [hs, h0, zero_smul]
  have hEig := hE 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  obtain ⟨hne, hsymm, -⟩ := huangVerlindeFusionInput_of_eigen_rho hE
    VerlindeRho.rhoNegOneInput_pbw 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hunit := famFusion_vac_right D hirr v0 hv0
  -- `σ v0 = v0`
  have hσv0 : σ v0 = v0 := by
    have h := hdual v0 v0
    rw [famFusion_vac D hirr v0 hv0 v0 v0, if_pos rfl] at h
    split_ifs at h with hh
    · exact hh.symm
  have hlam : eigval hEig b v0 ≠ 0 := by
    intro h0
    have h := eq_eigval_mul hunit hEig b v0
    rw [h0, zero_mul, ← hsymm b] at h
    exact hne b h
  refine ⟨fun x => s * eigval hEig b (σ x), ?_, fun x z => ?_⟩
  · change s * eigval hEig b (σ v0) ≠ 0
    rw [hσv0]
    exact mul_ne_zero hs0 hlam
  -- matrices
  set Nm : Matrix ι ι ℂ := Matrix.of fun x y => (famFusion D b x y : ℂ) with hNm
  set Sm : Matrix ι ι ℂ := Matrix.of D.repS with hSm
  set Pm : Matrix ι ι ℂ := Matrix.of fun x z => if x = σ z then 1 else 0 with hPm
  set Λ : Matrix ι ι ℂ := Matrix.diagonal (fun z => eigval hEig b z) with hΛ
  set Λ' : Matrix ι ι ℂ := Matrix.diagonal (fun z => eigval hEig b (σ z)) with hΛ'
  have hTval : ∀ y w, T y w = D.repS y (σ w) := fun y w => by rw [← hTσ y (σ w), hσσ]
  have hNS : Nm * Sm = Sm * Λ := by
    ext x' z'
    rw [Matrix.mul_apply, hΛ, Matrix.mul_diagonal]
    simp only [hNm, hSm, Matrix.of_apply]
    rw [eigval_spec hEig b z' x', mul_comm]
  have hSS : Sm * Sm = Pm := by
    ext x' z'
    have h := congrFun (congrFun hST x') (σ z')
    rw [Matrix.mul_apply] at h ⊢
    simp only [hSm, hPm, Matrix.of_apply] at h ⊢
    simp only [hTval, hσσ] at h
    rw [h, Matrix.one_apply]
  have hPT : Pm * T = Sm := by
    ext x' z'
    rw [Matrix.mul_apply]
    simp only [hPm, hSm, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (σ x')]
    · rw [if_pos (hσσ x').symm, hTval, hSσ]
    · intro w _ hw
      rw [if_neg (fun h => hw (by rw [h, hσσ]))]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPΛ : Pm * Λ = Λ' * Pm := by
    ext x' z'
    rw [hΛ, hΛ', Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hPm, Matrix.of_apply]
    split_ifs with hh
    · rw [hh, hσσ, one_mul, mul_one]
    · simp
  have key : Sm * Nm = Λ' * Sm := by
    calc Sm * Nm = Sm * Nm * (Sm * T) := by rw [hST, Matrix.mul_one]
      _ = Sm * (Nm * Sm) * T := by simp only [Matrix.mul_assoc]
      _ = Sm * (Sm * Λ) * T := by rw [hNS]
      _ = (Sm * Sm) * Λ * T := by simp only [Matrix.mul_assoc]
      _ = Λ' * (Pm * T) := by rw [hSS, hPΛ, Matrix.mul_assoc]
      _ = Λ' * Sm := by rw [hPT]
  have hkey := congrFun (congrFun key x) z
  rw [Matrix.mul_apply, hΛ', Matrix.diagonal_mul] at hkey
  simp only [hNm, hSm, Matrix.of_apply] at hkey
  simp only [transferMatrix_eq_zigzag_scalar hNice D hirr F H c β hβ s hs]
  calc ∑ y, D.repS x y * (s * (famFusion D b y z : ℂ))
      = s * ∑ y, D.repS x y * (famFusion D b y z : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => by ring)
    _ = s * eigval hEig b (σ x) * D.repS x z := by rw [hkey, mul_assoc]

/-- **Exact strength of (G1)**, machine-checked. -/
theorem vacuumChannelTransportInput_iff :
    VacuumChannelTransportInput.{u, w} ↔
      FusionEigenInput.{u, w} ∧ ZigzagNonzeroInput.{u, w} :=
  ⟨fun h1 => ⟨fusionEigenInput_of_genusOne h1, zigzagNonzeroInput_of_genusOne h1⟩,
    fun h => vacuumChannelTransportInput_of_eigen_zigzag h.1 h.2⟩

end VOA.Huang.VerlindeTransport

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian
  VOA.Huang.VerlindeEigen VOA.Huang.VerlindeTransport

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), with Huang's Verlinde input reduced to the
genus-one transport statement.** As `gannonRayhaun_eigen`, with `FusionEigenInput` replaced by
`VacuumChannelTransportInput` (genus zero and `ρ(−1) = C` are proved). -/
theorem gannonRayhaun_genusOne
    (h1 : VacuumChannelTransportInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_eigen (fusionEigenInput_of_genusOne h1) hC hG hQ hHK

end VOA.Classification.COne
