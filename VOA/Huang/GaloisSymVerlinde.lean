import VOA.Huang.GaloisSymIntegral
import VOA.Huang.VerlindeFusion

/-!
# Conditional algebraic Galois symmetry of Zhu's actual S-matrix

The normalized-character permutation uses precisely `HuangVerlindeFusionInput`.
The signed-row law additionally retains full symmetry and integral bilinear
normalization: neither is a field of that input (which has only vacuum symmetry).
These statements apply to automorphisms of `ℂ` already supplied as data. They do
not assert membership in the cyclotomic field of the order of `ρ(T)`.
-/

noncomputable section

namespace VOA.Huang.GaloisSym

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The actual representation matrix is invertible, with no analytic hypothesis. -/
theorem repS_isUnit (D : VOA.ModularData W ι) : IsUnit (Matrix.of D.repS) := by
  rw [← D.rep_S]
  exact (Group.isUnit _).map D.rep

theorem verlindeSystem_of_huang (hH : HuangVerlindeFusionInput.{u, w})
    (hW : Nice W) (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) :
    VerlindeSystem (famFusion D) (Matrix.of D.repS) v0 := by
  obtain ⟨hn, _, hV⟩ := hH 𝒱 W hW ι D hZ hirr hcomp v0 hv0
  exact ⟨repS_isUnit D, hn, hV⟩

/-- The fusion-character Galois permutation, conditional only on Huang's input. -/
theorem galois_permutation_of_huang (hH : HuangVerlindeFusionInput.{u, w})
    (hW : Nice W) (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (σ : ℂ ≃+* ℂ) :
    ∃ π : Equiv.Perm ι, ∀ a x,
      σ (D.repS a x / D.repS v0 x) = D.repS a (π x) / D.repS v0 (π x) :=
  (verlindeSystem_of_huang hH hW D hZ hirr hcomp v0 hv0).galois_permutation σ

/-- Integrality of the actual fusion eigenvalues, with no cyclotomic input. -/
theorem isIntegral_ratio_of_huang (hH : HuangVerlindeFusionInput.{u, w})
    (hW : Nice W) (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a x : ι) :
    IsIntegral ℤ (D.repS a x / D.repS v0 x) :=
  (verlindeSystem_of_huang hH hW D hZ hirr hcomp v0 hv0).isIntegral_fusionCharacter a x

/-- Signed-row symmetry with the two additional normalization hypotheses visible. -/
theorem galois_signed_rows_of_huang (hH : HuangVerlindeFusionInput.{u, w})
    (hW : Nice W) (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)))
    (hnorm : IntegralColumnNormalization (Matrix.of D.repS))
    (hs : (Matrix.of D.repS).transpose = Matrix.of D.repS) (σ : ℂ ≃+* ℂ) :
    ∃ (π : Equiv.Perm ι) (ε : ι → ℂ), (∀ a, ε a = 1 ∨ ε a = -1) ∧
      ∀ a b, σ (D.repS a b) = ε a * D.repS (π a) b :=
  (verlindeSystem_of_huang hH hW D hZ hirr hcomp v0 hv0).galois_signed_rows hnorm hs σ

end VOA.Huang.GaloisSym
