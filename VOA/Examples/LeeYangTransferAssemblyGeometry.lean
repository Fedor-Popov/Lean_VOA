import VOA.Examples.GradedUnitaryCohomologyTransfer

/-!
# Kähler geometry before the weak graded-unitarity input

This is the existing Kähler datum with positivity left out. It lets the main
assembly consume affine graded unitarity through the separate weak-GU tensor
positivity node, instead of assuming a positive complex independently of it.
-/
namespace VOA.LeeYangTransferAssembly
open GradedUnitaryCohomology
universe u
structure KahlerGeometry (K : Type u) [AddCommGroup K] [Module ℂ K] where
  /-- The modified Hermitian form `⟨x|y⟩ = ((σ∘ρ)x, y)` (conjugate-linear in the first slot). -/
  P : SesqForm K
  /-- The bigrading by `(2R, ghost number)`. -/
  deg : ℤ × ℤ → Submodule ℂ K
  /-- The bigraded pieces span. -/
  span : iSup deg = ⊤
  /-- Distinct bigraded pieces are `P`-orthogonal. -/
  orth : ∀ a b, a ≠ b → ∀ x ∈ deg a, ∀ y ∈ deg b, P x y = 0
  /-- `Q⁻`: raises `2R` by one and the ghost number by one. -/
  Qm : K →ₗ[ℂ] K
  /-- `S⁻`: lowers `2R` by one, raises the ghost number by one. -/
  Sm : K →ₗ[ℂ] K
  /-- `Q⁺`: raises `2R` by one, lowers the ghost number by one. -/
  Qp : K →ₗ[ℂ] K
  /-- `S⁺`: lowers `2R` by one and the ghost number by one. -/
  Sp : K →ₗ[ℂ] K
  Qm_deg : ∀ a, ∀ x ∈ deg a, Qm x ∈ deg (a + shQm)
  Sm_deg : ∀ a, ∀ x ∈ deg a, Sm x ∈ deg (a + shSm)
  Qp_deg : ∀ a, ∀ x ∈ deg a, Qp x ∈ deg (a + shQp)
  Sp_deg : ∀ a, ∀ x ∈ deg a, Sp x ∈ deg (a + shSp)
  /-- The sign `ε_{-+}` of Beem–Garner Lemma 3.16. -/
  c : ℝ
  c_sq : c * c = 1
  /-- `(Q⁻)† = c S⁺`. -/
  adj_Qm : ∀ x y, P (Qm x) y = (c : ℂ) * P x (Sp y)
  /-- `(S⁻)† = -c Q⁺`. -/
  adj_Sm : ∀ x y, P (Sm x) y = -(c : ℂ) * P x (Qp y)
  /-- `(𝐐⁻)² = 0`. -/
  sq_zero : (Qm + Sm).comp (Qm + Sm) = 0
  /-- `𝐐⁻ 𝐐⁺ + 𝐐⁺ 𝐐⁻ = 0`. -/
  anticomm : (Qm + Sm).comp (Qp + Sp) + (Qp + Sp).comp (Qm + Sm) = 0


/-- Supply exactly the missing positivity clause to the verified Kähler API. -/
def KahlerGeometry.toKahler {K : Type u} [AddCommGroup K] [Module ℂ K]
    (S : KahlerGeometry K) (hpos : IsPosOn S.P ⊤) : KahlerComplex K where
  P := S.P
  deg := S.deg
  span := S.span
  orth := S.orth
  Qm := S.Qm
  Sm := S.Sm
  Qp := S.Qp
  Sp := S.Sp
  Qm_deg := S.Qm_deg
  Sm_deg := S.Sm_deg
  Qp_deg := S.Qp_deg
  Sp_deg := S.Sp_deg
  c := S.c
  c_sq := S.c_sq
  adj_Qm := S.adj_Qm
  adj_Sm := S.adj_Sm
  sq_zero := S.sq_zero
  anticomm := S.anticomm
  pos := hpos

end VOA.LeeYangTransferAssembly
