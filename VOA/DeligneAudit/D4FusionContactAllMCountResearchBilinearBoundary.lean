import VOA.DeligneAudit.D4FusionContactAllMCountResearchBilinear

/-! # Finite-color formula for the differentiated middle error

The whole current coefficient and both ordered middle terms are kept.
Only the finite bilinear color operator remains after the Cartan shift.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open BoundaryPair

noncomputable section

theorem sourceH_X (x : Vars 2) :
    g0Deriv 2 0 0 (MvPolynomial.X x) =
      (h0Weight x.1 : ℂ) • MvPolynomial.X x := by
  have hh := h0Deriv_modeX 2 0 x.2.val x.1
  simpa only [modeX,dif_pos x.2.isLt,Nat.zero_add,Fin.eta] using hh

theorem lowerH_product (i j : Fin 9) :
    lowerH (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      (h0Weight i : ℂ) • (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) := by
  rw [lowerH.leibniz]
  simp [lowerH,MvPolynomial.mkDerivation_X,smul_eq_mul,mul_comm]

theorem swapModes_product (i j : Fin 9) :
    swapModesAlg (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      MvPolynomial.X (j,0) * MvPolynomial.X (i,1) := by
  simp [swapModesAlg,swapModes,mul_comm]

theorem sourceH_product (i j : Fin 9) :
    g0Deriv 2 0 0 (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      ((h0Weight i : ℂ)+(h0Weight j : ℂ)) •
        (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) := by
  rw [(g0Deriv 2 0 0).leibniz,sourceH_X,sourceH_X]
  simp only [smul_eq_mul,mul_smul_comm]
  rw [mul_comm (MvPolynomial.X (j,1)) (MvPolynomial.X (i,0)),← add_smul]
  congr 1
  exact add_comm _ _

theorem middleBoundaryMap_product (i j : Fin 9) :
    middleBoundaryMap (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      (1/2:ℂ) • (((h0Weight j : ℂ)-(h0Weight i : ℂ)) •
        (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) +
      ((h0Weight i : ℂ)+(h0Weight j : ℂ)) •
        (MvPolynomial.X (j,0) * MvPolynomial.X (i,1))) := by
  change (1/2:ℂ) •
    (g0Deriv 2 0 0 (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) -
      (2:ℂ) • lowerH (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) +
      swapModesAlg (g0Deriv 2 0 0 (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)))) = _
  rw [sourceH_product,lowerH_product,map_smul,swapModes_product]
  module

variable {m : ℕ} (b : BoundaryPair m)

theorem rename_boundary_product (i j : Fin 9) :
    MvPolynomial.rename b.embed (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      modeX m i b.lower.val * modeX m j b.top.val := by
  simp [BoundaryPair.embed,BoundaryPair.embedMode,modeX,b.lower.isLt,b.top.isLt]

theorem rename_nearest_product (i j : Fin 9) :
    MvPolynomial.rename (nearestPair b).embed
      (MvPolynomial.X (i,0) * MvPolynomial.X (j,1)) =
      modeX m i (b.top.val-1) * modeX m j b.top.val := by
  rw [rename_boundary_product]
  rfl

theorem h0Deriv_boundary_product (ha : b.lower.val + 1 < b.top.val) (i j : Fin 9) :
    g0Deriv m 0 (refinementMode b).val
      (MvPolynomial.rename b.embed (MvPolynomial.X (i,0) * MvPolynomial.X (j,1))) =
      (h0Weight i : ℂ) • (modeX m i (b.top.val-1) * modeX m j b.top.val) := by
  rw [rename_boundary_product,(g0Deriv m 0 (refinementMode b).val).leibniz,
    h0Deriv_lower_mode,h0Deriv_top_mode_zero b ha]
  simp only [smul_eq_mul,Algebra.smul_def]
  ring

theorem bilinear_boundary_product (ha : b.lower.val + 1 < b.top.val) (i j : Fin 9) :
    g0Deriv m 0 (refinementMode b).val
      (groupedErrorMap b (MvPolynomial.X (i,0) * MvPolynomial.X (j,1))) =
      MvPolynomial.rename (nearestPair b).embed
        (middleBoundaryMap (MvPolynomial.X (i,0) * MvPolynomial.X (j,1))) := by
  rw [groupedErrorMap_apply]
  rw [Derivation.map_sub,Derivation.map_smul,map_mul,colorCurrentAlg_X,
    colorCurrentAlg_X,h0Deriv_mixed_coefficient,h0Deriv_boundary_product b ha,
    middleBoundaryMap_product]
  simp only [map_smul,map_add,rename_nearest_product]
  simp only [mul_comm]
  module

/-- Exact identity on the entire bilinear span, before any finite color check. -/
theorem bilinear_boundary (ha : b.lower.val + 1 < b.top.val)
    {p : MvPolynomial (Vars 2) ℂ} (hp : p ∈ bilinearSpan) :
    g0Deriv m 0 (refinementMode b).val (groupedErrorMap b p) =
      MvPolynomial.rename (nearestPair b).embed (middleBoundaryMap p) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hp
      exact bilinear_boundary_product b ha i j
  | zero => simp only [map_zero]
  | add p q _ _ ihp ihq => simp only [map_add,ihp,ihq]
  | smul a p _ ih => simp only [map_smul,Derivation.map_smul,ih]

/-- Apply the universal finite-color formula to an actual checked middle orbit. -/
theorem leviOrbit_middle_boundary (ha : b.lower.val + 1 < b.top.val) (l : List (Fin 3)) :
    g0Deriv m 0 (refinementMode b).val
      (evalMap b (leviOrbit l .base).toWheel (middleSeed b)) =
      MvPolynomial.rename (nearestPair b).embed
        (middleBoundaryMap (twoEvalMap (leviOrbit l .base).toWheel twoSeed)) := by
  rw [leviOrbit_middle_error]
  exact bilinear_boundary b ha (checked_levi_bilinear l)

end

#print axioms bilinear_boundary
#print axioms leviOrbit_middle_boundary

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
