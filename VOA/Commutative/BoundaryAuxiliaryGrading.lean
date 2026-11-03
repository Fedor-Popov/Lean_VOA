/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryAuxiliaryInitial
import VOA.Filtered.InfiniteLiJetBidegree

/-!
# Actual conformal grading of the boundary arc presentations

Original and auxiliary ordinary coefficient ideals are homogeneous in conformal
weight. Fixed-weight infinite polynomial pieces use finitely many jet variables.
-/
namespace VOA.BoundaryAuxiliary
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

/-- The conformal weight of a jet current is its ordinary order plus one. -/
def conformalWeight (v : Fin 3 × ℕ) : ℕ := v.2 + 1

/-- The auxiliary filtration is bounded by conformal weight on every variable. -/
theorem auxWeight_le_conformalWeight (v : Fin 3 × ℕ) : auxWeight v ≤ conformalWeight v := by
  dsimp [auxWeight, currentWeight, conformalWeight]
  split_ifs <;> omega

/-- Including a finite jet exponent preserves conformal weight. -/
theorem conformalWeight_mapDomain (p : ℕ) (d : VOA.FiniteJet.JetVar (Fin 3) p →₀ ℕ) :
    Finsupp.weight conformalWeight (d.mapDomain (VOA.InfiniteJet.finiteJetVar p)) =
      Finsupp.weight (VOA.FiniteJet.jetWeight (fun _ => 1) p) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · simp [conformalWeight, VOA.InfiniteJet.finiteJetVar, VOA.FiniteJet.jetWeight, Nat.add_comm]
  · simp
  · simp [Nat.add_mul]

/-- Finite-stage inclusion preserves the actual conformal grading. -/
theorem ofFinite_conformalHomogeneous (p N : ℕ)
    {f : VOA.FiniteJet.JetPoly R (Fin 3) p}
    (hf : f.IsWeightedHomogeneous (VOA.FiniteJet.jetWeight (fun _ => 1) p) N) :
    (VOA.InfiniteJet.ofFinite p f).IsWeightedHomogeneous conformalWeight N := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  | add f g hf hg ihf ihg => simpa only [map_add] using ihf.add ihg
  | monomial e c he =>
      rw [VOA.InfiniteJet.ofFinite, MvPolynomial.rename_monomial]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [conformalWeight_mapDomain, he]

/-- The quadratic Casimir has ordinary polynomial weight two. -/
theorem casimir_homogeneous :
    (casimir : BasePoly R).IsWeightedHomogeneous (fun _ => (1 : ℕ)) 2 := by
  have hx := MvPolynomial.isWeightedHomogeneous_X R (fun _ : Fin 3 => (1 : ℕ))
  have hh := (hx 1).pow 2
  have hef := ((hx 0).mul (hx 2)).C_mul (4 : R)
  simpa [casimir, mul_assoc] using hh.add hef

/-- All three original relations have weight `2*m+1`. -/
theorem baseRelation_homogeneous (m : ℕ) (i : Fin 3) :
    (baseRelation (R := R) m i).IsWeightedHomogeneous (fun _ => (1 : ℕ)) (2 * m + 1) := by
  have h := (MvPolynomial.isWeightedHomogeneous_X R (fun _ : Fin 3 => (1 : ℕ)) i).mul
    ((casimir_homogeneous (R := R)).pow m)
  simpa [baseRelation, nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using h

/-- The auxiliary relations have the same conformal weight. -/
theorem auxiliaryRelation_homogeneous (m : ℕ) (i : Fin 3) :
    (auxiliaryRelation (R := R) m i).IsWeightedHomogeneous (fun _ => (1 : ℕ)) (2 * m + 1) := by
  have hx := MvPolynomial.isWeightedHomogeneous_X R (fun _ : Fin 3 => (1 : ℕ))
  have h := (hx i).mul (((hx 0).mul (hx 2)).pow m)
  simpa [auxiliaryRelation, nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using h

/-- An ordinary relation coefficient has the original weight plus its derivative order. -/
theorem relationCoefficient_conformalHomogeneous {D n : ℕ} {f : BasePoly R}
    (hf : f.IsWeightedHomogeneous (fun _ => (1 : ℕ)) D) :
    (VOA.InfiniteJet.relationCoefficient f n).IsWeightedHomogeneous conformalWeight (D + n) := by
  rw [VOA.InfiniteJet.relationCoefficient_eq_ofFinite]
  apply ofFinite_conformalHomogeneous
  exact VOA.FiniteJet.relationCoeff_isWeightedHomogeneous _ n D n hf

local instance conformalGradedAlgebra :
    GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule R conformalWeight) :=
  MvPolynomial.weightedGradedAlgebra R conformalWeight

/-- The original infinite coefficient ideal is homogeneous for the actual conformal grading. -/
theorem sourceIdeal_conformalHomogeneous (m : ℕ) :
    (sourceIdeal (R := R) m).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R conformalWeight) := by
  unfold sourceIdeal VOA.InfiniteJet.coefficientIdeal
  apply Ideal.homogeneous_span
  rintro p ⟨f, ⟨i, rfl⟩, n, rfl⟩
  exact ⟨2 * m + 1 + n, relationCoefficient_conformalHomogeneous (baseRelation_homogeneous m i)⟩

/-- The auxiliary infinite coefficient ideal is homogeneous for conformal weight as well. -/
theorem auxiliaryIdeal_conformalHomogeneous (m : ℕ) :
    (auxiliaryIdeal (R := R) m).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R conformalWeight) := by
  unfold auxiliaryIdeal VOA.InfiniteJet.coefficientIdeal
  apply Ideal.homogeneous_span
  rintro p ⟨f, ⟨i, rfl⟩, n, rfl⟩
  exact ⟨2 * m + 1 + n, relationCoefficient_conformalHomogeneous (auxiliaryRelation_homogeneous m i)⟩

/-- A supported variable of a conformal-weight-`N` monomial has order at most `N`. -/
theorem conformal_monomialSupport_subset (N : ℕ) (d : Fin 3 × ℕ →₀ ℕ)
    (hd : Finsupp.weight conformalWeight d = N) :
    (↑d.support : Set (Fin 3 × ℕ)) ⊆ Set.range (VOA.InfiniteJet.finiteJetVar N) := by
  intro v hv
  have hpos : 0 < d v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
  have hterm : d v * conformalWeight v ≤ Finsupp.weight conformalWeight d := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (d i * conformalWeight i)) hv
  rw [hd] at hterm
  have hvN : v.2 ≤ N := by dsimp [conformalWeight] at hterm; nlinarith
  exact ⟨⟨v.1, ⟨v.2, Nat.lt_succ_iff.mpr hvN⟩⟩, rfl⟩

/-- Restricting a fixed conformal piece to a sufficient finite stage loses no coefficients. -/
theorem ofFinite_killCompl_conformal (N : ℕ) (f : JetPoly R)
    (hf : f.IsWeightedHomogeneous conformalWeight N) :
    VOA.InfiniteJet.ofFinite N (MvPolynomial.killCompl (VOA.InfiniteJet.finiteJetVar_injective N) f) = f := by
  apply VOA.InfiniteJet.ofFinite_killCompl_eq_of_support_subset
  intro d hd
  exact conformal_monomialSupport_subset N d (hf (MvPolynomial.mem_support_iff.mp hd))

/-- The finite restriction has the same conformal weight. -/
theorem killCompl_conformalHomogeneous (N : ℕ) (f : JetPoly R)
    (hf : f.IsWeightedHomogeneous conformalWeight N) :
    (MvPolynomial.killCompl (VOA.InfiniteJet.finiteJetVar_injective N) f).IsWeightedHomogeneous
      (VOA.FiniteJet.jetWeight (fun _ => 1) N) N := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero]; exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  | add f g hf hg ihf ihg => simpa only [map_add] using ihf.add ihg
  | monomial d c hd =>
      have hs := conformal_monomialSupport_subset N d hd
      rw [MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset
        (VOA.InfiniteJet.finiteJetVar_injective N) _ hs]
      apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [← conformalWeight_mapDomain,
        d.mapDomain_comapDomain _ (VOA.InfiniteJet.finiteJetVar_injective N) hs, hd]

section Field
variable {K : Type*} [Field K]

/-- Finite restriction embeds the infinite homogeneous piece into a finite-stage piece. -/
def conformalPieceToFinite (N : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule K conformalWeight N →ₗ[K]
      VOA.FiniteJet.JetWeightPiece K (fun _ : Fin 3 => 1) N N :=
  ((MvPolynomial.killCompl (VOA.InfiniteJet.finiteJetVar_injective N)).toLinearMap.comp
    (MvPolynomial.weightedHomogeneousSubmodule K conformalWeight N).subtype).codRestrict _
      (fun f => killCompl_conformalHomogeneous (R := K) N f.val f.property)

theorem conformalPieceToFinite_injective (N : ℕ) :
    Function.Injective (conformalPieceToFinite (K := K) N) := by
  intro f g hfg
  apply Subtype.ext
  have h := congrArg (fun q => VOA.InfiniteJet.ofFinite N q.val) hfg
  change VOA.InfiniteJet.ofFinite N
      (MvPolynomial.killCompl (VOA.InfiniteJet.finiteJetVar_injective N) f.val) =
    VOA.InfiniteJet.ofFinite N
      (MvPolynomial.killCompl (VOA.InfiniteJet.finiteJetVar_injective N) g.val) at h
  rwa [ofFinite_killCompl_conformal N f.val f.property,
    ofFinite_killCompl_conformal N g.val g.property] at h

/-- Every conformal-weight polynomial piece is finite dimensional despite infinitely many jets. -/
theorem finiteDimensional_conformalPiece (N : ℕ) :
    FiniteDimensional K (MvPolynomial.weightedHomogeneousSubmodule K conformalWeight N) := by
  letI : Finite (VOA.FiniteJet.JetVar (Fin 3) N) :=
    Finite.of_injective (fun v => (v.generator, v.order)) (by
      intro v w h
      exact VOA.FiniteJet.JetVar.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  letI := VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_weightedHomogeneousSubmodule
    (K := K) (VOA.FiniteJet.jetWeight (fun _ : Fin 3 => 1) N) (fun v => by
      dsimp [VOA.FiniteJet.jetWeight]; omega) N
  exact FiniteDimensional.of_injective (conformalPieceToFinite (K := K) N)
    (conformalPieceToFinite_injective N)

end Field
end
end VOA.BoundaryAuxiliary
