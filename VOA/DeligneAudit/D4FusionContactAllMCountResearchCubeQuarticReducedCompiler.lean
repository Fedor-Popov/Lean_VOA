import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedSyntax
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticJetModel

/-! Sound static-cube and unbounded-jet compilation. The finite certificates
only visit jets0--3, but the jet derivative remains globally untruncated. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
open QuarticReducedRows
noncomputable section

theorem rowNext_eq_cubeNext : ∀ d i, rowNext d i = cubeNext d i := by decide +kernel

variable (K : Type*) [CommRing K]

theorem lowerStep_eval (d : Fin 3) (i : Fin 8) :
    lower K d (MvPolynomial.X i) =
      eval (MvPolynomial.X : Fin 8 → P8 K) (lowerStep d i) := by
  rw [lower_X]
  unfold lowerStep
  rw [rowNext_eq_cubeNext]
  cases ht : cubeNext d i <;> simp [wordEval]

theorem orbitRow_eval (r a b c : ℕ) :
    eval (MvPolynomial.X : Fin 8 → P8 K) (orbitRow r a b c) =
      orbit K r a b c := by
  rw [orbitRow,eval_iterate_deriv _ (lower K 2) _ (lowerStep_eval K 2),
    eval_iterate_deriv _ (lower K 1) _ (lowerStep_eval K 1),
    eval_iterate_deriv _ (lower K 0) _ (lowerStep_eval K 0)]
  simp only [eval_cons,eval_nil,one_zsmul,add_zero,wordEval,
    List.map_replicate,List.prod_replicate]
  rfl

theorem jetStep_eval (n : ℕ) : jetRaise (jetVarNat n) = eval jetVarNat (jetStep n) := by
  rw [jetRaise_jetVarNat]
  simp [jetStep,wordEval]

theorem jetRow_eval (j r a b c : ℕ) :
    eval jetVarNat (jetRow j r a b c) =
      ((jetRaise : JetRing → JetRing)^[j]) (jetBase (orbit ℂ r a b c)) := by
  rw [jetRow,eval_iterate_deriv _ jetRaise _ jetStep_eval,eval_map]
  simp only [jetVarNat_base]
  apply congrArg ((jetRaise : JetRing → JetRing)^[j])
  have h := eval_hom (MvPolynomial.X : Fin 8 → P8 ℂ)
    jetBase.toRingHom (orbitRow r a b c)
  change jetBase (eval (MvPolynomial.X : Fin 8 → P8 ℂ) (orbitRow r a b c)) =
    eval (fun i => jetBase (MvPolynomial.X i)) (orbitRow r a b c) at h
  rw [orbitRow_eval] at h
  exact h.symm

end
#print axioms orbitRow_eval
#print axioms jetRow_eval
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
