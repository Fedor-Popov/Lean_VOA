import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedSyntax

/-! The first cleared static C-color certificate. This light kernel check
uses the un-divided cube lowerings and is sound under every commutative-ring
evaluation. No current cutoff, source coverage or rank is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
open QuarticReducedRows QuarticReduced

def targetRow0 : Row (Fin 8) := [([0,0,7,7],1)]

def productRow0 : Row (Fin 8) :=
  mul (orbitRow 2 0 0 0) (orbitRow 2 2 2 2)

def differenceRow0 : Row (Fin 8) :=
  scale 8 targetRow0 ++ scale (-1) productRow0

/-- The exact stored integer identity, checked by the Lean kernel. -/
theorem check0 : collect differenceRow0 = [] := by decide +kernel

/-- The cleared identity remains valid for every variable assignment over
every commutative ring. The two orbit rows use the established cube compiler. -/
theorem eval_identity0 {A : Type*} [CommRing A] (v : Fin 8 → A) :
    (8 : ℤ) • (v 0 ^ 2 * v 7 ^ 2) =
      eval v (orbitRow 2 0 0 0) * eval v (orbitRow 2 2 2 2) := by
  have h := eval_zero_of_collect v differenceRow0 check0
  rw [differenceRow0,eval_append,eval_scale,eval_scale,productRow0,eval_mul] at h
  have he : (8 : ℤ) • eval v targetRow0 =
      eval v (orbitRow 2 0 0 0) * eval v (orbitRow 2 2 2 2) :=
    sub_eq_zero.mp (by simpa only [neg_one_zsmul,sub_eq_add_neg] using h)
  have ht : eval v targetRow0 = v 0 ^ 2 * v 7 ^ 2 := by
    simp [targetRow0,eval,wordEval,pow_two,mul_assoc]
  simpa only [ht] using he

#print axioms check0
#print axioms eval_identity0
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
