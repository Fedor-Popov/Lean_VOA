import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedSyntax

/-! Generic cleared static C-color certificates. A certificate stores a
nonzero integer multiplier, a target color word and integer multiples of
static polar products (quadratic times quadratic, quadratic times cubic,
or one color times cubic). Its kernel check is the vanishing of the
collected difference row; the identity then holds under every evaluation
in every commutative ring. No current cutoff, source coverage or rank is
assumed here. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
open QuarticReducedRows QuarticReduced

/-- One static polar-product generator, with un-divided cube lowerings. -/
inductive Gen
  | qq (a1 b1 c1 a2 b2 c2 : ℕ)
  | qc (a1 b1 c1 a2 b2 c2 : ℕ)
  | lc (i : Fin 8) (a2 b2 c2 : ℕ)

def Gen.row : Gen → Row (Fin 8)
  | .qq a1 b1 c1 a2 b2 c2 => mul (orbitRow 2 a1 b1 c1) (orbitRow 2 a2 b2 c2)
  | .qc a1 b1 c1 a2 b2 c2 => mul (orbitRow 2 a1 b1 c1) (orbitRow 3 a2 b2 c2)
  | .lc i a2 b2 c2 => mul [([i],1)] (orbitRow 3 a2 b2 c2)

/-- `mult * target = Σ coefficient * generator`, stored over the integers. -/
structure Cert where
  mult : ℤ
  target : List (Fin 8)
  terms : List (ℤ × Gen)

def termsRow (L : List (ℤ × Gen)) : Row (Fin 8) :=
  L.flatMap fun t => scale (-t.1) t.2.row

def Cert.row (C : Cert) : Row (Fin 8) :=
  scale C.mult [(C.target,1)] ++ termsRow C.terms

/-- The kernel-checkable validity predicate of a certificate. -/
def Cert.valid (C : Cert) : Prop := collect C.row = [] ∧ C.mult ≠ 0

instance (C : Cert) : Decidable C.valid :=
  inferInstanceAs (Decidable (collect C.row = [] ∧ C.mult ≠ 0))

variable {A : Type*} [CommRing A] (v : Fin 8 → A)

theorem eval_termsRow (L : List (ℤ × Gen)) :
    eval v (termsRow L) = -(L.map fun t => t.1 • eval v t.2.row).sum := by
  induction L with
  | nil => simp [termsRow]
  | cons t L ih =>
      rw [termsRow,List.flatMap_cons,eval_append,eval_scale,← termsRow,ih]
      simp only [List.map_cons,List.sum_cons,neg_add,neg_zsmul]

/-- A valid certificate is a polynomial identity under every evaluation. -/
theorem Cert.eval_identity (C : Cert) (h : collect C.row = []) :
    C.mult • wordEval v C.target =
      (C.terms.map fun t => t.1 • eval v t.2.row).sum := by
  have hz := eval_zero_of_collect v C.row h
  rw [Cert.row,eval_append,eval_scale,eval_termsRow] at hz
  have ht : eval v [(C.target,(1 : ℤ))] = wordEval v C.target := by simp
  rw [ht] at hz
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)

#print axioms Cert.eval_identity
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
