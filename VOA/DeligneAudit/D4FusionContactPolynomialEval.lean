import VOA.DeligneAudit.D4FusionContactPolynomialGr
import VOA.DeligneAudit.D4FusionContactTruncation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Finite polynomial evaluation on the actual restricted contact PBW module

The target is the graded cyclic span of actual word symbols. The nine
negative-current symbols commute there; no commutativity on the full
ambient quotient is used. Vector evaluation has an actual annihilator
ideal because polynomial operators act multiplicatively.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

section Evaluation

variable {ι : Type} (letter : ι → CurrentLetter)

def polyOp (i : ι) : Module.End ℂ (Gr R w) := grOp R w (letter i).1 (letter i).2

theorem polyOp_commute (i j : ι) :
    polyOp R w letter i * polyOp R w letter j = polyOp R w letter j * polyOp R w letter i :=
  grOp_commute R w _ _ _ _

abbrev PolyAlg := Algebra.adjoin ℂ (Set.range (polyOp R w letter))

def polyAlg : MvPolynomial ι ℂ →ₐ[ℂ] Module.End ℂ (Gr R w) :=
  letI : IsMulCommutative (PolyAlg R w letter) := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact polyOp_commute R w letter i j)
  letI : CommRing (PolyAlg R w letter) :=
    { toRing := inferInstance
      mul_comm := mul_comm' }
  (PolyAlg R w letter).val.comp
    (MvPolynomial.aeval fun i => ⟨polyOp R w letter i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

theorem polyAlg_X (i : ι) : polyAlg R w letter (MvPolynomial.X i) = polyOp R w letter i := by
  simp [polyAlg]

def polyEval : MvPolynomial ι ℂ →ₗ[ℂ] Gr R w :=
  (LinearMap.applyₗ (grGenerator R w)).comp (polyAlg R w letter).toLinearMap

theorem polyEval_one : polyEval R w letter 1 = grGenerator R w := by
  change (polyAlg R w letter 1) (grGenerator R w) = _
  rw [map_one]
  rfl

theorem polyEval_mul (p q : MvPolynomial ι ℂ) :
    polyEval R w letter (p * q) = polyAlg R w letter p (polyEval R w letter q) := by
  change (polyAlg R w letter (p * q)) (grGenerator R w) = _
  rw [map_mul, Module.End.mul_apply]
  rfl

theorem polyEval_X_mul (i : ι) (p : MvPolynomial ι ℂ) :
    polyEval R w letter (MvPolynomial.X i * p) =
      grOp R w (letter i).1 (letter i).2 (polyEval R w letter p) := by
  rw [polyEval_mul, polyAlg_X]
  rfl

/-- The full kernel of vector evaluation is an ideal, with closure under
all polynomial multipliers proved from the actual operator algebra. -/
def annIdeal : Ideal (MvPolynomial ι ℂ) where
  carrier := {p | polyEval R w letter p = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro p q hp hq
    change polyEval R w letter (p + q) = 0
    rw [map_add, hp, hq, add_zero]
  smul_mem' := by
    intro p q hq
    change polyEval R w letter (p * q) = 0
    rw [polyEval_mul, hq, map_zero]

theorem mem_annIdeal (p : MvPolynomial ι ℂ) :
    p ∈ annIdeal R w letter ↔ polyEval R w letter p = 0 := Iff.rfl

theorem annIdeal_restrictScalars :
    (annIdeal R w letter).restrictScalars ℂ = LinearMap.ker (polyEval R w letter) := rfl

def polyWord (l : List ι) : MvPolynomial ι ℂ := (l.map MvPolynomial.X).prod

theorem polyEval_polyWord (l : List ι) :
    polyEval R w letter (polyWord l) = grWord R w (l.map letter) := by
  induction l with
  | nil => exact polyEval_one R w letter
  | cons i l ih =>
      change polyEval R w letter (MvPolynomial.X i * polyWord l) = _
      rw [polyEval_X_mul, ih, grOp_grWord]
      rfl

theorem polyEval_surjective
    (hcover : ∀ i r, (∃ j, letter j = (i, r)) ∨ R.op (radIndex i) r w = 0) :
    Function.Surjective (polyEval R w letter) := by
  have hword : ∀ l : List CurrentLetter, grWord R w l ∈ LinearMap.range (polyEval R w letter) := by
    intro l
    induction l with
    | nil => exact ⟨1, polyEval_one R w letter⟩
    | cons x l ih =>
        obtain ⟨p, hp⟩ := ih
        rcases hcover x.1 x.2 with ⟨j, hj⟩ | hk
        · refine ⟨MvPolynomial.X j * p, ?_⟩
          rw [polyEval_X_mul, hj, hp, grOp_grWord]
        · refine ⟨0, ?_⟩
          rw [map_zero, ← grOp_grWord, grOp_zero_of_source_zero R w x.1 x.2 hk]
          rfl
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← grWord_span_top R w]
  exact Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hword l)

/-- An actual ideal contained in the full vector annihilator gives an
actual vector-space quotient map, with all multipliers already handled. -/
def polyQuotientMap (I : Ideal (MvPolynomial ι ℂ)) (hI : I ≤ annIdeal R w letter) :
    (MvPolynomial ι ℂ ⧸ I.restrictScalars ℂ) →ₗ[ℂ] Gr R w :=
  (I.restrictScalars ℂ).liftQ (polyEval R w letter) (fun _ hp => hI hp)

theorem polyQuotientMap_surjective (I : Ideal (MvPolynomial ι ℂ))
    (hI : I ≤ annIdeal R w letter)
    (hcover : ∀ i r, (∃ j, letter j = (i, r)) ∨ R.op (radIndex i) r w = 0) :
    Function.Surjective (polyQuotientMap R w letter I hI) := by
  intro v
  obtain ⟨p, hp⟩ := polyEval_surjective R w letter hcover v
  exact ⟨(I.restrictScalars ℂ).mkQ p, hp⟩

end Evaluation

abbrev Vars (m : ℕ) := Fin 9 × Fin m

def modeLetter (m : ℕ) (x : Vars m) : CurrentLetter := (x.1, x.2.val)

variable {R w}

theorem modeLetter_cover {m : ℕ}
    (hhigh : ∀ i r, m ≤ r → R.op (radIndex i) r w = 0) :
    ∀ i r, (∃ x, modeLetter m x = (i, r)) ∨ R.op (radIndex i) r w = 0 := by
  intro i r
  by_cases hr : r < m
  · exact Or.inl ⟨(i, ⟨r, hr⟩), rfl⟩
  · exact Or.inr (hhigh i r (by omega))

open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

variable {R : CurrentModule D4sector.f V} {m : ℕ}

theorem source_polyEval_surjective (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m) :
    Function.Surjective (polyEval R w (modeLetter m)) := by
  apply polyEval_surjective
  apply modeLetter_cover
  intro i r hr
  exact localWeyl_high_kills hm h (radIndex i) r hr

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.annIdeal_restrictScalars
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_polyEval_surjective
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.polyQuotientMap_surjective
