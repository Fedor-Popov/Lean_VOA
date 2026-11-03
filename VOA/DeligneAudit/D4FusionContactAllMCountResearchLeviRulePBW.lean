import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleActual
import VOA.DeligneAudit.DeligneFusionPBW

/-! Triangular PBW straightening of the original actual differential ideal.
The resulting ideal equality is proved; no completeness input is assumed.
Eliminating the killed positive blocks and counting normal words are separate. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
noncomputable section

/-- Contacts / negative Levi / Cartan / positive Levi, from outside to inside. -/
def category (a : Fin 18) : ℕ :=
  if a.val < 4 then 2 else if a.val < 7 then 3 else if a.val < 10 then 1 else 0

def key (x : Fin 18 × ℕ) : ℕ := category x.1

def pack {m : ℕ} : AllM.DerivIndex m → Fin 18 × ℕ
  | .inl x => (Fin.castAdd 8 x.1,x.2.val)
  | .inr x => (Fin.natAdd 10 x.1,x.2.val)

theorem derivWord_eq_wordOp (m : ℕ) (l : List (AllM.DerivIndex m))
    (p : MvPolynomial (Vars m) ℂ) :
    AllM.derivWord m l p = wordOp (representation ℂ m) (l.map pack) p := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      cases d with
      | inl x =>
          change g0Deriv m x.1 x.2.val (AllM.derivWord m l p) =
            deriv ℂ m (Fin.castAdd 8 x.1) x.2.val
              (wordOp (representation ℂ m) (l.map pack) p)
          rw [ih,deriv_g0]
      | inr x =>
          change eDeriv m x.1 x.2.val (AllM.derivWord m l p) =
            deriv ℂ m (Fin.natAdd 10 x.1) x.2.val
              (wordOp (representation ℂ m) (l.map pack) p)
          rw [ih,deriv_contact]

theorem word_mem_candidate (m : ℕ) (l : List (Fin 18 × ℕ))
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ AllM.candidateIdeal m) :
    wordOp (representation ℂ m) l p ∈ AllM.candidateIdeal m := by
  induction l with
  | nil => exact hp
  | cons x l ih => exact deriv_closed m x.1 x.2 ih

def triangularSeeds (m : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ (j : AllM.SeedIndex m) (l : List (Fin 18 × ℕ)),
    l.IsChain (fun x y => key x ≤ key y) ∧
      p = wordOp (representation ℂ m) l (AllM.seedPoly m j)}

def triangularIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) := Ideal.span (triangularSeeds m)

/-- Every original unsorted source word straightens into the actual sorted ideal. -/
theorem candidate_le_triangular (m : ℕ) : AllM.candidateIdeal m ≤ triangularIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨⟨l,j⟩,rfl⟩
  change AllM.derivWord m l (AllM.seedPoly m j) ∈ triangularIdeal m
  rw [derivWord_eq_wordOp]
  have h := wordOp_mem_sorted key (representation ℂ m) (AllM.seedPoly m j)
    (l.map pack).length (l.map pack) rfl
  have hle : Submodule.span ℂ (sortedSet key (representation ℂ m) (AllM.seedPoly m j)
      (l.map pack).length (VOA.DeligneAudit.SectorGraded.wordDeg (l.map pack))) ≤
      (triangularIdeal m).restrictScalars ℂ := by
    apply Submodule.span_le.mpr
    rintro p ⟨w,hs,_,_,rfl⟩
    exact Ideal.subset_span ⟨j,w,hs,rfl⟩
  exact hle h

/-- Sorting introduced no source equations: every sorted word was already actual. -/
theorem triangular_le_candidate (m : ℕ) : triangularIdeal m ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨j,l,_,rfl⟩
  exact word_mem_candidate m l (AllM.seed_mem_candidate m j)

/-- Unconditional equality with the original whole-coefficient differential ideal. -/
theorem candidateIdeal_eq_triangularIdeal (m : ℕ) :
    AllM.candidateIdeal m = triangularIdeal m :=
  le_antisymm (candidate_le_triangular m) (triangular_le_candidate m)

end
#print axioms candidate_le_triangular
#print axioms candidateIdeal_eq_triangularIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
