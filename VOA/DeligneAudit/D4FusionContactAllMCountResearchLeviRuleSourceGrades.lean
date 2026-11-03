import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleOrbits
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleGradeData

/-! Exact PBW/current/color degrees for the complete actual orbit sources. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
noncomputable section

variable (K : Type*) [Field K]

def wordGrade (δ : Fin 18 → ℤ) (t : ℤ) (l : List (Fin 18 × ℕ)) : ℤ :=
  (l.map fun x => δ x.1 + t*x.2).sum

theorem word_graded (m : ℕ) (w : Fin 9 → ℤ) (t : ℤ) (δ : Fin 18 → ℤ)
    (l : List (Fin 18 × ℕ))
    (hl : ∀ x ∈ l, ∀ i, coeff x.1 i = 0 ∨ w (target x.1 i) = w i + δ x.1)
    {p : Ring K m} {n : ℤ} (hp : p.IsWeightedHomogeneous (modeWeight m w t) n) :
    (wordOp (representation K m) l p).IsWeightedHomogeneous
      (modeWeight m w t) (n + wordGrade δ t l) := by
  induction l with
  | nil => simpa only [wordOp,wordGrade,List.map_nil,List.sum_nil,add_zero] using hp
  | cons x l ih =>
      have ht := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      change (deriv K m x.1 x.2 (wordOp (representation K m) l p)).IsWeightedHomogeneous _ _
      have hh := deriv_graded K m w t (δ x.1) x.1 x.2
        (hl x (List.mem_cons_self)) ht
      convert hh using 1
      simp only [wordGrade,List.map_cons,List.sum_cons]
      ring

/-- PBW length is unchanged by every original current operator. -/
theorem word_pbw_graded (m : ℕ) (l : List (Fin 18 × ℕ))
    {p : Ring K m} {r : ℤ} (hp : p.IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) r) :
    (wordOp (representation K m) l p).IsWeightedHomogeneous (modeWeight m (fun _ => 1) 0) r := by
  have h := word_graded K m (fun _ => 1) 0 (fun _ => 0) l
    (fun _ _ _ => Or.inr (by ring)) hp
  simpa only [wordGrade,zero_mul,add_zero,List.map_const',List.sum_replicate,nsmul_zero] using h

/-- Current degree is increased by the sum of all nonnegative letter modes. -/
theorem word_current_graded (m : ℕ) (l : List (Fin 18 × ℕ))
    {p : Ring K m} {s : ℤ} (hp : p.IsWeightedHomogeneous (modeWeight m (fun _ => 0) 1) s) :
    (wordOp (representation K m) l p).IsWeightedHomogeneous
      (modeWeight m (fun _ => 0) 1) (s + ((l.map Prod.snd).sum : ℤ)) := by
  have h := word_graded K m (fun _ => 0) 1 (fun _ => 0) l
    (fun _ _ _ => Or.inr (by ring)) hp
  convert h using 1
  simp [wordGrade,Function.comp_def]

end
#print axioms word_graded
#print axioms word_pbw_graded
#print axioms word_current_graded
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
