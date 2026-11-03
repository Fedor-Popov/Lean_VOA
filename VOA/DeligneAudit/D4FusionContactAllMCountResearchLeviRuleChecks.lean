import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleData

/-! Eighteen independent 162-entry integer cancellation leaves. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules

private theorem check00 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 0 b i) = [] := by decide +kernel

private theorem check01 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 1 b i) = [] := by decide +kernel

private theorem check02 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 2 b i) = [] := by decide +kernel

private theorem check03 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 3 b i) = [] := by decide +kernel

private theorem check04 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 4 b i) = [] := by decide +kernel

private theorem check05 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 5 b i) = [] := by decide +kernel

private theorem check06 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 6 b i) = [] := by decide +kernel

private theorem check07 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 7 b i) = [] := by decide +kernel

private theorem check08 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 8 b i) = [] := by decide +kernel

private theorem check09 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 9 b i) = [] := by decide +kernel

private theorem check10 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 10 b i) = [] := by decide +kernel

private theorem check11 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 11 b i) = [] := by decide +kernel

private theorem check12 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 12 b i) = [] := by decide +kernel

private theorem check13 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 13 b i) = [] := by decide +kernel

private theorem check14 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 14 b i) = [] := by decide +kernel

private theorem check15 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 15 b i) = [] := by decide +kernel

private theorem check16 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 16 b i) = [] := by decide +kernel

private theorem check17 : ∀ (b : Fin 18) (i : Fin 9),
    Rows.collect (bracketRow 17 b i) = [] := by decide +kernel

theorem bracketRow_check (a b : Fin 18) (i : Fin 9) :
    Rows.collect (bracketRow a b i) = [] := by
  fin_cases a
  · exact check00 b i
  · exact check01 b i
  · exact check02 b i
  · exact check03 b i
  · exact check04 b i
  · exact check05 b i
  · exact check06 b i
  · exact check07 b i
  · exact check08 b i
  · exact check09 b i
  · exact check10 b i
  · exact check11 b i
  · exact check12 b i
  · exact check13 b i
  · exact check14 b i
  · exact check15 b i
  · exact check16 b i
  · exact check17 b i

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules.bracketRow_check
