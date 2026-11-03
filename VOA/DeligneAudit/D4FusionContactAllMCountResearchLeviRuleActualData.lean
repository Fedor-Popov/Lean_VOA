import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleData
import VOA.DeligneAudit.D4FusionContactM2ImagesTable

/-! The light sparse rules agree with the original certified D4 coefficients. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.DeligneSector.Sparse

private theorem actual00 : ∀ (i j : Fin 9),
    sparse (rootImages 0 i) j =
      if j = target (Fin.castAdd 8 (0 : Fin 10)) i then
        coeff (Fin.castAdd 8 (0 : Fin 10)) i else 0 := by decide +kernel

private theorem actual01 : ∀ (i j : Fin 9),
    sparse (rootImages 1 i) j =
      if j = target (Fin.castAdd 8 (1 : Fin 10)) i then
        coeff (Fin.castAdd 8 (1 : Fin 10)) i else 0 := by decide +kernel

private theorem actual02 : ∀ (i j : Fin 9),
    sparse (rootImages 2 i) j =
      if j = target (Fin.castAdd 8 (2 : Fin 10)) i then
        coeff (Fin.castAdd 8 (2 : Fin 10)) i else 0 := by decide +kernel

private theorem actual03 : ∀ (i j : Fin 9),
    sparse (rootImages 3 i) j =
      if j = target (Fin.castAdd 8 (3 : Fin 10)) i then
        coeff (Fin.castAdd 8 (3 : Fin 10)) i else 0 := by decide +kernel

private theorem actual04 : ∀ (i j : Fin 9),
    sparse (rootImages 4 i) j =
      if j = target (Fin.castAdd 8 (4 : Fin 10)) i then
        coeff (Fin.castAdd 8 (4 : Fin 10)) i else 0 := by decide +kernel

private theorem actual05 : ∀ (i j : Fin 9),
    sparse (rootImages 5 i) j =
      if j = target (Fin.castAdd 8 (5 : Fin 10)) i then
        coeff (Fin.castAdd 8 (5 : Fin 10)) i else 0 := by decide +kernel

private theorem actual06 : ∀ (i j : Fin 9),
    sparse (rootImages 6 i) j =
      if j = target (Fin.castAdd 8 (6 : Fin 10)) i then
        coeff (Fin.castAdd 8 (6 : Fin 10)) i else 0 := by decide +kernel

private theorem actual07 : ∀ (i j : Fin 9),
    sparse (rootImages 7 i) j =
      if j = target (Fin.castAdd 8 (7 : Fin 10)) i then
        coeff (Fin.castAdd 8 (7 : Fin 10)) i else 0 := by decide +kernel

private theorem actual08 : ∀ (i j : Fin 9),
    sparse (rootImages 8 i) j =
      if j = target (Fin.castAdd 8 (8 : Fin 10)) i then
        coeff (Fin.castAdd 8 (8 : Fin 10)) i else 0 := by decide +kernel

private theorem actual09 : ∀ (i j : Fin 9),
    sparse (rootImages 9 i) j =
      if j = target (Fin.castAdd 8 (9 : Fin 10)) i then
        coeff (Fin.castAdd 8 (9 : Fin 10)) i else 0 := by decide +kernel

theorem actual_g0_check (g : Fin 10) (i j : Fin 9) :
    sparse (rootImages g i) j =
      if j = target (Fin.castAdd 8 g) i then coeff (Fin.castAdd 8 g) i else 0 := by
  fin_cases g
  · exact actual00 i j
  · exact actual01 i j
  · exact actual02 i j
  · exact actual03 i j
  · exact actual04 i j
  · exact actual05 i j
  · exact actual06 i j
  · exact actual07 i j
  · exact actual08 i j
  · exact actual09 i j

theorem actual_contact_coeff : ∀ (e : Fin 8) (i : Fin 9),
    coeff (Fin.natAdd 10 e) i = if i=8 then 1 else 0 := by decide +kernel

theorem actual_contact_target : ∀ e : Fin 8,
    target (Fin.natAdd 10 e) 8 = e.castSucc := by decide +kernel

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules.actual_g0_check
