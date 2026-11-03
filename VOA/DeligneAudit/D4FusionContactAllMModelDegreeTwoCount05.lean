import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount04
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 350..419, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem350Deg (b : Fin 5) : ℕ := [7, 1, 0, 0, 0].getD b.val 0

def stem350DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem092Deg,
    fun _ => 0,
    stem093Deg,
    fun _ => 0,
    stem094Deg,
    stem095Deg].getD v.val (fun _ => 0)

theorem stem350_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [2, 12]) b.val = stem350Deg b := by
  have hc : ∀ v, stem350Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 12] ++ [v])) c.val =
        stem350DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem092_dcount c
    · cases hv
    · exact stem093_dcount c
    · cases hv
    · exact stem094_dcount c
    · exact stem095_dcount c
  rw [degCount_of_flags leaders 1 12 [2, 12] stem350Flags stem350DCounts
    stem350_flags hc b]
  fin_cases b <;> decide +kernel

def stem351Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

def stem351DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem096Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem351_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [2, 13]) b.val = stem351Deg b := by
  have hc : ∀ v, stem351Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 13] ++ [v])) c.val =
        stem351DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem096_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [2, 13] stem351Flags stem351DCounts
    stem351_flags hc b]
  fin_cases b <;> decide +kernel

def stem352Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem352DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem097Deg,
    stem098Deg].getD v.val (fun _ => 0)

theorem stem352_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [2, 14]) b.val = stem352Deg b := by
  have hc : ∀ v, stem352Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 14] ++ [v])) c.val =
        stem352DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem097_dcount c
    · exact stem098_dcount c
  rw [degCount_of_flags leaders 1 14 [2, 14] stem352Flags stem352DCounts
    stem352_flags hc b]
  fin_cases b <;> decide +kernel

def stem353Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem353DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem099Deg,
    stem100Deg].getD v.val (fun _ => 0)

theorem stem353_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [2, 16]) b.val = stem353Deg b := by
  have hc : ∀ v, stem353Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 16] ++ [v])) c.val =
        stem353DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem099_dcount c
    · exact stem100_dcount c
  rw [degCount_of_flags leaders 1 16 [2, 16] stem353Flags stem353DCounts
    stem353_flags hc b]
  fin_cases b <;> decide +kernel

def stem354Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem354DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem354_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [2, 17]) b.val = stem354Deg b := by
  have hc : ∀ v, stem354Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 17] ++ [v])) c.val =
        stem354DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [2, 17] stem354Flags stem354DCounts
    stem354_flags hc b]
  fin_cases b <;> decide +kernel

def stem355Deg (b : Fin 5) : ℕ := [0, 25, 3, 0, 0].getD b.val 0

def stem355DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem101Deg,
    fun _ => 0,
    stem102Deg,
    stem103Deg,
    stem104Deg,
    fun _ => 0,
    stem105Deg,
    fun _ => 0,
    stem106Deg,
    fun _ => 0,
    stem107Deg,
    fun _ => 0,
    stem108Deg,
    stem109Deg].getD v.val (fun _ => 0)

theorem stem355_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 4 [3, 4]) b.val = stem355Deg b := by
  have hc : ∀ v, stem355Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 4] ++ [v])) c.val =
        stem355DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem101_dcount c
    · cases hv
    · exact stem102_dcount c
    · exact stem103_dcount c
    · exact stem104_dcount c
    · cases hv
    · exact stem105_dcount c
    · cases hv
    · exact stem106_dcount c
    · cases hv
    · exact stem107_dcount c
    · cases hv
    · exact stem108_dcount c
    · exact stem109_dcount c
  rw [degCount_of_flags leaders 1 4 [3, 4] stem355Flags stem355DCounts
    stem355_flags hc b]
  fin_cases b <;> decide +kernel

def stem356Deg (b : Fin 5) : ℕ := [0, 0, 9, 0, 0].getD b.val 0

def stem356DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem110Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem111Deg,
    fun _ => 0,
    stem112Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem113Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem356_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 5 [3, 5]) b.val = stem356Deg b := by
  have hc : ∀ v, stem356Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 5] ++ [v])) c.val =
        stem356DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem110_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem111_dcount c
    · cases hv
    · exact stem112_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem113_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 5 [3, 5] stem356Flags stem356DCounts
    stem356_flags hc b]
  fin_cases b <;> decide +kernel

def stem357Deg (b : Fin 5) : ℕ := [0, 17, 1, 0, 0].getD b.val 0

def stem357DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem114Deg,
    fun _ => 0,
    stem115Deg,
    fun _ => 0,
    stem116Deg,
    fun _ => 0,
    stem117Deg,
    fun _ => 0,
    stem118Deg,
    fun _ => 0,
    stem119Deg,
    stem120Deg].getD v.val (fun _ => 0)

theorem stem357_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [3, 6]) b.val = stem357Deg b := by
  have hc : ∀ v, stem357Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 6] ++ [v])) c.val =
        stem357DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem114_dcount c
    · cases hv
    · exact stem115_dcount c
    · cases hv
    · exact stem116_dcount c
    · cases hv
    · exact stem117_dcount c
    · cases hv
    · exact stem118_dcount c
    · cases hv
    · exact stem119_dcount c
    · exact stem120_dcount c
  rw [degCount_of_flags leaders 1 6 [3, 6] stem357Flags stem357DCounts
    stem357_flags hc b]
  fin_cases b <;> decide +kernel

def stem358Deg (b : Fin 5) : ℕ := [0, 0, 8, 0, 0].getD b.val 0

def stem358DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem121Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem122Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem123Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem358_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 7 [3, 7]) b.val = stem358Deg b := by
  have hc : ∀ v, stem358Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 7] ++ [v])) c.val =
        stem358DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem121_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem122_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem123_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 7 [3, 7] stem358Flags stem358DCounts
    stem358_flags hc b]
  fin_cases b <;> decide +kernel

def stem359Deg (b : Fin 5) : ℕ := [0, 9, 3, 0, 0].getD b.val 0

def stem359DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem124Deg,
    fun _ => 0,
    stem125Deg,
    stem126Deg,
    fun _ => 0,
    fun _ => 0,
    stem127Deg,
    stem128Deg].getD v.val (fun _ => 0)

theorem stem359_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [3, 8]) b.val = stem359Deg b := by
  have hc : ∀ v, stem359Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 8] ++ [v])) c.val =
        stem359DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem124_dcount c
    · cases hv
    · exact stem125_dcount c
    · exact stem126_dcount c
    · cases hv
    · cases hv
    · exact stem127_dcount c
    · exact stem128_dcount c
  rw [degCount_of_flags leaders 1 8 [3, 8] stem359Flags stem359DCounts
    stem359_flags hc b]
  fin_cases b <;> decide +kernel

def stem360Deg (b : Fin 5) : ℕ := [0, 6, 3, 0, 0].getD b.val 0

def stem360DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem129Deg,
    stem130Deg,
    fun _ => 0,
    fun _ => 0,
    stem131Deg,
    stem132Deg].getD v.val (fun _ => 0)

theorem stem360_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [3, 10]) b.val = stem360Deg b := by
  have hc : ∀ v, stem360Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 10] ++ [v])) c.val =
        stem360DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem129_dcount c
    · exact stem130_dcount c
    · cases hv
    · cases hv
    · exact stem131_dcount c
    · exact stem132_dcount c
  rw [degCount_of_flags leaders 1 10 [3, 10] stem360Flags stem360DCounts
    stem360_flags hc b]
  fin_cases b <;> decide +kernel

def stem361Deg (b : Fin 5) : ℕ := [0, 7, 1, 0, 0].getD b.val 0

def stem361DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem133Deg,
    fun _ => 0,
    stem134Deg,
    fun _ => 0,
    stem135Deg,
    stem136Deg].getD v.val (fun _ => 0)

theorem stem361_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [3, 12]) b.val = stem361Deg b := by
  have hc : ∀ v, stem361Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 12] ++ [v])) c.val =
        stem361DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem133_dcount c
    · cases hv
    · exact stem134_dcount c
    · cases hv
    · exact stem135_dcount c
    · exact stem136_dcount c
  rw [degCount_of_flags leaders 1 12 [3, 12] stem361Flags stem361DCounts
    stem361_flags hc b]
  fin_cases b <;> decide +kernel

def stem362Deg (b : Fin 5) : ℕ := [0, 0, 3, 0, 0].getD b.val 0

def stem362DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem137Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem362_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [3, 13]) b.val = stem362Deg b := by
  have hc : ∀ v, stem362Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 13] ++ [v])) c.val =
        stem362DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem137_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [3, 13] stem362Flags stem362DCounts
    stem362_flags hc b]
  fin_cases b <;> decide +kernel

def stem363Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem363DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem138Deg,
    stem139Deg].getD v.val (fun _ => 0)

theorem stem363_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [3, 14]) b.val = stem363Deg b := by
  have hc : ∀ v, stem363Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 14] ++ [v])) c.val =
        stem363DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem138_dcount c
    · exact stem139_dcount c
  rw [degCount_of_flags leaders 1 14 [3, 14] stem363Flags stem363DCounts
    stem363_flags hc b]
  fin_cases b <;> decide +kernel

def stem364Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem364DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem140Deg,
    stem141Deg].getD v.val (fun _ => 0)

theorem stem364_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [3, 16]) b.val = stem364Deg b := by
  have hc : ∀ v, stem364Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 16] ++ [v])) c.val =
        stem364DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem140_dcount c
    · exact stem141_dcount c
  rw [degCount_of_flags leaders 1 16 [3, 16] stem364Flags stem364DCounts
    stem364_flags hc b]
  fin_cases b <;> decide +kernel

def stem365Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem365DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem365_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [3, 17]) b.val = stem365Deg b := by
  have hc : ∀ v, stem365Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([3, 17] ++ [v])) c.val =
        stem365DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [3, 17] stem365Flags stem365DCounts
    stem365_flags hc b]
  fin_cases b <;> decide +kernel

def stem366Deg (b : Fin 5) : ℕ := [10, 6, 0, 0, 0].getD b.val 0

def stem366DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem142Deg,
    stem143Deg,
    fun _ => 0,
    fun _ => 0,
    stem144Deg,
    stem145Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem146Deg,
    stem147Deg].getD v.val (fun _ => 0)

theorem stem366_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 4 [4, 4]) b.val = stem366Deg b := by
  have hc : ∀ v, stem366Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 4] ++ [v])) c.val =
        stem366DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem142_dcount c
    · exact stem143_dcount c
    · cases hv
    · cases hv
    · exact stem144_dcount c
    · exact stem145_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem146_dcount c
    · exact stem147_dcount c
  rw [degCount_of_flags leaders 1 4 [4, 4] stem366Flags stem366DCounts
    stem366_flags hc b]
  fin_cases b <;> decide +kernel

def stem367Deg (b : Fin 5) : ℕ := [17, 1, 0, 0, 0].getD b.val 0

def stem367DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem148Deg,
    fun _ => 0,
    stem149Deg,
    fun _ => 0,
    stem150Deg,
    fun _ => 0,
    stem151Deg,
    fun _ => 0,
    stem152Deg,
    fun _ => 0,
    stem153Deg,
    stem154Deg].getD v.val (fun _ => 0)

theorem stem367_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [4, 6]) b.val = stem367Deg b := by
  have hc : ∀ v, stem367Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 6] ++ [v])) c.val =
        stem367DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem148_dcount c
    · cases hv
    · exact stem149_dcount c
    · cases hv
    · exact stem150_dcount c
    · cases hv
    · exact stem151_dcount c
    · cases hv
    · exact stem152_dcount c
    · cases hv
    · exact stem153_dcount c
    · exact stem154_dcount c
  rw [degCount_of_flags leaders 1 6 [4, 6] stem367Flags stem367DCounts
    stem367_flags hc b]
  fin_cases b <;> decide +kernel

def stem368Deg (b : Fin 5) : ℕ := [0, 8, 0, 0, 0].getD b.val 0

def stem368DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem155Deg,
    fun _ => 0,
    stem156Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem157Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem368_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 7 [4, 7]) b.val = stem368Deg b := by
  have hc : ∀ v, stem368Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 7] ++ [v])) c.val =
        stem368DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem155_dcount c
    · cases hv
    · exact stem156_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem157_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 7 [4, 7] stem368Flags stem368DCounts
    stem368_flags hc b]
  fin_cases b <;> decide +kernel

def stem369Deg (b : Fin 5) : ℕ := [9, 3, 0, 0, 0].getD b.val 0

def stem369DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem158Deg,
    stem159Deg,
    stem160Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem161Deg,
    stem162Deg].getD v.val (fun _ => 0)

theorem stem369_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [4, 8]) b.val = stem369Deg b := by
  have hc : ∀ v, stem369Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 8] ++ [v])) c.val =
        stem369DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem158_dcount c
    · exact stem159_dcount c
    · exact stem160_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem161_dcount c
    · exact stem162_dcount c
  rw [degCount_of_flags leaders 1 8 [4, 8] stem369Flags stem369DCounts
    stem369_flags hc b]
  fin_cases b <;> decide +kernel

def stem370Deg (b : Fin 5) : ℕ := [10, 1, 0, 0, 0].getD b.val 0

def stem370DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem163Deg,
    fun _ => 0,
    stem164Deg,
    fun _ => 0,
    stem165Deg,
    fun _ => 0,
    stem166Deg,
    stem167Deg].getD v.val (fun _ => 0)

theorem stem370_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [4, 10]) b.val = stem370Deg b := by
  have hc : ∀ v, stem370Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 10] ++ [v])) c.val =
        stem370DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem163_dcount c
    · cases hv
    · exact stem164_dcount c
    · cases hv
    · exact stem165_dcount c
    · cases hv
    · exact stem166_dcount c
    · exact stem167_dcount c
  rw [degCount_of_flags leaders 1 10 [4, 10] stem370Flags stem370DCounts
    stem370_flags hc b]
  fin_cases b <;> decide +kernel

def stem371Deg (b : Fin 5) : ℕ := [0, 5, 0, 0, 0].getD b.val 0

def stem371DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem168Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem169Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem371_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 11 [4, 11]) b.val = stem371Deg b := by
  have hc : ∀ v, stem371Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 11] ++ [v])) c.val =
        stem371DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem168_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem169_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 11 [4, 11] stem371Flags stem371DCounts
    stem371_flags hc b]
  fin_cases b <;> decide +kernel

def stem372Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem372DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem170Deg,
    stem171Deg].getD v.val (fun _ => 0)

theorem stem372_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [4, 12]) b.val = stem372Deg b := by
  have hc : ∀ v, stem372Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 12] ++ [v])) c.val =
        stem372DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem170_dcount c
    · exact stem171_dcount c
  rw [degCount_of_flags leaders 1 12 [4, 12] stem372Flags stem372DCounts
    stem372_flags hc b]
  fin_cases b <;> decide +kernel

def stem373Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem373DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem172Deg,
    stem173Deg].getD v.val (fun _ => 0)

theorem stem373_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [4, 14]) b.val = stem373Deg b := by
  have hc : ∀ v, stem373Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 14] ++ [v])) c.val =
        stem373DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem172_dcount c
    · exact stem173_dcount c
  rw [degCount_of_flags leaders 1 14 [4, 14] stem373Flags stem373DCounts
    stem373_flags hc b]
  fin_cases b <;> decide +kernel

def stem374Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem374DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem174Deg,
    stem175Deg].getD v.val (fun _ => 0)

theorem stem374_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [4, 16]) b.val = stem374Deg b := by
  have hc : ∀ v, stem374Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 16] ++ [v])) c.val =
        stem374DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem174_dcount c
    · exact stem175_dcount c
  rw [degCount_of_flags leaders 1 16 [4, 16] stem374Flags stem374DCounts
    stem374_flags hc b]
  fin_cases b <;> decide +kernel

def stem375Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem375DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem375_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [4, 17]) b.val = stem375Deg b := by
  have hc : ∀ v, stem375Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([4, 17] ++ [v])) c.val =
        stem375DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [4, 17] stem375Flags stem375DCounts
    stem375_flags hc b]
  fin_cases b <;> decide +kernel

def stem376Deg (b : Fin 5) : ℕ := [0, 17, 1, 0, 0].getD b.val 0

def stem376DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem176Deg,
    fun _ => 0,
    stem177Deg,
    fun _ => 0,
    stem178Deg,
    fun _ => 0,
    stem179Deg,
    fun _ => 0,
    stem180Deg,
    fun _ => 0,
    stem181Deg,
    stem182Deg].getD v.val (fun _ => 0)

theorem stem376_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [5, 6]) b.val = stem376Deg b := by
  have hc : ∀ v, stem376Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 6] ++ [v])) c.val =
        stem376DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem176_dcount c
    · cases hv
    · exact stem177_dcount c
    · cases hv
    · exact stem178_dcount c
    · cases hv
    · exact stem179_dcount c
    · cases hv
    · exact stem180_dcount c
    · cases hv
    · exact stem181_dcount c
    · exact stem182_dcount c
  rw [degCount_of_flags leaders 1 6 [5, 6] stem376Flags stem376DCounts
    stem376_flags hc b]
  fin_cases b <;> decide +kernel

def stem377Deg (b : Fin 5) : ℕ := [0, 0, 8, 0, 0].getD b.val 0

def stem377DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem183Deg,
    fun _ => 0,
    stem184Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem185Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem377_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 7 [5, 7]) b.val = stem377Deg b := by
  have hc : ∀ v, stem377Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 7] ++ [v])) c.val =
        stem377DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem183_dcount c
    · cases hv
    · exact stem184_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem185_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 7 [5, 7] stem377Flags stem377DCounts
    stem377_flags hc b]
  fin_cases b <;> decide +kernel

def stem378Deg (b : Fin 5) : ℕ := [0, 9, 3, 0, 0].getD b.val 0

def stem378DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem186Deg,
    stem187Deg,
    stem188Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem189Deg,
    stem190Deg].getD v.val (fun _ => 0)

theorem stem378_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [5, 8]) b.val = stem378Deg b := by
  have hc : ∀ v, stem378Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 8] ++ [v])) c.val =
        stem378DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem186_dcount c
    · exact stem187_dcount c
    · exact stem188_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem189_dcount c
    · exact stem190_dcount c
  rw [degCount_of_flags leaders 1 8 [5, 8] stem378Flags stem378DCounts
    stem378_flags hc b]
  fin_cases b <;> decide +kernel

def stem379Deg (b : Fin 5) : ℕ := [0, 10, 1, 0, 0].getD b.val 0

def stem379DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem191Deg,
    fun _ => 0,
    stem192Deg,
    fun _ => 0,
    stem193Deg,
    fun _ => 0,
    stem194Deg,
    stem195Deg].getD v.val (fun _ => 0)

theorem stem379_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [5, 10]) b.val = stem379Deg b := by
  have hc : ∀ v, stem379Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 10] ++ [v])) c.val =
        stem379DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem191_dcount c
    · cases hv
    · exact stem192_dcount c
    · cases hv
    · exact stem193_dcount c
    · cases hv
    · exact stem194_dcount c
    · exact stem195_dcount c
  rw [degCount_of_flags leaders 1 10 [5, 10] stem379Flags stem379DCounts
    stem379_flags hc b]
  fin_cases b <;> decide +kernel

def stem380Deg (b : Fin 5) : ℕ := [0, 0, 5, 0, 0].getD b.val 0

def stem380DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem196Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem197Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem380_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 11 [5, 11]) b.val = stem380Deg b := by
  have hc : ∀ v, stem380Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 11] ++ [v])) c.val =
        stem380DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem196_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem197_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 11 [5, 11] stem380Flags stem380DCounts
    stem380_flags hc b]
  fin_cases b <;> decide +kernel

def stem381Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem381DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem198Deg,
    stem199Deg].getD v.val (fun _ => 0)

theorem stem381_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [5, 12]) b.val = stem381Deg b := by
  have hc : ∀ v, stem381Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 12] ++ [v])) c.val =
        stem381DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem198_dcount c
    · exact stem199_dcount c
  rw [degCount_of_flags leaders 1 12 [5, 12] stem381Flags stem381DCounts
    stem381_flags hc b]
  fin_cases b <;> decide +kernel

def stem382Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem382DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem200Deg,
    stem201Deg].getD v.val (fun _ => 0)

theorem stem382_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [5, 14]) b.val = stem382Deg b := by
  have hc : ∀ v, stem382Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 14] ++ [v])) c.val =
        stem382DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem200_dcount c
    · exact stem201_dcount c
  rw [degCount_of_flags leaders 1 14 [5, 14] stem382Flags stem382DCounts
    stem382_flags hc b]
  fin_cases b <;> decide +kernel

def stem383Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem383DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem202Deg,
    stem203Deg].getD v.val (fun _ => 0)

theorem stem383_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [5, 16]) b.val = stem383Deg b := by
  have hc : ∀ v, stem383Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 16] ++ [v])) c.val =
        stem383DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem202_dcount c
    · exact stem203_dcount c
  rw [degCount_of_flags leaders 1 16 [5, 16] stem383Flags stem383DCounts
    stem383_flags hc b]
  fin_cases b <;> decide +kernel

def stem384Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem384DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem384_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [5, 17]) b.val = stem384Deg b := by
  have hc : ∀ v, stem384Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([5, 17] ++ [v])) c.val =
        stem384DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [5, 17] stem384Flags stem384DCounts
    stem384_flags hc b]
  fin_cases b <;> decide +kernel

def stem385Deg (b : Fin 5) : ℕ := [6, 3, 0, 0, 0].getD b.val 0

def stem385DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem204Deg,
    stem205Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem206Deg,
    stem207Deg].getD v.val (fun _ => 0)

theorem stem385_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [6, 6]) b.val = stem385Deg b := by
  have hc : ∀ v, stem385Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 6] ++ [v])) c.val =
        stem385DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem204_dcount c
    · exact stem205_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem206_dcount c
    · exact stem207_dcount c
  rw [degCount_of_flags leaders 1 6 [6, 6] stem385Flags stem385DCounts
    stem385_flags hc b]
  fin_cases b <;> decide +kernel

def stem386Deg (b : Fin 5) : ℕ := [14, 1, 0, 0, 0].getD b.val 0

def stem386DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem208Deg,
    fun _ => 0,
    stem209Deg,
    fun _ => 0,
    stem210Deg,
    fun _ => 0,
    stem211Deg,
    fun _ => 0,
    stem212Deg,
    stem213Deg].getD v.val (fun _ => 0)

theorem stem386_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [6, 8]) b.val = stem386Deg b := by
  have hc : ∀ v, stem386Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 8] ++ [v])) c.val =
        stem386DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem208_dcount c
    · cases hv
    · exact stem209_dcount c
    · cases hv
    · exact stem210_dcount c
    · cases hv
    · exact stem211_dcount c
    · cases hv
    · exact stem212_dcount c
    · exact stem213_dcount c
  rw [degCount_of_flags leaders 1 8 [6, 8] stem386Flags stem386DCounts
    stem386_flags hc b]
  fin_cases b <;> decide +kernel

def stem387Deg (b : Fin 5) : ℕ := [0, 7, 0, 0, 0].getD b.val 0

def stem387DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem214Deg,
    fun _ => 0,
    stem215Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem216Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem387_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 9 [6, 9]) b.val = stem387Deg b := by
  have hc : ∀ v, stem387Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 9] ++ [v])) c.val =
        stem387DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem214_dcount c
    · cases hv
    · exact stem215_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem216_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 9 [6, 9] stem387Flags stem387DCounts
    stem387_flags hc b]
  fin_cases b <;> decide +kernel

def stem388Deg (b : Fin 5) : ℕ := [5, 1, 0, 0, 0].getD b.val 0

def stem388DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem217Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem218Deg,
    stem219Deg].getD v.val (fun _ => 0)

theorem stem388_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [6, 10]) b.val = stem388Deg b := by
  have hc : ∀ v, stem388Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 10] ++ [v])) c.val =
        stem388DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem217_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem218_dcount c
    · exact stem219_dcount c
  rw [degCount_of_flags leaders 1 10 [6, 10] stem388Flags stem388DCounts
    stem388_flags hc b]
  fin_cases b <;> decide +kernel

def stem389Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem389DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem220Deg,
    stem221Deg].getD v.val (fun _ => 0)

theorem stem389_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [6, 12]) b.val = stem389Deg b := by
  have hc : ∀ v, stem389Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 12] ++ [v])) c.val =
        stem389DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem220_dcount c
    · exact stem221_dcount c
  rw [degCount_of_flags leaders 1 12 [6, 12] stem389Flags stem389DCounts
    stem389_flags hc b]
  fin_cases b <;> decide +kernel

def stem390Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem390DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem222Deg,
    stem223Deg].getD v.val (fun _ => 0)

theorem stem390_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [6, 14]) b.val = stem390Deg b := by
  have hc : ∀ v, stem390Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 14] ++ [v])) c.val =
        stem390DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem222_dcount c
    · exact stem223_dcount c
  rw [degCount_of_flags leaders 1 14 [6, 14] stem390Flags stem390DCounts
    stem390_flags hc b]
  fin_cases b <;> decide +kernel

def stem391Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem391DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem224Deg,
    stem225Deg].getD v.val (fun _ => 0)

theorem stem391_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [6, 16]) b.val = stem391Deg b := by
  have hc : ∀ v, stem391Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 16] ++ [v])) c.val =
        stem391DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem224_dcount c
    · exact stem225_dcount c
  rw [degCount_of_flags leaders 1 16 [6, 16] stem391Flags stem391DCounts
    stem391_flags hc b]
  fin_cases b <;> decide +kernel

def stem392Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem392DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem392_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [6, 17]) b.val = stem392Deg b := by
  have hc : ∀ v, stem392Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([6, 17] ++ [v])) c.val =
        stem392DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [6, 17] stem392Flags stem392DCounts
    stem392_flags hc b]
  fin_cases b <;> decide +kernel

def stem393Deg (b : Fin 5) : ℕ := [0, 14, 1, 0, 0].getD b.val 0

def stem393DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem226Deg,
    fun _ => 0,
    stem227Deg,
    fun _ => 0,
    stem228Deg,
    fun _ => 0,
    stem229Deg,
    fun _ => 0,
    stem230Deg,
    stem231Deg].getD v.val (fun _ => 0)

theorem stem393_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [7, 8]) b.val = stem393Deg b := by
  have hc : ∀ v, stem393Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 8] ++ [v])) c.val =
        stem393DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem226_dcount c
    · cases hv
    · exact stem227_dcount c
    · cases hv
    · exact stem228_dcount c
    · cases hv
    · exact stem229_dcount c
    · cases hv
    · exact stem230_dcount c
    · exact stem231_dcount c
  rw [degCount_of_flags leaders 1 8 [7, 8] stem393Flags stem393DCounts
    stem393_flags hc b]
  fin_cases b <;> decide +kernel

def stem394Deg (b : Fin 5) : ℕ := [0, 0, 7, 0, 0].getD b.val 0

def stem394DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem232Deg,
    fun _ => 0,
    stem233Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem234Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem394_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 9 [7, 9]) b.val = stem394Deg b := by
  have hc : ∀ v, stem394Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 9] ++ [v])) c.val =
        stem394DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem232_dcount c
    · cases hv
    · exact stem233_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem234_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 9 [7, 9] stem394Flags stem394DCounts
    stem394_flags hc b]
  fin_cases b <;> decide +kernel

def stem395Deg (b : Fin 5) : ℕ := [0, 5, 1, 0, 0].getD b.val 0

def stem395DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem235Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem236Deg,
    stem237Deg].getD v.val (fun _ => 0)

theorem stem395_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [7, 10]) b.val = stem395Deg b := by
  have hc : ∀ v, stem395Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 10] ++ [v])) c.val =
        stem395DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem235_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem236_dcount c
    · exact stem237_dcount c
  rw [degCount_of_flags leaders 1 10 [7, 10] stem395Flags stem395DCounts
    stem395_flags hc b]
  fin_cases b <;> decide +kernel

def stem396Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem396DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem238Deg,
    stem239Deg].getD v.val (fun _ => 0)

theorem stem396_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [7, 12]) b.val = stem396Deg b := by
  have hc : ∀ v, stem396Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 12] ++ [v])) c.val =
        stem396DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem238_dcount c
    · exact stem239_dcount c
  rw [degCount_of_flags leaders 1 12 [7, 12] stem396Flags stem396DCounts
    stem396_flags hc b]
  fin_cases b <;> decide +kernel

def stem397Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem397DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem240Deg,
    stem241Deg].getD v.val (fun _ => 0)

theorem stem397_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [7, 14]) b.val = stem397Deg b := by
  have hc : ∀ v, stem397Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 14] ++ [v])) c.val =
        stem397DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem240_dcount c
    · exact stem241_dcount c
  rw [degCount_of_flags leaders 1 14 [7, 14] stem397Flags stem397DCounts
    stem397_flags hc b]
  fin_cases b <;> decide +kernel

def stem398Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem398DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem242Deg,
    stem243Deg].getD v.val (fun _ => 0)

theorem stem398_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [7, 16]) b.val = stem398Deg b := by
  have hc : ∀ v, stem398Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 16] ++ [v])) c.val =
        stem398DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem242_dcount c
    · exact stem243_dcount c
  rw [degCount_of_flags leaders 1 16 [7, 16] stem398Flags stem398DCounts
    stem398_flags hc b]
  fin_cases b <;> decide +kernel

def stem399Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem399DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem399_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [7, 17]) b.val = stem399Deg b := by
  have hc : ∀ v, stem399Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([7, 17] ++ [v])) c.val =
        stem399DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [7, 17] stem399Flags stem399DCounts
    stem399_flags hc b]
  fin_cases b <;> decide +kernel

def stem400Deg (b : Fin 5) : ℕ := [10, 6, 0, 0, 0].getD b.val 0

def stem400DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem244Deg,
    stem245Deg,
    stem246Deg,
    stem247Deg,
    fun _ => 0,
    fun _ => 0,
    stem248Deg,
    stem249Deg].getD v.val (fun _ => 0)

theorem stem400_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [8, 8]) b.val = stem400Deg b := by
  have hc : ∀ v, stem400Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 8] ++ [v])) c.val =
        stem400DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem244_dcount c
    · exact stem245_dcount c
    · exact stem246_dcount c
    · exact stem247_dcount c
    · cases hv
    · cases hv
    · exact stem248_dcount c
    · exact stem249_dcount c
  rw [degCount_of_flags leaders 1 8 [8, 8] stem400Flags stem400DCounts
    stem400_flags hc b]
  fin_cases b <;> decide +kernel

def stem401Deg (b : Fin 5) : ℕ := [11, 3, 0, 0, 0].getD b.val 0

def stem401DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem250Deg,
    fun _ => 0,
    stem251Deg,
    stem252Deg,
    stem253Deg,
    fun _ => 0,
    stem254Deg,
    stem255Deg].getD v.val (fun _ => 0)

theorem stem401_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [8, 10]) b.val = stem401Deg b := by
  have hc : ∀ v, stem401Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 10] ++ [v])) c.val =
        stem401DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem250_dcount c
    · cases hv
    · exact stem251_dcount c
    · exact stem252_dcount c
    · exact stem253_dcount c
    · cases hv
    · exact stem254_dcount c
    · exact stem255_dcount c
  rw [degCount_of_flags leaders 1 10 [8, 10] stem401Flags stem401DCounts
    stem401_flags hc b]
  fin_cases b <;> decide +kernel

def stem402Deg (b : Fin 5) : ℕ := [0, 5, 0, 0, 0].getD b.val 0

def stem402DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem256Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem257Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem402_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 11 [8, 11]) b.val = stem402Deg b := by
  have hc : ∀ v, stem402Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 11] ++ [v])) c.val =
        stem402DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem256_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem257_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 11 [8, 11] stem402Flags stem402DCounts
    stem402_flags hc b]
  fin_cases b <;> decide +kernel

def stem403Deg (b : Fin 5) : ℕ := [7, 1, 0, 0, 0].getD b.val 0

def stem403DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem258Deg,
    fun _ => 0,
    stem259Deg,
    fun _ => 0,
    stem260Deg,
    stem261Deg].getD v.val (fun _ => 0)

theorem stem403_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [8, 12]) b.val = stem403Deg b := by
  have hc : ∀ v, stem403Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 12] ++ [v])) c.val =
        stem403DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem258_dcount c
    · cases hv
    · exact stem259_dcount c
    · cases hv
    · exact stem260_dcount c
    · exact stem261_dcount c
  rw [degCount_of_flags leaders 1 12 [8, 12] stem403Flags stem403DCounts
    stem403_flags hc b]
  fin_cases b <;> decide +kernel

def stem404Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

def stem404DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem262Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem404_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [8, 13]) b.val = stem404Deg b := by
  have hc : ∀ v, stem404Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 13] ++ [v])) c.val =
        stem404DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem262_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [8, 13] stem404Flags stem404DCounts
    stem404_flags hc b]
  fin_cases b <;> decide +kernel

def stem405Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem405DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem263Deg,
    stem264Deg].getD v.val (fun _ => 0)

theorem stem405_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [8, 14]) b.val = stem405Deg b := by
  have hc : ∀ v, stem405Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 14] ++ [v])) c.val =
        stem405DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem263_dcount c
    · exact stem264_dcount c
  rw [degCount_of_flags leaders 1 14 [8, 14] stem405Flags stem405DCounts
    stem405_flags hc b]
  fin_cases b <;> decide +kernel

def stem406Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem406DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem265Deg,
    stem266Deg].getD v.val (fun _ => 0)

theorem stem406_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [8, 16]) b.val = stem406Deg b := by
  have hc : ∀ v, stem406Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 16] ++ [v])) c.val =
        stem406DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem265_dcount c
    · exact stem266_dcount c
  rw [degCount_of_flags leaders 1 16 [8, 16] stem406Flags stem406DCounts
    stem406_flags hc b]
  fin_cases b <;> decide +kernel

def stem407Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem407DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem407_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [8, 17]) b.val = stem407Deg b := by
  have hc : ∀ v, stem407Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([8, 17] ++ [v])) c.val =
        stem407DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [8, 17] stem407Flags stem407DCounts
    stem407_flags hc b]
  fin_cases b <;> decide +kernel

def stem408Deg (b : Fin 5) : ℕ := [0, 11, 3, 0, 0].getD b.val 0

def stem408DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem267Deg,
    fun _ => 0,
    stem268Deg,
    stem269Deg,
    stem270Deg,
    fun _ => 0,
    stem271Deg,
    stem272Deg].getD v.val (fun _ => 0)

theorem stem408_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [9, 10]) b.val = stem408Deg b := by
  have hc : ∀ v, stem408Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 10] ++ [v])) c.val =
        stem408DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem267_dcount c
    · cases hv
    · exact stem268_dcount c
    · exact stem269_dcount c
    · exact stem270_dcount c
    · cases hv
    · exact stem271_dcount c
    · exact stem272_dcount c
  rw [degCount_of_flags leaders 1 10 [9, 10] stem408Flags stem408DCounts
    stem408_flags hc b]
  fin_cases b <;> decide +kernel

def stem409Deg (b : Fin 5) : ℕ := [0, 0, 5, 0, 0].getD b.val 0

def stem409DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem273Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem274Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem409_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 11 [9, 11]) b.val = stem409Deg b := by
  have hc : ∀ v, stem409Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 11] ++ [v])) c.val =
        stem409DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem273_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem274_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 11 [9, 11] stem409Flags stem409DCounts
    stem409_flags hc b]
  fin_cases b <;> decide +kernel

def stem410Deg (b : Fin 5) : ℕ := [0, 7, 1, 0, 0].getD b.val 0

def stem410DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem275Deg,
    fun _ => 0,
    stem276Deg,
    fun _ => 0,
    stem277Deg,
    stem278Deg].getD v.val (fun _ => 0)

theorem stem410_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [9, 12]) b.val = stem410Deg b := by
  have hc : ∀ v, stem410Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 12] ++ [v])) c.val =
        stem410DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem275_dcount c
    · cases hv
    · exact stem276_dcount c
    · cases hv
    · exact stem277_dcount c
    · exact stem278_dcount c
  rw [degCount_of_flags leaders 1 12 [9, 12] stem410Flags stem410DCounts
    stem410_flags hc b]
  fin_cases b <;> decide +kernel

def stem411Deg (b : Fin 5) : ℕ := [0, 0, 3, 0, 0].getD b.val 0

def stem411DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem279Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem411_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [9, 13]) b.val = stem411Deg b := by
  have hc : ∀ v, stem411Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 13] ++ [v])) c.val =
        stem411DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem279_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [9, 13] stem411Flags stem411DCounts
    stem411_flags hc b]
  fin_cases b <;> decide +kernel

def stem412Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem412DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem280Deg,
    stem281Deg].getD v.val (fun _ => 0)

theorem stem412_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [9, 14]) b.val = stem412Deg b := by
  have hc : ∀ v, stem412Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 14] ++ [v])) c.val =
        stem412DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem280_dcount c
    · exact stem281_dcount c
  rw [degCount_of_flags leaders 1 14 [9, 14] stem412Flags stem412DCounts
    stem412_flags hc b]
  fin_cases b <;> decide +kernel

def stem413Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem413DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem282Deg,
    stem283Deg].getD v.val (fun _ => 0)

theorem stem413_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [9, 16]) b.val = stem413Deg b := by
  have hc : ∀ v, stem413Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 16] ++ [v])) c.val =
        stem413DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem282_dcount c
    · exact stem283_dcount c
  rw [degCount_of_flags leaders 1 16 [9, 16] stem413Flags stem413DCounts
    stem413_flags hc b]
  fin_cases b <;> decide +kernel

def stem414Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem414DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem414_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [9, 17]) b.val = stem414Deg b := by
  have hc : ∀ v, stem414Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([9, 17] ++ [v])) c.val =
        stem414DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
  rw [degCount_of_flags leaders 1 17 [9, 17] stem414Flags stem414DCounts
    stem414_flags hc b]
  fin_cases b <;> decide +kernel

def stem415Deg (b : Fin 5) : ℕ := [6, 3, 0, 0, 0].getD b.val 0

def stem415DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem284Deg,
    stem285Deg,
    fun _ => 0,
    fun _ => 0,
    stem286Deg,
    stem287Deg].getD v.val (fun _ => 0)

theorem stem415_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [10, 10]) b.val = stem415Deg b := by
  have hc : ∀ v, stem415Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 10] ++ [v])) c.val =
        stem415DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem284_dcount c
    · exact stem285_dcount c
    · cases hv
    · cases hv
    · exact stem286_dcount c
    · exact stem287_dcount c
  rw [degCount_of_flags leaders 1 10 [10, 10] stem415Flags stem415DCounts
    stem415_flags hc b]
  fin_cases b <;> decide +kernel

def stem416Deg (b : Fin 5) : ℕ := [7, 1, 0, 0, 0].getD b.val 0

def stem416DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem288Deg,
    fun _ => 0,
    stem289Deg,
    fun _ => 0,
    stem290Deg,
    stem291Deg].getD v.val (fun _ => 0)

theorem stem416_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [10, 12]) b.val = stem416Deg b := by
  have hc : ∀ v, stem416Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 12] ++ [v])) c.val =
        stem416DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem288_dcount c
    · cases hv
    · exact stem289_dcount c
    · cases hv
    · exact stem290_dcount c
    · exact stem291_dcount c
  rw [degCount_of_flags leaders 1 12 [10, 12] stem416Flags stem416DCounts
    stem416_flags hc b]
  fin_cases b <;> decide +kernel

def stem417Deg (b : Fin 5) : ℕ := [0, 3, 0, 0, 0].getD b.val 0

def stem417DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem292Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem417_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [10, 13]) b.val = stem417Deg b := by
  have hc : ∀ v, stem417Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 13] ++ [v])) c.val =
        stem417DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem292_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [10, 13] stem417Flags stem417DCounts
    stem417_flags hc b]
  fin_cases b <;> decide +kernel

def stem418Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem418DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem293Deg,
    stem294Deg].getD v.val (fun _ => 0)

theorem stem418_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [10, 14]) b.val = stem418Deg b := by
  have hc : ∀ v, stem418Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 14] ++ [v])) c.val =
        stem418DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem293_dcount c
    · exact stem294_dcount c
  rw [degCount_of_flags leaders 1 14 [10, 14] stem418Flags stem418DCounts
    stem418_flags hc b]
  fin_cases b <;> decide +kernel

def stem419Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem419DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem295Deg,
    stem296Deg].getD v.val (fun _ => 0)

theorem stem419_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [10, 16]) b.val = stem419Deg b := by
  have hc : ∀ v, stem419Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 16] ++ [v])) c.val =
        stem419DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem295_dcount c
    · exact stem296_dcount c
  rw [degCount_of_flags leaders 1 16 [10, 16] stem419Flags stem419DCounts
    stem419_flags hc b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem419_dcount
