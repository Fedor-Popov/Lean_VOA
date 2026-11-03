import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount05
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 420..459, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem420Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem420DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem420_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [10, 17]) b.val = stem420Deg b := by
  have hc : ∀ v, stem420Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([10, 17] ++ [v])) c.val =
        stem420DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [10, 17] stem420Flags stem420DCounts
    stem420_flags hc b]
  fin_cases b <;> decide +kernel

def stem421Deg (b : Fin 5) : ℕ := [0, 7, 1, 0, 0].getD b.val 0

def stem421DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem297Deg,
    fun _ => 0,
    stem298Deg,
    fun _ => 0,
    stem299Deg,
    stem300Deg].getD v.val (fun _ => 0)

theorem stem421_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [11, 12]) b.val = stem421Deg b := by
  have hc : ∀ v, stem421Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([11, 12] ++ [v])) c.val =
        stem421DCounts v c := by
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
    · exact stem297_dcount c
    · cases hv
    · exact stem298_dcount c
    · cases hv
    · exact stem299_dcount c
    · exact stem300_dcount c
  rw [degCount_of_flags leaders 1 12 [11, 12] stem421Flags stem421DCounts
    stem421_flags hc b]
  fin_cases b <;> decide +kernel

def stem422Deg (b : Fin 5) : ℕ := [0, 0, 3, 0, 0].getD b.val 0

def stem422DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem301Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem422_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 13 [11, 13]) b.val = stem422Deg b := by
  have hc : ∀ v, stem422Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([11, 13] ++ [v])) c.val =
        stem422DCounts v c := by
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
    · exact stem301_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 13 [11, 13] stem422Flags stem422DCounts
    stem422_flags hc b]
  fin_cases b <;> decide +kernel

def stem423Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem423DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem302Deg,
    stem303Deg].getD v.val (fun _ => 0)

theorem stem423_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [11, 14]) b.val = stem423Deg b := by
  have hc : ∀ v, stem423Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([11, 14] ++ [v])) c.val =
        stem423DCounts v c := by
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
    · exact stem302_dcount c
    · exact stem303_dcount c
  rw [degCount_of_flags leaders 1 14 [11, 14] stem423Flags stem423DCounts
    stem423_flags hc b]
  fin_cases b <;> decide +kernel

def stem424Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem424DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem304Deg,
    stem305Deg].getD v.val (fun _ => 0)

theorem stem424_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [11, 16]) b.val = stem424Deg b := by
  have hc : ∀ v, stem424Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([11, 16] ++ [v])) c.val =
        stem424DCounts v c := by
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
    · exact stem304_dcount c
    · exact stem305_dcount c
  rw [degCount_of_flags leaders 1 16 [11, 16] stem424Flags stem424DCounts
    stem424_flags hc b]
  fin_cases b <;> decide +kernel

def stem425Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem425DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem425_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [11, 17]) b.val = stem425Deg b := by
  have hc : ∀ v, stem425Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([11, 17] ++ [v])) c.val =
        stem425DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [11, 17] stem425Flags stem425DCounts
    stem425_flags hc b]
  fin_cases b <;> decide +kernel

def stem426Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem426DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem306Deg,
    stem307Deg].getD v.val (fun _ => 0)

theorem stem426_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [12, 12]) b.val = stem426Deg b := by
  have hc : ∀ v, stem426Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([12, 12] ++ [v])) c.val =
        stem426DCounts v c := by
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
    · exact stem306_dcount c
    · exact stem307_dcount c
  rw [degCount_of_flags leaders 1 12 [12, 12] stem426Flags stem426DCounts
    stem426_flags hc b]
  fin_cases b <;> decide +kernel

def stem427Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem427DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem308Deg,
    stem309Deg].getD v.val (fun _ => 0)

theorem stem427_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [12, 14]) b.val = stem427Deg b := by
  have hc : ∀ v, stem427Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([12, 14] ++ [v])) c.val =
        stem427DCounts v c := by
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
    · exact stem308_dcount c
    · exact stem309_dcount c
  rw [degCount_of_flags leaders 1 14 [12, 14] stem427Flags stem427DCounts
    stem427_flags hc b]
  fin_cases b <;> decide +kernel

def stem428Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem428DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem310Deg,
    stem311Deg].getD v.val (fun _ => 0)

theorem stem428_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [12, 16]) b.val = stem428Deg b := by
  have hc : ∀ v, stem428Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([12, 16] ++ [v])) c.val =
        stem428DCounts v c := by
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
    · exact stem310_dcount c
    · exact stem311_dcount c
  rw [degCount_of_flags leaders 1 16 [12, 16] stem428Flags stem428DCounts
    stem428_flags hc b]
  fin_cases b <;> decide +kernel

def stem429Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem429DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem429_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [12, 17]) b.val = stem429Deg b := by
  have hc : ∀ v, stem429Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([12, 17] ++ [v])) c.val =
        stem429DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [12, 17] stem429Flags stem429DCounts
    stem429_flags hc b]
  fin_cases b <;> decide +kernel

def stem430Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem430DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem312Deg,
    stem313Deg].getD v.val (fun _ => 0)

theorem stem430_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [13, 14]) b.val = stem430Deg b := by
  have hc : ∀ v, stem430Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([13, 14] ++ [v])) c.val =
        stem430DCounts v c := by
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
    · exact stem312_dcount c
    · exact stem313_dcount c
  rw [degCount_of_flags leaders 1 14 [13, 14] stem430Flags stem430DCounts
    stem430_flags hc b]
  fin_cases b <;> decide +kernel

def stem431Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem431DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem314Deg,
    stem315Deg].getD v.val (fun _ => 0)

theorem stem431_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [13, 16]) b.val = stem431Deg b := by
  have hc : ∀ v, stem431Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([13, 16] ++ [v])) c.val =
        stem431DCounts v c := by
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
    · exact stem314_dcount c
    · exact stem315_dcount c
  rw [degCount_of_flags leaders 1 16 [13, 16] stem431Flags stem431DCounts
    stem431_flags hc b]
  fin_cases b <;> decide +kernel

def stem432Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem432DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem432_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [13, 17]) b.val = stem432Deg b := by
  have hc : ∀ v, stem432Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([13, 17] ++ [v])) c.val =
        stem432DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [13, 17] stem432Flags stem432DCounts
    stem432_flags hc b]
  fin_cases b <;> decide +kernel

def stem433Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem433DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem316Deg,
    stem317Deg].getD v.val (fun _ => 0)

theorem stem433_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [14, 14]) b.val = stem433Deg b := by
  have hc : ∀ v, stem433Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([14, 14] ++ [v])) c.val =
        stem433DCounts v c := by
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
    · exact stem316_dcount c
    · exact stem317_dcount c
  rw [degCount_of_flags leaders 1 14 [14, 14] stem433Flags stem433DCounts
    stem433_flags hc b]
  fin_cases b <;> decide +kernel

def stem434Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem434DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem318Deg,
    stem319Deg].getD v.val (fun _ => 0)

theorem stem434_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [14, 16]) b.val = stem434Deg b := by
  have hc : ∀ v, stem434Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([14, 16] ++ [v])) c.val =
        stem434DCounts v c := by
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
    · exact stem318_dcount c
    · exact stem319_dcount c
  rw [degCount_of_flags leaders 1 16 [14, 16] stem434Flags stem434DCounts
    stem434_flags hc b]
  fin_cases b <;> decide +kernel

def stem435Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem435DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem435_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [14, 17]) b.val = stem435Deg b := by
  have hc : ∀ v, stem435Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([14, 17] ++ [v])) c.val =
        stem435DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [14, 17] stem435Flags stem435DCounts
    stem435_flags hc b]
  fin_cases b <;> decide +kernel

def stem436Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem436DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem320Deg,
    stem321Deg].getD v.val (fun _ => 0)

theorem stem436_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [15, 16]) b.val = stem436Deg b := by
  have hc : ∀ v, stem436Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([15, 16] ++ [v])) c.val =
        stem436DCounts v c := by
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
    · exact stem320_dcount c
    · exact stem321_dcount c
  rw [degCount_of_flags leaders 1 16 [15, 16] stem436Flags stem436DCounts
    stem436_flags hc b]
  fin_cases b <;> decide +kernel

def stem437Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem437DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem437_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [15, 17]) b.val = stem437Deg b := by
  have hc : ∀ v, stem437Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([15, 17] ++ [v])) c.val =
        stem437DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [15, 17] stem437Flags stem437DCounts
    stem437_flags hc b]
  fin_cases b <;> decide +kernel

def stem438Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem438DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem322Deg,
    stem323Deg].getD v.val (fun _ => 0)

theorem stem438_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [16, 16]) b.val = stem438Deg b := by
  have hc : ∀ v, stem438Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([16, 16] ++ [v])) c.val =
        stem438DCounts v c := by
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
    · exact stem322_dcount c
    · exact stem323_dcount c
  rw [degCount_of_flags leaders 1 16 [16, 16] stem438Flags stem438DCounts
    stem438_flags hc b]
  fin_cases b <;> decide +kernel

def stem439Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem439DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem439_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [16, 17]) b.val = stem439Deg b := by
  have hc : ∀ v, stem439Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([16, 17] ++ [v])) c.val =
        stem439DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [16, 17] stem439Flags stem439DCounts
    stem439_flags hc b]
  fin_cases b <;> decide +kernel

def stem440Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem440DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem440_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [17, 17]) b.val = stem440Deg b := by
  have hc : ∀ v, stem440Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([17, 17] ++ [v])) c.val =
        stem440DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [17, 17] stem440Flags stem440DCounts
    stem440_flags hc b]
  fin_cases b <;> decide +kernel

def stem441Deg (b : Fin 5) : ℕ := [46, 10, 0, 0, 0].getD b.val 0

def stem441DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [stem324Deg,
    fun _ => 0,
    stem325Deg,
    fun _ => 0,
    stem326Deg,
    fun _ => 0,
    stem327Deg,
    fun _ => 0,
    stem328Deg,
    fun _ => 0,
    stem329Deg,
    fun _ => 0,
    stem330Deg,
    fun _ => 0,
    stem331Deg,
    fun _ => 0,
    stem332Deg,
    stem333Deg].getD v.val (fun _ => 0)

theorem stem441_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 0 [0]) b.val = stem441Deg b := by
  have hc : ∀ v, stem441Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([0] ++ [v])) c.val =
        stem441DCounts v c := by
    intro v hv c
    fin_cases v
    · exact stem324_dcount c
    · cases hv
    · exact stem325_dcount c
    · cases hv
    · exact stem326_dcount c
    · cases hv
    · exact stem327_dcount c
    · cases hv
    · exact stem328_dcount c
    · cases hv
    · exact stem329_dcount c
    · cases hv
    · exact stem330_dcount c
    · cases hv
    · exact stem331_dcount c
    · cases hv
    · exact stem332_dcount c
    · exact stem333_dcount c
  rw [degCount_of_flags leaders 2 0 [0] stem441Flags stem441DCounts
    stem441_flags hc b]
  fin_cases b <;> decide +kernel

def stem442Deg (b : Fin 5) : ℕ := [0, 43, 9, 0, 0].getD b.val 0

def stem442DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    stem334Deg,
    fun _ => 0,
    stem335Deg,
    fun _ => 0,
    stem336Deg,
    fun _ => 0,
    stem337Deg,
    fun _ => 0,
    stem338Deg,
    fun _ => 0,
    stem339Deg,
    fun _ => 0,
    stem340Deg,
    fun _ => 0,
    stem341Deg,
    stem342Deg].getD v.val (fun _ => 0)

theorem stem442_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 1 [1]) b.val = stem442Deg b := by
  have hc : ∀ v, stem442Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([1] ++ [v])) c.val =
        stem442DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · exact stem334_dcount c
    · cases hv
    · exact stem335_dcount c
    · cases hv
    · exact stem336_dcount c
    · cases hv
    · exact stem337_dcount c
    · cases hv
    · exact stem338_dcount c
    · cases hv
    · exact stem339_dcount c
    · cases hv
    · exact stem340_dcount c
    · cases hv
    · exact stem341_dcount c
    · exact stem342_dcount c
  rw [degCount_of_flags leaders 2 1 [1] stem442Flags stem442DCounts
    stem442_flags hc b]
  fin_cases b <;> decide +kernel

def stem443Deg (b : Fin 5) : ℕ := [86, 44, 0, 0, 0].getD b.val 0

def stem443DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    stem343Deg,
    fun _ => 0,
    stem344Deg,
    stem345Deg,
    stem346Deg,
    stem347Deg,
    stem348Deg,
    fun _ => 0,
    stem349Deg,
    fun _ => 0,
    stem350Deg,
    stem351Deg,
    stem352Deg,
    fun _ => 0,
    stem353Deg,
    stem354Deg].getD v.val (fun _ => 0)

theorem stem443_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 2 [2]) b.val = stem443Deg b := by
  have hc : ∀ v, stem443Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([2] ++ [v])) c.val =
        stem443DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · exact stem343_dcount c
    · cases hv
    · exact stem344_dcount c
    · exact stem345_dcount c
    · exact stem346_dcount c
    · exact stem347_dcount c
    · exact stem348_dcount c
    · cases hv
    · exact stem349_dcount c
    · cases hv
    · exact stem350_dcount c
    · exact stem351_dcount c
    · exact stem352_dcount c
    · cases hv
    · exact stem353_dcount c
    · exact stem354_dcount c
  rw [degCount_of_flags leaders 2 2 [2] stem443Flags stem443DCounts
    stem443_flags hc b]
  fin_cases b <;> decide +kernel

def stem444Deg (b : Fin 5) : ℕ := [0, 71, 34, 0, 0].getD b.val 0

def stem444DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem355Deg,
    stem356Deg,
    stem357Deg,
    stem358Deg,
    stem359Deg,
    fun _ => 0,
    stem360Deg,
    fun _ => 0,
    stem361Deg,
    stem362Deg,
    stem363Deg,
    fun _ => 0,
    stem364Deg,
    stem365Deg].getD v.val (fun _ => 0)

theorem stem444_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 3 [3]) b.val = stem444Deg b := by
  have hc : ∀ v, stem444Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([3] ++ [v])) c.val =
        stem444DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem355_dcount c
    · exact stem356_dcount c
    · exact stem357_dcount c
    · exact stem358_dcount c
    · exact stem359_dcount c
    · cases hv
    · exact stem360_dcount c
    · cases hv
    · exact stem361_dcount c
    · exact stem362_dcount c
    · exact stem363_dcount c
    · cases hv
    · exact stem364_dcount c
    · exact stem365_dcount c
  rw [degCount_of_flags leaders 2 3 [3] stem444Flags stem444DCounts
    stem444_flags hc b]
  fin_cases b <;> decide +kernel

def stem445Deg (b : Fin 5) : ℕ := [56, 28, 0, 0, 0].getD b.val 0

def stem445DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem366Deg,
    fun _ => 0,
    stem367Deg,
    stem368Deg,
    stem369Deg,
    fun _ => 0,
    stem370Deg,
    stem371Deg,
    stem372Deg,
    fun _ => 0,
    stem373Deg,
    fun _ => 0,
    stem374Deg,
    stem375Deg].getD v.val (fun _ => 0)

theorem stem445_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 4 [4]) b.val = stem445Deg b := by
  have hc : ∀ v, stem445Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([4] ++ [v])) c.val =
        stem445DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem366_dcount c
    · cases hv
    · exact stem367_dcount c
    · exact stem368_dcount c
    · exact stem369_dcount c
    · cases hv
    · exact stem370_dcount c
    · exact stem371_dcount c
    · exact stem372_dcount c
    · cases hv
    · exact stem373_dcount c
    · cases hv
    · exact stem374_dcount c
    · exact stem375_dcount c
  rw [degCount_of_flags leaders 2 4 [4] stem445Flags stem445DCounts
    stem445_flags hc b]
  fin_cases b <;> decide +kernel

def stem446Deg (b : Fin 5) : ℕ := [0, 46, 22, 0, 0].getD b.val 0

def stem446DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem376Deg,
    stem377Deg,
    stem378Deg,
    fun _ => 0,
    stem379Deg,
    stem380Deg,
    stem381Deg,
    fun _ => 0,
    stem382Deg,
    fun _ => 0,
    stem383Deg,
    stem384Deg].getD v.val (fun _ => 0)

theorem stem446_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 5 [5]) b.val = stem446Deg b := by
  have hc : ∀ v, stem446Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([5] ++ [v])) c.val =
        stem446DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem376_dcount c
    · exact stem377_dcount c
    · exact stem378_dcount c
    · cases hv
    · exact stem379_dcount c
    · exact stem380_dcount c
    · exact stem381_dcount c
    · cases hv
    · exact stem382_dcount c
    · cases hv
    · exact stem383_dcount c
    · exact stem384_dcount c
  rw [degCount_of_flags leaders 2 5 [5] stem446Flags stem446DCounts
    stem446_flags hc b]
  fin_cases b <;> decide +kernel

def stem447Deg (b : Fin 5) : ℕ := [35, 16, 0, 0, 0].getD b.val 0

def stem447DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem385Deg,
    fun _ => 0,
    stem386Deg,
    stem387Deg,
    stem388Deg,
    fun _ => 0,
    stem389Deg,
    fun _ => 0,
    stem390Deg,
    fun _ => 0,
    stem391Deg,
    stem392Deg].getD v.val (fun _ => 0)

theorem stem447_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 6 [6]) b.val = stem447Deg b := by
  have hc : ∀ v, stem447Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([6] ++ [v])) c.val =
        stem447DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem385_dcount c
    · cases hv
    · exact stem386_dcount c
    · exact stem387_dcount c
    · exact stem388_dcount c
    · cases hv
    · exact stem389_dcount c
    · cases hv
    · exact stem390_dcount c
    · cases hv
    · exact stem391_dcount c
    · exact stem392_dcount c
  rw [degCount_of_flags leaders 2 6 [6] stem447Flags stem447DCounts
    stem447_flags hc b]
  fin_cases b <;> decide +kernel

def stem448Deg (b : Fin 5) : ℕ := [0, 29, 13, 0, 0].getD b.val 0

def stem448DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem393Deg,
    stem394Deg,
    stem395Deg,
    fun _ => 0,
    stem396Deg,
    fun _ => 0,
    stem397Deg,
    fun _ => 0,
    stem398Deg,
    stem399Deg].getD v.val (fun _ => 0)

theorem stem448_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 7 [7]) b.val = stem448Deg b := by
  have hc : ∀ v, stem448Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([7] ++ [v])) c.val =
        stem448DCounts v c := by
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
    · exact stem393_dcount c
    · exact stem394_dcount c
    · exact stem395_dcount c
    · cases hv
    · exact stem396_dcount c
    · cases hv
    · exact stem397_dcount c
    · cases hv
    · exact stem398_dcount c
    · exact stem399_dcount c
  rw [degCount_of_flags leaders 2 7 [7] stem448Flags stem448DCounts
    stem448_flags hc b]
  fin_cases b <;> decide +kernel

def stem449Deg (b : Fin 5) : ℕ := [35, 21, 0, 0, 0].getD b.val 0

def stem449DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem400Deg,
    fun _ => 0,
    stem401Deg,
    stem402Deg,
    stem403Deg,
    stem404Deg,
    stem405Deg,
    fun _ => 0,
    stem406Deg,
    stem407Deg].getD v.val (fun _ => 0)

theorem stem449_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 8 [8]) b.val = stem449Deg b := by
  have hc : ∀ v, stem449Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([8] ++ [v])) c.val =
        stem449DCounts v c := by
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
    · exact stem400_dcount c
    · cases hv
    · exact stem401_dcount c
    · exact stem402_dcount c
    · exact stem403_dcount c
    · exact stem404_dcount c
    · exact stem405_dcount c
    · cases hv
    · exact stem406_dcount c
    · exact stem407_dcount c
  rw [degCount_of_flags leaders 2 8 [8] stem449Flags stem449DCounts
    stem449_flags hc b]
  fin_cases b <;> decide +kernel

def stem450Deg (b : Fin 5) : ℕ := [0, 25, 15, 0, 0].getD b.val 0

def stem450DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem408Deg,
    stem409Deg,
    stem410Deg,
    stem411Deg,
    stem412Deg,
    fun _ => 0,
    stem413Deg,
    stem414Deg].getD v.val (fun _ => 0)

theorem stem450_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 9 [9]) b.val = stem450Deg b := by
  have hc : ∀ v, stem450Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([9] ++ [v])) c.val =
        stem450DCounts v c := by
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
    · exact stem408_dcount c
    · exact stem409_dcount c
    · exact stem410_dcount c
    · exact stem411_dcount c
    · exact stem412_dcount c
    · cases hv
    · exact stem413_dcount c
    · exact stem414_dcount c
  rw [degCount_of_flags leaders 2 9 [9] stem450Flags stem450DCounts
    stem450_flags hc b]
  fin_cases b <;> decide +kernel

def stem451Deg (b : Fin 5) : ℕ := [20, 10, 0, 0, 0].getD b.val 0

def stem451DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem415Deg,
    fun _ => 0,
    stem416Deg,
    stem417Deg,
    stem418Deg,
    fun _ => 0,
    stem419Deg,
    stem420Deg].getD v.val (fun _ => 0)

theorem stem451_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 10 [10]) b.val = stem451Deg b := by
  have hc : ∀ v, stem451Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([10] ++ [v])) c.val =
        stem451DCounts v c := by
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
    · exact stem415_dcount c
    · cases hv
    · exact stem416_dcount c
    · exact stem417_dcount c
    · exact stem418_dcount c
    · cases hv
    · exact stem419_dcount c
    · exact stem420_dcount c
  rw [degCount_of_flags leaders 2 10 [10] stem451Flags stem451DCounts
    stem451_flags hc b]
  fin_cases b <;> decide +kernel

def stem452Deg (b : Fin 5) : ℕ := [0, 14, 7, 0, 0].getD b.val 0

def stem452DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem421Deg,
    stem422Deg,
    stem423Deg,
    fun _ => 0,
    stem424Deg,
    stem425Deg].getD v.val (fun _ => 0)

theorem stem452_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 11 [11]) b.val = stem452Deg b := by
  have hc : ∀ v, stem452Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([11] ++ [v])) c.val =
        stem452DCounts v c := by
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
    · exact stem421_dcount c
    · exact stem422_dcount c
    · exact stem423_dcount c
    · cases hv
    · exact stem424_dcount c
    · exact stem425_dcount c
  rw [degCount_of_flags leaders 2 11 [11] stem452Flags stem452DCounts
    stem452_flags hc b]
  fin_cases b <;> decide +kernel

def stem453Deg (b : Fin 5) : ℕ := [10, 4, 0, 0, 0].getD b.val 0

def stem453DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem426Deg,
    fun _ => 0,
    stem427Deg,
    fun _ => 0,
    stem428Deg,
    stem429Deg].getD v.val (fun _ => 0)

theorem stem453_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 12 [12]) b.val = stem453Deg b := by
  have hc : ∀ v, stem453Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([12] ++ [v])) c.val =
        stem453DCounts v c := by
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
    · exact stem426_dcount c
    · cases hv
    · exact stem427_dcount c
    · cases hv
    · exact stem428_dcount c
    · exact stem429_dcount c
  rw [degCount_of_flags leaders 2 12 [12] stem453Flags stem453DCounts
    stem453_flags hc b]
  fin_cases b <;> decide +kernel

def stem454Deg (b : Fin 5) : ℕ := [0, 7, 3, 0, 0].getD b.val 0

def stem454DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem430Deg,
    fun _ => 0,
    stem431Deg,
    stem432Deg].getD v.val (fun _ => 0)

theorem stem454_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 13 [13]) b.val = stem454Deg b := by
  have hc : ∀ v, stem454Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([13] ++ [v])) c.val =
        stem454DCounts v c := by
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
    · exact stem430_dcount c
    · cases hv
    · exact stem431_dcount c
    · exact stem432_dcount c
  rw [degCount_of_flags leaders 2 13 [13] stem454Flags stem454DCounts
    stem454_flags hc b]
  fin_cases b <;> decide +kernel

def stem455Deg (b : Fin 5) : ℕ := [7, 3, 0, 0, 0].getD b.val 0

def stem455DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem433Deg,
    fun _ => 0,
    stem434Deg,
    stem435Deg].getD v.val (fun _ => 0)

theorem stem455_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 14 [14]) b.val = stem455Deg b := by
  have hc : ∀ v, stem455Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([14] ++ [v])) c.val =
        stem455DCounts v c := by
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
    · exact stem433_dcount c
    · cases hv
    · exact stem434_dcount c
    · exact stem435_dcount c
  rw [degCount_of_flags leaders 2 14 [14] stem455Flags stem455DCounts
    stem455_flags hc b]
  fin_cases b <;> decide +kernel

def stem456Deg (b : Fin 5) : ℕ := [0, 4, 2, 0, 0].getD b.val 0

def stem456DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem436Deg,
    stem437Deg].getD v.val (fun _ => 0)

theorem stem456_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 15 [15]) b.val = stem456Deg b := by
  have hc : ∀ v, stem456Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([15] ++ [v])) c.val =
        stem456DCounts v c := by
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
    · exact stem436_dcount c
    · exact stem437_dcount c
  rw [degCount_of_flags leaders 2 15 [15] stem456Flags stem456DCounts
    stem456_flags hc b]
  fin_cases b <;> decide +kernel

def stem457Deg (b : Fin 5) : ℕ := [4, 2, 0, 0, 0].getD b.val 0

def stem457DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem438Deg,
    stem439Deg].getD v.val (fun _ => 0)

theorem stem457_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 16 [16]) b.val = stem457Deg b := by
  have hc : ∀ v, stem457Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([16] ++ [v])) c.val =
        stem457DCounts v c := by
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
    · exact stem438_dcount c
    · exact stem439_dcount c
  rw [degCount_of_flags leaders 2 16 [16] stem457Flags stem457DCounts
    stem457_flags hc b]
  fin_cases b <;> decide +kernel

def stem458Deg (b : Fin 5) : ℕ := [0, 1, 1, 0, 0].getD b.val 0

def stem458DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem440Deg].getD v.val (fun _ => 0)

theorem stem458_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 3 17 [17]) b.val = stem458Deg b := by
  have hc : ∀ v, stem458Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 2 v.val ([17] ++ [v])) c.val =
        stem458DCounts v c := by
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
    · exact stem440_dcount c
  rw [degCount_of_flags leaders 2 17 [17] stem458Flags stem458DCounts
    stem458_flags hc b]
  fin_cases b <;> decide +kernel

def stem459Deg (b : Fin 5) : ℕ := [300, 378, 106, 0, 0].getD b.val 0

def stem459DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [stem441Deg,
    stem442Deg,
    stem443Deg,
    stem444Deg,
    stem445Deg,
    stem446Deg,
    stem447Deg,
    stem448Deg,
    stem449Deg,
    stem450Deg,
    stem451Deg,
    stem452Deg,
    stem453Deg,
    stem454Deg,
    stem455Deg,
    stem456Deg,
    stem457Deg,
    stem458Deg].getD v.val (fun _ => 0)

theorem stem459_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 4 0 []) b.val = stem459Deg b := by
  have hc : ∀ v, stem459Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 3 v.val ([] ++ [v])) c.val =
        stem459DCounts v c := by
    intro v hv c
    fin_cases v
    · exact stem441_dcount c
    · exact stem442_dcount c
    · exact stem443_dcount c
    · exact stem444_dcount c
    · exact stem445_dcount c
    · exact stem446_dcount c
    · exact stem447_dcount c
    · exact stem448_dcount c
    · exact stem449_dcount c
    · exact stem450_dcount c
    · exact stem451_dcount c
    · exact stem452_dcount c
    · exact stem453_dcount c
    · exact stem454_dcount c
    · exact stem455_dcount c
    · exact stem456_dcount c
    · exact stem457_dcount c
    · exact stem458_dcount c
  rw [degCount_of_flags leaders 3 0 [] stem459Flags stem459DCounts
    stem459_flags hc b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem459_dcount
