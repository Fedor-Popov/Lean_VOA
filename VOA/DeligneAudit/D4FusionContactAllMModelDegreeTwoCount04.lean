import VOA.DeligneAudit.D4FusionContactAllMModelDegreeTwoCount03
import Mathlib.Tactic.FinCases

/-! Current-degree counts of the m=2 normal-word stems 280..349, reusing the
kernel-checked stem flags of the length cascade (generated certificate). -/
namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

set_option maxRecDepth 100000

def stem280Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem280_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 14, 16]) b.val = stem280Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 14, 16] stem280Flags stem280_flags b]
  fin_cases b <;> decide +kernel

def stem281Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem281_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [9, 14, 17]) b.val = stem281Deg b := by
  rw [degCount_fuel_one leaders 17 [9, 14, 17] stem281Flags stem281_flags b]
  fin_cases b <;> decide +kernel

def stem282Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem282_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [9, 16, 16]) b.val = stem282Deg b := by
  rw [degCount_fuel_one leaders 16 [9, 16, 16] stem282Flags stem282_flags b]
  fin_cases b <;> decide +kernel

def stem283Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem283_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [9, 16, 17]) b.val = stem283Deg b := by
  rw [degCount_fuel_one leaders 17 [9, 16, 17] stem283Flags stem283_flags b]
  fin_cases b <;> decide +kernel

def stem284Deg (b : Fin 5) : ℕ := [3, 0, 0, 0, 0].getD b.val 0

theorem stem284_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [10, 10, 12]) b.val = stem284Deg b := by
  rw [degCount_fuel_one leaders 12 [10, 10, 12] stem284Flags stem284_flags b]
  fin_cases b <;> decide +kernel

def stem285Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem285_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 13 [10, 10, 13]) b.val = stem285Deg b := by
  rw [degCount_fuel_one leaders 13 [10, 10, 13] stem285Flags stem285_flags b]
  fin_cases b <;> decide +kernel

def stem286Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem286_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [10, 10, 16]) b.val = stem286Deg b := by
  rw [degCount_fuel_one leaders 16 [10, 10, 16] stem286Flags stem286_flags b]
  fin_cases b <;> decide +kernel

def stem287Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem287_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [10, 10, 17]) b.val = stem287Deg b := by
  rw [degCount_fuel_one leaders 17 [10, 10, 17] stem287Flags stem287_flags b]
  fin_cases b <;> decide +kernel

def stem288Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem288_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [10, 12, 12]) b.val = stem288Deg b := by
  rw [degCount_fuel_one leaders 12 [10, 12, 12] stem288Flags stem288_flags b]
  fin_cases b <;> decide +kernel

def stem289Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem289_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [10, 12, 14]) b.val = stem289Deg b := by
  rw [degCount_fuel_one leaders 14 [10, 12, 14] stem289Flags stem289_flags b]
  fin_cases b <;> decide +kernel

def stem290Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem290_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [10, 12, 16]) b.val = stem290Deg b := by
  rw [degCount_fuel_one leaders 16 [10, 12, 16] stem290Flags stem290_flags b]
  fin_cases b <;> decide +kernel

def stem291Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem291_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [10, 12, 17]) b.val = stem291Deg b := by
  rw [degCount_fuel_one leaders 17 [10, 12, 17] stem291Flags stem291_flags b]
  fin_cases b <;> decide +kernel

def stem292Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem292_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [10, 13, 16]) b.val = stem292Deg b := by
  rw [degCount_fuel_one leaders 16 [10, 13, 16] stem292Flags stem292_flags b]
  fin_cases b <;> decide +kernel

def stem293Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem293_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [10, 14, 16]) b.val = stem293Deg b := by
  rw [degCount_fuel_one leaders 16 [10, 14, 16] stem293Flags stem293_flags b]
  fin_cases b <;> decide +kernel

def stem294Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem294_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [10, 14, 17]) b.val = stem294Deg b := by
  rw [degCount_fuel_one leaders 17 [10, 14, 17] stem294Flags stem294_flags b]
  fin_cases b <;> decide +kernel

def stem295Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem295_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [10, 16, 16]) b.val = stem295Deg b := by
  rw [degCount_fuel_one leaders 16 [10, 16, 16] stem295Flags stem295_flags b]
  fin_cases b <;> decide +kernel

def stem296Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem296_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [10, 16, 17]) b.val = stem296Deg b := by
  rw [degCount_fuel_one leaders 17 [10, 16, 17] stem296Flags stem296_flags b]
  fin_cases b <;> decide +kernel

def stem297Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem297_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 12 [11, 12, 12]) b.val = stem297Deg b := by
  rw [degCount_fuel_one leaders 12 [11, 12, 12] stem297Flags stem297_flags b]
  fin_cases b <;> decide +kernel

def stem298Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem298_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 14 [11, 12, 14]) b.val = stem298Deg b := by
  rw [degCount_fuel_one leaders 14 [11, 12, 14] stem298Flags stem298_flags b]
  fin_cases b <;> decide +kernel

def stem299Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem299_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [11, 12, 16]) b.val = stem299Deg b := by
  rw [degCount_fuel_one leaders 16 [11, 12, 16] stem299Flags stem299_flags b]
  fin_cases b <;> decide +kernel

def stem300Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem300_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [11, 12, 17]) b.val = stem300Deg b := by
  rw [degCount_fuel_one leaders 17 [11, 12, 17] stem300Flags stem300_flags b]
  fin_cases b <;> decide +kernel

def stem301Deg (b : Fin 5) : ℕ := [0, 0, 2, 0, 0].getD b.val 0

theorem stem301_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [11, 13, 16]) b.val = stem301Deg b := by
  rw [degCount_fuel_one leaders 16 [11, 13, 16] stem301Flags stem301_flags b]
  fin_cases b <;> decide +kernel

def stem302Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem302_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [11, 14, 16]) b.val = stem302Deg b := by
  rw [degCount_fuel_one leaders 16 [11, 14, 16] stem302Flags stem302_flags b]
  fin_cases b <;> decide +kernel

def stem303Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem303_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [11, 14, 17]) b.val = stem303Deg b := by
  rw [degCount_fuel_one leaders 17 [11, 14, 17] stem303Flags stem303_flags b]
  fin_cases b <;> decide +kernel

def stem304Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem304_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [11, 16, 16]) b.val = stem304Deg b := by
  rw [degCount_fuel_one leaders 16 [11, 16, 16] stem304Flags stem304_flags b]
  fin_cases b <;> decide +kernel

def stem305Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem305_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [11, 16, 17]) b.val = stem305Deg b := by
  rw [degCount_fuel_one leaders 17 [11, 16, 17] stem305Flags stem305_flags b]
  fin_cases b <;> decide +kernel

def stem306Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem306_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [12, 12, 16]) b.val = stem306Deg b := by
  rw [degCount_fuel_one leaders 16 [12, 12, 16] stem306Flags stem306_flags b]
  fin_cases b <;> decide +kernel

def stem307Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem307_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [12, 12, 17]) b.val = stem307Deg b := by
  rw [degCount_fuel_one leaders 17 [12, 12, 17] stem307Flags stem307_flags b]
  fin_cases b <;> decide +kernel

def stem308Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem308_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [12, 14, 16]) b.val = stem308Deg b := by
  rw [degCount_fuel_one leaders 16 [12, 14, 16] stem308Flags stem308_flags b]
  fin_cases b <;> decide +kernel

def stem309Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem309_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [12, 14, 17]) b.val = stem309Deg b := by
  rw [degCount_fuel_one leaders 17 [12, 14, 17] stem309Flags stem309_flags b]
  fin_cases b <;> decide +kernel

def stem310Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem310_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [12, 16, 16]) b.val = stem310Deg b := by
  rw [degCount_fuel_one leaders 16 [12, 16, 16] stem310Flags stem310_flags b]
  fin_cases b <;> decide +kernel

def stem311Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem311_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [12, 16, 17]) b.val = stem311Deg b := by
  rw [degCount_fuel_one leaders 17 [12, 16, 17] stem311Flags stem311_flags b]
  fin_cases b <;> decide +kernel

def stem312Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem312_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [13, 14, 16]) b.val = stem312Deg b := by
  rw [degCount_fuel_one leaders 16 [13, 14, 16] stem312Flags stem312_flags b]
  fin_cases b <;> decide +kernel

def stem313Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem313_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [13, 14, 17]) b.val = stem313Deg b := by
  rw [degCount_fuel_one leaders 17 [13, 14, 17] stem313Flags stem313_flags b]
  fin_cases b <;> decide +kernel

def stem314Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem314_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [13, 16, 16]) b.val = stem314Deg b := by
  rw [degCount_fuel_one leaders 16 [13, 16, 16] stem314Flags stem314_flags b]
  fin_cases b <;> decide +kernel

def stem315Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem315_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [13, 16, 17]) b.val = stem315Deg b := by
  rw [degCount_fuel_one leaders 17 [13, 16, 17] stem315Flags stem315_flags b]
  fin_cases b <;> decide +kernel

def stem316Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem316_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [14, 14, 16]) b.val = stem316Deg b := by
  rw [degCount_fuel_one leaders 16 [14, 14, 16] stem316Flags stem316_flags b]
  fin_cases b <;> decide +kernel

def stem317Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem317_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [14, 14, 17]) b.val = stem317Deg b := by
  rw [degCount_fuel_one leaders 17 [14, 14, 17] stem317Flags stem317_flags b]
  fin_cases b <;> decide +kernel

def stem318Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem318_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [14, 16, 16]) b.val = stem318Deg b := by
  rw [degCount_fuel_one leaders 16 [14, 16, 16] stem318Flags stem318_flags b]
  fin_cases b <;> decide +kernel

def stem319Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem319_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [14, 16, 17]) b.val = stem319Deg b := by
  rw [degCount_fuel_one leaders 17 [14, 16, 17] stem319Flags stem319_flags b]
  fin_cases b <;> decide +kernel

def stem320Deg (b : Fin 5) : ℕ := [0, 2, 0, 0, 0].getD b.val 0

theorem stem320_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [15, 16, 16]) b.val = stem320Deg b := by
  rw [degCount_fuel_one leaders 16 [15, 16, 16] stem320Flags stem320_flags b]
  fin_cases b <;> decide +kernel

def stem321Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

theorem stem321_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [15, 16, 17]) b.val = stem321Deg b := by
  rw [degCount_fuel_one leaders 17 [15, 16, 17] stem321Flags stem321_flags b]
  fin_cases b <;> decide +kernel

def stem322Deg (b : Fin 5) : ℕ := [2, 0, 0, 0, 0].getD b.val 0

theorem stem322_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 16 [16, 16, 16]) b.val = stem322Deg b := by
  rw [degCount_fuel_one leaders 16 [16, 16, 16] stem322Flags stem322_flags b]
  fin_cases b <;> decide +kernel

def stem323Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

theorem stem323_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 1 17 [16, 16, 17]) b.val = stem323Deg b := by
  rw [degCount_fuel_one leaders 17 [16, 16, 17] stem323Flags stem323_flags b]
  fin_cases b <;> decide +kernel

def stem324Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem324DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem000Deg,
    stem001Deg].getD v.val (fun _ => 0)

theorem stem324_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 0 [0, 0]) b.val = stem324Deg b := by
  have hc : ∀ v, stem324Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 0] ++ [v])) c.val =
        stem324DCounts v c := by
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
    · exact stem000_dcount c
    · exact stem001_dcount c
  rw [degCount_of_flags leaders 1 0 [0, 0] stem324Flags stem324DCounts
    stem324_flags hc b]
  fin_cases b <;> decide +kernel

def stem325Deg (b : Fin 5) : ℕ := [9, 1, 0, 0, 0].getD b.val 0

def stem325DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem002Deg,
    fun _ => 0,
    stem003Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem004Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem005Deg,
    stem006Deg].getD v.val (fun _ => 0)

theorem stem325_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 2 [0, 2]) b.val = stem325Deg b := by
  have hc : ∀ v, stem325Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 2] ++ [v])) c.val =
        stem325DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem002_dcount c
    · cases hv
    · exact stem003_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem004_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem005_dcount c
    · exact stem006_dcount c
  rw [degCount_of_flags leaders 1 2 [0, 2] stem325Flags stem325DCounts
    stem325_flags hc b]
  fin_cases b <;> decide +kernel

def stem326Deg (b : Fin 5) : ℕ := [7, 1, 0, 0, 0].getD b.val 0

def stem326DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem007Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem008Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem009Deg,
    stem010Deg].getD v.val (fun _ => 0)

theorem stem326_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 4 [0, 4]) b.val = stem326Deg b := by
  have hc : ∀ v, stem326Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 4] ++ [v])) c.val =
        stem326DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem007_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem008_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem009_dcount c
    · exact stem010_dcount c
  rw [degCount_of_flags leaders 1 4 [0, 4] stem326Flags stem326DCounts
    stem326_flags hc b]
  fin_cases b <;> decide +kernel

def stem327Deg (b : Fin 5) : ℕ := [5, 1, 0, 0, 0].getD b.val 0

def stem327DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem011Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem012Deg,
    stem013Deg].getD v.val (fun _ => 0)

theorem stem327_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [0, 6]) b.val = stem327Deg b := by
  have hc : ∀ v, stem327Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 6] ++ [v])) c.val =
        stem327DCounts v c := by
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
    · exact stem011_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem012_dcount c
    · exact stem013_dcount c
  rw [degCount_of_flags leaders 1 6 [0, 6] stem327Flags stem327DCounts
    stem327_flags hc b]
  fin_cases b <;> decide +kernel

def stem328Deg (b : Fin 5) : ℕ := [7, 1, 0, 0, 0].getD b.val 0

def stem328DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem014Deg,
    fun _ => 0,
    stem015Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem016Deg,
    stem017Deg].getD v.val (fun _ => 0)

theorem stem328_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [0, 8]) b.val = stem328Deg b := by
  have hc : ∀ v, stem328Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 8] ++ [v])) c.val =
        stem328DCounts v c := by
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
    · exact stem014_dcount c
    · cases hv
    · exact stem015_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem016_dcount c
    · exact stem017_dcount c
  rw [degCount_of_flags leaders 1 8 [0, 8] stem328Flags stem328DCounts
    stem328_flags hc b]
  fin_cases b <;> decide +kernel

def stem329Deg (b : Fin 5) : ℕ := [5, 1, 0, 0, 0].getD b.val 0

def stem329DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem018Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem019Deg,
    stem020Deg].getD v.val (fun _ => 0)

theorem stem329_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [0, 10]) b.val = stem329Deg b := by
  have hc : ∀ v, stem329Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 10] ++ [v])) c.val =
        stem329DCounts v c := by
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
    · exact stem018_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem019_dcount c
    · exact stem020_dcount c
  rw [degCount_of_flags leaders 1 10 [0, 10] stem329Flags stem329DCounts
    stem329_flags hc b]
  fin_cases b <;> decide +kernel

def stem330Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem330DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem021Deg,
    stem022Deg].getD v.val (fun _ => 0)

theorem stem330_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [0, 12]) b.val = stem330Deg b := by
  have hc : ∀ v, stem330Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 12] ++ [v])) c.val =
        stem330DCounts v c := by
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
    · exact stem021_dcount c
    · exact stem022_dcount c
  rw [degCount_of_flags leaders 1 12 [0, 12] stem330Flags stem330DCounts
    stem330_flags hc b]
  fin_cases b <;> decide +kernel

def stem331Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem331DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem023Deg,
    stem024Deg].getD v.val (fun _ => 0)

theorem stem331_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [0, 14]) b.val = stem331Deg b := by
  have hc : ∀ v, stem331Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 14] ++ [v])) c.val =
        stem331DCounts v c := by
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
    · exact stem023_dcount c
    · exact stem024_dcount c
  rw [degCount_of_flags leaders 1 14 [0, 14] stem331Flags stem331DCounts
    stem331_flags hc b]
  fin_cases b <;> decide +kernel

def stem332Deg (b : Fin 5) : ℕ := [3, 1, 0, 0, 0].getD b.val 0

def stem332DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem025Deg,
    stem026Deg].getD v.val (fun _ => 0)

theorem stem332_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [0, 16]) b.val = stem332Deg b := by
  have hc : ∀ v, stem332Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 16] ++ [v])) c.val =
        stem332DCounts v c := by
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
    · exact stem025_dcount c
    · exact stem026_dcount c
  rw [degCount_of_flags leaders 1 16 [0, 16] stem332Flags stem332DCounts
    stem332_flags hc b]
  fin_cases b <;> decide +kernel

def stem333Deg (b : Fin 5) : ℕ := [0, 1, 0, 0, 0].getD b.val 0

def stem333DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem333_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [0, 17]) b.val = stem333Deg b := by
  have hc : ∀ v, stem333Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([0, 17] ++ [v])) c.val =
        stem333DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [0, 17] stem333Flags stem333DCounts
    stem333_flags hc b]
  fin_cases b <;> decide +kernel

def stem334Deg (b : Fin 5) : ℕ := [0, 9, 1, 0, 0].getD b.val 0

def stem334DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem027Deg,
    fun _ => 0,
    stem028Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem029Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem030Deg,
    stem031Deg].getD v.val (fun _ => 0)

theorem stem334_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 2 [1, 2]) b.val = stem334Deg b := by
  have hc : ∀ v, stem334Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 2] ++ [v])) c.val =
        stem334DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem027_dcount c
    · cases hv
    · exact stem028_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem029_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem030_dcount c
    · exact stem031_dcount c
  rw [degCount_of_flags leaders 1 2 [1, 2] stem334Flags stem334DCounts
    stem334_flags hc b]
  fin_cases b <;> decide +kernel

def stem335Deg (b : Fin 5) : ℕ := [0, 7, 1, 0, 0].getD b.val 0

def stem335DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem032Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem033Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem034Deg,
    stem035Deg].getD v.val (fun _ => 0)

theorem stem335_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 4 [1, 4]) b.val = stem335Deg b := by
  have hc : ∀ v, stem335Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 4] ++ [v])) c.val =
        stem335DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem032_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem033_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem034_dcount c
    · exact stem035_dcount c
  rw [degCount_of_flags leaders 1 4 [1, 4] stem335Flags stem335DCounts
    stem335_flags hc b]
  fin_cases b <;> decide +kernel

def stem336Deg (b : Fin 5) : ℕ := [0, 5, 1, 0, 0].getD b.val 0

def stem336DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem036Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem037Deg,
    stem038Deg].getD v.val (fun _ => 0)

theorem stem336_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [1, 6]) b.val = stem336Deg b := by
  have hc : ∀ v, stem336Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 6] ++ [v])) c.val =
        stem336DCounts v c := by
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
    · exact stem036_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem037_dcount c
    · exact stem038_dcount c
  rw [degCount_of_flags leaders 1 6 [1, 6] stem336Flags stem336DCounts
    stem336_flags hc b]
  fin_cases b <;> decide +kernel

def stem337Deg (b : Fin 5) : ℕ := [0, 7, 1, 0, 0].getD b.val 0

def stem337DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem039Deg,
    fun _ => 0,
    stem040Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem041Deg,
    stem042Deg].getD v.val (fun _ => 0)

theorem stem337_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [1, 8]) b.val = stem337Deg b := by
  have hc : ∀ v, stem337Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 8] ++ [v])) c.val =
        stem337DCounts v c := by
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
    · exact stem039_dcount c
    · cases hv
    · exact stem040_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem041_dcount c
    · exact stem042_dcount c
  rw [degCount_of_flags leaders 1 8 [1, 8] stem337Flags stem337DCounts
    stem337_flags hc b]
  fin_cases b <;> decide +kernel

def stem338Deg (b : Fin 5) : ℕ := [0, 5, 1, 0, 0].getD b.val 0

def stem338DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem043Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem044Deg,
    stem045Deg].getD v.val (fun _ => 0)

theorem stem338_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [1, 10]) b.val = stem338Deg b := by
  have hc : ∀ v, stem338Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 10] ++ [v])) c.val =
        stem338DCounts v c := by
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
    · exact stem043_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem044_dcount c
    · exact stem045_dcount c
  rw [degCount_of_flags leaders 1 10 [1, 10] stem338Flags stem338DCounts
    stem338_flags hc b]
  fin_cases b <;> decide +kernel

def stem339Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem339DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem046Deg,
    stem047Deg].getD v.val (fun _ => 0)

theorem stem339_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 12 [1, 12]) b.val = stem339Deg b := by
  have hc : ∀ v, stem339Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 12] ++ [v])) c.val =
        stem339DCounts v c := by
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
    · exact stem046_dcount c
    · exact stem047_dcount c
  rw [degCount_of_flags leaders 1 12 [1, 12] stem339Flags stem339DCounts
    stem339_flags hc b]
  fin_cases b <;> decide +kernel

def stem340Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem340DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem048Deg,
    stem049Deg].getD v.val (fun _ => 0)

theorem stem340_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 14 [1, 14]) b.val = stem340Deg b := by
  have hc : ∀ v, stem340Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 14] ++ [v])) c.val =
        stem340DCounts v c := by
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
    · exact stem048_dcount c
    · exact stem049_dcount c
  rw [degCount_of_flags leaders 1 14 [1, 14] stem340Flags stem340DCounts
    stem340_flags hc b]
  fin_cases b <;> decide +kernel

def stem341Deg (b : Fin 5) : ℕ := [0, 3, 1, 0, 0].getD b.val 0

def stem341DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem050Deg,
    stem051Deg].getD v.val (fun _ => 0)

theorem stem341_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 16 [1, 16]) b.val = stem341Deg b := by
  have hc : ∀ v, stem341Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 16] ++ [v])) c.val =
        stem341DCounts v c := by
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
    · exact stem050_dcount c
    · exact stem051_dcount c
  rw [degCount_of_flags leaders 1 16 [1, 16] stem341Flags stem341DCounts
    stem341_flags hc b]
  fin_cases b <;> decide +kernel

def stem342Deg (b : Fin 5) : ℕ := [0, 0, 1, 0, 0].getD b.val 0

def stem342DCounts (v : Fin 18) : Fin 5 → ℕ :=
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

theorem stem342_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 17 [1, 17]) b.val = stem342Deg b := by
  have hc : ∀ v, stem342Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([1, 17] ++ [v])) c.val =
        stem342DCounts v c := by
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
  rw [degCount_of_flags leaders 1 17 [1, 17] stem342Flags stem342DCounts
    stem342_flags hc b]
  fin_cases b <;> decide +kernel

def stem343Deg (b : Fin 5) : ℕ := [15, 10, 0, 0, 0].getD b.val 0

def stem343DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem052Deg,
    stem053Deg,
    stem054Deg,
    stem055Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem056Deg,
    stem057Deg,
    fun _ => 0,
    fun _ => 0,
    stem058Deg,
    stem059Deg].getD v.val (fun _ => 0)

theorem stem343_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 2 [2, 2]) b.val = stem343Deg b := by
  have hc : ∀ v, stem343Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 2] ++ [v])) c.val =
        stem343DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem052_dcount c
    · exact stem053_dcount c
    · exact stem054_dcount c
    · exact stem055_dcount c
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem056_dcount c
    · exact stem057_dcount c
    · cases hv
    · cases hv
    · exact stem058_dcount c
    · exact stem059_dcount c
  rw [degCount_of_flags leaders 1 2 [2, 2] stem343Flags stem343DCounts
    stem343_flags hc b]
  fin_cases b <;> decide +kernel

def stem344Deg (b : Fin 5) : ℕ := [25, 3, 0, 0, 0].getD b.val 0

def stem344DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem060Deg,
    fun _ => 0,
    stem061Deg,
    stem062Deg,
    stem063Deg,
    fun _ => 0,
    stem064Deg,
    fun _ => 0,
    stem065Deg,
    fun _ => 0,
    stem066Deg,
    fun _ => 0,
    stem067Deg,
    stem068Deg].getD v.val (fun _ => 0)

theorem stem344_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 4 [2, 4]) b.val = stem344Deg b := by
  have hc : ∀ v, stem344Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 4] ++ [v])) c.val =
        stem344DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem060_dcount c
    · cases hv
    · exact stem061_dcount c
    · exact stem062_dcount c
    · exact stem063_dcount c
    · cases hv
    · exact stem064_dcount c
    · cases hv
    · exact stem065_dcount c
    · cases hv
    · exact stem066_dcount c
    · cases hv
    · exact stem067_dcount c
    · exact stem068_dcount c
  rw [degCount_of_flags leaders 1 4 [2, 4] stem344Flags stem344DCounts
    stem344_flags hc b]
  fin_cases b <;> decide +kernel

def stem345Deg (b : Fin 5) : ℕ := [0, 9, 0, 0, 0].getD b.val 0

def stem345DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem069Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem070Deg,
    fun _ => 0,
    stem071Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem072Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem345_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 5 [2, 5]) b.val = stem345Deg b := by
  have hc : ∀ v, stem345Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 5] ++ [v])) c.val =
        stem345DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem069_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem070_dcount c
    · cases hv
    · exact stem071_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem072_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 5 [2, 5] stem345Flags stem345DCounts
    stem345_flags hc b]
  fin_cases b <;> decide +kernel

def stem346Deg (b : Fin 5) : ℕ := [17, 1, 0, 0, 0].getD b.val 0

def stem346DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem073Deg,
    fun _ => 0,
    stem074Deg,
    fun _ => 0,
    stem075Deg,
    fun _ => 0,
    stem076Deg,
    fun _ => 0,
    stem077Deg,
    fun _ => 0,
    stem078Deg,
    stem079Deg].getD v.val (fun _ => 0)

theorem stem346_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 6 [2, 6]) b.val = stem346Deg b := by
  have hc : ∀ v, stem346Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 6] ++ [v])) c.val =
        stem346DCounts v c := by
    intro v hv c
    fin_cases v
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · cases hv
    · exact stem073_dcount c
    · cases hv
    · exact stem074_dcount c
    · cases hv
    · exact stem075_dcount c
    · cases hv
    · exact stem076_dcount c
    · cases hv
    · exact stem077_dcount c
    · cases hv
    · exact stem078_dcount c
    · exact stem079_dcount c
  rw [degCount_of_flags leaders 1 6 [2, 6] stem346Flags stem346DCounts
    stem346_flags hc b]
  fin_cases b <;> decide +kernel

def stem347Deg (b : Fin 5) : ℕ := [0, 8, 0, 0, 0].getD b.val 0

def stem347DCounts (v : Fin 18) : Fin 5 → ℕ :=
  [fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem080Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem081Deg,
    fun _ => 0,
    fun _ => 0,
    fun _ => 0,
    stem082Deg,
    fun _ => 0].getD v.val (fun _ => 0)

theorem stem347_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 7 [2, 7]) b.val = stem347Deg b := by
  have hc : ∀ v, stem347Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 7] ++ [v])) c.val =
        stem347DCounts v c := by
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
    · exact stem080_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem081_dcount c
    · cases hv
    · cases hv
    · cases hv
    · exact stem082_dcount c
    · cases hv
  rw [degCount_of_flags leaders 1 7 [2, 7] stem347Flags stem347DCounts
    stem347_flags hc b]
  fin_cases b <;> decide +kernel

def stem348Deg (b : Fin 5) : ℕ := [9, 3, 0, 0, 0].getD b.val 0

def stem348DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem083Deg,
    fun _ => 0,
    stem084Deg,
    stem085Deg,
    fun _ => 0,
    fun _ => 0,
    stem086Deg,
    stem087Deg].getD v.val (fun _ => 0)

theorem stem348_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 8 [2, 8]) b.val = stem348Deg b := by
  have hc : ∀ v, stem348Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 8] ++ [v])) c.val =
        stem348DCounts v c := by
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
    · exact stem083_dcount c
    · cases hv
    · exact stem084_dcount c
    · exact stem085_dcount c
    · cases hv
    · cases hv
    · exact stem086_dcount c
    · exact stem087_dcount c
  rw [degCount_of_flags leaders 1 8 [2, 8] stem348Flags stem348DCounts
    stem348_flags hc b]
  fin_cases b <;> decide +kernel

def stem349Deg (b : Fin 5) : ℕ := [6, 3, 0, 0, 0].getD b.val 0

def stem349DCounts (v : Fin 18) : Fin 5 → ℕ :=
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
    stem088Deg,
    stem089Deg,
    fun _ => 0,
    fun _ => 0,
    stem090Deg,
    stem091Deg].getD v.val (fun _ => 0)

theorem stem349_dcount (b : Fin 5) :
    degCount (enumerateFrom leaders 2 10 [2, 10]) b.val = stem349Deg b := by
  have hc : ∀ v, stem349Flags v = true → ∀ c : Fin 5,
      degCount (enumerateFrom leaders 1 v.val ([2, 10] ++ [v])) c.val =
        stem349DCounts v c := by
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
    · exact stem088_dcount c
    · exact stem089_dcount c
    · cases hv
    · cases hv
    · exact stem090_dcount c
    · exact stem091_dcount c
  rw [degCount_of_flags leaders 1 10 [2, 10] stem349Flags stem349DCounts
    stem349_flags hc b]
  fin_cases b <;> decide +kernel

end VOA.DeligneAudit.D4FusionContact.M2Certificate.Count

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Count.stem349_dcount
