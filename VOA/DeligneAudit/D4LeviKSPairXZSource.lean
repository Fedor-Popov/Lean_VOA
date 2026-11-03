import VOA.DeligneAudit.D4LeviKSPairUFactorial
import VOA.DeligneAudit.D4LeviKSPairUnconditional

/-! Strict key height of the XZ source in the PAIR transfer. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

def xModeWord (rs : List ℕ) : List (Fin 6 × ℕ) :=
  rs.map fun r => (1, r)

/-- An XZ source lies strictly above a symmetric target with at least one Y. -/
theorem xzSource_key_higher (m a b c d : ℕ)
    (xs zs : List ℕ) (hx : xs.length = a + b)
    (hz : zs.length = c) (hb : 0 < b) :
    keyLess m (pairFinalKey a b c d)
      (wordKey (xModeWord xs ++ zModeWord zs)) := by
  left
  simp [pairFinalKey, keyHeight, wordKey, xModeWord, zModeWord,
    List.countP_append, List.countP_map, Function.comp_def]
  omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- An XZ word is in the prefix of the matching symmetric key. -/
theorem xzSource_prefix
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d)
    (xs zs : List ℕ) (hx : xs.length = a + b)
    (hz : zs.length = c) (hb : 0 < b) :
    radicalWord ρ w (xModeWord xs ++ zModeWord zs) ∈
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  apply keyOrbit_le_higher ρ w m (pairFinalKey a b c d)
    (wordKey (xModeWord xs ++ zModeWord zs))
  · exact xzSource_key_higher m a b c d xs zs hx hz hb
  · exact keyLayer_le_orbit ρ w _
      (radicalWord_mem_key ρ w (xModeWord xs ++ zModeWord zs))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xzSource_key_higher
#print axioms VOA.DeligneAudit.D4Levi.xzSource_prefix
