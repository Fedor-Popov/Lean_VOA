import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleDerivation
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeMaps
import Mathlib.RingTheory.PowerSeries.Basic

/-! Single-color current models: positive currents kill the original seeds,
Cartan currents preserve their image, and negative currents kill C's image. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section

def positive (e : Fin 3) : Fin 18 := ⟨4+e.val,by omega⟩
def negative (d : Fin 3) : Fin 18 := ⟨7+d.val,by omega⟩
def cartan (h : Fin 4) : Fin 18 := ⟨h.val,by omega⟩
def sourceColor (b : Bool) : Fin 9 := if b then 8 else 0

theorem positive_coeff : ∀ (e : Fin 3) (b : Bool), coeff (positive e) (sourceColor b) = 0 := by
  decide +kernel

theorem negative_center_coeff : ∀ d : Fin 3, coeff (negative d) 8 = 0 := by decide +kernel

theorem cartan_source : ∀ (h : Fin 4) (b : Bool),
    coeff (cartan h) (sourceColor b) = 0 ∨ target (cartan h) (sourceColor b) = sourceColor b := by
  decide +kernel

variable (K : Type*) [CommRing K]
abbrev MonoRing (m : ℕ) := MvPolynomial (Fin m) K

def monoMode (m r : ℕ) : MonoRing K m :=
  if hr : r < m then MvPolynomial.X ⟨r,hr⟩ else 0

def monoShift (m k : ℕ) : Derivation K (MonoRing K m) (MonoRing K m) :=
  MvPolynomial.mkDerivation K (fun i => monoMode K m (k+i.val))

def monoMap (m : ℕ) (c : Fin 9) : MonoRing K m →ₐ[K] Ring K m :=
  MvPolynomial.aeval (fun i => mode K m c i.val)

theorem monoMap_X (m : ℕ) (c : Fin 9) (i : Fin m) :
    monoMap K m c (MvPolynomial.X i) = mode K m c i.val := MvPolynomial.aeval_X _ _

theorem monoMap_mode (m : ℕ) (c : Fin 9) (r : ℕ) :
    monoMap K m c (monoMode K m r) = mode K m c r := by
  by_cases hr : r < m
  · simp only [monoMode,dif_pos hr,monoMap_X]
  · simp only [monoMode,mode,dif_neg hr,map_zero]

theorem positive_mono (m : ℕ) (e : Fin 3) (b : Bool) (k : ℕ) (p : MonoRing K m) :
    deriv K m (positive e) k (monoMap K m (sourceColor b) p) = 0 := by
  have h := Cube.map_derivation (monoMap K m (sourceColor b))
    (0 : Derivation K (MonoRing K m) (MonoRing K m)) (deriv K m (positive e) k)
    (fun i => ?_) p
  · simpa only [Derivation.zero_apply,map_zero] using h.symm
  · rw [Derivation.zero_apply,map_zero,monoMap_X,deriv_mode,positive_coeff,zero_zsmul]

theorem negative_center_mono (m : ℕ) (d : Fin 3) (k : ℕ) (p : MonoRing K m) :
    deriv K m (negative d) k (monoMap K m 8 p) = 0 := by
  have h := Cube.map_derivation (monoMap K m 8)
    (0 : Derivation K (MonoRing K m) (MonoRing K m)) (deriv K m (negative d) k)
    (fun i => ?_) p
  · simpa only [Derivation.zero_apply,map_zero] using h.symm
  · rw [Derivation.zero_apply,map_zero,monoMap_X,deriv_mode,negative_center_coeff,zero_zsmul]

theorem cartan_mono (m : ℕ) (h : Fin 4) (b : Bool) (k : ℕ) (p : MonoRing K m) :
    deriv K m (cartan h) k (monoMap K m (sourceColor b) p) =
      coeff (cartan h) (sourceColor b) •
        monoMap K m (sourceColor b) (monoShift K m k p) := by
  have hc := Cube.map_derivation (monoMap K m (sourceColor b))
    (coeff (cartan h) (sourceColor b) • monoShift K m k) (deriv K m (cartan h) k)
    (fun i => ?_) p
  · simpa only [map_zsmul,Derivation.smul_apply] using hc.symm
  · rw [Derivation.smul_apply,map_zsmul,
      show monoShift K m k (MvPolynomial.X i) = monoMode K m (k+i.val) from
        MvPolynomial.mkDerivation_X K _ _,monoMap_mode,monoMap_X,deriv_mode]
    rcases cartan_source h b with hz | ht
    · rw [hz,zero_zsmul,zero_zsmul]
    · rw [ht]

def monoCurrent (m : ℕ) : PowerSeries (MonoRing K m) := PowerSeries.mk (monoMode K m)
def colorCurrent (m : ℕ) (c : Fin 9) : PowerSeries (Ring K m) := PowerSeries.mk (mode K m c)

theorem monoCurrent_map (m : ℕ) (c : Fin 9) :
    PowerSeries.map (monoMap K m c).toRingHom (monoCurrent K m) = colorCurrent K m c := by
  apply PowerSeries.ext
  intro s
  simp only [PowerSeries.coeff_map,monoCurrent,colorCurrent,PowerSeries.coeff_mk]
  change monoMap K m c (monoMode K m s) = mode K m c s
  exact monoMap_mode K m c s

theorem monoMap_seed (m : ℕ) (c : Fin 9) (r s : ℕ) :
    monoMap K m c (PowerSeries.coeff s (monoCurrent K m^r)) =
      PowerSeries.coeff s (colorCurrent K m c^r) := by
  change (monoMap K m c).toRingHom (PowerSeries.coeff s (monoCurrent K m^r)) = _
  rw [← PowerSeries.coeff_map,map_pow,monoCurrent_map]

theorem positive_seed (m : ℕ) (e : Fin 3) (b : Bool) (k r s : ℕ) :
    deriv K m (positive e) k (PowerSeries.coeff s (colorCurrent K m (sourceColor b)^r)) = 0 := by
  rw [← monoMap_seed]
  exact positive_mono K m e b k _

end
#print axioms positive_seed
#print axioms cartan_mono
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
