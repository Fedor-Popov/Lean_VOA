import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeTopShiftWords
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticModeWords

/-! Mixed highest-color shift words and actual negative-current words on quartic
U sources reduce to an exact static polar modulo the literal quadratic/cubic ideal. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Actual negative-current words preserve natural scalar multiples. -/
theorem negativeModeWord_nsmul (m : ℕ) (l : List (Fin 3 × ℕ)) (n : ℕ)
    (p : MvPolynomial (Vars m) ℂ) :
    negativeModeWord m l (n • p) = n • negativeModeWord m l p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change g0Deriv m (cubeDirection x.1) x.2 (negativeModeWord m l (n • p)) = _
      rw [ih,map_nsmul]
      rfl

private theorem source_difference_trans (m : ℕ) {p q r : MvPolynomial (Vars m) ℂ}
    (hp : p - q ∈ quadraticCubicPolarIdeal m)
    (hq : q - r ∈ quadraticCubicPolarIdeal m) :
    p - r ∈ quadraticCubicPolarIdeal m := by
  have he : p - r = (p - q) + (q - r) := by ring
  rw [he]
  exact (quadraticCubicPolarIdeal m).add_mem hp hq

/-- Every mixed quartic U source is congruent to a scalar multiple of one original
static whole polar. No C-source reduction or dimension assertion is included. -/
theorem quartic_shift_negativeModeWord_static_mem_polarIdeal
    (m s : ℕ) (ks : List ℕ) (l : List (Fin 3 × ℕ)) (hs : m < 4 + s) :
    negativeModeWord m l
        (topMap m (topShiftWord m ks (PowerSeries.coeff s (topCurrent m ^ 4)))) -
      (4 ^ ks.length) • PowerSeries.coeff (s + ks.sum + (l.map Prod.snd).sum)
        (currentMap m (orbit ℂ 4 (negativeModeAxisCount 0 l)
          (negativeModeAxisCount 1 l) (negativeModeAxisCount 2 l))) ∈
      quadraticCubicPolarIdeal m := by
  have hshift := topMap_topQuadraticCubicIdeal_mem m
    (topShiftWord_quartic_static_mem_topIdeal m s ks hs)
  rw [map_sub,map_nsmul,topMap_seed] at hshift
  have hnegative := negativeModeWord_congr_polarIdeal m l hshift
  rw [negativeModeWord_nsmul] at hnegative
  have hstatic := quartic_negativeModeWord_static_mem_polarIdeal m (s + ks.sum)
    0 0 0 l (by omega)
  have hzero : currentMap m (orbit ℂ 4 0 0 0) = AllM.current m 0 ^ 4 := by
    rw [currentMap_orbit]
    rfl
  simp only [hzero,Nat.zero_add] at hstatic
  have hscaled := (quadraticCubicPolarIdeal m).nsmul_mem hstatic (4 ^ ks.length)
  rw [nsmul_sub] at hscaled
  exact source_difference_trans m hnegative hscaled

end
#print axioms negativeModeWord_nsmul
#print axioms quartic_shift_negativeModeWord_static_mem_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
