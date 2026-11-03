import VOA.DeligneAudit.D4FusionContactAllMCountResearchMiddleSeed

/-! # Strict convex energy of the middle-mode correction

The span records total degree four, current degree 2(p+q), and strict
energy below 2(p²+q²). Its membership statements concern actual
polynomials and actual source expressions, with no counting premise.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open BoundaryPair

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

def currentDegree (l : List (Vars m)) : ℕ := (l.map fun x => x.2.val).sum

def currentEnergy (l : List (Vars m)) : ℕ := (l.map fun x => x.2.val ^ 2).sum

abbrev LowEnergyWord := {l : List (Vars m) // l.length = 4 ∧
  currentDegree l = 2*(b.lower.val+b.top.val) ∧
  currentEnergy l < 2*(b.lower.val^2+b.top.val^2)}

def energySpan : Submodule ℂ (MvPolynomial (Vars m) ℂ) :=
  Submodule.span ℂ (Set.range fun l : LowEnergyWord b => polyWord l.val)

/-- Strict convexity, in the precise integer region used by convolution. -/
theorem middle_energy (z : MiddlePair b) :
    z.left.2.val^2 + z.right.2.val^2 < b.lower.val^2+b.top.val^2 := by
  have hp := z.left_lower
  have hq := z.left_upper
  have hs := z.mode_sum
  have h0 : 0 < z.left.2.val-b.lower.val := Nat.sub_pos_of_lt hp
  have h1 : 0 < b.top.val-z.left.2.val := Nat.sub_pos_of_lt hq
  have hprod := Nat.mul_pos h0 h1
  have ha := Nat.sub_add_cancel (Nat.le_of_lt hp)
  have hc := Nat.sub_add_cancel (Nat.le_of_lt hq)
  nlinarith

theorem endpoint_middle_product_mem (i j : Fin 9) (z : MiddlePair b) :
    MvPolynomial.X (i,b.lower) * MvPolynomial.X (j,b.top) *
      (MvPolynomial.X z.left * MvPolynomial.X z.right) ∈ energySpan b := by
  let l : List (Vars m) := [(i,b.lower),(j,b.top),z.left,z.right]
  have hl : l.length = 4 ∧ currentDegree l = 2*(b.lower.val+b.top.val) ∧
      currentEnergy l < 2*(b.lower.val^2+b.top.val^2) := by
    refine ⟨rfl,?_,?_⟩
    · simp only [currentDegree,l,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have := z.mode_sum
      omega
    · simp only [currentEnergy,l,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      have := middle_energy b z
      omega
  have hh := (Submodule.subset_span (R := ℂ)
    (s := Set.range fun w : LowEnergyWord b => polyWord w.val) ⟨⟨l,hl⟩,rfl⟩)
  simpa only [energySpan,l,polyWord,List.map_cons,List.map_nil,List.prod_cons,
    List.prod_nil,mul_one,mul_assoc] using hh

theorem endpoint_middle_mem (i j : Fin 9) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ middleSpan b) :
    MvPolynomial.X (i,b.lower) * MvPolynomial.X (j,b.top) * p ∈ energySpan b := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨z,rfl⟩ := hp
      exact endpoint_middle_product_mem b i j z
  | zero => simp only [mul_zero]; exact (energySpan b).zero_mem
  | add p q _ _ ihp ihq =>
      simpa only [mul_add] using (energySpan b).add_mem ihp ihq
  | smul a p _ ih =>
      simpa only [mul_smul_comm] using (energySpan b).smul_mem a ih

def leviCurrent : Fin 3 → Fin 10 := ![7,8,9]

theorem evalMap_levi_step (i : Fin 3) (e : IntegerExpr) (p : MvPolynomial (Vars m) ℂ) :
    evalMap b (.deriv (leviIndex i) e.toWheel) p =
      g0Deriv m (leviCurrent i) 0 (evalMap b e.toWheel p) := by
  fin_cases i <;>
    simp [evalMap,leviIndex,leviCurrent,derivationIndex,BoundaryPair.mapDeriv,
      BoundaryPair.shift,Polynomial.AllM.candidateDeriv]

theorem evalMap_levi_middle (l : List (Fin 3)) (e : IntegerExpr)
    (p : MvPolynomial (Vars m) ℂ) (hp : evalMap b e.toWheel p ∈ middleSpan b) :
    evalMap b (leviOrbit l e).toWheel p ∈ middleSpan b := by
  induction l with
  | nil => exact hp
  | cons i l ih =>
      change evalMap b (.deriv (leviIndex i) (leviOrbit l e).toWheel) p ∈ _
      rw [evalMap_levi_step]
      exact g0Deriv_middle b (leviCurrent i) ih

theorem evalMap_square_middle_zero :
    evalMap b (IntegerExpr.deriv 3 .base).toWheel (middleSeed b) = 0 := by
  change g0Deriv m 1 (b.top.val-b.lower.val) (middleSeed b) = 0
  exact g0Deriv_middle_zero b 1 (middleSeed_mem b)

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.middle_energy
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.endpoint_middle_mem
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.evalMap_square_middle_zero
