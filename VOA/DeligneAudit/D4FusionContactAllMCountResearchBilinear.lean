import VOA.DeligneAudit.D4FusionContactAllMCountResearchColorCoefficient
import VOA.DeligneAudit.D4FusionContactAllMCountResearchMixedCartan

/-! # The checked quadratic color orbits lie in the bilinear source span -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

def bilinearSpan : Submodule ℂ (MvPolynomial (Vars 2) ℂ) :=
  Submodule.span ℂ (Set.range fun x : Fin 9 × Fin 9 =>
    MvPolynomial.X (x.1,0) * MvPolynomial.X (x.2,1))

theorem bilinear_product_mem (i j : Fin 9) :
    MvPolynomial.X (i,0) * MvPolynomial.X (j,1) ∈ bilinearSpan :=
  Submodule.subset_span ⟨(i,j),rfl⟩

theorem bilinear_constant_deriv (g : Fin 10) {p : MvPolynomial (Vars 2) ℂ}
    (hp : p ∈ bilinearSpan) : g0Deriv 2 g 0 p ∈ bilinearSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hp
      rw [(g0Deriv 2 g 0).leibniz]
      simp only [smul_eq_mul,g0Deriv_X_constant,Finset.mul_sum,mul_smul_comm]
      apply bilinearSpan.add_mem
      · apply bilinearSpan.sum_mem
        intro k _
        exact bilinearSpan.smul_mem _ (bilinear_product_mem i k)
      · apply bilinearSpan.sum_mem
        intro k _
        have hh := bilinearSpan.smul_mem
          (contactF (zeroIndex g) (radIndex i) (radIndex k)) (bilinear_product_mem k j)
        simpa only [mul_comm] using hh
  | zero => rw [map_zero]; exact bilinearSpan.zero_mem
  | add p q _ _ ihp ihq => simpa only [map_add] using bilinearSpan.add_mem ihp ihq
  | smul a p _ ih => simpa only [Derivation.map_smul] using bilinearSpan.smul_mem a ih

theorem checked_levi_bilinear (l : List (Fin 3)) :
    twoEvalMap (leviOrbit l .base).toWheel twoSeed ∈ bilinearSpan := by
  induction l with
  | nil => exact bilinear_product_mem 0 0
  | cons i l ih =>
      change twoEvalMap (.deriv (leviIndex i) (leviOrbit l .base).toWheel) twoSeed ∈ _
      rw [twoEvalMap_levi_step]
      exact bilinear_constant_deriv (leviCurrent i) ih

/-- The actual diagonal Cartan action restricted to the lower source mode. -/
def lowerH : Derivation ℂ (MvPolynomial (Vars 2) ℂ) (MvPolynomial (Vars 2) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun x =>
    if x.2=0 then (h0Weight x.1 : ℂ) • MvPolynomial.X x else 0

def swapModes : Vars 2 → Vars 2 := fun x => (x.1,if x.2=0 then 1 else 0)

def swapModesAlg : MvPolynomial (Vars 2) ℂ →ₐ[ℂ] MvPolynomial (Vars 2) ℂ :=
  MvPolynomial.rename swapModes

/-- The universal finite-color boundary operator. Its factor 1/2 comes
from the whole grouped seed, including repeated middle-mode terms. -/
def middleBoundaryMap : Module.End ℂ (MvPolynomial (Vars 2) ℂ) :=
  (1/2:ℂ) • ((g0Deriv 2 0 0).toLinearMap - (2:ℂ) • lowerH.toLinearMap +
    swapModesAlg.toLinearMap.comp (g0Deriv 2 0 0).toLinearMap)

variable {m : ℕ} (b : BoundaryPair m)

def nearestPair : BoundaryPair m where
  lower := ⟨b.top.val-1,by have := b.top.isLt; omega⟩
  top := b.top
  lt := by change b.top.val-1 < b.top.val; have := b.lt; omega
  last := b.last

def coefficientCurrentMap (s : ℕ) :
    MvPolynomial (Vars 2) ℂ →ₗ[ℂ] MvPolynomial (Vars m) ℂ :=
  ((PowerSeries.coeff s).restrictScalars ℂ).comp (colorCurrentAlg m).toLinearMap

def groupedErrorMap : MvPolynomial (Vars 2) ℂ →ₗ[ℂ] MvPolynomial (Vars m) ℂ :=
  (1/2:ℂ) • coefficientCurrentMap (m := m) (b.lower.val+b.top.val) -
    (MvPolynomial.rename b.embed).toLinearMap

theorem groupedErrorMap_apply (p : MvPolynomial (Vars 2) ℂ) :
    groupedErrorMap b p = (1/2:ℂ) • PowerSeries.coeff (b.lower.val+b.top.val)
      (colorCurrentAlg m p) - MvPolynomial.rename b.embed p := rfl

/-- Exact whole-coefficient interpretation of every checked middle orbit. -/
theorem leviOrbit_middle_error (l : List (Fin 3)) :
    evalMap b (leviOrbit l .base).toWheel (middleSeed b) =
      groupedErrorMap b (twoEvalMap (leviOrbit l .base).toWheel twoSeed) := by
  rw [middleSeed,map_sub,leviOrbit_grouped_coefficient,evalMap_transport]
  rfl

end

#print axioms checked_levi_bilinear
#print axioms leviOrbit_middle_error

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
