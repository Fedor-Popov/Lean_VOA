import VOA.DeligneAudit.D4FusionContactPolynomialIntertwiner
import VOA.DeligneAudit.D4FusionContactPolynomialDerivationAction

/-!
# Finite current derivations preserve the actual full annihilator

Direct current-mode variables use the actual source high-mode zero.
The graded operator commutators therefore give the entire polynomial
intertwiner, including every polynomial multiplier.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def modeX (m : ℕ) (i : Fin 9) (r : ℕ) : MvPolynomial (Vars m) ℂ :=
  if hr : r < m then MvPolynomial.X (i, ⟨r,hr⟩) else 0

def g0Image (m : ℕ) (g : Fin 10) (k : ℕ) (x : Vars m) : MvPolynomial (Vars m) ℂ :=
  ∑ j : Fin 9, contactF (zeroIndex g) (radIndex x.1) (radIndex j) • modeX m j (k+x.2.val)

def eImage (m : ℕ) (i : Fin 8) (k : ℕ) (x : Vars m) : MvPolynomial (Vars m) ℂ :=
  if x.1 = 8 then modeX m i.castSucc (k+x.2.val) else 0

def g0Deriv (m : ℕ) (g : Fin 10) (k : ℕ) :
    Derivation ℂ (MvPolynomial (Vars m) ℂ) (MvPolynomial (Vars m) ℂ) :=
  MvPolynomial.mkDerivation ℂ (g0Image m g k)

def eDeriv (m : ℕ) (i : Fin 8) (k : ℕ) :
    Derivation ℂ (MvPolynomial (Vars m) ℂ) (MvPolynomial (Vars m) ℂ) :=
  MvPolynomial.mkDerivation ℂ (eImage m i k)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem polyAlg_modeX
    (hhigh : ∀ i r, m ≤ r → R.op (radIndex i) r w = 0) (i : Fin 9) (r : ℕ) :
    polyAlg R w (modeLetter m) (modeX m i r) = grOp R w i r := by
  by_cases hr : r < m
  · rw [modeX, dif_pos hr, polyAlg_X]
    rfl
  · rw [modeX, dif_neg hr, map_zero, grOp_zero_of_source_zero R w i r (hhigh i r (by omega))]

theorem polyAlg_g0Deriv_X
    (hhigh : ∀ i r, m ≤ r → R.op (radIndex i) r w = 0)
    (g : Fin 10) (k : ℕ) (x : Vars m) :
    polyAlg R w (modeLetter m) (g0Deriv m g k (MvPolynomial.X x)) =
      ∑ j : Fin 9, contactF (zeroIndex g) (radIndex x.1) (radIndex j) •
        grOp R w j (k+x.2.val) := by
  simp only [g0Deriv, MvPolynomial.mkDerivation_X, g0Image, map_sum, map_smul,
    polyAlg_modeX hhigh]

theorem polyAlg_eDeriv_X
    (hhigh : ∀ i r, m ≤ r → R.op (radIndex i) r w = 0)
    (i : Fin 8) (k : ℕ) (x : Vars m) :
    polyAlg R w (modeLetter m) (eDeriv m i k (MvPolynomial.X x)) =
      if x.1 = 8 then grOp R w i.castSucc (k+x.2.val) else 0 := by
  by_cases hx : x.1 = 8
  · simp only [eDeriv, MvPolynomial.mkDerivation_X, eImage, if_pos hx, polyAlg_modeX hhigh]
  · simp only [eDeriv, MvPolynomial.mkDerivation_X, eImage, if_neg hx, map_zero]

variable {R : CurrentModule D4sector.f V}

theorem source_g0_ann_closed (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (g : Fin 10) (k : ℕ) :
    ∀ p ∈ annIdeal R w (modeLetter m), g0Deriv m g k p ∈ annIdeal R w (modeLetter m) := by
  have hw := highestRel_of_localWeyl h
  have hh : ∀ i r, m ≤ r → R.op (radIndex i) r w = 0 :=
    fun i r hr => localWeyl_high_kills hm h (radIndex i) r hr
  obtain ⟨a,ha⟩ := g0Gr_generator_eigen hw g k
  apply annIdeal_derivation_closed R w (modeLetter m) (g0Deriv m g k) (g0Gr hw g k) a ha
  intro x
  rw [polyAlg_g0Deriv_X hh]
  exact g0Gr_comm hw g x.1 k x.2.val

theorem source_e_ann_closed (hm : 1 ≤ m) (h : LocalWeylRelG D4sector R w m)
    (i : Fin 8) (k : ℕ) :
    ∀ p ∈ annIdeal R w (modeLetter m), eDeriv m i k p ∈ annIdeal R w (modeLetter m) := by
  have hw := highestRel_of_localWeyl h
  have hh : ∀ j r, m ≤ r → R.op (radIndex j) r w = 0 :=
    fun j r hr => localWeyl_high_kills hm h (radIndex j) r hr
  apply annIdeal_derivation_closed R w (modeLetter m) (eDeriv m i k) (eGr hw i k) 0
  · simpa only [zero_smul] using eGr_generator_zero hw i k
  · intro x
    rw [polyAlg_eDeriv_X hh]
    exact eGr_comm hw i x.1 k x.2.val

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_g0_ann_closed
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_e_ann_closed
