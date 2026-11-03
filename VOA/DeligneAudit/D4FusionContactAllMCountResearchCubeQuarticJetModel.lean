import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCurrent
import Mathlib.RingTheory.PowerSeries.Derivative

/-! An infinite polynomial jet model with exact whole-series evaluation.
No top jet is truncated, so derivation intertwining holds globally. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

abbrev JetVar := Fin 8 × ℕ
abbrev JetRing := MvPolynomial JetVar ℂ

def jetRaise : Derivation ℂ JetRing JetRing :=
  MvPolynomial.mkDerivation ℂ (fun x => MvPolynomial.X (x.1,x.2+1))

theorem jetRaise_X (x : JetVar) : jetRaise (MvPolynomial.X x) = MvPolynomial.X (x.1,x.2+1) :=
  MvPolynomial.mkDerivation_X ℂ _ _

def jetBase : P8 ℂ →ₐ[ℂ] JetRing := MvPolynomial.rename (fun i => (i,0))

theorem jetBase_X (i : Fin 8) : jetBase (MvPolynomial.X i) = MvPolynomial.X (i,0) :=
  MvPolynomial.rename_X _ _

/-- Natural jet ids use eight colors per derivative order. -/
def jetVarNat (n : ℕ) : JetRing := MvPolynomial.X (⟨n%8,by omega⟩,n/8)

theorem jetRaise_jetVarNat (n : ℕ) : jetRaise (jetVarNat n) = jetVarNat (n+8) := by
  rw [jetVarNat,jetRaise_X]
  unfold jetVarNat
  congr 1
  apply Prod.ext
  · apply Fin.ext
    change n%8 = (n+8)%8
    omega
  · change n/8+1 = (n+8)/8
    omega

theorem jetVarNat_base (i : Fin 8) : jetVarNat i.val = jetBase (MvPolynomial.X i) := by
  rw [jetBase_X]
  unfold jetVarNat
  congr 1
  apply Prod.ext
  · apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  · exact Nat.div_eq_of_lt i.isLt

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def seriesJetDerivation : Derivation ℂ (PowerSeries A) (PowerSeries A) :=
  (PowerSeries.derivative A).restrictScalars ℂ

def jetEvaluate (v : Fin 8 → PowerSeries A) : JetRing →ₐ[ℂ] PowerSeries A :=
  MvPolynomial.aeval (fun x =>
    ((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[x.2]) (v x.1))

theorem jetEvaluate_X (v : Fin 8 → PowerSeries A) (x : JetVar) :
    jetEvaluate v (MvPolynomial.X x) =
      ((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[x.2]) (v x.1) :=
  MvPolynomial.aeval_X _ _

theorem jetEvaluate_jetVarNat (v : Fin 8 → PowerSeries A) (n : ℕ) :
    jetEvaluate v (jetVarNat n) =
      ((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[n/8])
        (v ⟨n%8,by omega⟩) := jetEvaluate_X v _

/-- Every polynomial jet, not only a bounded jet image, intertwines. -/
theorem jetEvaluate_raise (v : Fin 8 → PowerSeries A) (p : JetRing) :
    jetEvaluate v (jetRaise p) = PowerSeries.derivative A (jetEvaluate v p) := by
  apply map_derivation_to (jetEvaluate v) jetRaise seriesJetDerivation
  intro x
  rw [jetRaise_X,jetEvaluate_X,jetEvaluate_X]
  change ((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[x.2+1]) (v x.1) =
    PowerSeries.derivative A
      (((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[x.2]) (v x.1))
  exact Function.iterate_succ_apply' _ _ _

theorem jetEvaluate_iterate (v : Fin 8 → PowerSeries A) (p : JetRing) (a : ℕ) :
    jetEvaluate v (((jetRaise : JetRing → JetRing)^[a]) p) =
      ((PowerSeries.derivative A : PowerSeries A → PowerSeries A)^[a]) (jetEvaluate v p) := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [Function.iterate_succ_apply',jetEvaluate_raise,ih,Function.iterate_succ_apply']

theorem jetEvaluate_base (v : Fin 8 → PowerSeries A) :
    (jetEvaluate v).comp jetBase = MvPolynomial.aeval v := by
  apply MvPolynomial.algHom_ext
  intro i
  change jetEvaluate v (jetBase (MvPolynomial.X i)) = _
  rw [jetBase_X,jetEvaluate_X]
  exact (MvPolynomial.aeval_X v i).symm

def currentJetEvaluate (m : ℕ) : JetRing →ₐ[ℂ] PowerSeries (MvPolynomial (Vars m) ℂ) :=
  jetEvaluate (actualCurrent m)

theorem currentJetEvaluate_base (m : ℕ) (p : P8 ℂ) :
    currentJetEvaluate m (jetBase p) = currentMap m p := by
  exact AlgHom.congr_fun (jetEvaluate_base (actualCurrent m)) p

/-- Exact transfer of every whole ordinary derivative of every color polynomial. -/
theorem currentJetEvaluate_iterate_base (m a : ℕ) (p : P8 ℂ) :
    currentJetEvaluate m (((jetRaise : JetRing → JetRing)^[a]) (jetBase p)) =
      ((PowerSeries.derivative (MvPolynomial (Vars m) ℂ) : _ → _)^[a]) (currentMap m p) := by
  rw [currentJetEvaluate,jetEvaluate_iterate]
  rw [← currentJetEvaluate_base m p]
  rfl

end
#print axioms jetRaise_jetVarNat
#print axioms jetEvaluate_raise
#print axioms currentJetEvaluate_iterate_base
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
