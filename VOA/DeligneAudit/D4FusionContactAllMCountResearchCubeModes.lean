import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeCommute

/-! Arbitrary current-mode cube lowerings commute on the whole truncated
polynomial ring, including both truncation boundaries. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section
variable (K : Type*) [CommRing K]

abbrev ModePoly (m : ℕ) := MvPolynomial (Fin 8 × Fin m) K

def shiftedX (m : ℕ) (i : Fin 8) (r : ℕ) : ModePoly K m :=
  if hr : r < m then MvPolynomial.X (i,⟨r,hr⟩) else 0

def stepMode (m : ℕ) (t : Option (Fin 8)) (r : ℕ) : ModePoly K m :=
  match t with
  | none => 0
  | some i => shiftedX K m i r

def shiftedLower (m : ℕ) (d : Fin 3) (k : ℕ) :
    Derivation K (ModePoly K m) (ModePoly K m) :=
  MvPolynomial.mkDerivation K (fun x => stepMode K m (orderNext d x.1) (k+x.2.val))

theorem shiftedLower_X (m : ℕ) (d : Fin 3) (k : ℕ) (x : Fin 8 × Fin m) :
    shiftedLower K m d k (MvPolynomial.X x) =
      stepMode K m (orderNext d x.1) (k+x.2.val) :=
  MvPolynomial.mkDerivation_X K _ _

theorem stepMode_high (m : ℕ) (t : Option (Fin 8)) (r : ℕ) (hr : m ≤ r) :
    stepMode K m t r = 0 := by
  cases t <;> simp [stepMode,shiftedX,Nat.not_lt.mpr hr]

theorem shiftedLower_mode (m : ℕ) (d : Fin 3) (k : ℕ) (i : Fin 8) (r : ℕ) :
    shiftedLower K m d k (shiftedX K m i r) =
      stepMode K m (orderNext d i) (k+r) := by
  by_cases hr : r < m
  · rw [shiftedX,dif_pos hr,shiftedLower_X]
  · rw [shiftedX,dif_neg hr,map_zero]
    exact (stepMode_high K m _ _ (by omega)).symm

theorem shiftedLower_step (m : ℕ) (d : Fin 3) (k : ℕ)
    (t : Option (Fin 8)) (r : ℕ) :
    shiftedLower K m d k (stepMode K m t r) =
      stepMode K m (t.bind (orderNext d)) (k+r) := by
  cases t with
  | none => exact map_zero _
  | some i => exact shiftedLower_mode K m d k i r

/-- All modes commute, before any projection or coefficient reduction. -/
theorem shiftedLower_commute (m : ℕ) (d e : Fin 3) (k l : ℕ) :
    Function.Commute (shiftedLower K m d k : ModePoly K m → ModePoly K m)
      (shiftedLower K m e l : ModePoly K m → ModePoly K m) := by
  have hz : ⁅shiftedLower K m d k,shiftedLower K m e l⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro x
    change shiftedLower K m d k (shiftedLower K m e l (MvPolynomial.X x)) -
      shiftedLower K m e l (shiftedLower K m d k (MvPolynomial.X x)) = 0
    rw [shiftedLower_X,shiftedLower_X,shiftedLower_step,shiftedLower_step,
      orderNext_commute,show k+(l+x.2.val) = l+(k+x.2.val) by omega,sub_self]
  intro p
  apply sub_eq_zero.mp
  change ⁅shiftedLower K m d k,shiftedLower K m e l⁆ p = 0
  rw [hz]
  rfl

theorem shiftedLower_high (m : ℕ) (d : Fin 3) (k : ℕ) (hk : m ≤ k) :
    shiftedLower K m d k = 0 := by
  apply MvPolynomial.derivation_ext
  intro x
  rw [shiftedLower_X,stepMode_high K m _ _ (by omega)]
  rfl

end
#print axioms shiftedLower_commute
#print axioms shiftedLower_high
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
