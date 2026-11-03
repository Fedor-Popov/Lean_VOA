import VOA.DeligneAudit.D4LeviKSLemma0Four

/-! The f₄ derivation on arbitrary radical words. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The only nonzero f₄ brackets are X to minus U and U' to minus Y. -/
theorem fFour_radical_comm (j : Fin 6) (r s : ℕ) :
    ρ.op (16 : Fin 28) r * ρ.op (radicalColour j) s -
      ρ.op (radicalColour j) s * ρ.op (16 : Fin 28) r =
        if j = 1 then -ρ.op (24 : Fin 28) (r + s)
        else if j = 3 then -ρ.op (26 : Fin 28) (r + s) else 0 := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [ρ.comm (16 : Fin 28) (radicalColour j) r s v]
  change (∑ c : Fin 28,
    fD4 (lowerColour 1) (radicalColour j) c • ρ.op c (r + s) v) = _
  simp_rw [lower_coefficient 1 j]
  fin_cases j <;> simp [lowerAction, radicalColour]

noncomputable def fFourLetter (r : ℕ) (p : Fin 6 × ℕ) : Module.End ℂ V :=
  if p.1 = 1 then -ρ.op (24 : Fin 28) (r + p.2)
  else if p.1 = 3 then -ρ.op (26 : Fin 28) (r + p.2) else 0

noncomputable def fFourDerivative (r : ℕ) :
    List (Fin 6 × ℕ) → V → V
  | [], _ => 0
  | p :: l, v =>
      (fFourLetter ρ r p)
        (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v) +
      ρ.op (radicalColour p.1) p.2 (fFourDerivative r l v)

theorem fFour_word (r : ℕ) (l : List (Fin 6 × ℕ)) (v : V) :
    ρ.op (16 : Fin 28) r
      (wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) v) =
    wordOp ρ (l.map fun p => (radicalColour p.1, p.2))
      (ρ.op (16 : Fin 28) r v) + fFourDerivative ρ r l v := by
  induction l with
  | nil => simp [fFourDerivative, wordOp]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      have hc := congrArg (fun T : Module.End ℂ V =>
        T (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v))
        (fFour_radical_comm ρ j r s)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hletter :
          (if j = 1 then -ρ.op (24 : Fin 28) (r + s)
            else if j = 3 then -ρ.op (26 : Fin 28) (r + s) else 0) =
          fFourLetter ρ r (j, s) := rfl
      rw [hletter] at hc
      simp only [List.map_cons, wordOp, fFourDerivative]
      have happly : ρ.op (16 : Fin 28) r
          (ρ.op (radicalColour j) s
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v)) =
        ρ.op (radicalColour j) s
          (ρ.op (16 : Fin 28) r
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v)) +
        fFourLetter ρ r (j, s)
          (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v) := by
        rw [← hc]
        abel
      rw [happly, ih, map_add]
      abel

theorem fFour_radicalWord
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (l : List (Fin 6 × ℕ)) :
    ρ.op (16 : Fin 28) r (radicalWord ρ w l) =
      fFourDerivative ρ r l w := by
  have hz (q : List (Fin 6 × ℕ)) :
      wordOp ρ (q.map fun p => (radicalColour p.1, p.2)) (0 : V) = 0 := by
    induction q with
    | nil => rfl
    | cons p q ih =>
        simp only [List.map_cons, wordOp, ih, map_zero]
  have hword := fFour_word ρ r l w
  rw [fFour_source_mode_zero ρ w m h r, hz l, zero_add] at hword
  exact hword

/-- An f₄ derivative of a higher key remains in its full Levi orbit. -/
theorem fFour_derivative_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : keyLess m k (wordKey l)) :
    fFourDerivative ρ r l w ∈ higherOrbit ρ w m k := by
  have hword : radicalWord ρ w l ∈ higherOrbit ρ w m k :=
    keyOrbit_le_higher ρ w m k (wordKey l) hl
      (keyLayer_le_orbit ρ w (wordKey l) (radicalWord_mem_key ρ w l))
  have hf := higherOrbit_full_levi_inv ρ w m k (16 : Fin 28)
    ⟨12, rfl⟩ r hword
  change ρ.op (16 : Fin 28) r (radicalWord ρ w l) ∈
    higherOrbit ρ w m k at hf
  rw [fFour_radicalWord ρ w m h r l] at hf
  exact hf

/-- A zero-mode X source isolates U, with a derivative error on its tail. -/
theorem fFour_xzero_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : keyLess m k (wordKey ((1, 0) :: l))) :
    -ρ.op (24 : Fin 28) r (radicalWord ρ w l) +
      ρ.op (22 : Fin 28) 0 (fFourDerivative ρ r l w) ∈
        higherOrbit ρ w m k := by
  have hd := fFour_derivative_higher ρ w m h k r ((1, 0) :: l) hl
  simpa only [fFourDerivative, fFourLetter, radicalWord,
    List.map_cons, wordOp, zero_add, if_true] using hd

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fFour_radical_comm
#print axioms VOA.DeligneAudit.D4Levi.fFour_word
#print axioms VOA.DeligneAudit.D4Levi.fFour_radicalWord
#print axioms VOA.DeligneAudit.D4Levi.fFour_derivative_higher
#print axioms VOA.DeligneAudit.D4Levi.fFour_xzero_higher
