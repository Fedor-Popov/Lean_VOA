import VOA.DeligneAudit.D4LeviKSLemma0Start

/-! The f₃ current acts on every radical word by a two-letter derivation. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The only nonzero f₃ brackets are X to minus U' and U to minus Y. -/
theorem fThree_radical_comm (j : Fin 6) (r s : ℕ) :
    ρ.op (17 : Fin 28) r * ρ.op (radicalColour j) s -
      ρ.op (radicalColour j) s * ρ.op (17 : Fin 28) r =
        if j = 1 then -ρ.op (25 : Fin 28) (r + s)
        else if j = 2 then -ρ.op (26 : Fin 28) (r + s) else 0 := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  rw [ρ.comm (17 : Fin 28) (radicalColour j) r s v]
  change (∑ c : Fin 28,
    fD4 (lowerColour 0) (radicalColour j) c • ρ.op c (r + s) v) = _
  simp_rw [lower_coefficient 0 j]
  fin_cases j <;> simp [lowerAction, radicalColour]

/-- The f₃ derivative of one radical letter, including its bracket sign. -/
noncomputable def fThreeLetter (r : ℕ) (p : Fin 6 × ℕ) : Module.End ℂ V :=
  if p.1 = 1 then -ρ.op (25 : Fin 28) (r + p.2)
  else if p.1 = 2 then -ρ.op (26 : Fin 28) (r + p.2) else 0

/-- Leibniz expansion of f₃ on a radical word. -/
noncomputable def fThreeDerivative (r : ℕ) :
    List (Fin 6 × ℕ) → V → V
  | [], _ => 0
  | p :: l, v =>
      (fThreeLetter ρ r p)
        (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v) +
      ρ.op (radicalColour p.1) p.2 (fThreeDerivative r l v)

/-- The exact derivation identity on an arbitrary radical word and vector. -/
theorem fThree_word (r : ℕ) (l : List (Fin 6 × ℕ)) (v : V) :
    ρ.op (17 : Fin 28) r
      (wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) v) =
    wordOp ρ (l.map fun p => (radicalColour p.1, p.2))
      (ρ.op (17 : Fin 28) r v) + fThreeDerivative ρ r l v := by
  induction l with
  | nil => simp [fThreeDerivative, wordOp]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      have hc := congrArg (fun T : Module.End ℂ V =>
        T (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v))
        (fThree_radical_comm ρ j r s)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hletter :
          (if j = 1 then -ρ.op (25 : Fin 28) (r + s)
            else if j = 2 then -ρ.op (26 : Fin 28) (r + s) else 0) =
          fThreeLetter ρ r (j, s) := rfl
      rw [hletter] at hc
      simp only [List.map_cons, wordOp, fThreeDerivative]
      have happly : ρ.op (17 : Fin 28) r
          (ρ.op (radicalColour j) s
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v)) =
        ρ.op (radicalColour j) s
          (ρ.op (17 : Fin 28) r
            (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v)) +
        fThreeLetter ρ r (j, s)
          (wordOp ρ (l.map fun q => (radicalColour q.1, q.2)) v) := by
        rw [← hc]
        abel
      rw [happly, ih, map_add]
      abel

/-- Since f₃ kills the source, its image on a radical word is the derivative. -/
theorem fThree_radicalWord
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (l : List (Fin 6 × ℕ)) :
    ρ.op (17 : Fin 28) r (radicalWord ρ w l) =
      fThreeDerivative ρ r l w := by
  have hz (q : List (Fin 6 × ℕ)) :
      wordOp ρ (q.map fun p => (radicalColour p.1, p.2)) (0 : V) = 0 := by
    induction q with
    | nil => rfl
    | cons p q ih =>
        simp only [List.map_cons, wordOp, ih, map_zero]
  have hword := fThree_word ρ r l w
  rw [fThree_source_mode_zero ρ w m h r, hz l, zero_add] at hword
  exact hword

/-- Every f₃ derivative from a strictly higher key vanishes in the key quotient. -/
theorem fThree_derivative_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : keyLess m k (wordKey l)) :
    fThreeDerivative ρ r l w ∈ higherOrbit ρ w m k := by
  have hword : radicalWord ρ w l ∈ higherOrbit ρ w m k :=
    keyOrbit_le_higher ρ w m k (wordKey l) hl
      (keyLayer_le_orbit ρ w (wordKey l) (radicalWord_mem_key ρ w l))
  have hf := higherOrbit_full_levi_inv ρ w m k (17 : Fin 28)
    ⟨7, rfl⟩ r hword
  change ρ.op (17 : Fin 28) r (radicalWord ρ w l) ∈
    higherOrbit ρ w m k at hf
  rw [fThree_radicalWord ρ w m h r l] at hf
  exact hf

/-- Polarization from a zero-mode X: the U' term equals its residual derivative
modulo any key below the source word. -/
theorem fThree_xzero_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ) (l : List (Fin 6 × ℕ))
    (hl : keyLess m k (wordKey ((1, 0) :: l))) :
    -ρ.op (25 : Fin 28) r (radicalWord ρ w l) +
      ρ.op (22 : Fin 28) 0 (fThreeDerivative ρ r l w) ∈
        higherOrbit ρ w m k := by
  have hd := fThree_derivative_higher ρ w m h k r ((1, 0) :: l) hl
  simpa only [fThreeDerivative, fThreeLetter, radicalWord,
    List.map_cons, wordOp, zero_add, if_true] using hd

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.fThree_radical_comm
#print axioms VOA.DeligneAudit.D4Levi.fThree_word
#print axioms VOA.DeligneAudit.D4Levi.fThree_radicalWord
#print axioms VOA.DeligneAudit.D4Levi.fThree_derivative_higher
#print axioms VOA.DeligneAudit.D4Levi.fThree_xzero_higher
