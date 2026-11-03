import VOA.DeligneAudit.D4FusionContactCurrentWords
import VOA.DeligneAudit.D4FusionContactCurrentCenterTail
import VOA.DeligneAudit.D4FusionContactCurrentCenter

/-! # Current contact normal words used by the mixed cutoff induction -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def currentNormal (a : List ACurrentLetter) (n : ℕ) (c : List ℕ) (w : V) : V :=
  currentAWord R a ((currentCenter R 0 ^ n) (ECalc.Fw (currentCenter R) c w))

theorem currentAWord_append (a b : List ACurrentLetter) :
    currentAWord R (a++b) = currentAWord R a * currentAWord R b := by
  induction a with
  | nil => simp only [List.nil_append, currentAWord, one_mul]
  | cons x a ih => simp only [List.cons_append, currentAWord, ih, mul_assoc]

theorem currentNormal_append (a : List ACurrentLetter) (x : ACurrentLetter)
    (n : ℕ) (c : List ℕ) (w : V) :
    currentNormal R (a++[x]) n c w =
      currentAWord R a (currentRoot R x.1 x.2
        ((currentCenter R 0 ^ n) (ECalc.Fw (currentCenter R) c w))) := by
  simp only [currentNormal, currentAWord_append, currentAWord, mul_one, Module.End.mul_apply]

theorem current_center_word_eq (l : List ℕ) (v : V) :
    ECalc.Fw (currentCenter R) l v =
      currentRadicalWord R (l.map fun r => ((8 : Fin 9),r)) v := by
  induction l with
  | nil => rfl
  | cons r l ih =>
      change currentCenter R r (ECalc.Fw (currentCenter R) l v) =
        currentCenter R r (currentRadicalWord R (l.map fun r => ((8 : Fin 9),r)) v)
      exact congrArg (currentCenter R r) ih

theorem current_center_word_mem (w : V) (l : List ℕ) :
    ECalc.Fw (currentCenter R) l w ∈ currentPiece R w l.length := by
  rw [current_center_word_eq]
  exact currentRadicalWord_mem R w _ (by simp)

theorem current_center_pow_mem (w : V) (n : ℕ) {d : ℕ} {v : V}
    (hv : v ∈ currentPiece R w d) :
    (currentCenter R 0 ^ n) v ∈ currentPiece R w (n+d) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.zero_add] using hv
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact currentPiece_mono R w (by omega) (current_radical_mem R w 8 0 ih)

theorem currentNormal_mem (w : V) (a : List ACurrentLetter) (n : ℕ) (c : List ℕ) :
    currentNormal R a n c w ∈ currentPiece R w (a.length+n+c.length) := by
  exact currentPiece_mono R w (by omega)
    (currentAWord_mem R w a (current_center_pow_mem R w n (current_center_word_mem R w c)))

theorem center_pow_word_eq (n : ℕ) (c : List ℕ) (w : V) :
    (currentCenter R 0 ^ n) (ECalc.Fw (currentCenter R) c w) =
      ECalc.Fw (currentCenter R) (List.replicate n 0 ++ c) w := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, List.replicate_zero, List.nil_append]
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, List.replicate_succ,
        List.cons_append, ECalc.Fw]

def currentNormalList (a : List ACurrentLetter) (n : ℕ) (c : List ℕ) :
    List CurrentLetter :=
  a.map (fun x => (x.1.castSucc, x.2)) ++
    (List.replicate n ((8 : Fin 9), 0) ++ c.map (fun r => ((8 : Fin 9), r)))

private theorem currentNormal_radicalWord_append (a b : List CurrentLetter) (v : V) :
    currentRadicalWord R (a++b) v = currentRadicalWord R a (currentRadicalWord R b v) := by
  induction a with
  | nil => rfl
  | cons x a ih =>
      change R.op (radIndex x.1) x.2 (currentRadicalWord R (a++b) v) =
        R.op (radIndex x.1) x.2 (currentRadicalWord R a (currentRadicalWord R b v))
      exact congrArg (R.op (radIndex x.1) x.2) ih

theorem currentNormal_eq_word (a : List ACurrentLetter) (n : ℕ) (c : List ℕ) (w : V) :
    currentNormal R a n c w = currentRadicalWord R (currentNormalList a n c) w := by
  rw [currentNormal, currentAWord_eq, center_pow_word_eq, current_center_word_eq,
    ← currentNormal_radicalWord_append]
  simp only [List.map_append, List.map_replicate, currentNormalList]

end
end VOA.DeligneAudit.D4FusionContact
