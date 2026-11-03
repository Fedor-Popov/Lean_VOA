import VOA.DeligneAudit.D4FusionContactCurrentCutoff
import VOA.DeligneAudit.D4FusionContactCurrentPermutation
import VOA.DeligneAudit.D4FusionContactCurrentNormalForm

/-!
# Actual all-m contact words have length at most 2m

The normal-word cutoff and source-free permutation identities supply
all radical words, then prefix action propagates the reduction to every
length. This is a spanning bound, not the sharp count 28^m.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem localWeyl_currentWord_cutoff (h : LocalWeylRelG D4sector R w m)
    (l : List CurrentLetter) (hl : l.length = 2 * m + 1) :
    currentRadicalWord R l w ∈ currentPiece R w (2 * m) := by
  obtain ⟨a,n,c,hp,hperm⟩ := exists_current_normal_form l
  have hlen := current_normal_form_length hperm
  have hsize : a.length + n + c.length = 2 * m + 1 := by omega
  have hN := localWeyl_currentNormal_cutoff h a n c hp hsize
  rw [currentNormal_eq_word] at hN
  have hperm' : l.Perm (currentNormalList a n c) := by
    simpa only [currentNormalList, List.append_assoc] using hperm
  have hdiff := currentRadicalWord_perm_sub R w hperm'
  have hdiff' : currentRadicalWord R l w -
      currentRadicalWord R (currentNormalList a n c) w ∈ currentPiece R w (2 * m) :=
    currentPiece_mono R w (by omega) hdiff
  have hh := (currentPiece R w (2 * m)).add_mem hdiff' hN
  convert hh using 1; abel

theorem localWeyl_currentPiece_step (h : LocalWeylRelG D4sector R w m) :
    currentPiece R w (2 * m + 1) ≤ currentPiece R w (2 * m) := by
  rw [currentPiece, Submodule.span_le]
  rintro _ ⟨l,hl,rfl⟩
  by_cases hs : l.length ≤ 2 * m
  · exact currentRadicalWord_mem R w l hs
  · exact localWeyl_currentWord_cutoff h l (by omega)

theorem localWeyl_currentPiece_invariant (h : LocalWeylRelG D4sector R w m)
    (i : Fin 9) (r : ℕ) {v : V} (hv : v ∈ currentPiece R w (2 * m)) :
    R.op (radIndex i) r v ∈ currentPiece R w (2 * m) :=
  localWeyl_currentPiece_step h (current_radical_mem R w i r hv)

/-- Every actual contact word, with arbitrary current modes, reduces
to length at most 2m. No source finiteness or polynomial count premise. -/
theorem localWeyl_currentWord_bound (h : LocalWeylRelG D4sector R w m)
    (l : List CurrentLetter) : currentRadicalWord R l w ∈ currentPiece R w (2 * m) := by
  induction l with
  | nil => exact current_generator_mem R w (2 * m)
  | cons x l ih => exact localWeyl_currentPiece_invariant h x.1 x.2 ih

theorem localWeyl_currentPiece_bound (h : LocalWeylRelG D4sector R w m) (d : ℕ) :
    currentPiece R w d ≤ currentPiece R w (2 * m) := by
  rw [currentPiece, Submodule.span_le]
  rintro _ ⟨l,_,rfl⟩
  exact localWeyl_currentWord_bound h l

private theorem current_word_indices : ∀ (l : List (Fin 28 × ℕ)),
    (∀ x ∈ l, active x.1) → ∃ t : List CurrentLetter,
      l = t.map (fun x => (radIndex x.1,x.2))
  | [], _ => ⟨[], rfl⟩
  | (c,r)::l, ha => by
      obtain ⟨i,hi⟩ := (active_iff_index c).mp (ha (c,r) (by simp))
      obtain ⟨t,ht⟩ := current_word_indices l (fun x hx => ha x (by simp [hx]))
      exact ⟨(i,r)::t, by simp only [List.map_cons, ← hi, ← ht]⟩

/-- Every actual homogeneous current-degree piece lies in the bounded
contact-length span. This does not provide the sharp all-m count. -/
theorem localWeyl_cycDeg_currentPiece (h : LocalWeylRelG D4sector R w m) (d : ℕ) :
    cycDeg R w d ≤ currentPiece R w (2 * m) := by
  apply (localWeyl_cycDeg_contact h d).trans
  rw [Submodule.span_le]
  rintro _ ⟨l,_,ha,_,rfl⟩
  obtain ⟨t,rfl⟩ := current_word_indices l ha
  exact localWeyl_currentWord_bound h t

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_currentWord_bound
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_currentPiece_bound
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_cycDeg_currentPiece
