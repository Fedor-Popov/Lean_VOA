import VOA.DeligneAudit.D4FusionContactCurrentNormal

/-!
# The mixed all-current contact cutoff in ordered normal form

Two finite inductions use actual raising-current identities: first the
number of A letters, then the number of positive-mode C factors. The
center-only input is discharged by the actual highest-root E-calculus.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V} {m : ℕ}

theorem currentNormal_cutoff_of_center (h : HighestRel R w m) (D : ℕ)
    (hcenter : ∀ l : List ℕ, D ≤ l.length → ECalc.Fw (currentCenter R) l w = 0)
    (a : List ACurrentLetter) (n : ℕ) (c : List ℕ)
    (hp : ∀ j ∈ c, 0 < j) (hsize : a.length+n+c.length = D) :
    currentNormal R a n c w ∈ currentPiece R w (D-1) := by
  have main : ∀ ac : ℕ, ∀ a : List ACurrentLetter, ∀ n : ℕ, ∀ c : List ℕ,
      a.length = ac → (∀ j ∈ c, 0 < j) → a.length+n+c.length = D →
      currentNormal R a n c w ∈ currentPiece R w (D-1) := by
    intro ac
    induction ac using Nat.strong_induction_on with
    | h ac ihA =>
      intro a n c ha hp hs
      rcases List.eq_nil_or_concat' a with rfl | ⟨b,x,rfl⟩
      · change (currentCenter R 0 ^ n) (ECalc.Fw (currentCenter R) c w) ∈ _
        have hlen : D ≤ (List.replicate n 0 ++ c).length := by
          simp only [List.length_append, List.length_replicate]
          simp only [List.length_nil, Nat.zero_add] at hs
          omega
        rw [center_pow_word_eq, hcenter _ hlen]
        exact Submodule.zero_mem _
      · have hb : b.length < ac := by
          simp only [List.length_append, List.length_singleton] at ha
          omega
        have inner : ∀ z : ℕ, ∀ x : ACurrentLetter, ∀ n : ℕ, ∀ c : List ℕ,
            c.length = z → (∀ j ∈ c, 0 < j) → b.length+1+n+c.length = D →
            currentNormal R (b++[x]) n c w ∈ currentPiece R w (D-1) := by
          intro z
          induction z using Nat.strong_induction_on with
          | h z ihZ =>
            intro x n c hc hp hs
            have hN : currentNormal R b (n+1) c w ∈ currentPiece R w (D-1) :=
              ihA b.length hb b (n+1) c rfl hp (by omega)
            have hEN := current_raise_mem h x.1 x.2 hN
            have hv := current_center_pow_mem R w (n+1) (current_center_word_mem R w c)
            have hcomm := current_raise_AWord_mem h x.1 x.2 b hv
            have hcomm' : currentRaise R x.1 x.2 (currentNormal R b (n+1) c w) -
                currentAWord R b (currentRaise R x.1 x.2
                  ((currentCenter R 0 ^ (n+1)) (ECalc.Fw (currentCenter R) c w))) ∈
                currentPiece R w (D-1) :=
              currentPiece_mono R w (by omega) hcomm
            have hExtract : currentAWord R b (currentRaise R x.1 x.2
                ((currentCenter R 0 ^ (n+1)) (ECalc.Fw (currentCenter R) c w))) ∈
                currentPiece R w (D-1) := by
              have hh := (currentPiece R w (D-1)).sub_mem hEN hcomm'
              convert hh using 1; abel
            have hmap : positiveCenterDerivedSpan R w x.1 c.length ≤
                (currentPiece R w (D-1)).comap
                  (currentAWord R b * currentCenter R 0 ^ (n+1)) := by
              rw [positiveCenterDerivedSpan, Submodule.span_le]
              rintro _ ⟨s, c', hlen, hp', rfl⟩
              change currentAWord R b ((currentCenter R 0 ^ (n+1))
                (currentRoot R x.1 s (ECalc.Fw (currentCenter R) c' w))) ∈
                  currentPiece R w (D-1)
              have he : (currentCenter R 0 ^ (n+1))
                  (currentRoot R x.1 s (ECalc.Fw (currentCenter R) c' w)) =
                  currentRoot R x.1 s ((currentCenter R 0 ^ (n+1))
                    (ECalc.Fw (currentCenter R) c' w)) :=
                congrArg (fun T : Module.End ℂ V => T (ECalc.Fw (currentCenter R) c' w))
                  ((Commute.pow_left (current_center_root_comm R x.1 0 s) (n+1)).eq)
              rw [he, ← currentNormal_append R b (x.1,s) (n+1) c' w]
              exact ihZ c'.length (by omega) (x.1,s) (n+1) c' rfl hp' (by omega)
            have hTail := hmap (raise_positive_center_span h x.1 x.2 c hp)
            change currentAWord R b ((currentCenter R 0 ^ (n+1))
              (currentRaise R x.1 x.2 (ECalc.Fw (currentCenter R) c w))) ∈
                currentPiece R w (D-1) at hTail
            rw [current_raise_center0_pow_apply, map_add, map_nsmul] at hExtract
            have hscalar : (n+1) • currentNormal R (b++[x]) n c w ∈
                currentPiece R w (D-1) := by
              simpa only [add_sub_cancel_right, ← currentNormal_append] using
                (currentPiece R w (D-1)).sub_mem hExtract hTail
            rw [← Nat.cast_smul_eq_nsmul ℂ] at hscalar
            exact (Submodule.smul_mem_iff _
              (by exact_mod_cast Nat.succ_ne_zero n : ((n+1 : ℕ) : ℂ) ≠ 0)).mp hscalar
        apply inner c.length x n c rfl hp
        simpa only [List.length_append, List.length_singleton] using hs
  exact main a.length a n c rfl hp hsize

open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

variable {R : CurrentModule D4sector.f V}

/-- Actual source-only ordered mixed-current cutoff, for every m. -/
theorem localWeyl_currentNormal_cutoff (h : LocalWeylRelG D4sector R w m)
    (a : List ACurrentLetter) (n : ℕ) (c : List ℕ)
    (hp : ∀ j ∈ c, 0 < j) (hsize : a.length + n + c.length = 2 * m + 1) :
    currentNormal R a n c w ∈ currentPiece R w (2 * m) := by
  have hh := currentNormal_cutoff_of_center (highestRel_of_localWeyl h) (2 * m + 1)
    (localWeyl_current_center_word_zero h) a n c hp hsize
  simpa only [Nat.add_sub_cancel] using hh

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.currentNormal_cutoff_of_center

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_currentNormal_cutoff
