import VOA.DeligneAudit.D4FusionContactCurrentPolarization

/-! # Exact current polarization of positive-mode center tails -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

def positiveCenterDerivedSpan (i : Fin 8) (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ r : ℕ, ∃ l : List ℕ,
    l.length + 1 = n ∧ (∀ j ∈ l, 0 < j) ∧
      v = currentRoot R i r (ECalc.Fw (currentCenter R) l w)}

theorem center_positiveDerived_mem (i : Fin 8) (r : ℕ) (hr : 0 < r)
    {n : ℕ} {v : V} (hv : v ∈ positiveCenterDerivedSpan R w i n) :
    currentCenter R r v ∈ positiveCenterDerivedSpan R w i (n+1) := by
  change v ∈ Submodule.span ℂ _ at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨s, l, hl, hp, rfl⟩ := hv
      have he : currentCenter R r (currentRoot R i s (ECalc.Fw (currentCenter R) l w)) =
          currentRoot R i s (ECalc.Fw (currentCenter R) (r::l) w) := by
        simpa only [ECalc.Fw, Module.End.mul_apply] using
          congrArg (fun T : Module.End ℂ V => T (ECalc.Fw (currentCenter R) l w))
            (current_center_root_comm R i r s)
      rw [he]
      apply Submodule.subset_span
      refine ⟨s, r::l, by simp only [List.length_cons]; omega, ?_, rfl⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hr
      · exact hp j hj
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul a v hv ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

variable {R w} {m : ℕ}

/-- Raising a tail of positive-mode centers produces only A-current
words with one fewer positive-mode center. This is an exact source equality
into a spanning space, before any PBW quotient. -/
theorem raise_positive_center_span (h : HighestRel R w m) (i : Fin 8) (r : ℕ)
    (l : List ℕ) (hp : ∀ j ∈ l, 0 < j) :
    currentRaise R i r (ECalc.Fw (currentCenter R) l w) ∈
      positiveCenterDerivedSpan R w i l.length := by
  induction l with
  | nil =>
      change currentRaise R i r w ∈ _
      rw [current_raise_kills h i r]
      exact Submodule.zero_mem _
  | cons j l ih =>
      have hj := hp j (by simp)
      have hl : ∀ k ∈ l, 0 < k := fun k hk => hp k (by simp [hk])
      have hc := congrArg (fun T : Module.End ℂ V => T (ECalc.Fw (currentCenter R) l w))
        (current_raise_center_comm R i r j)
      simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
      change currentRaise R i r (currentCenter R j (ECalc.Fw (currentCenter R) l w)) ∈ _
      rw [sub_eq_iff_eq_add.mp hc]
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨r+j, l, by simp, hl, rfl⟩
      · exact center_positiveDerived_mem R w i j hj (ih hl)

variable (R)

theorem current_raise_center0_pow (i : Fin 8) (r n : ℕ) :
    currentRaise R i r * currentCenter R 0 ^ (n+1) -
      currentCenter R 0 ^ (n+1) * currentRaise R i r =
        (n+1) • (currentCenter R 0 ^ n * currentRoot R i r) := by
  induction n with
  | zero => simpa only [Nat.zero_add, pow_one, pow_zero, one_mul, one_nsmul,
      Nat.add_zero] using current_raise_center_comm R i r 0
  | succ n ih =>
      have hm : currentCenter R 0 ^ n * currentRoot R i r * currentCenter R 0 =
          currentCenter R 0 ^ (n+1) * currentRoot R i r := by
        rw [mul_assoc, ← current_center_root_comm R i 0 r, ← mul_assoc, ← pow_succ]
      calc
        _ = (currentRaise R i r * currentCenter R 0 ^ (n+1) -
              currentCenter R 0 ^ (n+1) * currentRaise R i r) * currentCenter R 0 +
            currentCenter R 0 ^ (n+1) *
              (currentRaise R i r * currentCenter R 0 -
                currentCenter R 0 * currentRaise R i r) := by
          rw [pow_succ]
          noncomm_ring
        _ = (n+1) • (currentCenter R 0 ^ n * currentRoot R i r * currentCenter R 0) +
            currentCenter R 0 ^ (n+1) * currentRoot R i r := by
          rw [ih, current_raise_center_comm, smul_mul_assoc]
          simp only [Nat.add_zero]
        _ = (n+1+1) • (currentCenter R 0 ^ (n+1) * currentRoot R i r) := by
          simp only [hm, add_nsmul, one_nsmul]

theorem current_raise_center0_pow_apply (i : Fin 8) (r n : ℕ) (v : V) :
    currentRaise R i r ((currentCenter R 0 ^ (n+1)) v) =
      (n+1) • currentRoot R i r ((currentCenter R 0 ^ n) v) +
        (currentCenter R 0 ^ (n+1)) (currentRaise R i r v) := by
  have hc := congrArg (fun T : Module.End ℂ V => T v) (current_raise_center0_pow R i r n)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hc
  have he : (currentCenter R 0 ^ n) (currentRoot R i r v) =
      currentRoot R i r ((currentCenter R 0 ^ n) v) :=
    congrArg (fun T : Module.End ℂ V => T v)
      ((Commute.pow_left (current_center_root_comm R i 0 r) n).eq)
  rw [he] at hc
  exact sub_eq_iff_eq_add.mp hc

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.raise_positive_center_span
#print axioms VOA.DeligneAudit.D4FusionContact.current_raise_center0_pow_apply
