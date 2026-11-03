import VOA.DeligneAudit.D4FusionContactTable
import VOA.DeligneAudit.DeligneFusionPBW

/-!
# The actual D₄ nine-color contact PBW spanning reduction

The hypotheses are defining highest-weight and outer-simple-root
relations. They are extracted from `LocalWeylRelG` in the sector
wrapper. No dimension or finite-dimensionality premise occurs here.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorGraded

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule contactF V} {w : V}

/-- The exact highest-weight source relations needed to discard the
three outer Levi colors. The central simple nilpotence and fusion
cutoffs are not needed for this spanning reduction. -/
structure HighestRel (R : CurrentModule contactF V) (w : V) (m : ℕ) : Prop where
  raising : ∀ e : Fin 28, 4 ≤ e.val ∧ e.val < 16 → ∀ r, R.op e r w = 0
  cartan_pos : ∀ h : Fin 28, h.val < 4 → ∀ r, 1 ≤ r → R.op h r w = 0
  cartan_zero : ∀ h : Fin 28, h.val < 4 →
    R.op h 0 w = (if h.val = 1 then (m : ℂ) else 0) • w
  levi_zero : ∀ i : Fin 3, R.op (leviIndex i) 0 w = 0

/-- Positive Cartan modes propagate an outer simple zero-mode relation
to every current mode of that outer root. -/
theorem levi_all {m : ℕ} (h : HighestRel R w m) (i : Fin 3) (r : ℕ) :
    R.op (leviIndex i) r w = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact h.levi_zero i
  · have hc := R.comm (leviCartan i) (leviIndex i) r 0 w
    simp only [levi_cartan_table, Nat.add_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
    rw [h.levi_zero i, map_zero,
      h.cartan_pos (leviCartan i) (leviCartan_lt_four i) r hr, map_zero, sub_self] at hc
    exact (smul_eq_zero.mp hc.symm).resolve_left (by norm_num)

theorem nonactive_hw {m : ℕ} (h : HighestRel R w m) (c : Fin 28) (r : ℕ)
    (hc : ¬ active c) : R.op c r w ∈ ℂ ∙ w ∧ (1 ≤ r → R.op c r w = 0) := by
  by_cases hc4 : c.val < 4
  · refine ⟨?_, fun hr => h.cartan_pos c hc4 r hr⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [h.cartan_zero c hc4]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · rw [h.cartan_pos c hc4 r hr]
      exact Submodule.zero_mem _
  · by_cases hc16 : c.val < 16
    · rw [h.raising c (by omega) r]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · obtain ⟨i, hi⟩ := (negative_nonactive_iff c).mp ⟨by omega, hc⟩
      subst c
      rw [levi_all h i r]
      exact ⟨Submodule.zero_mem _, fun _ => rfl⟩

def contactKey (x : Fin 28 × ℕ) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (if active x.1 then 0 else 1, toLex (x.1.val, x.2))

theorem contactKey_low (x y : Fin 28 × ℕ) (hx : ¬ active x.1) (hy : active y.1) :
    contactKey y < contactKey x := by
  simp only [contactKey, if_pos hy, if_neg hx]
  exact Prod.Lex.lt_iff.mpr (Or.inl Nat.zero_lt_one)

/-- Every current-degree piece is spanned by sorted words in only
the nine contact-radical colors. This holds for every multiplicity. -/
theorem cycDeg_le_contact {m : ℕ} (h : HighestRel R w m) (d : ℕ) :
    cycDeg R w d ≤ Submodule.span ℂ {u | ∃ l : List (Fin 28 × ℕ),
      l.IsChain (fun a b => contactKey a ≤ contactKey b) ∧
      (∀ x ∈ l, active x.1) ∧
      VOA.DeligneAudit.SectorGraded.wordDeg l = d ∧ u = wordOp R l w} :=
  cycDeg_le_sortedLow contactKey active R contactKey_low (nonactive_hw h) d

/-- The contact brackets are exact operator identities on the full
module, with the four nonzero pairs recorded by `contactCoeff`. -/
theorem contact_comm (i j : Fin 9) (r s : ℕ) :
    R.op (radIndex i) r * R.op (radIndex j) s -
        R.op (radIndex j) s * R.op (radIndex i) r =
      (contactCoeff i j : ℂ) • R.op 27 (r + s) := by
  ext v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    contact_table, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
    R.comm (radIndex i) (radIndex j) r s v

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.levi_all
#print axioms VOA.DeligneAudit.D4FusionContact.cycDeg_le_contact
#print axioms VOA.DeligneAudit.D4FusionContact.contact_comm
