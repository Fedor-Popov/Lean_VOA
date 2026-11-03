import VOA.DeligneAudit.SL4TSecondLeviHighest

/-! Last-root highest weights and integrability on the second multiplicity quotient. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.CVsl2

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- A raising current sends a fixed second count layer into earlier count layers. -/
theorem secondLeviCountLayer_raising (he : ∀ s φ, Q.op 1 s (β φ) = 0)
    (e₁ e₂ s : ℕ) : secondLeviCountLayer Q β e₁ e₂ ≤
      (higherSecondLeviCountClosure Q β e₁ e₂).comap (Q.op 1 s) := by
  apply iSup_le
  intro φ
  apply iSup_le
  intro degree v hv
  change Q.op 1 s v ∈ higherSecondLeviCountClosure Q β e₁ e₂
  by_cases hz : e₂ = 0
  · have hh : Q.op 1 s v = 0 := by
      induction hv using Submodule.span_induction with
      | mem z hz' =>
        obtain ⟨l, _, hd₂, _, _, rfl⟩ := hz'
        exact secondRadical_raising_zero_of_no_compound Q (β φ)
          (fun r => he r φ) s l (hd₂.trans hz)
      | zero => simp
      | add x y _ _ hx hy => simp [map_add, hx, hy]
      | smul c x _ hx => simp [map_smul, hx]
    rw [hh]
    exact Submodule.zero_mem _
  · apply secondLeviCountLayer_le_higher Q β e₁ e₂ (e₁ + 1) (e₂ - 1)
      (by omega) (by omega)
    apply Submodule.mem_iSup_of_mem φ
    apply Submodule.mem_iSup_of_mem (degree + s)
    exact secondRadical_raising_maps_key Q (β φ) (fun r => he r φ) s
      ⟨e₁, e₂, degree⟩ hv

/-- The last zero-mode Cartan weight depends only on the two lowering counts. -/
theorem secondLeviCountLayer_weight (q : ℕ)
    (hh : ∀ φ, Q.op 7 0 (β φ) = (q : ℂ) • β φ) (e₁ e₂ : ℕ)
    {v : V} (hv : v ∈ secondLeviCountLayer Q β e₁ e₂) :
    Q.op 7 0 v = ((q : ℂ) + e₁ - e₂) • v := by
  refine Submodule.iSup_induction _ (motive := fun v =>
    Q.op 7 0 v = ((q : ℂ) + e₁ - e₂) • v) hv ?_ ?_ ?_
  · intro φ v hv
    refine Submodule.iSup_induction _ (motive := fun v =>
      Q.op 7 0 v = ((q : ℂ) + e₁ - e₂) • v) hv ?_ ?_ ?_
    · intro degree v hv
      exact a2_node2_weight_key Q (β φ) q ⟨e₁, e₂, degree⟩ (hh φ) hv
    · simp
    · intro x y hx hy
      simp [map_add, hx, hy, smul_add]
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy, smul_add]

/-- A common lowering power kills the whole count layer, including all base coefficients. -/
theorem secondLeviCountLayer_nilpotent (q : ℕ)
    (hf : ∀ φ, (Q.op 4 0 ^ (q + 1)) (β φ) = 0) (e₁ e₂ : ℕ)
    {v : V} (hv : v ∈ secondLeviCountLayer Q β e₁ e₂) :
    (Q.op 4 0 ^ (q + 1 + adK A2sector * (e₁ + e₂))) v = 0 := by
  refine Submodule.iSup_induction _ (motive := fun v =>
    (Q.op 4 0 ^ (q + 1 + adK A2sector * (e₁ + e₂))) v = 0) hv ?_ ?_ ?_
  · intro φ v hv
    refine Submodule.iSup_induction _ (motive := fun v =>
      (Q.op 4 0 ^ (q + 1 + adK A2sector * (e₁ + e₂))) v = 0) hv ?_ ?_ ?_
    · intro degree v hv
      exact secondRadical_key_lowering_nilpotent Q (β φ) q (hf φ)
        ⟨e₁, e₂, degree⟩ hv
    · simp
    · intro x y hx hy
      simp [map_add, hx, hy]
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- The last raising current descends to the quotient by earlier second counts. -/
def secondLeviQuotientRaising (e₁ e₂ s : ℕ) :
    Module.End ℂ (V ⧸ higherSecondLeviCountClosure Q β e₁ e₂) :=
  (higherSecondLeviCountClosure Q β e₁ e₂).mapQ
    (higherSecondLeviCountClosure Q β e₁ e₂) (Q.op 1 s)
    (a2LeviClosure_inv Q _ 1 s (by simp [a2Levi]))

/-- The last lowering current descends to the quotient by earlier second counts. -/
def secondLeviQuotientLowering (e₁ e₂ s : ℕ) :
    Module.End ℂ (V ⧸ higherSecondLeviCountClosure Q β e₁ e₂) :=
  (higherSecondLeviCountClosure Q β e₁ e₂).mapQ
    (higherSecondLeviCountClosure Q β e₁ e₂) (Q.op 4 s)
    (a2LeviClosure_inv Q _ 4 s (by simp [a2Levi]))

/-- The last-root current triple survives the second Levi quotient. -/
theorem secondLeviQuotient_currentRelations (e₁ e₂ : ℕ) :
    SL2 (secondLeviQuotientRaising Q β e₁ e₂)
      (secondLeviQuotientCartan Q β e₁ e₂ 1) (secondLeviQuotientLowering Q β e₁ e₂) :=
  SL2_quot (a2_node2_sl2 Q) (higherSecondLeviCountClosure Q β e₁ e₂)
    (fun s => a2LeviClosure_inv Q _ 1 s (by simp [a2Levi]))
    (fun s => a2LeviClosure_inv Q _ 7 s (by simp [a2Levi]))
    (fun s => a2LeviClosure_inv Q _ 4 s (by simp [a2Levi]))

/-- Every vector in the second multiplicity is killed by the last raising currents. -/
theorem secondLeviMultiplicity_raising (he : ∀ s φ, Q.op 1 s (β φ) = 0)
    (e₁ e₂ s : ℕ) (v : secondLeviMultiplicity Q β e₁ e₂) :
    secondLeviQuotientRaising Q β e₁ e₂ s v.val = 0 := by
  obtain ⟨x, hx, hxv⟩ := v.property
  rw [← hxv]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (secondLeviCountLayer_raising Q β he e₁ e₂ s hx)

/-- Every vector in the second multiplicity has the predicted last-root weight. -/
theorem secondLeviMultiplicity_weight (q : ℕ)
    (hh : ∀ φ, Q.op 7 0 (β φ) = (q : ℂ) • β φ)
    (e₁ e₂ : ℕ) (v : secondLeviMultiplicity Q β e₁ e₂) :
    secondLeviQuotientCartan Q β e₁ e₂ 1 0 v.val =
      (((q : ℤ) + e₁ - e₂ : ℤ) : ℂ) • v.val := by
  obtain ⟨x, hx, hxv⟩ := v.property
  rw [← hxv]
  change (higherSecondLeviCountClosure Q β e₁ e₂).mkQ (Q.op 7 0 x) = _
  rw [secondLeviCountLayer_weight Q β q hh e₁ e₂ hx, map_smul]
  simp

/-- Negative second weights vanish; nonnegative second weights have sharp lowering powers. -/
theorem secondLeviMultiplicity_lowering_sharp (q : ℕ)
    (he : ∀ s φ, Q.op 1 s (β φ) = 0)
    (hh : ∀ φ, Q.op 7 0 (β φ) = (q : ℂ) • β φ)
    (hf : ∀ φ, (Q.op 4 0 ^ (q + 1)) (β φ) = 0)
    (e₁ e₂ : ℕ) (v : secondLeviMultiplicity Q β e₁ e₂) :
    let r : ℤ := q + e₁ - e₂
    (r < 0 → v.val = 0) ∧ (0 ≤ r →
      (secondLeviQuotientLowering Q β e₁ e₂ 0 ^ (r.toNat + 1)) v.val = 0) := by
  dsimp
  let E := secondLeviQuotientRaising Q β e₁ e₂
  let H := secondLeviQuotientCartan Q β e₁ e₂ 1
  let F := secondLeviQuotientLowering Q β e₁ e₂
  have hS := secondLeviQuotient_currentRelations Q β e₁ e₂
  have hef : ∀ x, E 0 (F 0 x) - F 0 (E 0 x) = H 0 x := by
    intro x
    simpa using congrArg (fun T : Module.End ℂ _ => T x) (hS.hEF 0 0)
  have hhf : ∀ x, H 0 (F 0 x) - F 0 (H 0 x) = (-2 : ℂ) • F 0 x := by
    intro x
    simpa using congrArg (fun T : Module.End ℂ _ => T x) (hS.hHF 0 0)
  have hp : ∀ n x, (F 0 ^ n) ((higherSecondLeviCountClosure Q β e₁ e₂).mkQ x) =
      (higherSecondLeviCountClosure Q β e₁ e₂).mkQ ((Q.op 4 0 ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  let K := q + 1 + adK A2sector * (e₁ + e₂)
  have hn : (F 0)^[K] v.val = 0 := by
    obtain ⟨x, hx, hxv⟩ := v.property
    rw [← hxv, ← Module.End.pow_apply, hp,
      secondLeviCountLayer_nilpotent Q β q hf e₁ e₂ hx, map_zero]
  simpa only [← Module.End.pow_apply] using VOA.DeligneAudit.CLFilt.hw_pow
    (E 0) (F 0) (H 0) hef hhf (secondLeviMultiplicity_raising Q β he e₁ e₂ 0 v)
      (secondLeviMultiplicity_weight Q β q hh e₁ e₂ v) K hn

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_raising
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_weight
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_nilpotent
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotient_currentRelations
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_raising
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_weight
#print axioms VOA.DeligneAudit.SL4T.secondLeviMultiplicity_lowering_sharp
