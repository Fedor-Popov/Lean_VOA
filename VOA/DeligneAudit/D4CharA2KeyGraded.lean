import VOA.DeligneAudit.D4CharSl2GradedAction
import VOA.DeligneAudit.LeviTypeA2CertSl2OtherKey

/-! The sharp sl2 estimate in the actual higher-key quotients of the type-A2 chain. -/

namespace VOA.DeligneAudit.D4Char

open A3Sector SectorWeyl CVsl2

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

def a2GradedKeyOp (q : ℕ) (k : A2RadicalKey) (a : Fin 8) (ha : a2Levi a)
    (r : ℕ) : Module.End ℂ (V ⧸ a2LeviClosure ρ (a2HigherKeySpan ρ w q k)) :=
  (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mapQ
    (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)) (ρ.op a r)
    (a2LeviClosure_inv ρ _ a r ha)

abbrev a2GradedKeyE (q : ℕ) (k : A2RadicalKey) :=
  a2GradedKeyOp ρ w q k 1 (Or.inl rfl)

abbrev a2GradedKeyF (q : ℕ) (k : A2RadicalKey) :=
  a2GradedKeyOp ρ w q k 4 (Or.inr (Or.inl rfl))

abbrev a2GradedKeyH (q : ℕ) (k : A2RadicalKey) :=
  a2GradedKeyOp ρ w q k 7 (Or.inr (Or.inr (Or.inr rfl)))

abbrev a2GradedKeyK (q : ℕ) (k : A2RadicalKey) :=
  a2GradedKeyOp ρ w q k 6 (Or.inr (Or.inr (Or.inl rfl)))

theorem a2GradedKey_sl2 (q : ℕ) (k : A2RadicalKey) :
    SL2 (a2GradedKeyE ρ w q k) (a2GradedKeyH ρ w q k) (a2GradedKeyF ρ w q k) :=
  SL2_quot (a2_node2_sl2 ρ) _
    (fun r => a2LeviClosure_inv ρ _ 1 r (Or.inl rfl))
    (fun r => a2LeviClosure_inv ρ _ 7 r (Or.inr (Or.inr (Or.inr rfl))))
    (fun r => a2LeviClosure_inv ρ _ 4 r (Or.inr (Or.inl rfl)))

/-- All generator conditions required by the sharp graded sl2 bound hold in the quotient. -/
theorem a2GradedKey_rel (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    let z := (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v
    (∀ s, a2GradedKeyE ρ w q k s z = 0) ∧
    (∀ s, 0 < s → a2GradedKeyH ρ w q k s z = 0) ∧
    (∃ a : ℂ, a2GradedKeyH ρ w q k 0 z = a • z) ∧
    (0 ≤ a2KeyHeight q k →
      (a2GradedKeyF ρ w q k 0 ^ ((a2KeyHeight q k).toNat + 1)) z = 0) := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  have hr := a2_key_local_weyl_levi_quotient ρ w p q h k hv
  refine ⟨fun s => ?_, fun s hs => ?_, ?_, fun hk => ?_⟩
  · exact (Submodule.Quotient.mk_eq_zero N).mpr (hr.1 s)
  · exact (Submodule.Quotient.mk_eq_zero N).mpr (hr.2.1 s hs)
  · refine ⟨(a2KeyHeight q k : ℂ), ?_⟩
    change N.mkQ (ρ.op 7 0 v) = _
    rw [hr.2.2.1, map_smul]
  · have hp : ∀ j : ℕ,
        (a2GradedKeyF ρ w q k 0 ^ j) (N.mkQ v) = N.mkQ ((ρ.op 4 0 ^ j) v) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          rw [pow_succ', Module.End.mul_apply, ih]
          change N.mkQ (ρ.op 4 0 ((ρ.op 4 0 ^ j) v)) = _
          rw [pow_succ', Module.End.mul_apply]
    rw [hp]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hr.2.2.2.2 hk)

theorem a2GradedKey_lower_bound (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k)
    (hk : 0 ≤ a2KeyHeight q k) (d : ℕ) :
    let z := (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v
    FiniteDimensional ℂ (sl2LowerDegree (a2GradedKeyF ρ w q k) z d) ∧
      Module.finrank ℂ (sl2LowerDegree (a2GradedKeyF ρ w q k) z d) ≤
        A2.gl2Hilb (a2KeyHeight q k).toNat 0 d := by
  have hr := a2GradedKey_rel ρ w p q h k hv
  exact sl2_local_weyl_graded_bound (a2GradedKey_sl2 ρ w q k)
    hr.1 hr.2.1 _ (hr.2.2.2 hk) d

theorem a2GradedKey_extra_comm (q : ℕ) (k : A2RadicalKey) (s r : ℕ) :
    a2GradedKeyK ρ w q k s * a2GradedKeyF ρ w q k r -
      a2GradedKeyF ρ w q k r * a2GradedKeyK ρ w q k s =
        a2GradedKeyF ρ w q k (s + r) := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  apply LinearMap.ext
  intro z
  obtain ⟨u, rfl⟩ := N.mkQ_surjective z
  simp only [a2GradedKeyK, a2GradedKeyF, a2GradedKeyOp,
    Submodule.mkQ_apply, Submodule.mapQ_apply,
    LinearMap.sub_apply, Module.End.mul_apply, ← Submodule.Quotient.mk_sub]
  exact congrArg N.mkQ (congrArg (fun T : Module.End ℂ V => T u)
    (a2_other_f2_comm ρ s r))

theorem a2GradedKey_extra_rel (p q : ℕ) (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) {v : V} (hv : v ∈ a2KeyLayer ρ w k) :
    let z := (a2LeviClosure ρ (a2HigherKeySpan ρ w q k)).mkQ v
    (∃ a : ℂ, a2GradedKeyK ρ w q k 0 z = a • z) ∧
      (∀ s, 0 < s → a2GradedKeyK ρ w q k s z = 0) := by
  let N := a2LeviClosure ρ (a2HigherKeySpan ρ w q k)
  constructor
  · refine ⟨(p : ℂ) - 2 * (k.d₁ : ℂ) - (k.d₂ : ℂ), ?_⟩
    change N.mkQ (ρ.op 6 0 v) = _
    rw [a2_other_cartan_weight_key ρ w p k h.cartan_first hv, map_smul]
  · intro s hs
    exact (Submodule.Quotient.mk_eq_zero N).mpr
      ((a2LeviClosure_contains ρ _)
        (a2_other_cartan_pos_mem_higher ρ w p q h s hs k hv))

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_sl2
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_rel
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_lower_bound
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_extra_comm
#print axioms VOA.DeligneAudit.D4Char.a2GradedKey_extra_rel
