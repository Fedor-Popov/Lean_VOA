import VOA.DeligneAudit.SL4TMixedLabelModule

/-!
Radical multiplicity spaces with mode degrees merged before taking Levi quotients.
The ordering uses radical depth and Levi height, retaining every mode degree at each step.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- A fixed triple of radical counts with all mode degrees retained. -/
def radicalCountLayer (d : Fin 3 → ℕ) : Submodule ℂ V :=
  ⨆ degree : ℕ, a3KeyLayer ρ w ⟨d 0, d 1, d 2, degree⟩

/-- Earlier radical counts at the same depth, ordered first by Levi height. -/
def higherRadicalCounts (d : Fin 3 → ℕ) (k : A3RadicalKey) : Prop :=
  k.d₁ + k.d₂ + k.d₃ = d 0 + d 1 + d 2 ∧
    ((d 0 : ℤ) - d 2 < (k.d₁ : ℤ) - k.d₃ ∨
      (d 0 : ℤ) - d 2 = (k.d₁ : ℤ) - k.d₃ ∧
        (d 0 < k.d₁ ∨ d 0 = k.d₁ ∧
          (d 1 < k.d₂ ∨ d 1 = k.d₂ ∧ d 2 < k.d₃)))

/-- Levi closure of the earlier radical counts, without a mode-degree cutoff. -/
def higherRadicalCountClosure (d : Fin 3 → ℕ) : Submodule ℂ V :=
  a3LeviClosure ρ (⨆ (k : A3RadicalKey) (_ : higherRadicalCounts d k), a3KeyLayer ρ w k)

/-- The Levi current action on the quotient by earlier count layers. -/
def radicalCountQuotCurrent (d : Fin 3 → ℕ) :
    CurrentModule VOA.AffineSl3.bracketTable (V ⧸ higherRadicalCountClosure ρ w d) :=
  a3LeviQuotCurrent ρ _ (fun x s => a3LeviClosure_inv ρ _ x s)

/-- The actual multiplicity subspace inside the merged Levi quotient. -/
def radicalCountMultiplicity (d : Fin 3 → ℕ) :
    Submodule ℂ (V ⧸ higherRadicalCountClosure ρ w d) :=
  (radicalCountLayer ρ w d).map (higherRadicalCountClosure ρ w d).mkQ

theorem radicalCountLayer_le_cyclic (d : Fin 3 → ℕ) :
    radicalCountLayer ρ w d ≤ UnivG.cycSubG ρ w := by
  apply iSup_le
  intro degree
  rw [a3KeyLayer, Submodule.span_le]
  rintro z ⟨l, h₀, h₁, h₂, hdegree, hlength, rfl⟩
  clear h₀ h₁ h₂ hdegree hlength
  induction l with
  | nil => exact UnivG.wordOp_mem_cycSubG ρ w []
  | cons x l ih => exact UnivG.cycSubG_inv ρ w (F x.1) x.2 ih

/-- All merged radical multiplicities are finite for every dominant weight. -/
theorem radicalCountMultiplicity_finite (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ) :
    FiniteDimensional ℂ (radicalCountMultiplicity ρ w d) := by
  haveI := (a3_all_weight_rank ρ w a b c h).1
  haveI : FiniteDimensional ℂ (radicalCountLayer ρ w d) :=
    Submodule.finiteDimensional_of_le (radicalCountLayer_le_cyclic ρ w d)
  exact Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp
    (inferInstance : Module.Finite ℂ (radicalCountLayer ρ w d))).map _)

/-- Positive Cartan currents preserve a merged radical count layer. -/
theorem radicalCountLayer_cartan_positive (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) (s : ℕ) (hs : 0 < s) :
    radicalCountLayer ρ w d ≤ (radicalCountLayer ρ w d).comap (ρ.op (leviH i) s) := by
  apply iSup_le
  intro degree v hv
  change ρ.op (leviH i) s v ∈ radicalCountLayer ρ w d
  have hm := a3_cartan_pos_maps_key ρ w a b c h i s hs
    ⟨d 0, d 1, d 2, degree⟩ hv
  exact (le_iSup (fun t => a3KeyLayer ρ w ⟨d 0, d 1, d 2, t⟩) (degree + s)) hm

/-- Zero-mode weights depend on radical counts, with no mode-degree contribution. -/
theorem radicalCountLayer_cartan_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) {v : V} (hv : v ∈ radicalCountLayer ρ w d) :
    ρ.op (leviH i) 0 v = a3KeyLabel b c i ⟨d 0, d 1, d 2, 0⟩ • v := by
  refine Submodule.iSup_induction _
    (motive := fun x => ρ.op (leviH i) 0 x =
      a3KeyLabel b c i ⟨d 0, d 1, d 2, 0⟩ • x) hv ?_ ?_ ?_
  · intro degree x hx
    exact a3_cartan_weight_key_local ρ w a b c h i ⟨d 0, d 1, d 2, degree⟩ hx
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy, smul_add]

/-- Raising currents land in strictly earlier radical counts. -/
theorem radicalCountLayer_raising (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 3) (s : ℕ) :
    radicalCountLayer ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (ρ.op (leviE i) s) := by
  apply iSup_le
  intro degree v hv
  let k : A3RadicalKey := ⟨d 0, d 1, d 2, degree⟩
  change ρ.op (leviE i) s v ∈ higherRadicalCountClosure ρ w d
  by_cases hz : (if i = 0 then k.d₂ else k.d₃) = 0
  · rw [a3_raising_zero_no_source ρ w a b c h i s k hz hv]
    exact Submodule.zero_mem _
  · have hh : higherRadicalCounts d (a3RaiseKey i s k) := by
      fin_cases i <;>
        simp [higherRadicalCounts, a3RaiseKey, k] at * <;> omega
    apply a3LeviClosure_contains ρ _
    exact Submodule.mem_iSup_of_mem (a3RaiseKey i s k)
      (Submodule.mem_iSup_of_mem hh (a3_raising_maps_key ρ w a b c h i s k hv))

/-- The merged multiplicity vectors are highest vectors for every positive Levi mode. -/
theorem radicalCountQuot_raising (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 3) (s : ℕ)
    {v : V} (hv : v ∈ radicalCountLayer ρ w d) :
    (radicalCountQuotCurrent ρ w d).op
      (if i = 0 then 0 else if i = 1 then 2 else 1) s
      ((higherRadicalCountClosure ρ w d).mkQ v) = 0 := by
  have hm := radicalCountLayer_raising ρ w a b c h d i s hv
  fin_cases i <;> exact (Submodule.Quotient.mk_eq_zero _).mpr hm

/-- The two Levi highest weights of the merged multiplicity vectors. -/
theorem radicalCountQuot_cartan_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) {v : V} (hv : v ∈ radicalCountLayer ρ w d) :
    (radicalCountQuotCurrent ρ w d).op (if i = 0 then 6 else 7) 0
      ((higherRadicalCountClosure ρ w d).mkQ v) =
        a3KeyLabel b c i ⟨d 0, d 1, d 2, 0⟩ •
          (higherRadicalCountClosure ρ w d).mkQ v := by
  have he := congrArg (higherRadicalCountClosure ρ w d).mkQ
    (radicalCountLayer_cartan_zero ρ w a b c h d i hv)
  fin_cases i <;> simpa only [map_smul] using he

/-- Positive Cartan action survives on the multiplicity space after merging degrees. -/
theorem radicalCountMultiplicity_cartan_positive (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) (s : ℕ) (hs : 0 < s) :
    radicalCountMultiplicity ρ w d ≤ (radicalCountMultiplicity ρ w d).comap
      ((radicalCountQuotCurrent ρ w d).op (if i = 0 then 6 else 7) s) := by
  rintro x ⟨v, hv, rfl⟩
  have hm := radicalCountLayer_cartan_positive ρ w a b c h d i s hs hv
  fin_cases i <;> exact ⟨_, hm, rfl⟩

/-- A uniform lowering nilpotence exponent works across all mode degrees. -/
theorem radicalCountLayer_lowering_nilpotent (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) {v : V} (hv : v ∈ radicalCountLayer ρ w d) :
    (ρ.op (leviF i) 0 ^
      ((if i = 0 then b else c) + 1 + 2 * (d 0 + d 1 + d 2))) v = 0 := by
  refine Submodule.iSup_induction _
    (motive := fun x => (ρ.op (leviF i) 0 ^
      ((if i = 0 then b else c) + 1 + 2 * (d 0 + d 1 + d 2))) x = 0) hv ?_ ?_ ?_
  · intro degree x hx
    exact a3_key_lowering_nilpotent ρ w a b c h i _ hx
  · simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Negative highest weights vanish and nonnegative weights have sharp lowering powers. -/
theorem radicalCountQuot_lowering_sharp (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (d : Fin 3 → ℕ) (i : Fin 2) {v : V} (hv : v ∈ radicalCountLayer ρ w d) :
    let N := higherRadicalCountClosure ρ w d
    let Q := radicalCountQuotCurrent ρ w d
    let m := a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩
    (m < 0 → N.mkQ v = 0) ∧
      (0 ≤ m → (Q.op (if i = 0 then 3 else 4) 0)^[m.toNat + 1] (N.mkQ v) = 0) := by
  dsimp
  let N := higherRadicalCountClosure ρ w d
  let Q := radicalCountQuotCurrent ρ w d
  let m := a3KeyLabelInt b c i ⟨d 0, d 1, d 2, 0⟩
  have he : Q.op (if i = 0 then 0 else 1) 0 (N.mkQ v) = 0 := by
    fin_cases i
    · exact radicalCountQuot_raising ρ w a b c h d 0 0 hv
    · exact radicalCountQuot_raising ρ w a b c h d 2 0 hv
  have hh : Q.op (if i = 0 then 6 else 7) 0 (N.mkQ v) = (m : ℂ) • N.mkQ v := by
    rw [radicalCountQuot_cartan_zero ρ w a b c h d i hv, a3KeyLabel_eq_int]
  have hi : ∀ j (u : V), (Q.op (if i = 0 then 3 else 4) 0)^[j] (N.mkQ u) =
      N.mkQ ((ρ.op (leviF i) 0)^[j] u) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      fin_cases i <;> rfl
  let K := (if i = 0 then b else c) + 1 + 2 * (d 0 + d 1 + d 2)
  have hn : (Q.op (if i = 0 then 3 else 4) 0)^[K] (N.mkQ v) = 0 := by
    rw [hi, ← Module.End.pow_apply,
      radicalCountLayer_lowering_nilpotent ρ w a b c h d i hv, map_zero]
  exact a3_sl3_simple_hw_pow Q i (N.mkQ v) m K he hh hn

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_le_cyclic
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_finite
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_cartan_positive
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_cartan_zero
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_raising
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_raising
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_cartan_zero
#print axioms VOA.DeligneAudit.SL4T.radicalCountMultiplicity_cartan_positive
#print axioms VOA.DeligneAudit.SL4T.radicalCountLayer_lowering_nilpotent
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_lowering_sharp
