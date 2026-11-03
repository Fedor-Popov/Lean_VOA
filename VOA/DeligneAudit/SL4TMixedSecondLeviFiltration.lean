import VOA.DeligneAudit.SL4TFiniteFiltrationRank

/-! Summing the actual second Levi count filtration over the valid mixed blocks. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b : ℕ) (h : LocalWeylRel ρ w (weightABC a b a))

/-- Multiplication by a natural scalar commutes with a complex-linear evaluator. -/
theorem linearMap_natCast_mul {R W : Type} [CommRing R] [Algebra ℂ R]
    [AddCommGroup W] [Module ℂ W] (f : R →ₗ[ℂ] W) (n : ℕ) (x : R) :
    f ((n : R) * x) = (n : ℂ) • f x := by
  simp [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]

/-- First-site support and the two lowering-count bounds give a valid mixed tuple. -/
theorem mixedLabelBlockParams_valid (d : Fin 3 → ℕ)
    (hd : d 0 ≤ a ∧ d 1 ≤ b ∧ d 2 ≤ a) (e₁ e₂ : ℕ)
    (he₁ : (e₁ : ℤ) ≤ a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩)
    (he₂ : (e₂ : ℤ) ≤ a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩) :
    MixedValid (mixedLabelBlockParams a b d e₁ e₂) := by
  simp [MixedValid, mixedLabelBlockParams, mixedP, mixedQ]
  simp [a3KeyLabelInt] at he₁ he₂
  omega

set_option synthInstance.maxHeartbeats 100000 in
-- The source of the evaluator is a tensor product of quotient algebras.
/-- The first retained Cartan preserves each actual second multiplicity in every mode. -/
theorem radicalSecondLeviMultiplicity_otherCartan (d : Fin 3 → ℕ)
    (hm : 0 ≤ a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩)
    (e₁ e₂ s : ℕ) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
    secondLeviMultiplicity Q β e₁ e₂ ≤ (secondLeviMultiplicity Q β e₁ e₂).comap
      (secondLeviQuotientCartan Q β e₁ e₂ 0 s) := by
  by_cases hs : s = 0
  · subst s
    apply secondLeviMultiplicity_cartan _ _ e₁ e₂ 0 0
      (((a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat : ℕ) :
        RadicalGrassmannianRing a b a d)
    intro φ
    have hw := radicalGrassmannianAmbientEvaluation_weight ρ w a b a h d 0 hm φ
    exact hw.trans (linearMap_natCast_mul
      (radicalGrassmannianAmbientEvaluation ρ w a b a h d) _ φ).symm
  · exact secondLeviMultiplicity_cartan _ _ e₁ e₂ 0 s
      (radicalLeviPowerSum a b a d 0 s)
      (radicalGrassmannianAmbientEvaluation_cartan ρ w a b a h d 0 s (by omega))

set_option synthInstance.maxHeartbeats 100000 in
-- Nested quotient tensor algebras need the larger synthesis budget.
/-- Unsupported counts have zero Levi orbit in the second count quotient. -/
theorem radicalSecondLeviClosure_map_zero (d : Fin 3 → ℕ)
    (hm : ∀ j, 0 ≤ a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩)
    (e₁ e₂ : ℕ)
    (he : (a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat < e₁ ∨
      (a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩).toNat < e₂) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
    (a2LeviClosure Q (secondLeviCountLayer Q β e₁ e₂)).map
      (higherSecondLeviCountClosure Q β e₁ e₂).mkQ = ⊥ := by
  dsimp only
  rw [secondLeviClosure_map_eq_orbit _ _ e₁ e₂
    (radicalSecondLeviMultiplicity_otherCartan ρ w a b h d (hm 0) e₁ e₂)]
  rw [secondLeviOrbit, secondLeviMultiplicity_eq_bot_of_unsupported ρ w a b a h d
    e₁ e₂ hm he]
  apply le_antisymm _ bot_le
  apply currentSpan_le
  · intro x hx
    exact hx
  · exact ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩

/-- Counts at a fixed total form a finite fiber, ordered by decreasing first count. -/
def secondLeviCountFiber (e : ℕ × ℕ) : Finset (ℕ × ℕ) := Finset.antidiagonal (e.1 + e.2)

/-- The earlier second closure only uses smaller positions in its finite count fiber. -/
theorem higherSecondLeviCountClosure_le_fiber {B W : Type}
    [CommRing B] [Algebra ℂ B] [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.AffineSl3.bracketTable W) (β : B →ₗ[ℂ] W) (e : ℕ × ℕ) :
    higherSecondLeviCountClosure Q β e.1 e.2 ≤
      ⨆ j ∈ secondLeviCountFiber e, ⨆ (_ : -(j.1 : ℤ) < -(e.1 : ℤ)),
        a2LeviClosure Q (secondLeviCountLayer Q β j.1 j.2) := by
  unfold higherSecondLeviCountClosure
  rw [a2LeviClosure_iSup]
  apply iSup_le
  intro u
  rw [a2LeviClosure_iSup]
  apply iSup_le
  intro v
  rw [a2LeviClosure_iSup]
  apply iSup_le
  intro hv
  exact le_iSup_of_le (u, v)
    (le_iSup_of_le (Finset.mem_antidiagonal.mpr hv.1)
      (le_iSup_of_le (by omega) le_rfl))

set_option synthInstance.maxHeartbeats 100000 in
-- The count filtration lives over the nested Grassmannian coefficient algebra.
/-- The whole second Levi filtration is bounded by the sum of its valid mixed cell blocks. -/
theorem mixedSecondLeviFiltration_rank_le [FiniteDimensional ℂ V]
    (ht : ∀ i s v, a + b ≤ s → ρ.op i s v = 0)
    (d : Fin 3 → ℕ) (hd : d 0 ≤ a ∧ d 1 ≤ b ∧ d 2 ≤ a) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
    let p := (a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat
    let q := (a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩).toNat
    Module.finrank ℂ ↥(⨆ e : ℕ × ℕ,
      a2LeviClosure Q (secondLeviCountLayer Q β e.1 e.2)) ≤
        ∑ e ∈ (Finset.range (p + 1)) ×ˢ (Finset.range (q + 1)),
          mixedBlockBound (mixedLabelBlockParams a b d e.1 e.2) := by
  classical
  let Q := radicalCountQuotCurrent ρ w d
  let β := radicalGrassmannianAmbientEvaluation ρ w a b a h d
  let p := (a3KeyLabelInt b a 0 ⟨d 0, d 1, d 2, 0⟩).toNat
  let q := (a3KeyLabelInt b a 1 ⟨d 0, d 1, d 2, 0⟩).toNat
  let S := fun e : ℕ × ℕ => a2LeviClosure Q (secondLeviCountLayer Q β e.1 e.2)
  let N := fun e : ℕ × ℕ => higherSecondLeviCountClosure Q β e.1 e.2
  let t := (Finset.range (p + 1)) ×ˢ (Finset.range (q + 1))
  let c := fun e : ℕ × ℕ => if e ∈ t then
    mixedBlockBound (mixedLabelBlockParams a b d e.1 e.2) else 0
  have hm : ∀ j, 0 ≤ a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩ := by
    intro j
    fin_cases j <;> simp [a3KeyLabelInt] <;> omega
  have hb := finiteFiberFiltration_finrank_le S N secondLeviCountFiber
    (fun e => -(e.1 : ℤ)) c t
    (fun i => Finset.mem_antidiagonal.mpr rfl)
    (fun i j hj => by
      have he := Finset.mem_antidiagonal.mp hj
      simp only [secondLeviCountFiber, he])
    (higherSecondLeviCountClosure_le_fiber Q β)
    (fun e => by
      by_cases he : e ∈ t
      · have he' := he
        simp only [t, Finset.mem_product, Finset.mem_range] at he'
        have hv := mixedLabelBlockParams_valid a b d hd e.1 e.2
          (by rw [← Int.toNat_of_nonneg (hm 0)]; exact_mod_cast (by omega : e.1 ≤ p))
          (by rw [← Int.toNat_of_nonneg (hm 1)]; exact_mod_cast (by omega : e.2 ≤ q))
        rw [show (S e).map (N e).mkQ = secondLeviOrbit Q β e.1 e.2 from
          secondLeviClosure_map_eq_orbit Q β e.1 e.2
            (radicalSecondLeviMultiplicity_otherCartan ρ w a b h d (hm 0) e.1 e.2)]
        simpa only [c, if_pos he] using (mixedSecondLeviOrbit_bound ρ w a b h ht d
          e.1 e.2 hv).2
      · have he' : p < e.1 ∨ q < e.2 := by
          simp only [t, Finset.mem_product, Finset.mem_range] at he
          omega
        rw [show (S e).map (N e).mkQ = ⊥ from
          radicalSecondLeviClosure_map_zero ρ w a b h d hm e.1 e.2 he']
        simp [c, he])
    (fun e he => by simp [c, he])
  simpa only [c, Finset.sum_ite_mem, Finset.inter_self] using hb

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedLabelBlockParams_valid
#print axioms VOA.DeligneAudit.SL4T.linearMap_natCast_mul
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviMultiplicity_otherCartan
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviClosure_map_zero
#print axioms VOA.DeligneAudit.SL4T.higherSecondLeviCountClosure_le_fiber
#print axioms VOA.DeligneAudit.SL4T.mixedSecondLeviFiltration_rank_le
