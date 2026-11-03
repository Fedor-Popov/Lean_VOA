import VOA.DeligneAudit.SL4TAdjointSiteCartanGeneration

/-!
# The compound move on the second Levi filtration

In the rank-two Levi current module, the two second-level lowering letters `g = f₂` (sl₃ colour
`3`) and `q = f₂₃` (colour `5`) span a module for the bracket with the final `gl₂` (colours
`1`, `4`, `6`, `7`): every such bracket of `g` or `q` is a combination of `g` and `q`. Adding a
`g`- or a `q`-letter to a word of a count `(u, v)` with `u + v = e₁ + e₂` and `u > e₁` gives a count
`(u + 1, v)` or `(u, v + 1)` that is higher than `(e₁, e₂ + 1)`. Hence:

**Lemma M(ii)** (`higherSecondLeviCountClosure_compound_le`). For every mode `r`,

    q(r) · W_{>(d, (e₁, e₂))} ⊆ W_{>(d, (e₁, e₂ + 1))},

and the same holds for `g(r)` (`higherSecondLeviCountClosure_middle_le`). Iterating,
`q(0)^m · W_{>(d, (e₁, e₂))} ⊆ W_{>(d, (e₁, e₂ + m))}`.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-- The brackets of `g` and `q` with the final `gl₂` stay in the span of `g` and `q`. -/
theorem secondLowering_bracket_finalLevi (c a e : Fin 8) (hc : c = 3 ∨ c = 5)
    (ha : a2Levi a) (he : e ≠ 3 ∧ e ≠ 5) : VOA.AffineSl3.bracketTable c a e = 0 := by
  obtain ⟨he₃, he₅⟩ := he
  rcases hc with rfl | rfl <;> rcases ha with rfl | rfl | rfl | rfl <;> fin_cases e <;>
    first
    | exact absurd rfl he₃
    | exact absurd rfl he₅
    | simp [VOA.AffineSl3.bracketTable]

variable {B W : Type} [CommRing B] [Algebra ℂ B] [AddCommGroup W] [Module ℂ W]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable W) (β : B →ₗ[ℂ] W)

/-- `g(r)` raises the first second-level count of a count layer. -/
theorem secondLeviCountLayer_middle (u v r : ℕ) :
    secondLeviCountLayer Q β u v ≤ (secondLeviCountLayer Q β (u + 1) v).comap (Q.op 3 r) := by
  apply iSup_le
  intro φ x hx
  exact Submodule.mem_iSup_of_mem φ (a2CountSpan_first Q (β φ) u v r hx)

/-- `q(r)` raises the second second-level count of a count layer. -/
theorem secondLeviCountLayer_compound (u v r : ℕ) :
    secondLeviCountLayer Q β u v ≤ (secondLeviCountLayer Q β u (v + 1)).comap (Q.op 5 r) := by
  apply iSup_le
  intro φ x hx
  exact Submodule.mem_iSup_of_mem φ (a2CountSpan_second Q (β φ) u v r hx)

/-- The vectors sent by every mode of `g` and of `q` into a fixed subspace. -/
def secondLoweringPreimage (C : Submodule ℂ W) : Submodule ℂ W :=
  ⨅ r : ℕ, C.comap (Q.op 3 r) ⊓ C.comap (Q.op 5 r)

theorem mem_secondLoweringPreimage (C : Submodule ℂ W) (x : W) :
    x ∈ secondLoweringPreimage Q C ↔ ∀ r, Q.op 3 r x ∈ C ∧ Q.op 5 r x ∈ C := by
  simp [secondLoweringPreimage, Submodule.mem_iInf, Submodule.mem_inf]

/-- The final `gl₂` preserves the preimage of a `gl₂`-stable subspace under `g` and `q`. -/
theorem secondLoweringPreimage_finalLevi (C : Submodule ℂ W)
    (hC : ∀ a r, a2Levi a → C ≤ C.comap (Q.op a r)) (a : Fin 8) (t : ℕ) (ha : a2Levi a) :
    secondLoweringPreimage Q C ≤ (secondLoweringPreimage Q C).comap (Q.op a t) := by
  intro x hx
  rw [Submodule.mem_comap, mem_secondLoweringPreimage]
  rw [mem_secondLoweringPreimage] at hx
  have key (c : Fin 8) (hc : c = 3 ∨ c = 5) (r : ℕ) : Q.op c r (Q.op a t x) ∈ C := by
    have hcomm := Q.comm c a r t x
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    apply C.add_mem
    · apply Submodule.sum_mem
      intro e _
      by_cases he : e = 3 ∨ e = 5
      · rcases he with rfl | rfl
        · exact C.smul_mem _ (hx (r + t)).1
        · exact C.smul_mem _ (hx (r + t)).2
      · rw [secondLowering_bracket_finalLevi c a e hc ha
          ⟨fun h => he (Or.inl h), fun h => he (Or.inr h)⟩, zero_smul]
        exact C.zero_mem
    · rcases hc with rfl | rfl
      · exact hC a t ha (hx r).1
      · exact hC a t ha (hx r).2
  exact fun r => ⟨key 3 (Or.inl rfl) r, key 5 (Or.inr rfl) r⟩

/-- Both `g` and `q` send the higher closure of `(e₁, e₂)` into that of `(e₁, e₂ + 1)`. -/
theorem higherSecondLeviCountClosure_le_secondLoweringPreimage (e₁ e₂ : ℕ) :
    higherSecondLeviCountClosure Q β e₁ e₂ ≤
      secondLoweringPreimage Q (higherSecondLeviCountClosure Q β e₁ (e₂ + 1)) := by
  apply a2LeviClosure_le_of_inv
  · apply iSup_le
    intro u
    apply iSup_le
    intro v
    apply iSup_le
    intro huv x hx
    rw [mem_secondLoweringPreimage]
    intro r
    constructor
    · exact secondLeviCountLayer_le_higher Q β e₁ (e₂ + 1) (u + 1) v
        (by omega) (by omega) (secondLeviCountLayer_middle Q β u v r hx)
    · exact secondLeviCountLayer_le_higher Q β e₁ (e₂ + 1) u (v + 1)
        (by omega) (by omega) (secondLeviCountLayer_compound Q β u v r hx)
  · intro a r ha
    exact secondLoweringPreimage_finalLevi Q _
      (fun a' r' ha' => a2LeviClosure_inv Q _ a' r' ha') a r ha

/-- **Lemma M(ii).** `q(r)` sends `W_{>(d,(e₁, e₂))}` into `W_{>(d,(e₁, e₂ + 1))}`. -/
theorem higherSecondLeviCountClosure_compound_le (e₁ e₂ r : ℕ) :
    higherSecondLeviCountClosure Q β e₁ e₂ ≤
      (higherSecondLeviCountClosure Q β e₁ (e₂ + 1)).comap (Q.op 5 r) := fun _ hx =>
  ((mem_secondLoweringPreimage Q _ _).mp
    (higherSecondLeviCountClosure_le_secondLoweringPreimage Q β e₁ e₂ hx) r).2

/-- The companion move: `g(r)` also sends `W_{>(d,(e₁, e₂))}` into `W_{>(d,(e₁, e₂ + 1))}`. -/
theorem higherSecondLeviCountClosure_middle_le (e₁ e₂ r : ℕ) :
    higherSecondLeviCountClosure Q β e₁ e₂ ≤
      (higherSecondLeviCountClosure Q β e₁ (e₂ + 1)).comap (Q.op 3 r) := fun _ hx =>
  ((mem_secondLoweringPreimage Q _ _).mp
    (higherSecondLeviCountClosure_le_secondLoweringPreimage Q β e₁ e₂ hx) r).1

/-- Iterated Lemma M(ii): `q(0)^m` sends `W_{>(d,(e₁, e₂))}` into `W_{>(d,(e₁, e₂ + m))}`. -/
theorem higherSecondLeviCountClosure_compoundPower_le (e₁ e₂ m : ℕ) :
    higherSecondLeviCountClosure Q β e₁ e₂ ≤
      (higherSecondLeviCountClosure Q β e₁ (e₂ + m)).comap (Q.op 5 0 ^ m) := by
  induction m with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact higherSecondLeviCountClosure_compound_le Q β e₁ (e₂ + m) 0 (ih hx)

end

end VOA.DeligneAudit.SL4T
