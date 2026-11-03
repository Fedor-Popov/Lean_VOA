import VOA.DeligneAudit.SL4TLeviCountGeneration

/-! The first Levi filtration with all mode degrees merged into finite count fibers. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.UnivG
attribute [local instance 2000] Fin.fintype Fin.instOfNat

/-- All triples whose coordinates are at most the given bound. -/
def radicalCountBox (n : ℕ) : Finset (Fin 3 → ℕ) :=
  Finset.univ.image (fun x : Fin 3 → Fin (n + 1) => fun i => (x i).val)

theorem mem_radicalCountBox (n : ℕ) (d : Fin 3 → ℕ) :
    d ∈ radicalCountBox n ↔ ∀ i, d i ≤ n := by
  classical
  constructor
  · intro hd
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
    exact fun i => Nat.le_of_lt_succ (x i).isLt
  · intro hd
    exact Finset.mem_image.mpr ⟨fun i => ⟨d i, Nat.lt_succ_of_le (hd i)⟩,
      Finset.mem_univ _, rfl⟩

/-- All count triples at the same total radical depth. -/
def radicalCountFiber (d : Fin 3 → ℕ) : Finset (Fin 3 → ℕ) :=
  (radicalCountBox (d 0 + d 1 + d 2)).filter
    (fun j => j 0 + j 1 + j 2 = d 0 + d 1 + d 2)

theorem mem_radicalCountFiber (d j : Fin 3 → ℕ) :
    j ∈ radicalCountFiber d ↔ j 0 + j 1 + j 2 = d 0 + d 1 + d 2 := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hj
    apply Finset.mem_filter.mpr
    refine ⟨(mem_radicalCountBox _ _).mpr ?_, hj⟩
    intro i
    fin_cases i <;> simp <;> omega

/-- Integer positions decrease along the first Levi's earlier-count ordering. -/
def radicalCountPosition (d : Fin 3 → ℕ) : ℤ :=
  -((d 0 + d 1 + d 2 : ℕ) + 1 : ℤ) * ((d 0 : ℤ) - d 2) - d 0

/-- Earlier first counts have a strictly smaller position in their common finite fiber. -/
theorem higherRadicalCounts_position (d : Fin 3 → ℕ) (k : A3RadicalKey)
    (hk : higherRadicalCounts d k) :
    radicalCountPosition ![k.d₁, k.d₂, k.d₃] < radicalCountPosition d := by
  rcases hk with ⟨ht, hh⟩
  change -((k.d₁ + k.d₂ + k.d₃ : ℕ) + 1 : ℤ) * ((k.d₁ : ℤ) - k.d₃) - k.d₁ <
    -((d 0 + d 1 + d 2 : ℕ) + 1 : ℤ) * ((d 0 : ℤ) - d 2) - d 0
  rw [ht]
  have hd : (d 0 : ℤ) ≤ (d 0 + d 1 + d 2 : ℕ) := by omega
  have hkd : (k.d₁ : ℤ) ≤ (d 0 + d 1 + d 2 : ℕ) := by omega
  rcases hh with hh | ⟨hh, hlex⟩
  · have hdiff : 1 ≤ ((k.d₁ : ℤ) - k.d₃) - ((d 0 : ℤ) - d 2) := by omega
    have hmul := mul_le_mul_of_nonneg_left hdiff
      (show 0 ≤ ((d 0 + d 1 + d 2 : ℕ) + 1 : ℤ) by positivity)
    nlinarith
  · have hfirst : d 0 < k.d₁ := by omega
    nlinarith

/-- First multiplicities can be nonzero only inside the three highest-weight counts. -/
def radicalSupportedCounts (a b c : ℕ) : Finset (Fin 3 → ℕ) :=
  (radicalCountBox (a + b + c)).filter (fun d => d 0 ≤ a ∧ d 1 ≤ b ∧ d 2 ≤ c)

theorem mem_radicalSupportedCounts (a b c : ℕ) (d : Fin 3 → ℕ) :
    d ∈ radicalSupportedCounts a b c ↔ d 0 ≤ a ∧ d 1 ≤ b ∧ d 2 ≤ c := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hd
    refine Finset.mem_filter.mpr ⟨(mem_radicalCountBox _ _).mpr ?_, hd⟩
    intro i
    fin_cases i <;> simp <;> omega

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The first earlier closure lies in the earlier positions of its finite count fiber. -/
theorem higherRadicalCountClosure_le_fiber (d : Fin 3 → ℕ) :
    higherRadicalCountClosure ρ w d ≤
      ⨆ j ∈ radicalCountFiber d, ⨆ (_ : radicalCountPosition j < radicalCountPosition d),
        a3LeviClosure ρ (radicalCountLayer ρ w j) := by
  unfold higherRadicalCountClosure
  rw [a3LeviClosure_iSup]
  apply iSup_le
  intro k
  rw [a3LeviClosure_iSup]
  apply iSup_le
  intro hk
  apply le_iSup_of_le ![k.d₁, k.d₂, k.d₃]
  apply le_iSup_of_le ((mem_radicalCountFiber _ _).mpr (by simpa using hk.1))
  apply le_iSup_of_le (higherRadicalCounts_position d k hk)
  apply a3LeviClosure_mono
  exact le_iSup_of_le k.degree le_rfl

/-- A zero first multiplicity has zero Levi orbit in its count quotient. -/
theorem radicalCountClosure_map_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ)
    (hd : a < d 0 ∨ b < d 1 ∨ c < d 2) :
    (a3LeviClosure ρ (radicalCountLayer ρ w d)).map
      (higherRadicalCountClosure ρ w d).mkQ = ⊥ := by
  let N := higherRadicalCountClosure ρ w d
  have hz : radicalCountLayer ρ w d ≤ N := by
    intro x hx
    have hm : N.mkQ x ∈ radicalCountMultiplicity ρ w d := ⟨x, hx, rfl⟩
    rw [radicalCountMultiplicity_eq_bot_of_unsupported ρ w a b c h d hd] at hm
    exact (Submodule.Quotient.mk_eq_zero _).mp hm
  have hcl : a3LeviClosure ρ (radicalCountLayer ρ w d) ≤ N :=
    a3LeviClosure_le_of_inv ρ _ _ hz (fun i s => a3LeviClosure_inv ρ _ i s)
  apply le_antisymm _ bot_le
  rintro x ⟨v, hv, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero N).mpr (hcl hv)

/-- The complete cyclic module is the sum of the merged first-count Levi closures. -/
theorem cyclic_eq_radicalCountClosures (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    cycSubG ρ w = ⨆ d : Fin 3 → ℕ, a3LeviClosure ρ (radicalCountLayer ρ w d) := by
  rw [a3_cycSubG_eq_leviClosure_allKeys ρ w a b c h, ← a3LeviClosure_iSup]
  congr 1
  apply le_antisymm
  · apply iSup_le
    intro k
    exact le_iSup_of_le ![k.d₁, k.d₂, k.d₃] (le_iSup_of_le k.degree le_rfl)
  · apply iSup_le
    intro d
    apply iSup_le
    intro degree
    exact le_iSup (fun k => a3KeyLayer ρ w k) ⟨d 0, d 1, d 2, degree⟩

/-- The complete first filtration is bounded by any supported family of quotient orbit bounds. -/
theorem radicalCountFiltration_rank_le [FiniteDimensional ℂ V] (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) (bound : (Fin 3 → ℕ) → ℕ)
    (hb : ∀ d, d ∈ radicalSupportedCounts a b c →
      Module.finrank ℂ ((a3LeviClosure ρ (radicalCountLayer ρ w d)).map
        (higherRadicalCountClosure ρ w d).mkQ) ≤ bound d) :
    Module.finrank ℂ (cycSubG ρ w) ≤ ∑ d ∈ radicalSupportedCounts a b c, bound d := by
  classical
  let c' := fun d => if d ∈ radicalSupportedCounts a b c then bound d else 0
  have hf := finiteFiberFiltration_finrank_le
    (fun d => a3LeviClosure ρ (radicalCountLayer ρ w d))
    (higherRadicalCountClosure ρ w) radicalCountFiber radicalCountPosition
    c' (radicalSupportedCounts a b c)
    (fun i => (mem_radicalCountFiber _ _).mpr rfl)
    (fun i j hj => by
      have he := (mem_radicalCountFiber _ _).mp hj
      simp only [radicalCountFiber, he])
    (higherRadicalCountClosure_le_fiber ρ w)
    (fun d => by
      by_cases hd : d ∈ radicalSupportedCounts a b c
      · simpa [c', hd] using hb d hd
      · have he : a < d 0 ∨ b < d 1 ∨ c < d 2 := by
          rw [mem_radicalSupportedCounts] at hd
          omega
        rw [radicalCountClosure_map_zero ρ w a b c h d he]
        simp [c', hd])
    (fun d hd => by simp [c', hd])
  rw [← cyclic_eq_radicalCountClosures ρ w a b c h] at hf
  simpa only [c', Finset.sum_ite_mem, Finset.inter_self] using hf

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mem_radicalCountBox
#print axioms VOA.DeligneAudit.SL4T.mem_radicalCountFiber
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCounts_position
#print axioms VOA.DeligneAudit.SL4T.mem_radicalSupportedCounts
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_le_fiber
#print axioms VOA.DeligneAudit.SL4T.radicalCountClosure_map_zero
#print axioms VOA.DeligneAudit.SL4T.cyclic_eq_radicalCountClosures
#print axioms VOA.DeligneAudit.SL4T.radicalCountFiltration_rank_le
