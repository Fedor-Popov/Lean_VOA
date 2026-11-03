import VOA.Classification.COne.OrbIcoVChannelRigidity

/-! Finite positive-mode Ward equations determine the actual channel
sequences from their leading state. This is the uniqueness side of the
specialization bridge. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco

def vacuumChannel : Submodule ℂ (orbifold ico).carrier :=
  (LinearMap.ker spinCasimir).comap (orbifold ico).carrier.subtype

theorem finite_ward_sequence_unique (P : Submodule ℂ (orbifold ico).carrier)
    (h R : ℕ) (c₁ c₂ : ℕ → ℂ)
    (rigid : ∀ n, 0 < n → n ≤ R → ∀ x : (orbifold ico).carrier,
      x ∈ P → x ∈ Wi.grading ((h+n : ℕ) : ℤ) →
      Wi.L 1 x = 0 → Wi.L 2 x = 0 → x = 0)
    (f g : ℕ → (orbifold ico).carrier)
    (hfP : ∀ n ≤ R, f n ∈ P) (hgP : ∀ n ≤ R, g n ∈ P)
    (hfg : ∀ n ≤ R, f n ∈ Wi.grading ((h+n : ℕ) : ℤ))
    (hgg : ∀ n ≤ R, g n ∈ Wi.grading ((h+n : ℕ) : ℤ))
    (hf₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (f n) = c₁ n • f (n-1))
    (hg₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (g n) = c₁ n • g (n-1))
    (hf₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (f n) = if 2 ≤ n then c₂ n • f (n-2) else 0)
    (hg₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (g n) = if 2 ≤ n then c₂ n • g (n-2) else 0)
    (hzero : f 0 = g 0) : ∀ n ≤ R, f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hz : n=0
    · simpa [hz] using hzero
    · have hnpos : 0 < n := by omega
      apply sub_eq_zero.mp
      apply rigid n hnpos hn (f n - g n) (P.sub_mem (hfP n hn) (hgP n hn))
        ((Wi.grading _).sub_mem (hfg n hn) (hgg n hn))
      · rw [map_sub, hf₁ n hnpos hn, hg₁ n hnpos hn, ih (n-1) (by omega) (by omega),
          sub_self]
      · rw [map_sub, hf₂ n hnpos hn, hg₂ n hnpos hn]
        by_cases htwo : 2 ≤ n
        · rw [if_pos htwo, if_pos htwo, ih (n-2) (by omega) (by omega), sub_self]
        · rw [if_neg htwo, if_neg htwo, sub_self]

theorem vacuum_ward_sequence_unique (R : ℕ) (hR : R < 100)
    (c₁ c₂ : ℕ → ℂ) (f g : ℕ → (orbifold ico).carrier)
    (hfC : ∀ n ≤ R, spinCasimir (f n : Sp) = 0)
    (hgC : ∀ n ≤ R, spinCasimir (g n : Sp) = 0)
    (hfg : ∀ n ≤ R, f n ∈ Wi.grading (n : ℤ))
    (hgg : ∀ n ≤ R, g n ∈ Wi.grading (n : ℤ))
    (hf₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (f n) = c₁ n • f (n-1))
    (hg₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (g n) = c₁ n • g (n-1))
    (hf₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (f n) = if 2 ≤ n then c₂ n • f (n-2) else 0)
    (hg₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (g n) = if 2 ≤ n then c₂ n • g (n-2) else 0)
    (hzero : f 0 = g 0) : ∀ n ≤ R, f n = g n := by
  apply finite_ward_sequence_unique vacuumChannel 0 R c₁ c₂ _ f g
    (fun n hn => hfC n hn) (fun n hn => hgC n hn) _ _ hf₁ hg₁ hf₂ hg₂ hzero
  · intro n hn hnR x hx hg h₁ h₂
    exact vacuum_channel_positive_rigidity (n : ℤ) (by exact_mod_cast hn) (by omega) x (by simpa using hg) hx h₁ h₂
  · simpa using hfg
  · simpa using hgg

set_option maxHeartbeats 1000000 in
theorem sixth_ward_sequence_unique (R : ℕ) (hR : R < 64)
    (c₁ c₂ : ℕ → ℂ) (f g : ℕ → (orbifold ico).carrier)
    (hfg : ∀ n ≤ R, f n ∈ Wi.grading ((36+n : ℕ) : ℤ))
    (hgg : ∀ n ≤ R, g n ∈ Wi.grading ((36+n : ℕ) : ℤ))
    (hf₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (f n) = c₁ n • f (n-1))
    (hg₁ : ∀ n, 0 < n → n ≤ R → Wi.L 1 (g n) = c₁ n • g (n-1))
    (hf₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (f n) = if 2 ≤ n then c₂ n • f (n-2) else 0)
    (hg₂ : ∀ n, 0 < n → n ≤ R →
      Wi.L 2 (g n) = if 2 ≤ n then c₂ n • g (n-2) else 0)
    (hzero : f 0 = g 0) : ∀ n ≤ R, f n = g n := by
  apply finite_ward_sequence_unique ⊤ 36 R c₁ c₂ _ f g
    (by intro n hn; exact Submodule.mem_top) (by intro n hn; exact Submodule.mem_top)
    hfg hgg hf₁ hg₁ hf₂ hg₂ hzero
  intro n hn hnR x _ hg h₁ h₂
  exact sixth_channel_positive_rigidity (36+n) (by omega) (by omega) x (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hg) h₁ h₂

end VOA.Classification.COne.OrbIcoV
