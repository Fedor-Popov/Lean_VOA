import VOA.DeligneAudit.D4FusionKernelGeneric
import VOA.DeligneAudit.D4FusionContactTruncation
import VOA.DeligneAudit.D4FusionContactZero
import VOA.DeligneAudit.DeligneFusionFiniteGD4

/-! Kus–Littelmann (PJM 278, 2015), step 1, for D4 and λ = θ: the truncated Weyl
module W(mθ, m) is the level-one Demazure module D(1, mθ) truncated by g ⊗ t^m
(Theorem 4.1 at λ⁰ = 0, where the extra Demazure relations are redundant). In
relation form: a cyclic module satisfies the local-Weyl/fusion relations of
multiplicity m iff its generator satisfies the D(1, mθ) relations `ravFam m 0`
and f_θ ⊗ t^m kills it. Consequently the total-dimension input T is equivalent
to the same bound stated for truncated Demazure modules. -/
namespace VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule D4sector.f V} {w : V}

/-- Changing only the f_θ fusion mode of `ravSpec`, given that mode kills the generator. -/
theorem sat_ravSpec_fusionMode {k d d' : ℕ} (h : Sat D4sector.f ρ w (ravSpec D4sector k d))
    (hc : ρ.op D4sector.c₀ d' w = 0) : Sat D4sector.f ρ w (ravSpec D4sector k d') where
  tail t ht := by
    simp only [ravSpec, Set.mem_setOf_eq] at ht
    rcases ht with h1 | h2 | h3 | ⟨x, hx, rfl⟩ | h5
    · exact h.tail t (by simp only [ravSpec, Set.mem_setOf_eq]; exact Or.inl h1)
    · exact h.tail t (by simp only [ravSpec, Set.mem_setOf_eq]; exact Or.inr (Or.inl h2))
    · exact h.tail t (by simp only [ravSpec, Set.mem_setOf_eq]; exact Or.inr (Or.inr (Or.inl h3)))
    · by_cases hx0 : x = D4sector.c₀
      · subst hx0
        simp only [if_true, wordOp]
        exact hc
      · simp only [if_neg hx0]
        exact h.tail [(x, k)] (by
          simp only [ravSpec, Set.mem_setOf_eq]
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx, by simp only [if_neg hx0]⟩))))
    · exact h.tail t (by
        simp only [ravSpec, Set.mem_setOf_eq]
        exact Or.inr (Or.inr (Or.inr (Or.inr h5))))
  eig q hq := h.eig q hq

theorem ravFam_zero_right (m : ℕ) : ravFam D4sector m 0 = ravSpec D4sector m (2 * m) := by
  simp only [ravFam, Nat.add_zero]

/-- **W(mθ, m) = D(1, mθ)/(g ⊗ t^m)**, in relation form, for every m ≥ 1. -/
theorem localWeylRelG_iff_demazure_trunc {m : ℕ} (hm : 1 ≤ m) :
    LocalWeylRelG D4sector ρ w m ↔
      (Sat D4sector.f ρ w (ravFam D4sector m 0) ∧ ρ.op D4sector.c₀ m w = 0) := by
  constructor
  · intro h
    have hs : Sat D4sector.f ρ w (ravSpec D4sector m m) := by
      rw [ravSpec_self]
      exact (localWeylRelG_iff D4sector ρ w m).mp h
    refine ⟨?_, D4FusionContact.localWeyl_high_kills hm h _ m le_rfl⟩
    rw [ravFam_zero_right]
    exact sat_ravSpec_fusionMode hs (D4FusionContact.localWeyl_high_kills hm h _ (2 * m) (by omega))
  · rintro ⟨hs, hc⟩
    rw [ravFam_zero_right] at hs
    apply (localWeylRelG_iff D4sector ρ w m).mpr
    rw [← ravSpec_self]
    exact sat_ravSpec_fusionMode hs hc

/-- **Input T on the Demazure side**: the total bound 28^m for every truncated
D(1, mθ)-module (m ≥ 1). -/
def TruncatedDemazureTotalDim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule D4sector.f V) (w : V),
    Sat D4sector.f ρ w (ravFam D4sector m 0) → ρ.op D4sector.c₀ m w = 0 →
      ∀ B : ℕ, ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ 28 ^ m

/-- The two forms of input T are equivalent. -/
theorem fusionTotalDimG_iff_truncatedDemazure :
    FiniteG.FusionTotalDimG D4sector ↔ TruncatedDemazureTotalDim := by
  constructor
  · intro hT m hm V _ _ ρ w hs hc B
    exact hT m V ρ w ((localWeylRelG_iff_demazure_trunc hm).mpr ⟨hs, hc⟩) B
  · intro hT m V _ _ ρ w h B
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using D4FusionContact.localWeyl_zero_total_dim h B
    · obtain ⟨hs, hc⟩ := (localWeylRelG_iff_demazure_trunc hm).mp h
      exact hT m hm V ρ w hs hc B

end VOA.DeligneAudit.UnivG
#print axioms VOA.DeligneAudit.UnivG.localWeylRelG_iff_demazure_trunc
#print axioms VOA.DeligneAudit.UnivG.fusionTotalDimG_iff_truncatedDemazure
