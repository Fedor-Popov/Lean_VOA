/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionFiniteGLen
import VOA.DeligneAudit.DeligneFusionUnivGSector

/-!
# Splitting `FusionTotalBoundG`

the named input `FusionTotalBoundG S` (`DeligneFusionUnivGSector`) is the conjunction of

* `FusionTotalFinG S`: the degree pieces `cycDeg ρ w b` are finite-dimensional, and
* `FusionTotalDimG S`: the total dimension is at most `(dim 𝔤)^m`

(`fusionTotalBoundG_iff`). The finiteness clause is **proved** from the table facts
`FiniteTableG S` (`fusionTotalFinG_of_table`), so

`fusionTotalBoundG_of_dim : FiniteTableG S → FusionTotalDimG S → FusionTotalBoundG S`,

and every type's residual is the bare dimension bound. `finiteTableG_of_cert` builds
`FiniteTableG S` from a nilpotency certificate (`certValid`, a `Bool` check on the integer
structure constants and the weights), discharged per type by `decide +kernel`.
-/

namespace VOA.DeligneAudit.FiniteG

open Finset VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG

noncomputable section

variable (S : DeligneSectorData)

/-- **The finiteness clause** of `FusionTotalBoundG`. -/
def FusionTotalFinG : Prop :=
  ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → ∀ b, FiniteDimensional ℂ (cycDeg ρ w b)

/-- **The bare dimension bound** `dim ≤ (dim 𝔤)^m` (the residual named input). -/
def FusionTotalDimG : Prop :=
  ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V) (w : V),
    LocalWeylRelG S ρ w m → ∀ B : ℕ, ∑ b ∈ Finset.range B, Module.finrank ℂ (cycDeg ρ w b) ≤ S.n ^ m

theorem fusionTotalBoundG_iff : FusionTotalBoundG S ↔ FusionTotalFinG S ∧ FusionTotalDimG S :=
  ⟨fun h => ⟨fun m V _ _ ρ w hW => (h m V ρ w hW).1, fun m V _ _ ρ w hW => (h m V ρ w hW).2⟩,
    fun h m V _ _ ρ w hW => ⟨h.1 m V ρ w hW, h.2 m V ρ w hW⟩⟩

variable {S}

/-- **The finiteness clause is proved** from the table facts. -/
theorem fusionTotalFinG_of_table (T : FiniteTableG S) : FusionTotalFinG S :=
  fun _ _ _ _ _ _ hW b => cycDeg_finiteDimensionalG T hW b

/-- **`FusionTotalBoundG` reduces to the bare dimension bound.** -/
theorem fusionTotalBoundG_of_dim (T : FiniteTableG S) (h : FusionTotalDimG S) :
    FusionTotalBoundG S :=
  (fusionTotalBoundG_iff S).mpr ⟨fusionTotalFinG_of_table T, h⟩

/-! ## Tables from certificates -/

section Cert

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule S.f V} {w : V} {m : ℕ}

theorem known_raising (hW : LocalWeylRelG S ρ w m) {c : Fin S.n} (hc : S.raising c) :
    Known ρ w c :=
  ⟨1, by rw [pow_one]; exact hW.raising c hc 0⟩

theorem known_lowering (hW : LocalWeylRelG S ρ w m) {c : Fin S.n} (hc : S.lowering c) :
    Known ρ w c :=
  ⟨m * S.lowExp c + 1, by rw [Module.End.pow_apply]; exact hW.lowering c hc⟩

end Cert

/-- Nonzero structure constants from an integer table. -/
theorem fnz_of_table {fz : Fin S.n → Fin S.n → Fin S.n → ℤ} (hfz : ∀ a b c, S.f a b c = fz a b c) :
    ∀ a b c, (fz a b c != 0) = true → S.f a b c ≠ 0 := by
  intro a b c h
  rw [hfz]
  simp only [bne_iff_ne, ne_eq] at h
  exact_mod_cast h

/-- **`FiniteTableG` from a certificate**: `kn` marks raising or simple lowering letters, the
certificate is valid, and every low letter is reached and has nonzero weight. -/
theorem finiteTableG_of_cert {fnz : Fin S.n → Fin S.n → Fin S.n → Bool}
    (hfz : ∀ a b c, fnz a b c = true → S.f a b c ≠ 0) (kn : Fin S.n → Bool) (cert : List (Step S.n))
    (hkn : ∀ c, kn c = true → S.raising c ∨ S.lowering c) (hv : certValid S.wt fnz kn cert = true)
    (hcov : ∀ c, (certKnown kn cert c && !wEqB (S.wt c) 0) = true ∨
      S.raising c ∨ S.cartan c ∨ S.cartanN c) :
    FiniteTableG S where
  wt_ne c hc h := by
    rcases hcov c with h1 | h1
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      rw [(wEqB_iff _ _).mpr h] at h1
      exact Bool.noConfusion h1.2
    · exact hc h1
  nil m V _ _ ρ w hW c hc := by
    refine known_of_certValid ρ hfz cert kn (fun c hc => ?_) hv c ?_
    · rcases hkn c hc with h | h
      · exact known_raising hW h
      · exact known_lowering hW h
    · rcases hcov c with h1 | h1
      · simp only [Bool.and_eq_true] at h1; exact h1.1
      · exact absurd h1 hc

end

end VOA.DeligneAudit.FiniteG

section AxiomAudit
#print axioms VOA.DeligneAudit.FiniteG.fusionTotalBoundG_iff
#print axioms VOA.DeligneAudit.FiniteG.fusionTotalBoundG_of_dim
#print axioms VOA.DeligneAudit.FiniteG.finiteTableG_of_cert
end AxiomAudit
