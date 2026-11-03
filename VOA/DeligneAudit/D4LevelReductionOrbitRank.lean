import VOA.DeligneAudit.D4LevelReductionOrbitQuotient
import VOA.DeligneAudit.LeviTypeA3BasisLifts

/-! Quotient basis lifts reduce a key orbit to finitely many sl₄ cyclic modules. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)
variable (N : Submodule ℂ V)
variable (hN : ∀ a r, IsLevi a → N ≤ N.comap (ρ.op a r))

private theorem cyclic_le_invariantSubspace
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (Q : CurrentModule VOA.DeligneAudit.A3Sector.bracketTable W)
    (v : W) (T : Submodule ℂ W) (hv : v ∈ T)
    (hT : ∀ a r, T ≤ T.comap (Q.op a r)) :
    cycSubG Q v ≤ T := by
  rw [cycSubG, Submodule.span_le]
  rintro z ⟨l, rfl⟩
  induction l with
  | nil => exact hv
  | cons p l ih =>
      rcases p with ⟨a, r⟩
      exact hT a r ih

theorem keyOrbit_quotient_eq_basisOrbits
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey)
    (hpos : ∀ v ∈ keyLayer ρ w k, ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N) :
    let S := keyLayer ρ w k
    ∃ v : Fin (Module.finrank ℂ (S ⧸ N.comap S.subtype)) → S,
      (keyOrbit ρ w k).map N.mkQ =
        ⨆ j, cycSubG (quotRepG (leviCurrent ρ) N
          (quotientLevi_invariant ρ N hN)) (N.mkQ (v j : V)) := by
  let S := keyLayer ρ w k
  let Q := quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)
  letI : FiniteDimensional ℂ S := keyLayer_finite ρ w k
  obtain ⟨v, hv⟩ := VOA.DeligneAudit.A3Sector.a3_keyQuot_basis_lifts N S
  refine ⟨v, ?_⟩
  let D : Submodule ℂ (V ⧸ N) := ⨆ j, cycSubG Q (N.mkQ (v j : V))
  have hDinv : ∀ a r, D ≤ D.comap (Q.op a r) := by
    intro a r x hx
    refine Submodule.iSup_induction
      (p := fun j => cycSubG Q (N.mkQ (v j : V)))
      (motive := fun x => Q.op a r x ∈ D) hx ?_ ?_ ?_
    · intro j x hxj
      exact Submodule.mem_iSup_of_mem j
        (cycSubG_inv Q (N.mkQ (v j : V)) a r hxj)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact D.add_mem hx hy
  have hS : S ≤ D.comap N.mkQ := by
    apply hv.trans
    apply sup_le
    · intro x hx
      have hz : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
      change N.mkQ x ∈ D
      rw [hz]
      exact D.zero_mem
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      change N.mkQ (v j : V) ∈ D
      exact Submodule.mem_iSup_of_mem j
        (by simpa using wordOp_mem_cycSubG Q (N.mkQ (v j : V)) [])
  have hle : (keyOrbit ρ w k).map N.mkQ ≤ D := by
    rw [keyOrbit_eq_iSup_vectorOrbit, Submodule.map_iSup]
    apply iSup_le
    intro x
    rw [keyVectorOrbit_quotient_eq_cyclic ρ w m N hN h k x.property
      (hpos x x.property)]
    exact cyclic_le_invariantSubspace Q (N.mkQ (x : V)) D (hS x.property) hDinv
  have hge : D ≤ (keyOrbit ρ w k).map N.mkQ := by
    apply iSup_le
    intro j
    rw [← keyVectorOrbit_quotient_eq_cyclic ρ w m N hN h k (v j).property
      (hpos (v j) (v j).property)]
    apply Submodule.map_mono
    rw [keyOrbit_eq_iSup_vectorOrbit]
    exact le_iSup (fun x : {x : V // x ∈ S} => keyVectorOrbit ρ x.val) (v j)
  exact le_antisymm hle hge

theorem keyOrbit_quotient_rank_le
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (L : ℕ)
    (hpos : ∀ v ∈ keyLayer ρ w k, ∀ r, 0 < r → ρ.op (0 : Fin 28) r v ∈ N)
    (hbound : ∀ v ∈ keyLayer ρ w k,
      FiniteDimensional ℂ
        (cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) (N.mkQ v)) ∧
      Module.finrank ℂ
        (cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) (N.mkQ v)) ≤
          L) :
    let S := keyLayer ρ w k
    FiniteDimensional ℂ ((keyOrbit ρ w k).map N.mkQ) ∧
      Module.finrank ℂ ((keyOrbit ρ w k).map N.mkQ) ≤
        L * Module.finrank ℂ (S ⧸ N.comap S.subtype) := by
  let S := keyLayer ρ w k
  let n := Module.finrank ℂ (S ⧸ N.comap S.subtype)
  obtain ⟨v, hv⟩ := keyOrbit_quotient_eq_basisOrbits ρ w m N hN h k hpos
  let O : Fin n → Submodule ℂ (V ⧸ N) :=
    fun j => cycSubG (quotRepG (leviCurrent ρ) N (quotientLevi_invariant ρ N hN)) (N.mkQ (v j : V))
  have hcyc (j : Fin n) :
      FiniteDimensional ℂ (O j) ∧ Module.finrank ℂ (O j) ≤ L := by
    exact hbound (v j) (v j).property
  have haux (s : Finset (Fin n)) :
      FiniteDimensional ℂ (s.sup O : Submodule ℂ (V ⧸ N)) ∧
        Module.finrank ℂ (s.sup O : Submodule ℂ (V ⧸ N)) ≤
          ∑ j ∈ s, L := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨by simpa using
          (inferInstance : FiniteDimensional ℂ (⊥ : Submodule ℂ (V ⧸ N))),
          by
            have hz : (∅ : Finset (Fin n)).sup O = ⊥ := rfl
            rw [hz, finrank_bot]
            simp⟩
    | @insert j s hj ih =>
        haveI : FiniteDimensional ℂ (O j) := (hcyc j).1
        haveI : FiniteDimensional ℂ (s.sup O : Submodule ℂ (V ⧸ N)) := ih.1
        rw [Finset.sup_insert, Finset.sum_insert hj]
        exact ⟨inferInstance,
          (Submodule.finrank_add_le_finrank_add_finrank (O j) (s.sup O)).trans
            (Nat.add_le_add (hcyc j).2 ih.2)⟩
  have hall := haux Finset.univ
  have heq : (Finset.univ : Finset (Fin n)).sup O =
      (keyOrbit ρ w k).map N.mkQ := by
    simpa [O, Finset.sup_eq_iSup] using hv.symm
  rw [heq] at hall
  refine ⟨hall.1, ?_⟩
  simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
    Nat.mul_comm] using hall.2

end
end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_quotient_eq_basisOrbits

#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_quotient_rank_le
