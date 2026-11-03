import VOA.DeligneAudit.SL4TCellBasic

/-! # The truncated Weyl bound on one successive cell quotient -/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.CVsl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V}

/-- The image of the next flag member in the ambient quotient is cyclic and satisfies
the balanced truncated Weyl bound. This image is the successive subquotient. -/
theorem cellFlag_step_bound (hS : SL2 E H F) (v : ℕ → V) (i r ν : ℕ)
    (hν : 1 ≤ ν) (hR : CellRelations E H F (cellFlag E H F v i) (v i) r ν) :
    FiniteDimensional ℂ ((cellFlag E H F v (i + 1)).map (cellFlag E H F v i).mkQ) ∧
      Module.finrank ℂ ((cellFlag E H F v (i + 1)).map (cellFlag E H F v i).mkQ) ≤
        ((bal r ν).map (· + 1)).prod := by
  let P := cellFlag E H F v i
  have hP := cellFlag_stable (E := E) (H := H) (F := F) v i
  let Eq : ℕ → Module.End ℂ (V ⧸ P) := fun s => P.mapQ P (E s) (hP.1 s)
  let Hq : ℕ → Module.End ℂ (V ⧸ P) := fun s => P.mapQ P (H s) (hP.2.1 s)
  let Fq : ℕ → Module.End ℂ (V ⧸ P) := fun s => P.mapQ P (F s) (hP.2.2 s)
  have hSq : SL2 Eq Hq Fq := SL2_quot hS P hP.1 hP.2.1 hP.2.2
  have hE : ∀ s, Eq s (P.mkQ (v i)) = 0 := by
    intro s
    change Submodule.Quotient.mk (E s (v i)) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hR.raising s)
  have hH : ∀ s, 1 ≤ s → Hq s (P.mkQ (v i)) = 0 := by
    intro s hs
    change Submodule.Quotient.mk (H s (v i)) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hR.cartan s hs)
  have hH0 : Hq 0 (P.mkQ (v i)) = (r : ℂ) • P.mkQ (v i) := by
    change P.mkQ (H 0 (v i)) = (r : ℂ) • P.mkQ (v i)
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hR.weight
  have hpow : ∀ n, P.mkQ ((F 0 ^ n) (v i)) = (Fq 0 ^ n) (P.mkQ (v i)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply]
        change Fq 0 (P.mkQ ((F 0 ^ n) (v i))) = _
        rw [ih]
  have hF0 : (Fq 0 ^ (r + 1)) (P.mkQ (v i)) = 0 := by
    rw [← hpow, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hR.integrable
  have htr : ∀ s, ν ≤ s → Fq s (P.mkQ (v i)) = 0 := by
    intro s hs
    change Submodule.Quotient.mk (F s (v i)) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hR.truncated s hs)
  have hst := Fspan_stable hSq.hEF hSq.hHF hE hH hH0
  have himage : (cellFlag E H F v (i + 1)).map P.mkQ = Fspan Fq (P.mkQ (v i)) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      apply currentSpan_le
      · rintro _ ⟨j, hj, rfl⟩
        change P.mkQ (v j) ∈ Fspan Fq (P.mkQ (v i))
        by_cases hji : j < i
        · have hz : P.mkQ (v j) = 0 :=
            (Submodule.Quotient.mk_eq_zero P).mpr (cellFlag_mem v hji)
          rw [hz]
          exact Submodule.zero_mem _
        · have he : j = i := by omega
          subst j
          exact self_mem _
      · refine ⟨?_, ?_, ?_⟩ <;> intro s x hx
        · change Eq s (P.mkQ x) ∈ Fspan Fq (P.mkQ (v i))
          exact hst.1 s hx
        · change Hq s (P.mkQ x) ∈ Fspan Fq (P.mkQ (v i))
          exact hst.2 s hx
        · change Fq s (P.mkQ x) ∈ Fspan Fq (P.mkQ (v i))
          exact Fspan_F _ s hx
    · rw [← map_Fspan P.mkQ (fun _ _ => rfl) (v i)]
      exact Submodule.map_mono (Fspan_le_of_stable
        (cellFlag_stable v (i + 1)).2.2 (cellFlag_mem v (by omega)))
  rw [himage]
  exact tw_bound hSq hE hH ⟨(r : ℂ), hH0⟩ hν hF0 htr

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.cellFlag_step_bound
