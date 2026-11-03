import VOA.DeligneAudit.DeligneFusionD1SiteGCyclic

/-! # Actual coadjoint weight support and simple-root nilpotence at the new site -/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.DeligneSector

noncomputable section

variable (S : DeligneSectorData)

def CoSupport (μ : Fin S.R → ℤ) (v : Co S.n) : Prop :=
  ∀ c, S.wt c ≠ μ → v c = 0

theorem coOp_support {μ : Fin S.R → ℤ} {v : Co S.n} (hv : CoSupport S μ v) (c : Fin S.n) :
    CoSupport S (μ - S.wt c) (coOp S.f c v) := by
  intro y hy
  rw [coOp_apply]
  change -(∑ d, S.f c y d * v d) = 0
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro d _
  by_cases hd : S.wt d = μ
  · have hf : S.wt d ≠ S.wt c + S.wt y := by
      intro he
      apply hy
      rw [hd] at he
      funext i
      have hi := congrFun he i
      change μ i = S.wt c i + S.wt y i at hi
      change S.wt y i = μ i - S.wt c i
      omega
    rw [S.table_wt c y d hf, zero_mul]
  · rw [hv d hd, mul_zero]

theorem delta_support : CoSupport S (S.wt S.c₀) (Pi.single S.c₀ 1) := by
  intro c hc
  have hne : S.c₀ ≠ c := by rintro rfl; exact hc rfl
  simp [Pi.single_apply, hne]

theorem iterate_support (i : Fin S.n) (k : ℕ) :
    CoSupport S (S.wt S.c₀ - k • S.wt i) ((coOp S.f i)^[k] (Pi.single S.c₀ 1)) := by
  induction k with
  | zero => simpa using delta_support S
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hh := coOp_support S ih i
      have he : S.wt S.c₀ - k • S.wt i - S.wt i =
          S.wt S.c₀ - (k + 1) • S.wt i := by rw [add_smul, one_smul]; abel
      simpa only [he] using hh

/-- The existing sector weight exclusion proves actual simple-root
nilpotence on the coadjoint highest vector. -/
theorem coOp_lowering_nil (i : Fin S.n) (hi : S.lowering i) :
    (coOp S.f i)^[S.lowExp i + 1] (Pi.single S.c₀ 1) = 0 := by
  funext c
  apply iterate_support S i (S.lowExp i + 1) c
  simpa only [Fin.sum_univ_one, one_smul, one_mul] using
    S.lowering_noweight i hi 1 (fun _ => c)

theorem zeroOp_iterate (i : Fin S.n) (k : ℕ) (v : Co S.n) :
    (zeroOp S.f i)^[k] (inCo v) = inCo ((coOp S.f i)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

theorem site_lowering_nil (i : Fin S.n) (hi : S.lowering i) :
    (zeroOp S.f i)^[S.lowExp i + 1] (w S.c₀) = 0 := by
  change (zeroOp S.f i)^[S.lowExp i + 1] (inCo (Pi.single S.c₀ 1)) = 0
  rw [zeroOp_iterate, coOp_lowering_nil S i hi, map_zero]

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.site_lowering_nil
