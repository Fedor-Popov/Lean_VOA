import VOA.DeligneAudit.D4LeviKSDemazureRank

/-! High-current images on the cyclic level-one D4 module. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- The linear span of the selected high-current images of a subspace. -/
def currentTail (S : Submodule ℂ V) (colours : Set (Fin 28)) (N : ℕ) :
    Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ c ∈ colours, ∃ r, N ≤ r ∧
    ∃ v ∈ S, z = ρ.op c r v}

theorem currentTail_contains (S : Submodule ℂ V) (colours : Set (Fin 28))
    (N : ℕ) {c : Fin 28} (hc : c ∈ colours) {r : ℕ} (hr : N ≤ r)
    {v : V} (hv : v ∈ S) : ρ.op c r v ∈ currentTail ρ S colours N :=
  Submodule.subset_span ⟨c, hc, r, hr, v, hv, rfl⟩

theorem currentTail_mono_colours (S : Submodule ℂ V) (N : ℕ)
    {colours colours' : Set (Fin 28)} (h : colours ⊆ colours') :
    currentTail ρ S colours N ≤ currentTail ρ S colours' N := by
  apply Submodule.span_mono
  rintro z ⟨c, hc, r, hr, v, hv, rfl⟩
  exact ⟨c, h hc, r, hr, v, hv, rfl⟩

/-- All high D4 currents acting on the cyclic module. -/
def fullCurrentTail (w : V) (N : ℕ) : Submodule ℂ V :=
  currentTail ρ (cycSubG ρ w) Set.univ N

/-- High currents of the full node-one reductive Levi, including its centre. -/
def leviCurrentTail (w : V) (N : ℕ) : Submodule ℂ V :=
  currentTail ρ (cycSubG ρ w) {c | IsLevi c} N

theorem leviCurrentTail_le_full (w : V) (N : ℕ) :
    leviCurrentTail ρ w N ≤ fullCurrentTail ρ w N :=
  currentTail_mono_colours ρ _ _ (Set.subset_univ _)

/-- Closure of the full reductive Levi in the fixed D4 colour basis. -/
theorem reductiveLevi_bracket_support (a b c : Fin 28)
    (ha : IsLevi a) (hb : IsLevi b) (hc : ¬ IsLevi c) :
    D4sector.f a b c = 0 := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hcheck : ∀ i j : Fin 16,
      (br (leviIndex i) (leviIndex j)).all
        (fun p => decide (∃ k : Fin 16, (leviIndex k).val = p.1)) = true := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  have hzero : VOA.DeligneAudit.DeligneSector.Sparse.sget
      (br (leviIndex i) (leviIndex j)) c = 0 := by
    by_contra hn
    obtain ⟨p, hp, hpc⟩ :=
      VOA.DeligneAudit.DeligneSector.Sparse.exists_of_sget_ne_zero hn
    have hh := hcheck i j
    simp only [List.all_eq_true, decide_eq_true_eq] at hh
    obtain ⟨k, hk⟩ := hh p hp
    exact hc ⟨k, Fin.ext (hk.trans hpc)⟩
  simpa [D4sector, fD4, VOA.DeligneAudit.DeligneSector.Sparse.fC,
    VOA.DeligneAudit.DeligneSector.Sparse.fZ] using
      congrArg (fun n : ℤ => (n : ℂ)) hzero

/-- The high Levi images form a Levi current submodule. -/
theorem leviCurrentTail_stable (w : V) (N : ℕ) (a : Fin 28) (s : ℕ)
    (ha : IsLevi a) {v : V} (hv : v ∈ leviCurrentTail ρ w N) :
    ρ.op a s v ∈ leviCurrentTail ρ w N := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨b, hb, r, hr, u, hu, rfl⟩ := hz
      rw [sub_eq_iff_eq_add.mp (ρ.comm a b s r u)]
      apply Submodule.add_mem
      · apply Submodule.sum_mem
        intro c _
        by_cases hc : IsLevi c
        · exact (leviCurrentTail ρ w N).smul_mem _
            (currentTail_contains ρ _ _ N hc (by omega) hu)
        · rw [reductiveLevi_bracket_support a b c ha hb hc, zero_smul]
          exact Submodule.zero_mem _
      · exact currentTail_contains ρ _ _ N hb hr (cycSubG_inv ρ w a s hu)
  | zero => simpa using (leviCurrentTail ρ w N).zero_mem
  | add x y _ _ hx hy => simpa using (leviCurrentTail ρ w N).add_mem hx hy
  | smul c x _ hx => simpa using (leviCurrentTail ρ w N).smul_mem c hx

/-- Levi words preserve the high Levi images. -/
theorem leviCurrentTail_word (w : V) (N : ℕ) (l : List (Fin 28 × ℕ))
    (hl : l.Forall (fun x => IsLevi x.1))
    {v : V} (hv : v ∈ leviCurrentTail ρ w N) :
    wordOp ρ l v ∈ leviCurrentTail ρ w N := by
  induction l with
  | nil => exact hv
  | cons a l ih =>
      simp only [List.forall_cons] at hl
      exact leviCurrentTail_stable ρ w N a.1 a.2 hl.1 (ih hl.2)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_contains
#print axioms VOA.DeligneAudit.D4LevelReduction.currentTail_mono_colours
#print axioms VOA.DeligneAudit.D4LevelReduction.leviCurrentTail_le_full
#print axioms VOA.DeligneAudit.D4LevelReduction.reductiveLevi_bracket_support
#print axioms VOA.DeligneAudit.D4LevelReduction.leviCurrentTail_stable
#print axioms VOA.DeligneAudit.D4LevelReduction.leviCurrentTail_word
