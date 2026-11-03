import VOA.DeligneAudit.D4FusionToroidalFilt

/-!
# The high-mode word filtration and toroidal-module interface

This file constructs the decreasing filtration by the number of letters whose mode is at
least `m`, and records its behavior under prepending. It also defines toroidal modules and
their word operators. No dimension or surjectivity assertion is made.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n : ℕ}

/-- Number of letters with mode at least `m`. -/
def tmWeight (m : ℕ) : List (Ltr n) → ℕ
  | [] => 0
  | x :: l => (if m ≤ x.2 then 1 else 0) + tmWeight m l

theorem tmWeight_eq_filt (m : ℕ) : ∀ l : List (Ltr n),
    tmWeight m l = FusionToroidal.tmWeight m l
  | [] => by simp [tmWeight, FusionToroidal.tmWeight]
  | x :: l => by
      rw [tmWeight, FusionToroidal.tmWeight_cons, tmWeight_eq_filt m l]
      omega

/-- A single letter of mode `2*m` still has only one high-letter unit. -/
theorem tmWeight_double_mode (m : ℕ) (hm : 1 ≤ m) (c : Fin n) :
    tmWeight m [(c, 2 * m)] = 1 := by
  simp [tmWeight, show m ≤ 2 * m by omega]

/-- Hence the requested `u`-degree-two shift is not the word-count shift. -/
theorem double_mode_not_two (m : ℕ) (hm : 1 ≤ m) (c : Fin n) :
    ¬ 2 ≤ tmWeight m [(c, 2 * m)] := by
  rw [tmWeight_double_mode m hm c]
  omega

/-- Formal words with at least `j` high-mode letters. -/
def T (m j : ℕ) : Submodule ℂ (FreeW n) :=
  Submodule.span ℂ {v | ∃ l, j ≤ tmWeight m l ∧ v = sw l}

theorem T_mono (m : ℕ) {j k : ℕ} (h : j ≤ k) : T (n := n) m k ≤ T m j := by
  apply Submodule.span_mono
  rintro v ⟨l, hl, rfl⟩
  exact ⟨l, h.trans hl, rfl⟩

theorem T_cons (m j : ℕ) (x : Ltr n) :
    T m j ≤ (T m (j + if m ≤ x.2 then 1 else 0)).comap (consL x) := by
  rw [T, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  change consL x (sw l) ∈ T m (j + if m ≤ x.2 then 1 else 0)
  rw [consL_sw]
  apply Submodule.subset_span
  refine ⟨x :: l, ?_, rfl⟩
  simp only [tmWeight]
  omega

theorem sw_mem_T (m j : ℕ) (l : List (Ltr n))
    (h : j ≤ tmWeight m l) : sw l ∈ T m j :=
  Submodule.subset_span ⟨l, h, rfl⟩

theorem T_eq_filt (m j : ℕ) :
    T (n := n) m j = FusionToroidal.Tfree m j := by
  apply le_antisymm
  · rw [T, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact FusionToroidal.sw_mem_Tfree m j l
      (by rw [← tmWeight_eq_filt]; exact hl)
  · rw [FusionToroidal.Tfree, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    exact sw_mem_T m j l (by rw [tmWeight_eq_filt]; exact hl)

theorem T_zero (m : ℕ) : T (n := n) m 0 = ⊤ := by
  apply top_unique
  intro v _
  suffices ∀ v : FreeW n, v ∈ T m 0 from this v
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | single l a =>
      have h := sw_mem_T (n := n) m 0 l (Nat.zero_le _)
      simpa [sw] using Submodule.smul_mem (T m 0) a h

/-- Image of the high-mode word filtration in the universal module. -/
def TU (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n) (m j : ℕ) :
    Submodule ℂ (UModG f R) := (T m j).map (Jrel f R).mkQ

theorem TU_eq_filt (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m j : ℕ) : TU f R m j = FusionToroidal.TU f R m j := by
  rw [TU, FusionToroidal.TU, T_eq_filt]

theorem TU_mono (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m : ℕ) {j k : ℕ} (h : j ≤ k) : TU f R m k ≤ TU f R m j :=
  Submodule.map_mono (T_mono m h)

theorem TU_zero (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m : ℕ) : TU f R m 0 = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (Jrel f R) x
  exact ⟨v, by rw [T_zero]; trivial, rfl⟩

theorem TU_cons (f : Fin n → Fin n → Fin n → ℂ) (R : RelSpec n)
    (m j : ℕ) (x : Ltr n) :
    TU f R m j ≤
      (TU f R m (j + if m ≤ x.2 then 1 else 0)).comap (opU f R x) := by
  rw [TU, T, Submodule.map_span, Submodule.span_le]
  rintro v ⟨u, ⟨l, hl, rfl⟩, rfl⟩
  change opU f R x (Submodule.Quotient.mk (sw l)) ∈
    TU f R m (j + if m ≤ x.2 then 1 else 0)
  rw [opU_mk]
  exact Submodule.mem_map_of_mem (sw_mem_T m _ (x :: l) (by
    simp only [tmWeight]
    omega))

/-- A module over the truncated toroidal symbol algebra. The `u` degree is unbounded. -/
structure ToroidalModule (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  op : Fin n → ℕ → ℕ → V →ₗ[ℂ] V
  high_zero : ∀ c i s, m ≤ s → op c i s = 0
  comm : ∀ a b i j r s v,
    op a i r (op b j s v) - op b j s (op a i r v) =
      if r + s < m then ∑ e, f a b e • op e (i + j) (r + s) v else 0

variable {f : Fin n → Fin n → Fin n → ℂ} {m : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A toroidal letter records colour, `u` degree, and `t` mode. -/
abbrev TLtr (n : ℕ) := Fin n × ℕ × ℕ

/-- Apply a list of toroidal symbols from right to left. -/
def wordOpT (ρ : ToroidalModule f m V) : List (TLtr n) → V → V
  | [], v => v
  | x :: l, v => ρ.op x.1 x.2.1 x.2.2 (wordOpT ρ l v)

/-- Total `u` degree of a toroidal word. -/
def uDeg : List (TLtr n) → ℕ
  | [] => 0
  | x :: l => x.2.1 + uDeg l

/-- The cyclic piece at fixed total `u` degree. -/
def cycDegT (ρ : ToroidalModule f m V) (w : V) (i : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l, uDeg l = i ∧ v = wordOpT ρ l w}

end

end VOA.DeligneAudit.Toroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.T_cons
#print axioms VOA.DeligneAudit.Toroidal.TU_cons
#print axioms VOA.DeligneAudit.Toroidal.TU_eq_filt
#print axioms VOA.DeligneAudit.Toroidal.double_mode_not_two
end AxiomAudit
