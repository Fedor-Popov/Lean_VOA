import VOA.DeligneAudit.D4FusionToroidalGarlandUniv
import VOA.DeligneAudit.D4FusionToroidalFusionD4RavFam

/-!
# Garland symbols `P^{(j)}_N` in the toroidal associated graded (★a, symbol level)

`P^{(j)}_N x := [z^N] f(z) g(z)^j x` with `f(z) = ∑_r (f_θ ⊗ t^r) z^r` (the `u`-degree-zero
letters) and `g(z) = ∑_s (f_θ ⊗ u t^s) z^s` (the `u`-degree-one letters), in any truncated
toroidal module (`Psym`).  These are the extra symbol relations of the toroidal
presentation.

**Proved here (`j = 1`, sharp range `N ≥ m − 1`):** `P^{(1)}_N` kills the graded generator of
`Gr(U_m)` (`garland_symbol_zero`).  The lift is the quadratic Garland element
`G_{2,N+m} v = ∑_{a+b=N+m} f_a f_b v = 0` of `D4FusionToroidalGarlandUniv`; for `N ≥ m − 1` it
has no `(u = 0, u = 0)` term, its `(u = 1, u = 0)` and `(u = 0, u = 1)` parts coincide by the
commutation of the `f_θ ⊗ t^i`, and its `(u ≥ 1, u ≥ 1)` part lies in the second filtration
step.  Hence `2 ·(u-degree-one part) ∈ TU 2`, whose symbol in grade one is zero.

**Not proved (named Props):** the symbols `P^{(j)}_N`, `j ≥ 2`, `N ≥ m − j` (`JprimeLeAnnGr`),
and the fusion-side vanishing (★b) (`JprimeLeAnnF`).  For `j ≥ 2` the Garland element
`G_{j+1, N+jm}` has `u`-degree-one terms in the needed range (`N ≤ 2m − 2 − j`), so its
vanishing in `U_m` does not bound the `u`-degree-`j` symbol; the probe's lifts for `j ≥ 2` were
checked only in the fusion model.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

section Symbols

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ} {m : ℕ}
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `[z^s] g(z)^j x`, `g(z) = ∑_s (c₀ ⊗ u t^s) z^s`. -/
def gpow (ρ : ToroidalModule f m V) (c₀ : Fin n) : ℕ → ℕ → V → V
  | 0, s, x => if s = 0 then x else 0
  | j + 1, s, x => ∑ p ∈ Finset.antidiagonal s, ρ.op c₀ 1 p.1 (gpow ρ c₀ j p.2 x)

/-- The Garland symbol `P^{(j)}_N x = [z^N] f(z) g(z)^j x`. -/
def Psym (ρ : ToroidalModule f m V) (c₀ : Fin n) (j N : ℕ) (x : V) : V :=
  ∑ p ∈ Finset.antidiagonal N, ρ.op c₀ 0 p.1 (gpow ρ c₀ j p.2 x)

theorem gpow_one (ρ : ToroidalModule f m V) (c₀ : Fin n) (s : ℕ) (x : V) :
    gpow ρ c₀ 1 s x = ρ.op c₀ 1 s x := by
  simp only [gpow]
  rw [Finset.sum_eq_single (s, 0)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    rw [Finset.mem_antidiagonal] at hp
    have hb : b ≠ 0 := by
      intro hb
      exact hne (Prod.ext (by omega) hb)
    simp [hb]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

theorem Psym_one (ρ : ToroidalModule f m V) (c₀ : Fin n) (N : ℕ) (x : V) :
    Psym ρ c₀ 1 N x =
      ∑ p ∈ Finset.antidiagonal N, ρ.op c₀ 0 p.1 (ρ.op c₀ 1 p.2 x) := by
  simp only [Psym, gpow_one]

end Symbols

/-! ## The lift in `U_m` and the symbol in `Gr(U_m)` -/

section D4

variable (m : ℕ)

/-- Two-letter `f_θ`-words lie in the filtration step given by their symbol degree. -/
theorem d4_pair_mem (hm : 1 ≤ m) (a b j : ℕ) (hj : j ≤ a / m + b / m) :
    d4Ftheta m a (d4Ftheta m b (d4Gen m)) ∈ TU D4sector.f (ravFam D4sector m 0) m j := by
  have h := word_mem_shift D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm [(D4sector.c₀, a), (D4sector.c₀, b)] 0
    (wUG D4sector.f (ravFam D4sector m 0)) (by rw [TU_zero]; trivial)
  refine TU_mono _ _ _ ?_ h
  simpa only [symbolDegree, Nat.add_zero, Nat.zero_add] using hj

theorem d4_div_ge_one (hm : 1 ≤ m) (s : ℕ) : 1 ≤ (m + s) / m :=
  (Nat.le_div_iff_mul_le hm).mpr (by omega)

theorem d4_div_ge_one' (hm : 1 ≤ m) (r : ℕ) (hr : m ≤ r) : 1 ≤ r / m :=
  (Nat.le_div_iff_mul_le hm).mpr (by omega)

theorem d4_div_ge_two (hm : 1 ≤ m) (s : ℕ) (hs : m ≤ s) : 2 ≤ (m + s) / m :=
  (Nat.le_div_iff_mul_le hm).mpr (by omega)

/-- **The lift of `P^{(1)}_N` lies in the second filtration step** for `N ≥ m − 1`:
`∑_{r+s=N} f_r f_{m+s} v ∈ TU 2`. -/
theorem d4_lift_mem (hm : 1 ≤ m) (N : ℕ) (hN : m ≤ N + 1) :
    ∑ p ∈ Finset.antidiagonal N, d4Ftheta m p.1 (d4Ftheta m (m + p.2) (d4Gen m)) ∈
      TU D4sector.f (ravFam D4sector m 0) m 2 := by
  have hG := d4_garland_two m (N + m) (by omega)
  have hsplit : ∀ q ∈ Finset.antidiagonal (N + m),
      d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) =
        (if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) +
        (if m ≤ q.1 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) -
        (if m ≤ q.1 ∧ m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) := by
    intro q hq
    rw [Finset.mem_antidiagonal] at hq
    by_cases h1 : m ≤ q.1
    · by_cases h2 : m ≤ q.2
      · simp only [h1, h2, true_and, ↓reduceIte]
        abel
      · simp only [h1, h2, true_and, ↓reduceIte, zero_add, sub_zero]
    · by_cases h2 : m ≤ q.2
      · simp only [h1, h2, false_and, ↓reduceIte, add_zero, sub_zero]
      · omega
  have hsum : ∑ q ∈ Finset.antidiagonal (N + m), d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) =
      (∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) +
      (∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.1 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) -
      (∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.1 ∧ m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hsplit
  have hswap : (∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.1 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) =
      ∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]
    split_ifs
    · exact d4Ftheta_comm m q.2 q.1 (d4Gen m)
    · rfl
  have hC : (∑ q ∈ Finset.antidiagonal (N + m),
      if m ≤ q.1 ∧ m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) ∈
        TU D4sector.f (ravFam D4sector m 0) m 2 := by
    refine Submodule.sum_mem _ fun q _ => ?_
    split_ifs with h
    · refine d4_pair_mem m hm q.1 q.2 2 ?_
      have h1 := d4_div_ge_one' m hm q.1 h.1
      have h2 := d4_div_ge_one' m hm q.2 h.2
      omega
    · exact Submodule.zero_mem _
  have hA : (∑ q ∈ Finset.antidiagonal (N + m),
      if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) ∈
        TU D4sector.f (ravFam D4sector m 0) m 2 := by
    rw [hsum, hswap] at hG
    have h2 : (2 : ℂ) • (∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0) =
        ∑ q ∈ Finset.antidiagonal (N + m),
          if m ≤ q.1 ∧ m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0 := by
      rw [two_smul]
      exact sub_eq_zero.mp hG
    have := Submodule.smul_mem _ ((2 : ℂ)⁻¹) hC
    rwa [← h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at this
  have hX : ∑ p ∈ Finset.antidiagonal N, d4Ftheta m p.1 (d4Ftheta m (m + p.2) (d4Gen m)) =
      ∑ q ∈ Finset.antidiagonal (N + m),
        if m ≤ q.2 then d4Ftheta m q.1 (d4Ftheta m q.2 (d4Gen m)) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun p => (p.1, m + p.2)) (fun q => (q.1, q.2 - m)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      omega
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq
      simp only [Finset.mem_antidiagonal]
      omega
    · intro p _
      exact Prod.ext rfl (by change m + p.2 - m = p.2; omega)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq
      exact Prod.ext rfl (by change m + (q.2 - m) = q.2; omega)
    · intro p _
      rfl
  rw [hX]
  exact hA

/-- The homogeneous symbol map `TU j → grNumerator`, as a linear map. -/
def gradedSingleL (j : ℕ) :
    TU D4sector.f (ravFam D4sector m 0) m j →ₗ[ℂ]
      grNumerator D4sector.f (ravFam D4sector m 0) m where
  toFun y := gradedSingle D4sector.f (ravFam D4sector m 0) m j y.1 y.2
  map_add' y z := by
    apply Subtype.ext
    simp [gradedSingle, Finsupp.single_add]
  map_smul' a y := by
    apply Subtype.ext
    simp [gradedSingle, Finsupp.smul_single]

/-- The symbol in grade `j` of an element of `TU j`. -/
def symbL (j : ℕ) :
    TU D4sector.f (ravFam D4sector m 0) m j →ₗ[ℂ]
      Gr D4sector.f (ravFam D4sector m 0) m :=
  (grKernel D4sector.f (ravFam D4sector m 0) m).mkQ ∘ₗ gradedSingleL m j

theorem symbL_apply (j : ℕ) (y : TU D4sector.f (ravFam D4sector m 0) m j) :
    symbL m j y = (grKernel D4sector.f (ravFam D4sector m 0) m).mkQ
      (gradedSingle D4sector.f (ravFam D4sector m 0) m j y.1 y.2) := rfl

/-- An element of the next filtration step has zero symbol. -/
theorem symbL_zero (j : ℕ) (y : TU D4sector.f (ravFam D4sector m 0) m j)
    (hy : y.1 ∈ TU D4sector.f (ravFam D4sector m 0) m (j + 1)) : symbL m j y = 0 := by
  rw [symbL_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (gradedSingle_mem_kernel D4sector.f (ravFam D4sector m 0) m j y.1 hy)

theorem grToroidal_D4_op (hm : 1 ≤ m) (c : Fin 28) (i s : ℕ) :
    (grToroidal_D4 m hm).op c i s =
      grOp D4sector.f (ravFam D4sector m 0) m
        (highModeShift_D4 (ravFam D4sector m 0) m hm) c i s := rfl

theorem grGenerator_D4_eq :
    grGenerator D4sector.f (ravFam D4sector m 0) m =
      (grKernel D4sector.f (ravFam D4sector m 0) m).mkQ
        (gradedSingle D4sector.f (ravFam D4sector m 0) m 0
          (wUG D4sector.f (ravFam D4sector m 0)) (by rw [TU_zero]; trivial)) := rfl

/-- The pair `(c₀,0,r)(c₀,1,s)` on the graded generator is the grade-one symbol of
`f_r f_{m+s} v`, for all `r, s` (both sides vanish outside the truncation). -/
theorem d4_grOp_pair (hm : 1 ≤ m) (r s : ℕ) :
    (grToroidal_D4 m hm).op D4sector.c₀ 0 r ((grToroidal_D4 m hm).op D4sector.c₀ 1 s
      (grGenerator D4sector.f (ravFam D4sector m 0) m)) =
    symbL m 1 ⟨d4Ftheta m r (d4Ftheta m (m + s) (d4Gen m)),
      d4_pair_mem m hm r (m + s) 1 (le_add_left (d4_div_ge_one m hm s))⟩ := by
  by_cases hs : s < m
  · by_cases hr : r < m
    · rw [grToroidal_D4_op, grToroidal_D4_op, grGenerator_D4_eq,
        grOp_single D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 1 s 0 _ hs _,
        grOp_single D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 0 r (0 + 1) _ hr _,
        symbL_apply]
      congr 1
      apply Subtype.ext
      simp [gradedSingle, d4Ftheta, d4Gen]
    · rw [grToroidal_D4_op,
        grOp_high_zero D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 0 r
          (Nat.le_of_not_lt hr),
        LinearMap.zero_apply, symbL_zero]
      refine d4_pair_mem m hm r (m + s) 2 ?_
      have h1 := d4_div_ge_one' m hm r (Nat.le_of_not_lt hr)
      have h2 := d4_div_ge_one m hm s
      omega
  · rw [grToroidal_D4_op (c := D4sector.c₀) (i := 1) (s := s),
      grOp_high_zero D4sector.f (ravFam D4sector m 0) m _ D4sector.c₀ 1 s
        (Nat.le_of_not_lt hs),
      LinearMap.zero_apply, map_zero, symbL_zero]
    exact d4_pair_mem m hm r (m + s) 2
      (le_add_left (d4_div_ge_two m hm s (Nat.le_of_not_lt hs)))

/-- **(★a), `j = 1`, sharp range**: the Garland symbol `P^{(1)}_N` kills the graded
generator of `Gr(U_m)` for every `N ≥ m − 1`. -/
theorem garland_symbol_zero (hm : 1 ≤ m) (N : ℕ) (hN : m ≤ N + 1) :
    Psym (grToroidal_D4 m hm) D4sector.c₀ 1 N
      (grGenerator D4sector.f (ravFam D4sector m 0) m) = 0 := by
  rw [Psym_one, Finset.sum_congr rfl (fun p _ => d4_grOp_pair m hm p.1 p.2), ← map_sum]
  have hsum : (∑ p ∈ Finset.antidiagonal N,
      (⟨d4Ftheta m p.1 (d4Ftheta m (m + p.2) (d4Gen m)),
        d4_pair_mem m hm p.1 (m + p.2) 1 (le_add_left (d4_div_ge_one m hm p.2))⟩ :
          TU D4sector.f (ravFam D4sector m 0) m 1)) =
      ⟨∑ p ∈ Finset.antidiagonal N, d4Ftheta m p.1 (d4Ftheta m (m + p.2) (d4Gen m)),
        TU_mono _ _ _ (by omega) (d4_lift_mem m hm N hN)⟩ := by
    apply Subtype.ext
    simp
  rw [hsum]
  exact symbL_zero m 1 _ (d4_lift_mem m hm N hN)

end D4

/-! ## The package `J'_m` -/

section Package

/-- A symbol relation, read as a natural operation on every truncated toroidal module. -/
abbrev TRel (n : ℕ) (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ) :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V], ToroidalModule f m V → V → V

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ} {m : ℕ}

/-- The relation given by a toroidal word. -/
def wordRel (l : List (TLtr n)) : TRel n f m :=
  fun _ _ _ ρ x => wordOpT ρ l x

/-- The relation `P^{(j)}_N`. -/
def PsymRel (c₀ : Fin n) (j N : ℕ) : TRel n f m :=
  fun _ _ _ ρ x => Psym ρ c₀ j N x

variable (m)

/-- The symbols of the Ravinder tails of `ravFam D4sector m 0` (the ideal `J` of the probe). -/
def Jsymbols : Set (TRel 28 D4sector.f m) :=
  {ρ | ∃ t ∈ (ravFam D4sector m 0).tails, ρ = wordRel (symbolLetters m t)}

/-- `J'_m = J + ⟨P^{(j)}_N : 1 ≤ j ≤ m − 1, N ≥ m − j⟩`, the probe's uniform family. -/
def Jprime : Set (TRel 28 D4sector.f m) :=
  Jsymbols m ∪ {ρ | ∃ j N, 1 ≤ j ∧ j + 1 ≤ m ∧ m ≤ N + j ∧ ρ = PsymRel D4sector.c₀ j N}

/-- The `j = 1` part of `J'_m` (together with `J`): `P^{(1)}_N`, `N ≥ m − 1`. -/
def JprimeOne : Set (TRel 28 D4sector.f m) :=
  Jsymbols m ∪ {ρ | ∃ N, m ≤ N + 1 ∧ ρ = PsymRel D4sector.c₀ 1 N}

/-- Relations killing the graded generator of `Gr(U_m)`. -/
def annGr (hm : 1 ≤ m) : Set (TRel 28 D4sector.f m) :=
  {ρ | ρ _ (grToroidal_D4 m hm) (grGenerator D4sector.f (ravFam D4sector m 0) m) = 0}

/-- Relations killing the fusion-side graded highest vector. -/
def annF : Set (TRel 28 D4sector.f m) :=
  {ρ | ρ _ (D4Fusion.gradedAction m) (D4Fusion.gradedHighest m) = 0}

theorem JprimeOne_le_Jprime (hm : 2 ≤ m) : JprimeOne m ⊆ Jprime m := by
  rintro ρ (h | ⟨N, hN, rfl⟩)
  · exact Or.inl h
  · exact Or.inr ⟨1, N, le_rfl, hm, by omega, rfl⟩

/-- `J ⊆ Ann(g₀)` in `Gr(U_m)`: the tail symbols (`gr_tail_D4`). -/
theorem Jsymbols_le_annGr (hm : 1 ≤ m) : Jsymbols m ⊆ annGr m hm := by
  rintro ρ ⟨t, ht, rfl⟩
  exact gr_tail_D4 m hm t ht

/-- **`J'_m` at `j = 1` kills the graded generator of `Gr(U_m)`.** -/
theorem JprimeOne_le_annGr (hm : 1 ≤ m) : JprimeOne m ⊆ annGr m hm := by
  rintro ρ (h | ⟨N, hN, rfl⟩)
  · exact Jsymbols_le_annGr m hm h
  · exact garland_symbol_zero m hm N hN

/-- `J ⊆ Ann(v_F)` on the fusion side (`graded_ravFam_tail`). -/
theorem Jsymbols_le_annF (hm : 1 ≤ m) : Jsymbols m ⊆ annF m := by
  rintro ρ ⟨t, ht, rfl⟩
  exact D4Fusion.graded_ravFam_tail m hm t ht

/-- **Open (★a, `j ≥ 2`)**: the full family `J'_m` kills the graded generator of `Gr(U_m)`. -/
def JprimeLeAnnGr (hm : 1 ≤ m) : Prop := Jprime m ⊆ annGr m hm

/-- **Open (★b)**: the full family `J'_m` kills the fusion-side graded highest vector
(the probe reports `P^{(j)}_N v_F = 0 ⟺ N ≥ m − j`, machine-checked at `m = 2, 3`). -/
def JprimeLeAnnF : Prop := Jprime m ⊆ annF m

/-- **Open (★b, `j = 1`)**: `P^{(1)}_N v_F = 0` for `N ≥ m − 1`. -/
def PsymOneKillsFusion : Prop :=
  ∀ N, m ≤ N + 1 →
    Psym (D4Fusion.gradedAction m) D4sector.c₀ 1 N (D4Fusion.gradedHighest m) = 0

theorem JprimeOne_le_annF_of (hm : 1 ≤ m) (h : PsymOneKillsFusion m) :
    JprimeOne m ⊆ annF m := by
  rintro ρ (h' | ⟨N, hN, rfl⟩)
  · exact Jsymbols_le_annF m hm h'
  · exact h N hN

end Package

end

end VOA.DeligneAudit.Toroidal

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.d4_lift_mem
#print axioms VOA.DeligneAudit.Toroidal.d4_grOp_pair
#print axioms VOA.DeligneAudit.Toroidal.garland_symbol_zero
#print axioms VOA.DeligneAudit.Toroidal.JprimeOne_le_annGr
#print axioms VOA.DeligneAudit.Toroidal.Jsymbols_le_annF
#print axioms VOA.DeligneAudit.Toroidal.JprimeOne_le_annF_of
end AxiomAudit
