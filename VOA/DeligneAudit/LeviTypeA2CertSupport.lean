import VOA.DeligneAudit.LeviTypeA2CertKeys

/-! A degree cutoff for each radical key and a finite key box. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule
    VOA.AffineSl3.bracketTable V) (w : V)

private theorem radicalWord_comm (i : Fin 2) (s : ℕ)
    (l : List (Fin 2 × ℕ)) :
    a2RadicalOp ρ i s * radicalWord (a2RadicalOp ρ) l =
      radicalWord (a2RadicalOp ρ) l * a2RadicalOp ρ i s := by
  induction l with
  | nil => simp [radicalWord]
  | cons x l ih =>
      rcases x with ⟨j, t⟩
      change a2RadicalOp ρ i s *
        (a2RadicalOp ρ j t * radicalWord (a2RadicalOp ρ) l) =
        (a2RadicalOp ρ j t * radicalWord (a2RadicalOp ρ) l) *
          a2RadicalOp ρ i s
      calc
        _ = (a2RadicalOp ρ i s * a2RadicalOp ρ j t) *
              radicalWord (a2RadicalOp ρ) l := by rw [mul_assoc]
        _ = (a2RadicalOp ρ j t * a2RadicalOp ρ i s) *
              radicalWord (a2RadicalOp ρ) l := by
                rw [a2RadicalOp_comm]
        _ = a2RadicalOp ρ j t *
              (a2RadicalOp ρ i s * radicalWord (a2RadicalOp ρ) l) := by
                rw [mul_assoc]
        _ = _ := by rw [ih, mul_assoc]

private theorem radicalWord_high_zero (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) (l : List (Fin 2 × ℕ))
    (hl : ∃ x ∈ l, p + q ≤ x.2) :
    radicalWord (a2RadicalOp ρ) l • w = 0 := by
  induction l with
  | nil => simp at hl
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      obtain ⟨y, hy, hys⟩ := hl
      rcases List.mem_cons.mp hy with hxy | hyl
      · subst y
        change (a2RadicalOp ρ i s * radicalWord (a2RadicalOp ρ) l) • w = 0
        rw [radicalWord_comm, mul_smul]
        have hzero : a2RadicalOp ρ i s • w = 0 := by
          fin_cases i
          · simpa [a2RadicalOp] using
              a2_simple_mode_zero ρ w p q h 0 s (by change p ≤ s; omega)
          · simpa [a2RadicalOp] using
              a2_compound_mode_zero ρ w p q h s hys
        rw [hzero, smul_zero]
      · change (a2RadicalOp ρ i s * radicalWord (a2RadicalOp ρ) l) • w = 0
        rw [mul_smul, ih ⟨y, hyl, hys⟩, smul_zero]

private theorem sum_modes_le (B : ℕ) (l : List (Fin 2 × ℕ))
    (h : ∀ x ∈ l, x.2 < B) : (l.map Prod.snd).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx : x.2 < B := h x (by simp)
      have ht : ∀ y ∈ l, y.2 < B := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := ih ht
      rw [Nat.succ_mul]
      omega

/-- Above the mode box for a fixed radical length, the key layer vanishes. -/
theorem a2KeyLayer_eq_bot_of_degree_gt (p q : ℕ) (k : A2RadicalKey)
    (h : A2LocalWeylRel ρ w p q)
    (hk : (p + q) * (k.d₁ + k.d₂) < k.degree) :
    a2KeyLayer ρ w k = ⊥ := by
  rw [a2KeyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, _, _, hdegree, hlen, rfl⟩ := hz
  have hbad : ∃ x ∈ l, p + q ≤ x.2 := by
    by_contra hn
    have hall : ∀ x ∈ l, x.2 < p + q := by
      intro x hx
      have hnot : ¬ p + q ≤ x.2 := by
        intro hle
        exact hn ⟨x, hx, hle⟩
      omega
    have hs := sum_modes_le (p + q) l hall
    have hs' : k.degree ≤ (p + q) * (k.d₁ + k.d₂) := by
      simpa only [hlen, hdegree, Nat.mul_comm] using hs
    omega
  rw [radicalWord_high_zero ρ w p q h l hbad]
  exact Submodule.zero_mem _

/-- A concrete finite search box once both radical letter counts are bounded. -/
def a2KeyBox (p q : ℕ) : Finset A2RadicalKey :=
  (Finset.range (p + 1)).biUnion fun d₁ =>
    (Finset.range (p + q + 1)).biUnion fun d₂ =>
      (Finset.range ((p + q) * (2 * p + q) + 1)).image
        fun degree => ⟨d₁, d₂, degree⟩

theorem mem_a2KeyBox (p q : ℕ) (k : A2RadicalKey)
    (h₁ : k.d₁ ≤ p) (h₂ : k.d₂ ≤ p + q)
    (hdeg : k.degree ≤ (p + q) * (2 * p + q)) :
    k ∈ a2KeyBox p q := by
  unfold a2KeyBox
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₁, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₂, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨k.degree, Finset.mem_range.mpr (by omega), by cases k; rfl⟩

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyLayer_eq_bot_of_degree_gt
#print axioms VOA.DeligneAudit.A3Sector.mem_a2KeyBox
