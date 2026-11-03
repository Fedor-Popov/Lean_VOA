import VOA.DeligneAudit.LeviTypeA3Keys

/-! Finite mode support for radical words at each fixed depth. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

private theorem radicalWord_comm (i : Fin 3) (s : ℕ)
    (l : List (Fin 3 × ℕ)) :
    radicalOp ρ i s * radicalWord (radicalOp ρ) l =
      radicalWord (radicalOp ρ) l * radicalOp ρ i s := by
  induction l with
  | nil => simp [radicalWord]
  | cons x l ih =>
      rcases x with ⟨j, t⟩
      change radicalOp ρ i s *
        (radicalOp ρ j t * radicalWord (radicalOp ρ) l) =
        (radicalOp ρ j t * radicalWord (radicalOp ρ) l) * radicalOp ρ i s
      calc
        _ = (radicalOp ρ i s * radicalOp ρ j t) *
              radicalWord (radicalOp ρ) l := by rw [mul_assoc]
        _ = (radicalOp ρ j t * radicalOp ρ i s) *
              radicalWord (radicalOp ρ) l := by rw [radicalOp_comm]
        _ = radicalOp ρ j t *
              (radicalOp ρ i s * radicalWord (radicalOp ρ) l) := by rw [mul_assoc]
        _ = _ := by rw [ih, mul_assoc]

private theorem radicalWord_high_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (l : List (Fin 3 × ℕ))
    (hl : ∃ x ∈ l, a + b + c ≤ x.2) :
    radicalWord (radicalOp ρ) l • w = 0 := by
  have hcut : ∀ i s, a + b + c ≤ s → radicalOp ρ i s • w = 0 := by
    intro i s hs
    change ρ.op (F i) s w = 0
    apply radical_mode_zero ρ w a b c
      (simple_mode_zero ρ w (weightABC a b c) h 0)
      (simple_mode_zero ρ w (weightABC a b c) h 1)
      (simple_mode_zero ρ w (weightABC a b c) h 2) i s
    fin_cases i <;> simp_all <;> omega
  induction l with
  | nil => simp at hl
  | cons x l ih =>
      rcases x with ⟨i, s⟩
      obtain ⟨y, hy, hys⟩ := hl
      rcases List.mem_cons.mp hy with hxy | hyl
      · subst y
        change (radicalOp ρ i s * radicalWord (radicalOp ρ) l) • w = 0
        rw [radicalWord_comm, mul_smul, hcut i s hys, smul_zero]
      · change (radicalOp ρ i s * radicalWord (radicalOp ρ) l) • w = 0
        rw [mul_smul, ih ⟨y, hyl, hys⟩, smul_zero]

private theorem sum_modes_le (B : ℕ) (l : List (Fin 3 × ℕ))
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

/-- A fixed key vanishes beyond the uniform mode-degree cutoff. -/
theorem a3KeyLayer_eq_bot_of_degree_gt (a b c : ℕ) (k : A3RadicalKey)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (hk : (a + b + c) * (k.d₁ + k.d₂ + k.d₃) < k.degree) :
    a3KeyLayer ρ w k = ⊥ := by
  rw [a3KeyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, _, _, _, hdegree, hlen, rfl⟩ := hz
  have hbad : ∃ x ∈ l, a + b + c ≤ x.2 := by
    by_contra hn
    have hall : ∀ x ∈ l, x.2 < a + b + c := by
      intro x hx
      have hnot : ¬ a + b + c ≤ x.2 := by
        intro hle
        exact hn ⟨x, hx, hle⟩
      omega
    have hs := sum_modes_le (a + b + c) l hall
    have hs' : k.degree ≤ (a + b + c) * (k.d₁ + k.d₂ + k.d₃) := by
      simpa only [hlen, hdegree, Nat.mul_comm] using hs
    omega
  rw [radicalWord_high_zero ρ w a b c h l hbad]
  exact Submodule.zero_mem _

/-- A finite search box for the keys at radical depth `j`. -/
def a3DepthKeyBox (a b c j : ℕ) : Finset A3RadicalKey :=
  (Finset.range (j + 1)).biUnion fun d₁ =>
    (Finset.range (j + 1)).biUnion fun d₂ =>
      (Finset.range (j + 1)).biUnion fun d₃ =>
        (Finset.range ((a + b + c) * j + 1)).image
          fun degree => ⟨d₁, d₂, d₃, degree⟩

theorem mem_a3DepthKeyBox (a b c j : ℕ) (k : A3RadicalKey)
    (h₁ : k.d₁ ≤ j) (h₂ : k.d₂ ≤ j) (h₃ : k.d₃ ≤ j)
    (hdeg : k.degree ≤ (a + b + c) * j) :
    k ∈ a3DepthKeyBox a b c j := by
  unfold a3DepthKeyBox
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₁, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₂, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₃, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨k.degree, Finset.mem_range.mpr (by omega), by cases k; rfl⟩

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_eq_bot_of_degree_gt
#print axioms VOA.DeligneAudit.A3Sector.mem_a3DepthKeyBox
