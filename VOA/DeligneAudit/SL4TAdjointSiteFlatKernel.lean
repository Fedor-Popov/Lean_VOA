import VOA.DeligneAudit.SL4TAdjointSiteKernelRelations

/-!
# The flat kernel space at one adjoint site, and the vanishing of `F(h)` on it

Colours, in the 0-based matrix units of `A3Sector.bracketTable`: `x = E₁₀` (colour 6),
`y = E₂₀` (7), `z = E₃₀` (8), `g = E₂₁` (9), `q = E₃₁` (10), `F = E₃₂` (11) and `η = E₁₂` (3).

The *corner vector* is `ω = q g^B v`. The *flat kernel space* is the span of all words applied
to `ω` whose letters are either currents of positive mode, or zero-mode currents of the
parabolic `p₃ = {X : [X, F] ∈ ℂ F}`; the zero-mode colours of `p₃` are `E₀₁, E₀₂, η, x, z, q, F`
and the three Cartan colours.

**Lemma 6.1** (`flatKernelSpace_lastLowering_zero`). Let `v` satisfy the local Weyl relations of
weight `(1, B, 1)`, `f₂(h) v = 0` with `h ≥ 1`, and let every current of mode at least `h + 1`
vanish. Then `F(h)` kills the whole flat kernel space. The proof:

1. `q(h) F v = 0` (the transported relation);
2. `u₀ = q q(h) v` is killed by `η`, has `α₂`-weight `B - 2`, and is killed by `g^(B+1)`; by
   `sl₂` theory `g^(B-1) u₀ = 0`;
3. `F(h) ω = B g^(B-1) u₀ = 0`;
4. for an allowed letter `X`, `F(h) X = X F(h) + (multiple of F(h))`, the bracket of positive
   mode vanishing by the cutoff.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-- The zero-mode colours whose bracket with `F = E₃₂` is a multiple of `F`. -/
def flatParabolicColour (c : Fin 15) : Prop :=
  c = 0 ∨ c = 1 ∨ c = 3 ∨ c = 6 ∨ c = 8 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14

/-- A letter of the flat kernel space: a current of positive mode, or a zero-mode current of the
parabolic of `F`. -/
def FlatKernelLetter (x : Fin 15 × ℕ) : Prop := 1 ≤ x.2 ∨ flatParabolicColour x.1

/-- The bracket of `F` with a parabolic colour has no component outside `F`. -/
theorem bracket_last_flatParabolic (c : Fin 15) (hc : flatParabolicColour c) :
    ∀ e : Fin 15, e ≠ 11 → bracketInt 11 c e = 0 := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `[η, q] = -F`. -/
theorem bracket_raising_lastPair (e : Fin 15) :
    bracketInt 3 10 e = if e = 11 then -1 else 0 := by
  fin_cases e <;> decide

/-- `[E₁₁ - E₂₂, q] = -q`. -/
theorem bracket_middleCartan_lastPair (e : Fin 15) :
    bracketInt 13 10 e = if e = 10 then -1 else 0 := by
  fin_cases e <;> decide

/-- `[η, g] = E₁₁ - E₂₂`. -/
theorem bracket_raising_middle (e : Fin 15) :
    bracketInt 3 9 e = if e = 13 then 1 else 0 := by
  fin_cases e <;> decide

/-- `[E₁₁ - E₂₂, g] = -2 g`. -/
theorem bracket_middleCartan_middle (e : Fin 15) :
    bracketInt 13 9 e = if e = 9 then -2 else 0 := by
  fin_cases e <;> decide

/-- `[g, q] = 0`. -/
theorem bracket_middle_lastPair_zero (e : Fin 15) : bracketInt 9 10 e = 0 := by
  fin_cases e <;> decide

/-- `[q, g] = 0`. -/
theorem bracket_lastPair_middle_zero (e : Fin 15) : bracketInt 10 9 e = 0 := by
  fin_cases e <;> decide

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The corner vector `ω = q g^B v`. -/
def flatCornerVector (B : ℕ) : V := ρ.op 10 0 ((ρ.op 9 0 ^ B) w)

/-- The flat kernel space: words in allowed letters applied to the corner vector. -/
def flatKernelSpace (B : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ l : List (Fin 15 × ℕ), l.Forall FlatKernelLetter ∧
    u = wordOp ρ l (flatCornerVector ρ w B)}

theorem flatCornerVector_mem_flatKernelSpace (B : ℕ) :
    flatCornerVector ρ w B ∈ flatKernelSpace ρ w B :=
  Submodule.subset_span ⟨[], by simp, rfl⟩

/-- Every allowed letter preserves the flat kernel space. -/
theorem flatKernelSpace_letter (B : ℕ) (c : Fin 15) (r : ℕ) (hc : FlatKernelLetter (c, r)) :
    flatKernelSpace ρ w B ≤ (flatKernelSpace ρ w B).comap (ρ.op c r) := by
  rw [flatKernelSpace, Submodule.span_le]
  rintro u ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨(c, r) :: l, (List.forall_cons _ _ _).mpr ⟨hc, hl⟩, rfl⟩

/-- Every current of positive mode preserves the flat kernel space. -/
theorem flatKernelSpace_positive (B : ℕ) (c : Fin 15) (r : ℕ) (hr : 1 ≤ r) :
    flatKernelSpace ρ w B ≤ (flatKernelSpace ρ w B).comap (ρ.op c r) :=
  flatKernelSpace_letter ρ w B c r (Or.inl hr)

/-- Every zero-mode current of the parabolic of `F` preserves the flat kernel space. -/
theorem flatKernelSpace_parabolic (B : ℕ) (c : Fin 15) (hc : flatParabolicColour c) :
    flatKernelSpace ρ w B ≤ (flatKernelSpace ρ w B).comap (ρ.op c 0) :=
  flatKernelSpace_letter ρ w B c 0 (Or.inr hc)

/-- Step (iv): `F(h)` passes an allowed letter up to a multiple of itself. -/
theorem lastLowering_flatKernelLetter (h : ℕ) (ht : ∀ i s u, h + 1 ≤ s → ρ.op i s u = 0)
    (c : Fin 15) (r : ℕ) (hc : FlatKernelLetter (c, r)) (u : V) (hu : ρ.op 11 h u = 0) :
    ρ.op 11 h (ρ.op c r u) = 0 := by
  have hcomm := ρ.comm 11 c h r u
  rw [hu, map_zero, sub_zero] at hcomm
  rw [hcomm]
  rcases hc with hr | hp
  · apply Finset.sum_eq_zero
    intro e _
    rw [ht e (h + r) u (by simp only at hr; omega), smul_zero]
  · rw [Finset.sum_eq_single (11 : Fin 15)]
    · rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [add_zero, hu, smul_zero]
      · rw [ht 11 (h + r) u (by omega), smul_zero]
    · intro e _ he
      simp [bracketTable, bracket_last_flatParabolic c hp e he]
    · simp

/-- If `F(h)` kills the corner vector, it kills the whole flat kernel space. -/
theorem flatKernelSpace_lastLowering_of_corner (B h : ℕ)
    (ht : ∀ i s u, h + 1 ≤ s → ρ.op i s u = 0)
    (hω : ρ.op 11 h (flatCornerVector ρ w B) = 0) :
    ∀ u ∈ flatKernelSpace ρ w B, ρ.op 11 h u = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    induction l with
    | nil => exact hω
    | cons x l ih =>
      obtain ⟨hx, hl⟩ := (List.forall_cons _ _ _).mp hl
      exact lastLowering_flatKernelLetter ρ h ht x.1 x.2 hx _ (ih hl)
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

/-- The `sl₂(α₂)` highest-weight step (ii): `g^(B-1) q q(h) v = 0`. -/
theorem flatCorner_secondStep (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (hg : ρ.op 9 h w = 0) (hh : 1 ≤ h) :
    (ρ.op 9 0 ^ (B - 1)) (ρ.op 10 0 (ρ.op 10 h w)) = 0 := by
  set u₀ := ρ.op 10 0 (ρ.op 10 h w) with hu₀
  have hFh : ρ.op 11 h w = 0 :=
    simple_mode_zero ρ w (weightABC 1 B 1) hW 2 h (by change 1 ≤ h; exact hh)
  have hηw (r : ℕ) : ρ.op 3 r w = 0 := hW.raising 3 (by decide) r
  have hq := (adjointSite_transported_relations ρ w B h hW hg).1
  -- `η q(r) = q(r) η - F(r)`
  have hηq (r : ℕ) (x : V) :
      ρ.op 3 0 (ρ.op 10 r x) = ρ.op 10 r (ρ.op 3 0 x) - ρ.op 11 r x := by
    have hc := op_comm_of_single_bracket ρ bracket_raising_lastPair 0 r x
    rw [zero_add] at hc
    rw [hc]
    simp [sub_eq_add_neg]
  have hFq : ρ.op 11 0 (ρ.op 10 h w) = ρ.op 10 h (ρ.op 11 0 w) :=
    op_comm_of_zero_bracket ρ bracket_last_lastPair 0 h w
  have hE : ρ.op 3 0 u₀ = 0 := by
    rw [hu₀, hηq, hηq, hηw, map_zero, zero_sub, hFh, neg_zero, map_zero, zero_sub, hFq, hq,
      neg_zero]
  -- the Cartan weight `B - 2`
  have hHq (r : ℕ) (x : V) :
      ρ.op 13 0 (ρ.op 10 r x) = ρ.op 10 r (ρ.op 13 0 x) - ρ.op 10 r x := by
    have hc := op_comm_of_single_bracket ρ bracket_middleCartan_lastPair 0 r x
    rw [zero_add] at hc
    rw [hc]
    simp [sub_eq_add_neg]
  have hHw : ρ.op 13 0 w = (B : ℂ) • w := hW.cartan_zero 1
  have hH : ρ.op 13 0 u₀ = (((B : ℤ) - 2 : ℤ) : ℂ) • u₀ := by
    rw [hu₀, hHq, hHq, hHw]
    simp only [map_sub, map_smul]
    push_cast
    module
  -- `g` commutes with `q`
  have hgq (r : ℕ) (n : ℕ) (x : V) : (ρ.op 9 0 ^ n) (ρ.op 10 r x) = ρ.op 10 r ((ρ.op 9 0 ^ n) x) :=
    (op_pow_comm_of_zero_bracket ρ bracket_lastPair_middle_zero r 0 n x).symm
  have hK : (ρ.op 9 0)^[B + 1] u₀ = 0 := by
    rw [← Module.End.pow_apply, hu₀, hgq, hgq]
    have hl := hW.lowering 1
    change (ρ.op 9 0)^[B + 1] w = 0 at hl
    rw [Module.End.pow_apply, hl, map_zero, map_zero]
  have hEF (x : V) : ρ.op 3 0 (ρ.op 9 0 x) - ρ.op 9 0 (ρ.op 3 0 x) = ρ.op 13 0 x := by
    have hc := op_comm_of_single_bracket ρ bracket_raising_middle 0 0 x
    rw [hc]
    simp
  have hHF (x : V) : ρ.op 13 0 (ρ.op 9 0 x) - ρ.op 9 0 (ρ.op 13 0 x) =
      (-2 : ℂ) • ρ.op 9 0 x := by
    have hc := op_comm_of_single_bracket ρ bracket_middleCartan_middle 0 0 x
    rw [hc]
    simp
  obtain ⟨hneg, hpos⟩ := VOA.DeligneAudit.CLFilt.hw_pow (ρ.op 3 0) (ρ.op 9 0) (ρ.op 13 0)
    hEF hHF hE hH (B + 1) hK
  by_cases hB : 2 ≤ B
  · have h' := hpos (by omega)
    have he : (((B : ℤ) - 2).toNat + 1) = B - 1 := by omega
    rw [he, ← Module.End.pow_apply] at h'
    exact h'
  · rw [hneg (by omega), map_zero]

/-- Step (iii): `F(h) ω = 0`. -/
theorem flatCorner_lastLowering_zero (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (hg : ρ.op 9 h w = 0) (hh : 1 ≤ h) :
    ρ.op 11 h (flatCornerVector ρ w B) = 0 := by
  have hFh : ρ.op 11 h w = 0 :=
    simple_mode_zero ρ w (weightABC 1 B 1) hW 2 h (by change 1 ≤ h; exact hh)
  have hFq (x : V) : ρ.op 11 h (ρ.op 10 0 x) = ρ.op 10 0 (ρ.op 11 h x) :=
    op_comm_of_zero_bracket ρ bracket_last_lastPair h 0 x
  rw [flatCornerVector, hFq]
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [pow_zero, Module.End.one_apply, hFh, map_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
    have hFg (x : V) : ρ.op 11 h (ρ.op 9 0 x) = ρ.op 9 0 (ρ.op 11 h x) + ρ.op 10 h x := by
      simpa only [add_zero, Int.cast_one, one_smul] using
        op_comm_of_single_bracket ρ bracket_last_middle h 0 x
    have hqg (x : V) : ρ.op 10 h (ρ.op 9 0 x) = ρ.op 9 0 (ρ.op 10 h x) :=
      op_comm_of_zero_bracket ρ bracket_lastPair_middle_zero h 0 x
    rw [endomorphism_derivation_pow (ρ.op 11 h) (ρ.op 9 0) (ρ.op 10 h) hFg hqg m w, hFh,
      map_zero, zero_add, map_smul]
    have hgq : ρ.op 10 0 ((ρ.op 9 0 ^ m) (ρ.op 10 h w)) =
        (ρ.op 9 0 ^ m) (ρ.op 10 0 (ρ.op 10 h w)) :=
      op_pow_comm_of_zero_bracket ρ bracket_lastPair_middle_zero 0 0 m _
    rw [hgq]
    have h2 := flatCorner_secondStep ρ w (m + 1) h hW hg hh
    rw [Nat.add_sub_cancel] at h2
    rw [h2, smul_zero]

/-- **Lemma 6.1.** `F(h)` kills the flat kernel space. -/
theorem flatKernelSpace_lastLowering_zero (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (hg : ρ.op 9 h w = 0) (hh : 1 ≤ h) (ht : ∀ i s u, h + 1 ≤ s → ρ.op i s u = 0) :
    ∀ u ∈ flatKernelSpace ρ w B, ρ.op 11 h u = 0 :=
  flatKernelSpace_lastLowering_of_corner ρ w B h ht (flatCorner_lastLowering_zero ρ w B h hW hg hh)

end

end VOA.DeligneAudit.SL4T
