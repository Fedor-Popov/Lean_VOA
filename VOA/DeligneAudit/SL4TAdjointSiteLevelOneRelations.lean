import VOA.DeligneAudit.SL4TAdjointSiteTransportedRelations
import VOA.DeligneAudit.SL4TMixedSecondLeviBlockBound

/-!
# The first Levi relations at one adjoint site

At outer labels `(1, ·, 1)` the two outer radical alphabets have Grassmannian ring `H(d, 1)` with
`d ≤ 1`, which is one-dimensional; all of its positive power sums vanish
(`grassmannianPowerSum_label_one`). Hence the outer alphabet currents act by zero on every first
Levi multiplicity (`radicalAlphabetQuotCurrent_outer_eq_zero`). In particular, at the key
`D = (1, d, 1)`,

    x y^d z(r) v ∈ M_{>D}      for every r ≥ 1

(`adjointSite_shiftedTopWord_mem`). This is the level-1 alphabet bound used in the note.

**Lemma E** (`adjointSite_lowerKey_mem`). If in addition `f₂(h) v = 0` with `h ≥ 1`, then

    (d + 1) · x y^d z z(h) v ∈ M_{>(1, d + 1, 1)}.

The vector on the left has the lower key `(1, d, 2)`; the proof applies `F = f₃` to the vector
`x y^(d+1) z(h) v ∈ M_{>(1, d + 1, 1)}`, which is `F`-stable, and kills the remaining summand
with the transported relation `z(h) x F v = 0`.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

noncomputable section

/-- `e₁ = h₁` in the stable presentation. -/
theorem complete_one : complete 1 = elementary 1 := by
  rw [complete_succ]
  simp

/-- All positive elementary classes vanish in `H(d, 1)` for `d ≤ 1`. -/
theorem eClass_label_one (n : ℕ) (hn : n ≤ 1) (j : ℕ) (hj : 0 < j) :
    eClass n (1 - n) j = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact eClass_eq_zero 0 1 j hj
  · by_cases hj1 : j = 1
    · subst j
      have he : eClass 1 0 1 = hClass 1 0 1 := by
        simp only [eClass, hClass, complete_one]
      exact he.trans (hClass_eq_zero 1 0 1 (by norm_num))
    · exact eClass_eq_zero 1 0 j (by omega)

/-- All positive power sums vanish in the one-dimensional Grassmannian rings `H(d, 1)`. -/
theorem grassmannianPowerSum_label_one (n : ℕ) (hn : n ≤ 1) (s : ℕ) (hs : 0 < s) :
    grassmannianPowerSum n 1 s = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  unfold grassmannianPowerSum
  rw [powerSumOfCoeff]
  simp [eClass_label_one n hn _ (Nat.succ_pos _)]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget during rewriting.
/-- At outer labels one, the two outer Grassmannian power sums vanish in positive degree. -/
theorem radicalGrassmannianPowerSum_outer_eq_zero (B : ℕ) (D : Fin 3 → ℕ) (j : Fin 3)
    (hj : (j = 0 ∧ D 0 ≤ 1) ∨ (j = 2 ∧ D 2 ≤ 1)) (s : ℕ) (hs : 0 < s) :
    radicalGrassmannianPowerSum 1 B 1 D j s = 0 := by
  rcases hj with ⟨rfl, hD⟩ | ⟨rfl, hD⟩
  · simp only [radicalGrassmannianPowerSum, grassmannianPowerSum_label_one (D 0) hD s hs,
      TensorProduct.zero_tmul]
  · simp only [radicalGrassmannianPowerSum, grassmannianPowerSum_label_one (D 2) hD s hs,
      TensorProduct.tmul_zero]

set_option synthInstance.maxHeartbeats 100000 in
-- Nested tensor-product ring instances exceed the default synthesis budget during rewriting.
/-- At outer labels one, the outer alphabet currents of positive mode act by zero on every
first Levi multiplicity vector. -/
theorem radicalAlphabetQuotCurrent_outer_eq_zero (B : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (D : Fin 3 → ℕ) (j : Fin 3)
    (hj : (j = 0 ∧ D 0 ≤ 1) ∨ (j = 2 ∧ D 2 ≤ 1)) (s : ℕ) (hs : 0 < s)
    (u : V ⧸ higherRadicalCountClosure ρ w D) (hu : u ∈ radicalCountMultiplicity ρ w D) :
    radicalAlphabetQuotCurrent ρ w 1 B 1 hW D j s u = 0 := by
  obtain ⟨φ, hφ⟩ := radicalGrassmannianEvaluation_surjective ρ w 1 B 1 hW D ⟨u, hu⟩
  have he := radicalGrassmannianEvaluation_powerSum ρ w 1 B 1 hW D j s hs φ
  rw [hφ, radicalGrassmannianPowerSum_outer_eq_zero B D j hj s hs, zero_mul,
    map_zero] at he
  simpa using he

/-- The zero-mode top word `x y^n z(r) v` lies in the first Levi layer of key `(1, n, 1)`. -/
theorem adjointSite_topWord_mem_layer (n r : ℕ) :
    ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 r w)) ∈ radicalCountLayer ρ w ![1, n, 1] := by
  have hm := a3_three_mode_mem_key ρ w [0] (List.replicate n 0) [r]
  simp only [List.length_singleton, List.length_replicate, List.sum_singleton,
    List.sum_replicate, smul_zero, zero_add] at hm
  unfold radicalCountLayer
  apply Submodule.mem_iSup_of_mem r
  convert hm using 1
  simp [aWord, List.map_replicate, List.prod_replicate, F, Module.End.mul_apply]

/-- A commuting pair of current operators also commutes with all powers. -/
theorem op_pow_comm_of_zero_bracket {a b : Fin 15} (hab : ∀ e, bracketInt a b e = 0)
    (r s n : ℕ) (u : V) :
    ρ.op a r ((ρ.op b s ^ n) u) = (ρ.op b s ^ n) (ρ.op a r u) := by
  have hc : Commute (ρ.op a r) (ρ.op b s) :=
    LinearMap.ext fun v => op_comm_of_zero_bracket ρ hab r s v
  exact congrArg (fun T : Module.End ℂ V => T u) (hc.pow_right n).eq

/-- `F(r) y^(n+1) = y^(n+1) F(r) + (n + 1) y^n z(r)`. -/
theorem last_compoundPower_comm (r n : ℕ) (u : V) :
    ρ.op 11 r ((ρ.op 7 0 ^ (n + 1)) u) =
      (ρ.op 7 0 ^ (n + 1)) (ρ.op 11 r u) +
        ((n + 1 : ℕ) : ℂ) • (ρ.op 7 0 ^ n) (ρ.op 8 r u) := by
  have hFy (v : V) : ρ.op 11 r (ρ.op 7 0 v) = ρ.op 7 0 (ρ.op 11 r v) + ρ.op 8 r v := by
    simpa only [add_zero, Int.cast_one, one_smul] using
      op_comm_of_single_bracket ρ bracket_last_compound r 0 v
  induction n with
  | zero => simpa only [zero_add, pow_one, pow_zero, Nat.cast_one, one_smul,
      Module.End.one_apply] using hFy u
  | succ n ih =>
    have hy : ∀ m (v : V), ρ.op 7 0 ((ρ.op 7 0 ^ m) v) = (ρ.op 7 0 ^ (m + 1)) v := by
      intro m v
      rw [pow_succ', Module.End.mul_apply]
    rw [← hy (n + 1) u, ← hy (n + 1) (ρ.op 11 r u), hFy, ih, map_add, map_smul,
      op_pow_comm_of_zero_bracket ρ bracket_highest_compound r 0 (n + 1) u, hy n]
    push_cast
    module

/-- The first two alphabet currents commute with the third radical letter's shift. -/
theorem radicalAlphabetCurrent_last_comm_other (j : Fin 3) (hj : j ≠ 2) (r s : ℕ) (v : V) :
    radicalAlphabetCurrent ρ 2 r (ρ.op (F j) s v) =
      ρ.op (F j) s (radicalAlphabetCurrent ρ 2 r v) := by
  have h := radicalAlphabetCurrent_comm ρ 2 j r s v
  rw [if_neg (Ne.symm hj), zero_smul] at h
  exact sub_eq_zero.mp h

/-- The last alphabet current shifts the mode of the single `z`-letter of the top word. -/
theorem radicalAlphabetCurrent_topWord (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (n r : ℕ) (hr : 0 < r) :
    radicalAlphabetCurrent ρ 2 r (ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) =
      ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 r w)) := by
  have h0 := radicalAlphabetCurrent_last_comm_other ρ 0 (by decide) r 0
  have h1 := radicalAlphabetCurrent_last_comm_other ρ 1 (by decide) r 0
  change ∀ v, radicalAlphabetCurrent ρ 2 r (ρ.op 6 0 v) = ρ.op 6 0 _ at h0
  change ∀ v, radicalAlphabetCurrent ρ 2 r (ρ.op 7 0 v) = ρ.op 7 0 _ at h1
  have hpow : ∀ m (v : V), radicalAlphabetCurrent ρ 2 r ((ρ.op 7 0 ^ m) v) =
      (ρ.op 7 0 ^ m) (radicalAlphabetCurrent ρ 2 r v) := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, h1, ih, Module.End.mul_apply]
  have hz := radicalAlphabetCurrent_comm ρ 2 2 r 0 w
  rw [radicalAlphabetCurrent_source_zero ρ w 1 B 1 hW 2 r hr, map_zero, sub_zero,
    if_pos rfl, one_smul, add_zero] at hz
  rw [h0, hpow]
  change ρ.op 6 0 ((ρ.op 7 0 ^ n) (radicalAlphabetCurrent ρ 2 r (radicalOp ρ 2 0 w))) = _
  rw [hz]
  rfl

/-- **The level-1 alphabet bound.** At the key `(1, n, 1)`, a positive mode on the `z`-letter
puts the top word into the higher first Levi subspace: `x y^n z(r) v ∈ M_{>(1,n,1)}`. -/
theorem adjointSite_shiftedTopWord_mem (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (n r : ℕ) (hr : 0 < r) :
    ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 r w)) ∈ higherRadicalCountClosure ρ w ![1, n, 1] := by
  have hmem : (higherRadicalCountClosure ρ w ![1, n, 1]).mkQ
      (ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 0 w))) ∈ radicalCountMultiplicity ρ w ![1, n, 1] :=
    ⟨_, adjointSite_topWord_mem_layer ρ w n 0, rfl⟩
  have hz := radicalAlphabetQuotCurrent_outer_eq_zero ρ w B hW ![1, n, 1] 2
    (Or.inr ⟨rfl, by simp⟩) r hr _ hmem
  rw [radicalAlphabetQuotCurrent_mk, radicalAlphabetCurrent_topWord ρ w B hW n r hr] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

/-- **Lemma E.** With `f₂(h) v = 0` and `h ≥ 1`, the lower-key vector `(n + 1) x y^n z z(h) v`
lies in the higher first Levi subspace of the key `(1, n + 1, 1)`. -/
theorem adjointSite_lowerKey_mem (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (hh : 0 < h) (hg : ρ.op 9 h w = 0) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • ρ.op 6 0 ((ρ.op 7 0 ^ n) (ρ.op 8 0 (ρ.op 8 h w))) ∈
      higherRadicalCountClosure ρ w ![1, n + 1, 1] := by
  have hwd := adjointSite_shiftedTopWord_mem ρ w B hW (n + 1) h hh
  have hF : ρ.op 11 0 (ρ.op 6 0 ((ρ.op 7 0 ^ (n + 1)) (ρ.op 8 h w))) ∈
      higherRadicalCountClosure ρ w ![1, n + 1, 1] := a3LeviClosure_inv ρ _ 4 0 hwd
  rw [op_comm_of_zero_bracket ρ bracket_last_first, last_compoundPower_comm,
    op_comm_of_zero_bracket ρ bracket_last_highest, map_add, map_smul] at hF
  have hT := (adjointSite_transported_relations ρ w B h hW hg).2
  have hzero : ρ.op 6 0 ((ρ.op 7 0 ^ (n + 1)) (ρ.op 8 h (ρ.op 11 0 w))) = 0 := by
    rw [op_pow_comm_of_zero_bracket ρ bracket_first_compound,
      op_comm_of_zero_bracket ρ bracket_first_highest, hT, map_zero]
  rw [hzero, zero_add] at hF
  exact hF

end

end VOA.DeligneAudit.SL4T
