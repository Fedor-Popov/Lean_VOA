import VOA.DeligneAudit.SL4TAdjointSiteFlatShift

/-!
# The expansion identity and the flat relation on unit-compound top blocks

Write `N(α, β, γ, δ; X) = g^α q^β y^γ z^δ X` (all letters of mode zero; `g, q, y, z` commute
pairwise). On the commuting letters, `ad x = -z ∂_q - y ∂_g`, and `x` commutes with `y` and `z`:

    x N(α, β, γ, δ; X) = N(α, β, γ, δ; x X) - α N(α-1, β, γ+1, δ; X) - β N(α, β-1, γ, δ+1; X)

(`first_flatNormalWord`). Fix `B` and `e`, and put `L(a, b) = N(B-b, e-a, b, a; v)` (the *leak
words*; `L(0, d)` is the top word of the block `(0, d, 0; B - d, e)`, and `L(a, b)` with `a ≥ 1` is
`z^a` times the top word of the block `(0, b, 0; B - b, e - a)`) and
`X(a, b) = N(B-b, e-a, b, a; x v)` (the *marked words*, of first Levi key `(1, b, a)`).

**Lemma 6.2, the expansion identity** (`flat_expansion`). For every `n`,

    x^n (q^e g^B v) - (-1)^n [B]_n L(0, n)
      ∈ span {L(a, b) : a + b = n, 1 ≤ a ≤ e} + span {X(a, b) : a + b + 1 = n, a ≤ e},

with `[B]_n = B (B-1) ⋯ (B-n+1)`. All parameters are general.

**Proposition 6.3 at `e = 1`** (`flatTopRelation_unit`). On the top block `(0, d, 0; B - d, 1)`,
with `f = d`: the only leak word is `z y^(d-1) g^(B-d+1) v`, killed by `D_d` (fewer than `d`
shifted letters), and every marked word has key `(1, b, a)` with `a ≤ 1`, which is higher than
`(0, d, 0)`. Hence `F(h) D_d (g^(B-d) q y^d v) ∈ M_{>(0,d,0)}`.

For `e ≥ 2` the marked words with `a ≥ 2` have keys `(1, b, a)` with `1 - a < 0`; in the first
Levi order (Levi height first) these keys are *lower* than `(0, d, 0)`, so they are not in
`M_{>(0,d,0)}`. The paper's proof treats them as higher; this is not available here, and the
case `e ≥ 2` is left as the named residual of `SL4TAdjointSiteFlatRelation`.
-/

namespace VOA.DeligneAudit.SL4T

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-- A derivation-type commutation `D Y = Y D - Z`, with `Z` commuting with `Y`, on all powers. -/
theorem endomorphism_antiderivation_pow {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D Y Z : Module.End ℂ W) (hDY : ∀ u, D (Y u) = Y (D u) - Z u)
    (hYZ : ∀ u, Z (Y u) = Y (Z u)) (n : ℕ) (u : W) :
    D ((Y ^ n) u) = (Y ^ n) (D u) - (n : ℂ) • (Y ^ (n - 1)) (Z u) := by
  rcases n with _ | m
  · simp
  · have h := endomorphism_derivation_pow D Y (-Z) (fun v => by
      rw [hDY, LinearMap.neg_apply, sub_eq_add_neg]) (fun v => by
      simp only [LinearMap.neg_apply, map_neg, hYZ]) m u
    rw [h, LinearMap.neg_apply, map_neg, smul_neg, ← sub_eq_add_neg, Nat.add_sub_cancel]

/-- `[y, q] = 0`. -/
theorem bracket_compound_lastPair (e : Fin 15) : bracketInt 7 10 e = 0 := by
  fin_cases e <;> decide

/-- `[y, g] = 0`. -/
theorem bracket_compound_middle_zero (e : Fin 15) : bracketInt 7 9 e = 0 := by
  fin_cases e <;> decide

/-- `[x, g] = -y`. -/
theorem bracket_first_middle (e : Fin 15) :
    bracketInt 6 9 e = if e = 7 then -1 else 0 := by
  fin_cases e <;> decide

/-- `[z, q] = 0`. -/
theorem bracket_highest_lastPair (e : Fin 15) : bracketInt 8 10 e = 0 := by
  fin_cases e <;> decide

/-- `[z, g] = 0`. -/
theorem bracket_highest_middle (e : Fin 15) : bracketInt 8 9 e = 0 := by
  fin_cases e <;> decide

/-- `[q, z] = 0`. -/
theorem bracket_lastPair_highest (e : Fin 15) : bracketInt 10 8 e = 0 := by
  fin_cases e <;> decide

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- The normal-form word `g^α q^β y^γ z^δ X`, all letters of mode zero. -/
def flatNormalWord (α β γ δ : ℕ) (X : V) : V :=
  (ρ.op 9 0 ^ α) ((ρ.op 10 0 ^ β) ((ρ.op 7 0 ^ γ) ((ρ.op 8 0 ^ δ) X)))

/-- **`ad x` on normal-form words.** -/
theorem first_flatNormalWord (α β γ δ : ℕ) (X : V) :
    ρ.op 6 0 (flatNormalWord ρ α β γ δ X) =
      flatNormalWord ρ α β γ δ (ρ.op 6 0 X) -
        (α : ℂ) • flatNormalWord ρ (α - 1) β (γ + 1) δ X -
          (β : ℂ) • flatNormalWord ρ α (β - 1) γ (δ + 1) X := by
  -- `x g = g x - y`, `x q = q x - z`, with `y` commuting with `g` and `z` with `q`
  have hxg (u : V) : ρ.op 6 0 (ρ.op 9 0 u) = ρ.op 9 0 (ρ.op 6 0 u) - ρ.op 7 0 u := by
    rw [op_comm_of_single_bracket ρ bracket_first_middle 0 0 u]
    simp [sub_eq_add_neg]
  have hyg (u : V) : ρ.op 7 0 (ρ.op 9 0 u) = ρ.op 9 0 (ρ.op 7 0 u) :=
    op_comm_of_zero_bracket ρ bracket_compound_middle_zero 0 0 u
  have hxq (u : V) : ρ.op 6 0 (ρ.op 10 0 u) = ρ.op 10 0 (ρ.op 6 0 u) - ρ.op 8 0 u := by
    rw [op_comm_of_single_bracket ρ bracket_first_lastPair 0 0 u]
    simp [sub_eq_add_neg]
  have hzq (u : V) : ρ.op 8 0 (ρ.op 10 0 u) = ρ.op 10 0 (ρ.op 8 0 u) :=
    op_comm_of_zero_bracket ρ bracket_highest_lastPair 0 0 u
  have hg := endomorphism_antiderivation_pow (ρ.op 6 0) (ρ.op 9 0) (ρ.op 7 0) hxg hyg α
  have hq := endomorphism_antiderivation_pow (ρ.op 6 0) (ρ.op 10 0) (ρ.op 8 0) hxq hzq β
  have hxy (n : ℕ) (u : V) : ρ.op 6 0 ((ρ.op 7 0 ^ n) u) = (ρ.op 7 0 ^ n) (ρ.op 6 0 u) :=
    op_pow_comm_of_zero_bracket ρ bracket_first_compound 0 0 n u
  have hxz (n : ℕ) (u : V) : ρ.op 6 0 ((ρ.op 8 0 ^ n) u) = (ρ.op 8 0 ^ n) (ρ.op 6 0 u) :=
    op_pow_comm_of_zero_bracket ρ bracket_first_highest 0 0 n u
  have hzy (n : ℕ) (u : V) : ρ.op 8 0 ((ρ.op 7 0 ^ n) u) = (ρ.op 7 0 ^ n) (ρ.op 8 0 u) :=
    op_pow_comm_of_zero_bracket ρ bracket_highest_compound 0 0 n u
  have hyq (n : ℕ) (u : V) : ρ.op 7 0 ((ρ.op 10 0 ^ n) u) = (ρ.op 10 0 ^ n) (ρ.op 7 0 u) :=
    op_pow_comm_of_zero_bracket ρ bracket_compound_lastPair 0 0 n u
  have hzz (n : ℕ) (u : V) : ρ.op 8 0 ((ρ.op 8 0 ^ n) u) = (ρ.op 8 0 ^ (n + 1)) u := by
    rw [pow_succ', Module.End.mul_apply]
  have hyy (n : ℕ) (u : V) : ρ.op 7 0 ((ρ.op 7 0 ^ n) u) = (ρ.op 7 0 ^ (n + 1)) u := by
    rw [pow_succ', Module.End.mul_apply]
  simp only [flatNormalWord]
  rw [hg, hq, hxy, hxz, map_sub, map_smul, hzy, hzz, hyq, hyy]
  module

/-- The leak word `L(a, b) = g^(B-b) q^(e-a) y^b z^a v`. -/
def flatLeakWord (B e a b : ℕ) : V := flatNormalWord ρ (B - b) (e - a) b a w

/-- The marked word `X(a, b) = g^(B-b) q^(e-a) y^b z^a x v`, of first Levi key `(1, b, a)`. -/
def flatMarkedWord (B e a b : ℕ) : V := flatNormalWord ρ (B - b) (e - a) b a (ρ.op 6 0 w)

/-- The span of the leak words with `a + b = n` and `1 ≤ a ≤ e`. -/
def flatLeakSpan (B e n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ a b, a + b = n ∧ 1 ≤ a ∧ a ≤ e ∧ u = flatLeakWord ρ w B e a b}

/-- The span of the marked words with `a + b + 1 = n` and `a ≤ e`. -/
def flatMarkedSpan (B e n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ a b, a + b + 1 = n ∧ a ≤ e ∧ u = flatMarkedWord ρ w B e a b}

/-- One `x` on a leak word. -/
theorem first_flatLeakWord (B e a b : ℕ) :
    ρ.op 6 0 (flatLeakWord ρ w B e a b) =
      flatMarkedWord ρ w B e a b - ((B - b : ℕ) : ℂ) • flatLeakWord ρ w B e a (b + 1) -
        ((e - a : ℕ) : ℂ) • flatLeakWord ρ w B e (a + 1) b := by
  rw [flatLeakWord, first_flatNormalWord, flatMarkedWord, flatLeakWord, flatLeakWord,
    Nat.sub_sub, Nat.sub_sub]

theorem flatNormalWord_zero (α β γ δ : ℕ) : flatNormalWord ρ α β γ δ 0 = 0 := by
  simp [flatNormalWord]

/-- One `x` on a marked word: `x² v = 0` removes the leading term. -/
theorem first_flatMarkedWord (B e a b : ℕ) (hx : ρ.op 6 0 (ρ.op 6 0 w) = 0) :
    ρ.op 6 0 (flatMarkedWord ρ w B e a b) =
      -(((B - b : ℕ) : ℂ) • flatMarkedWord ρ w B e a (b + 1)) -
        ((e - a : ℕ) : ℂ) • flatMarkedWord ρ w B e (a + 1) b := by
  rw [flatMarkedWord, first_flatNormalWord, hx, flatNormalWord_zero, zero_sub, flatMarkedWord,
    flatMarkedWord, Nat.sub_sub, Nat.sub_sub]

/-- `x` maps the marked span of `n` into the marked span of `n + 1`, if `x² v = 0`. -/
theorem flatMarkedSpan_first (B e n : ℕ) (hx : ρ.op 6 0 (ρ.op 6 0 w) = 0) :
    flatMarkedSpan ρ w B e n ≤ (flatMarkedSpan ρ w B e (n + 1)).comap (ρ.op 6 0) := by
  rw [flatMarkedSpan, Submodule.span_le]
  rintro u ⟨a, b, hab, hae, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, first_flatMarkedWord ρ w B e a b hx]
  apply Submodule.sub_mem
  · apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, b + 1, by omega, hae, rfl⟩
  · by_cases ha : a + 1 ≤ e
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a + 1, b, by omega, ha, rfl⟩)
    · rw [show e - a = 0 by omega, Nat.cast_zero, zero_smul]
      exact Submodule.zero_mem _

/-- `x` maps the leak span of `n` into the sum of the leak and marked spans of `n + 1`. -/
theorem flatLeakSpan_first (B e n : ℕ) :
    flatLeakSpan ρ w B e n ≤
      (flatLeakSpan ρ w B e (n + 1) ⊔ flatMarkedSpan ρ w B e (n + 1)).comap (ρ.op 6 0) := by
  rw [flatLeakSpan, Submodule.span_le]
  rintro u ⟨a, b, hab, ha1, hae, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, first_flatLeakWord]
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, b, by omega, hae, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨a, b + 1, by omega, ha1, hae, rfl⟩))
  · by_cases ha : a + 1 ≤ e
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨a + 1, b, by omega, by omega, ha, rfl⟩))
    · rw [show e - a = 0 by omega, Nat.cast_zero, zero_smul]
      exact Submodule.zero_mem _

/-- **Lemma 6.2, the expansion identity.** `x^n (q^e g^B v) - (-1)^n [B]_n L(0, n)` lies in the
span of the leak words `L(a, b)` with `a + b = n`, `1 ≤ a ≤ e`, plus the span of the marked words
`X(a, b)` with `a + b + 1 = n`, `a ≤ e`. -/
theorem flat_expansion (B e : ℕ) (hx : ρ.op 6 0 (ρ.op 6 0 w) = 0) (n : ℕ) :
    (ρ.op 6 0 ^ n) (flatLeakWord ρ w B e 0 0) -
        ((-1 : ℂ) ^ n * (B.descFactorial n : ℂ)) • flatLeakWord ρ w B e 0 n ∈
      flatLeakSpan ρ w B e n ⊔ flatMarkedSpan ρ w B e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp ih
    have hstep : (ρ.op 6 0 ^ (n + 1)) (flatLeakWord ρ w B e 0 0) -
        ((-1 : ℂ) ^ (n + 1) * (B.descFactorial (n + 1) : ℂ)) • flatLeakWord ρ w B e 0 (n + 1) =
        ((-1 : ℂ) ^ n * (B.descFactorial n : ℂ)) •
            (flatMarkedWord ρ w B e 0 n - ((e - 0 : ℕ) : ℂ) • flatLeakWord ρ w B e 1 n) +
          ρ.op 6 0 l + ρ.op 6 0 m := by
      have hpow : (ρ.op 6 0 ^ (n + 1)) (flatLeakWord ρ w B e 0 0) =
          ρ.op 6 0 ((ρ.op 6 0 ^ n) (flatLeakWord ρ w B e 0 0)) := by
        rw [pow_succ', Module.End.mul_apply]
      have hsplit : (ρ.op 6 0 ^ n) (flatLeakWord ρ w B e 0 0) =
          ((-1 : ℂ) ^ n * (B.descFactorial n : ℂ)) • flatLeakWord ρ w B e 0 n + (l + m) := by
        rw [hlm]
        abel
      rw [hpow, hsplit, map_add, map_add, map_smul, first_flatLeakWord, Nat.descFactorial_succ,
        zero_add]
      push_cast
      module
    rw [hstep]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · apply Submodule.smul_mem
      apply Submodule.sub_mem
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨0, n, by omega, by omega, rfl⟩)
      · by_cases he : 1 ≤ e
        · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
            (Submodule.subset_span ⟨1, n, by omega, le_rfl, he, rfl⟩))
        · rw [show e - 0 = 0 by omega, Nat.cast_zero, zero_smul]
          exact Submodule.zero_mem _
    · exact flatLeakSpan_first ρ w B e n hl
    · exact Submodule.mem_sup_right (flatMarkedSpan_first ρ w B e n hx hm)

/-! ### The top block with a single compound letter -/

/-- The corner vector is the leak word `L(0, 0)` at `e = 1`. -/
theorem flatLeakWord_corner (B : ℕ) : flatLeakWord ρ w B 1 0 0 = flatCornerVector ρ w B := by
  simp only [flatLeakWord, flatNormalWord, flatCornerVector, Nat.sub_zero, pow_one, pow_zero,
    Module.End.one_apply]
  exact (op_pow_comm_of_zero_bracket ρ bracket_lastPair_middle_zero 0 0 B w).symm

/-- Powers of a Levi colour preserve every higher first Levi closure. -/
theorem higherRadicalCountClosure_leviPow (d : Fin 3 → ℕ) (c : Fin 8) (r n : ℕ) :
    higherRadicalCountClosure ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (ρ.op (a3LeviColour c) r ^ n) := by
  induction n with
  | zero => intro u hu; simpa using hu
  | succ n ih =>
    intro u hu
    rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
    exact a3LeviClosure_inv ρ _ c r (ih hu)

/-- A marked word with at most one `z` lies in the higher first Levi closure. -/
theorem flatMarkedWord_mem_higherRadical (B e a b : ℕ) (ha : a ≤ 1) :
    flatMarkedWord ρ w B e a b ∈ higherRadicalCountClosure ρ w ![0, a + b + 1, 0] := by
  have hk : higherRadicalCounts ![0, a + b + 1, 0] ⟨1, b, a, 0⟩ := by
    simp only [higherRadicalCounts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  have hmem := zeroModeWord_mem_higherRadical ρ w ![0, a + b + 1, 0] 1 b a hk
  have hre : (ρ.op 7 0 ^ b) ((ρ.op 8 0 ^ a) (ρ.op 6 0 w)) =
      (ρ.op 6 0 ^ 1) ((ρ.op 7 0 ^ b) ((ρ.op 8 0 ^ a) w)) := by
    rw [pow_one, op_pow_comm_of_zero_bracket ρ bracket_first_compound,
      op_pow_comm_of_zero_bracket ρ bracket_first_highest]
  rw [flatMarkedWord, flatNormalWord, hre]
  exact higherRadicalCountClosure_leviPow ρ w _ 3 0 _
    (higherRadicalCountClosure_leviPow ρ w _ 5 0 _ hmem)

/-- Every power of `x` keeps the corner vector in the flat kernel space. -/
theorem firstPow_flatCorner_mem (B n : ℕ) :
    (ρ.op 6 0 ^ n) (flatCornerVector ρ w B) ∈ flatKernelSpace ρ w B := by
  induction n with
  | zero => simpa using flatCornerVector_mem_flatKernelSpace ρ w B
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact flatKernelSpace_parabolic ρ w B 6 (by simp [flatParabolicColour]) ih

/-- At `e = 1` every marked word of total `d` lies in the higher first Levi closure. -/
theorem flatMarkedSpan_unit_le (B d : ℕ) :
    flatMarkedSpan ρ w B 1 d ≤ higherRadicalCountClosure ρ w ![0, d, 0] := by
  rw [flatMarkedSpan, Submodule.span_le]
  rintro u ⟨a, b, hab, hae, rfl⟩
  have hm := flatMarkedWord_mem_higherRadical ρ w B 1 a b hae
  rwa [hab] at hm

variable (B h : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (hg : ρ.op 9 h w = 0)
variable (hh : 1 ≤ h) (ht : ∀ i s u, h + 1 ≤ s → ρ.op i s u = 0)

include hW in
/-- The Newton operators of the flat shift current preserve every higher first Levi closure. -/
theorem higherRadicalCountClosure_flatNewton (d : Fin 3 → ℕ) (f : ℕ) :
    higherRadicalCountClosure ρ w d ≤
      (higherRadicalCountClosure ρ w d).comap (newtonEnd (flatShiftCurrent ρ) f) :=
  newtonEnd_le_comap _ _ (fun s _ => higherRadicalCountClosure_flatShift ρ w 1 B 1 hW d s) f

include hW in
/-- The Newton operators kill every leak word with at least one `z` at `e = 1`. -/
theorem flatLeakSpan_unit_newton (d : ℕ) :
    ∀ u ∈ flatLeakSpan ρ w B 1 d, newtonEnd (flatShiftCurrent ρ) d u = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, hab, ha1, hae, rfl⟩ := hz
    obtain rfl : a = 1 := by omega
    have hcomm := newtonEnd_commute (flatShiftCurrent ρ) (ρ.op 9 0 ^ (B - b))
      (fun s _ => LinearMap.ext fun v => (flatShiftCurrent_middlePow ρ s (B - b) v).symm) d
    simp only [flatLeakWord, flatNormalWord, Nat.sub_self, pow_zero, Module.End.one_apply,
      pow_one]
    have hc' : newtonEnd (flatShiftCurrent ρ) d ((ρ.op 9 0 ^ (B - b)) ((ρ.op 7 0 ^ b)
        (ρ.op 8 0 w))) = (ρ.op 9 0 ^ (B - b)) (newtonEnd (flatShiftCurrent ρ) d
          ((ρ.op 7 0 ^ b) (ρ.op 8 0 w))) := by
      simpa only [Module.End.mul_apply] using
        (LinearMap.congr_fun hcomm.eq ((ρ.op 7 0 ^ b) (ρ.op 8 0 w))).symm
    rw [hc', newtonEnd_flatShift_compoundPow_eq_zero ρ (ρ.op 8 0 w) (fun s hs => by
        rw [flatShiftCurrent_highest, flatShiftCurrent_source_zero ρ w 1 B 1 hW s hs, map_zero])
        b d (by omega), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul c x _ hx => simp [map_smul, hx]

include hW hg hh ht in
/-- **Proposition 6.3 at `e = 1`.** On the top block `(0, d, 0; B - d, 1)`,
`F(h) D_d (g^(B-d) q y^d v) ∈ M_{>(0,d,0)}`. -/
theorem flatTopRelation_unit (d : ℕ) (hd : d ≤ B) :
    ρ.op 11 h (newtonEnd (flatShiftCurrent ρ) d (flatNormalWord ρ (B - d) 1 d 0 w)) ∈
      higherRadicalCountClosure ρ w ![0, d, 0] := by
  set D := newtonEnd (flatShiftCurrent ρ) d with hD
  set M := higherRadicalCountClosure ρ w ![0, d, 0] with hM
  have hx2 : ρ.op 6 0 (ρ.op 6 0 w) = 0 := lowering_square_of_label_one ρ w _ hW 0 rfl
  obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp (flat_expansion ρ w B 1 hx2 d)
  -- the expanded vector lies in the flat kernel space
  have hX : (ρ.op 6 0 ^ d) (flatLeakWord ρ w B 1 0 0) ∈ flatKernelSpace ρ w B := by
    rw [flatLeakWord_corner]
    exact firstPow_flatCorner_mem ρ w B d
  have hK : D ((ρ.op 6 0 ^ d) (flatLeakWord ρ w B 1 0 0)) ∈ flatKernelSpace ρ w B :=
    newtonEnd_le_comap _ _ (fun s hs => flatKernelSpace_flatShift ρ w B s hs) d hX
  have hF0 := flatKernelSpace_lastLowering_zero ρ w B h hW hg hh ht _ hK
  have hl0 : D l = 0 := flatLeakSpan_unit_newton ρ w B hW d l hl
  have hmM : m ∈ M := flatMarkedSpan_unit_le ρ w B d hm
  have hDm : ρ.op 11 h (D m) ∈ M :=
    a3LeviClosure_inv ρ _ 4 h (higherRadicalCountClosure_flatNewton ρ w B hW _ d hmM)
  have hc : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
  have hY : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) • flatLeakWord ρ w B 1 0 d =
      (ρ.op 6 0 ^ d) (flatLeakWord ρ w B 1 0 0) - l - m := by
    rw [sub_sub, hlm]
    abel
  have heq : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) •
      ρ.op 11 h (D (flatLeakWord ρ w B 1 0 d)) =
      ρ.op 11 h (D ((ρ.op 6 0 ^ d) (flatLeakWord ρ w B 1 0 0))) - ρ.op 11 h (D l) -
        ρ.op 11 h (D m) := by
    rw [← map_smul, ← map_smul, hY, map_sub, map_sub, map_sub, map_sub]
  have hmem : ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ)) •
      ρ.op 11 h (D (flatLeakWord ρ w B 1 0 d)) ∈ M := by
    rw [heq, hF0, hl0, map_zero, sub_zero, zero_sub]
    exact Submodule.neg_mem _ hDm
  have hfin := M.smul_mem ((-1 : ℂ) ^ d * (B.descFactorial d : ℂ))⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hfin
  rw [flatLeakWord, Nat.sub_zero] at hfin
  exact hfin

end

end VOA.DeligneAudit.SL4T
