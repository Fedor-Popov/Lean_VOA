/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionKernelTheta
import VOA.DeligneAudit.G2Sector
import VOA.DeligneAudit.G2LieHeadline

/-!
# `G₂`: Ravinder's kernel lemma and `G₂` from the named fusion inputs

* **Generic Leibniz nilpotency** (`nil_of_ad`): if `A w = 0`, `(ad A)^{r+1} X = 0` and `X^p w = 0`,
  then `((ad A)^r X)^p w = 0`, from the Leibniz rule `(ad A)^{rp}(X^p) = c · ((ad A)^r X)^p`,
  `c ≠ 0`. This replaces the Heisenberg chain along the short `α₁`-string, where Heisenberg pairs
  do not exist.
* `g2KernelTable : KernelTable G2sector` (the `cartanN` index `1`, `θ(h₁) = -1`, is handled by the
  signed `τ`); the table scan was done outside Lean.
* `g2_thetaNil`: `f_{α₁} = x₄` kills `w`, `(ad x₄)^3 x₁₃ = 6 x₃` (`x₃ = f_{3α₁+α₂}`, long),
  `(ad x₄)^4 x₁₃ = 0`, so `x₃^{k+1} w = 0` (`nil_of_ad`); then the long `A₂` Heisenberg pair
  `[x₁₃, x₃] = x₁₂ = f_θ` gives `f_θ^{2k+1} w = 0`.
* `g2_ravinderKernelRel`, `g2_fusionModuleBoundZ_of_totalBound`,
  `g2_classicallyFree_of_totalBound` (in `G2FusionKernelTheta`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.UnivG

open PowerSeries VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.G2 Finset

noncomputable section

/-! ## Leibniz nilpotency -/

section Leib

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V)

/-- `ad A` on endomorphisms. -/
def adL : Module.End ℂ V →ₗ[ℂ] Module.End ℂ V := LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A

theorem adL_apply (T : Module.End ℂ V) : adL A T = A * T - T * A := rfl

theorem adL_mul (S T : Module.End ℂ V) : adL A (S * T) = adL A S * T + S * adL A T := by
  simp only [adL_apply, mul_sub, sub_mul, mul_assoc]; abel

/-- The general Leibniz rule for `ad A`. -/
theorem adL_leibniz (n : ℕ) (S T : Module.End ℂ V) :
    (adL A)^[n] (S * T) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ((adL A)^[ij.1] S * (adL A)^[ij.2] T) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (M := Module.End ℂ V) (fun i j => (adL A)^[i] S * (adL A)^[j] T) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, adL_mul, smul_add,
      sum_add_distrib]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

theorem adL_iterate_kill {w : V} (hA : A w = 0) {T : Module.End ℂ V} (hT : T w = 0) :
    ∀ n, ((adL A)^[n] T) w = 0
  | 0 => hT
  | n + 1 => by
      rw [Function.iterate_succ_apply', adL_apply, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, adL_iterate_kill hA hT n, hA, map_zero, map_zero, sub_zero]

theorem adL_iterate_high {X : Module.End ℂ V} {r : ℕ} (hX : (adL A)^[r + 1] X = 0) :
    ∀ i, r + 1 ≤ i → (adL A)^[i] X = 0 := by
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (r + 1) := ⟨i - (r + 1), by omega⟩
  rw [Function.iterate_add_apply, hX]
  exact iterate_map_zero (adL A) j

theorem adL_pow_key {X : Module.End ℂ V} {r : ℕ} (hX : (adL A)^[r + 1] X = 0) :
    ∀ p : ℕ, (∀ i, r * p < i → (adL A)^[i] (X ^ p) = 0) ∧
      ∃ c : ℕ, c ≠ 0 ∧ (adL A)^[r * p] (X ^ p) = c • ((adL A)^[r] X) ^ p
  | 0 => by
      refine ⟨fun i hi => ?_, 1, one_ne_zero, by simp⟩
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [pow_zero, Function.iterate_add_apply]
      have : (adL A)^[1] (1 : Module.End ℂ V) = 0 := by simp [adL_apply]
      rw [this]; exact iterate_map_zero (adL A) j
  | p + 1 => by
      obtain ⟨ih1, c, hc, ih2⟩ := adL_pow_key hX p
      have hhigh := adL_iterate_high A hX
      have e1 : r * (p + 1) = r * p + r := Nat.mul_succ r p
      have hterm : ∀ a b, ¬ (a = r * p ∧ b = r) → r * (p + 1) ≤ a + b →
          (adL A)^[a] (X ^ p) * (adL A)^[b] X = 0 := by
        intro a b hab hle
        by_cases ha : r * p < a
        · rw [ih1 a ha, zero_mul]
        · have hb : r + 1 ≤ b := by omega
          rw [hhigh b hb, mul_zero]
      refine ⟨fun i hi => ?_, (r * (p + 1)).choose (r * p) * c, ?_, ?_⟩
      · rw [pow_succ, adL_leibniz]
        refine sum_eq_zero fun ⟨a, b⟩ hab => ?_
        rw [mem_antidiagonal] at hab
        rw [hterm a b (by omega) (by omega), smul_zero]
      · exact mul_ne_zero (Nat.choose_pos (by omega)).ne' hc
      · rw [pow_succ, adL_leibniz, sum_eq_single (r * p, r)]
        · rw [show r * p + r = r * (p + 1) by omega] at *
          rw [ih2, smul_mul_assoc, smul_smul, pow_succ]
        · rintro ⟨a, b⟩ hab hne
          rw [mem_antidiagonal] at hab
          simp only [ne_eq, Prod.mk.injEq] at hne
          rw [hterm a b hne (by omega), smul_zero]
        · intro h; exact absurd (mem_antidiagonal.mpr (by omega)) h

/-- **Leibniz nilpotency**: `A w = 0`, `(ad A)^{r+1} X = 0`, `X^p w = 0` give
`((ad A)^r X)^p w = 0`. -/
theorem nil_of_ad {w : V} (hA : A w = 0) {X : Module.End ℂ V} {r p : ℕ}
    (hX : (adL A)^[r + 1] X = 0) (hXp : (X ^ p) w = 0) : (((adL A)^[r] X) ^ p) w = 0 := by
  obtain ⟨_, c, hc, h2⟩ := adL_pow_key A hX p
  have h := adL_iterate_kill A hA hXp (r * p)
  rw [h2, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast hc)

end Leib

/-! ## The `G₂` table -/

/-- The signed `θ`-values on the Cartan basis. -/
def g2τZ (c : Fin 14) : ℤ := if c.val = 0 then 3 else if c.val = 1 then -1 else 0

/-- A Cartan acting diagonally and invertibly on each negative root vector. -/
def g2hsel (x : Fin 14) : Fin 14 := if x.val = 13 then 1 else 0

theorem g2_truncUpZ : ∀ x : Fin 14, x.val ∈ negL →
    ((g2hsel x).val = 0 ∨ (g2hsel x).val = 1) ∧ fZ br (g2hsel x) x x ≠ 0 ∧
      ∀ c : Fin 14, c ≠ x → fZ br (g2hsel x) x c = 0 := by decide +kernel

theorem g2_raisThetaZ : ∀ e c : Fin 14, e.val ∈ posL → fZ br e 12 c ≠ 0 →
    c.val = 0 ∨ c.val = 1 ∨ (c.val ∈ negL ∧ c ≠ 12) := by decide +kernel

theorem g2_cartTauZ : ∀ h c : Fin 14, (h.val = 0 ∨ h.val = 1) →
    fZ br h 12 c = if c = 12 then -g2τZ h else 0 := by decide +kernel

theorem g2_lowCommZ : ∀ x c : Fin 14, x.val ∈ negL → fZ br x 12 c = 0 := by decide +kernel

theorem g2_simpleZ : (∀ c : Fin 14, fZ br 7 13 c ≠ 0 → c.val = 0 ∨ c.val = 1) ∧
    ∑ c : Fin 14, -fZ br 7 13 c * g2τZ c = 1 ∧
    ∀ d : Fin 14, ∑ c : Fin 14, -fZ br 7 13 c * fZ br c 13 d = if d = 13 then -2 else 0 := by
  decide +kernel

theorem g2_eθZ : (∀ c : Fin 14, fZ br 6 12 c ≠ 0 → c.val = 0 ∨ c.val = 1) ∧
    ∑ c : Fin 14, fZ br 6 12 c * g2τZ c = -2 := by decide +kernel

def g2bsel (x : Fin 14) : Fin 14 :=
  if x.val = 3 then 7 else if x.val = 8 then 5 else if x.val = 11 then 2 else 9

def g2ksel (x : Fin 14) : ℤ := if x.val = 3 ∨ x.val = 11 then -1 else 1

theorem g2_rootZ : ∀ x : Fin 14, x.val ∈ negL → x ≠ 12 → x.val ≠ 4 →
    (g2bsel x).val ∈ posL ∧ g2ksel x ≠ 0 ∧
      ∀ c : Fin 14, fZ br (g2bsel x) 12 c = if c = x then g2ksel x else 0 := by decide +kernel

theorem fG2_eq (a b c : Fin 14) : fG2 a b c = ((fZ br a b c : ℤ) : ℂ) := rfl

theorem fG2_12 (a c : Fin 14) : fG2 a 12 c = ((fZ br a 12 c : ℤ) : ℂ) := rfl

theorem fG2_7_13 (c : Fin 14) : fG2 7 13 c = ((fZ br 7 13 c : ℤ) : ℂ) := rfl

theorem fG2_c13 (c d : Fin 14) : fG2 c 13 d = ((fZ br c 13 d : ℤ) : ℂ) := rfl

theorem fG2_6_12 (c : Fin 14) : fG2 6 12 c = ((fZ br 6 12 c : ℤ) : ℂ) := rfl

theorem negL_of_low (x : Fin 14) (hx : x.val ∈ negL ∨ x.val ∈ ([4, 13] : List ℕ)) :
    x.val ∈ negL := by
  rcases hx with hx | hx
  · exact hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h <;> simp [negL, h]

theorem cart01 (c : Fin 14) (h : c.val = 0 ∨ c.val = 1) :
    c.val ∈ ([0] : List ℕ) ∨ c.val ∈ ([1] : List ℕ) := by
  rcases h with h | h
  · left; simp [h]
  · right; simp [h]

theorem g2_tauH (h : Fin 14) (hh : h.val ∈ ([0] : List ℕ)) :
    ((g2τZ h : ℤ) : ℂ) = ((thetaH h : ℕ) : ℂ) := by
  have h0 : h.val = 0 := by simpa using hh
  simp [g2τZ, thetaH, h0]

theorem g2_tauN (h : Fin 14) (hh : h.val ∈ ([1] : List ℕ)) :
    ((g2τZ h : ℤ) : ℂ) = -((thetaN h : ℕ) : ℂ) := by
  have h1 : h.val = 1 := by simpa using hh
  simp [g2τZ, thetaN, h1]

theorem g2_truncUp (x : Fin 14) (hx : x.val ∈ negL ∨ x.val ∈ ([4, 13] : List ℕ)) :
    ∃ h : Fin 14, (h.val ∈ ([0] : List ℕ) ∨ h.val ∈ ([1] : List ℕ)) ∧ fG2 h x x ≠ 0 ∧
      ∀ c, c ≠ x → fG2 h x c = 0 := by
  obtain ⟨h1, h2, h3⟩ := g2_truncUpZ x (negL_of_low x hx)
  refine ⟨g2hsel x, cart01 _ h1, ?_, fun c hc => ?_⟩
  · rw [fG2_eq]; exact_mod_cast h2
  · rw [fG2_eq, h3 c hc, Int.cast_zero]

theorem g2_raisTheta (e : Fin 14) (he : e.val ∈ posL) (c : Fin 14) (hc : fG2 e 12 c ≠ 0) :
    (c.val ∈ ([0] : List ℕ) ∨ c.val ∈ ([1] : List ℕ)) ∨ (c.val ∈ negL ∧ c ≠ 12) := by
  rw [fG2_12] at hc
  rcases g2_raisThetaZ e c he (by exact_mod_cast hc) with h | h | h
  · exact Or.inl (cart01 c (Or.inl h))
  · exact Or.inl (cart01 c (Or.inr h))
  · exact Or.inr h

theorem g2_cartTau (h : Fin 14) (hh : h.val ∈ ([0] : List ℕ) ∨ h.val ∈ ([1] : List ℕ))
    (c : Fin 14) : fG2 h 12 c = if c = 12 then -((g2τZ h : ℤ) : ℂ) else 0 := by
  have hh' : h.val = 0 ∨ h.val = 1 := by
    rcases hh with hh | hh
    · left; simpa using hh
    · right; simpa using hh
  rw [fG2_12, g2_cartTauZ h c hh']
  split_ifs <;> simp

theorem g2_lowComm (x : Fin 14) (hx : x.val ∈ negL ∨ x.val ∈ ([4, 13] : List ℕ)) (c : Fin 14) :
    fG2 x 12 c = 0 := by
  rw [fG2_12, g2_lowCommZ x c (negL_of_low x hx), Int.cast_zero]

theorem g2_lowExp_le (i : Fin 14) : lowExpS i ≤ 1 := by
  unfold lowExpS; split_ifs <;> omega

theorem g2_simple (i : Fin 14) (h1 : lowExpS i = 1) :
    ∃ (e : Fin 14) (s : ℂ), e.val ∈ posL ∧
      (∀ c, fG2 e i c ≠ 0 → c.val ∈ ([0] : List ℕ) ∨ c.val ∈ ([1] : List ℕ)) ∧
      ∑ c, s * fG2 e i c * ((g2τZ c : ℤ) : ℂ) = 1 ∧
      ∀ d, ∑ c, s * fG2 e i c * fG2 c i d = if d = i then -2 else 0 := by
  have hi13 : i = (13 : Fin 14) := by
    unfold lowExpS at h1
    split_ifs at h1 with h4 h13
    exact Fin.ext h13
  subst hi13
  obtain ⟨s1, s2, s3⟩ := g2_simpleZ
  refine ⟨7, -1, by decide, fun c hc => ?_, ?_, fun d => ?_⟩
  · rw [fG2_7_13] at hc
    exact cart01 c (s1 c (by exact_mod_cast hc))
  · have := congrArg (fun z : ℤ => (z : ℂ)) s2
    push_cast at this
    rw [show (∑ c : Fin 14, (-1 : ℂ) * fG2 7 13 c * ((g2τZ c : ℤ) : ℂ)) =
        ∑ c : Fin 14, -((fZ br 7 13 c : ℤ) : ℂ) * ((g2τZ c : ℤ) : ℂ) from
      sum_congr rfl fun c _ => by rw [fG2_7_13]; ring, this]
  · have := congrArg (fun z : ℤ => (z : ℂ)) (s3 d)
    push_cast at this
    rw [show (∑ c : Fin 14, (-1 : ℂ) * fG2 7 13 c * fG2 c 13 d) =
        ∑ c : Fin 14, -((fZ br 7 13 c : ℤ) : ℂ) * ((fZ br c 13 d : ℤ) : ℂ) from
      sum_congr rfl fun c _ => by rw [fG2_7_13, fG2_c13]; ring, this]

theorem g2_eθ_cartan (c : Fin 14) (hc : fG2 6 12 c ≠ 0) :
    c.val ∈ ([0] : List ℕ) ∨ c.val ∈ ([1] : List ℕ) := by
  rw [fG2_6_12] at hc
  exact cart01 c (g2_eθZ.1 c (by exact_mod_cast hc))

theorem g2_eθ_theta : (-1 : ℂ) * ∑ c : Fin 14, fG2 6 12 c * ((g2τZ c : ℤ) : ℂ) = 2 := by
  have := congrArg (fun z : ℤ => (z : ℂ)) g2_eθZ.2
  push_cast at this
  simp only [fG2_6_12]
  rw [this]; norm_num

theorem g2_fusionRoot (x : Fin 14) (hx : x.val ∈ negL) (hx0 : x ≠ 12) :
    (∃ (β : Fin 14) (κ : ℂ), β.val ∈ posL ∧ κ ≠ 0 ∧ ∀ c, fG2 β 12 c = if c = x then κ else 0) ∨
      (x.val ∈ ([4, 13] : List ℕ) ∧ lowExpS x = 0) := by
  by_cases h4 : x.val = 4
  · right
    refine ⟨by simp [h4], ?_⟩
    unfold lowExpS; simp [h4]
  · left
    obtain ⟨h1, h2, h3⟩ := g2_rootZ x hx hx0 h4
    refine ⟨g2bsel x, (g2ksel x : ℂ), h1, by exact_mod_cast h2, fun c => ?_⟩
    rw [fG2_12, h3 c]; split_ifs <;> simp

/-- **The `G₂` kernel table.** -/
def g2KernelTable : KernelTable G2sector where
  τ c := ((g2τZ c : ℤ) : ℂ)
  tauH := g2_tauH
  tauN := g2_tauN
  c0_fusion := show ((12 : Fin 14) : ℕ) ∈ negL by decide
  truncUp := g2_truncUp
  raisTheta := g2_raisTheta
  cartTau := g2_cartTau
  lowComm := g2_lowComm
  lowExp_le i _ := g2_lowExp_le i
  simple i _ h1 := g2_simple i h1
  eθ := (6 : Fin 14)
  sθ := -1
  eθ_raising := show ((6 : Fin 14) : ℕ) ∈ posL by decide
  eθ_cartan := g2_eθ_cartan
  eθ_theta := g2_eθ_theta
  kill0 x := G2sector.lowering x ∧ G2sector.lowExp x = 0
  rk _ := 0
  kill0_low _ h := Or.inr h.1
  kill0_gen _ h := Or.inl h
  fusionRoot := g2_fusionRoot

end

end VOA.DeligneAudit.UnivG

section AxiomAudit
#print axioms VOA.DeligneAudit.UnivG.nil_of_ad
#print axioms VOA.DeligneAudit.UnivG.g2KernelTable
end AxiomAudit
