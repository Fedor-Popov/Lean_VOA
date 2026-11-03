/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneFusionFiniteGAlg
import VOA.DeligneAudit.DeligneFusionFiniteGCert
import VOA.DeligneAudit.DeligneFusionPBW

/-!
# Local nilpotency of the grade-0 letters for a Deligne sector

For sector data `S` and a current-algebra module `ρ` with a vector `w`:

* `adR_iterate_op`: `(ad x₀)^j (y ⊗ t^r) = Σ_c adCo x j y c • (c ⊗ t^r)`, and the coefficients
  respect the weights (`adCo_wt`). Since the weights are bounded, **every letter of nonzero weight
  is `ad`-nilpotent of order `adK S = 2B+1`** (`adR_iterate_adK`), with no per-type computation.
* `pow_kill_word` (Kac's lemma): if `x` has nonzero weight and `x₀^N w = 0`, then
  `x₀^(N + adK·|l|)` kills `wordOp l w` for every word `l`.
* `known_step`: if `X₀` and `Y₀` are nilpotent on `w`, `Y` has nonzero weight, and the
  `ad X`-string from `Y` runs through single basis vectors `Y = a₀, a₁, …, a_q` with nonzero
  structure constants and stops (`pathChk`), then `(a_q)₀` is nilpotent on `w`. This is
  `top_nil`; it needs neither Heisenberg pairs nor simply-laced strings.
* `known_of_certValid`: a certificate (a list of such steps, `certValid`, a `Bool` check on an
  integer table) propagates nilpotency from an initial set (raising and simple lowering letters).
-/

namespace VOA.DeligneAudit.FiniteG

open Finset VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector

noncomputable section

variable (S : DeligneSectorData)

/-! ## Commutators of letters -/

section Comm

variable {S} {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)

theorem op_comm_end (a b : Fin S.n) (r s : ℕ) :
    ρ.op a r * ρ.op b s - ρ.op b s * ρ.op a r = ∑ e, S.f a b e • ρ.op e (r + s) := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  exact ρ.comm a b r s x

theorem adR_op (a b : Fin S.n) (r : ℕ) :
    adR (ρ.op a 0) (ρ.op b r) = ∑ e, S.f a b e • ρ.op e r := by
  rw [adR_apply, op_comm_end, zero_add]

theorem adR_smul (X T : Module.End ℂ V) (k : ℂ) : adR X (k • T) = k • adR X T := by
  simp only [adR_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem adR_iterate_smul (X T : Module.End ℂ V) (k : ℂ) :
    ∀ j, (adR X)^[j] (k • T) = k • (adR X)^[j] T
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', adR_iterate_smul X T k j,
        adR_smul]

end Comm

/-! ## `ad`-coefficients and weights -/

/-- Coefficients of `(ad x)^j y` in the basis. -/
def adCo (x : Fin S.n) : ℕ → Fin S.n → Fin S.n → ℂ
  | 0, y => Pi.single y 1
  | j + 1, y => fun c => ∑ e, S.f x e c * adCo x j y e

section Coeff

variable {S} {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)

theorem adR_iterate_op (x y : Fin S.n) (r : ℕ) :
    ∀ j, (adR (ρ.op x 0))^[j] (ρ.op y r) = ∑ c, adCo S x j y c • ρ.op c r
  | 0 => by
      simp only [Function.iterate_zero, id_eq, adCo]
      rw [Finset.sum_eq_single y (fun c _ hc => by rw [Pi.single_eq_of_ne hc, zero_smul])
        (by simp)]
      simp
  | j + 1 => by
      rw [Function.iterate_succ_apply', adR_iterate_op x y r j, map_sum]
      simp only [adR_smul, adR_op, Finset.smul_sum, smul_smul, adCo]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [mul_comm]

end Coeff

theorem adCo_wt (x y : Fin S.n) : ∀ j c, adCo S x j y c ≠ 0 → S.wt c = S.wt y + j • S.wt x
  | 0, c, h => by
      simp only [adCo] at h
      by_cases hc : c = y
      · subst hc; simp
      · simp [hc] at h
  | j + 1, c, h => by
      simp only [adCo] at h
      obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h1 : S.f x e c ≠ 0 := left_ne_zero_of_mul he
      have h2 : adCo S x j y e ≠ 0 := right_ne_zero_of_mul he
      have hw1 : S.wt c = S.wt x + S.wt e := by
        by_contra hc; exact h1 (S.table_wt x e c hc)
      rw [hw1, adCo_wt x y j e h2, succ_nsmul]
      abel

/-- A bound on all weight coordinates. -/
def wtB : ℕ := ∑ c : Fin S.n, ∑ i : Fin S.R, (S.wt c i).natAbs

theorem wt_le (c : Fin S.n) (i : Fin S.R) : (S.wt c i).natAbs ≤ wtB S := by
  unfold wtB
  refine le_trans ?_ (Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ c))
  exact Finset.single_le_sum (f := fun i => (S.wt c i).natAbs) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- The uniform `ad`-nilpotency order of the letters of nonzero weight. -/
def adK : ℕ := 2 * wtB S + 1

theorem adCo_adK (x y c : Fin S.n) (hx : S.wt x ≠ 0) : adCo S x (adK S) y c = 0 := by
  by_contra h
  have hw := adCo_wt S x y _ c h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hwi := congrFun hw i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hwi hi
  have b1 := wt_le S c i
  have b2 := wt_le S y i
  have hK : (adK S : ℤ) = 2 * (wtB S : ℤ) + 1 := by simp [adK]
  have ha : 1 ≤ |S.wt x i| := Int.one_le_abs hi
  have e1 : |S.wt c i| ≤ (wtB S : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast b1
  have e2 : |S.wt y i| ≤ (wtB S : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast b2
  have e3 : |((adK S : ℕ) : ℤ) * S.wt x i| = (adK S : ℤ) * |S.wt x i| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have e4 : ((adK S : ℕ) : ℤ) * S.wt x i = S.wt c i - S.wt y i := by
    rw [hwi]; ring
  have e5 : |S.wt c i - S.wt y i| ≤ |S.wt c i| + |S.wt y i| := abs_sub _ _
  rw [e4] at e3
  nlinarith [abs_nonneg (S.wt x i)]

section Nil

variable {S} {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)

/-- Letters of nonzero weight are `ad`-nilpotent of order `adK S`. -/
theorem adR_iterate_adK (x y : Fin S.n) (hx : S.wt x ≠ 0) (r : ℕ) :
    (adR (ρ.op x 0))^[adK S] (ρ.op y r) = 0 := by
  rw [adR_iterate_op]
  exact Finset.sum_eq_zero fun c _ => by rw [adCo_adK S x y c hx, zero_smul]

/-- **Kac's lemma on words.** -/
theorem pow_kill_word (x : Fin S.n) (hx : S.wt x ≠ 0) {w : V} {N : ℕ}
    (hw : (ρ.op x 0 ^ N) w = 0) :
    ∀ l : List (Fin S.n × ℕ), (ρ.op x 0 ^ (N + adK S * l.length)) (wordOp ρ l w) = 0
  | [] => by simpa using hw
  | (a :: l) => by
      have ih := pow_kill_word x hx hw l
      have := pow_kill_of_ad (ρ.op x 0) (ρ.op a.1 a.2) (adK S) _ (wordOp ρ l w)
        (adR_iterate_adK ρ x a.1 hx a.2) ih
      rw [List.length_cons, show N + adK S * (l.length + 1) = N + adK S * l.length + adK S by ring]
      exact this

theorem pow_eq_wordOp (x : Fin S.n) (w : V) :
    ∀ k : ℕ, (ρ.op x 0 ^ k) w = wordOp ρ (List.replicate k (x, 0)) w
  | 0 => rfl
  | k + 1 => by
      rw [pow_succ', Module.End.mul_apply, pow_eq_wordOp x w k]; rfl

/-- Nilpotency of the grade-0 letter `c` on `w`. -/
def Known (w : V) (c : Fin S.n) : Prop := ∃ N, (ρ.op c 0 ^ N) w = 0

end Nil

/-! ## Single-vector `ad`-strings -/

section Path

variable {S} {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)

theorem adR_op_single {X a b : Fin S.n} (h : singleChk S.wt X a b = true) (r : ℕ) :
    adR (ρ.op X 0) (ρ.op a r) = S.f X a b • ρ.op b r := by
  rw [adR_op]
  refine Finset.sum_eq_single b (fun c _ hc => ?_) (by simp)
  simp only [singleChk, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  rcases h c with h | h
  · exact absurd h hc
  · have hf : S.f X a c = 0 := S.table_wt X a c (fun he => by
      rw [(wEqB_iff _ _).mpr he] at h; exact Bool.noConfusion h)
    rw [hf, zero_smul]

theorem adR_op_top {X a : Fin S.n} (h : topChk S.wt X a = true) (r : ℕ) :
    adR (ρ.op X 0) (ρ.op a r) = 0 := by
  rw [adR_op]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [topChk, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at h
  have h := h c
  have hf : S.f X a c = 0 := S.table_wt X a c (fun he => by
    rw [(wEqB_iff _ _).mpr he] at h; exact Bool.noConfusion h)
  rw [hf, zero_smul]

theorem adR_path {fnz : Fin S.n → Fin S.n → Fin S.n → Bool}
    (hfz : ∀ a b c, fnz a b c = true → S.f a b c ≠ 0)
    (X : Fin S.n) : ∀ (path : List (Fin S.n)) (a : Fin S.n), pathChk S.wt fnz X a path = true →
      ∃ κ : ℂ, κ ≠ 0 ∧ (adR (ρ.op X 0))^[path.length] (ρ.op a 0) = κ • ρ.op (path.getLastD a) 0 ∧
        (adR (ρ.op X 0))^[path.length + 1] (ρ.op a 0) = 0
  | [], a, h => by
      simp only [pathChk] at h
      exact ⟨1, one_ne_zero, by simp, by simp [adR_op_top ρ h]⟩
  | (b :: rest), a, h => by
      simp only [pathChk, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨κ, hκ, e1, e2⟩ := adR_path hfz X rest b h3
      have hs := adR_op_single ρ h1 0
      refine ⟨S.f X a b * κ, mul_ne_zero (hfz _ _ _ h2) hκ, ?_, ?_⟩
      · rw [List.length_cons, Function.iterate_succ_apply, hs, adR_iterate_smul, e1,
          List.getLastD_cons, smul_smul]
      · rw [List.length_cons, Function.iterate_succ_apply, hs, adR_iterate_smul, e2, smul_zero]

/-- **One step of the nilpotency chain.** -/
theorem known_step {fnz : Fin S.n → Fin S.n → Fin S.n → Bool}
    (hfz : ∀ a b c, fnz a b c = true → S.f a b c ≠ 0)
    {w : V} {X Y : Fin S.n} {path : List (Fin S.n)} (hX : Known ρ w X) (hY : Known ρ w Y)
    (hYw : S.wt Y ≠ 0) (hp : pathChk S.wt fnz X Y path = true) :
    Known ρ w (path.getLastD Y) := by
  obtain ⟨NX, hNX⟩ := hX
  obtain ⟨NY, hNY⟩ := hY
  obtain ⟨κ, hκ, e1, e2⟩ := adR_path ρ hfz X path Y hp
  refine ⟨NY + adK S * NX, ?_⟩
  have := top_nil (ρ.op X 0) (ρ.op Y 0) path.length NX (NY + adK S * NX) w e2 hNX
    (fun b hb => by
      rw [pow_eq_wordOp ρ X w b]
      refine pow_kill_mono _ (pow_kill_word ρ Y hYw hNY _) ?_
      simp only [List.length_replicate]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hb.le) _)
  rw [e1, smul_pow, LinearMap.smul_apply, smul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hκ)

end Path

/-! ## Certificates -/

section Cert

variable {S} {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule S.f V)

/-- **A valid certificate propagates nilpotency.** -/
theorem known_of_certValid {fnz : Fin S.n → Fin S.n → Fin S.n → Bool}
    (hfz : ∀ a b c, fnz a b c = true → S.f a b c ≠ 0) {w : V} :
    ∀ (cert : List (Step S.n)) (kn : Fin S.n → Bool), (∀ c, kn c = true → Known ρ w c) →
      certValid S.wt fnz kn cert = true → ∀ c, certKnown kn cert c = true → Known ρ w c
  | [], kn, hkn, _, c, hc => hkn c hc
  | ((X, Y, p) :: rest), kn, hkn, hv, c, hc => by
      simp only [certValid, Bool.and_eq_true, Bool.not_eq_true'] at hv
      obtain ⟨⟨⟨⟨hX, hY⟩, hYw⟩, hp⟩, hrest⟩ := hv
      have hYw' : S.wt Y ≠ 0 := fun h => by
        rw [(wEqB_iff _ _).mpr h] at hYw
        exact Bool.noConfusion hYw
      refine known_of_certValid hfz rest _ (fun c hc => ?_) hrest c hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | rfl
      · exact hkn c hc
      · exact known_step ρ hfz (hkn X hX) (hkn Y hY) hYw' hp

end Cert

end

end VOA.DeligneAudit.FiniteG

section AxiomAudit
#print axioms VOA.DeligneAudit.FiniteG.pow_kill_word
#print axioms VOA.DeligneAudit.FiniteG.known_step
#print axioms VOA.DeligneAudit.FiniteG.known_of_certValid
end AxiomAudit
