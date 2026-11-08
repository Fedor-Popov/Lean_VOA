/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessUntwisted

/-!
# The short-class combinatorics of the Griess dictionary, from additivity of `phi0`

`ShortSignDictionary ζ` (`MoonshineCNGriessUntwisted`) has three fields that do not involve the
phases `ζ`: `pm_injective`, `sum_shape`, `sum_exists`.  This file derives all three from two
properties of Axiom's coordinate map `phi0 : C × Cocode → Λ/2Λ`:

* additivity `phi0 (p + q) = phi0 p + phi0 q` (the source's `lamT_add`, the bundling of `phi0`
  as a `ZMod 2`-linear map) — for `sum_shape` and `sum_exists`;
* injectivity of `phi0` (half of the source's `phi0Equiv`) — for `pm_injective`.

The lattice input is the classical fact that three minimal Leech vectors with
`γ ≡ α + β (mod 2Λ)` satisfy `⟨α,β⟩ = ∓2` and `γ = ±(α ± β)` (`minVecs_class_add_cases`): the four
vectors `γ ± α ± β` all lie in `2Λ`, whose nonzero vectors have norm `≥ 16`, and the parallelogram
law leaves no room unless one of them vanishes.

## Main results
* `classOf_uvec` — `classOf (uvec c) = phi0 c.1`.
* ⭐ `minVecs_class_add_cases` — the mod-`2Λ` sum of two minimal vectors, in Axiom's coordinates.
* ⭐ `shortVec_pm_injective` (from injectivity), ⭐ `shortVec_sum_shape` and ⭐ `shortVec_sum_exists`
  (from additivity).
* ⭐ `ShortSignDictionary.of_phi0` — a sign dictionary from additivity and injectivity of `phi0`
  and the three phase conditions `sq`, `sign_neg_two`, `sign_two` alone.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.IntegralLattice
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.Code
  VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.MonsterGriess.LeechMatch (leechEquiv classOf_eq_iff classOf_of_mem
  thirtytwo_le_dot dot_self_of_mem_minVecs leechEquiv_dotProduct)
open Matrix

/-! ## §1  Classes of short vectors -/

theorem classOf_uvec (c : ShortIdx) : classOf (uvec c) = phi0 c.1 := by
  have h0 := c.2.choose_spec
  unfold uvec
  split_ifs
  · exact h0.2
  · rw [(classOf_eq_iff (neg_mem_minVecs h0.1) h0.1).2 (Or.inr rfl), h0.2]

theorem classOf_add_of_mem {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice MonsterGriess.Code.C) (hv : v ∈ codeLattice MonsterGriess.Code.C) :
    classOf (u + v) = classOf u + classOf v := by
  rw [classOf_of_mem (add_mem_codeLattice allOnes_mem_C hu hv), classOf_of_mem hu,
    classOf_of_mem hv, ← Submodule.Quotient.mk_add]
  rfl

/-- `(c + p a + q b)·(c + p a + q b)` expanded. -/
theorem dot_comb (c a b : Fin 24 → ℤ) (p q : ℤ) :
    (c + p • a + q • b) ⬝ᵥ (c + p • a + q • b)
      = c ⬝ᵥ c + p ^ 2 * (a ⬝ᵥ a) + q ^ 2 * (b ⬝ᵥ b) + 2 * p * (c ⬝ᵥ a) + 2 * q * (c ⬝ᵥ b)
        + 2 * p * q * (a ⬝ᵥ b) := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm a c, dotProduct_comm b c, dotProduct_comm b a]
  ring

/-- A vector of `2Λ` (in Axiom's coordinates) is `0` or has norm `≥ 128`. -/
theorem two_smul_dot_cases (w : ↥(codeLatticeSubgroup allOnes_mem_C)) :
    (w : Fin 24 → ℤ) = 0 ∨
      128 ≤ ((2 : ℤ) • (w : Fin 24 → ℤ)) ⬝ᵥ ((2 : ℤ) • (w : Fin 24 → ℤ)) := by
  by_cases hw : w = 0
  · left
    rw [hw]
    rfl
  · right
    have h := thirtytwo_le_dot w hw
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    omega

/-- ⭐ **The mod-`2Λ` sum of two minimal vectors** (Axiom's coordinates, `u·u = 32` for minimal `u`):
if `classOf c = classOf a + classOf b` for minimal `a, b, c`, then either `a·b = −16` and
`c = ±(a + b)`, or `a·b = 16` and `c = ±(b − a)`. -/
theorem minVecs_class_add_cases {a b c : Fin 24 → ℤ} (ha : a ∈ minVecs) (hb : b ∈ minVecs)
    (hc : c ∈ minVecs) (h : classOf c = classOf a + classOf b) :
    (a ⬝ᵥ b = -16 ∧ (c = a + b ∨ c = -(a + b))) ∨ (a ⬝ᵥ b = 16 ∧ (c = b - a ∨ c = -(b - a))) := by
  have haa := dot_self_of_mem_minVecs ha
  have hbb := dot_self_of_mem_minVecs hb
  have hcc := dot_self_of_mem_minVecs hc
  have hab : a + b ∈ codeLattice MonsterGriess.Code.C := add_mem_codeLattice allOnes_mem_C ha.1 hb.1
  have h' : classOf c = classOf (a + b) := by rw [h, classOf_add_of_mem ha.1 hb.1]
  rw [classOf_of_mem hc.1, classOf_of_mem hab, Submodule.Quotient.eq, mem_two_range_iff] at h'
  obtain ⟨w, hw⟩ := h'
  have hw1 : (2 : ℤ) • (w : Fin 24 → ℤ) = c + (-1 : ℤ) • a + (-1 : ℤ) • b := by
    rw [hw]
    change c - (a + b) = _
    simp only [neg_one_smul]
    abel
  let A : ↥(codeLatticeSubgroup allOnes_mem_C) := ⟨a, ha.1⟩
  let B : ↥(codeLatticeSubgroup allOnes_mem_C) := ⟨b, hb.1⟩
  have hw2 : (2 : ℤ) • ((w + A + B : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = c + (1 : ℤ) • a + (1 : ℤ) • b := by
    change (2 : ℤ) • ((w : Fin 24 → ℤ) + a + b) = _
    rw [smul_add, smul_add, hw1]
    simp only [neg_one_smul, one_smul, two_smul]
    abel
  have hw3 : (2 : ℤ) • ((w + A : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = c + (1 : ℤ) • a + (-1 : ℤ) • b := by
    change (2 : ℤ) • ((w : Fin 24 → ℤ) + a) = _
    rw [smul_add, hw1]
    simp only [neg_one_smul, one_smul, two_smul]
    abel
  have hw4 : (2 : ℤ) • ((w + B : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = c + (-1 : ℤ) • a + (1 : ℤ) • b := by
    change (2 : ℤ) • ((w : Fin 24 → ℤ) + b) = _
    rw [smul_add, hw1]
    simp only [neg_one_smul, one_smul, two_smul]
    abel
  have d1 := dot_comb c a b (-1) (-1)
  have d2 := dot_comb c a b 1 1
  have d3 := dot_comb c a b 1 (-1)
  have d4 := dot_comb c a b (-1) 1
  rcases two_smul_dot_cases w with e1 | e1
  · -- `c = a + b`
    have hc' : c = a + b := by
      have h0 := hw1
      rw [e1, smul_zero] at h0
      simp only [neg_one_smul] at h0
      refine sub_eq_zero.1 ?_
      rw [show c - (a + b) = c + -a + -b by abel]
      exact h0.symm
    left
    refine ⟨?_, Or.inl hc'⟩
    rw [hc'] at hcc
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm b a] at hcc
    omega
  rcases two_smul_dot_cases (w + A + B) with e2 | e2
  · have hc' : c = -(a + b) := by
      have h0 := hw2
      rw [e2, smul_zero] at h0
      simp only [one_smul] at h0
      rw [eq_neg_iff_add_eq_zero, show c + (a + b) = c + a + b by abel]
      exact h0.symm
    left
    refine ⟨?_, Or.inr hc'⟩
    rw [hc'] at hcc
    simp only [neg_dotProduct, dotProduct_neg, neg_neg, add_dotProduct, dotProduct_add,
      dotProduct_comm b a] at hcc
    omega
  rcases two_smul_dot_cases (w + A) with e3 | e3
  · have hc' : c = b - a := by
      have h0 := hw3
      rw [e3, smul_zero] at h0
      simp only [one_smul, neg_one_smul] at h0
      refine sub_eq_zero.1 ?_
      rw [show c - (b - a) = c + a + -b by abel]
      exact h0.symm
    right
    refine ⟨?_, Or.inl hc'⟩
    rw [hc'] at hcc
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm b a] at hcc
    omega
  rcases two_smul_dot_cases (w + B) with e4 | e4
  · have hc' : c = -(b - a) := by
      have h0 := hw4
      rw [e4, smul_zero] at h0
      simp only [one_smul, neg_one_smul] at h0
      rw [eq_neg_iff_add_eq_zero, show c + (b - a) = c + -a + b by abel]
      exact h0.symm
    right
    refine ⟨?_, Or.inr hc'⟩
    rw [hc'] at hcc
    simp only [neg_dotProduct, dotProduct_neg, neg_neg, sub_dotProduct, dotProduct_sub,
      dotProduct_comm b a] at hcc
    omega
  rw [hw1, d1] at e1
  rw [hw2, d2] at e2
  rw [hw3, d3] at e3
  rw [hw4, d4] at e4
  nlinarith

/-! ## §2  The three combinatorial fields of a sign dictionary -/

theorem leechEquiv_shortVec_coe (c : ShortIdx) :
    ((leechEquiv (shortVec c) : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ) = uvec c :=
  leechEquiv_shortVec c

theorem eight_mul_form_shortVec (d e : ShortIdx) :
    uvec d ⬝ᵥ uvec e = 8 * leech.form (shortVec d) (shortVec e) := by
  rw [← leechEquiv_dotProduct, leechEquiv_shortVec_coe, leechEquiv_shortVec_coe]

/-- Equality of lattice vectors from equality of their Axiom coordinates. -/
theorem eq_of_leechEquiv_coe {x y : leech.carrier}
    (h : ((leechEquiv x : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = ((leechEquiv y : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)) : x = y :=
  leechEquiv.injective (Subtype.ext h)

theorem leechEquiv_coe_add (x y : leech.carrier) :
    ((leechEquiv (x + y) : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = (leechEquiv x : Fin 24 → ℤ) + (leechEquiv y : Fin 24 → ℤ) := by
  rw [map_add]
  rfl

theorem leechEquiv_coe_neg (x : leech.carrier) :
    ((leechEquiv (-x) : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = -(leechEquiv x : Fin 24 → ℤ) := by
  rw [map_neg]
  rfl

theorem leechEquiv_coe_sub (x y : leech.carrier) :
    ((leechEquiv (x - y) : ↥(codeLatticeSubgroup allOnes_mem_C)) : Fin 24 → ℤ)
      = (leechEquiv x : Fin 24 → ℤ) - (leechEquiv y : Fin 24 → ℤ) := by
  rw [map_sub]
  rfl

/-- ⭐ **Distinct short classes give distinct `±`-pairs**, if `phi0` is injective. -/
theorem shortVec_pm_injective (hinj : Function.Injective phi0) (c d : ShortIdx)
    (h : shortVec d = shortVec c ∨ shortVec d = -shortVec c) : d = c := by
  have hcl : classOf (uvec d) = classOf (uvec c) := by
    rw [classOf_eq_iff (uvec_mem_minVecs d) (uvec_mem_minVecs c)]
    rcases h with h | h
    · left
      rw [← leechEquiv_shortVec_coe, ← leechEquiv_shortVec_coe, h]
    · right
      rw [← leechEquiv_shortVec_coe, ← leechEquiv_shortVec_coe, h, leechEquiv_coe_neg]
  rw [classOf_uvec, classOf_uvec] at hcl
  exact Subtype.ext (hinj hcl)

/-- ⭐ **`c = d + e` forces `⟨α_d, α_e⟩ = ∓2` and `α_c = ±(α_d ± α_e)`**, if `phi0` is additive. -/
theorem shortVec_sum_shape (hadd : ∀ p q, phi0 (p + q) = phi0 p + phi0 q) (d e c : ShortIdx)
    (h : c.1 = d.1 + e.1) :
    (leech.form (shortVec d) (shortVec e) = -2 ∧
      (shortVec c = shortVec d + shortVec e ∨ shortVec c = -(shortVec d + shortVec e))) ∨
    (leech.form (shortVec d) (shortVec e) = 2 ∧
      (shortVec c = shortVec e - shortVec d ∨ shortVec c = -(shortVec e - shortVec d))) := by
  have hcl : classOf (uvec c) = classOf (uvec d) + classOf (uvec e) := by
    rw [classOf_uvec, classOf_uvec, classOf_uvec, h, hadd]
  have h8 := eight_mul_form_shortVec d e
  rcases minVecs_class_add_cases (uvec_mem_minVecs d) (uvec_mem_minVecs e)
      (uvec_mem_minVecs c) hcl with ⟨hs, hc | hc⟩ | ⟨hs, hc | hc⟩
  · refine Or.inl ⟨by omega, Or.inl (eq_of_leechEquiv_coe ?_)⟩
    rw [leechEquiv_coe_add, leechEquiv_shortVec_coe, leechEquiv_shortVec_coe,
      leechEquiv_shortVec_coe, hc]
  · refine Or.inl ⟨by omega, Or.inr (eq_of_leechEquiv_coe ?_)⟩
    rw [leechEquiv_coe_neg, leechEquiv_coe_add, leechEquiv_shortVec_coe, leechEquiv_shortVec_coe,
      leechEquiv_shortVec_coe, hc]
  · refine Or.inr ⟨by omega, Or.inl (eq_of_leechEquiv_coe ?_)⟩
    rw [leechEquiv_coe_sub, leechEquiv_shortVec_coe, leechEquiv_shortVec_coe,
      leechEquiv_shortVec_coe, hc]
  · refine Or.inr ⟨by omega, Or.inr (eq_of_leechEquiv_coe ?_)⟩
    rw [leechEquiv_coe_neg, leechEquiv_coe_sub, leechEquiv_shortVec_coe, leechEquiv_shortVec_coe,
      leechEquiv_shortVec_coe, hc]

/-- ⭐ **`⟨α_d, α_e⟩ = ±2` makes `d + e` a short coordinate**, if `phi0` is additive. -/
theorem shortVec_sum_exists (hadd : ∀ p q, phi0 (p + q) = phi0 p + phi0 q) (d e : ShortIdx)
    (h : leech.form (shortVec d) (shortVec e) = -2 ∨ leech.form (shortVec d) (shortVec e) = 2) :
    ∃ c : ShortIdx, c.1 = d.1 + e.1 := by
  have h8 := eight_mul_form_shortVec d e
  have hd := uvec_mem_minVecs d
  have he := uvec_mem_minVecs e
  have hdd := dot_self_of_mem_minVecs hd
  have hee := dot_self_of_mem_minVecs he
  have hsum : classOf (uvec d + uvec e) = phi0 (d.1 + e.1) := by
    rw [classOf_add_of_mem hd.1 he.1, classOf_uvec, classOf_uvec, hadd]
  rcases h with h | h
  · -- `u_d + u_e` is minimal
    have hm : uvec d + uvec e ∈ minVecs := by
      refine ⟨add_mem_codeLattice allOnes_mem_C hd.1 he.1, ?_⟩
      change codeForm (LeechMatch.toQ (uvec d + uvec e)) (LeechMatch.toQ (uvec d + uvec e)) = 4
      rw [LeechMatch.codeForm_toQ]
      have : (uvec d + uvec e) ⬝ᵥ (uvec d + uvec e) = 32 := by
        simp only [add_dotProduct, dotProduct_add, dotProduct_comm (uvec e) (uvec d)]
        omega
      rw [this]
      norm_num
    exact ⟨⟨d.1 + e.1, ⟨_, hm, hsum⟩⟩, rfl⟩
  · -- `u_e − u_d` is minimal and congruent to `u_d + u_e`
    have hsubm : uvec e - uvec d ∈ codeLattice MonsterGriess.Code.C := by
      rw [sub_eq_add_neg]
      exact add_mem_codeLattice allOnes_mem_C he.1 (neg_mem_codeLattice allOnes_mem_C hd.1)
    have hm : uvec e - uvec d ∈ minVecs := by
      refine ⟨hsubm, ?_⟩
      change codeForm (LeechMatch.toQ (uvec e - uvec d)) (LeechMatch.toQ (uvec e - uvec d)) = 4
      rw [LeechMatch.codeForm_toQ]
      have : (uvec e - uvec d) ⬝ᵥ (uvec e - uvec d) = 32 := by
        simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (uvec e) (uvec d)]
        omega
      rw [this]
      norm_num
    have hcong : classOf (uvec e - uvec d) = classOf (uvec d + uvec e) := by
      rw [classOf_of_mem hsubm, classOf_of_mem (add_mem_codeLattice allOnes_mem_C hd.1 he.1),
        Submodule.Quotient.eq, mem_two_range_iff]
      refine ⟨⟨-uvec d, neg_mem_codeLattice allOnes_mem_C hd.1⟩, ?_⟩
      change (2 : ℤ) • (-uvec d) = (uvec e - uvec d) - (uvec d + uvec e)
      rw [two_smul]
      abel
    exact ⟨⟨d.1 + e.1, ⟨_, hm, hcong.trans hsum⟩⟩, rfl⟩

/-- ⭐ **A sign dictionary from additivity and injectivity of `phi0`**: only the three phase
conditions remain. -/
theorem ShortSignDictionary.of_phi0 {ζ : ShortIdx → ℂ}
    (hadd : ∀ p q, phi0 (p + q) = phi0 p + phi0 q) (hinj : Function.Injective phi0)
    (sq : ∀ c, ζ c ^ 2 * latticeCocycle leech (shortVec c) (shortVec c) = 1)
    (sign_neg_two : ∀ d e c : ShortIdx, c.1 = d.1 + e.1 →
      leech.form (shortVec d) (shortVec e) = -2 →
      (MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * ζ c
        = ζ d * ζ e * latticeCocycle leech (shortVec d) (shortVec e))
    (sign_two : ∀ d e c : ShortIdx, c.1 = d.1 + e.1 → leech.form (shortVec d) (shortVec e) = 2 →
      (MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * ζ c
        = ζ d * ζ e * latticeCocycle leech (shortVec d) (-shortVec e)) :
    ShortSignDictionary ζ where
  sq := sq
  pm_injective := shortVec_pm_injective hinj
  sum_shape := shortVec_sum_shape hadd
  sum_exists := shortVec_sum_exists hadd
  sign_neg_two := sign_neg_two
  sign_two := sign_two

end VOA.Moonshine.GriessDictionary
