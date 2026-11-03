/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2DivisorPairOps

/-!
# The two-slot model for `PairComparison` (interface with the `A2PairW*`)

Fix two slots `a ≠ b` and spectator labels `s : Fin m → Fin 8`.  A tensor polynomial restricted to
the labellings that agree with `s` off `{a, b}` is a **pair table** `Y : Fin 8 → Fin 8 → P_m`
(`PairTable`), and `emb a b s Y = Σ_{c,d} Y c d · δ_{s[a↦c][b↦d]}`.

* `emb_apply`: `emb a b s Y t = Y (t a) (t b)` if `t` agrees with `s` off `{a,b}`, else `0`;
* `slotOp_emb_a`, `slotOp_emb_b`: the slot operators act on tables by the coadjoint matrices
  (`opA`, `opB`);
* `pairTable x a b s c d = x (s[a↦c][b↦d])`, and `tensor_eq_sum_emb`: every tensor is the sum, over
  canonical spectators (`s a = s b = 5`), of the embeddings of its pair tables.

**Interface with the W side.**  `PairWShape` is the statement proved in `A2PairW*.lean`: for
`x ∈ W_m`, `a ≠ b` and any spectators `s`, with `X = pairTable x a b s`,
* `(z_a - z_b) ∣ X c d - X d c` for all `c d` (the `Λ²` part vanishes on the diagonal), and
* `(z_a - z_b)² ∣ Σ_{c,d} fullMatrix r (c,d) · (X c d + X d c)` for every relation `r` of the full `I₂`
  (the `I₂` coordinates of the symmetric part vanish to second order).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable {m : ℕ}

/-- Two-slot tables with polynomial entries. -/
abbrev PairTable (m : ℕ) := Fin 8 → Fin 8 → Pm m

/-- The labelling `s[a↦c][b↦d]`. -/
def pairLabel (a b : Fin m) (s : Fin m → Fin 8) (c d : Fin 8) : Fin m → Fin 8 :=
  Function.update (Function.update s a c) b d

/-- The pair table of a tensor. -/
def pairTable (x : TP m) (a b : Fin m) (s : Fin m → Fin 8) : PairTable m :=
  fun c d => x (pairLabel a b s c d)

/-- Embedding a pair table. -/
def emb (a b : Fin m) (s : Fin m → Fin 8) (Y : PairTable m) : TP m :=
  ∑ c, ∑ d, Y c d • deltaT (pairLabel a b s c d)

/-- Coadjoint action in the first slot. -/
def opA (x : Fin 8) (Y : PairTable m) : PairTable m :=
  fun c d => -∑ e, MvPolynomial.C (bracketTable x c e) * Y e d

/-- Coadjoint action in the second slot. -/
def opB (x : Fin 8) (Y : PairTable m) : PairTable m :=
  fun c d => -∑ e, MvPolynomial.C (bracketTable x d e) * Y c e

/-- Agreement off the two slots. -/
def AgreeOff (a b : Fin m) (s t : Fin m → Fin 8) : Prop := ∀ k, k ≠ a → k ≠ b → t k = s k

instance (a b : Fin m) (s t : Fin m → Fin 8) : Decidable (AgreeOff a b s t) := by
  unfold AgreeOff; infer_instance

theorem pairLabel_eq_iff (a b : Fin m) (hab : a ≠ b) (s t : Fin m → Fin 8) (c d : Fin 8) :
    t = pairLabel a b s c d ↔ AgreeOff a b s t ∧ t a = c ∧ t b = d := by
  constructor
  · rintro rfl
    refine ⟨fun k hka hkb => ?_, ?_, ?_⟩
    · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
    · simp [pairLabel, Function.update_of_ne hab]
    · simp [pairLabel]
  · rintro ⟨h, rfl, rfl⟩
    funext k
    by_cases hkb : k = b
    · subst hkb; simp [pairLabel]
    · by_cases hka : k = a
      · subst hka; simp [pairLabel, Function.update_of_ne hkb]
      · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb, h k hka hkb]

theorem emb_apply (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin 8) (Y : PairTable m)
    (t : Fin m → Fin 8) :
    emb a b s Y t = if AgreeOff a b s t then Y (t a) (t b) else 0 := by
  classical
  simp only [emb, Finset.sum_apply, psmul_apply, deltaT, mul_ite, mul_one, mul_zero,
    pairLabel_eq_iff a b hab]
  by_cases h : AgreeOff a b s t
  · simp only [h, true_and]
    rw [Finset.sum_eq_single (t a)]
    · rw [Finset.sum_eq_single (t b)]
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Ne.symm hc]
    · simp
  · simp [h]

theorem agreeOff_update_a (a b : Fin m) (_hab : a ≠ b) (s t : Fin m → Fin 8) (e : Fin 8) :
    AgreeOff a b s (Function.update t a e) ↔ AgreeOff a b s t := by
  unfold AgreeOff
  refine forall_congr' fun k => ?_
  constructor
  · intro h hka hkb; have := h hka hkb; rwa [Function.update_of_ne hka] at this
  · intro h hka hkb; rw [Function.update_of_ne hka]; exact h hka hkb

theorem agreeOff_update_b (a b : Fin m) (_hab : a ≠ b) (s t : Fin m → Fin 8) (e : Fin 8) :
    AgreeOff a b s (Function.update t b e) ↔ AgreeOff a b s t := by
  unfold AgreeOff
  refine forall_congr' fun k => ?_
  constructor
  · intro h hka hkb; have := h hka hkb; rwa [Function.update_of_ne hkb] at this
  · intro h hka hkb; rw [Function.update_of_ne hkb]; exact h hka hkb

/-- **Slot `a` acts on pair tables by `opA`.** -/
theorem slotOp_emb_a (x : Fin 8) (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin 8)
    (Y : PairTable m) : slotOp x a (emb a b s Y) = emb a b s (opA x Y) := by
  funext t
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [emb_apply a b hab]
  simp only [emb_apply a b hab, agreeOff_update_a a b hab, Function.update_self,
    Function.update_of_ne (Ne.symm hab)]
  by_cases h : AgreeOff a b s t
  · simp only [h, if_true, opA]
  · simp [h]

/-- **Slot `b` acts on pair tables by `opB`.** -/
theorem slotOp_emb_b (x : Fin 8) (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin 8)
    (Y : PairTable m) : slotOp x b (emb a b s Y) = emb a b s (opB x Y) := by
  funext t
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [emb_apply a b hab]
  simp only [emb_apply a b hab, agreeOff_update_b a b hab, Function.update_self,
    Function.update_of_ne hab]
  by_cases h : AgreeOff a b s t
  · simp only [h, if_true, opB]
  · simp [h]

theorem emb_add (a b : Fin m) (s : Fin m → Fin 8) (Y Z : PairTable m) :
    emb a b s (Y + Z) = emb a b s Y + emb a b s Z := by
  simp only [emb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem emb_smul (a b : Fin m) (s : Fin m → Fin 8) (p : Pm m) (Y : PairTable m) :
    emb a b s (p • Y) = p • emb a b s Y := by
  simp only [emb, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Canonical spectators: the two slots carry the label `5`. -/
def IsCanon (a b : Fin m) (s : Fin m → Fin 8) : Prop := s a = 5 ∧ s b = 5

instance (a b : Fin m) (s : Fin m → Fin 8) : Decidable (IsCanon a b s) := by
  unfold IsCanon; infer_instance

/-- **Every tensor is the sum of the embeddings of its pair tables.** -/
theorem tensor_eq_sum_emb (x : TP m) (a b : Fin m) (hab : a ≠ b) :
    x = ∑ s ∈ Finset.univ.filter (IsCanon a b), emb a b s (pairTable x a b s) := by
  classical
  funext t
  rw [Finset.sum_apply]
  simp only [emb_apply a b hab]
  set s₀ := pairLabel a b t 5 5 with hs₀
  have hcan : IsCanon a b s₀ := by
    refine ⟨?_, ?_⟩ <;> simp [s₀, pairLabel, Function.update_of_ne hab]
  have hag : AgreeOff a b s₀ t := by
    intro k hka hkb; simp [s₀, pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
  rw [Finset.sum_eq_single s₀]
  · rw [if_pos hag, pairTable]
    congr 1
    exact ((pairLabel_eq_iff a b hab s₀ t (t a) (t b)).mpr ⟨hag, rfl, rfl⟩)
  · intro s hs hne
    rw [Finset.mem_filter] at hs
    rw [if_neg]
    intro hag'
    apply hne
    funext k
    by_cases hka : k = a
    · subst hka; rw [hs.2.1, hcan.1]
    · by_cases hkb : k = b
      · subst hkb; rw [hs.2.2, hcan.2]
      · rw [← hag' k hka hkb, hag k hka hkb]
  · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcan⟩) h

/-- **The W-side interface (proved in `A2PairW*`).** -/
structure PairWShape : Prop where
  anti : ∀ m, ∀ x ∈ currentCarrier fullMatrix m 0, ∀ a b : Fin m, a ≠ b → ∀ s c d,
    (zr (K := ℂ) a - zr b) ∣ pairTable x a b s c d - pairTable x a b s d c
  sym : ∀ m, ∀ x ∈ currentCarrier fullMatrix m 0, ∀ a b : Fin m, a ≠ b → ∀ s (r : Option (Fin 8)),
    (zr (K := ℂ) a - zr b) ^ 2 ∣ ∑ c, ∑ d, MvPolynomial.C (fullMatrix r (c, d)) *
      (pairTable x a b s c d + pairTable x a b s d c)

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.slotOp_emb_a
#print axioms VOA.DeligneAudit.A2.slotOp_emb_b
#print axioms VOA.DeligneAudit.A2.tensor_eq_sum_emb
end AxiomAudit
