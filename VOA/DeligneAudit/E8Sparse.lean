/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7Sparse

/-!
# Bucketed sparse cubic identities (for `E₈`)

`E7Sparse.cubicZero` sorts the whole term list in the kernel; for the `E₈` U3 certificates
(up to ~14 600 cubic terms per current) one such `decide` peaks at ~11 GB.  Here the monomial keys
are split into ranges (`BucketChain`): each range is checked by its own `cubicZero` on the
filtered list (a separate `decide`, ~3 000 terms, ~5 GB), and `cubicP_eq_zero_of_chain` glues them.

* `keyOf t` — the canonical key of a cubic term (`< 2²⁴` for indices `< 256`);
* `inR lo hi` — key in `[lo, hi)`;
* **`cubicP_eq_zero_of_chain`**: `small l`, and a chain `0 = b₀ ≤ b₁ ≤ … ≤ b_m` with
  `2²⁴ ≤ b_m` and every bucket zero, give `cubicP l = 0`;
* **`mem_of_cubicP_zero`**: then `X_a · Q` lies in the ideal.
-/

namespace VOA.DeligneAudit.E8Sparse

open MvPolynomial VOA.DeligneAudit.E7Sparse

noncomputable section

variable {n : ℕ}

/-- The canonical key of a cubic term. -/
def keyOf (t : CTerm) : ℕ := enc3 (sort3 t.2)

/-- The key lies in `[lo, hi)`. -/
def inR (lo hi : ℕ) (t : CTerm) : Bool := decide (lo ≤ keyOf t) && decide (keyOf t < hi)

/-- The key is `≥ lo`. -/
def geR (lo : ℕ) (t : CTerm) : Bool := decide (lo ≤ keyOf t)

/-- A chain of buckets covering `[lo, 2²⁴)`, each with vanishing sum. -/
def BucketChain (l : List CTerm) : List ℕ → Prop
  | [] => False
  | [hi] => 16777216 ≤ hi
  | lo :: hi :: rest => lo ≤ hi ∧ cubicZero (l.filter (inR lo hi)) = true ∧
      BucketChain l (hi :: rest)

theorem cubicP_filter_split (l : List CTerm) (p q r : CTerm → Bool)
    (h : ∀ t ∈ l, p t = (q t || r t)) (hd : ∀ t ∈ l, (q t && r t) = false) :
    cubicP n (l.filter p) = cubicP n (l.filter q) + cubicP n (l.filter r) := by
  induction l with
  | nil => simp [cubicP]
  | cons t l ih =>
    have ih' := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      (fun s hs => hd s (List.mem_cons_of_mem _ hs))
    have ht := h t (List.mem_cons_self ..)
    have hdt := hd t (List.mem_cons_self ..)
    by_cases hq : q t = true
    · have hr : r t = false := by simpa [hq] using hdt
      have hp : p t = true := by rw [ht, hq]; rfl
      simp only [List.filter_cons, hp, hq, hr, if_true, if_false, Bool.false_eq_true]
      rw [cubicP_cons, cubicP_cons, ih']; ring
    · simp only [Bool.not_eq_true] at hq
      by_cases hr : r t = true
      · have hp : p t = true := by rw [ht, hq, hr]; rfl
        simp only [List.filter_cons, hp, hq, hr, if_true, if_false, Bool.false_eq_true]
        rw [cubicP_cons, cubicP_cons, ih']; ring
      · simp only [Bool.not_eq_true] at hr
        have hp : p t = false := by rw [ht, hq, hr]; rfl
        simp only [List.filter_cons, hp, hq, hr, if_false, Bool.false_eq_true]
        exact ih'

theorem enc3_lt (k : ℕ × ℕ × ℕ) (h0 : k.1 < 256) (h1 : k.2.1 < 256) (h2 : k.2.2 < 256) :
    enc3 k < 16777216 := by
  obtain ⟨a, b, c⟩ := k
  simp only [enc3] at *
  omega

theorem sort3_fst_lt (k : ℕ × ℕ × ℕ) (h0 : k.1 < 256) (h1 : k.2.1 < 256) (h2 : k.2.2 < 256) :
    (sort3 k).1 < 256 := by
  obtain ⟨a, b, c⟩ := k
  simp only [sort3] at *
  split_ifs <;> simp <;> omega

theorem keyOf_lt (t : CTerm) (h : (t.2.1 < 256 && t.2.2.1 < 256 && t.2.2.2 < 256) = true) :
    keyOf t < 16777216 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hs := sort3_lt t.2 h0 h1 h2
  have h0' : (sort3 t.2).1 < 256 := sort3_fst_lt t.2 h0 h1 h2
  exact enc3_lt _ h0' hs.1 hs.2

theorem cubicP_ge_eq_zero (l : List CTerm) (hsmall : small l = true) :
    ∀ (bs : List ℕ) (lo : ℕ), BucketChain l (lo :: bs) → cubicP n (l.filter (geR lo)) = 0 := by
  intro bs
  induction bs with
  | nil =>
    intro lo h
    simp only [BucketChain] at h
    have hnil : l.filter (geR lo) = [] := by
      rw [List.filter_eq_nil_iff]
      intro t ht
      have hk := keyOf_lt t (List.all_eq_true.mp hsmall t ht)
      simp only [geR, decide_eq_true_eq]
      omega
    rw [hnil]; rfl
  | cons hi rest ih =>
    intro lo h
    simp only [BucketChain] at h
    obtain ⟨hle, hz, hrest⟩ := h
    rw [cubicP_filter_split l (geR lo) (inR lo hi) (geR hi)
      (fun t _ => by
        simp only [geR, inR]
        by_cases h1 : lo ≤ keyOf t <;> by_cases h2 : keyOf t < hi <;> by_cases h3 : hi ≤ keyOf t <;>
          simp [h1, h2, h3] <;> omega)
      (fun t _ => by
        simp only [geR, inR]
        by_cases h2 : keyOf t < hi <;> by_cases h3 : hi ≤ keyOf t <;> simp [h2, h3] <;> omega),
      cubicP_eq_zero_of_cubicZero _ hz, ih hi hrest, add_zero]

/-- **A bucket chain from `0` proves the identity.** -/
theorem cubicP_eq_zero_of_chain (l : List CTerm) (hsmall : small l = true) (bs : List ℕ)
    (h : BucketChain l (0 :: bs)) : cubicP n l = 0 := by
  have := cubicP_ge_eq_zero (n := n) l hsmall bs 0 h
  have hf : l.filter (geR 0) = l := by
    rw [List.filter_eq_self]
    intro t _
    simp [geR]
  rwa [hf] at this

/-- **Ideal membership from a vanishing certificate identity.** -/
theorem mem_of_cubicP_zero (relQ : ℕ → List (ℕ × ℕ × ℤ)) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : List (ℕ × ℕ × ℤ)) (a : ℕ) (L : ℤ) (hL : L ≠ 0) (cert : List (ℤ × ℕ × ℕ))
    (hrel : ∀ t ∈ cert, quadP n (relQ t.2.2) ∈ I)
    (h0 : cubicP n (mulX L a q ++ negT (certExp relQ cert)) = 0) :
    Xn n a * quadP n q ∈ I := by
  rw [cubicP_append, cubicP_negT, cubicP_mulX, certExp, cubicP_flatMap] at h0
  have hsum : (L : MvPolynomial (Fin n) ℂ) * Xn n a * quadP n q
      = (cert.map fun t => cubicP n (mulX t.1 t.2.1 (relQ t.2.2))).sum := by
    linear_combination h0
  have hmem : (L : MvPolynomial (Fin n) ℂ) * Xn n a * quadP n q ∈ I := by
    rw [hsum]
    refine list_sum_mem fun y hy => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    rw [cubicP_mulX]
    exact I.mul_mem_left _ (hrel t ht)
  have hC : (L : MvPolynomial (Fin n) ℂ) = C (L : ℂ) := by simp
  have h2 := I.mul_mem_left (C ((L : ℂ)⁻¹)) hmem
  rwa [hC, mul_assoc, ← mul_assoc (C _), ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hL),
    map_one, one_mul] at h2

end

end VOA.DeligneAudit.E8Sparse

section AxiomAudit
#print axioms VOA.DeligneAudit.E8Sparse.cubicP_eq_zero_of_chain
#print axioms VOA.DeligneAudit.E8Sparse.mem_of_cubicP_zero
end AxiomAudit
