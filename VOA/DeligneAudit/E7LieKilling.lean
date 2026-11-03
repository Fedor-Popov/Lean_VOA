/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieBasis
import VOA.DeligneAudit.E7LieModel
import VOA.DeligneAudit.E7LieFormChecks
import VOA.AffineGeneral.LatticeNormalization

/-!
# The Killing form of `e7Lie` on the cert basis, by invariance

No trace is computed.  From the `Killing(hβ, hβ) = 72` (`Normalization.e7_killing`) and invariance:

* `K_EF`: `Killing(E_i, F_i) = 36`, `K_cartan`: `Killing(H_j, H_i) = 36 A_{ji}`;
* `K_weight`: `(λ+μ) Killing(x,y) = 0` for `ad H`-eigenvectors (kills pairs of nonzero total weight);
* for opposite roots, `λ Killing(x_a, x_{-a}) = Killing(H, [x_a, x_{-a}])`.

**`killing_xs`**: `Killing(x_a, x_c) = 36 · Gz a c` (the cert form), from the per-pair checks.
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.LatGen VOA.IntegralLattice VOA.CartanLattices VOA.AffineGeneral
  VOA.AffineGeneral.LatticeLie VOA.AffineGeneral.CartanSimple

noncomputable section

theorem ci7_eq (i : Fin 7) : ci7 i = cI i := rfl

/-- The cert brackets as sparse sums. -/
theorem bracket (a b : Fin 133) : ⁅xs a, xs b⁆ = spL (sL a b) :=
  bracket_of_pairOK a b (pairOK_all a b)

/-- The Killing form of `e7Lie`. -/
abbrev K : LinearMap.BilinForm ℂ e7Lie := killingForm ℂ e7Lie

theorem K_inv (x y z : e7Lie) : K ⁅x, y⁆ z = K x ⁅y, z⁆ :=
  LieModule.traceForm_apply_lie_apply ℂ e7Lie e7Lie x y z

theorem K_spL (x : e7Lie) (l : List (Fin 133 × ℤ)) :
    K x (spL l) = (l.map fun t => (t.2 : ℂ) * K x (xs t.1)).sum := by
  induction l with
  | nil => simp [spL]
  | cons t l ih =>
      simp only [spL, List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul] at ih ⊢
      rw [ih]

theorem formZ_add_right (v w₁ w₂ : Lat) : formZ v (w₁ + w₂) = formZ v w₁ + formZ v w₂ := by
  simp only [formZ, Pi.add_apply]; ring

/-- Eigenvectors of `ad H_i` with eigenvalues summing to a nonzero number are `K`-orthogonal. -/
theorem K_weight (i : Fin 7) (x y : e7Lie) (lx ly : ℂ) (hx : ⁅xs (cI i), x⁆ = lx • x)
    (hy : ⁅xs (cI i), y⁆ = ly • y) : (lx + ly) * K x y = 0 := by
  have h1 := LieModule.traceForm_apply_lie_apply' ℂ e7Lie e7Lie (xs (cI i)) x y
  rw [hx, hy] at h1
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  linear_combination h1

theorem simpleData (i : Fin 7) :
    sL (eI i) (fI i) = [(cI i, 1)] ∧ wt (eI i) = hvec (cI i) ∧ 7 ≤ (eI i).val ∧ 7 ≤ (fI i).val := by
  have h := simple_ok i
  simp only [simpleOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem bracket_EF (i : Fin 7) : ⁅xs (eI i), xs (fI i)⁆ = xs (cI i) := by
  rw [bracket, (simpleData i).1]
  simp [spL]

theorem Am_eq (i j : Fin 7) : Am i j = formZ (hvec (cI i)) (hvec (cI j)) := rfl

theorem Am_diag : ∀ i, Am i i = 2 := by decide

theorem K_diag (i : Fin 7) : K (xs (cI i)) (xs (cI i)) = 72 := by
  have h := Normalization.e7_killing
    (simpleRoot (CartanMatrix.E₇) CartanMatrix.E₇_isSymm e7_posDef (by decide) i)
  rw [xs_cI]
  exact h

theorem K_EF (i : Fin 7) : K (xs (eI i)) (xs (fI i)) = 36 := by
  have h : K (xs (cI i)) ⁅xs (eI i), xs (fI i)⁆ = 72 := by rw [bracket_EF]; exact K_diag i
  rw [← K_inv, cartan_xs, (simpleData i).2.1, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← Am_eq, Am_diag] at h
  push_cast at h
  linear_combination h / 2

theorem K_cartan (j i : Fin 7) : K (xs (cI j)) (xs (cI i)) = 36 * Am j i := by
  rw [← bracket_EF i, ← K_inv, cartan_xs, (simpleData i).2.1, map_smul, LinearMap.smul_apply,
    smul_eq_mul, K_EF, ← Am_eq]
  ring

theorem xs_mod (c : Fin 133) (hc : c.val < 7) :
    xs c = xs (cI ⟨c.val % 7, Nat.mod_lt _ (by decide)⟩) := by
  congr 1
  ext
  simp [cI, Nat.mod_eq_of_lt hc]

/-- **The Killing form on the cert basis is `36 ×` the cert form.** -/
theorem killing_xs (a c : Fin 133) : K (xs a) (xs c) = 36 * (Gz a c : ℂ) := by
  have h := formPair_all a c
  unfold formPairOK at h
  split_ifs at h with hw
  · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨ha, hc⟩, hG⟩ | ⟨ha, rfl⟩
    · rw [xs_mod a ha, xs_mod c hc, K_cartan, hG]
    · have hr := root_ok a ha
      simp only [rootOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hr
      obtain ⟨⟨⟨⟨_, _⟩, hcart⟩, hne⟩, hval⟩ := hr
      set p := pickI a
      rw [show ci7 p = cI p from rfl] at hval hne
      have h1 : (formZ (hvec (cI p)) (wt a) : ℂ) * K (xs a) (xs (opp a)) =
          K (xs (cI p)) ⁅xs a, xs (opp a)⁆ := by
        rw [← K_inv, cartan_xs, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [bracket, K_spL] at h1
      have h2 : ((sL a (opp a)).map fun t => (t.2 : ℂ) * K (xs (cI p)) (xs t.1)).sum =
          36 * (((sL a (opp a)).map fun t =>
            t.2 * Am p ⟨t.1.val % 7, Nat.mod_lt _ (by decide)⟩).sum : ℤ) := by
        rw [Int.cast_list_sum, List.map_map, ← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro t ht
        have := hcart t ht
        simp only [Function.comp_apply]
        rw [xs_mod t.1 this, K_cartan]
        push_cast
        ring
      rw [h2, ← hval] at h1
      have hne' : (formZ (hvec (cI p)) (wt a) : ℂ) ≠ 0 := by exact_mod_cast hne
      apply mul_left_cancel₀ hne'
      rw [h1]
      push_cast
      ring
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hG, hne⟩ := h
    set i := pickV (wt a + wt c)
    have h0 := K_weight i (xs a) (xs c) _ _ (cartan_xs i a) (cartan_xs i c)
    rw [← Int.cast_add, ← formZ_add_right] at h0
    have hne' : ((formZ (hvec (cI i)) (wt a + wt c) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hne
    rw [hG, Int.cast_zero, mul_zero]
    exact (mul_eq_zero.mp h0).resolve_left hne'

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E7Lie.killing_xs
end AxiomAudit
