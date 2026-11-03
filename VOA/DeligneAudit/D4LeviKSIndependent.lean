import VOA.DeligneAudit.D4LeviKSMixedShift
import VOA.DeligneAudit.D4LeviKSLemma0Deriv

/-! Polynomial Cartan shifts of mixed relations and the first PAIR identity. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

/-- The three lists prescribe independent power-sum shifts of X, Y, and Z. -/
def independentShiftModes (xs ys zs : List ℕ) : List (Fin 3 × ℕ) :=
  xs.map (fun r => (0, r)) ++ ys.map (fun r => (1, r)) ++
    zs.map (fun r => (2, r))

/-- The span of every Cartan power-sum polynomial applied to a vector. -/
def cartanShiftSpan (v : V) : Submodule ℂ V :=
  Submodule.span ℂ {u | ∃ ps : List (Fin 3 × ℕ),
    u = selectiveCartanWord ρ ps v}

theorem cartanShiftSpan_le_higher (k : RadicalKey) {v : V}
    (hv : v ∈ higherOrbit ρ w m k) :
    cartanShiftSpan ρ v ≤ higherOrbit ρ w m k := by
  rw [cartanShiftSpan, Submodule.span_le]
  rintro u ⟨ps, rfl⟩
  exact selectiveCartanWord_higher ρ w m ps k hv

/-- Every finite polynomial in the three selective Cartan currents preserves
    the XZG relation at its fixed key. -/
theorem xz_independent_power_shift_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s i : ℕ) (xs' ys' zs' : List ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey (List.replicate rs.length 0) ys [] c
        (rs.sum + ys.sum + s)) :
    selectiveCartanWord ρ (independentShiftModes xs' ys' zs')
      (mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
        (rs.map (transportCurrent (xOp ρ))).prod w) ∈
      keyPrefix ρ w m i :=
  xz_cartan_shifted_prefix ρ w m h rs ys c s i
    (independentShiftModes xs' ys' zs') hK hks hi hkey

/-- All finite linear combinations of Cartan power-sum shifts of XZG lie in
    the same graded prefix. -/
theorem xz_cartanShiftSpan_le_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs ys : List ℕ) (c s i : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey (List.replicate rs.length 0) ys [] c
        (rs.sum + ys.sum + s)) :
    cartanShiftSpan ρ
      (mixedTop (yOp ρ) (zOp ρ) c s (ys ++ List.replicate c 0)
        (rs.map (transportCurrent (xOp ρ))).prod w) ≤
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact cartanShiftSpan_le_higher ρ w m _
    (xz_full_contractions_higher ρ w m h rs ys c s hK hks)

/-- The corresponding independently shifted YZG relation. -/
theorem yz_independent_power_shift_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s i : ℕ) (xs' ys' zs' : List ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c
        (rs.sum + xs.sum + s)) :
    selectiveCartanWord ρ (independentShiftModes xs' ys' zs')
      (mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
        (rs.map (transportCurrent (yOp ρ))).prod w) ∈
      keyPrefix ρ w m i :=
  yz_cartan_shifted_prefix ρ w m h rs xs c s i
    (independentShiftModes xs' ys' zs') hK hks hi hkey

theorem yz_cartanShiftSpan_le_prefix
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (rs xs : List ℕ) (c s i : ℕ)
    (hK : 1 ≤ rs.length) (hks : m + 1 ≤ c + rs.length + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ =
      rzKey xs (List.replicate rs.length 0) [] c
        (rs.sum + xs.sum + s)) :
    cartanShiftSpan ρ
      (mixedTop (xOp ρ) (zOp ρ) c s (xs ++ List.replicate c 0)
        (rs.map (transportCurrent (yOp ρ))).prod w) ≤
      keyPrefix ρ w m i := by
  rw [keyPrefix_eq_higher ρ w m h i hi, hkey]
  exact cartanShiftSpan_le_higher ρ w m _
    (yz_full_contractions_higher ρ w m h rs xs c s hK hks)

/-- Leibniz splitting of the f3 derivative at an arbitrary word boundary.
    This is the algebraic one-step antipode identity used for PAIR. -/
theorem fThreeDerivative_append (r : ℕ)
    (l₁ l₂ : List (Fin 6 × ℕ)) (v : V) :
    fThreeDerivative ρ r (l₁ ++ l₂) v =
      fThreeDerivative ρ r l₁
        (wordOp ρ (l₂.map fun p => (radicalColour p.1, p.2)) v) +
      wordOp ρ (l₁.map fun p => (radicalColour p.1, p.2))
        (fThreeDerivative ρ r l₂ v) := by
  induction l₁ with
  | nil => simp [fThreeDerivative, wordOp]
  | cons p l₁ ih =>
      rcases p with ⟨j, t⟩
      simp only [List.cons_append, List.map_cons, fThreeDerivative,
        wordOp, ih, map_add]
      rw [List.map_append, wordOp_append]
      abel

/-- A single f3 mode can be moved across any radical-word boundary, with
    a minus sign, modulo the higher-key orbit. -/
theorem fThree_antipode_one_higher
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) (r : ℕ)
    (l₁ l₂ : List (Fin 6 × ℕ))
    (hl : keyLess m k (wordKey (l₁ ++ l₂))) :
    fThreeDerivative ρ r l₁ (radicalWord ρ w l₂) +
      wordOp ρ (l₁.map fun p => (radicalColour p.1, p.2))
        (fThreeDerivative ρ r l₂ w) ∈ higherOrbit ρ w m k := by
  have hd := fThree_derivative_higher ρ w m h k r (l₁ ++ l₂) hl
  rw [fThreeDerivative_append ρ r l₁ l₂ w] at hd
  exact hd

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.xz_independent_power_shift_prefix
#print axioms VOA.DeligneAudit.D4Levi.yz_independent_power_shift_prefix
#print axioms VOA.DeligneAudit.D4Levi.cartanShiftSpan_le_higher
#print axioms VOA.DeligneAudit.D4Levi.xz_cartanShiftSpan_le_prefix
#print axioms VOA.DeligneAudit.D4Levi.yz_cartanShiftSpan_le_prefix
#print axioms VOA.DeligneAudit.D4Levi.fThreeDerivative_append
#print axioms VOA.DeligneAudit.D4Levi.fThree_antipode_one_higher
