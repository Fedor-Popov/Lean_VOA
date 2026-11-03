import VOA.Classification.COne.PlusUnitaryFinal

/-!
# Lowest weights relevant to the two-step splitting problem

The spectral bound below is proved from the certified Zhu relations, without
assuming rationality or a classification of irreducibles. It applies to ordinary
modules with a nonzero lowest-weight space. It does NOT assert that an arbitrary
simple weak subquotient is ordinary, or that extensions are ordinary.

Abe, https://arxiv.org/html/math/0311210, Table 2 and Propositions 7.2--7.4:
equal weights and nonintegral differences are one case; nonzero integral
differences require the vacuum/sign argument or the Heisenberg fixed-point
extension and fusion arguments. The half-lattice weight is exactly `m / 4`.
-/

namespace VOA.Classification.COne.PlusSplitting

open PlusUnitary

/-- The finite list of possible numerical lowest weights. Multiplicities and
isomorphism classes of modules are deliberately not encoded by this predicate. -/
def LowestWeightValue (m : ℕ) (h : ℂ) : Prop :=
  h = 1 ∨ h = 1 / 16 ∨ h = 9 / 16 ∨ h = (m : ℂ) / 4 ∨
    ∃ j : ℕ, j < m ∧ h = (j : ℂ) ^ 2 / (4 * m)

/-- The existing Zhu certificates bound every nonzero ordinary lowest-weight
space, without any irreducibility or semisimplicity hypothesis. -/
theorem lowestWeightValue_of_ordinary
    (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) (h : ℂ)
    (hlow : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    LowestWeightValue m h := by
  obtain ⟨w, x, hx, hx0, hW⟩ := exists_eigen_lowest m hm N hne (WP m hm)
  rcases plusM1Dichotomy_holds m hm M N h w x hlow hx hx0 hW with
    hcurve | h16 | h916 | hone
  · by_cases hE : oMod N (EP m hm) x = 0
    · obtain ⟨j, hjm, hj⟩ := plusEESquare_holds m hm M N h x hlow hx hx0
        (by rw [hW, hcurve]) hE
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hjm, ?_⟩)))
      have hm0 : (4 * (m : ℂ)) ≠ 0 :=
        mul_ne_zero (by norm_num) (by exact_mod_cast (show m ≠ 0 by omega))
      rw [eq_div_iff hm0]
      linear_combination hj
    · have hrel := plusERelation_holds m hm hm2 M N h x hlow hx
      have hc : (h - (m : ℂ) / 4) * (h - 1 / 16) * (h - 9 / 16) = 0 :=
        (smul_eq_zero.mp hrel).resolve_right hE
      rcases mul_eq_zero.mp hc with hc | hc
      · rcases mul_eq_zero.mp hc with hc | hc
        · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hc))))
        · exact Or.inr (Or.inl (sub_eq_zero.mp hc))
      · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hc)))
  · exact Or.inr (Or.inl h16)
  · exact Or.inr (Or.inr (Or.inl h916))
  · exact Or.inl hone

/-- In particular, this bound applies to all irreducible ordinary modules. -/
theorem exists_lowestWeightValue_of_irreducible
    (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule (V2mPlus m hm) M) (hirr : N.IsIrreducible) :
    ∃ h : ℂ, IsLowestWeight N h ∧ N.weight h ≠ ⊥ ∧ LowestWeightValue m h := by
  obtain ⟨h, hlow, hne⟩ := OrdVModule.exists_isLowestWeight_of_irreducible N hirr
  exact ⟨h, hlow, hne, lowestWeightValue_of_ordinary m hm hm2 N h hlow hne⟩

/-- The exceptional weights not coming from a nonzero lattice coset. -/
def ExceptionalWeight (h : ℂ) : Prop :=
  h = 0 ∨ h = 1 ∨ h = 1 / 16 ∨ h = 9 / 16

/-- Numerical lattice weights, including the half-lattice endpoint. -/
def LatticeWeight (m : ℕ) (h : ℂ) : Prop :=
  h = (m : ℂ) / 4 ∨ ∃ j : ℕ, 0 < j ∧ j < m ∧ h = (j : ℂ) ^ 2 / (4 * m)

theorem exceptional_or_latticeWeight {m : ℕ} {h : ℂ}
    (hh : LowestWeightValue m h) : ExceptionalWeight h ∨ LatticeWeight m h := by
  rcases hh with h | h | h | h | ⟨j, hj, h⟩
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inl h)
  · rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact Or.inl (Or.inl (by simpa using h))
    · exact Or.inr (Or.inr ⟨j, hpos, hj, h⟩)

/-- Among exceptional weights, only `0` and `1` differ by a nonzero integer. -/
theorem exceptional_nonzero_integral_difference
    {h k : ℂ} (hh : ExceptionalWeight h) (hk : ExceptionalWeight k)
    {z : ℤ} (hz : z ≠ 0) (he : h - k = (z : ℂ)) :
    (h = 0 ∧ k = 1) ∨ (h = 1 ∧ k = 0) := by
  have hr := congrArg Complex.re he
  have hb : (-1 : ℝ) ≤ z ∧ (z : ℝ) ≤ 1 := by
    rcases hh with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;>
      norm_num at hr ⊢ <;> constructor <;> linarith
  have hzi : -1 ≤ z ∧ z ≤ 1 := by exact_mod_cast hb
  obtain ⟨hzlo, hzhi⟩ := hzi
  interval_cases z <;>
    rcases hh with rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl
  all_goals norm_num at *

/-- A numerical case split, not an Ext-vanishing assertion: all remaining
nonzero integral differences involve a lattice weight or the pair `0,1`. -/
theorem nonzero_integral_difference_cases
    {m : ℕ} {h k : ℂ} (hh : LowestWeightValue m h) (hk : LowestWeightValue m k)
    {z : ℤ} (hz : z ≠ 0) (he : h - k = (z : ℂ)) :
    LatticeWeight m h ∨ LatticeWeight m k ∨
      (h = 0 ∧ k = 1) ∨ (h = 1 ∧ k = 0) := by
  rcases exceptional_or_latticeWeight hh with hh | hh
  · rcases exceptional_or_latticeWeight hk with hk | hk
    · exact Or.inr (Or.inr (exceptional_nonzero_integral_difference hh hk hz he))
    · exact Or.inr (Or.inl hk)
  · exact Or.inl hh

/-- The half-lattice weight never lies in either twisted-weight integer coset. -/
theorem half_lattice_twisted_nonintegral (m : ℕ) (z : ℤ) :
    (m : ℂ) / 4 - 1 / 16 ≠ (z : ℂ) ∧
      (m : ℂ) / 4 - 9 / 16 ≠ (z : ℂ) := by
  constructor
  · intro he
    have he' : 4 * (m : ℂ) - 1 = 16 * (z : ℂ) := by linear_combination 16 * he
    have hi : 4 * (m : ℤ) - 1 = 16 * z := by exact_mod_cast he'
    omega
  · intro he
    have he' : 4 * (m : ℂ) - 9 = 16 * (z : ℂ) := by linear_combination 16 * he
    have hi : 4 * (m : ℤ) - 9 = 16 * z := by exact_mod_cast he'
    omega

/-- Charged weights can nevertheless coincide numerically with twisted weights;
weight equality must not be confused with a module isomorphism. -/
theorem lattice_twisted_weight_collision :
    LatticeWeight 16 (1 / 16) ∧ LatticeWeight 16 (9 / 16) := by
  constructor
  · exact Or.inr ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact Or.inr ⟨6, by norm_num, by norm_num, by norm_num⟩

/-- A nonzero integral difference already occurs in the numerical list for
`m = 8`, between the vacuum and half-lattice weights. -/
theorem nonzero_integral_weight_example :
    LowestWeightValue 8 0 ∧ LowestWeightValue 8 2 ∧
      (2 : ℂ) - (0 : ℂ) = ((2 : ℤ) : ℂ) := by
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨0, by norm_num, by norm_num⟩))),
    Or.inr (Or.inr (Or.inr (Or.inl (by norm_num)))), by norm_num⟩

end VOA.Classification.COne.PlusSplitting
