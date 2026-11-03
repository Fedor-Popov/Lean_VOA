import VOA.Classification.COne.ExceptionalOrbifoldBasic
import VOA.Modules.PoissonDescent

/-!
# The algebraic end of the icosahedral C₂ argument

Source: S. Xu, arXiv:2608.13872v2, §§6–7 and 10
(https://arxiv.org/html/2608.13872v2).
We prove the determinant elimination and finite spanning argument, and check
the four displayed rational numbers in §10.1 using kernel-checked arithmetic.
The identification of these numbers with VOA coupling coefficients is NOT proved.
`XuIcosahedralPoissonRelations` records exactly that missing input, together
with the two-tower spanning assertion. It is a cited proposition, not an axiom.
-/

namespace VOA.Classification.COne
open VOA VertexOperatorAlgebra Module

section LinearAlgebra
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Invertible scalar systems also eliminate unknown vectors. -/
theorem exceptional_two_relations_vanish {a b c d : ℂ} {v w : M}
    (hdet : a * d - c * b ≠ 0)
    (h₁ : a • v + b • w = 0) (h₂ : c • v + d • w = 0) : v = 0 ∧ w = 0 := by
  have hv : (a * d - c * b) • v = 0 := calc
    _ = d • (a • v + b • w) - b • (c • v + d • w) := by module
    _ = 0 := by rw [h₁, h₂]; simp
  have hw : (a * d - c * b) • w = 0 := calc
    _ = a • (c • v + d • w) - c • (a • v + b • w) := by module
    _ = 0 := by rw [h₁, h₂]; simp
  exact ⟨(smul_eq_zero.mp hv).resolve_left hdet, (smul_eq_zero.mp hw).resolve_left hdet⟩

/-- Two truncated endomorphism towers span a finite-dimensional space of dimension at most `p+q`. -/
theorem exceptional_two_tower_finite (D : Module.End ℂ M) (v x : M) (p q : ℕ)
    (hspan : Submodule.span ℂ (Set.range (Sum.elim (fun n : ℕ => (D ^ n) v)
      (fun n : ℕ => (D ^ n) x))) = ⊤)
    (hv : (D ^ p) v = 0) (hx : (D ^ q) x = 0) :
    FiniteDimensional ℂ M ∧ Module.finrank ℂ M ≤ p + q := by
  classical
  let f : Fin p ⊕ Fin q → M := Sum.elim (fun n => (D ^ n.val) v) (fun n => (D ^ n.val) x)
  have high (y : M) (k : ℕ) (hy : (D ^ k) y = 0) (n : ℕ) (hn : k ≤ n) :
      (D ^ n) y = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm, pow_add, Module.End.mul_apply, hy, map_zero]
  have hf : Submodule.span ℂ (Set.range f) = ⊤ := by
    rw [← top_le_iff, ← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨n | n, rfl⟩
    · by_cases hn : n < p
      · exact Submodule.subset_span ⟨Sum.inl ⟨n, hn⟩, rfl⟩
      · change (D ^ n) v ∈ _
        rw [high v p hv n (by omega)]
        exact Submodule.zero_mem _
    · by_cases hn : n < q
      · exact Submodule.subset_span ⟨Sum.inr ⟨n, hn⟩, rfl⟩
      · change (D ^ n) x ∈ _
        rw [high x q hx n (by omega)]
        exact Submodule.zero_mem _
  exact ⟨⟨hf ▸ Submodule.fg_span (Set.finite_range f)⟩,
    by simpa using (finrank_le_of_span_eq_top hf)⟩

end LinearAlgebra

/-- The numerical values printed in Xu v2 §10.1; their VOA interpretation remains an input. -/
def xuU37 : ℚ :=
  151263443583192657816671715030186994700903477084314677248 /
  2882600776450368744635282416475520501925952726159180517626585800175145677947998046875
def xuU38 : ℚ :=
  416407995333748762833621605276412963013510875028372514816 /
  319415226836912459855546374004819475777410969680246474797166719345807542282061767578125
def xuV19 : ℚ :=
  3681867191643718569047819232838269056 /
  778381304340824441834206161488913991594789560118793865234375
def xuV20 : ℚ :=
  604984096354415173700324126916891008 /
  4539519766915688144777090333803346398980812714612805822046875

/-- Exact arithmetic only: this does not identify any Virasoro coefficient. -/
theorem xu_determinant_pos : 0 < xuU37 * xuV20 - xuU38 * xuV19 := by
  norm_num [xuU37, xuU38, xuV19, xuV20]

theorem xu_determinant_complex_ne_zero :
    (xuU37 : ℂ) * (xuV20 : ℂ) - (xuU38 : ℂ) * (xuV19 : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt xu_determinant_pos

/-- Multiplication by the conformal class on the actual C₂ quotient. -/
noncomputable def exceptionalConformalEnd {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : Module.End ℂ (A₂ W) := A₂mul W (mk₂ W W.conformalVector)

theorem exceptionalConformalEnd_mk {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    exceptionalConformalEnd W (mk₂ W v) = mk₂ W (W.L (-2) v) := by
  rw [exceptionalConformalEnd, A₂mul_mk]
  rfl

/-- The quotient towers used below are exactly the classes of Virasoro descendants. -/
theorem exceptionalConformalEnd_pow_mk {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (v : 𝒱) :
    (exceptionalConformalEnd W ^ n) (mk₂ W v) = mk₂ W (((W.L (-2)) ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, exceptionalConformalEnd_mk,
      pow_succ', Module.End.mul_apply]

/-- Xu v2 Theorem 6.4, Lemma 7.5, Proposition 7.7 and §10.1, expressed on the
actual Poisson quotient. The coefficients include the two nonzero VOA couplings.
This input includes the coefficient/VOA bridge, not just the numerical determinant. -/
def XuIcosahedralPoissonRelations : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), Nonempty (G ≃* alternatingGroup (Fin 5)) →
    ∃ (X : (orbifold G).carrier) (c₀ c₆ : ℂ),
      X ∈ (orbifoldVOA G).grading 36 ∧ c₀ ≠ 0 ∧ c₆ ≠ 0 ∧
      let W := orbifoldVOA G
      let D := exceptionalConformalEnd W
      let v := mk₂ W W.vacuum
      let x := mk₂ W X
      Submodule.span ℂ (Set.range (Sum.elim (fun n : ℕ => (D ^ n) v)
        (fun n : ℕ => (D ^ n) x))) = ⊤ ∧
      (c₀ * (xuU37 : ℂ)) • ((D ^ 37) v) + (c₆ * (xuV19 : ℂ)) • ((D ^ 19) x) = 0 ∧
      (c₀ * (xuU38 : ℂ)) • ((D ^ 38) v) + (c₆ * (xuV20 : ℂ)) • ((D ^ 20) x) = 0

-- Elaborating powers of quotient endomorphisms needs a deeper definitional-equality stack.
set_option maxRecDepth 4096 in
/-- The missing VOA relations imply both C₂-cofiniteness and Xu's dimension bound. -/
theorem exceptionalOrbifold_icosa_c2_of_relations (h : XuIcosahedralPoissonRelations)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    C2Cofinite (orbifoldVOA G) ∧ Module.finrank ℂ (A₂ (orbifoldVOA G)) ≤ 58 := by
  obtain ⟨X, c₀, c₆, _, hc₀, hc₆, hspan, h37, h38⟩ := h G hG
  let D := exceptionalConformalEnd (orbifoldVOA G)
  have h37' := congrArg D h37
  simp only [map_add, map_smul, map_zero] at h37'
  have hpow (n : ℕ) (y : A₂ (orbifoldVOA G)) : D ((D ^ n) y) = (D ^ (n + 1)) y := by
    rw [pow_succ', Module.End.mul_apply]
  change (c₀ * (xuU37 : ℂ)) • D ((D ^ 37) _) +
    (c₆ * (xuV19 : ℂ)) • D ((D ^ 19) _) = 0 at h37'
  rw [hpow, hpow] at h37'
  have hd : (c₀ * (xuU37 : ℂ)) * (c₆ * (xuV20 : ℂ)) -
      (c₀ * (xuU38 : ℂ)) * (c₆ * (xuV19 : ℂ)) ≠ 0 := by
    have he : (c₀ * (xuU37 : ℂ)) * (c₆ * (xuV20 : ℂ)) -
        (c₀ * (xuU38 : ℂ)) * (c₆ * (xuV19 : ℂ)) =
        c₀ * c₆ * ((xuU37 : ℂ) * (xuV20 : ℂ) - (xuU38 : ℂ) * (xuV19 : ℂ)) := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero hc₀ hc₆) xu_determinant_complex_ne_zero
  obtain ⟨hv, hx⟩ := exceptional_two_relations_vanish hd h37' h38
  exact exceptional_two_tower_finite D _ _ 38 20 hspan hv hx

end VOA.Classification.COne
