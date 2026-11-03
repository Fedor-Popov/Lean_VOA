import VOA.DeligneAudit.D4FusionToroidalGarlandSymbol

/-!
# Graded transfer of the Garland symbols `P^{(j)}_N` (★b, all `j`)

For a toroidal action `A` on `V` with cyclic vector `w` and a high-mode shift (`HighTShift`),
the cyclic associated graded `Gr A w = numerator / kernel` embeds into the larger quotient
`Q = (ℕ →₀ V) ⧸ denominator` (`ι`, injective).  On `Q` every lifted operator descends
(`Lop`), with `Lop c i s (Λ d y) = Λ (d + s) (A.op c i s y)` for the tagging maps
`Λ d = mkQ ∘ single d`, and `ι ∘ grOp c i s = Lop c i s ∘ ι` for **all** modes `s` (both
sides vanish for `s ≥ m`, by the high-mode shift).  Consequently

`ι (P^{(j)}_N g₀) = Λ N (P^{(j)}_N w)` with the ungraded
`P^{(j)}_N w = ∑_{a+b=N} f_a [z^b] g(z)^j w`,

so the symbol `P^{(j)}_N g₀` vanishes as soon as the ungraded vector `P^{(j)}_N w` lies in the
`t`-degree `< N` filtration piece (`Psym_zero_of_mem`).  This reduces (★b) for every `j` to an
ungraded filtration statement in the tensor model.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr.StarB2

open VOA.DeligneAudit.Toroidal
open Finset

noncomputable section

section Transfer

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (A : ToroidalAction f V) (w : V) (m : ℕ)

/-- The quotient of all tagged vectors by the denominator. -/
abbrev Q := (ℕ →₀ V) ⧸ denominator A w

/-- Tagging a vector in degree `d`. -/
def Λ (d : ℕ) : V →ₗ[ℂ] Q A w :=
  (denominator A w).mkQ ∘ₗ Finsupp.lsingle d

theorem Λ_apply (d : ℕ) (y : V) :
    Λ A w d y = (denominator A w).mkQ (Finsupp.single d y) := rfl

/-- The lifted operator on the big quotient. -/
def Lop (c : Fin n) (i s : ℕ) : Q A w →ₗ[ℂ] Q A w :=
  (denominator A w).mapQ (denominator A w) (liftedOp A c i s) (denominator_inv A w c i s)

theorem Lop_Λ (c : Fin n) (i s d : ℕ) (y : V) :
    Lop A w c i s (Λ A w d y) = Λ A w (d + s) (A.op c i s y) := by
  rw [Λ_apply, Λ_apply, Lop, Submodule.mkQ_apply, Submodule.mapQ_apply, liftedOp_single]
  rfl

theorem kernel_le_ker :
    kernel A w ≤ LinearMap.ker ((denominator A w).mkQ ∘ₗ (numerator A w).subtype) := by
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact hv

/-- The comparison map `Gr A w → Q A w`. -/
def ι : Gr A w →ₗ[ℂ] Q A w :=
  (kernel A w).liftQ ((denominator A w).mkQ ∘ₗ (numerator A w).subtype) (kernel_le_ker A w)

theorem ι_mkQ (v : numerator A w) :
    ι A w ((kernel A w).mkQ v) = (denominator A w).mkQ v.1 := by
  rw [ι, Submodule.mkQ_apply, Submodule.liftQ_apply]
  rfl

theorem ι_injective : Function.Injective (ι A w) := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hv
  exact hv

/-- `ι` intertwines the truncated graded operators with the lifted operators, for all modes. -/
theorem ι_grOp (h : HighTShift A w m) (c : Fin n) (i s : ℕ) (ξ : Gr A w) :
    ι A w (grOp A w m c i s ξ) = Lop A w c i s (ι A w ξ) := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (kernel A w) ξ
  by_cases hs : s < m
  · rw [grOp_mk A w m c i s hs, ι_mkQ, ι_mkQ, Lop]
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
    rfl
  · rw [grOp_high_zero A w m c i s (Nat.le_of_not_lt hs), LinearMap.zero_apply, map_zero,
      ι_mkQ, Lop]
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
    symm
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact high_mem_denominator A w m h c i s (Nat.le_of_not_lt hs) v.2

theorem ι_grGenerator : ι A w (grGenerator A w) = Λ A w 0 w := by
  rw [grGenerator, ι_mkQ]
  rfl

/-- `[z^s] g(z)^j y` in the ungraded action. -/
def gpowA (c₀ : Fin n) : ℕ → ℕ → V → V
  | 0, s, y => if s = 0 then y else 0
  | j + 1, s, y => ∑ p ∈ antidiagonal s, A.op c₀ 1 p.1 (gpowA c₀ j p.2 y)

/-- The ungraded `P^{(j)}_N y = ∑_{a+b=N} f_a [z^b] g(z)^j y`. -/
def PsymA (c₀ : Fin n) (j N : ℕ) (y : V) : V :=
  ∑ p ∈ antidiagonal N, A.op c₀ 0 p.1 (gpowA A c₀ j p.2 y)

theorem ι_gpow (h : HighTShift A w m) (c₀ : Fin n) (j : ℕ) :
    ∀ (s d : ℕ) (ξ : Gr A w) (y : V), ι A w ξ = Λ A w d y →
      ι A w (gpow (grToroidal A w m h) c₀ j s ξ) = Λ A w (d + s) (gpowA A c₀ j s y) := by
  induction j with
  | zero =>
    intro s d ξ y hξ
    simp only [gpow, gpowA]
    split_ifs with hs
    · subst hs
      simpa using hξ
    · simp
  | succ j ih =>
    intro s d ξ y hξ
    simp only [gpow, gpowA, map_sum]
    refine sum_congr rfl fun p hp => ?_
    have hp' := mem_antidiagonal.mp hp
    change ι A w (grOp A w m c₀ 1 p.1 (gpow (grToroidal A w m h) c₀ j p.2 ξ)) = _
    rw [ι_grOp A w m h, ih p.2 d ξ y hξ, Lop_Λ, show d + p.2 + p.1 = d + s by omega]

theorem ι_Psym (h : HighTShift A w m) (c₀ : Fin n) (j N : ℕ) :
    ι A w (Psym (grToroidal A w m h) c₀ j N (grGenerator A w)) =
      Λ A w N (PsymA A c₀ j N w) := by
  simp only [Psym, PsymA, map_sum]
  refine sum_congr rfl fun p hp => ?_
  have hp' := mem_antidiagonal.mp hp
  change ι A w (grOp A w m c₀ 0 p.1 (gpow (grToroidal A w m h) c₀ j p.2 (grGenerator A w))) = _
  rw [ι_grOp A w m h, ι_gpow A w m h c₀ j p.2 0 _ w (ι_grGenerator A w), Lop_Λ,
    show 0 + p.2 + p.1 = N by omega]

/-- **Graded transfer**: the symbol `P^{(j)}_N` kills the graded generator as soon as the
ungraded `P^{(j)}_N w` lies in the `t`-degree `< N` filtration piece. -/
theorem Psym_zero_of_mem (h : HighTShift A w m) (c₀ : Fin n) (j N : ℕ)
    (hmem : PsymA A c₀ j N w ∈ evalFbelow A w N) :
    Psym (grToroidal A w m h) c₀ j N (grGenerator A w) = 0 := by
  apply ι_injective A w
  rw [ι_Psym, map_zero, Λ_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span ⟨N, _, hmem, rfl⟩

end Transfer

end

end VOA.DeligneAudit.Toroidal.FusionGr.StarB2

section AxiomAudit
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.StarB2.ι_injective
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.StarB2.ι_grOp
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.StarB2.Psym_zero_of_mem
end AxiomAudit
