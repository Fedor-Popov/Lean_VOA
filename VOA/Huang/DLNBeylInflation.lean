import VOA.Huang.DLNBeylSurjective
import VOA.Huang.DLNCentralReduction

/-!
# DLN lifting from Beyl's inflation-vanishing theorem

`InflationTrivial r` is the group-theoretic content of "the map `r_* : H₂(B, ℤ) → H₂(A, ℤ)`
on Schur multipliers is zero", phrased without homology: for every central extension
`π : E ↠ A` and every pair of homomorphisms `α : F → E`, `β : F → B` over `r`, a commutator
of `F` killed by `β` is killed by `α`.

Why this is implied by `r_* = 0`: `(α, β)` maps `F` into the pullback `P = E ×_A B`, a
central extension of `B` by `Z = ker π`; by the five-term sequence `Z ∩ [P, P]` is the image of
`H₂(B) → H₂(A) → Z`, which is zero.

`BeylInflationSL2` is the second statement of Dong–Lin–Ng, arXiv:1201.6644, Theorem 2.1
(Beyl, Math. Z. 191 (1986), Thm. 3.9 and Cor. 3.10): the inflation along
`SL₂(ℤ/2m) → SL₂(ℤ/m)` is trivial. Here it is an explicit, unproved proposition.

Proved here: `BeylInflationSL2 → RelativeCommutatorCongruence` (the exact level `12 N`),
hence `MatrixDLNLifting`, following DLN Lemma 2.2 / Theorem 2.3.
-/

namespace VOA.Huang.DLNBeyl

open VOA.Huang.DLN VOA.Huang.DLNLifting CongruenceSubgroup
open scoped commutatorElement

/-- The homology-free form of "the map on Schur multipliers induced by `r` vanishes". -/
def InflationTrivial {A B : Type*} [Group A] [Group B] (r : B →* A) : Prop :=
  ∀ (E : Type) [Group E] (π : E →* A), Function.Surjective π → π.ker ≤ Subgroup.center E →
    ∀ (F : Type) [Group F] (α : F →* E) (β : F →* B), π.comp α = r.comp β →
      ∀ x ∈ commutator F, β x = 1 → α x = 1

/-- Trivial Schur multiplier, in the same homology-free form. -/
def SchurTrivial (Q : Type*) [Group Q] : Prop := InflationTrivial (MonoidHom.id Q)

/-- Reduction `SL₂(ℤ/L) → SL₂(ℤ/N)` for `N ∣ L`. -/
def reductionMod (L N : ℕ) (h : N ∣ L) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod L) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom h (ZMod N))

theorem reductionMod_comp_reduction (L N : ℕ) (h : N ∣ L) :
    (reductionMod L N h).comp (reduction L) = reduction N := by
  ext γ i j
  simp [reductionMod, reduction]

/-- **Beyl / DLN Theorem 2.1 (second statement), homology-free form.** Unproved here.
TRUE: Beyl, Math. Z. 191 (1986), Thm. 3.9 and Cor. 3.10, as assembled in DLN Thm. 2.1. -/
def BeylInflationSL2 : Prop :=
  ∀ N : ℕ, 0 < N → InflationTrivial (reductionMod (2 * N) N (dvd_mul_left N 2))

/-- The canonical map of the universal relative central quotient onto `SL₂(ℤ/N)`. -/
def centralToSL (N : ℕ) : CentralQuotient N →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
  QuotientGroup.lift (relativeCommutator N) (reduction N) (relativeCommutator_le_gamma N)

theorem centralToSL_surjective (N : ℕ) [NeZero N] : Function.Surjective (centralToSL N) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (reduction_surjective N) _

theorem centralToSL_ker (N : ℕ) :
    (centralToSL N).ker = (Gamma N).map (QuotientGroup.mk' (relativeCommutator N)) := by
  rw [centralToSL, QuotientGroup.ker_lift]
  rfl

theorem centralToSL_ker_le_center (N : ℕ) :
    (centralToSL N).ker ≤ Subgroup.center (CentralQuotient N) := by
  rw [centralToSL_ker]; exact gamma_image_le_center N

/-- **Inflation vanishing gives the relative-commutator containment on the derived part.** -/
theorem gamma_inf_commutator_le_of_inflation {L N : ℕ} (hN : 0 < N) (h : N ∣ L)
    (hinf : InflationTrivial (reductionMod L N h)) :
    Gamma L ⊓ commutator SL2Z ≤ relativeCommutator N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  intro x hx
  have hα := hinf (CentralQuotient N) (centralToSL N) (centralToSL_surjective N)
    (centralToSL_ker_le_center N) SL2Z (QuotientGroup.mk' (relativeCommutator N)) (reduction L)
    (by rw [reductionMod_comp_reduction]; rfl) x hx.2 hx.1
  simpa using hα

/-- **Beyl inflation implies the exact relative-commutator congruence**
`Γ(12N) ≤ [SL₂(ℤ), Γ(N)]`. -/
theorem relativeCommutatorCongruence_of_beyl (hB : BeylInflationSL2) :
    RelativeCommutatorCongruence := by
  intro N hN γ hγ
  refine gamma_inf_commutator_le_of_inflation hN (dvd_mul_left N 2) (hB N hN) ⟨?_, ?_⟩
  · exact gamma_le_of_dvd (by
      rw [show 12 * N = 6 * (2 * N) by ring]; exact dvd_mul_left _ _) hγ
  · exact gamma_twelve_le_commutator (gamma_le_of_dvd (dvd_mul_right 12 N) hγ)

/-- **DLN Theorem 2.3 (matrix form) from Beyl's inflation theorem.** -/
theorem matrixDLNLifting_of_beyl (hB : BeylInflationSL2) : DLNBridge.MatrixDLNLifting :=
  matrixDLNLifting_of_relativeCommutator (relativeCommutatorCongruence_of_beyl hB)

theorem centralCongruenceSL2_of_beyl (hB : BeylInflationSL2) : CentralCongruenceSL2 :=
  relativeCommutatorCongruenceSome_iff_centralCongruenceSL2.mp
    (relativeCommutatorCongruenceSome_of_exact (relativeCommutatorCongruence_of_beyl hB))

theorem finiteCentralDerivedCongruenceSL2_of_beyl (hB : BeylInflationSL2) :
    FiniteCentralDerivedCongruenceSL2 :=
  relativeCommutatorCongruenceSome_iff_finiteCentralDerived.mp
    (relativeCommutatorCongruenceSome_of_exact (relativeCommutatorCongruence_of_beyl hB))

theorem zhuCongruence_of_beyl (hB : BeylInflationSL2)
    (hP : DLNBridge.ZhuProjectiveCongruenceInput.{u}) : DLNBridge.ZhuCongruenceInput.{u} :=
  zhuCongruence_of_relativeCommutatorSome
    (relativeCommutatorCongruenceSome_of_exact (relativeCommutatorCongruence_of_beyl hB)) hP

/-- Sanity: a trivial target has trivial inflation (every extension of the trivial group is
abelian). -/
theorem inflationTrivial_of_subsingleton {A B : Type*} [Group A] [Group B] [Subsingleton A]
    (r : B →* A) : InflationTrivial r := by
  intro E _ π _ hc F _ α β _ x hx _
  have hcomm : commutator E = ⊥ := by
    rw [eq_bot_iff, commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    have ha : a ∈ Subgroup.center E := hc (Subsingleton.elim (π a) 1)
    have hab : b * a = a * b := Subgroup.mem_center_iff.mp ha b
    change ⁅a, b⁆ ∈ (⊥ : Subgroup E)
    rw [Subgroup.mem_bot, commutatorElement_def, ← hab]; group
  have : α x ∈ commutator E := by
    have h2 : (commutator F).map α ≤ commutator E := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 ⟨x, hx, rfl⟩
  rw [hcomm] at this
  exact this

end VOA.Huang.DLNBeyl
