import VOA.DeligneAudit.LeviTypeA3Table
import VOA.DeligneAudit.DeligneFusionSl2Module

/-! Mode-word length cutoff at each simple root of the A3 current algebra. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem boxP_degree_le (m : ℕ) (f : ℕ →₀ ℕ)
    (hf : BoxP m f) : Finsupp.degree f ≤ m := by
  by_cases hzero : f = 0
  · subst f
    simp
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hzero
    have h := hf i hi
    omega

private theorem box_weight_first (f : ℕ →₀ ℕ) :
    (Finsupp.weight om f).1 = Finsupp.degree f := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

private noncomputable def zWord (l : List ℕ) : R := (l.map z).prod

private theorem zWord_hom : ∀ l : List ℕ,
    MvPolynomial.IsWeightedHomogeneous om (zWord l) (l.length, l.sum) := by
  intro l
  induction l with
  | nil =>
      simpa [zWord] using MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s l ih =>
      have hz : MvPolynomial.IsWeightedHomogeneous om (z s) (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      have hm := hz.mul ih
      simpa [zWord, Nat.add_comm] using hm

private theorem evAlg_zWord (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (l : List ℕ) :
    Sl2Weyl.evAlg F hFF (zWord l) = (l.map F).prod := by
  induction l with
  | nil => simp [zWord]
  | cons s l ih =>
      simp only [zWord, List.map_cons, List.prod_cons] at *
      rw [map_mul, Sl2Weyl.evAlg_z, ih]

theorem a3_box_word_length_zero (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (y : V) (m : ℕ)
    (hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) y = 0)
    (l : List ℕ) (hl : m < l.length) : (l.map F).prod y = 0 := by
  have hspan := span_box_graded F hFF y m hk (zWord_hom l)
  have hle : Submodule.span ℂ {v : V | ∃ f, BoxP m f ∧
      Finsupp.weight om f = (l.length, l.sum) ∧
      v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v ⟨f, hf, hw, hv⟩
    have hd := boxP_degree_le m f hf
    have he := box_weight_first f
    have : l.length = Finsupp.degree f := by rw [hw] at he; exact he
    have : v = 0 := by omega
    rw [this]
    exact Submodule.zero_mem _
  have hz := (Submodule.mem_bot ℂ).mp (hle hspan)
  simpa only [evAlg_zWord] using hz

variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem op_comm_end (x y : Fin 15) (r s : ℕ) :
    ρ.op x r * ρ.op y s - ρ.op y s * ρ.op x r =
      ∑ e, bracketTable x y e • ρ.op e (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact ρ.comm x y r s v

/-- More than the highest-weight coefficient's number of modes at a simple
root kills the local Weyl generator. -/
theorem a3_simple_word_length_zero (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (i : Fin 3) (l : List ℕ)
    (hl : (weightABC a b c) i < l.length) :
    (l.map fun s => ρ.op (simpleF i) s).prod w = 0 := by
  let F : ℕ → Module.End ℂ V := fun s => ρ.op (simpleF i) s
  let H : ℕ → Module.End ℂ V := fun s => ρ.op (simpleH i) s
  let E : Module.End ℂ V := ρ.op (simpleE i) 1
  have hFF : ∀ r s, F r * F s = F s * F r := by
    intro r s
    apply sub_eq_zero.mp
    rw [op_comm_end]
    simp [F, simple_ff_table]
  have hEF : ∀ k, E * F k - F k * E = H (k + 1) := by
    intro k
    rw [op_comm_end]
    simp [E, F, H, simple_ef_table, Nat.add_comm]
  have hHF : ∀ m k,
      H (m + 1) * F k - F k * H (m + 1) =
        (-2 : ℂ) • F (m + 1 + k) := by
    intro m k
    rw [op_comm_end]
    simp [F, H, simple_hf_table]
  have hE : E w = 0 := h.raising (simpleE i) (simpleE_raising i) 1
  have hH : ∀ m, H (m + 1) w = 0 := by
    intro m
    exact h.cartan_pos i (m + 1) (by omega)
  have hN : (F 0 ^ ((weightABC a b c) i + 1)) w = 0 := by
    simpa [F, Module.End.pow_apply] using h.lowering i
  have hk : ∀ r s, 1 ≤ r → (weightABC a b c) i + 1 ≤ r + s →
      (PowerSeries.coeff s (VOA.DeligneAudit.Garland.Fs F ^ r)) w = 0 := by
    intro r s hr hrs
    exact VOA.DeligneAudit.Garland.garland hEF hHF hFF hE hH
      r hr hN s hrs
  exact a3_box_word_length_zero F hFF w ((weightABC a b c) i) hk l hl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_simple_word_length_zero
#print axioms VOA.DeligneAudit.A3Sector.a3_box_word_length_zero
