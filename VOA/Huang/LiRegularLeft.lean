import VOA.Huang.LiRegularShift

/-! # Li's left action `Y^L_{P(z)}` on the regular representation (Li, Lemma 3.20)

For an ordinary module `N` and `z ≠ 0`, Li defines `Y^L_{P(z)}` on `D_{P(z)}(M)` as the
regularized action `Y^R_{P(−z)}` of the translated opposite base `Y°(v, x + z)`
(here `transBase N (−z)`).  We prove:

* `bres_trans_poly` — on polynomial test functions the translated residue is the original
  residue of the translated polynomial;
* `inD_iff_trans` — `D_{P(z)}(M) = D_{P(−z)}(M, Y°(·, · + z))` (Li, Lemma 3.20); the
  roles of the pole bounds at `0` and at `z` are exchanged;
* `regularRepL N hz` — `(D_{P(z)}(M), Y^L)` is a weak `V`-module (Li, Proposition 3.21).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiConverse LaurentPolynomial
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Transport of weak modules along linear equivalences -/

section Transport

variable {E F : Type u} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- A weak module structure transported along a linear equivalence `e : E ≃ F`. -/
noncomputable def WeakModule.transport (A : WeakModule W F) (e : E ≃ₗ[ℂ] F) : WeakModule W E where
  YM :=
    { toFun := fun a => (fun k : ℤ => (e.symm.toLinearMap ∘ₗ A.YM a k ∘ₗ e.toLinearMap :
        Module.End ℂ E) : FormalDist (Module.End ℂ E))
      map_add' := fun a b => by
        funext k
        refine LinearMap.ext fun x => ?_
        change e.symm ((A.YM (a + b)) k (e x))
          = e.symm (A.YM a k (e x)) + e.symm (A.YM b k (e x))
        rw [map_add]
        change e.symm (A.YM a k (e x) + A.YM b k (e x)) = _
        rw [map_add]
      map_smul' := fun c a => by
        funext k
        refine LinearMap.ext fun x => ?_
        change e.symm ((A.YM (c • a)) k (e x)) = c • e.symm (A.YM a k (e x))
        rw [map_smul]
        change e.symm (c • A.YM a k (e x)) = _
        rw [map_smul] }
  vacuum_YM := by
    funext k
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
      A.vacuum_YM]
    change e.symm (((1 : FormalDist (Module.End ℂ F)) k) (e x))
      = ((1 : FormalDist (Module.End ℂ E)) k) x
    have h1 : ∀ (X : Type u) [AddCommGroup X] [Module ℂ X],
        ((1 : FormalDist (Module.End ℂ X)) k) = if k = 0 then 1 else 0 := fun _ _ _ => rfl
    rw [h1, h1]
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  truncation a x := by
    obtain ⟨N, hN⟩ := A.truncation a (e x)
    refine ⟨N, fun n hn => ?_⟩
    change e.symm (mode (A.YM a) n (e x)) = 0
    rw [hN n hn, map_zero]
  jacobi a b x l m n := by
    have hmode : ∀ (c : V) (p : ℤ) (y : E),
        mode ((fun k : ℤ => (e.symm.toLinearMap ∘ₗ A.YM c k ∘ₗ e.toLinearMap :
          Module.End ℂ E)) : FormalDist (Module.End ℂ E)) p y = e.symm (mode (A.YM c) p (e y)) :=
      fun c p y => rfl
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hmode, LinearEquiv.apply_symm_apply]
    have hL := A.jacobi a b (e x) l m n
    have hfinL : (Function.support fun i : ℤ => (negOnePow i * cbz l i) •
        (mode (A.YM a) (l + m - i) (mode (A.YM b) (n + i) (e x))
          - negOnePow l • mode (A.YM b) (l + n - i) (mode (A.YM a) (m + i) (e x)))).Finite := by
      obtain ⟨Na, hNa⟩ := A.truncation a (e x)
      obtain ⟨Nb, hNb⟩ := A.truncation b (e x)
      apply (Set.finite_Icc 0 (max (Na - m) (Nb - n))).subset
      intro i hi
      rw [Function.mem_support] at hi
      refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
      · simp [cbz_apply_neg l h]
      · rw [hNb _ (by omega), hNa _ (by omega), map_zero, map_zero, smul_zero, sub_zero,
          smul_zero]
    have hfinR : (Function.support fun i : ℤ =>
        cbz m i • mode (A.YM (W.smul a (l + i) b)) (m + n - i) (e x)).Finite := by
      obtain ⟨R, hR⟩ := W.regularity a b
      apply (Set.finite_Icc 0 (R - l)).subset
      intro i hi
      rw [Function.mem_support] at hi
      refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
      · simp [cbz_apply_neg m h]
      · rw [show W.smul a (l + i) b = 0 from hR _ (by omega), map_zero]
        exact smul_eq_zero_of_right _ rfl
    have := congrArg e.symm hL
    rw [map_finsum e.symm hfinL, map_finsum e.symm hfinR] at this
    simpa only [LinearEquiv.coe_coe, map_smul, map_sub] using this

theorem WeakModule.transport_mode (A : WeakModule W F) (e : E ≃ₗ[ℂ] F) (a : V) (n : ℤ)
    (x : E) : mode ((WeakModule.transport A e).YM a) n x = e.symm (mode (A.YM a) n (e x)) :=
  rfl

end Transport

/-! ## Translated residues of polynomial test functions -/

section Left

theorem T_mul_toLaurent_nat (N : ℕ) (p : ℂ[X]) :
    (T (N : ℤ) : ℂ[T;T⁻¹]) * Polynomial.toLaurent p
      = Polynomial.toLaurent (Polynomial.X ^ N * p) := by
  rw [map_mul, toLaurent_X_pow']

namespace OppBase

variable (Bs : OppBase W M) (S : Bs.Shift)

theorem tB_nat (c : ℂ) (a : V) (j : ℕ) (y : M) :
    (Bs.tBase S c).B a j y
      = ∑ k ∈ Finset.range (j + 1), (((j.choose k : ℕ) : ℂ) * c ^ k) • Bs.B a (j - k) y := by
  rw [tBase_B]
  refine finsum_eq_sum_of_support_subset _ (fun k hk => ?_) |>.trans
    (Finset.sum_congr rfl fun k hk => ?_)
  · rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [cbz_lt (p := (j : ℤ)) (c := (k : ℤ)) (by positivity) (by omega), zero_mul,
      zero_smul])
  · rw [Finset.mem_range] at hk
    rw [cbz_natCast_eq_choose (by omega)]

/-- On polynomial test functions, the translated residue is the residue of the translated
polynomial: `Res_x p(x) Y°(a, x + c) = Res_y p(y − c) Y°(a, y)` (as series at `∞`). -/
theorem bres_tBase_poly (c : ℂ) (a : V) (p : ℂ[X]) :
    (Bs.tBase S c).bres a (Polynomial.toLaurent p)
      = Bs.bres a (Polynomial.toLaurent (p.comp (Polynomial.X + Polynomial.C c))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, OppBase.bres_add, hp, hq, Polynomial.add_comp, map_add,
      OppBase.bres_add]
  | monomial j d =>
    ext y
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      OppBase.bres_CT, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, add_pow,
      Finset.mul_sum, map_sum, OppBase.bres_sum, LinearMap.smul_apply, tB_nat,
      LinearMap.coeFn_sum, Finset.sum_apply, Finset.smul_sum]
    have hterm : ∀ x ∈ Finset.range (j + 1),
        Bs.bres a (Polynomial.toLaurent (Polynomial.C d * (Polynomial.X ^ x *
          Polynomial.C c ^ (j - x) * ((j.choose x : ℕ) : ℂ[X])))) y
        = (d * c ^ (j - x) * (j.choose x : ℂ)) • Bs.B a x y := by
      intro x _
      rw [show Polynomial.C d * (Polynomial.X ^ x * Polynomial.C c ^ (j - x) *
          ((j.choose x : ℕ) : ℂ[X])) = Polynomial.C (d * c ^ (j - x) * (j.choose x : ℂ)) *
            Polynomial.X ^ x by simp only [map_mul, map_pow, map_natCast]; ring,
        map_mul, Polynomial.toLaurent_C, toLaurent_X_pow', OppBase.bres_CT]
      rfl
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show j + 1 - 1 - k = j - k by omega, Nat.choose_symm (by omega), smul_smul,
      show (j : ℤ) - ((j - k : ℕ) : ℤ) = (k : ℤ) by push_cast [Nat.cast_sub (by omega : k ≤ j)]; ring]
    congr 1
    ring

theorem ys_tBase_poly (c : ℂ) (a : V) (p : ℂ[X]) (α : Module.Dual ℂ M) :
    (Bs.tBase S c).ys a (Polynomial.toLaurent p) α
      = Bs.ys a (Polynomial.toLaurent (p.comp (Polynomial.X + Polynomial.C c))) α := by
  ext w; simp only [OppBase.ys_apply, bres_tBase_poly]

/-- **Li's Lemma 3.20**: `D_{P(z)}(M) = D_{P(−z)}(M, Y°(·, · + z))`. -/
theorem inD_iff_tBase {z : ℂ} (α : Module.Dual ℂ M) :
    Bs.InD z α ↔ (Bs.tBase S (-z)).InD (-z) α := by
  constructor
  · intro h a
    obtain ⟨k, N₀, hW⟩ := h a
    refine ⟨N₀.toNat, k, fun q => ?_⟩
    have hW' : Bs.Wit z a α k (N₀.toNat : ℤ) := hW.mono le_rfl (by omega)
    rw [show (T (k : ℤ) : ℂ[T;T⁻¹]) = T ((k : ℕ) : ℤ) from rfl, T_mul_toLaurent_nat,
      ys_tBase_poly]
    have e : (Polynomial.X ^ k * (lz (-z) ^ N₀.toNat * q)).comp
        (Polynomial.X + Polynomial.C (-z))
        = Polynomial.X ^ N₀.toNat * (lz z ^ k * q.comp (Polynomial.X + Polynomial.C (-z))) := by
      simp only [lz, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
        Polynomial.sub_comp, Polynomial.C_comp, map_neg, Polynomial.neg_comp]
      ring
    rw [e, ← T_mul_toLaurent_nat]
    exact hW' _
  · intro h a
    obtain ⟨k', N', hW⟩ := h a
    refine ⟨N'.toNat, k', fun q => ?_⟩
    have hW' : (Bs.tBase S (-z)).Wit (-z) a α k' (N'.toNat : ℤ) := hW.mono le_rfl (by omega)
    rw [show (T (k' : ℤ) : ℂ[T;T⁻¹]) = T ((k' : ℕ) : ℤ) from rfl, T_mul_toLaurent_nat]
    have e : Polynomial.X ^ k' * (lz z ^ N'.toNat * q)
        = (Polynomial.X ^ N'.toNat * (lz (-z) ^ k' * q.comp (Polynomial.X + Polynomial.C z))).comp
          (Polynomial.X + Polynomial.C (-z)) := by
      simp only [lz, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
        Polynomial.sub_comp, Polynomial.C_comp, map_neg, Polynomial.neg_comp,
        Polynomial.comp_assoc, Polynomial.add_comp]
      simp only [sub_neg_eq_add]
      ring_nf
      simp only [Polynomial.comp_X]
    rw [e, ← ys_tBase_poly, ← T_mul_toLaurent_nat]
    exact hW' _

theorem dsub_eq_tBase (z : ℂ) : Bs.Dsub z = (Bs.tBase S (-z)).Dsub (-z) := by
  ext α; exact inD_iff_tBase Bs S α

/-- The identification of the two descriptions of `D_{P(z)}(M)`. -/
noncomputable def dEquivT (z : ℂ) :
    Bs.Dsub z ≃ₗ[ℂ] (Bs.tBase S (-z)).Dsub (-z) :=
  LinearEquiv.ofEq _ _ (dsub_eq_tBase Bs S z)

/-- **Li's left action**: `(D_{P(z)}(M), Y^L_{P(z)})` is a weak `V`-module
(Li, Proposition 3.21). -/
noncomputable def weakModuleL {z : ℂ} (hz : z ≠ 0) : WeakModule W (Bs.Dsub z) :=
  WeakModule.transport ((Bs.tBase S (-z)).weakModuleR (-z) (neg_ne_zero.2 hz)) (dEquivT Bs S z)

theorem weakModuleL_mode {z : ℂ} (hz : z ≠ 0) (a : V) (n : ℤ) (α : Bs.Dsub z) :
    ((mode ((Bs.weakModuleL S hz).YM a) n α : Bs.Dsub z) : Module.Dual ℂ M)
      = (Bs.tBase S (-z)).yR (-z) (neg_ne_zero.2 hz) a n α := by
  rw [weakModuleL, WeakModule.transport_mode, dEquivT, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, OppBase.weakModuleR_mode, LinearEquiv.coe_ofEq_apply]

end OppBase

variable (N : OrdVModule W M)

theorem transB_nat (c : ℂ) (a : V) (j : ℕ) (y : M) :
    (transBase N c).B a j y
      = ∑ k ∈ Finset.range (j + 1), (((j.choose k : ℕ) : ℂ) * c ^ k) • oppB N a (j - k) y :=
  (oppBase N).tB_nat (oppShift N) c a j y

theorem bres_trans_poly (c : ℂ) (a : V) (p : ℂ[X]) :
    (transBase N c).bres a (Polynomial.toLaurent p)
      = (oppBase N).bres a (Polynomial.toLaurent (p.comp (Polynomial.X + Polynomial.C c))) :=
  (oppBase N).bres_tBase_poly (oppShift N) c a p

theorem ys_trans_poly (c : ℂ) (a : V) (p : ℂ[X]) (α : Module.Dual ℂ M) :
    (transBase N c).ys a (Polynomial.toLaurent p) α
      = (oppBase N).ys a (Polynomial.toLaurent (p.comp (Polynomial.X + Polynomial.C c))) α :=
  (oppBase N).ys_tBase_poly (oppShift N) c a p α

/-- **Li's Lemma 3.20**: `D_{P(z)}(M) = D_{P(−z)}(M, Y°(·, · + z))`. -/
theorem inD_iff_trans {z : ℂ} (α : Module.Dual ℂ M) :
    (oppBase N).InD z α ↔ (transBase N (-z)).InD (-z) α :=
  (oppBase N).inD_iff_tBase (oppShift N) α

theorem dsub_eq (z : ℂ) : (oppBase N).Dsub z = (transBase N (-z)).Dsub (-z) :=
  (oppBase N).dsub_eq_tBase (oppShift N) z

/-- **Li's left action**: `(D_{P(z)}(M), Y^L_{P(z)})` is a weak `V`-module
(Li, Proposition 3.21). -/
noncomputable def regularRepL {z : ℂ} (hz : z ≠ 0) : WeakModule W ((oppBase N).Dsub z) :=
  (oppBase N).weakModuleL (oppShift N) hz

theorem regularRepL_mode {z : ℂ} (hz : z ≠ 0) (a : V) (n : ℤ) (α : (oppBase N).Dsub z) :
    ((mode ((regularRepL N hz).YM a) n α : (oppBase N).Dsub z) : Module.Dual ℂ M)
      = (transBase N (-z)).yR (-z) (neg_ne_zero.2 hz) a n α :=
  (oppBase N).weakModuleL_mode (oppShift N) hz a n α

theorem regularRepR_mode {z : ℂ} (hz : z ≠ 0) (a : V) (n : ℤ) (α : (oppBase N).Dsub z) :
    ((mode ((regularRepR N hz).YM a) n α : (oppBase N).Dsub z) : Module.Dual ℂ M)
      = (oppBase N).yR z hz a n α :=
  OppBase.weakModuleR_mode hz a n α

end Left

end VOA.Huang.LiRegular
