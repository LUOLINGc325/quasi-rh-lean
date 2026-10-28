import QRHShort.SmoothLogCoordinates
import QRHShort.WeightNorm
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open scoped BigOperators ContDiff

namespace QRHShort

def imaginaryExp (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))

theorem imaginaryExp_contDiff (t : ℝ) : ContDiff ℝ ∞ (imaginaryExp t) := by
  unfold imaginaryExp
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Complex.I * (t : ℂ))).mul
    Complex.ofRealCLM.contDiff).cexp

theorem imaginaryExp_hasDerivAt (t x : ℝ) :
    HasDerivAt (imaginaryExp t) (Complex.I * (t : ℂ) * imaginaryExp t x) x := by
  unfold imaginaryExp
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id x).ofReal_comp).const_mul (Complex.I * (t : ℂ))).cexp

theorem imaginaryExp_deriv (t : ℝ) :
    deriv (imaginaryExp t) = fun x => Complex.I * (t : ℂ) * imaginaryExp t x := by
  funext x
  exact (imaginaryExp_hasDerivAt t x).deriv

theorem imaginaryExp_iteratedDeriv (t : ℝ) (j : ℕ) :
    iteratedDeriv j (imaginaryExp t) =
      fun x => (Complex.I * (t : ℂ)) ^ j * imaginaryExp t x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ', imaginaryExp_deriv]
    funext x
    rw [iteratedDeriv_const_mul_field, congrFun ih x, pow_succ]
    ring

theorem imaginaryExp_norm (t x : ℝ) : ‖imaginaryExp t x‖ = 1 := by
  simp [imaginaryExp, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem imaginaryExp_iteratedFDeriv_norm (t x : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (imaginaryExp t) x‖ = |t| ^ j := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, imaginaryExp_iteratedDeriv]
  simp [norm_mul, norm_pow, imaginaryExp_norm, Real.norm_eq_abs]

/-- A fixed smooth real phase has Mellin-frequency growth of order at most `m`
after multiplication by a fixed compactly supported smooth cutoff. -/
theorem cutoff_phase_weightNorm_bound {I : SupportInterval}
    (χ : ℝ → ℂ) (hχ : SmoothSupported I χ)
    (L : ℝ → ℝ) (hL : ContDiff ℝ ∞ L) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SmoothSupported I (fun x => χ x * imaginaryExp t (L x)) ∧
      weightNorm m (fun x => χ x * imaginaryExp t (L x)) ≤ C * (1 + |t|) ^ m := by
  classical
  obtain ⟨A, hA, hAb⟩ := hχ.hasCompactSupport.exists_bound_iteratedFDeriv hχ.1 m
  obtain ⟨D, hD, hDb⟩ := exists_bound_iteratedFDeriv_on_compact hL
    (show IsCompact (Set.Icc I.lo I.hi) from isCompact_Icc) m
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let E (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * A * ((j - i).factorial * D ^ (j - i))
  let C : ℝ := ∑ j ∈ Finset.range (m + 1), E j
  have hE (j : ℕ) : 0 ≤ E j := by dsimp [E]; positivity
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hE j)
  refine ⟨C, hC, ?_⟩
  intro t
  have hs : SmoothSupported I (fun x => χ x * imaginaryExp t (L x)) := by
    refine ⟨hχ.1.mul ((imaginaryExp_contDiff t).comp hL), ?_⟩
    intro x hx
    exact hχ.2 ((mul_ne_zero_iff.mp hx).1)
  refine ⟨hs, ?_⟩
  apply QRHLean3.supZero_le (mul_nonneg hC (by positivity))
  rintro v ⟨j, hj, x, rfl⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : x ∈ Set.Icc I.lo I.hi
  · have hphase (k : ℕ) (hk : k ≤ m) :
        ‖iteratedFDeriv ℝ k (fun y => imaginaryExp t (L y)) x‖ ≤
          (k.factorial : ℝ) * (1 + |t|) ^ m * D ^ k := by
      apply norm_iteratedFDeriv_comp_le (imaginaryExp_contDiff t) hL (by simp) x
      · intro i hi
        rw [imaginaryExp_iteratedFDeriv_norm]
        exact (pow_le_pow_left₀ (abs_nonneg t)
          (le_add_of_nonneg_left zero_le_one) i).trans
            (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg t)) (hi.trans hk))
      · intro i hi₁ hi₂
        exact (hDb i (hi₂.trans hk) x hx).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hD hi₁)
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun y => imaginaryExp t (L y)) x‖ :=
        norm_iteratedFDeriv_mul_le hχ.1 ((imaginaryExp_contDiff t).comp hL) x (by simp)
      _ ≤ E j * (1 + |t|) ^ m := by
        dsimp [E]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc
          _ ≤ (j.choose i : ℝ) * A *
              ((j - i).factorial * (1 + |t|) ^ m * D ^ (j - i)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hAb i (hij.trans hj) x) (by positivity))
              (hphase (j - i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      _ ≤ C * (1 + |t|) ^ m := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hE j)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) (by positivity)
  · have hz : iteratedFDeriv ℝ j (fun x => χ x * imaginaryExp t (L x)) x = 0 := by
      by_contra hn
      exact hx ((closure_minimal hs.2 isClosed_Icc) ((support_iteratedFDeriv_subset j) hn))
    simpa only [hz, norm_zero] using mul_nonneg hC (by positivity : 0 ≤ (1 + |t|) ^ m)

end QRHShort

#print axioms QRHShort.imaginaryExp_iteratedFDeriv_norm
#print axioms QRHShort.cutoff_phase_weightNorm_bound
