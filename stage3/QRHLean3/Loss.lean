import QRHLean3.Supremum
import QRH.Powers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace QRHLean3

/-- L1: normalized child weights remove the norm factor (paper2.tex:1582–1588). -/
theorem normalized_energy_bound {E Sigma K D ε N : ℝ}
    (hSigma : 0 < Sigma) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hN0 : 0 ≤ N) (hN1 : N ≤ 1)
    (hE : E ≤ K * D ^ ε * Sigma * N ^ 2) : E / Sigma ≤ K * D ^ ε := by
  have hDpow : 0 ≤ D ^ ε := Real.rpow_nonneg hD ε
  have hNsq : N ^ 2 ≤ (1 : ℝ) := by
    simpa only [sq, one_mul] using mul_self_le_mul_self hN0 hN1
  apply (div_le_iff₀ hSigma).2
  calc
    E ≤ K * D ^ ε * Sigma * N ^ 2 := hE
    _ ≤ K * D ^ ε * Sigma * 1 :=
      mul_le_mul_of_nonneg_left hNsq (by positivity)
    _ = K * D ^ ε * Sigma := mul_one _

/-- L2: three epsilon/3 factors multiply to the required epsilon loss. -/
theorem epsilon_thirds {D : ℝ} (hD : 0 < D) (ε : ℝ) :
    (D ^ (ε / 3)) ^ (3 : ℕ) = D ^ ε := by
  rw [← Real.rpow_mul_natCast hD.le]
  congr 1
  ring

/-- L3: absorb the transfer estimate's additive one; q will be D^(ε/3). -/
theorem transfer_loss_bound {q Sigma N T A B S : ℝ}
    (hq : 1 ≤ q) (hSigma : 0 ≤ Sigma) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : S ≤ B * q)
    (hT : T ≤ A * q * Sigma * N ^ 2 * (1 + S)) :
    T ≤ A * (1 + B) * q ^ 2 * Sigma * N ^ 2 := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hone : 1 + S ≤ (1 + B) * q := by nlinarith only [hq, hS]
  calc
    T ≤ A * q * Sigma * N ^ 2 * (1 + S) := hT
    _ ≤ A * q * Sigma * N ^ 2 * ((1 + B) * q) :=
      mul_le_mul_of_nonneg_left hone (by positivity)
    _ = A * (1 + B) * q ^ 2 * Sigma * N ^ 2 := by ring

/-- L4: absorb the cube estimate's base term and bounded column supremum. -/
theorem cube_loss_bound {q Sigma N E C K S : ℝ}
    (hq : 1 ≤ q) (hSigma : 0 ≤ Sigma) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hS : S ≤ K * q ^ 2 * Sigma * N ^ 2)
    (hE : E ≤ C * q * (Sigma * N ^ 2 + S)) :
    E ≤ C * (1 + K) * q ^ 3 * Sigma * N ^ 2 := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hq2 : 1 ≤ q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hbase : Sigma * N ^ 2 ≤ q ^ 2 * (Sigma * N ^ 2) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq2 (mul_nonneg hSigma (sq_nonneg N))
  have hsum : Sigma * N ^ 2 + S ≤ (1 + K) * q ^ 2 * Sigma * N ^ 2 := by
    calc
      Sigma * N ^ 2 + S ≤ q ^ 2 * (Sigma * N ^ 2) + K * q ^ 2 * Sigma * N ^ 2 :=
        add_le_add hbase hS
      _ = (1 + K) * q ^ 2 * Sigma * N ^ 2 := by ring
  calc
    E ≤ C * q * (Sigma * N ^ 2 + S) := hE
    _ ≤ C * q * ((1 + K) * q ^ 2 * Sigma * N ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC hq0)
    _ = C * (1 + K) * q ^ 3 * Sigma * N ^ 2 := by ring

/-- L5: induction → transfer → cube scalar substitution, including empty sets.
Constants are uniform in the column index. N is a common upper bound for the
two parent-weight norms, after choosing J ≥ cubeOrder and J ≥ 4m+12.
This theorem does not prove the analytic hypotheses htransfer or hcube. -/
theorem nested_energy_bound {ι : Type*} {D ε Sigma N E C A B : ℝ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hSigma : 0 ≤ Sigma)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (columns : Set ι) (columnEnergy : ι → ℝ) (children : ι → Set ℝ)
    (hchildren : ∀ b ∈ columns, ∀ r ∈ children b, r ≤ B * D ^ (ε / 3))
    (htransfer : ∀ b ∈ columns,
      columnEnergy b ≤ A * D ^ (ε / 3) * Sigma * N ^ 2 * (1 + supZero (children b)))
    (hcube : E ≤ C * D ^ (ε / 3) * (Sigma * N ^ 2 + supZero (columnEnergy '' columns))) :
    E ≤ C * (1 + A * (1 + B)) * D ^ ε * Sigma * N ^ 2 := by
  have hq : 1 ≤ D ^ (ε / 3) := Real.one_le_rpow hD (by positivity)
  have hq0 : 0 ≤ D ^ (ε / 3) := le_trans zero_le_one hq
  have hchild : ∀ b ∈ columns, supZero (children b) ≤ B * D ^ (ε / 3) := by
    intro b hb
    exact supZero_le (mul_nonneg hB hq0) (hchildren b hb)
  have hcolumns : supZero (columnEnergy '' columns) ≤
      A * (1 + B) * (D ^ (ε / 3)) ^ 2 * Sigma * N ^ 2 := by
    apply supZero_le (by positivity)
    rintro x ⟨b, hb, rfl⟩
    exact transfer_loss_bound hq hSigma hA hB (hchild b hb) (htransfer b hb)
  have hfinal := cube_loss_bound hq hSigma hC
    (show 0 ≤ A * (1 + B) by positivity) hcolumns hcube
  rwa [epsilon_thirds (lt_of_lt_of_le zero_lt_one hD) ε] at hfinal

end QRHLean3
