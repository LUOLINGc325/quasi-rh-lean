import QRHShort.SquarefreeReflectionReduction
import QRHShort.SquarefreeReflectionLocal
import QRHShort.SquarefreeReflectionCount
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! Two internal children of the frozen reflection-packet node.

`SquarefreeRawReflectionStep` handles the finite arithmetic: split s=t*k,
resolve the fixed ray characters, apply the reflection formula, and bound
the number and conductors of the resulting raw columns.

`DualThetaPacketStep` handles one raw column: absolutely convergent theta
support reindexing and the three substitutions at exponent 4. It has no
completed-row estimate, no reflection premise, and no divisor-bound premise.

Neither child is asserted. The theorem below discharges the finite Cauchy
and indexing operations and proves that these exact children imply the
unchanged `SquarefreeReflectionPacketStep`.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

structure RawReflectionPacket where
  H : ℝ
  amplitude : ℝ
  datum : ReflectionDatum
  active : Finset (Ideal O)
  exponent : Ideal O → Fin 6
  coeff : Ideal O → ℂ

def rawReflectionScale (X : ℝ) (p : RawReflectionPacket) : ℝ :=
  normElement p.datum.denominator ^ 2 * p.H ^ 2 / X

def rawReflectionCost (p : RawReflectionPacket) : ℝ :=
  ∏ q ∈ p.active, reflectionLocalCost (normIdeal q) (p.exponent q)

def RawReflectionPacket.Valid (S : Finset (Ideal O)) (D C L X : ℝ)
    (Q : ℕ) (p : RawReflectionPacket) : Prop :=
  1 ≤ p.H ∧ p.H ≤ D ^ C ∧
    0 < rawReflectionScale X p ∧
    rawReflectionScale X p * (∏ q ∈ p.active, normIdeal q ^ 2) ≤ L * D ^ C ∧
    0 ≤ p.amplitude ∧ PrimeTwistSet S p.active ∧
    (∀ k ∈ sieveRows S p.H, ‖p.coeff k‖ ≤ 1) ∧
    (∀ k ∈ sieveRows S p.H,
      ¬ IsRelPrime k (∏ q ∈ p.active, q) → p.coeff k = 0) ∧
    6 * 3 ^ p.active.card ≤ Q

def rawReflectionRow (W : ℝ → ℂ) (X : ℝ) (p : RawReflectionPacket)
    (k : Ideal O) : ℂ :=
  (p.amplitude : ℂ) * p.coeff k *
    dualThetaSum p.datum (p.active ∪ primeFactors k)
      (variableTwistExponents p.active p.exponent)
      (fun x => (Real.sqrt x : ℂ) * W x) X

def rawReflectionEnergy (S : Finset (Ideal O)) (W : ℝ → ℂ) (X : ℝ)
    (p : RawReflectionPacket) : ℝ :=
  ∑ k ∈ sieveRows S p.H, ‖rawReflectionRow W X p k‖ ^ 2

/-- The integer Q is a common bound for all local branches and units.
A uniform bound on M*Q avoids a second divisor estimate in the
assembly. The raw cost is q at j=0,4 and q² otherwise, not the full squared
conductor at every prime. -/
def RawReflectionExpansion : Prop :=
  ∀ δ C : ℝ, 0 < δ → 1 ≤ C → ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∀ ξ : RayCharacter c, ∃ L B : ℝ, 1 ≤ L ∧ 1 ≤ B ∧
        ∀ (W : ℝ → ℂ) (D H X : ℝ) (g : O) (u : Oˣ),
          SmoothSupported I W → 2 ≤ D →
          1 ≤ H → H ≤ D ^ C → 1 ≤ X → X ≤ D ^ C →
          1 ≤ normElement g → normElement g ≤ D ^ C →
          ∃ M Q : ℕ, ∃ packet : Fin M → RawReflectionPacket,
            (∀ i, (packet i).Valid c.S D C₁ L X Q) ∧
            ((M * Q : ℕ) : ℝ) ≤ B * D ^ δ ∧
            (∀ i, (packet i).amplitude ^ 2 *
              ((packet i).H + rawReflectionScale X (packet i) *
                rawReflectionCost (packet i)) ≤
              B * (H + H ^ (2 : ℕ) * normElement g / X)) ∧
            (∑' s : Ideal O, if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then
              ‖completedRowElement c ξ W X ((u : O) * chosenGenerator s) g‖ ^ 2
              else 0) ≤ (M : ℝ) * ∑ i, rawReflectionEnergy c.S W X (packet i)

def SquarefreeRawReflectionStep : Prop :=
  ReflectionStatement → ReflectionUniformityStatement → RawReflectionExpansion

/-- A single-column analytic/algebraic identity. Absolute summability is
explicit, so a divergent `tsum` cannot justify a rearrangement. All row
dependence must be in the bounded coefficients, never in A. Empty added
slots allow the common Q to exceed the actual number of local branches. -/
def DualThetaPacketStep : Prop :=
  ThetaBoundsStatement →
    ∀ (c : ArithmeticContext) (I : SupportInterval) (W : ℝ → ℂ)
      (D C L X : ℝ) (Q : ℕ) (p : RawReflectionPacket),
      SmoothSupported I W → 2 ≤ D → 1 ≤ C → 1 ≤ L → 0 < X →
      p.Valid c.S D C L X Q →
      ∃ packet : Fin Q → ReflectionPacket,
        (∀ i, (packet i).Valid c.S D C L ∧ (packet i).H = p.H ∧
          (packet i).amplitude ^ 2 * ((packet i).H + (packet i).Y) ≤
            729 * (p.amplitude ^ 2 *
              (p.H + rawReflectionScale X p * rawReflectionCost p))) ∧
        (∀ i k, k ∈ sieveRows c.S p.H →
          Summable (fun q => ‖preparedThetaTerm W (packet i).H (packet i).Y
            (packet i).A (packet i).coeff k q‖)) ∧
        (∀ k ∈ sieveRows c.S p.H,
          rawReflectionRow W X p k = ∑ i,
            preparedThetaRow W (packet i).H (packet i).Y
              (packet i).A (packet i).coeff k)

theorem raw_reflection_energy_le_packets
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (X : ℝ) (Q : ℕ)
    (p : RawReflectionPacket) (packet : Fin Q → ReflectionPacket)
    (hH : ∀ i, (packet i).H = p.H)
    (hrow : ∀ k ∈ sieveRows S p.H,
      rawReflectionRow W X p k = ∑ i,
        preparedThetaRow W (packet i).H (packet i).Y
          (packet i).A (packet i).coeff k) :
    rawReflectionEnergy S W X p ≤
      (Q : ℝ) * ∑ i, reflectionPacketEnergy S W (packet i) := by
  unfold rawReflectionEnergy
  calc
    (∑ k ∈ sieveRows S p.H, ‖rawReflectionRow W X p k‖ ^ 2) ≤
        ∑ k ∈ sieveRows S p.H, (Q : ℝ) *
          ∑ i, ‖preparedThetaRow W (packet i).H (packet i).Y
            (packet i).A (packet i).coeff k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hrow k hk]
      exact norm_sum_sq_le_card_sum Q _
    _ = (Q : ℝ) * ∑ i, reflectionPacketEnergy S W (packet i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [reflectionPacketEnergy, hH i]

/-- Exact assembly of the two children, including the original rows that
meet S. The only numerical enlargement is the theta bound 27² = 729. -/
theorem squarefree_reflection_packet_step_of_children
    (hraw : SquarefreeRawReflectionStep) (hlocal : DualThetaPacketStep) :
    SquarefreeReflectionPacketStep := by
  intro hr hu hb δ C hδ hC
  obtain ⟨C₁, hC₁, hraw⟩ := hraw hr hu δ C hδ hC
  refine ⟨C₁, hC₁, ?_⟩
  intro c I hc ξ
  obtain ⟨L, B, hL, hB, hraw⟩ := hraw c I hc ξ
  refine ⟨L, 729 * B, hL, by nlinarith, ?_⟩
  intro W D H X g u hW hD hH hHC hX hXC hg hgC
  obtain ⟨M, Q, raw, hvalid, hcount, hcost, hcover⟩ :=
    hraw W D H X g u hW hD hH hHC hX hXC hg hgC
  have hpack := fun i : Fin M =>
    hlocal hb c I W D C₁ L X Q (raw i) hW hD hC₁ hL (by linarith) (hvalid i)
  choose packet hpacket hsummable hrow using hpack
  let e : (Fin M × Fin Q) ≃ Fin (M * Q) := finProdFinEquiv
  let flat : Fin (M * Q) → ReflectionPacket :=
    fun i => packet (e.symm i).1 (e.symm i).2
  refine ⟨M * Q, flat, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hpacket (e.symm i).1 (e.symm i).2).1
  · exact hcount.trans (mul_le_mul_of_nonneg_right
      (show B ≤ 729 * B by nlinarith) (Real.rpow_nonneg (by linarith) _))
  · intro i
    calc
      _ ≤ 729 * ((raw (e.symm i).1).amplitude ^ 2 *
          ((raw (e.symm i).1).H + rawReflectionScale X (raw (e.symm i).1) *
            rawReflectionCost (raw (e.symm i).1))) :=
        (hpacket (e.symm i).1 (e.symm i).2).2.2
      _ ≤ 729 * (B * (H + H ^ (2 : ℕ) * normElement g / X)) :=
        mul_le_mul_of_nonneg_left (hcost _) (by norm_num)
      _ = _ := by ring
  · have henergy : ∀ i, rawReflectionEnergy c.S W X (raw i) ≤
        (Q : ℝ) * ∑ j, reflectionPacketEnergy c.S W (packet i j) := by
      intro i
      exact raw_reflection_energy_le_packets c.S W X Q (raw i) (packet i)
        (fun j => (hpacket i j).2.1) (hrow i)
    have hflat : (∑ i, reflectionPacketEnergy c.S W (flat i)) =
        ∑ i, ∑ j, reflectionPacketEnergy c.S W (packet i j) := by
      exact (e.symm.sum_comp (fun ij : Fin M × Fin Q =>
        reflectionPacketEnergy c.S W (packet ij.1 ij.2))).trans
          (Fintype.sum_prod_type _)
    calc
      _ ≤ (M : ℝ) * ∑ i, rawReflectionEnergy c.S W X (raw i) := hcover
      _ ≤ (M : ℝ) * ∑ i, (Q : ℝ) *
          ∑ j, reflectionPacketEnergy c.S W (packet i j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => henergy i))
          (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, hflat, Nat.cast_mul]; ring

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.raw_reflection_energy_le_packets
#print axioms QRHShort.SquarefreeAssembly.squarefree_reflection_packet_step_of_children
