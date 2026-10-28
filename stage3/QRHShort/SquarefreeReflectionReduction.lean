import QRHShort.SquarefreePreparedStatements
import QRHShort.SquarefreeReflectionBudget

/-! A finite arithmetic child of the frozen `SquarefreeReflectionStep`.

The remaining child constructs the actual reflected columns, including the
partition `s = t*k`, the fixed ray classes, the local `j = 4` reindexing, and
the divisor bound. It assumes no prepared estimate and no derivative order.
The analytic estimate and the final small-power accounting are discharged
below. All original completed rows, including those meeting `S`, remain in
the covering inequality.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace QRHShort.SquarefreeAssembly

structure ReflectionPacket where
  H : ℝ
  Y : ℝ
  amplitude : ℝ
  A : ℕ → Ideal O → Ideal O → ℂ
  coeff : ℕ → Ideal O → ℂ

def ReflectionPacket.Valid (S : Finset (Ideal O)) (D C L : ℝ)
    (p : ReflectionPacket) : Prop :=
  1 ≤ p.H ∧ p.H ≤ D ^ C ∧ 0 < p.Y ∧ p.Y ≤ L * D ^ C ∧
    0 ≤ p.amplitude ∧ (∀ r n b, ‖p.A r n b‖ ≤ p.amplitude) ∧
    (∀ r k, k ∈ sieveRows S p.H → ‖p.coeff r k‖ ≤ 1)

def reflectionPacketEnergy (S : Finset (Ideal O)) (W : ℝ → ℂ)
    (p : ReflectionPacket) : ℝ :=
  ∑ k ∈ sieveRows S p.H,
    ‖preparedThetaRow W p.H p.Y p.A p.coeff k‖ ^ 2

/-- This is the finite arithmetic obligation, not an extra external input.
`C₁` precedes the arithmetic context, allowing the derivative order in the
prepared estimate to be chosen before that context. `L` and `B` precede the
weight, scales, element `g`, and unit. Coefficients `A` never depend on the
row variable. The cardinality and conductor inequalities are both required. -/
def ReflectionPacketExpansion : Prop :=
  ∀ δ C : ℝ, 0 < δ → 1 ≤ C → ∃ C₁ : ℝ, 1 ≤ C₁ ∧
    ∀ (c : ArithmeticContext) (I : SupportInterval), ArithmeticRelations c →
      ∀ ξ : RayCharacter c, ∃ L B : ℝ, 1 ≤ L ∧ 1 ≤ B ∧
        ∀ (W : ℝ → ℂ) (D H X : ℝ) (g : O) (u : Oˣ),
          SmoothSupported I W → 2 ≤ D →
          1 ≤ H → H ≤ D ^ C → 1 ≤ X → X ≤ D ^ C →
          1 ≤ normElement g → normElement g ≤ D ^ C →
          ∃ N : ℕ, ∃ packet : Fin N → ReflectionPacket,
            (∀ i, (packet i).Valid c.S D C₁ L) ∧
            (N : ℝ) ≤ B * D ^ δ ∧
            (∀ i, (packet i).amplitude ^ 2 * ((packet i).H + (packet i).Y) ≤
              B * (H + H ^ (2 : ℕ) * normElement g / X)) ∧
            (∑' s : Ideal O, if s ≠ ⊥ ∧ Squarefree s ∧ normIdeal s ≤ H then
              ‖completedRowElement c ξ W X ((u : O) * chosenGenerator s) g‖ ^ 2
              else 0) ≤ (N : ℝ) * ∑ i, reflectionPacketEnergy c.S W (packet i)

/-- The outstanding finite reflection child has exactly the three original
arithmetic/theta premises, and contains no analytic mean-square premise. -/
def SquarefreeReflectionPacketStep : Prop :=
  ReflectionStatement → ReflectionUniformityStatement → ThetaBoundsStatement →
    ReflectionPacketExpansion

theorem squarefree_completed_by_character_of_packets
    (hexpand : ReflectionPacketExpansion) (hprepared : PreparedThetaEstimate) :
    SquarefreeCompletedByCharacter := by
  intro ε C hε hC
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C₁, hC₁, hexpand⟩ := hexpand δ C hδ hC
  obtain ⟨J, hJ, hprepared⟩ := hprepared δ C₁ hδ hC₁
  refine ⟨J, hJ, ?_⟩
  intro c I hc ξ
  obtain ⟨L, B, hL, hB, hexpand⟩ := hexpand c I hc ξ
  obtain ⟨K, hK, hprepared⟩ := hprepared c.S I L hL
  refine ⟨K * B ^ 3, mul_nonneg hK (pow_nonneg (by linarith) _), ?_⟩
  intro W D H X g u hW hD hH hHC hX hXC hg hgC
  obtain ⟨N, packet, hvalid, hN, hcost, hcover⟩ :=
    hexpand W D H X g u hW hD hH hHC hX hXC hg hgC
  have hDpos : 0 < D := by linarith
  have hP : 0 ≤ H + H ^ (2 : ℕ) * normElement g / X := by positivity
  have hE : ∀ i, reflectionPacketEnergy c.S W (packet i) ≤
      K * D ^ δ * weightNorm J W ^ 2 *
        (B * (H + H ^ (2 : ℕ) * normElement g / X)) := by
    intro i
    obtain ⟨hHi, hHiC, hYi, hYiC, hai, hAi, hcoeffi⟩ := hvalid i
    have hi := (hprepared W D (packet i).H (packet i).Y (packet i).amplitude
      (packet i).A (packet i).coeff hW hD hHi hHiC hYi hYiC hai hAi hcoeffi).2
    change reflectionPacketEnergy c.S W (packet i) ≤ _ at hi
    calc
      reflectionPacketEnergy c.S W (packet i) ≤
          (K * D ^ δ * weightNorm J W ^ 2) *
            ((packet i).amplitude ^ 2 * ((packet i).H + (packet i).Y)) := by
        simpa only [mul_assoc] using hi
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcost i) (by positivity)
  have hbudget := reflection_packet_budget N
    (fun i => reflectionPacketEnergy c.S W (packet i))
    _ K B D (weightNorm J W ^ 2)
    (H + H ^ (2 : ℕ) * normElement g / X) δ hK (by linarith) hDpos
    (sq_nonneg _) hP hcover hN hE
  have hexp : δ + δ + δ = ε := by dsimp [δ]; ring
  rwa [hexp] at hbudget

/-- Conditional composition only. Discharging `hpacket` proves the frozen
reflection node; it is not hidden in the analytic upstream hypotheses. -/
theorem squarefree_reflection_step_of_packets
    (hpacket : SquarefreeReflectionPacketStep) : SquarefreeReflectionStep := by
  intro hr hu hb hprepared
  exact squarefree_completed_by_character_of_packets (hpacket hr hu hb) hprepared

end QRHShort.SquarefreeAssembly

#print axioms QRHShort.SquarefreeAssembly.squarefree_completed_by_character_of_packets
#print axioms QRHShort.SquarefreeAssembly.squarefree_reflection_step_of_packets
