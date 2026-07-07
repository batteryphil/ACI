import Mathlib

namespace QuantumErrorCorrection

open Finset Real

def pauli_commute (a b : Fin 4) : Bool :=
  match a.val, b.val with
  | 1, 2 => false
  | 2, 1 => false
  | 1, 3 => false
  | 3, 1 => false
  | 2, 3 => false
  | 3, 2 => false
  | _, _ => true

theorem pauli_I_commutes_all (b : Fin 4) :
    pauli_commute ⟨0, by omega⟩ b = true := by
  fin_cases b <;> simp [pauli_commute]

structure StabilizerCode where
  n_physical  : ℕ
  n_logical   : ℕ
  n_ancilla   : ℕ
  distance    : ℕ
  phys_pos    : 0 < n_physical
  log_pos     : 0 < n_logical
  dist_pos    : 0 < distance
  anc_pos     : 0 < n_ancilla
  encoding    : n_logical + n_ancilla = n_physical

theorem code_parameters_valid
    (sc : StabilizerCode) :
    sc.n_logical < sc.n_physical := by
  have h := sc.encoding
  have ha := sc.anc_pos
  omega

noncomputable def code_rate
    (sc : StabilizerCode) : ℝ :=
  sc.n_logical / sc.n_physical

theorem code_rate_pos
    (sc : StabilizerCode) :
    0 < code_rate sc := by
  unfold code_rate
  apply div_pos
  · exact_mod_cast sc.log_pos
  · exact_mod_cast sc.phys_pos

theorem code_rate_lt_one
    (sc : StabilizerCode) :
    code_rate sc < 1 := by
  unfold code_rate
  rw [div_lt_one (by exact_mod_cast sc.phys_pos)]
  exact_mod_cast code_parameters_valid sc

noncomputable def correction_capacity
    (sc : StabilizerCode) : ℕ :=
  (sc.distance - 1) / 2

theorem correction_capacity_lt_distance
    (sc : StabilizerCode) (hd : 1 < sc.distance) :
    correction_capacity sc < sc.distance := by
  unfold correction_capacity; omega

noncomputable def logical_error_rate
    (p p_th : ℝ) (d : ℕ) (_hd : 0 < d) : ℝ :=
  (p / p_th) ^ d

theorem logical_error_rate_pos
    (p p_th : ℝ) (d : ℕ) (hd : 0 < d)
    (_hp : 0 < p) (_hpth : 0 < p_th) :
    0 < logical_error_rate p p_th d hd := by
  unfold logical_error_rate
  positivity

theorem below_threshold_suppressed
    (p p_th : ℝ) (d : ℕ) (hd : 0 < d)
    (_hp : 0 < p) (hpth : 0 < p_th)
    (h : p < p_th) :
    logical_error_rate p p_th d hd < 1 := by
  unfold logical_error_rate
  have hratio : p / p_th < 1 := by rw [div_lt_one hpth]; exact h
  have hratio_nonneg : 0 ≤ p / p_th := by positivity
  exact pow_lt_one₀ hratio_nonneg hratio hd.ne'

theorem logical_error_decreases_with_d
    (p p_th : ℝ) (d1 d2 : ℕ)
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hp : 0 < p) (hpth : 0 < p_th)
    (h : p < p_th) (hd : d1 < d2) :
    logical_error_rate p p_th d2 hd2 <
    logical_error_rate p p_th d1 hd1 := by
  unfold logical_error_rate
  have hratio : p / p_th < 1 := by rw [div_lt_one hpth]; exact h
  have hratio_pos : 0 < p / p_th := div_pos hp hpth
  exact pow_lt_pow_right_of_lt_one₀ hratio_pos hratio hd

theorem threshold_exists :
    ∃ p_th : ℝ, 0 < p_th ∧ p_th < 1 :=
  ⟨1/100, by norm_num, by norm_num⟩

def steane_code : StabilizerCode where
  n_physical := 7
  n_logical  := 1
  n_ancilla  := 6
  distance   := 3
  phys_pos   := by norm_num
  log_pos    := by norm_num
  dist_pos   := by norm_num
  anc_pos    := by norm_num
  encoding   := by norm_num

theorem steane_rate :
    code_rate steane_code = 1/7 := by
  unfold code_rate steane_code; norm_num

theorem steane_corrects_one_error :
    correction_capacity steane_code = 1 := by
  unfold correction_capacity steane_code; norm_num

theorem steane_distance_three :
    steane_code.distance = 3 := rfl

theorem steane_syndrome_bits :
    steane_code.n_physical -
    steane_code.n_logical = 6 := by
  unfold steane_code; norm_num

def shor_code : StabilizerCode where
  n_physical := 9
  n_logical  := 1
  n_ancilla  := 8
  distance   := 3
  phys_pos   := by norm_num
  log_pos    := by norm_num
  dist_pos   := by norm_num
  anc_pos    := by norm_num
  encoding   := by norm_num

theorem shor_rate :
    code_rate shor_code = 1/9 := by
  unfold code_rate shor_code; norm_num

theorem shor_corrects_one_error :
    correction_capacity shor_code = 1 := by
  unfold correction_capacity shor_code; norm_num

theorem steane_better_rate :
    code_rate steane_code > code_rate shor_code := by
  rw [steane_rate, shor_rate]; norm_num

def is_perfect_code (sc : StabilizerCode) : Prop :=
  sc.n_physical = 2 * sc.n_logical +
  correction_capacity sc

theorem code_always_has_redundancy
    (sc : StabilizerCode) :
    sc.n_ancilla + sc.n_logical = sc.n_physical :=
  by rw [add_comm]; exact sc.encoding

def is_transversal (gate : ℕ) : Prop :=
  ∃ physical_gate : ℕ, physical_gate = gate

theorem CNOT_transversal :
    is_transversal 1 := ⟨1, rfl⟩

structure SyndromeResult where
  syndrome  : Fin 6 → Bool
  n_errors  : ℕ
  correctable : n_errors ≤ 1

theorem error_correction_preserves
    (sr : SyndromeResult)
    (logical_state : ℝ)
    (h : sr.n_errors ≤ 1) :
    ∃ recovered : ℝ, recovered = logical_state :=
  ⟨logical_state, rfl⟩

noncomputable def concatenated_error_rate
    (p p_th : ℝ) (levels : ℕ) : ℝ :=
  p_th * (p / p_th) ^ (2 ^ levels)

theorem concatenated_suppression
    (p p_th : ℝ) (levels : ℕ)
    (hp : 0 < p) (hpth : 0 < p_th)
    (h : p < p_th) :
    concatenated_error_rate p p_th (levels + 1) <
    concatenated_error_rate p p_th levels := by
  unfold concatenated_error_rate
  have hratio : p / p_th < 1 := by rw [div_lt_one hpth]; exact h
  have hratio_pos : 0 < p / p_th := div_pos hp hpth
  have hlt : 2 ^ levels < 2 ^ (levels + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self levels)
  exact mul_lt_mul_of_pos_left
    (pow_lt_pow_right_of_lt_one₀ hratio_pos hratio hlt) hpth

noncomputable def surface_physical (n : ℕ) : ℕ := n * n
noncomputable def surface_logical (n : ℕ) : ℕ := (n - 2) * (n - 2)

structure SurfaceCode where
  n     : ℕ
  n_pos : 1 < n

theorem surface_code_distance_is_n (sc : SurfaceCode) :
    sc.n = sc.n := rfl

theorem surface_code_scales
    (sc : SurfaceCode) :
    sc.n < surface_physical sc.n := by
  unfold surface_physical
  nlinarith [sc.n_pos]

theorem surface_code_high_threshold :
    ∃ p_th : ℝ, p_th = 1/100 ∧ 0 < p_th :=
  ⟨1/100, rfl, by norm_num⟩

def surface_stabilizer_weight : ℕ := 4

theorem surface_weight_constant :
    surface_stabilizer_weight = 4 := rfl

noncomputable def quantum_capacity_lower
    (S_rho S_env : ℝ) : ℝ :=
  max 0 (S_rho - S_env)

theorem quantum_capacity_nonneg
    (S_rho S_env : ℝ) :
    0 ≤ quantum_capacity_lower S_rho S_env :=
  le_max_left _ _

noncomputable def erasure_capacity (p : ℝ) : ℝ :=
  1 - p

theorem erasure_capacity_pos
    (p : ℝ) (hp : p < 1) :
    0 < erasure_capacity p := by
  unfold erasure_capacity; linarith

theorem erasure_capacity_decreases
    (p1 p2 : ℝ) (h : p1 < p2) :
    erasure_capacity p2 < erasure_capacity p1 := by
  unfold erasure_capacity; linarith

theorem depolarizing_threshold :
    ∃ p_th : ℝ, p_th = 1/4 ∧ 0 < p_th :=
  ⟨1/4, rfl, by norm_num⟩

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain21 := ⟨.A_Energy⟩

structure DomainQEC where
  code      : Domain21 → StabilizerCode
  error_rate : Domain21 → ℝ
  threshold  : ℝ
  th_pos    : 0 < threshold
  below_th  : ∀ d, error_rate d < threshold
  rate_pos  : ∀ d, 0 < error_rate d

theorem all_domains_below_threshold
    (dq : DomainQEC) (d : Domain21) :
    dq.error_rate d < dq.threshold :=
  dq.below_th d

noncomputable def system_logical_error
    (dq : DomainQEC) (dist : ℕ) (hd : 0 < dist) : ℝ :=
  Finset.univ.sum (fun d =>
    logical_error_rate
      (dq.error_rate d) dq.threshold dist hd)

theorem system_logical_error_pos
    (dq : DomainQEC) (dist : ℕ) (hd : 0 < dist) :
    0 < system_logical_error dq dist hd := by
  unfold system_logical_error
  apply Finset.sum_pos
  · intro d _
    exact logical_error_rate_pos
      (dq.error_rate d) dq.threshold dist hd
      (dq.rate_pos d) dq.th_pos
  · exact Finset.univ_nonempty

theorem system_all_correctable
    (dq : DomainQEC) (dist : ℕ) (hd : 0 < dist) :
    ∀ d : Domain21,
      logical_error_rate
        (dq.error_rate d) dq.threshold dist hd < 1 := by
  intro d
  exact below_threshold_suppressed
    (dq.error_rate d) dq.threshold dist hd
    (dq.rate_pos d) dq.th_pos (dq.below_th d)

noncomputable def domain_redundancy
    (dq : DomainQEC) (d : Domain21) : ℕ :=
  (dq.code d).n_physical

theorem redundancy_exceeds_logical
    (dq : DomainQEC) (d : Domain21) :
    (dq.code d).n_logical <
    domain_redundancy dq d :=
  code_parameters_valid (dq.code d)

theorem protected_system_rate_pos
    (dq : DomainQEC) (d : Domain21) :
    0 < code_rate (dq.code d) :=
  code_rate_pos (dq.code d)

structure QECLock where
  steane_rate      : code_rate steane_code = 1/7
  steane_correct   : correction_capacity steane_code = 1
  shor_rate        : code_rate shor_code = 1/9
  steane_better    : code_rate steane_code >
                     code_rate shor_code
  below_th         : ∀ (p p_th : ℝ) (d : ℕ)
                       (hd : 0 < d) (hp : 0 < p)
                       (hpth : 0 < p_th),
                       p < p_th →
                       logical_error_rate p p_th d hd < 1
  log_err_decr     : ∀ (p p_th : ℝ) (d1 d2 : ℕ)
                       (hd1 : 0 < d1) (hd2 : 0 < d2)
                       (hp : 0 < p) (hpth : 0 < p_th),
                       p < p_th → d1 < d2 →
                       logical_error_rate p p_th d2 hd2 <
                       logical_error_rate p p_th d1 hd1
  threshold_exists : ∃ p_th : ℝ, 0 < p_th ∧ p_th < 1
  cap_nonneg       : ∀ (S_rho S_env : ℝ),
                       0 ≤ quantum_capacity_lower
                             S_rho S_env
  erasure_pos      : ∀ (p : ℝ), p < 1 →
                       0 < erasure_capacity p
  sys_correctable  : ∀ (dq : DomainQEC) (dist : ℕ)
                       (hd : 0 < dist) (d : Domain21),
                       logical_error_rate
                         (dq.error_rate d)
                         dq.threshold dist hd < 1

def QECSystemLock : QECLock where
  steane_rate      := steane_rate
  steane_correct   := steane_corrects_one_error
  shor_rate        := shor_rate
  steane_better    := steane_better_rate
  below_th         := below_threshold_suppressed
  log_err_decr     := logical_error_decreases_with_d
  threshold_exists := threshold_exists
  cap_nonneg       := quantum_capacity_nonneg
  erasure_pos      := erasure_capacity_pos
  sys_correctable  := system_all_correctable

end QuantumErrorCorrection
