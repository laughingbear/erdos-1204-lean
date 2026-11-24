/-
Copyright 2026 Laughing Bear.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import PrimeNumberTheoremAnd.Consequences

/-!
# Erdős Problem 1204: the upper bounds `A(k) ≤ (1+o(1)) k log k`, `B(k) ≤ (1/2+o(1)) k log k`

Proofs of `Erdos1204.erdos_1204.variants.A_upper` and `Erdos1204.erdos_1204.variants.B_upper`
from google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1204.lean`). The
definitions `IsAdmissible`, `A`, `minSum`, `B` and the lemma `A_le` are copied verbatim.

Construction: the `k` smallest primes larger than `k`, i.e. `p_n` for `π(k) ≤ n < π(k) + k`.
It misses `0` modulo every prime `q ≤ k`, and has fewer than `q` elements for a prime `q > k`.
The bounds follow from `p_n ~ n log n` (`nth_prime_asymp`, PrimeNumberTheoremAnd) and
`π(x) ~ x / log x` (`pi_alt'`), which gives `π(k) = o(k)`.
-/

open Filter Asymptotics

namespace Erdos1204

/-- A finite set `S` of natural numbers is *admissible* if it misses at least one residue class
modulo every prime. A sequence $0\leq a_1<\cdots <a_k$ is identified with the set of its values. -/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r

/-- $A(k)$: the least possible value of $a_k$ over admissible sequences $0\leq a_1<\cdots <a_k$.
Any $k$ primes larger than $k$ form an admissible set, so `sInf` is a true minimum. -/
noncomputable def A (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∀ a ∈ S, a ≤ m}

/-- The least possible value of $a_1+\cdots+a_k$ over admissible sequences
$0\leq a_1<\cdots <a_k$. As for `A`, the minimum exists. -/
noncomputable def minSum (k : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∑ a ∈ S, a = s}

/-- $B(k)=\min \frac{a_1+\cdots+a_k}{k}$. -/
noncomputable def B (k : ℕ) : ℝ := (minSum k : ℝ) / k

/-- An admissible set of `k` natural numbers inside `[0, m]` gives `A k ≤ m`. -/
theorem A_le {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S)
    (hm : ∀ a ∈ S, a ≤ m) : A k ≤ m :=
  Nat.sInf_le ⟨S, hS, hadm, hm⟩

/-! ## The construction: the `k` smallest primes larger than `k` -/

/-- `P n` is the `n`-th prime (0-indexed). -/
noncomputable abbrev P (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma P_prime (n : ℕ) : (P n).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n

lemma P_mono : Monotone P := Nat.nth_monotone Nat.infinite_setOfPred_prime

lemma P_inj : Function.Injective P := Nat.nth_injective Nat.infinite_setOfPred_prime

/-- `P (π k + i) > k`. -/
lemma lt_P (k i : ℕ) : k < P (Nat.primeCounting k + i) := by
  have h : k + 1 ≤ P (Nat.primeCounting k) :=
    Nat.le_nth_count Nat.infinite_setOfPred_prime (k + 1)
  have h2 : P (Nat.primeCounting k) ≤ P (Nat.primeCounting k + i) := P_mono (by omega)
  omega

/-- The `k` smallest primes larger than `k`. -/
noncomputable def T (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => P (Nat.primeCounting k + i))

lemma card_T (k : ℕ) : (T k).card = k := by
  rw [T, Finset.card_image_of_injective _ (fun i j h => by simpa using P_inj h),
    Finset.card_range]

lemma mem_T {k a : ℕ} : a ∈ T k ↔ ∃ i < k, P (Nat.primeCounting k + i) = a := by
  simp [T]

lemma admissible_T (k : ℕ) : IsAdmissible (T k) := by
  intro q hq
  by_cases hqk : q ≤ k
  · refine ⟨0, fun a ha h0 => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_T.1 ha
    have hdvd : q ∣ P (Nat.primeCounting k + i) := (ZMod.natCast_eq_zero_iff _ _).1 h0
    have := (Nat.prime_dvd_prime_iff_eq hq (P_prime _)).1 hdvd
    have := lt_P k i
    omega
  · have : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨r, hr⟩ : ∃ r : ZMod q, r ∉ (T k).image (fun a : ℕ => (a : ZMod q)) := by
      by_contra! h
      have hsub : (Finset.univ : Finset (ZMod q)) ⊆ (T k).image (fun a : ℕ => (a : ZMod q)) :=
        fun r _ => h r
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, ZMod.card] at h1
      have h2 := Finset.card_image_le (s := T k) (f := fun a : ℕ => (a : ZMod q))
      rw [card_T] at h2
      omega
    exact ⟨r, fun a ha hra => hr (Finset.mem_image.2 ⟨a, ha, hra⟩)⟩

lemma A_le_P (k : ℕ) : A k ≤ P (Nat.primeCounting k + k) :=
  A_le (card_T k) (admissible_T k) fun a ha => by
    obtain ⟨i, hi, rfl⟩ := mem_T.1 ha
    exact P_mono (by omega)

lemma minSum_le (k : ℕ) : minSum k ≤ ∑ i ∈ Finset.range k, P (Nat.primeCounting k + i) := by
  refine Nat.sInf_le ⟨T k, card_T k, admissible_T k, ?_⟩
  rw [T, Finset.sum_image fun i _ j _ h => by simpa using P_inj h]

/-! ## Asymptotic input -/

open Real

/-- `p_n ≤ (1 + δ) n log n` for all large `n`. -/
lemma eventually_P_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (P n : ℝ) ≤ (1 + δ) * (n * log n) := by
  have h := (nth_prime_asymp.isLittleO.bound hδ)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hv : 0 ≤ (n : ℝ) * log n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact mul_nonneg (by linarith) (log_nonneg this)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hv] at hn
  have := le_abs_self ((P n : ℝ) - n * log n)
  linarith

/-- `π(k) ≤ δ k` for all large `k`. -/
lemma eventually_pi_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (Nat.primeCounting k : ℝ) ≤ δ * k := by
  have hpi : (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) / log n) := by
    have := pi_alt'.comp_tendsto tendsto_natCast_atTop_atTop
    refine this.congr_left (Eventually.of_forall fun n => ?_)
    simp [Function.comp_apply, Nat.floor_natCast]
  have hb := hpi.isLittleO.bound (c := 1) one_pos
  have hlog : ∀ᶠ k : ℕ in atTop, 2 / δ ≤ log k :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hb, hlog, eventually_ge_atTop 2] with k hk hl hk2
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hlogpos : 0 < log (k : ℝ) := log_pos (by linarith)
  have hdiv : (k : ℝ) / log k ≤ δ / 2 * k := by
    rw [div_le_iff₀ hlogpos]
    have h1 : 1 ≤ δ / 2 * log k := by
      have := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ δ / 2)
      rwa [show δ / 2 * (2 / δ) = 1 by field_simp] at this
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ k)]
  have hnn : 0 ≤ (k : ℝ) / log k := div_nonneg (by linarith) hlogpos.le
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnn] at hk
  have := le_abs_self ((Nat.primeCounting k : ℝ) - k / log k)
  linarith

/-- For `1 ≤ n ≤ (1 + δ) k` with `δ ≥ 0` and `k ≥ 3`: `log n ≤ (1 + δ) log k`. -/
lemma log_le_of_le {δ : ℝ} (hδ0 : 0 ≤ δ) {k n : ℝ} (hk : 3 ≤ k) (hn : 1 ≤ n)
    (hnk : n ≤ (1 + δ) * k) : log n ≤ (1 + δ) * log k := by
  have hk1 : 1 ≤ log k := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
  calc log n ≤ log ((1 + δ) * k) := log_le_log (by linarith) hnk
    _ = log (1 + δ) + log k := log_mul (by linarith) (by linarith)
    _ ≤ δ + log k := by linarith [log_le_sub_one_of_pos (show 0 < 1 + δ by linarith)]
    _ ≤ (1 + δ) * log k := by nlinarith

/-! ## Main theorems -/

/--
It is known that $A(k)\leq (1+o(1))k\log k$, by taking the $k$ smallest primes $>k$.
-/
theorem erdos_1204.variants.A_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (A k : ℝ) ≤ (1 + ε) * k * Real.log k := by
  intro ε hε
  set δ := min 1 (ε / 7) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 7 * δ ≤ ε := by have := min_le_right 1 (ε / 7); linarith
  have hidx : Tendsto (fun k : ℕ => Nat.primeCounting k + k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k _) tendsto_id
  filter_upwards [hidx.eventually (eventually_P_le hδ0), eventually_pi_le hδ0,
    eventually_ge_atTop 3] with k hP hpi hk3
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hn1 : (1 : ℝ) ≤ ((Nat.primeCounting k + k : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.primeCounting k + k by omega)
  have hnk : ((Nat.primeCounting k + k : ℕ) : ℝ) ≤ (1 + δ) * k := by
    push_cast; linarith
  have hlog := log_le_of_le hδ0.le hk3' hn1 hnk
  have hlogk : 0 ≤ log (k : ℝ) := log_nonneg (by linarith)
  have hlogn : 0 ≤ log ((Nat.primeCounting k + k : ℕ) : ℝ) := log_nonneg hn1
  have hA : (A k : ℝ) ≤ P (Nat.primeCounting k + k) := by exact_mod_cast A_le_P k
  have h1 : ((Nat.primeCounting k + k : ℕ) : ℝ) * log ((Nat.primeCounting k + k : ℕ) : ℝ) ≤
      ((1 + δ) * k) * ((1 + δ) * log k) :=
    mul_le_mul hnk hlog hlogn (by positivity)
  have hsq : δ * δ ≤ δ := by nlinarith
  have hcb : δ * (δ * δ) ≤ δ := by nlinarith
  have hcube : (1 + δ) * ((1 + δ) * (1 + δ)) ≤ 1 + ε := by
    have : (1 + δ) * ((1 + δ) * (1 + δ)) = 1 + 3 * δ + 3 * (δ * δ) + δ * (δ * δ) := by ring
    rw [this]; linarith
  calc (A k : ℝ) ≤ P (Nat.primeCounting k + k) := hA
    _ ≤ (1 + δ) * (((Nat.primeCounting k + k : ℕ) : ℝ) *
          log ((Nat.primeCounting k + k : ℕ) : ℝ)) := hP
    _ ≤ (1 + δ) * (((1 + δ) * k) * ((1 + δ) * log k)) := by gcongr
    _ = ((1 + δ) * ((1 + δ) * (1 + δ))) * (k * log k) := by ring
    _ ≤ (1 + ε) * (k * log k) := by gcongr
    _ = (1 + ε) * k * Real.log k := by ring

/--
Taking the first $k$ primes which are $>k$ implies $B(k)\leq (1/2+o(1))k\log k$.
-/
theorem erdos_1204.variants.B_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, B k ≤ (1 / 2 + ε) * k * Real.log k := by
  intro ε hε
  set δ := min 1 (ε / 6) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 6 * δ ≤ ε := by have := min_le_right 1 (ε / 6); linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_P_le hδ0)
  filter_upwards [Nat.tendsto_primeCounting.eventually_ge_atTop (N + 1), eventually_pi_le hδ0,
    eventually_ge_atTop 3] with k hπN hpi hk3
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hkpos : (0 : ℝ) < k := by linarith
  set m := Nat.primeCounting k with hm
  have hlogk : 0 ≤ log (k : ℝ) := log_nonneg (by linarith)
  -- each term is at most `(1 + δ) ((1 + δ) log k) (m + i)`
  have hterm : ∀ i ∈ Finset.range k,
      (P (m + i) : ℝ) ≤ (1 + δ) * ((1 + δ) * log k) * ((m : ℝ) + i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hidx1 : (1 : ℝ) ≤ ((m + i : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + i by omega)
    have hle : ((m + i : ℕ) : ℝ) ≤ (1 + δ) * k := by
      push_cast
      have : (i : ℝ) ≤ k := by exact_mod_cast hi.le
      linarith
    have hlog := log_le_of_le hδ0.le hk3' hidx1 hle
    have hP := hN (m + i) (by omega)
    calc (P (m + i) : ℝ) ≤ (1 + δ) * (((m + i : ℕ) : ℝ) * log ((m + i : ℕ) : ℝ)) := hP
      _ ≤ (1 + δ) * (((m + i : ℕ) : ℝ) * ((1 + δ) * log k)) := by gcongr
      _ = (1 + δ) * ((1 + δ) * log k) * ((m : ℝ) + i) := by push_cast; ring
  -- the sum of `i` over `range k` is at most `k^2 / 2`
  have hsumi : (∑ i ∈ Finset.range k, (i : ℝ)) ≤ (k : ℝ) ^ 2 / 2 := by
    have h := Finset.sum_range_id_mul_two k
    have h' : ((∑ i ∈ Finset.range k, i : ℕ) : ℝ) * 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    push_cast at h'
    nlinarith
  have hsum : (minSum k : ℝ) ≤ (1 + δ) * ((1 + δ) * log k) * (k * m + (k : ℝ) ^ 2 / 2) := by
    calc (minSum k : ℝ) ≤ ∑ i ∈ Finset.range k, (P (m + i) : ℝ) := by
          exact_mod_cast minSum_le k
      _ ≤ ∑ i ∈ Finset.range k, (1 + δ) * ((1 + δ) * log k) * ((m : ℝ) + i) :=
          Finset.sum_le_sum hterm
      _ = (1 + δ) * ((1 + δ) * log k) * (k * m + ∑ i ∈ Finset.range k, (i : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
      _ ≤ (1 + δ) * ((1 + δ) * log k) * (k * m + (k : ℝ) ^ 2 / 2) := by
          gcongr
  have hm' : (m : ℝ) ≤ δ * k := hpi
  have hsq : δ * δ ≤ δ := by nlinarith
  have hcb : δ * (δ * δ) ≤ δ := by nlinarith
  have hfac : (1 + δ) * (1 + δ) * (δ + 1 / 2) ≤ 1 / 2 + ε := by
    have : (1 + δ) * (1 + δ) * (δ + 1 / 2) =
        1 / 2 + 2 * δ + 5 / 2 * (δ * δ) + δ * (δ * δ) := by ring
    rw [this]; linarith
  rw [B, div_le_iff₀ hkpos]
  calc (minSum k : ℝ) ≤ (1 + δ) * ((1 + δ) * log k) * (k * m + (k : ℝ) ^ 2 / 2) := hsum
    _ ≤ (1 + δ) * ((1 + δ) * log k) * (k * (δ * k) + (k : ℝ) ^ 2 / 2) := by gcongr
    _ = ((1 + δ) * (1 + δ) * (δ + 1 / 2)) * (k * log k) * k := by ring
    _ ≤ (1 / 2 + ε) * (k * log k) * k := by gcongr
    _ = (1 / 2 + ε) * k * Real.log k * k := by ring

end Erdos1204
