/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort
import VCVio.EvalDist.TVDist

/-!
# Truncation error and Cauchy convergence for Fiat-Shamir with aborts

The deployed FIPS-204-style signing loop is *unbounded*: it retries the
commit-hash-respond cycle until a non-aborting transcript is produced. Such an
unbounded loop is **not** expressible as an `OracleComp`: the free monad on the
oracle signature is the inductive type of *finite* query trees, so every
`OracleComp` performs an a-priori bounded number of queries. The repository
therefore models signing by the fuel-indexed family `fsAbortSignLoop … n` of
bounded loops, each of which is a genuine `OracleComp`.

Faithfulness to the idealised unbounded algorithm is then expressed as
**Cauchy convergence of this family** in total variation distance. The single
controlling quantity is `signLoopAbortProb`, the iteration-independent
probability that one attempt aborts. Adding one unit of fuel perturbs the
output distribution by at most `q ^ n` (`fsAbortSignLoop_tvDist_succ_le`);
telescoping gives the geometric tail bound `q ^ n / (1 - q)` whenever `q < 1`
(`fsAbortSignLoop_tvDist_le_geometric`), which exhibits the family as a Cauchy
sequence converging to the unbounded loop's law.

All statements live in the fresh / uniform random-oracle interpretation, i.e.
under `HasEvalPMF` on `OracleComp (unifSpec + (M × Commit →ₒ Chal))`, where each
random-oracle query is a uniform sample. See `FiatShamir.WithAbort` for the
loop definition and `EvalDist.TVDist` for the total-variation API.
-/

open OracleComp OracleSpec
open scoped BigOperators

namespace FiatShamirWithAbort

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section Truncation

variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (M : Type) [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [(unifSpec + (M × Commit →ₒ Chal)).Fintype]
  [(unifSpec + (M × Commit →ₒ Chal)).Inhabited]
  (pk : Stmt) (sk : Wit) (msg : M)

/-- A single signing attempt, viewed in the uniform random-oracle world.

This is `fsAbortSignAttempt` specialized to the random-oracle interpretation
`OracleComp (unifSpec + (M × Commit →ₒ Chal))`. It returns the commitment
together with either a response or the abort marker `none`. -/
noncomputable def signLoopAttempt :
    OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Commit × Option Resp) :=
  fsAbortSignAttempt ids M pk sk msg

/-- The iteration-independent single-attempt abort probability `q`.

This is the probability that one `signLoopAttempt` aborts (returns `none` in
its response component), as a real number in `[0, 1]`. It is the geometric base
controlling the truncation error of the fuel-indexed loop family. -/
noncomputable def signLoopAbortProb : ℝ :=
  Pr[ (fun x => x.2 = none) | (signLoopAttempt ids M pk sk msg) ].toReal

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal]
  [(unifSpec + (M × Commit →ₒ Chal)).Fintype]
  [(unifSpec + (M × Commit →ₒ Chal)).Inhabited] in
/-- One-step unfolding of the loop as a bind of `signLoopAttempt` with a
continuation that only differs across fuel values inside the abort (`none`)
branch. -/
theorem fsAbortSignLoop_succ_eq (k : ℕ) :
    (fsAbortSignLoop ids M pk sk msg (k + 1) :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
      = (signLoopAttempt ids M pk sk msg) >>= fun x =>
          match x.2 with
          | some z => pure (some (x.1, z))
          | none => fsAbortSignLoop ids M pk sk msg k := by
  rfl

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- **Truncation error of the Fiat-Shamir-with-aborts signing loop.**
Increasing the fuel by one changes the output distribution by at most `q ^ n` in
total variation, where `q = signLoopAbortProb` is the single-attempt abort
probability. -/
theorem fsAbortSignLoop_tvDist_succ_le (n : ℕ) :
    tvDist
      (fsAbortSignLoop ids M pk sk msg (n + 1) :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
      (fsAbortSignLoop ids M pk sk msg n)
      ≤ (signLoopAbortProb ids M pk sk msg) ^ n := by
  induction n with
  | zero =>
    simpa using tvDist_le_one
      (fsAbortSignLoop ids M pk sk msg 1 :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
      (fsAbortSignLoop ids M pk sk msg 0)
  | succ n ih =>
    classical
    set q := signLoopAbortProb ids M pk sk msg with hq
    rw [fsAbortSignLoop_succ_eq ids M pk sk msg (n + 1),
        fsAbortSignLoop_succ_eq ids M pk sk msg n]
    set att := signLoopAttempt ids M pk sk msg with hatt
    set f : (Commit × Option Resp) →
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)) :=
      fun x => match x.2 with
        | some z => pure (some (x.1, z))
        | none => fsAbortSignLoop ids M pk sk msg (n + 1) with hf
    set g : (Commit × Option Resp) →
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)) :=
      fun x => match x.2 with
        | some z => pure (some (x.1, z))
        | none => fsAbortSignLoop ids M pk sk msg n with hg
    refine le_trans (tvDist_bind_left_le att f g) ?_
    -- pointwise: tvDist (f x) (g x) ≤ if x.2 = none then q^n else 0
    have hpt : ∀ x, tvDist (f x) (g x) ≤ (if x.2 = none then q ^ n else 0) := by
      intro x
      simp only [hf, hg]
      match hx : x.2 with
      | some z => simp
      | none => simpa [hx] using ih
    -- summability bookkeeping
    have hp_sum_le : (∑' x : Commit × Option Resp, Pr[= x | att]) ≤ 1 := tsum_probOutput_le_one
    have hp_ne_top : (∑' x : Commit × Option Resp, Pr[= x | att]) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hp_sum_le
    have hp_summable : Summable (fun x : Commit × Option Resp => Pr[= x | att].toReal) :=
      ENNReal.summable_toReal hp_ne_top
    have hL_summable : Summable (fun x => Pr[= x | att].toReal * tvDist (f x) (g x)) :=
      Summable.of_nonneg_of_le
        (fun x => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
        (fun x => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
        hp_summable
    have hI_summable : Summable (fun x : Commit × Option Resp =>
        if x.2 = none then Pr[= x | att].toReal else 0) :=
      Summable.of_nonneg_of_le
        (fun x => by by_cases hx : x.2 = none <;> simp [hx, ENNReal.toReal_nonneg])
        (fun x => by by_cases hx : x.2 = none <;> simp [hx, ENNReal.toReal_nonneg])
        hp_summable
    have hR_summable : Summable (fun x : Commit × Option Resp =>
        q ^ n * (if x.2 = none then Pr[= x | att].toReal else 0)) :=
      hI_summable.mul_left _
    -- pointwise real bound, weighted by the output probability
    have hpt' : ∀ x, Pr[= x | att].toReal * tvDist (f x) (g x)
        ≤ q ^ n * (if x.2 = none then Pr[= x | att].toReal else 0) := by
      intro x
      calc Pr[= x | att].toReal * tvDist (f x) (g x)
          ≤ Pr[= x | att].toReal * (if x.2 = none then q ^ n else 0) :=
            mul_le_mul_of_nonneg_left (hpt x) ENNReal.toReal_nonneg
        _ = q ^ n * (if x.2 = none then Pr[= x | att].toReal else 0) := by
            by_cases hx : x.2 = none <;> simp [hx, mul_comm]
    -- ∑' over the abort branch recovers the abort probability `q`
    have hevent : (∑' x : Commit × Option Resp,
        if x.2 = none then Pr[= x | att].toReal else 0)
        = Pr[ (fun x => x.2 = none) | att].toReal := by
      have hterm : ∀ x : Commit × Option Resp,
          (if x.2 = none then Pr[= x | att] else 0) ≠ ⊤ := by
        intro x; by_cases hx : x.2 = none
        · simp [hx, ne_top_of_le_ne_top ENNReal.one_ne_top
            (probOutput_le_one (mx := att) (x := x))]
        · simp [hx]
      rw [probEvent_eq_tsum_ite, ENNReal.tsum_toReal_eq hterm]
      refine tsum_congr fun x => ?_
      by_cases hx : x.2 = none <;> simp [hx]
    have hqval : Pr[ (fun x => x.2 = none) | att].toReal = q := by rw [hatt, hq]; rfl
    calc (∑' x, Pr[= x | att].toReal * tvDist (f x) (g x))
        ≤ ∑' x, q ^ n * (if x.2 = none then Pr[= x | att].toReal else 0) :=
          Summable.tsum_le_tsum hpt' hL_summable hR_summable
      _ = q ^ n * ∑' x, (if x.2 = none then Pr[= x | att].toReal else 0) := tsum_mul_left
      _ = q ^ n * Pr[ (fun x => x.2 = none) | att].toReal := by rw [hevent]
      _ = q ^ n * q := by rw [hqval]
      _ = q ^ (n + 1) := (pow_succ q n).symm

/-! ## Telescoping and geometric convergence

The one-step bound `fsAbortSignLoop_tvDist_succ_le` telescopes along the fuel
parameter, exhibiting the bounded-loop family as a Cauchy sequence in total
variation distance. -/

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- **Telescoping truncation bound.** For `n ≤ m`, the total-variation gap
between the `m`-fuel and `n`-fuel signing loops is at most the partial geometric
sum `∑_{j ∈ [n, m)} q ^ j`, where `q = signLoopAbortProb`. Proved by induction on
`m` via the triangle inequality and the one-step bound. -/
theorem fsAbortSignLoop_tvDist_le_sum_Ico {n m : ℕ} (hnm : n ≤ m) :
    tvDist
      (fsAbortSignLoop ids M pk sk msg m :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
      (fsAbortSignLoop ids M pk sk msg n)
      ≤ ∑ j ∈ Finset.Ico n m, (signLoopAbortProb ids M pk sk msg) ^ j := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := Nat.le_zero.mp hnm
    simp [tvDist_self]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · -- n ≤ m, so we can split off the top term q^m
      have hnm' : n ≤ m := Nat.lt_succ_iff.mp hlt
      refine le_trans (tvDist_triangle
        (fsAbortSignLoop ids M pk sk msg (m + 1) :
          OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
        (fsAbortSignLoop ids M pk sk msg m)
        (fsAbortSignLoop ids M pk sk msg n)) ?_
      rw [Finset.sum_Ico_succ_top hnm',
        add_comm (∑ j ∈ Finset.Ico n m, (signLoopAbortProb ids M pk sk msg) ^ j)]
      exact add_le_add (fsAbortSignLoop_tvDist_succ_le ids M pk sk msg m) (ih hnm')
    · -- n = m + 1, both loops are identical
      obtain rfl : n = m + 1 := le_antisymm hnm hge
      simp [tvDist_self]

omit [DecidableEq M] [DecidableEq Commit] [SampleableType Chal] in
/-- **Geometric (Cauchy) truncation bound.** When the single-attempt abort
probability satisfies `q < 1`, the bounded signing loops form a Cauchy sequence:
for `n ≤ m`, their total-variation gap is at most the geometric tail
`q ^ n / (1 - q)`. This converges to `0` as `n → ∞`, so the fuel-indexed family
converges to the law of the idealised unbounded loop. -/
theorem fsAbortSignLoop_tvDist_le_geometric
    (hq : signLoopAbortProb ids M pk sk msg < 1) {n m : ℕ} (hnm : n ≤ m) :
    tvDist
      (fsAbortSignLoop ids M pk sk msg m :
        OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Option (Commit × Resp)))
      (fsAbortSignLoop ids M pk sk msg n)
      ≤ (signLoopAbortProb ids M pk sk msg) ^ n / (1 - signLoopAbortProb ids M pk sk msg) := by
  set q := signLoopAbortProb ids M pk sk msg with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef, signLoopAbortProb]; exact ENNReal.toReal_nonneg
  refine le_trans (fsAbortSignLoop_tvDist_le_sum_Ico ids M pk sk msg hnm) ?_
  -- reindex the partial sum: ∑_{j ∈ [n,m)} q^j = q^n * ∑_{i ∈ range (m-n)} q^i
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [pow_add]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 n)
  -- ∑_{i ∈ range k} q^i ≤ ∑' i, q^i = (1 - q)⁻¹
  have hsummable : Summable (fun i : ℕ => q ^ i) := summable_geometric_of_lt_one hq0 hq
  refine le_trans (Summable.sum_le_tsum _ (fun i _ => pow_nonneg hq0 i) hsummable) ?_
  rw [tsum_geometric_of_lt_one hq0 hq]

end Truncation

end FiatShamirWithAbort
