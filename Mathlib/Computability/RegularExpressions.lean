/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Anthony DeRossi
-/
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.Language
import Mathlib.Computability.NFA
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Linarith
import Lean.Elab.Command

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent. -/

-- Porting note: this has been commented out
-- * `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.



open List Set

open Computability

universe u

variable {α β γ : Type*}

/-- This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α → RegularExpression α
  | plus : RegularExpression α → RegularExpression α → RegularExpression α
  | comp : RegularExpression α → RegularExpression α → RegularExpression α
  | star : RegularExpression α → RegularExpression α


-- Porting note: `simpNF` gets grumpy about how the `foo_def`s below can simplify these..
attribute [nolint simpNF] RegularExpression.zero.sizeOf_spec
attribute [nolint simpNF] RegularExpression.epsilon.sizeOf_spec
attribute [nolint simpNF] RegularExpression.plus.sizeOf_spec
attribute [nolint simpNF] RegularExpression.plus.injEq
attribute [nolint simpNF] RegularExpression.comp.injEq
attribute [nolint simpNF] RegularExpression.comp.sizeOf_spec

namespace RegularExpression

variable {a b : α}

instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩

instance : Add (RegularExpression α) :=
  ⟨plus⟩

instance : Mul (RegularExpression α) :=
  ⟨comp⟩

instance : One (RegularExpression α) :=
  ⟨epsilon⟩

instance : Zero (RegularExpression α) :=
  ⟨zero⟩

instance : Pow (RegularExpression α) ℕ :=
  ⟨fun n r => npowRec r n⟩

-- Porting note: declaration in an imported module
--attribute [match_pattern] Mul.mul

@[simp]
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl

@[simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl

-- Porting note: `matches` is reserved, moved to `matches'`
#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `matches' P` provides a language which contains all strings that `P` matches -/
-- Porting note: was '@[simp] but removed based on
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simpNF.20issues.20in.20Computability.2ERegularExpressions.20!4.232306/near/328355362
def matches' : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | comp P Q => P.matches' * Q.matches'
  | star P => P.matches'∗

@[simp]
theorem matches'_zero : (0 : RegularExpression α).matches' = 0 :=
  rfl

@[simp]
theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 :=
  rfl

@[simp]
theorem matches'_char (a : α) : (char a).matches' = {[a]} :=
  rfl

@[simp]
theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl

@[simp]
theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
theorem matches'_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).matches' = P.matches' ^ n
  | 0 => matches'_epsilon
  | n + 1 => (matches'_mul _ _).trans <| Eq.trans
      (congrFun (congrArg HMul.hMul (matches'_pow P n)) (matches' P))
      (pow_succ _ n).symm

@[simp]
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `matchEpsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | comp P Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

section DecidableEq
variable [DecidableEq α]

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | comp P Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[simp]
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl

@[simp]
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl

@[simp]
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  if_pos rfl

@[simp]
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 :=
  if_neg h

@[simp]
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[simp]
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches'`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

@[simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x <;> simp [rmatch, matchEpsilon, *]

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, matchEpsilon, *]

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  cases' x with _ x
  · exact of_decide_eq_true rfl
  cases' x with head tail
  · rw [rmatch, deriv]
    split_ifs
    · tauto
    · simp [List.singleton_inj]; tauto
  · rw [rmatch, rmatch, deriv]
    split_ifs with h
    · simp only [deriv_one, zero_rmatch, cons.injEq, and_false, reduceCtorEq]
    · simp only [deriv_zero, zero_rmatch, cons.injEq, and_false, reduceCtorEq]

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction x generalizing P Q with
  | nil => simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    repeat rw [rmatch]
    rw [deriv_add]
    exact ih _ _

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction' x with a x ih generalizing P Q
  · rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch, rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      cases' List.append_eq_nil.1 h₁.symm with ht hu
      subst ht
      subst hu
      repeat rw [rmatch] at h₂
      simp [h₂]
  · rw [rmatch]; simp only [deriv]
    split_ifs with hepsilon
    · rw [add_rmatch_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact ⟨a :: t, u, by tauto⟩
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
      · rintro ⟨t, u, h, hP, hQ⟩
        cases' t with b t
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
        · left
          rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · cases' t with b t
        · contradiction
        · rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x
          = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · cases' x with a x
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          omega
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch, reduceCtorEq]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      cases' x with a x
      · rfl
      · rw [rmatch, deriv, mul_rmatch_iff]
        cases' S with t' U
        · exact ⟨[], [], by tauto⟩
        · cases' t' with b t
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [eq_self_iff_true, not_true, Ne, false_and] at helem
          simp only [List.join, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.join, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert helem.2
            exact hsum.1
          · have hwf : U.join.length < (List.cons a x).length := by
              rw [hsum.1, hsum.2]
              simp only [List.length_append, List.length_join, List.length]
              omega
            rw [IH _ hwf]
            refine ⟨U, rfl, fun t h => helem t ?_⟩
            right
            assumption
  termination_by t => (P, t.length)

@[simp]
theorem rmatch_iff_matches' (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x ∈ P.matches' := by
  induction P generalizing x with
  | zero =>
    rw [zero_def, zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def, one_rmatch_iff, matches'_epsilon, Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def, add_rmatch_iff, ih₁, ih₂]
    rfl
  | comp P Q ih₁ ih₂ =>
    simp only [comp_def, mul_rmatch_iff, matches'_mul, Language.mem_mul, *]
    tauto
  | star _ ih =>
    simp only [star_rmatch_iff, matches'_star, ih, Language.mem_kstar_iff_exists_nonempty, and_comm]

instance (P : RegularExpression α) : DecidablePred (· ∈ P.matches') := fun _ ↦
  decidable_of_iff _ (rmatch_iff_matches' _ _)

end DecidableEq

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | comp R S => map f R * map f S
  | star R => star (map f R)

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) :
    ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => by dsimp; rfl
  | n + 1 => (congr_arg (· * map f P) (RegularExpression.map_pow f P n) : _)

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp_rw [map, map_id]
  | comp R S => by simp_rw [map, map_id]; rfl
  | star R => by simp_rw [map, map_id]

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp P Q`, instead of `x * y`. -/
@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char a => rfl
  | R + S => by simp only [map, Function.comp_apply, map_map]
  | comp R S => by simp only [map, Function.comp_apply, map_map]
  | star R => by simp only [map, Function.comp_apply, map_map]

#adaptation_note /-- around nightly-2024-02-25,
  we need to write `comp x y` in the pattern `comp R S`,
  instead of `x * y` (and the `erw` was just `rw`). -/
/-- The language of the map is the map of the language. -/
@[simp]
theorem matches'_map (f : α → β) :
    ∀ P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  -- Porting note: the following close with last `rw` but not with `simp`?
  | R + S => by simp only [matches'_map, map, matches'_add]; rw [map_add]
  | comp R S => by simp only [matches'_map, map, matches'_mul]; erw [map_mul]
  | star R => by
    simp_rw [map, matches', matches'_map]
    rw [Language.kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow]
    simp_rw [← map_pow]
    exact image_iUnion.symm

@[simp]
def pumping_const : RegularExpression α → ℕ
  | 0 => 1
  | 1 => 1
  | char _ => 2
  | P + Q => P.pumping_const + Q.pumping_const
  | comp P Q => P.pumping_const + Q.pumping_const
  | star P => P.pumping_const

theorem pumping_const_ge_1 (P : RegularExpression α) : P.pumping_const >= 1 := by
  induction P <;> rw [pumping_const] <;> linarith

-- An argument-swapped version of Eq.subst
private theorem subst' {r : α → Prop} {a b : α} (h : r a) (heq : a = b) : r b :=
  heq ▸ h

private theorem lang_le_mem (L₁ L₂ : Language α) (a : List α) : L₁ ≤ L₂ → a ∈ L₁ → a ∈ L₂ :=
  fun a b ↦ a b

private theorem lang_mul_kstar_le_kstar (L : Language α) (a : List α) : a ∈ L * L∗ → a ∈ L∗ := by
  apply lang_le_mem
  exact mul_kstar_le_kstar

theorem nonempty_mem_star_eq_append (L : Language α) (x : List α)
    (hx : x ∈ L∗) (hne : x ≠ []) :
    ∃ x₁ x₂, x = x₁ ++ x₂ ∧ x₁ ∈ L ∧ x₂ ∈ L∗ := by
  rw [← Language.one_add_self_mul_kstar_eq_kstar] at hx
  obtain _ | ⟨a, _, b, _, _⟩ := hx
  · contradiction
  · tauto

theorem replicate_append_mem_star (L : Language α) (x₁ x₂ : List α) (m : ℕ)
    (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L∗) :
    (replicate m x₁).join ++ x₂ ∈ L∗ := by
  induction m with
  | zero => simpa
  | succ m' ih =>
    rw [replicate_succ, join_cons, append_assoc]
    apply lang_mul_kstar_le_kstar
    apply Language.append_mem_mul <;> assumption

/-- A tactic to discharge cases of the pumping lemma --/
syntax "pump_auto" : tactic
macro_rules
| `(tactic| pump_auto) => `(tactic| (
  split_ands
  · -- x = a ++ b ++ c
    try rw [join_cons]
    first | assumption | ac_rfl
  · -- a.length + b.length ≤ P.pumping_const
    simp only [matches', pumping_const, length_append, length_nil, zero_add] at *
    linarith
  · -- b ≠ []
    assumption
  -- ∀ m, a ++ (replicate m b).join ++ c ∈ P.matches'
  focus try tauto
  ))

theorem pumping_lemma (P : RegularExpression α) (x : List α)
    (hx : x ∈ P.matches') (hlen : P.pumping_const ≤ x.length) :
    ∃ a b c,
      x = a ++ b ++ c ∧
      a.length + b.length ≤ P.pumping_const ∧
      b ≠ [] ∧
      ∀ m, a ++ (replicate m b).join ++ c ∈ P.matches' := by
  induction P generalizing x with
  | zero =>
    contradiction
  | epsilon
  | char _ =>
    cases hx
    contradiction
  | plus P Q ihP ihQ =>
    obtain hxP | hxQ := hx <;> [
      have ⟨a, b, c, _, _, _, _⟩ := ihP x hxP (Nat.le_of_add_right_le hlen);
      have ⟨a, b, c, _, _, _, _⟩ := ihQ x hxQ (le_of_add_le_right hlen)
      ] <;>
    · use a, b, c
      pump_auto
  | comp P Q ihP ihQ =>
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
    by_cases hlen₁ : P.pumping_const ≤ x₁.length
    · obtain ⟨a, b, c, rfl, _, _, ihm⟩ := ihP x₁ hx₁ hlen₁
      use a, b, c ++ x₂
      pump_auto
      · intro m
        apply subst'
        · exact Language.append_mem_mul (ihm m) hx₂
        · ac_rfl
    · rw [length_append] at hlen
      obtain _ | hlen₂ := le_or_le_of_add_le_add hlen; contradiction
      obtain ⟨a, b, c, rfl, _, _, ihm⟩ := ihQ x₂ hx₂ hlen₂
      use x₁ ++ a, b, c
      pump_auto
      · intro m
        apply subst'
        · exact Language.append_mem_mul hx₁ (ihm m)
        · ac_rfl
  | star P ih =>
    have hne : x ≠ [] := by
      rintro rfl
      rw [pumping_const, length_nil] at hlen
      have := pumping_const_ge_1 P
      linarith
    obtain ⟨x₁, x₂, rfl, hx₁, hx₂⟩ := nonempty_mem_star_eq_append _ x hx hne
    match le_or_gt P.pumping_const x₁.length with
    | Or.inl hp =>
      obtain ⟨a, b, c, rfl, _, _, ihm⟩ := ih x₁ hx₁ hp
      use a, b, c ++ x₂
      pump_auto
      · intro m
        apply lang_mul_kstar_le_kstar
        apply subst'
        · exact Language.append_mem_mul (ihm m) hx₂
        · ac_rfl
    | Or.inr _ =>
      by_cases x₁ = []
      · subst x₁
        cases P with
        | epsilon =>
          simp only [matches', nil_append, kstar_one] at hx
          subst x₂
          contradiction
        | zero
        | char =>
          contradiction
        | plus P' Q
        | comp P' Q =>
          obtain ⟨S, rfl, hS⟩ := Language.mem_kstar_iff_exists_nonempty.mp hx₂
          obtain _ | ⟨s, t⟩ := S; contradiction
          have ⟨hs, _⟩ := hS s (by simp)
          have ⟨ht, _⟩ := forall₂_and.mp (forall_mem_cons.mp hS).2
          cases le_or_gt (P'.pumping_const + Q.pumping_const) s.length with
          | inl hlen =>
            obtain ⟨a, b, c, rfl, _, _, ihm⟩ := ih s hs hlen
            use a, b, c ++ t.join
            pump_auto
            · intro m
              apply lang_mul_kstar_le_kstar
              apply subst'
              · exact Language.append_mem_mul (ihm m) (Language.join_mem_kstar ht)
              · ac_rfl
          | inr _ =>
            use [], s, t.join
            pump_auto
            · intro
              apply replicate_append_mem_star
              · exact hs
              · exact Language.join_mem_kstar ht
        | star P' =>
          simp only [matches', pumping_const, length_nil, append_assoc, nil_append, kstar_idem] at *
          exact ih x₂ hx₂ hlen
      · use [], x₁, x₂
        pump_auto
        · intro
          apply replicate_append_mem_star <;> assumption

/-! ## Thompson's construction for regular expressions -/

open εNFA

variable {σ σ₁ σ₂: Type*}

/-! ### Definitions -/

/-- The `εNFA` for `zero` has no transitions. -/
def zero_step : Unit → Option α → Set Unit
  | _, _ => ∅
def zero_start : Set Unit := ∅
def zero_accept : Set Unit := ∅

/-- The `εNFA` for `epsilon` only has an ε-transition from the starting state to the accepting
  state. -/
def epsilon_step : Option Unit → Option α → Set (Option Unit)
  | none, none => {some ()}
  | _, _ => ∅
def epsilon_start : Set (Option Unit) := {none}
def epsilon_accept : Set (Option Unit) := {some ()}

/-- The `εNFA` for `char a` only has an `a`-labeled transition from the starting state to the
  accepting state. -/
def char_step [DecidableEq α] (a : α) : Option Unit → Option α → Set (Option Unit)
  | none, some b => {s | s = some () ∧ a = b}
  | _, _ => ∅
def char_start : Set (Option Unit) := {none}
def char_accept : Set (Option Unit) := {some ()}

/-- The `εNFA` for `plus P Q` is constructed using a sum type to embed left (from the `εNFA` for
  `P`) and right (from the `εNFA` for `Q`) states and transitions. It has separate starting and
  accepting states, with ε-transitions from the starting state to the embedded left and right
  starting states, and from the embedded left and right accepting states to the accepting state. -/
def plus_step (MP : εNFA α σ₁) (MQ : εNFA α σ₂) :
    Option Unit ⊕ σ₁ ⊕ σ₂ → Option α → Set (Option Unit ⊕ σ₁ ⊕ σ₂)
  | Sum.inl none, none => Sum.inr '' Sum.elim MP.start MQ.start
  | Sum.inr (Sum.inl s'), a => Sum.inr ∘ Sum.inl '' MP.step s' a
      ∪ {s | s = Sum.inl (some ()) ∧ a = none ∧ s' ∈ MP.accept}
  | Sum.inr (Sum.inr s'), a => Sum.inr ∘ Sum.inr '' MQ.step s' a
      ∪ {s | s = Sum.inl (some ()) ∧ a = none ∧ s' ∈ MQ.accept}
  | _, _ => ∅
def plus_start : Set (Option Unit ⊕ σ₁ ⊕ σ₂) := {Sum.inl none}
def plus_accept : Set (Option Unit ⊕ σ₁ ⊕ σ₂) := {Sum.inl (some ())}

/-- The `εNFA` for `comp P Q` is constructed using a sum type to embed left (from the `εNFA` for
  `P`) and right (from the `εNFA` for `Q`) states and transitions. Unlike `plus P Q`, the starting
  and accepting states are the embedded left starting and right accepting states respectively. An
  ε-transition exists between the embedded left accepting and right starting states. -/
def comp_step (MP : εNFA α σ₁) (MQ : εNFA α σ₂) :
    σ₁ ⊕ σ₂ → Option α → Set (σ₁ ⊕ σ₂)
  | Sum.inl s', a => Sum.inl '' MP.step s' a
      ∪ {s | s ∈ Sum.inr '' MQ.start ∧ a = none ∧ s' ∈ MP.accept}
  | Sum.inr s', a => Sum.inr '' MQ.step s' a
def comp_start (MP : εNFA α σ₁) : Set (σ₁ ⊕ σ₂) := Sum.inl '' MP.start
def comp_accept (MQ : εNFA α σ₂) : Set (σ₁ ⊕ σ₂) := Sum.inr '' MQ.accept

/-- The `εNFA` for `star P` is constructed using a sum type to embed the `εNFA` for `P`, with
  ε-transitions from the starting and accepting states to the respective embedded states. Additional
  ε-transitions exist between the starting and accepting state (empty matching), and between the
  embedded final and starting states (repeating). -/
def star_step (MP : εNFA α σ) :
    Option Unit ⊕ σ → Option α → Set (Option Unit ⊕ σ)
  | Sum.inl none, none => Sum.inr '' MP.start ∪ {Sum.inl (some ())}
  | Sum.inr s', a => Sum.inr '' MP.step s' a
      ∪ {s | s ∈ {Sum.inl (some ())} ∪ Sum.inr '' MP.start ∧ a = none ∧ s' ∈ MP.accept}
  | _, _ => ∅
def star_start : Set (Option Unit ⊕ σ) := {Sum.inl none}
def star_accept : Set (Option Unit ⊕ σ) := {Sum.inl (some ())}

/-- `P.St` is the node type for the `εNFA` constructed by `P.toεNFA` -/
def St : RegularExpression α → Type
  | 0 => Unit
  | 1 => Option Unit
  | char _ => Option Unit
  | P + Q => Option Unit ⊕ St P ⊕ St Q
  | comp P Q => St P ⊕ St Q
  | star P => Option Unit ⊕ St P

/-- An `εNFA` constructed from a `RegularExpression` -/
def toεNFA [DecidableEq α] : (P : RegularExpression α) → εNFA α P.St
  | 0 =>
    ⟨zero_step, zero_start, zero_accept⟩
  | 1 =>
    ⟨epsilon_step, epsilon_start, epsilon_accept⟩
  | char a =>
    ⟨char_step a, char_start, char_accept⟩
  | P + Q =>
    ⟨plus_step P.toεNFA Q.toεNFA, plus_start, plus_accept⟩
  | comp P Q =>
    ⟨comp_step P.toεNFA Q.toεNFA, comp_start P.toεNFA, comp_accept Q.toεNFA⟩
  | star P =>
    ⟨star_step P.toεNFA, star_start, star_accept⟩

open Lean.Parser.Tactic

/-- A simplification tactic for expressions involving `Sum` + basic logic/set relations -/
syntax "simp_sum" (location)? : tactic
macro_rules
| `(tactic| simp_sum $[at $location]?) => `(tactic| simp only [and_false, Function.comp_apply,
  exists_eq_right, exists_false, false_and, false_or, Sum.inl.injEq, Sum.inr.injEq, mem_image,
  mem_inter_iff, mem_setOf_eq, mem_singleton_iff, mem_union, not_false_eq_true, or_false, or_self,
  reduceCtorEq, setOf_and, setOf_eq_eq_singleton, setOf_false, true_and, union_empty]
    $[at $location]?)

/-! ### Lemmas for `zero` -/

/-- Correctness of `zero.toεNFA` -/
theorem toεNFA_zero [DecidableEq α] : zero.toεNFA.accepts = (0 : Language α) := by
  simp only [accepts, toεNFA, zero_accept, exists_false, false_and, mem_empty_iff_false,
    setOf_false, zero_def]
  rfl

/-! ### Lemmas for `epsilon` -/

/-- The ε-closure for the starting state of `epsilon` contains all states. -/
theorem εClosure_epsilon [DecidableEq α] {M : εNFA α _} (hM : M = epsilon.toεNFA) :
    M.εClosure M.start = univ := by
  subst M
  simp only [toεNFA, epsilon_accept, epsilon_start, one_def]
  ext s
  constructor <;> intro _
  · trivial
  · cases s
    · apply εClosure.base
      · simp only [mem_singleton_iff]
    · apply εClosure.step none
      · simp only [epsilon_step, mem_singleton_iff]
      · apply εClosure.base
        simp only [mem_singleton_iff]

/-- `epsilon` accepts the empty string. -/
theorem eval_epsilon [DecidableEq α] {M : εNFA α _} (hM : M = epsilon.toεNFA) :
    (M.accept ∩ M.eval ([] : List α)).Nonempty := by
  subst M
  rw [eval_nil, εClosure_epsilon (by rfl)]
  simp only [toεNFA, epsilon_accept, inter_univ, one_def, singleton_nonempty]

/-- `eval` inversion for `epsilon`--if `eval` accepts a string, the string must be empty. -/
theorem eval_epsilon_inv [DecidableEq α] {M : εNFA α _} (hM : M = epsilon.toεNFA) (x : List α) :
    (M.accept ∩ M.eval x).Nonempty -> x = [] := by
  subst M
  intro h
  apply inter_nonempty.mp at h
  obtain ⟨_, _, h⟩ := h
  cases x using List.reverseRecOn
  · rfl
  · simp only [eval, evalFrom, toεNFA, epsilon_step, and_false, εClosure_empty, exists_false,
      foldl_append, foldl_cons, foldl_nil, mem_empty_iff_false, mem_stepSet_iff, one_def] at h

/-- Correctness of `epsilon.toεNFA` -/
theorem toεNFA_epsilon [DecidableEq α] : epsilon.toεNFA.accepts = (1 : Language α) := by
  simp only [accepts]
  apply Subset.antisymm
  · apply eval_epsilon_inv (by rfl)
  · intro x hx
    apply (Language.mem_one _).mp at hx
    rw [mem_setOf_eq, hx]
    apply inter_nonempty.mp
    apply eval_epsilon (by rfl)

/-! ### Lemmas for `char` -/

/-- `char a` has no ε-transitions. -/
theorem εClosure_char [DecidableEq α] {M : εNFA α _} (a : α) (hM : M = (char a).toεNFA)
    (S : Set (char α).St) :
    M.εClosure S = S := by
  subst M
  apply Subset.antisymm
  · intro s hs
    cases hs
    · assumption
    · simp only [toεNFA, char_step, mem_empty_iff_false] at *
  · apply subset_εClosure

/-- `char a` accepts `[a]`. This is a stronger statement (`eval` is the accepting set) to simplify
  later lemmas. -/
theorem eval_char_singleton_eq [DecidableEq α] {M : εNFA α _} (a : α) (hM : M = (char a).toεNFA) :
    M.eval [a] = M.accept := by
  subst M
  simp only [toεNFA, char_accept, char_start, char_step] at *
  apply Subset.antisymm
  · intro s hs
    rw [eval_singleton, mem_stepSet_iff] at hs
    obtain ⟨t, ht, hs⟩ := hs
    rw [εClosure_char _ (by rfl)] at *
    subst t
    cases hs
    subst s
    rfl
  · intro s hs
    rw [eval_singleton, mem_stepSet_iff]
    use none
    constructor <;> rw [εClosure_char _ (by rfl)]
    · rfl
    · simp only [char_step, and_true, mem_singleton_iff, setOf_eq_eq_singleton]
      subst s
      rfl

/-- `char a` does not accept `[b]` where `a ≠ b`. This is a stronger statement (`eval` is the empty
  set) to simplify later lemmas. -/
theorem eval_char_singleton_ne [DecidableEq α] {M : εNFA α _} (a b : α) (hM : M = (char a).toεNFA) :
    a ≠ b → M.eval [b] = ∅ := by
  subst M
  intro h
  rw [eval_singleton, εClosure_char _ (by rfl)]
  simp only [stepSet, iUnion_eq_empty]
  intro s hs
  rw [εClosure_char _ (by rfl)]
  simp only [step, toεNFA, char_step]
  cases s
  · simp only [h, and_false, setOf_false]
  · rfl

/-- The `stepSet` for `char a` is either an accepting state or empty. -/
theorem stepSet_char_subset_accept [DecidableEq α] {M : εNFA α _} (a b : α)
    (hM : M = (char a).toεNFA) (S : Set (char a).St) :
    M.stepSet S b ⊆ M.accept := by
  subst M
  intro s hs
  rw [mem_stepSet_iff] at hs
  obtain ⟨t, _, hs⟩ := hs
  rw [εClosure_char _ (by rfl)] at hs
  simp only [step, toεNFA, char_step] at hs
  cases t
  · rw [mem_setOf_eq] at hs
    rw [hs.1]
    rfl
  · simp only [mem_empty_iff_false] at hs

/-- `evalFrom` for `char a` makes no progress from an accepting state with a non-empty string. -/
theorem evalFrom_char_accept_nonempty_empty [DecidableEq α] {M : εNFA α _} (a : α)
    (hM : M = (char a).toεNFA) (x : List α) (b : α) :
    M.evalFrom M.accept (x ++ [b]) = ∅ := by
  subst M
  rw [evalFrom]
  induction' x using List.reverseRecOn with x c ih generalizing b
  · simp only [foldl_cons, foldl_nil, nil_append]
    apply subset_empty_iff.mp
    intro s hs
    simp only [toεNFA, mem_stepSet_iff] at hs
    obtain ⟨t, ht, hs⟩ := hs
    rw [εClosure_char _ (by rfl)] at *
    simp only [char_accept] at ht
    subst t
    simp only [char_step] at hs
    contradiction
  · simp only [ih c, foldl_append, foldl_cons, foldl_nil, stepSet_empty]

/-- `eval` inversion for `char a`--if `eval` accepts a string, the string must be `[a]`. -/
theorem eval_char_inv [DecidableEq α] {M : εNFA α _} (a : α) (hM : M = (char a).toεNFA)
    (x : List α) :
    (M.accept ∩ M.eval x).Nonempty → x = [a] := by
  rw [eval, evalFrom, εClosure_char _ hM]
  cases' x with x xs
  · simp only [foldl_nil, imp_false, ne_cons_self]
    convert Set.not_nonempty_empty
    subst M
    simp only [toεNFA, char_accept, char_start, inter_singleton_eq_empty, mem_singleton_iff,
      not_false_eq_true, reduceCtorEq]
  · by_cases heq : a = x
    · subst x
      intro h
      have he := eval_char_singleton_eq a hM
      simp only [eval, evalFrom, foldl_cons, foldl_nil, εClosure_char _ hM] at he
      simp only [foldl_cons, he] at h
      simp only [cons.injEq, true_and]
      cases' xs using List.reverseRecOn with x b
      · rfl
      · have he := evalFrom_char_accept_nonempty_empty _ hM x b
        simp only [evalFrom, εClosure_char _ hM] at he
        rw [he, inter_empty] at h
        apply Set.not_nonempty_empty at h
        contradiction
    · intro h
      apply eval_char_singleton_ne a x hM at heq
      rw [eval_singleton, εClosure_char _ hM] at heq
      rw [foldl_cons, heq] at h
      have he := M.evalFrom_empty xs
      rw [evalFrom, εClosure_empty] at he
      rw [he, inter_empty] at h
      apply Set.not_nonempty_empty at h
      contradiction

/-- Correctness of `(char a).toεNFA` -/
theorem toεNFA_char [DecidableEq α] {M : εNFA α _} (a : α) (hM : M = (char a).toεNFA) :
    M.accepts = ({[a]} : Language α) := by
  subst M
  apply Set.Subset.antisymm
  · apply Set.setOf_subset.mpr
    intro _ hx
    apply eval_char_inv a (by rfl) _ at hx
    trivial
  · intro x hx
    apply Set.eq_of_mem_singleton at hx
    subst x
    rw [accepts, mem_setOf_eq, eval_char_singleton_eq _ (by rfl)]
    use some ()
    trivial

/-! ### Lemmas for `plus` -/

/-- The ε-closure of starting states of the `εNFA` for `plus P Q` contains the starting states of
  the left `εNFA`. -/
theorem εClosure_plus_start_subset_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA) :
    Sum.inr ∘ Sum.inl '' MP.start ⊆ M.εClosure M.start := by
  subst M MP
  intro s hs
  apply εClosure.step (Sum.inl none)
  · simp only [toεNFA, plus_step, Sum.exists, mem_image]
    left
    obtain ⟨t, _, _⟩ := hs
    use t
    trivial
  · apply εClosure.base; rfl

/-- The ε-closure of starting states of the `εNFA` for `plus P Q` contains the starting states of
  the right `εNFA`. -/
theorem εClosure_plus_start_subset_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA) :
    Sum.inr ∘ Sum.inr '' MQ.start ⊆ M.εClosure M.start := by
  subst M MQ
  intro s hs
  apply εClosure.step (Sum.inl none)
  · simp only [toεNFA, plus_step, Sum.exists, mem_image]
    right
    obtain ⟨t, _, _⟩ := hs
    use t
    trivial
  · apply εClosure.base; rfl

/-- No ε-transition from a non-starting state in the `εNFA` for `plus P Q` can lead back to a
  starting state. -/
theorem step_plus_no_restart [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s t : (P + Q).St) :
    s ∈ M.start → t ∉ M.start → s ∉ M.step t none := by
  subst M
  simp only [toεNFA, plus_start, plus_step]
  intro h hn hc
  subst s
  rcases t with t | t
  · cases t <;> simp_sum at hc; contradiction
  · cases t <;> simp_sum at hc <;> obtain _ | _ := hc

/-- No ε-closure under the `εNFA` for `plus P Q` contains the starting state unless the starting
  state is in the state set. -/
theorem εClosure_plus_no_restart [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : (P + Q).St) (S : Set (P + Q).St) :
    s ∈ M.start → s ∉ S → s ∉ M.εClosure S := by
  subst M
  intro h hn hc
  cases' hc with _ _ t s hs
  · contradiction
  · simp only [toεNFA, plus_start, mem_singleton_iff] at h
    simp only [toεNFA, plus_step] at hs
    subst s
    rcases t with t | t
    · cases t <;> simp_sum at hs; contradiction
    · cases t <;> simp_sum at hs <;> obtain _ | _ := hs

/-- The ε-closure of any state set in the left `εNFA` is a subset of the ε-closure for the
  corresponding state set in the `εNFA` for `plus P Q`. -/
theorem εClosure_plus_subset_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set P.St) :
    Sum.inr ∘ Sum.inl '' MP.εClosure S ⊆ M.εClosure (Sum.inr ∘ Sum.inl '' S) := by
  intro s hs
  rw [mem_image] at hs
  obtain ⟨t, ht, _⟩ := hs
  induction' ht with _ _ t _ _ _ ih generalizing s
  · apply εClosure.base; tauto
  · subst M MP s
    apply εClosure.step (Sum.inr (Sum.inl t))
    · simp only [toεNFA, plus_step, mem_setOf_eq]
      left
      tauto
    · apply ih (by rfl)

/-- The ε-closure of any state set in the right `εNFA` is a subset of the ε-closure for the
  corresponding state set in the `εNFA` for `plus P Q`. -/
theorem εClosure_plus_subset_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set Q.St) :
    Sum.inr ∘ Sum.inr '' MQ.εClosure S ⊆ M.εClosure (Sum.inr ∘ Sum.inr '' S) := by
  intro s hs
  rw [mem_image] at hs
  obtain ⟨t, ht, _⟩ := hs
  induction' ht with _ _ t _ _ _ ih generalizing s
  · apply εClosure.base; tauto
  · subst M MQ s
    apply εClosure.step (Sum.inr (Sum.inr t))
    · simp only [toεNFA, plus_step, mem_setOf_eq]
      left
      tauto
    · apply ih (by rfl)

/-- The `εNFA` for `plus P Q` only has ε-transitions for non-embedded states, i.e. only states
  mapped to the left or right `εNFA` have labeled transitions. -/
theorem step_plus_label_empty [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : Option Unit) (a : α) :
    M.step (Sum.inl s) (some a) = ∅ := by
  subst M
  simp only [toεNFA, plus_step]

/-- An accepting state of the `εNFA` for `plus P Q` has no transitions. -/
theorem step_plus_accept_empty [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : (P + Q).St) (a : Option α) :
    s ∈ M.accept -> M.step s a = ∅ := by
  subst M
  intro h
  simp only [toεNFA, plus_accept, mem_singleton_iff] at h
  subst s
  simp only [toεNFA, plus_step]

/-- The ε-closure of an embedded left state does not contain any embedded right state. -/
theorem εClosure_plus_right_not_in_left [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set P.St) :
    ∀ s, Sum.inr (Sum.inr s) ∉ M.εClosure (Sum.inr ∘ Sum.inl '' S) := by
  subst M
  intro s h
  generalize heq : Sum.inr (Sum.inr s) = t at h
  induction' h with _ ht t _ hs ht ih generalizing s <;> subst heq
  · simp_sum at ht
  · rcases t with ⟨_ | _⟩ | ⟨_ | t⟩
    · apply εClosure_plus_no_restart (by rfl) at ht <;> try trivial
      simp_sum
    · rw [step_plus_accept_empty (by rfl)] at hs <;> trivial
    · simp only [toεNFA, plus_step] at hs
      simp_sum at hs
    · apply ih t (by rfl)

/-- The ε-closure of an embedded right state does not contain any embedded left state. -/
theorem εClosure_plus_left_not_in_right [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set Q.St) :
    ∀ s, Sum.inr (Sum.inl s) ∉ M.εClosure (Sum.inr ∘ Sum.inr '' S) := by
  subst M
  intro s h
  generalize heq : Sum.inr (Sum.inl s) = t at h
  induction' h with _ ht t _ hs ht ih generalizing s <;> subst heq
  · simp_sum at ht
  · rcases t with ⟨_ | _⟩ | ⟨t | _⟩
    · apply εClosure_plus_no_restart (by rfl) at ht <;> try trivial
      simp_sum
    · rw [step_plus_accept_empty (by rfl)] at hs <;> trivial
    · apply ih t (by rfl)
    · simp only [toεNFA, plus_step] at hs
      simp_sum at hs

/-- A left labeled transition in the `εNFA` for `plus P Q` has a corresponding transition in the
  left `εNFA`. -/
theorem step_plus_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (a : α) (s : P.St) :
    M.step (Sum.inr (Sum.inl s)) (some a) = Sum.inr ∘ Sum.inl '' MP.step s (some a) := by
  subst M MP
  simp only [toεNFA, plus_step]
  simp_sum

/-- A right labeled transition in the `εNFA` for `plus P Q` has a corresponding transition in the
  right `εNFA`. -/
theorem step_plus_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (a : α) (s : Q.St) :
    M.step (Sum.inr (Sum.inr s)) (some a) = Sum.inr ∘ Sum.inr '' MQ.step s (some a) := by
  subst M MQ
  simp only [toεNFA, plus_step]
  simp_sum

/-- The `stepSet` of any left `εNFA` is a subset of the stepset of the `εNFA` for `plus P Q`. -/
theorem stepSet_plus_subset_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (a : α) (S : Set P.St) :
    Sum.inr ∘ Sum.inl '' MP.stepSet S a ⊆ M.stepSet (Sum.inr ∘ Sum.inl '' S) a := by
  intro s hs
  simp only [mem_image, mem_stepSet_iff] at hs
  obtain ⟨_, ⟨s, _, _⟩, _⟩ := hs
  simp only [mem_stepSet_iff]
  use (Sum.inr (Sum.inl s))
  constructor
  · tauto
  · rw [step_plus_left hP hM]
    apply εClosure_plus_subset_left hP hM
    tauto

/-- The `stepSet` of any right `εNFA` is a subset of the stepset of the `εNFA` for `plus P Q`. -/
theorem stepSet_plus_subset_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (a : α) (S : Set Q.St) :
    Sum.inr ∘ Sum.inr '' MQ.stepSet S a ⊆ M.stepSet (Sum.inr ∘ Sum.inr '' S) a := by
  intro s hs
  simp only [mem_image, mem_stepSet_iff] at hs
  obtain ⟨_, ⟨s, _, _⟩, _⟩ := hs
  simp only [mem_stepSet_iff]
  use (Sum.inr (Sum.inr s))
  constructor
  · tauto
  · rw [step_plus_right hQ hM]
    apply εClosure_plus_subset_right hQ hM
    tauto

/-- There are no transitions from any embedded left state to any embedded right state. -/
theorem step_plus_right_not_in_left [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : P.St) (a : Option α) :
    ∀ t, Sum.inr (Sum.inr t) ∉ M.step (Sum.inr (Sum.inl s)) a := by
  subst M
  intro t hc
  simp only [toεNFA, plus_step] at hc
  simp_sum at hc

/-- There are no transitions from any embedded right state to any embedded left state. -/
theorem step_plus_left_not_in_right [DecidableEq α] {P Q : RegularExpression α}
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : Q.St) (a : Option α) :
    ∀ t, Sum.inr (Sum.inl t) ∉ M.step (Sum.inr (Sum.inr s)) a := by
  subst M
  intro t hc
  simp only [toεNFA, plus_step] at hc
  simp_sum at hc

/-- The ε-closure of an embedded left state is a subset of embedded left states or an accepting
  state. -/
theorem εClosure_plus_subset_accept_or_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set P.St) :
    M.εClosure (Sum.inr ∘ Sum.inl '' S) ⊆ M.accept ∪ Sum.inr ∘ Sum.inl '' MP.εClosure S := by
  subst M MP
  simp only [toεNFA, plus_accept, plus_start]
  intro s hs
  simp_sum
  induction' hs with _ ht t s hs ht ih
  · right
    simp_sum at ht
    obtain ⟨t, _, _⟩ := ht
    use t
    tauto
  · obtain heq | ⟨u, _, heq⟩ := ih
    · rw [step_plus_accept_empty (by rfl) _ _ heq] at hs
      contradiction
    · rcases s with ⟨_ | _⟩ | ⟨_ | _⟩
      · apply step_plus_no_restart at hs <;> tauto
        · intro h
          apply εClosure_plus_no_restart at ht <;> tauto
          · subst t
            tauto
      · left
        rfl
      · right
        subst t
        obtain ⟨v, hv, heq⟩ | hs := hs
        · use v
          constructor
          · apply εClosure.step u <;> assumption
          · assumption
        · simp_sum at hs
      · subst t
        apply step_plus_right_not_in_left (by rfl) at hs
        contradiction

/-- The ε-closure of an embedded right state is a subset of embedded right states or an accepting
  state. -/
theorem εClosure_plus_subset_accept_or_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set Q.St) :
    M.εClosure (Sum.inr ∘ Sum.inr '' S) ⊆ M.accept ∪ Sum.inr ∘ Sum.inr '' MQ.εClosure S := by
  subst M MQ
  simp only [toεNFA, plus_accept, plus_start]
  intro s hs
  simp_sum
  induction' hs with _ ht t s hs ht ih
  · right
    simp_sum at ht
    obtain ⟨t, _, _⟩ := ht
    use t
    tauto
  · obtain heq | ⟨u, _, heq⟩ := ih
    · rw [step_plus_accept_empty (by rfl) _ _ heq] at hs
      contradiction
    · rcases s with ⟨_ | _⟩ | ⟨_ | _⟩
      · apply step_plus_no_restart at hs <;> tauto
        · intro h
          apply εClosure_plus_no_restart at ht <;> tauto
          · subst t
            tauto
      · left
        rfl
      · subst t
        apply step_plus_left_not_in_right (by rfl) at hs
        contradiction
      · right
        subst t
        obtain ⟨v, hv, heq⟩ | hs := hs
        · use v
          constructor
          · apply εClosure.step u <;> assumption
          · assumption
        · simp_sum at hs

/-- `evalFrom` embeds states and transitions in the left `εNFA` as left states and transitions in
  the `εNFA` for `plus P Q`. -/
theorem evalFrom_plus_subset_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set P.St) (x : List α) :
    Sum.inr ∘ Sum.inl '' MP.evalFrom S x ⊆ M.evalFrom (Sum.inr ∘ Sum.inl '' S) x := by
  induction' x using List.reverseRecOn with a x _
  · rw [evalFrom_nil]
    apply εClosure_plus_subset_left hP hM
  · repeat rw [evalFrom_append_singleton]
    apply subset_trans
    · apply stepSet_plus_subset_left hP hM
    · apply stepSet_subset
      assumption

/-- `evalFrom` embeds states and transitions in the right `εNFA` as right states and transitions in
  the `εNFA` for `plus P Q`. -/
theorem evalFrom_plus_subset_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (S : Set Q.St) (x : List α) :
    Sum.inr ∘ Sum.inr '' MQ.evalFrom S x ⊆ M.evalFrom (Sum.inr ∘ Sum.inr '' S) x := by
  induction' x using List.reverseRecOn with a x _
  · rw [evalFrom_nil]
    apply εClosure_plus_subset_right hQ hM
  · repeat rw [evalFrom_append_singleton]
    apply subset_trans
    · apply stepSet_plus_subset_right hQ hM
    · apply stepSet_subset
      assumption

/-- If the left `εNFA` accepts, then the `εNFA` for `plus P Q` accepts. -/
theorem eval_plus_accept_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (x : List α) :
    (MP.accept ∩ MP.eval x).Nonempty → (M.accept ∩ M.eval x).Nonempty := by
  subst M MP
  intro ⟨s, _, _⟩
  use Sum.inl (some ())
  constructor
  · rfl
  · rw [eval, ← εClosure_evalFrom]
    apply εClosure.step (Sum.inr (Sum.inl s))
    · simp only [toεNFA, plus_step]
      simp_sum
      assumption
    · constructor
      apply evalFrom_εClosure_subset' _ _ _ _ (εClosure_plus_start_subset_left (by rfl) (by rfl))
      apply evalFrom_plus_subset_left (by rfl) (by rfl)
      simp_sum
      assumption

/-- If the right `εNFA` accepts, then the `εNFA` for `plus P Q` accepts. -/
theorem eval_plus_accept_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (x : List α) :
    (MQ.accept ∩ MQ.eval x).Nonempty → (M.accept ∩ M.eval x).Nonempty := by
  subst M MQ
  intro ⟨s, _, _⟩
  use Sum.inl (some ())
  constructor
  · rfl
  · rw [eval, ← εClosure_evalFrom]
    apply εClosure.step (Sum.inr (Sum.inr s))
    · simp only [toεNFA, plus_step]
      simp_sum
      assumption
    · constructor
      apply evalFrom_εClosure_subset' _ _ _ _ (εClosure_plus_start_subset_right (by rfl) (by rfl))
      apply evalFrom_plus_subset_right (by rfl) (by rfl)
      simp_sum
      assumption

/-- Starting state ε-closure inversion--an embedded left state in the ε-closure of the starting
  state of an `εNFA` for `plus P Q` exists in the ε-closure for the starting state of the left
  `εNFA`. -/
theorem εClosure_plus_start_left_inv [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : P.St) :
    Sum.inr (Sum.inl s) ∈ M.εClosure M.start → s ∈ MP.εClosure MP.start := by
  subst M MP
  intro h
  generalize heq : Sum.inr (Sum.inl s) = t at h
  induction' h with _ _ t _ ht generalizing s <;> subst heq
  · contradiction
  · simp only [toεNFA, plus_step] at ht
    rcases t with ⟨_ | _⟩ | ⟨t | _⟩ <;> simp_sum at ht <;> tauto
    · apply εNFA.εClosure.step t <;> tauto

/-- Starting state ε-closure inversion--an embedded right state in the ε-closure of the starting
  state of an `εNFA` for `plus P Q` exists in the ε-closure for the starting state of the right
  `εNFA`. -/
theorem εClosure_plus_start_right_inv [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : Q.St) :
    Sum.inr (Sum.inr s) ∈ M.εClosure M.start → s ∈ MQ.εClosure MQ.start := by
  subst M MQ
  intro h
  generalize heq : Sum.inr (Sum.inr s) = t at h
  induction' h with _ _ t _ ht generalizing s <;> subst heq
  · contradiction
  · simp only [toεNFA, plus_step] at ht
    rcases t with ⟨_ | _⟩ | ⟨_ | t⟩ <;> simp_sum at ht <;> tauto
    · apply εNFA.εClosure.step t <;> tauto

/-- The ε-closure of a starting state of the `εNFA` for `plus P Q` has an upper bound at the
  ε-closures of the starting states of the left and right `εNFA`s, plus the sets of starting and
  accepting states. -/
theorem εClosure_plus_start_subset [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA) :
    M.εClosure M.start ⊆
      M.start ∪ M.accept ∪ Sum.inr '' Sum.elim (MP.εClosure MP.start) (MQ.εClosure MQ.start) := by
  subst M MP MQ
  intro s hs
  cases' hs with _ _ t _ hs
  · tauto
  · simp only [toεNFA, plus_step] at hs
    rcases t with ⟨_ | _⟩ | t
    · right
      simp only [Sum.exists, mem_image] at *
      obtain ⟨u, hu, _⟩ | ⟨u, hu, _⟩ := hs
        <;> apply mem_def.mp at hu
        <;> simp only [Sum.elim_inl, Sum.elim_inr] at hu
        <;> [left; right]
        <;> use u
        <;> tauto
    · contradiction
    · simp only [Sum.exists, mem_image, mem_union]
      cases' t with t t <;> simp only [Function.comp_apply, mem_image, mem_union, true_and] at hs
      · obtain ⟨u, _, _⟩ | hs := hs
        · subst s
          right
          left
          use u
          simp only [and_true]
          apply εNFA.εClosure.step t
          · assumption
          · apply εClosure_plus_start_left_inv (by rfl) (by rfl)
            assumption
        · left
          right
          simp_sum at hs
          tauto
      · obtain ⟨u, _, _⟩ | hs := hs
        · subst s
          right
          right
          use u
          simp only [and_true]
          apply εNFA.εClosure.step t
          · assumption
          · apply εClosure_plus_start_right_inv (by rfl) (by rfl)
            assumption
        · left
          right
          simp_sum at hs
          tauto

/-- Labeled step inversion--an embedded left step in the `εNFA` for `plus P Q` is a step in the
  left `εNFA`. -/
theorem εClosure_step_plus_left_inv [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s t : P.St) (a : α) :
    Sum.inr (Sum.inl s) ∈ M.εClosure (M.step (Sum.inr (Sum.inl t)) (some a)) →
      s ∈ MP.εClosure (MP.step t (some a)) := by
  subst M MP
  intro h
  generalize heq : Sum.inr (Sum.inl s) = t at h
  induction' h with _ ht t _ hs ht ih generalizing s <;> subst heq
  · simp only [toεNFA, plus_step] at ht
    simp_sum at ht
    tauto
  · rw [step_plus_left (by rfl) (by rfl)] at ht
    apply εClosure_plus_subset_accept_or_left (by rfl) (by rfl) at ht
    obtain ht | ht := ht
    · rw [step_plus_accept_empty] at hs <;> tauto
    · simp_sum at ht
      obtain ⟨u, _, _⟩ := ht
      apply εClosure.step u
      · subst t
        simp only [toεNFA, plus_step] at hs
        simp_sum at hs
        assumption
      · trivial

/-- Labeled step inversion--an embedded right step in the `εNFA` for `plus P Q` is a step in the
  right `εNFA`. -/
theorem εClosure_step_plus_right_inv [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s t : Q.St) (a : α) :
    Sum.inr (Sum.inr s) ∈ M.εClosure (M.step (Sum.inr (Sum.inr t)) (some a)) →
      s ∈ MQ.εClosure (MQ.step t (some a)) := by
  subst M MQ
  intro h
  generalize heq : Sum.inr (Sum.inr s) = t at h
  induction' h with _ ht t _ hs ht ih generalizing s <;> subst heq
  · simp only [toεNFA, plus_step] at ht
    simp_sum at ht
    tauto
  · rw [step_plus_right (by rfl) (by rfl)] at ht
    apply εClosure_plus_subset_accept_or_right (by rfl) (by rfl) at ht
    obtain ht | ht := ht
    · rw [step_plus_accept_empty] at hs <;> tauto
    · simp_sum at ht
      obtain ⟨u, _, _⟩ := ht
      apply εClosure.step u
      · subst t
        simp only [toεNFA, plus_step] at hs
        simp_sum at hs
        assumption
      · trivial

/-- An embedded left state reached by `eval` on the `εNFA` for `plus P Q` is the same as the state
  reached by `eval` on the left `εNFA`. -/
theorem eval_plus_left [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : P.St) (x : List α) :
    Sum.inr (Sum.inl s) ∈ M.eval x → s ∈ MP.eval x := by
  subst M MP
  simp only [eval, evalFrom, stepSet]
  intro h
  induction' x using List.reverseRecOn with h' t generalizing s
  · simp only [toεNFA, plus_accept, plus_start, foldl_nil] at h
    apply εClosure_plus_start_subset (by rfl) (by rfl) (by rfl) at h
    simp_sum at h
    simp only [Sum.exists] at h
    obtain ⟨s, _, heq⟩ | ⟨_, _, heq⟩ := h <;> simp only [foldl_nil] <;> cases heq
    · assumption
  · simp only [Sum.exists, foldl_append, foldl_cons, foldl_nil, mem_stepSet_iff] at *
    obtain ⟨_, _, h⟩ | ⟨s, _, h⟩ | ⟨_, _, h⟩ := h
    · rw [step_plus_label_empty (by rfl), εClosure_empty] at h
      contradiction
    · use s
      constructor
      · tauto
      · apply εClosure_step_plus_left_inv (by rfl) (by rfl) at h
        assumption
    · rw [step_plus_right (by rfl) (by rfl)] at h
      apply εClosure_plus_left_not_in_right (by rfl) at h
      contradiction

/-- An embedded right state reached by `eval` on the `εNFA` for `plus P Q` is the same as the state
  reached by `eval` on the right `εNFA`. -/
theorem eval_plus_right [DecidableEq α] {P Q : RegularExpression α}
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s : Q.St) (x : List α) :
    Sum.inr (Sum.inr s) ∈ M.eval x → s ∈ MQ.eval x := by
  subst M MQ
  simp only [eval, evalFrom, stepSet]
  intro h
  induction' x using List.reverseRecOn with h' t generalizing s
  · simp only [toεNFA, plus_accept, plus_start, foldl_nil] at h
    apply εClosure_plus_start_subset (by rfl) (by rfl) (by rfl) at h
    simp_sum at h
    simp only [Sum.exists] at h
    obtain ⟨_, _, heq⟩ | ⟨s, _, heq⟩ := h <;> simp only [foldl_nil] <;> cases heq
    · assumption
  · simp only [Sum.exists, foldl_append, foldl_cons, foldl_nil, mem_stepSet_iff] at *
    obtain ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨s, _, h⟩ := h
    · rw [step_plus_label_empty (by rfl), εClosure_empty] at h
      contradiction
    · rw [step_plus_left (by rfl) (by rfl)] at h
      apply εClosure_plus_right_not_in_left (by rfl) at h
      contradiction
    · use s
      constructor
      · tauto
      · apply εClosure_step_plus_right_inv (by rfl) (by rfl) at h
        assumption

/-- Inversion for an accepting `step`--the previous state must be an accepting state in either the
  left or right `εNFA`. -/
theorem step_plus_accept_inv [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (s t : (P + Q).St) :
    s ∈ M.accept → s ∈ M.step t none →
        (∃ u, t = Sum.inr (Sum.inl u) ∧ u ∈ MP.accept)
      ∨ (∃ u, t = Sum.inr (Sum.inr u) ∧ u ∈ MQ.accept) := by
  subst M MP MQ
  simp only [toεNFA, plus_accept, plus_step]
  intro hs h
  subst s
  rcases t with ⟨_ | _⟩ | t
  · simp_sum at h
  · trivial
  · rcases t with t | t <;> [left; right] <;> simp_sum at h <;> use t <;> trivial

/-- Inversion for `eval` accepting the empty string--either the left or right `εNFA` accept the
  empty string. -/
theorem eval_plus_nil_inv [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA) :
    (M.accept ∩ M.eval []).Nonempty →
      (MP.accept ∩ MP.eval []).Nonempty ∨ (MQ.accept ∩ MQ.eval []).Nonempty := by
  subst M
  intro ⟨s, ⟨ha, he⟩⟩
  rw [eval_nil] at he
  cases' he with _ hs t s hs ht
  · simp only [toεNFA, plus_accept, plus_start] at *
    subst s
    cases hs
  · apply step_plus_accept_inv hP hQ (by rfl) _ _ ha at hs
    obtain ⟨s, _, _⟩ | ⟨s, _, _⟩ := hs
      <;> [left; right]
      <;> use s
      <;> constructor
      <;> try trivial
    · apply eval_plus_left hP (by rfl)
      subst t
      assumption
    · apply eval_plus_right hQ (by rfl)
      subst t
      assumption

/-- Inversion for `eval`--if the `εNFA` for `plus P Q` accepts a string, then either the left or
  right `εNFA` accept the same string. -/
theorem eval_plus_inv [DecidableEq α] {P Q : RegularExpression α}
    {MP : εNFA α _} (hP : MP = P.toεNFA)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA)
    (x : List α) :
    (M.accept ∩ M.eval x).Nonempty →
      (MP.accept ∩ MP.eval x).Nonempty ∨ (MQ.accept ∩ MQ.eval x).Nonempty := by
  subst M MP MQ
  simp only [toεNFA]
  intro ⟨s, ⟨ha, he⟩⟩
  induction' x using List.reverseRecOn with h t
  · apply eval_plus_nil_inv (by rfl) (by rfl) (by rfl)
    tauto
  · simp only [eval_append_singleton, mem_stepSet_iff] at he
    obtain ⟨t, _, hs⟩ := he
    cases' hs with _ hs u _ hs <;> simp only [plus_step] at hs
    · rcases t with ⟨_ | _⟩ | ⟨_ | _⟩
        <;> tauto
        <;> simp_sum at hs
        <;> subst s
        <;> tauto
    · rcases u with ⟨_ | u⟩ | ⟨u | u⟩
      · simp only [Sum.exists, mem_image] at hs
        obtain ⟨_, _, _⟩ | ⟨_, _, _⟩ := hs <;> subst s <;> contradiction
      · contradiction
      · obtain ⟨_, _, _⟩ | ⟨_, _, _⟩ := hs
        · subst s
          contradiction
        · left
          use u
          constructor
          · assumption
          · apply eval_plus_left (by rfl) (by rfl)
            simp only [eval, evalFrom, stepSet, exists_prop', foldl_append, foldl_cons, foldl_nil,
              mem_iUnion, nonempty_prop]
            tauto
      · obtain ⟨_, _, _⟩ | ⟨_, _, _⟩ := hs
        · subst s
          contradiction
        · right
          use u
          constructor
          · assumption
          · apply eval_plus_right (by rfl) (by rfl)
            simp only [eval, evalFrom, stepSet, exists_prop', foldl_append, foldl_cons, foldl_nil,
              mem_iUnion, nonempty_prop]
            tauto

/-- Correctness of `(plus P Q).toεNFA` -/
theorem toεNFA_plus [DecidableEq α] {P Q : RegularExpression α} {LP LQ : Language α}
    {MP : εNFA α _} (hP : MP = P.toεNFA) (hPL : LP = MP.accepts)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA) (hPQ : LQ = MQ.accepts)
    {M : εNFA α _} (hM : M = (P + Q).toεNFA) :
    M.accepts = LP + LQ := by
  subst LP LQ
  apply Subset.antisymm
  · apply setOf_subset.mpr
    intro x h
    apply eval_plus_inv hP hQ hM at h
    apply h
  · apply subset_setOf.mpr
    intro x h
    rw [Language.mem_add] at h
    obtain h | h := h
    · apply eval_plus_accept_left hP hM x h
    · apply eval_plus_accept_right hQ hM x h

/-! ### Lemmas for `comp` -/

/-- Correctness of `(comp P Q).toεNFA` -/
theorem toεNFA_comp [DecidableEq α] {P Q : RegularExpression α} {LP LQ : Language α}
    {MP : εNFA α _} (hP : MP = P.toεNFA) (hPL : LP = MP.accepts)
    {MQ : εNFA α _} (hQ : MQ = Q.toεNFA) (hPQ : LQ = MQ.accepts)
    {M : εNFA α _} (hM : M = (comp P Q).toεNFA) :
    M.accepts = LP * LQ := by
  -- TODO
  sorry

/-! ### Lemmas for `star` -/

/-- Correctness of `(star P).toεNFA` -/
theorem toεNFA_star [DecidableEq α] {P : RegularExpression α} {LP : Language α}
    {MP : εNFA α _} (hP : MP = P.toεNFA) (hPL : LP = MP.accepts)
    {M : εNFA α _} (hM : M = (star P).toεNFA) :
    M.accepts = LP∗ := by
  -- TODO
  sorry

/-! ### Correctness of `P.toεNFA` -/

theorem toεNFA_correct [DecidableEq α] (P : RegularExpression α) :
    P.toεNFA.accepts = P.matches' := by
  induction P with
  | zero =>
    exact toεNFA_zero
  | epsilon =>
    exact toεNFA_epsilon
  | char a =>
    exact toεNFA_char a (by rfl)
  | plus P Q hPL hQL =>
    generalize hP : P.toεNFA = MP at hPL
    generalize hQ : Q.toεNFA = MQ at hQL
    apply toεNFA_plus <;> symm <;> tauto
  | comp P Q hPL hQL =>
    generalize hP : P.toεNFA = MP at hPL
    generalize hQ : Q.toεNFA = MQ at hQL
    apply toεNFA_comp <;> symm <;> tauto
  | star P hPL =>
    generalize hP : P.toεNFA = MP at hPL
    apply toεNFA_star <;> symm <;> tauto

end RegularExpression
