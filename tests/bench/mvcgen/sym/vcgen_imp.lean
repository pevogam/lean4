/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Std.Tactic.Do
import Std.Internal.Do
import Std.Internal.Do.Triple.SpecLemmas

/-!
# `mvcgen'` on a non-monadic program type

This test exercises the `WP`/`WPMonad` split: it defines a small IMP language with (non-reentrant)
function calls whose weakest precondition is an *operational* semantics, gives it a `WP` instance
(without any `WPMonad` instance, since `Cmd` is not a monad), and uses `mvcgen'` to generate
verification conditions. The environment lives in the assertion (`Env → State → Prop`) so the
program stays a bare `Cmd` and `mvcgen'` discriminates on its constructors.
-/

open Std.Internal.Do
open Lean.Order

set_option mvcgen.warning false

/-! ## IMP syntax and state -/

abbrev Var := String
abbrev State := Var → Nat

def State.update (s : State) (x : Var) (v : Nat) : State :=
  fun y => if y = x then v else s y

inductive Expr where
  | lit (n : Nat)
  | var (x : Var)
  | add (e₁ e₂ : Expr)

@[simp] def Expr.eval (s : State) : Expr → Nat
  | .lit n => n
  | .var x => s x
  | .add e₁ e₂ => e₁.eval s + e₂.eval s

inductive Cmd where
  | skip
  | assign (x : Var) (e : Expr)
  | seq (c₁ c₂ : Cmd)
  | ite (cond : Expr) (c₁ c₂ : Cmd)
  | while (cond : Expr) (body : Cmd)
  | call (f : Nat)

/-! ## Non-reentrant function environment -/

inductive Env where
  | nil
  | snoc (Φ : Env) (body : Cmd)

def Env.lookup : Env → Nat → Option (Env × Cmd)
  | .nil, _ => none
  | .snoc Φ body, 0 => some (Φ, body)
  | .snoc Φ _, k+1 => Φ.lookup k

theorem Env.lookup_sizeOf_lt {Φ Φ' : Env} {body : Cmd} {f : Nat}
    (h : Φ.lookup f = some (Φ', body)) : sizeOf Φ' < sizeOf Φ := by
  induction Φ generalizing f with
  | nil => simp [Env.lookup] at h
  | snoc Ψ b ih =>
    cases f with
    | zero =>
      simp only [Env.lookup, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [Env.snoc.sizeOf_spec]; omega
    | succ k =>
      simp only [Env.lookup] at h
      have := ih (f := k) h
      simp only [Env.snoc.sizeOf_spec]; omega

/-! ## Omni-style weakest precondition -/

def wpCmd (Φ : Env) : Cmd → (State → Prop) → State → Prop
  | .skip, Q, s => Q s
  | .assign x e, Q, s => Q (s.update x (e.eval s))
  | .seq c₁ c₂, Q, s => wpCmd Φ c₁ (fun s' => wpCmd Φ c₂ Q s') s
  | .ite cond c₁ c₂, Q, s =>
    if cond.eval s ≠ 0 then wpCmd Φ c₁ Q s else wpCmd Φ c₂ Q s
  | .while cond body, Q, s =>
    ∃ I : State → Prop,
      I s ∧
      (∀ s', I s' → cond.eval s' ≠ 0 → wpCmd Φ body I s') ∧
      (∀ s', I s' → cond.eval s' = 0 → Q s')
  | .call f, Q, s =>
    match h : Φ.lookup f with
    | some (Φ', body) => wpCmd Φ' body Q s
    | none => False
  termination_by c => (sizeOf Φ, sizeOf c)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (Env.lookup_sizeOf_lt h)
      | (apply Prod.Lex.right
         simp only [Cmd.seq.sizeOf_spec, Cmd.ite.sizeOf_spec, Cmd.while.sizeOf_spec]; omega)

theorem wpCmd_mono {Φ : Env} {c : Cmd} {Q Q' : State → Prop} (hQ : ∀ s, Q s → Q' s) :
    ∀ s, wpCmd Φ c Q s → wpCmd Φ c Q' s := by
  match Φ, c with
  | Φ, .skip => intro s h; simp only [wpCmd] at h ⊢; exact hQ s h
  | Φ, .assign x e => intro s h; simp only [wpCmd] at h ⊢; exact hQ _ h
  | Φ, .seq c₁ c₂ =>
    intro s h
    simp only [wpCmd] at h ⊢
    exact wpCmd_mono (fun s' h' => wpCmd_mono hQ s' h') s h
  | Φ, .ite cond c₁ c₂ =>
    intro s h
    simp only [wpCmd] at h ⊢
    split
    · exact wpCmd_mono hQ s (by rwa [if_pos (by assumption)] at h)
    · exact wpCmd_mono hQ s (by rwa [if_neg (by assumption)] at h)
  | Φ, .while cond body =>
    intro s h
    simp only [wpCmd] at h ⊢
    obtain ⟨I, hI, hstep, hexit⟩ := h
    exact ⟨I, hI, hstep, fun s' hI' hc => hQ s' (hexit s' hI' hc)⟩
  | Φ, .call f =>
    intro s h
    simp only [wpCmd] at h ⊢
    split
    · next Φ' body heq => rw [heq] at h; exact wpCmd_mono hQ s h
    · next heq => rw [heq] at h; exact h.elim
  termination_by (sizeOf Φ, sizeOf c)
  decreasing_by
    all_goals first
      | exact Prod.Lex.left _ _ (Env.lookup_sizeOf_lt (by assumption))
      | (apply Prod.Lex.right
         simp only [Cmd.seq.sizeOf_spec, Cmd.ite.sizeOf_spec, Cmd.while.sizeOf_spec]; omega)

/-! ## `WP` instance: the env lives in the assertion

`wp` of a `Cmd` is a predicate transformer over `Env → State → Prop`: the program type is bare
`Cmd` (so `mvcgen'` discriminates on the `Cmd` constructors), and the environment threads through
the assertion rather than the type. -/

abbrev Assn := Env → State → Prop

instance : WP Cmd Unit Assn EPost.Nil where
  wpTrans c := ⟨fun Q _epost Φ s => wpCmd Φ c (Q () Φ) s⟩
  wp_trans_monotone c := by
    intro Q Q' e e' _he hQ Φ s h
    exact wpCmd_mono (fun s' h' => hQ () Φ s' h') s h

@[simp] theorem wp_cmd_eq (c : Cmd) (Q : Unit → Assn) (epost : EPost.Nil) :
    Std.Internal.Do.wp c Q epost = fun Φ s => wpCmd Φ c (Q () Φ) s := rfl

/-! ## Specification lemmas, one per constructor -/

variable {Q : Unit → Assn} {epost : EPost.Nil}

@[spec] theorem Spec.skip :
    Triple (Q ()) (Cmd.skip) Q epost :=
  Triple.iff.mpr (by simp only [wp_cmd_eq, wpCmd]; exact PartialOrder.rel_refl)

@[spec] theorem Spec.assign (x : Var) (e : Expr) :
    Triple (fun Φ s => Q () Φ (s.update x (e.eval s))) (Cmd.assign x e) Q epost :=
  Triple.iff.mpr (by simp only [wp_cmd_eq, wpCmd]; exact PartialOrder.rel_refl)

@[spec] theorem Spec.seq (c₁ c₂ : Cmd) :
    Triple (Std.Internal.Do.wp c₁ (fun _ => Std.Internal.Do.wp c₂ Q epost) epost)
      (Cmd.seq c₁ c₂) Q epost :=
  Triple.iff.mpr (by simp only [wp_cmd_eq, wpCmd]; exact PartialOrder.rel_refl)

@[spec] theorem Spec.ite (cond : Expr) (c₁ c₂ : Cmd) :
    Triple (fun Φ s => if cond.eval s ≠ 0
              then Std.Internal.Do.wp c₁ Q epost Φ s
              else Std.Internal.Do.wp c₂ Q epost Φ s)
      (Cmd.ite cond c₁ c₂) Q epost :=
  Triple.iff.mpr (by simp only [wp_cmd_eq, wpCmd]; exact PartialOrder.rel_refl)

/-- Modular spec for a non-reentrant call: the call's weakest precondition is the body's weakest
precondition in the (strictly smaller) prefix environment, with the postcondition still read at the
caller's environment. -/
@[spec] theorem Spec.call (f : Nat) :
    Triple (fun Φ s => (Φ.lookup f).elim False
              (fun p => Std.Internal.Do.wp p.2 (fun u _ => Q u Φ) epost p.1 s))
      (Cmd.call f) Q epost :=
  Triple.iff.mpr (by
    intro Φ s hs
    show wpCmd Φ (Cmd.call f) (Q () Φ) s
    rw [wpCmd]
    revert hs
    cases h : Φ.lookup f <;> simp [Option.elim, wp_cmd_eq])

/-! ## Generating weakest preconditions with `mvcgen'` -/

def env0 : Env := .snoc .nil (.assign "x" (.add (.var "x") (.lit 1)))
def client : Cmd := .seq (.assign "y" (.lit 5)) (.call 0)

-- `mvcgen'` decomposes the bare `Cmd` (seq/assign) and applies the modular call spec; the residual
-- VC is the call's lookup, discharged for the concrete environment `env0`.
example :
    Triple (fun Φ _ => Φ = env0) client (fun _ _ s => s "y" = 5) EPost.Nil.mk := by
  unfold client
  mvcgen' [Spec.call]
  subst_vars
  simp [env0, Env.lookup, wp_cmd_eq, wpCmd, State.update]
