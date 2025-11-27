import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Logic.Relation

inductive Mode where
  | idle
  | wait : Nat → Mode
  | crit : Nat → Mode


inductive Proc where
  | proc : Mode → Proc


notation "$[" m "]" => Proc.proc m

abbrev ProcSet := Multiset Proc

structure Conf where
  t : Nat
  s : Nat
  c : ProcSet

open Mode Proc Nat
open scoped Multiset

inductive Step : Conf → Conf → Prop where
  | wake : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n,      s := m, c := {$[idle]}   + ps}
           {t := succ n, s := m, c := {$[wait n]} + ps}
  | crit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m, c := {$[wait m]} + ps}
           {t := n, s := m, c := {$[crit m]} + ps}
  | exit : ∀ n m : Nat, ∀ ps : ProcSet,
      Step {t := n, s := m,      c := {$[crit m]} + ps}
           {t := n, s := succ m, c := {$[idle]} + ps}

infix:110 " ⇒ " => Step
infix:110 " ⇒* " => Relation.ReflTransGen Step

#check Step
#check ({$[idle]} : ProcSet)
#check {$[idle]} + {$[idle]}

def init1 : Conf :=
  {t := 0, s := 0, c := {$[idle]}}

def init2 : Conf :=
  {t := 0, s := 0, c := {$[idle], $[idle]}}


variable (n m k : Nat)
variable (ps : ProcSet)
variable (cf : Conf)


example : init1 ⇒* init1 := by
  apply Relation.ReflTransGen.refl


example : init1 ⇒* {t := 1, s := 0, c := {$[wait 0]}} := by
  apply Relation.ReflTransGen.single
  · apply Step.wake 0 0 0


example : init1 ⇒* {t := 1, s := 0, c := {$[crit 0]}} := by
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    apply Step.wake 0 0 0
  · apply Relation.ReflTransGen.single
    apply Step.crit


example : init2 ⇒* {t := 2, s := 0, c := {$[wait 1], $[wait 0]}} := by
  apply Relation.ReflTransGen.trans
  · apply Relation.ReflTransGen.single
    apply Step.wake 0 0 {$[idle]}
  · apply Relation.ReflTransGen.single
    rw [Multiset.add_comm]
    apply Step.wake

--- all proces are idle
def is (ps : ProcSet) :=
  ∀m ∈ ps, m = $[idle]

--- all procs are either idle or waiting
def ws (ps : ProcSet) :=
  ∀m ∈ ps, (m = $[idle] ∨ ∃ n, m = $[wait n])

def Proc.ticket? : Proc → Option Nat
  | $[wait n] => some n
  | $[crit n] => some n
  | $[idle]   => none

--- return the set of all ticket numbers in a procset
def tickets (ps : ProcSet) : Multiset Nat := ps.filterMap Proc.ticket?

#eval tickets {$[idle], $[wait 3], $[crit 5], $[wait 3]} = {3, 5, 3}

example : ¬(is ($[wait m] ::ₘ ps)) := by
  unfold is
  simp


---------------------
--- Useful Lemmas ---
---------------------

lemma tickets_up :
  ∀ (p: Proc) (ps: ProcSet) (k: Nat),
    k ∈ tickets ps →
    k ∈ tickets (p ::ₘ ps) := by
  intro p ps k hk
  simp [tickets] at *; right; apply hk


lemma tickets_down :
  ∀ (p: Proc) (ps: ProcSet) (k: Nat),
    k ∈ tickets (p ::ₘ ps) →
    (p.ticket? = some k ∨ k ∈ tickets ps) := by
  intro p ps k hk
  simp [tickets] at hk
  rcases hk with hk1 | hk2
  · exact Or.inl hk1
  · right; simpa [tickets]


lemma nodup_up {p : Proc} {ps : ProcSet} (k : Nat) :
  (p.ticket? = some k) →
    (k ∉ tickets ps) →
    (tickets ps).Nodup →
    (tickets (p ::ₘ ps)).Nodup := by
  intro h1 h2 h3
  have hpair : k ∉ tickets ps ∧ (tickets ps).Nodup := ⟨h2, h3⟩
  simpa [tickets, h1, Multiset.nodup_cons] using hpair


lemma nodup_down :
  ∀ (p : Proc) (ps : ProcSet), (tickets (p ::ₘ ps)).Nodup →
      (tickets ps).Nodup := by
  intro p ps h
  apply Multiset.nodup_of_le _ h
  simp [tickets]
  cases htp : ticket? p with
  | none => simp [htp]
  | some k => simp [htp]; exact Multiset.le_cons_self _ _


lemma freshness :
  ∀ (p : Proc) (ps : ProcSet) (n: Nat), (tickets (p ::ₘ ps)).Nodup →
    (p = $[wait n] ∨ p = $[crit n]) → n ∉ tickets ps := by
  intro p ps n h1 h2 h3
  have hp_ticket : ticket? p = some n := by
    cases h2 with
    | inl hw => simp [hw, ticket?]
    | inr hc => simp [hc, ticket?]
  have hnodup : (n ::ₘ tickets ps).Nodup := by
    simpa [tickets, hp_ticket] using h1
  have hn_not : n ∉ tickets ps :=
    (Multiset.nodup_cons.1 hnodup).1
  exact hn_not h3


----------------------------
--- Inductive Invariants ---
----------------------------

def init_pred (cf : Conf) : Prop :=
  cf.t = cf.s ∧ is cf.c

#check init_pred

def wait_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧ ws cf.c ∧ (∀ k ∈ tickets cf.c, k ≥ cf.s ∧ k < cf.t) ∧ ((tickets cf.c).Nodup)


def crit_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧
  ∃ ps : ProcSet,
    cf.c = {$[crit cf.s]} + ps ∧
    ws ps ∧
    (∀ k ∈ tickets ps, k > cf.s ∧ k < cf.t) ∧
    ((tickets ps).Nodup)


lemma idle_wait {cf cf' : Conf} :
    (init_pred cf ∧ (cf ⇒ cf')) →
    wait_pred cf' := by
  simp [init_pred, wait_pred, is, ws]
  intro hts his hstep
  cases hstep with
  | crit n m ps => simp at *
  | exit n m ps => simp at *
  | wake n m ps =>
      simp at *
      simp [hts]
      constructor
      · intro ha hha
        apply his at hha
        exact Or.inl hha
      · constructor
        · intro k hk
          simp [tickets, ticket?] at hk
          rcases hk with hA | hB
          · simp [hA]
          · rcases hB with ⟨a, ⟨ha, ha'⟩⟩
            apply his at ha
            simp [ha] at ha'
        · have hps: tickets ps = Multiset.zero := by
            induction ps using Multiset.induction_on with
            | empty => simp [tickets]; rfl
            | @cons p ps ih =>
                simp at his
                have h1 := his.1
                have h2 := ih his.2
                simp [h1, ←h2, tickets, ticket?]
          apply nodup_up m
          · simp [ticket?]
          · simp [hps]; intro hm; rcases hm
          · simp [hps]; apply Multiset.nodup_zero

lemma wait_waitOrCrit {cf cf' : Conf} :
    (wait_pred cf ∧ (cf ⇒ cf')) →
    (wait_pred cf' ∨ crit_pred cf') := by
  intro ⟨⟨hts,hws,⟨hrange, hnodup⟩⟩, hstep⟩
  cases hstep with
  | crit n m ps =>
    simp at * ; right ; simp [crit_pred]
    constructor
    · apply hts
    constructor
    · simp [ws] at * ; exact hws
    · simp [ws] at *
      constructor
      · intro k hk
        have h : m ∉ tickets ps
          := (freshness $[wait m] ps m hnodup (Or.inl rfl))
        have h' : k ∈ tickets ($[wait m] ::ₘ ps)
          := (tickets_up $[wait m] ps k hk)
        apply hrange at h'
        have hm : m ≠ k := by
          intro hmkeq; apply h; simpa [hmkeq]
        exact ⟨lt_of_le_of_ne h'.1 hm, h'.right⟩
      · exact (nodup_down $[wait m] ps hnodup)
  | exit n m ps => simp [ws] at *
  | wake n m ps =>
    simp [wait_pred] at *; left
    constructor
    · exact (lt_trans hts (Nat.lt_succ_self n))
    constructor
    · simp [ws] at *; apply hws
    constructor
    · intro k hk
      have hk' := hrange k
      apply tickets_down at hk
      rcases hk with hkA | hkB
      · simp [ticket?] at hkA
        constructor
        · rw [←hkA]; apply le_of_lt hts
        · rw [hkA]; apply lt_succ_self k
      · apply (tickets_up $[idle] ps) at hkB
        apply hk' at hkB
        exact ⟨hkB.1, lt_trans hkB.2 (Nat.lt_succ_self n)⟩
    · apply nodup_up
      · simp [ticket?]; rfl
      · intro hn
        apply tickets_up $[idle] ps at hn
        apply hrange at hn
        exact lt_irrefl n hn.2
      · exact nodup_down $[idle] ps hnodup

lemma crit_wait {cf cf' : Conf} :
    (crit_pred cf ∧ (cf ⇒ cf')) →
    (wait_pred cf') := by sorry

def inv_pred (cf : Conf) : Prop :=
  init_pred cf ∨ wait_pred cf ∨ crit_pred cf

lemma inv_ind {cf cf' : Conf} :
    (inv_pred cf ∧ (cf ⇒ cf')) →
    (inv_pred cf') := by sorry

def mutex_pred (cf : Conf) : Prop := sorry

lemma inv_mutex : ∀ (cf : Conf), inv_pred cf → mutex_pred cf := sorry

theorem bakery_mutex {cf cf' : Conf} :
    (init_pred cf ∧ (cf ⇒* cf')) →
    (mutex_pred cf') := by sorry
