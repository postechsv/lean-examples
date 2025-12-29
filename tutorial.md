# Tutorial

## representing rewrite theries
The rewrite rules for bakery algorithm can be encoded as 
the following inductive type `Step` in Lean.
```
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
```

## Verifying safety by inductive invariants


## representing inductive invariants
```
def init_pred (cf : Conf) : Prop :=
  cf.t = cf.s ∧ is cf.c

def wait_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧ ws cf.c ∧ (∀ k ∈ tickets cf.c, k ≥ cf.s ∧ k < cf.t) ∧ ((tickets cf.c).Nodup)

def crit_pred (cf : Conf) : Prop :=
  cf.t > cf.s ∧
  ∃ ps : ProcSet,
    cf.c = {$[crit cf.s]} + ps ∧
    ws ps ∧
    (∀ k ∈ tickets ps, k > cf.s ∧ k < cf.t) ∧
    ((tickets ps).Nodup)
```
