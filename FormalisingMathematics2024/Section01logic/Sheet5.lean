/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  cases' h1 with h3 h4
  constructor
  exact h4
  exact h3
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw[h1]
  intro h2
  rw[h2]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  rw[h2] at h1
  exact h1
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  cases' h1 with h2 h3
  exact And.intro h3 h2
  intro h1
  cases' h1 with h2 h3
  exact And.intro h3 h2
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  cases' h1 with h2 h3
  exact And.intro h2 h3
  intro h1
  constructor
  cases' h1 with h2 h3
  cases' h3 with h4 h5
  exact And.intro h2 h4
  cases' h1 with h2 h3
  cases' h3 with h4 h5
  exact h5
  done

example : P ↔ P ∧ True := by
  constructor
  intro h1
  constructor
  exact h1
  triv
  intro h1
  cases' h1 with h2 h3
  exact h2
  done

example : False ↔ P ∧ False := by
  constructor
  intro h1
  constructor
  exfalso
  exact h1
  exact h1
  intro h1
  cases' h1 with h2 h3
  exact h3
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  cases' h1 with h3 h4
  cases' h2 with h5 h6
  constructor
  intro h5
  cases' h5 with h8 h9
  apply h5 at h9
  apply h3 at h8
  exact And.intro h8 h9
  intro h7
  cases' h7 with h8 h9
  apply h4 at h8
  apply h6 at h9
  exact And.intro h8 h9
  done

example : ¬(P ↔ ¬P) := by
  intro h1
  change P <-> P -> False at h1
  by_cases hP:P
  cases' h1 with h2 h3
  apply h2
  exact hP
  exact hP
  cases' h1 with h2 h3
  apply h2
  apply h3
  exact hP
  apply h3
  exact hP




  done
