/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h
  left
  exact h
  done

example : Q → P ∨ Q := by
  intro h
  right
  exact h
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1 h2 h3
  cases' h1 with h5 h4 --/ regardless of which of q and p is true statement holds
  apply h2 at h5
  exact h5

  apply h3 at h4
  exact h4

  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases' h1 with h2 h3
  right
  exact h2
  left
  exact h3
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h1
  cases' h1 with h2 h3
  cases' h2 with h1 h2
  left
  exact h1
  right
  left
  exact h2
  right
  right
  exact h3
  intro h1
  cases' h1 with h2 h3
  left
  left
  exact h1
  cases' h3 with h4 h5
  left
  right
  exact h4
  right
  exact h5
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases' h3 with h4 h5
  apply h1 at h4
  left
  exact h4
  apply h2 at h5
  right
  exact h5
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases' h2 with h3 h3
  apply h1 at h3
  left
  exact h3
  right
  exact h3
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  constructor
  intro h3
  cases' h1 with h1a h1b
  cases' h3 with h3a h3b
  apply h1a at h3a
  left
  exact h3a
  cases' h2 with h2a h2b
  apply h2a at h3b
  right
  exact h3b
  intro h3
  cases' h3 with h3a h3b
  cases' h1 with h1a h1b
  apply h1b at h3a
  apply h1a at h3a
  apply h1b at h3a
  left
  exact h3a
  cases' h2 with h2a h2b
  apply h2b at h3b
  right
  exact h3b
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h1
  change P ∨ Q -> False at h1
  constructor
  intro h2
  apply h1
  left
  exact h2
  intro h2
  apply h1
  right
  exact h2
  intro h1
  intro h2
  cases' h1 with h1a h1b
  change P -> False at h1a
  change Q -> False at h1b
  cases' h2 with h2a h2b
  apply h1a
  exact h2a
  apply h1b
  exact h2b
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  -- Prove ¬(P ∧ Q) → ¬P ∨ ¬Q
  intro h
  by_cases hp : P
  -- Case 1: Assume P is true, so we need to show ¬Q.
  right
  intro hq
  apply h
  constructor
  exact hp
  exact hq
  -- Case 2: Assume P is false, so ¬P holds.
  left
  exact hp

  -- Prove Second Side of constructor
  intro h1
  intro h2
  cases' h1 with p q
  cases' h2 with h3  h4
  apply p
  exact h3
  cases' h2 with p q2
  apply q
  exact q2

  done
