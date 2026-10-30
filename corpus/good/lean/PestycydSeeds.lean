universe u

-- 1. nested inductive with an index
inductive ITree (α : Type u) : Nat → Type u where
  | leaf : α → ITree α 0
  | node : List (ITree α 0) → ITree α 1

def ITree.size : ITree α n → Nat
  | .leaf _ => 1
  | .node ts => ts.length + 1

theorem itree_size : (ITree.node [.leaf 1, .leaf 2] : ITree Nat 1).size = 3 := rfl

def ITree.sum : {n : Nat} → ITree Nat n → Nat
  | _, .leaf a => a
  | _, .node ts => go ts
where go : List (ITree Nat 0) → Nat
  | [] => 0
  | t :: ts => t.sum + go ts

theorem itree_sum : (ITree.node [.leaf 4, .leaf 5] : ITree Nat 1).sum = 9 := by decide

-- 2. recursive Prop families
inductive Ev : Nat → Prop where
  | zero : Ev 0
  | step : Ev n → Ev (n + 2)

theorem ev4 : Ev 4 := .step (.step .zero)

theorem ev_double : ∀ n, Ev (n + n)
  | 0 => .zero
  | n + 1 => by
      have h := ev_double n
      have : n + 1 + (n + 1) = n + n + 2 := by omega
      rw [this]; exact .step h

inductive WF (r : α → α → Prop) : α → Prop where
  | intro (x : α) : (∀ y, r y x → WF r y) → WF r x

theorem wf_inv {r : α → α → Prop} {x : α} (h : WF r x) : ∀ y, r y x → WF r y :=
  WF.rec (motive := fun x _ => ∀ y, r y x → WF r y) (fun _ h _ => h) h

-- 3. universe-polymorphic quotient
def Par (α : Sort u) : α → α → Prop := fun _ _ => True

def PQ (α : Sort u) := Quot (Par α)

def PQ.const {α : Sort u} {β : Sort v} (b : β) : PQ α → β :=
  Quot.lift (fun _ => b) (fun _ _ _ => rfl)

theorem pq_const_mk {α : Sort u} {β : Sort v} (a : α) (b : β) :
    PQ.const b (Quot.mk (Par α) a) = b := rfl

theorem pq_all_eq {α : Sort u} (x y : PQ α) : x = y :=
  Quot.ind (β := fun x => x = y)
    (fun a => Quot.ind (β := fun y => Quot.mk _ a = y) (fun _ => Quot.sound trivial) y) x

theorem ev_inv : Ev (n + 2) → Ev n
  | .step h => h

theorem not_ev1 : ¬ Ev 1 := fun h => nomatch h

theorem ev_rec_use : ∀ n, Ev n → n ≠ 1 :=
  fun _ h => Ev.rec (motive := fun n _ => n ≠ 1) (by decide) (fun _ _ => by simp) h

theorem prop_rec_bundle :
    Ev 4 ∧ (Ev 6 → Ev 4) ∧ ¬ Ev 1 ∧ (∀ (r : Nat → Nat → Prop) x, WF r x → ∀ y, r y x → WF r y) :=
  ⟨ev4, ev_inv, not_ev1, fun _ _ h => wf_inv h⟩

theorem nested_indexed_bundle :
    (ITree.node [.leaf 1, .leaf 2] : ITree Nat 1).size = 3 ∧
    (ITree.node [.leaf 4, .leaf 5] : ITree Nat 1).sum = 9 :=
  ⟨itree_size, itree_sum⟩

theorem quot_universe_bundle :
    PQ.const (α := Nat) (5 : Nat) (Quot.mk _ 0) = 5 ∧ ∀ (x y : PQ Prop), x = y :=
  ⟨pq_const_mk 0 5, pq_all_eq⟩
