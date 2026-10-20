/-
**The purity-and-phase environment of a single-RMW dispenser program**
(ISA-neutral core). Moved verbatim from `EnvG/DispenserPureA64.lean` so that the
x64 side can reuse it (`TicketX.dispPureX` and
`TicketX.TreeJ.dispX` are now these definitions); the names stay in
`TicketLock` (unchanged fully-qualified names).

- `dispPure A Q x N`: state `Bool` (`true`: after the hand-out). `ok` is
  `relPureQ`'s condition, no store to `x`, and an RMW on `x` only before the
  hand-out, writing `old + 1` below `N`; an RMW on `x` that writes moves to
  `true`, every other step keeps the phase. `Skips`.
- `TreeJ.disp`: the tree judgment `RelWrites ∧ All (∃ b, Post · b) ∧ (BefX`
  at `false`) `∧ (AftX` at `true)`.

The AArch64 specification (`DispSpec`, `dispSpec_step`, ...) stays in
`EnvG/DispenserPureA64.lean`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnv
import Kraken.Promising.SLR.DispenserRun

open Kraken Kraken.Promising
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

namespace Kraken.Promising.SLR.EnvG.TicketLock

/-! ## The environment -/

/-- **The purity-and-phase environment** of a single-RMW dispenser program
on `x` with bound `N`: `relPureQ A Q`, no store to `x`, an RMW on `x` only
before the hand-out (state `false`) and writing `old + 1` below `N`; a
writing RMW on `x` moves the state to `true`. -/
abbrev dispPure (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) : SharedEnv where
  State := Bool
  ok a b := match a with
    | .load .. => True
    | .store k _ addr n v => (A.storeKind k ≠ .rel → Q ⟨addr, n⟩ v) ∧ (⟨addr, n⟩ : Loc) ≠ x
    | .rmw k addr n op => (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q ⟨addr, n⟩ new) ∧
        ((⟨addr, n⟩ : Loc) = x → b = false ∧ ∀ old new, op old = some new → old.toNat < N → new.toNat = old.toNat + 1)
    | .fence _ => True
  step a b r b' := match a, r with
    | .rmw _ addr n op, old => b' = (b || (decide ((⟨addr, n⟩ : Loc) = x) && (op old).isSome))
    | _, _ => b' = b

variable {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat}

instance : (dispPure A Q x N).Skips := ⟨fun _ _ => ⟨trivial, fun _ h => h⟩⟩

@[simp] theorem dispPure_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {b : Bool} :
    (dispPure A Q x N).ok (.load k xcl addr n) b ↔ True := Iff.rfl

@[simp] theorem dispPure_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (dispPure A Q x N).ok (.store k xcl addr n v) b ↔ (A.storeKind k ≠ .rel → Q ⟨addr, n⟩ v) ∧ (⟨addr, n⟩ : Loc) ≠ x :=
  Iff.rfl

@[simp] theorem dispPure_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {b : Bool} :
    (dispPure A Q x N).ok (.rmw k addr n op) b ↔
      (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q ⟨addr, n⟩ new) ∧
        ((⟨addr, n⟩ : Loc) = x → b = false ∧ ∀ old new, op old = some new → old.toNat < N → new.toNat = old.toNat + 1) :=
  Iff.rfl

@[simp] theorem dispPure_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b b' : Bool} :
    (dispPure A Q x N).step (.load k xcl addr n) b v b' ↔ b' = b := Iff.rfl

@[simp] theorem dispPure_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {r : Bool} {b b' : Bool} :
    (dispPure A Q x N).step (.store k xcl addr n v) b r b' ↔ b' = b := Iff.rfl

@[simp] theorem dispPure_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    {b b' : Bool} :
    (dispPure A Q x N).step (.rmw k addr n op) b old b' ↔
      b' = (b || (decide ((⟨addr, n⟩ : Loc) = x) && (op old).isSome)) := Iff.rfl

/-- **The tree judgment of `dispPure`**: `RelWrites`, every leaf in some
phase, `BefX` before the hand-out and `AftX` after it. -/
def TreeJ.disp (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) {σ : Type} (Post : σ → Bool → Prop) :
    TreeJ (dispPure A Q x N) σ where
  W t b := t.RelWrites A Q ∧ t.All (fun s => ∃ b, Post s b) ∧
    (b = false → t.BefX x N (Post · false) (Post · true)) ∧ (b = true → t.AftX x (Post · true))
  Post s b := Post s b
  done {s g} h := by
    cases g
    · exact ⟨trivial, ⟨_, h⟩, fun _ => .inl h, fun h' => nomatch h'⟩
    · exact ⟨trivial, ⟨_, h⟩, (fun h' => nomatch h'), fun _ => h⟩
  fault := ⟨trivial, trivial, fun _ => trivial, fun _ => trivial⟩
  choose h := ⟨fun i => (h i).1, fun i => (h i).2.1, fun hb i => (h i).2.2.1 hb, fun hb i => (h i).2.2.2 hb⟩
  load _ h := ⟨fun v => (h v _ rfl).1, fun v => (h v _ rfl).2.1, fun hb v => (h v _ rfl).2.2.1 hb,
    fun hb v => (h v _ rfl).2.2.2 hb⟩
  store hok h := ⟨⟨hok.1, fun r => (h r _ rfl).1⟩, fun r => (h r _ rfl).2.1, fun hb => ⟨hok.2, fun r => (h r _ rfl).2.2.1 hb⟩,
    fun hb => ⟨hok.2, fun r => (h r _ rfl).2.2.2 hb⟩⟩
  rmw {k noRet addr n op ret g} hok h := by
    refine ⟨⟨hok.1, fun v => (h v _ rfl).1⟩, fun v => (h v _ rfl).2.1, fun hb v => ⟨fun hx new hop => ?_, fun hn => ?_⟩,
      fun hb => ⟨fun hx => absurd (hok.2 hx).1 (by rw [hb]; decide), fun v => ?_⟩⟩
    · refine ⟨(hok.2 hx).2 v new hop, (h v true ?_).2.2.2 rfl⟩
      show true = (g || (decide ((⟨addr, n⟩ : Loc) = x) && (op v).isSome))
      simp [hx, hop]
    · refine (h v false ?_).2.2.1 rfl
      show false = (g || (decide ((⟨addr, n⟩ : Loc) = x) && (op v).isSome))
      by_cases hx : (⟨addr, n⟩ : Loc) = x
      · simp [hb, hx, hn hx]
      · simp [hb, hx]
    · refine (h v true ?_).2.2.2 rfl
      show true = (g || (decide ((⟨addr, n⟩ : Loc) = x) && (op v).isSome))
      simp [hb]
  fence _ h := ⟨fun ⟨⟩ => (h _ rfl).1, fun ⟨⟩ => (h _ rfl).2.1, fun hb ⟨⟩ => (h _ rfl).2.2.1 hb,
    fun hb ⟨⟩ => (h _ rfl).2.2.2 hb⟩

end Kraken.Promising.SLR.EnvG.TicketLock
