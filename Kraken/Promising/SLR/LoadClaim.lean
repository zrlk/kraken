/-
**Design prototype.** A *ticket dispenser*: the
memory-arbitrated "load claim" that the `ldadda` ticket lock
(`Kraken/Examples/LockFree/AArch64/ticketlock2.kl`) needs).

## The problem

The take rule (`SLR/TakeRule*.lean`) lets the spinning `ldar owner` take the
slot `(owner, ts), ι` of an acquire id `ι` it holds. The holder of ticket
`v` must hold the id `tk v` whose slot carries the critical-section resource
at the `owner` message of value `v`. Who gets `tk v` is decided by the RMW
chain on `next` (the successful RMW that reads `next = v`). With `ldadda`
the writes to `next` are relaxed, so they may be promised; a promised relaxed
message must be pure for `W.rel next` (`PromisePure'`), and `Erase.relAcq`
then forces every slot predicate of `next` to accept the unit resource, so
`next`'s messages cannot carry exact token slots.

## The design (no slots on `next`)

- The tokens `tk n` (`n < N`, acquire ids of `owner`) live in one
  **dispenser slot** `((owner, 0), ιD)` on the initial `owner` message, whose
  id `ιD` is an **update id** of `owner`. So the slots of `tk n` are
  reachable by every thread (`CanAcq.upd`, then `CanAcq.step`): handing a
  token to a thread never grows its reach (K1), exactly as for update slots.
- A successful RMW on `next` that reads a message of value `n` moves `tk n`
  from the dispenser into the thread (`Dispenser.handGhost`, in
  `LoadClaimErase.lean`).
- What the existing `Erase` cannot give is **protection**: under `Erase` any
  thread's ghost step may move a token out of the dispenser. The new clause
  `Dispenser.TicketInv` pins the dispenser's contents to the claims: the
  dispenser holds `tk n` iff no claim of `next` read value `n`
  (`Dispenser.Handed`). Together with **`MonoX`** (the values of `next`'s
  messages strictly increase with the timestamp; this rules out a second
  message of an already handed value, promises included), the claimant of
  value `n` always finds `tk n` in the dispenser.
- `EraseT D := Erase ∧ TicketInv D` is the extended erasure. It is
  additive: `EraseT → Erase` is `.1`. What the Theorem 1′ chain needs from
  the extension (it depends only on memory, not on pending marks, and it
  survives a promise of a fresh value) is `ExtLaws`, proved here for
  `TicketInv` (`ticketInv_extLaws`).

## Limits (phase 1 of the prototype)

- Bounded: tokens `tk n` exist for `n < N` only (preallocated ids; the
  32-bit wraparound caveat of the take prototype: `MonoX` fails after `2^w`
  increments).
- One dispenser per program (one `next`/`owner` pair).
- `MonoX` makes every promise to `next` an obligation (a fresh, larger
  value): the a-posteriori analogue of `PromisePure'` (`FreshPromises`).

Nothing imports this file.
-/
import Kraken.Promising.SLR.TakeRuleErase

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

theorem lc_read?_le_last {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    t ≤ m.last := by
  unfold Memory.read? at h
  split at h
  · next h0 => subst h0; exact Nat.zero_le _
  · split at h
    · rename_i w hw; exact m.last_le_of_get?_eq_some hw
    · cases h

/-! ## Tokens as resources -/

/-- `r` without the acquire id `(o, ι)`. -/
def dropTk (r : Res) (o : Loc) (ι : PredId) : Res where
  wr := r.wr
  acq y j := if y = o ∧ j = ι then 0 else r.acq y j

/-- The resource holding exactly the acquire id `(o, ι)`. -/
def tok (o : Loc) (ι : PredId) : Res where
  wr := fun _ => Perm.unit
  acq y j := if y = o ∧ j = ι then 1 else 0

theorem dropTk_op_tok {r : Res} {o : Loc} {ι : PredId} (h : r.acq o ι = 1) :
    (dropTk r o ι).op (tok o ι) = r := by
  apply Res.ext
  · funext y; simp only [Res.op, dropTk, tok, Perm.op_unit]
  · funext y j
    simp only [Res.op, dropTk, tok]
    by_cases hy : y = o ∧ j = ι
    · obtain ⟨rfl, rfl⟩ := hy; simp [h]
    · simp only [hy, ↓reduceIte, Nat.add_zero]

theorem tok_wr (o : Loc) (ι : PredId) (y : Loc) : (tok o ι).wr y = Perm.unit := rfl

theorem op_tok_wr (r : Res) (o : Loc) (ι : PredId) : (r.op (tok o ι)).wr = r.wr := by
  funext y; simp only [Res.op, tok, Perm.op_unit]

/-! ## The dispenser -/

/-- A **ticket dispenser**: the ticket counter `x` (`next`), the turn location
`o` (`owner`), the dispenser slot's update id `ιD` (on `o`), and the ticket
ids `tk n` (acquire ids of `o`) for `n < N`. -/
structure Dispenser where
  x : Loc
  o : Loc
  ιD : PredId
  tk : Nat → PredId
  N : Nat
  xo : x ≠ o
  tkInj : ∀ n m, n < N → m < N → tk n = tk m → n = m
  tkNe : ∀ n, n < N → tk n ≠ ιD

namespace Dispenser

variable (D : Dispenser)

/-- The dispenser slot's message: the initial message of `o`. -/
def key : Key := (D.o, 0)

/-- `s` is the dispenser slot. -/
def IsDisp (s : Slot) : Prop := s.key = D.key ∧ s.id = D.ιD

instance (s : Slot) : Decidable (D.IsDisp s) := by unfold IsDisp; infer_instance

/-- Ticket `n` has been handed out: some claim of `x` read a message of
value `n`. -/
def Handed (g : Ghost) (mem : Memory) (n : Nat) : Prop :=
  ∃ tr tw v, ((D.x, tr), tw) ∈ g.claims ∧ mem.read? D.x tr = some v ∧ v.toNat = n

/-- The values of `x`'s messages (the initial message included) strictly
increase with the timestamp. -/
def MonoX (mem : Memory) : Prop :=
  ∀ ts₁ ts₂ v₁ v₂, ts₁ < ts₂ → mem.read? D.x ts₁ = some v₁ → mem.read? D.x ts₂ = some v₂ →
    v₁.toNat < v₂.toNat

/-- **The dispenser invariant**, with an exception set `ex` (the value whose
claim has just been recorded and whose token is still in the dispenser,
between `Erase.rmw` and the hand-out): the dispenser slot exists and holds
`tk n` exactly when ticket `n` is not handed out (or `n ∈ ex`); `ιD` is an
update id of `o` and the dispenser's message is never claimed; the
dispenser's predicate is closed under dropping tokens. -/
structure DispOK (g : Ghost) (mem : Memory) (ex : Nat → Prop) : Prop where
  slot : ∃ s ∈ g.u, D.IsDisp s ∧ ∀ n, n < D.N →
    (D.Handed g mem n ∧ ¬ ex n → s.res.acq D.o (D.tk n) = 0) ∧
    (¬ (D.Handed g mem n ∧ ¬ ex n) → s.res.acq D.o (D.tk n) = 1)
  upd : D.ιD ∈ g.upd D.o
  unclaimed : ¬ g.Claimed D.key
  dPred : ∀ v m V r ι, (g.acqPred D.ιD).P v m V r → (g.acqPred D.ιD).P v m V (dropTk r D.o ι)

/-- **The ticket invariant**: the dispenser invariant (no exception) and
`MonoX`. -/
structure TicketInv (g : Ghost) (c : Config I) : Prop where
  disp : D.DispOK g c.mem (fun _ => False)
  mono : D.MonoX c.mem

end Dispenser

/-- **The extended erasure** `EraseT D = Erase ∧ TicketInv D` (additive:
`EraseT → Erase` is `.1`). -/
def EraseT (D : Dispenser) (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) : Prop :=
  Erase rF g T c ∧ D.TicketInv g c

theorem EraseT.erase {D : Dispenser} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (h : EraseT D rF g T c) : Erase rF g T c := h.1

/-! ## Memory facts -/

namespace Dispenser

variable {D : Dispenser}

/-- `MonoX` makes values of `x` injective in the timestamp. -/
theorem MonoX.ts_eq {mem : Memory} (h : D.MonoX mem) {ts₁ ts₂ : Time} {v₁ v₂ : Val}
    (h₁ : mem.read? D.x ts₁ = some v₁) (h₂ : mem.read? D.x ts₂ = some v₂) (hv : v₁.toNat = v₂.toNat) :
    ts₁ = ts₂ := by
  rcases Nat.lt_trichotomy ts₁ ts₂ with hlt | heq | hgt
  · have := h _ _ _ _ hlt h₁ h₂; omega
  · exact heq
  · have := h _ _ _ _ hgt h₂ h₁; omega

/-- `MonoX` on a prefix. -/
theorem MonoX.of_prefix {mem mem' : Memory} (h : D.MonoX mem') (hp : mem.Prefix mem') : D.MonoX mem := by
  intro ts₁ ts₂ v₁ v₂ hlt h₁ h₂
  have hle₁ := lc_read?_le_last h₁
  have hle₂ := lc_read?_le_last h₂
  exact h ts₁ ts₂ v₁ v₂ hlt (by rw [hp.read? hle₁]; exact h₁) (by rw [hp.read? hle₂]; exact h₂)

/-- `w` is a **fresh** write for the dispenser at `mem`: a write to another
location, or a write to `x` of a value above every value of `x` in `mem`. -/
def Fresh (D : Dispenser) (mem : Memory) (w : Msg) : Prop :=
  w.loc = D.x → ∀ ts v, mem.read? D.x ts = some v → v.toNat < w.val.toNat

/-- **`MonoX` survives appending a fresh message.** -/
theorem MonoX.append {mem : Memory} {w : Msg} (h : D.MonoX mem) (hf : D.Fresh mem w) :
    D.MonoX (mem.append w).1 := by
  have hp := Memory.Prefix.append mem w
  have hnew : ∀ ts v, (mem.append w).1.read? D.x ts = some v → mem.last < ts → w.loc = D.x ∧ v = w.val := by
    intro ts v hv hlt
    have hle := lc_read?_le_last hv
    rw [Memory.last_append] at hle
    obtain rfl : ts = mem.last + 1 := by omega_t
    unfold Memory.read? at hv
    rw [Memory.get?_append_last] at hv
    simp only [Nat.add_one_ne_zero, ↓reduceIte] at hv
    split at hv
    · next hb => simp only [beq_iff_eq] at hb; simp only [Option.some.injEq] at hv; exact ⟨hb, hv.symm⟩
    · cases hv
  intro ts₁ ts₂ v₁ v₂ hlt h₁ h₂
  rcases Nat.lt_or_ge mem.last ts₂ with hl₂ | hl₂
  · obtain ⟨hloc, rfl⟩ := hnew ts₂ v₂ h₂ hl₂
    rcases Nat.lt_or_ge mem.last ts₁ with hl₁ | hl₁
    · have h1 := lc_read?_le_last h₁; have h2 := lc_read?_le_last h₂
      rw [Memory.last_append] at h1 h2; omega_t
    · rw [hp.read? hl₁] at h₁
      exact hf hloc ts₁ v₁ h₁
  · have hl₁ : ts₁ ≤ mem.last := by omega_t
    rw [hp.read? hl₁] at h₁; rw [hp.read? hl₂] at h₂
    exact h ts₁ ts₂ v₁ v₂ hlt h₁ h₂

/-- `Handed` is stable under memory growth (claimed keys are in memory). -/
theorem handed_prefix {g : Ghost} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hk : ∀ k tw, (k, tw) ∈ g.claims → k.2 ≤ mem.last) (n : Nat) :
    D.Handed g mem' n ↔ D.Handed g mem n := by
  constructor
  · rintro ⟨tr, tw, v, hc, hr, hv⟩
    exact ⟨tr, tw, v, hc, by rw [← hp.read? (hk _ _ hc)]; exact hr, hv⟩
  · rintro ⟨tr, tw, v, hc, hr, hv⟩
    exact ⟨tr, tw, v, hc, by rw [hp.read? (hk _ _ hc)]; exact hr, hv⟩

/-- Claimed keys are in memory (`Erase.claimsAt`). -/
theorem claims_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c) :
    ∀ k tw, (k, tw) ∈ g.claims → k.2 ≤ c.mem.last := by
  intro k tw hk
  obtain ⟨hlt, w, hw, -⟩ := E.claimsAt k tw hk
  have := c.mem.last_le_of_get?_eq_some hw
  omega_t

/-- `DispOK` only depends on `mem` through `Handed`. -/
theorem DispOK.congr_handed {g : Ghost} {mem mem' : Memory} {ex : Nat → Prop}
    (h : D.DispOK g mem ex) (hh : ∀ n, D.Handed g mem' n ↔ D.Handed g mem n) : D.DispOK g mem' ex := by
  obtain ⟨⟨s, hs, hd, hn⟩, hu, hc, hP⟩ := h
  refine ⟨⟨s, hs, hd, fun n hlt => ?_⟩, hu, hc, hP⟩
  rw [hh n]; exact hn n hlt

/-- `DispOK` ignores pending marks. -/
theorem DispOK.pend {g : Ghost} {mem : Memory} {ex : Nat → Prop} (P : List Time) :
    D.DispOK { g with pend := P } mem ex ↔ D.DispOK g mem ex :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

end Dispenser

/-! ## What the Theorem 1′ chain needs from an erasure extension -/

/-- **The laws an erasure extension `X` must satisfy** for a Theorem 1′ chain
over `Erase ∧ X` (the interface of the proposed chain change; `Fresh` is the
extra a-posteriori obligation on promises, the analogue of `PromisePure'`):

- `mem`: `X` depends on the configuration only through its memory
  (`Config.VirtualOf`, `Fulfilled`, `withThread` keep memory);
- `pend`: `X` ignores pending marks (`Erase.pendingOfFulfil`);
- `promise`: a promise of a message satisfying `Fresh` keeps `X`
  (`Erase.promise`, case (d2));
- `init`: (stated per program).

Weakening/validation (`T`) are free: `X` does not mention `T`. -/
structure ExtLaws (X : Ghost → Config I → Prop) (Fresh : Ghost → Memory → Msg → Prop) : Prop where
  mem : ∀ g (c c' : Config I), c.mem = c'.mem → X g c → X g c'
  pend : ∀ g (c : Config I) (P : List Time), X g c → X { g with pend := P } c
  promise : ∀ rF g T (c : Config I) tid t w, Erase rF g T c → c.threads[tid]? = some t → X g c →
    Fresh g c.mem w → X g (Promised c tid t w)

namespace Dispenser

variable {D : Dispenser}

theorem ticketInv_mem {g : Ghost} {c c' : Config I} (hm : c.mem = c'.mem) (h : D.TicketInv g c) :
    D.TicketInv g c' :=
  ⟨by rw [← hm]; exact h.disp, by rw [← hm]; exact h.mono⟩

/-- **`TicketInv` survives a fresh promise.** -/
theorem TicketInv.promise {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    {t : Thread I} {w : Msg} (E : Erase rF g T c) (_ht : c.threads[tid]? = some t) (h : D.TicketInv g c)
    (hf : D.Fresh c.mem { w with tid }) : D.TicketInv g (Promised c tid t w) := by
  refine ⟨h.disp.congr_handed (handed_prefix (Memory.Prefix.append _ _) (claims_le E)), ?_⟩
  exact h.mono.append hf

/-- **The ticket invariant satisfies the extension laws**, with `Fresh` the
freshness of the promised message (the promise appends `{ w with tid }`). -/
theorem ticketInv_extLaws (D : Dispenser) :
    ExtLaws (I := I) (fun g c => D.TicketInv g c) (fun _ mem w => ∀ tid, D.Fresh mem { w with tid }) where
  mem := fun _ _ _ hm h => ticketInv_mem hm h
  pend := fun _ _ P h => ⟨(DispOK.pend P).mpr h.disp, h.mono⟩
  promise := fun _ _ _ _ _ _ _ E ht h hf => h.promise E ht (hf _)

end Dispenser

end Kraken.Promising.SLR
