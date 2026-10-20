/-
**Theorem 1′ over an extended erasure `Erase ∧ X`, proved**.

`SLR/LoadClaimChain.lean` states `Theorem1IIPureX' G GV K X Fresh` (open
there). The Theorem 1′ chain is generic in its erasure and in the promise
obligation (`Theorem1IIPureXS'`, `ChainExt`, `SLR/Theorem1Proof.lean`;
`theorem1IIPureXS'`, `SLR/Theorem1Final.lean`). Here:

- `XPromiseLaw X Fresh`: the one law the chain needs of the extension `X`:
  a promise whose message is `Fresh` keeps `X` (case (d2)). Steps of the
  threads keep `X` by their tokens (`NPSafeP (modelX I X)`); `X` does not
  mention the exemption set, so re-targeting is free.
- `chainExt_X`: `ChainExt (Erase ∧ X) (pure ∧ Fresh)` from the law.
- `theorem1IIPureX'`: `Theorem1IIPureX'` for every `X`, `Fresh` with the law
  (and `GuardOK`/`K2OK` as `theorem1IIPure'`), from `theorem1IIPureXS'` at
  `S := StepGuard.top _`.
- `ticket_xPromiseLaw`, `theorem1IIPureX'_ticket`, `theorem1IIPureT`: the
  ticket instance (`TicketInv D`, `D.Fresh`; `Dispenser.TicketInv.promise`),
  with `EraseT D` at the virtual configuration (`theorem1IIPureT_of_X`).
-/
import Kraken.Promising.SLR.LoadClaimChain

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- **The promise law of an extension `X`** for the obligation `Fresh`: a
promise (by a thread of `c`, at an erased configuration) of a message that
is `Fresh` for the memory before it keeps `X`. -/
def XPromiseLaw (X : Ghost → Config I → Prop) (Fresh : Memory → Msg → Prop) : Prop :=
  ∀ (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) (tid : Nat) (t : Thread I) (w : Msg),
    Erase rF g T c → c.threads[tid]? = some t → X g c → Fresh c.mem { w with tid } → X g (Promised c tid t w)

/-- **`Erase ∧ X` and purity with freshness satisfy the chain's laws.** -/
theorem chainExt_X {X : Ghost → Config I → Prop} {Fresh : Memory → Msg → Prop} (hX : XPromiseLaw X Fresh) :
    ChainExt (I := I) (fun rF g T c => Erase rF g T c ∧ X g c)
      (fun rel mem w => Pred.Pure (rel w.loc) w.val ∧ Fresh mem w) where
  toErase h := h.1
  retarget h e := ⟨e, h.2⟩
  pure h := h.1
  promise h ht e ob := ⟨e, hX _ _ _ _ _ _ _ h.1 ht h.2 ob.2⟩

/-- **Theorem 1′ over the extended erasure `Erase ∧ X`** (`Theorem1IIPureX'`,
`SLR/LoadClaimChain.lean`), for every extension `X` whose promise law holds
for the obligation `Fresh`. -/
theorem theorem1IIPureX' {G GV : PrepayGuard I} {K : K2Frame (model I)} {X : Ghost → Config I → Prop}
    {Fresh : Memory → Msg → Prop} (hX : XPromiseLaw X Fresh) (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPureX' G GV K X Fresh A fuel := by
  intro B states initMem rF g hNT E hX0 hpend hpure hfresh hsafe c hc hlive
  obtain ⟨v, rF', g', hv, ⟨E', hX'⟩, hle, hB⟩ :=
    theorem1IIPureXS' (S := StepGuard.top _) (chainExt_X hX) GOK GVOK hGV KOK A fuel B states initMem rF g hNT
      ⟨E, hX0⟩ hpend
      (fun π h0 hf J hJ j t pw ht hw hJ1 hn =>
        ⟨hpure π h0 hf J hJ j t pw ht hw hJ1 hn, hfresh π h0 hf J hJ j t pw ht hw hJ1 hn⟩)
      (fun tid htid n m => NPSafeP.toS (StepGuard.top _) (hsafe tid htid n m)) c hc hlive
  exact ⟨v, rF', g', hv, E', hX', hle, hB⟩

/-- **The ticket invariant's promise law** (`Dispenser.TicketInv.promise`). -/
theorem ticket_xPromiseLaw (D : Dispenser) : XPromiseLaw (I := I) (fun g c => D.TicketInv g c) D.Fresh :=
  fun _ _ _ _ _ _ _ E ht h hf => h.promise E ht hf

/-- `Theorem1IIPureX'` for the ticket invariant. -/
theorem theorem1IIPureX'_ticket {G GV : PrepayGuard I} {K : K2Frame (model I)} (D : Dispenser)
    (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPureX' G GV K (fun g c => D.TicketInv g c) D.Fresh A fuel :=
  theorem1IIPureX' (ticket_xPromiseLaw D) GOK GVOK hGV KOK A fuel

/-- **The ticket instance, unconditional** (`theorem1IIPureT_of_X` with
`theorem1IIPureX'_ticket`): a ticket program whose threads are `NPSafeP` at
`modelT D`, whose initial ghost satisfies the ticket invariant and whose
promises are pure or fulfilled by a release store, and `Fresh`, gets
`EraseT D` at the virtual configuration. -/
theorem theorem1IIPureT {G GV : PrepayGuard I} {K : K2Frame (model I)} (D : Dispenser)
    (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) (KOK : K2OK (model I) K)
    [I.LawfulState] {A : Arch} {fuel : Nat}
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val)) (rF : Nat → Res)
    (g : Ghost) (hNT : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : EraseT D rF g (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g.pend)
    (hpure : PromisePure' G A fuel states initMem g.rel) (hfresh : PromiseFresh' G A fuel states initMem D.Fresh)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (modelT I D) A B tid G K n m True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hlive : c.Live A fuel) :
    ∃ v rF' g', c.VirtualOfG GV A v ∧ EraseT D rF' g' (fun _ => False) v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' :=
  theorem1IIPureT_of_X D (theorem1IIPureX'_ticket D GOK GVOK hGV KOK A fuel) B states initMem rF g hNT E hpend
    hpure hfresh hsafe c hc hlive

#print axioms chainExt_X
#print axioms theorem1IIPureX'
#print axioms theorem1IIPureX'_ticket
#print axioms theorem1IIPureT

end Kraken.Promising.SLR
