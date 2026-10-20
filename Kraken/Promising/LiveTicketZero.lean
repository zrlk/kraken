/-
**Stage 3: `TicketLive 0`**, the official
ticket-lock liveness statement (promises allowed) at certification fuel `0`.

At fuel `0` the machine makes no promise and keeps no promise-holding
instruction step: `certify … 0` takes no instruction, so it reports no write
and certifies only a thread that already has no outstanding promise
(`certify_go_zero`). Every successor is therefore a promise-free instruction
step (`succs_zero`), every stuttering trace is promise-free
(`promiseFree_zero`), and `TicketLive 0` follows from the promise-free
theorem (`ticket_live_zero`, from `TicketPF.ticket_live_pf`).

This is the only fuel at which this file closes the existing `TicketLive`. At
positive fuel, `TicketLive fuel` is about the executable `certify`, whose
visited set ignores the remaining fuel (KNOWN_GAPS: `succs` is not monotone
in `fuel`). The search can miss a certification that exists, so a thread
holding a promise may have no certified step. The intended property, with
certification "some run within `fuel` empties the promise set", is stated
and proved separately.

ISA-neutral up to the last section.
-/
import Kraken.Promising.LiveTicketPF

namespace Kraken.Promising.Live.TicketZero

open Kraken Kraken.Promising Kraken.Promising.Live

variable {I : ISA}

private theorem foldl_inv0 {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_inv0 P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

/-! ## Certification at fuel `0` -/

/-- A certification result at fuel `0` for thread `t`: no write, and
`certified` only if `t` has no outstanding promise. -/
def CertZero (t : Thread I) (r : CertResult I) : Prop :=
  r.writes = [] ∧ (r.certified = true → t.prom = [])

/-- Every cache entry is a fuel-`0` result for its key. -/
def CacheZero (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I), cache[(t, tid, mem)]? = some r → CertZero t r

/-- **`certify.go` with no instruction left** adds no write and certifies only
a thread with no outstanding promise. -/
theorem certify_go_zero (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) :
    CertZero t (certify.go A tid 0 ({}, {}) (t, mem, [], false)).2 := by
  rw [certify.go]
  split
  · exact ⟨rfl, fun h => by cases h⟩
  dsimp only
  split
  · exact ⟨rfl, fun h => by cases h⟩
  by_cases hc : (!false && t.prom.isEmpty) = true
  · rw [ite_eq_left hc]
    have hp : t.prom = [] := by simpa using hc
    dsimp only
    split <;> exact ⟨rfl, fun _ => hp⟩
  · rw [ite_eq_right hc]
    dsimp only
    split <;> exact ⟨rfl, fun h => by cases h⟩

private theorem prod_beq_iff0 {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show (a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true]

theorem certify_zero [I.LawfulState] (A : Arch) {cache : CertCache I} (hc : CacheZero cache) (t : Thread I) (tid : Nat)
    (mem : Memory) : CertZero t (certify A cache t tid mem 0).1 ∧ CacheZero (certify A cache t tid mem 0).2 := by
  unfold certify
  split
  · rename_i r h
    exact ⟨hc t tid mem r h, hc⟩
  · have hr := certify_go_zero A tid t mem
    refine ⟨hr, fun t' tid' mem' r' h => ?_⟩
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      cases h
      have hb : (t == t') = true := ((prod_beq_iff0 _ _).mp heq).1
      obtain ⟨-, -, -, -, hp⟩ := (Thread.beq_iff t t').mp hb
      exact ⟨hr.1, fun h => hp ▸ hr.2 h⟩
    · exact hc t' tid' mem' r' h

/-- At fuel `0` no thread has a certified promise. -/
theorem certifiedPromises_zero [I.LawfulState] (A : Arch) {cache : CertCache I} (hc : CacheZero cache) (c : Config I) (tid : Nat) :
    (certifiedPromises A cache c tid 0).1 = [] ∧ CacheZero (certifiedPromises A cache c tid 0).2.2 := by
  unfold certifiedPromises
  split
  · exact ⟨rfl, hc⟩
  · rename_i t ht
    obtain ⟨hw, hc'⟩ := certify_zero A hc t tid c.mem
    generalize certify A cache t tid c.mem 0 = rc at hw hc'
    obtain ⟨r, cache'⟩ := rc
    refine ⟨?_, hc'⟩
    have hw0 : r.writes = [] := hw.1
    simp [hw0]

/-- A promise-free instruction step of some thread. -/
def InstrPF (A : Arch) (c c' : Config I) : Prop :=
  ∃ tid t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ .ok o ∈ outs ∧
    o.thread.prom = [] ∧ c' = c.withThread tid o.thread o.mem

theorem succsL_zero [I.LawfulState] {A : Arch} {mp : Option Nat} (c : Config I) (cache : CertCache I) (hc : CacheZero cache) :
    ∀ x ∈ (succsL A cache c 0 mp).1, InstrPF A c x.1 := by
  unfold succsL
  refine (foldl_inv0 (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
      CacheZero acc.2.2.2 ∧ ∀ x ∈ acc.1, InstrPF A c x.1) _ _ _ ⟨hc, fun _ h => by cases h⟩ ?_).2
  rintro ⟨next, bound, faults, cache⟩ tid - ⟨hc, hn⟩
  have key : ∀ (F : List (Config I × List TraceEv) × Bool × List String × CertCache I)
      (ps : List (Config I × TraceEv)), (CacheZero F.2.2.2 ∧ ∀ x ∈ F.1, InstrPF A c x.1) →
      (∀ y ∈ ps, y ∈ (certifiedPromises A F.2.2.2 c tid 0).1) →
      CacheZero (certifiedPromises A F.2.2.2 c tid 0).2.2 ∧
        ∀ x ∈ F.1.reverse ++ List.map (fun x => (x.1, [x.2])) ps, InstrPF A c x.1 := by
    intro F ps ⟨hF, hF1⟩ hps
    obtain ⟨hp0, hc'⟩ := certifiedPromises_zero A hF c tid
    refine ⟨hc', fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · exact hF1 x (List.mem_reverse.mp h)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      have := hps y hy
      rw [hp0] at this
      cases this
  have hsub : ∀ (ps : List (Config I × TraceEv)) (y : Config I × TraceEv),
      y ∈ (match mp, c.threads[tid]? with
        | some k, some t => if t.prom.length < k then ps else []
        | _, _ => ps) → y ∈ ps := by
    intro ps y hy
    split at hy
    · split at hy
      · exact hy
      · cases hy
    · exact hy
  simp only
  split
  · exact key _ _ ⟨hc, hn⟩ (hsub _)
  · rename_i outs hstep
    obtain ⟨t, ht, hstep⟩ := stepThread_eq_some hstep
    refine key _ _ (foldl_inv0 (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
        CacheZero acc.2.2.2 ∧ ∀ x ∈ acc.1, InstrPF A c x.1) _ _ _ ⟨hc, hn⟩ ?_) (hsub _)
    rintro ⟨next, bound, faults, cache⟩ o ho ⟨hc, hn⟩
    cases o with
    | error m => exact ⟨hc, hn⟩
    | ok o =>
      obtain ⟨hr, hc'⟩ := certify_zero A hc o.thread tid o.mem
      simp only
      split
      · rename_i hp
        refine ⟨hc, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨tid, t, outs, o, ht, hstep, ho, List.isEmpty_iff.mp hp, rfl⟩
        · exact hn x hx
      · split
        · rename_i hcert
          refine ⟨hc', fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨tid, t, outs, o, ht, hstep, ho, hr.2 hcert, rfl⟩
          · exact hn x hx
        · exact ⟨hc', hn⟩

/-- **At fuel `0` every successor is a promise-free instruction step.** -/
theorem succs_zero [I.LawfulState] {A : Arch} {c c' : Config I} (h : c' ∈ (succs A c 0).1) : InstrPF A c c' := by
  unfold succs at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact succsL_zero c {} (fun _ _ _ _ h => by simp at h) x hx

/-- **Every stuttering trace at fuel `0` is promise-free.** -/
theorem promiseFree_zero [I.LawfulState] {A : Arch} (tr : TraceS A 0 I) : PromiseFree A tr.cfg := by
  rintro i tid ⟨t, p, ht, -, he⟩
  have hlt := lt_size_of_get? ht
  have hprom : ∃ t', (tr.cfg (i + 1)).threads[tid]? = some t' ∧ t'.prom.length = t.prom.length + 1 :=
    ⟨_, by rw [he, Config.withThread_get? _ _ _ hlt, ite_eq_left rfl], by simp⟩
  rcases tr.step i with hm | ⟨-, hst⟩
  · obtain ⟨j, u, outs, o, hu, -, -, hp, he'⟩ := succs_zero hm
    obtain ⟨t', ht', hl⟩ := hprom
    rw [he', Config.withThread_get? _ _ _ (lt_size_of_get? hu)] at ht'
    split at ht'
    · cases ht'; rw [hp] at hl; simp at hl
    · rename_i hne
      rw [ht] at ht'; cases ht'; omega
  · obtain ⟨t', ht', hl⟩ := hprom
    rw [hst, ht] at ht'; cases ht'; omega

/-! ## The ticket lock at fuel `0` -/

open Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker)

/-- **`TicketLive 0`**: the official ticket-lock liveness statement
(`WeakFair ∧ MemFair`, promises allowed) at certification fuel `0`, on a valid
layout of `tkWorker`. At fuel `0` every trace is promise-free
(`promiseFree_zero`), so this is `TicketPF.ticket_live_pf 0`. -/
theorem ticket_live_zero [layout : _root_.Layout] [Executable.ValidLayout (layout tkWorker)] :
    Ticket.TicketLive 0 := by
  intro N x o c states initMem hs tr h0 ⟨hwf, hmf⟩
  exact TicketPF.ticket_live_pf 0 N x o c states initMem hs tr h0 ⟨hwf, hmf, promiseFree_zero tr⟩

/-- `ticket_live_zero` at the concrete layout `TicketPF.tkLayout`. -/
theorem ticket_live_zero_concrete : @Ticket.TicketLive TicketPF.tkLayout 0 :=
  @ticket_live_zero TicketPF.tkLayout TicketPF.tkValid

end Kraken.Promising.Live.TicketZero

#print axioms Kraken.Promising.Live.TicketZero.ticket_live_zero
