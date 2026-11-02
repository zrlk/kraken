/-
**hello.w on x86-64: the pieces of the `spawn` obligation** (the twin of `Spike/Lib/HelloSpawn.lean`; x86-64
wake's `X64WakeSpawn` and `X64WakeStart` at hello's worker side `X64HelloW1.WSideH`): main's `clone` into slot 1 is
the source `spawn`, a source run with no observable event to `Post` after `afterClone`.

- `PktH`: the spawned worker's packet (the slice's three words, the pointer word `D.cw w`, main's id).
- `pt1_startH`: hello's worker relation `PT1h` at the spawn (given the buffer's `BufV`): the child in `Wi`, the
  source worker at `.tail "worker" …` on one frame with no type variables, in the print phase
  (`X64HelloW1.printPh_spawn`), no promise.
- `post_startH`: `X64WakeOwnX.post_startOXW` with `Q.PT1 = PT1hE D` (at `PT1h`): each thread owns its TCB self
  word (`Q.own = wakeOwnXW T W`), both in the clone's own list.
- `SpawnPreH`: the pre side's facts at the clone (`X64WakeSpawn.SpawnPre`'s, the spawned worker's at hello's
  packet), with `self`: both TCB self words at the clone when the own map is `X64WakeOwnX.wakeOwnXW T W`.

**Where this differs from AArch64** (forced by the x86-64 shape): the threads are over `X64.isa` (AArch64:
`isaLSE2`) and the worker side, `Post` and kernel pieces are the x86-64 twins (`X64HelloW1`, `X64HelloEmitPh`,
`X64WakeOwn`, `X64WakeW1.mainTidW`); the statements and proofs are otherwise the AArch64 ones. A64's `spawn_ofH`
is dead in the hello proof (hello's `spawn` field is `X64HelloSpawnR.spawn_RH`) and is not twinned, so this module
has no `#print axioms` check of it; `post_startH` is checked instead.
-/
import Spike.Lib.X64WakeSpawn
import Spike.Lib.X64HelloQ
import Spike.Lib.X64WakeOwnXW
import Spike.Lib.X64HelloSelfWords

namespace Spike.Lib.X64HelloSpawn

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.X64WakeT1
open Spike.Lib.X64HelloW1 (WSideH PT1h printPh_spawn)
open Spike.Lib.X64WakeW1 (mainTidW)

/-- **The spawned worker's packet**: the source worker's argument is the
slice's three words (the buffer's locative, its word count `D.mB w ≠ 0`,
its byte count `D.nB w`), the pointer word `D.cw w` and main's id. -/
def PktH {ι : Type} (D : WSideH ι) (w : ι) (env : TermRun.Env) : Prop :=
  ∃ (T : Ty) (w0 w1 w2 w4 : TermRun.Word), env = [("a", T, [w0, w1, w2, D.cw w, w4])] ∧
    w4.val = mainTidW ∧ w0.val = .loc ⟨D.bufL w, 0⟩ 0 ∧ w1.val = .num (D.mB w) ∧ D.mB w ≠ 0 ∧
    w2.val = .num (D.nB w)

/-- **hello's worker relation at the spawn**: the child in `Wi` (empty
stack of frames), the source worker at `.tail "worker" …` on one frame
with no type variables and hello's packet, no promise on either side (so
no promise spans an `emit`: the spawn witness of `PT1h`'s clause
`s1.promises = [] ∨ NoEmit`). -/
theorem pt1_startH {ι : Type} (D : WSideH ι) (w : ι) (tm : Memory) (sm : WeakMem.Memory) {t1 : Thread isa}
    {s1 : TermRun.TTh} (hW : D.Wi w t1.st (Ctl.of s1) []) (hst : s1.stack = []) (hσ : s1.σs = [])
    (ht : s1.term = .tail "worker" [] (.var "a") []) (henv : PktH D w s1.env) (hp : s1.promises = [])
    (hp1 : t1.prom = []) (hB : X64HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) sm) :
    PT1h D w tm sm t1 s1 := by
  obtain ⟨T, w0, w1, w2, w4, he, hj, h0, h1, hm, h2⟩ := henv
  refine ⟨hst ▸ hW, hσ, .inl ⟨printPh_spawn hj h0 h1 hm h2 hst ht he, hB, X64HelloW1.pTermH_spawn ht,
    .inl hp⟩, ?_, ?_, ?_⟩
  · rw [hp]; exact Nat.zero_le _
  · intro k hk; rw [hp] at hk; cases hk
  · rw [hp1]; exact List.nodup_nil

/-- **`Post` at the clone with hello's worker relation**: `post_startOXW` at
`Q.PT1 = PT1hE D`, the spawned worker built by `pt1_startH` (at `PT1h`); main owns `T`'s self word, the worker
`W`'s (`hQ`), both in the clone's own list (`hT0`, `hW0`) and each thread's cover set (`hcovT`, `hcovW`). -/
theorem post_startH {Λ : Scc.Sem.Layout} {Q : WakeRel} {D : WSideH Q.ι} {T W : BitVec 64}
    (hQ : Q.own = X64WakeOwnX.wakeOwnXW T W) (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    (hQ1 : Q.PT1 = X64HelloEmitPh.PT1hE D) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isa} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hT0 : ((⟨T, 8⟩ : Loc), T.setWidth 128) ∈ own₀) (hW0 : ((⟨W, 8⟩ : Loc), W.setWidth 128) ∈ own₀)
    (hcovT : (Q.P w).cov 0 ⟨T, 8⟩) (hcovW : (Q.P w).cov 1 ⟨W, 8⟩)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hW1 : D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1) []) (hst1 : s1.stack = [])
    (hσ1 : s1.σs = []) (ht1 : s1.term = .tail "worker" [] (.var "a") []) (henv1 : PktH D w s1.env)
    (hB : X64HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  have hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1 := by
    rw [hQ1]
    exact .inl <| pt1_startH D w _ _ hW1 hst1 hσ1 ht1 henv1 hsp1 childAfter_prom hB
  exact X64WakeOwnX.post_startOXW hQ hTW hSR h1 hs hi hp hmsgs hin hfits hG hb hown hT0 hW0 hcovT hcovW hsp0 hsp1
    hs0 hs1 hfrz hfoot hj hjl hPT0 hPT1 hProt hKR

/-- **The pre side's facts at main's clone** (`WakeSpawn.SpawnPre`'s, the
spawned worker's source thread at hello's packet `PktH`). -/
structure SpawnPreH (Q : WakeRel) (Λ : Scc.Sem.Layout) (D : WSideH Q.ι) (r0 r1 : Q.ι → Range) (w : Q.ι)
    (d : Cfg) (th : Thread isa) (stack : Nat) (s : TermRun.Cfg) (s0 s1 : TermRun.TTh)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat)
    (j : Nat) (own₀ : List (Loc × Val)) : Prop where
  SR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩
  threads : d.1.threads = #[th]
  ths : s.ths = #[s0, s1]
  inv1 : Inv1 Λ lbl lsize ts th d.1.mem s.mem
  prom : th.prom = []
  msgs : Consumer1.OwnMsgs d.1.mem
  memIn : Consumer1.MemIn Λ d.1.mem
  fits : Consumer1.MemFits d.1.mem
  memInv : MemInv (Q.G w) d.1.mem
  bnd : th.Bnd d.1.mem.last
  own : ExtRows.OwnOk own₀ d.1.mem th.prom
  sp0 : s0.promises = []
  sp1 : s1.promises = []
  scov0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc
  scov1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc
  /-- The flag's last write before the spawn is `0` ... -/
  flag : d.1.mem.read? (Q.C w).cT j = some 0
  /-- ... and no later message is to it. -/
  flagLast : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT
  /-- The spawned worker's source thread: one frame, no type variables, at
  `worker`'s tail call with hello's packet. -/
  st1 : s1.stack = []
  σ1 : s1.σs = []
  term1 : s1.term = .tail "worker" [] (.var "a") []
  env1 : PktH D w s1.env
  /-- The published buffer in the source memory at the spawn
  (`X64HelloW1.bufV_spawn`). -/
  buf : X64HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem
  /-- The kernel state for `KRH`. -/
  slots : ∃ k, d.2.slots = #[.run k]
  held : d.2.held = [(0, r1 w), (0, r0 w)]
  top : (r1 w).lo + (r1 w).size = stack
  live : ∀ s0', s.ths[0]? = some s0' → s0'.term ≠ WakeMLive.wlRet
  trace : SrcSem.traceOf s = []
  /-- **Both TCB self words at the clone** (`X64HelloSelfWords.SelfWordsAtClone`), for the words `T`, `W` of the
  relation's own map when it is `X64WakeOwnX.wakeOwnXW T W`: the facts the start row with both self words
  (`X64WakeOwnX.post_startOXW`) reads. While `Q.own` is not of that form (`X64WakeOwn.wakeOwn`) the field holds
  vacuously; the certificate reads it only at the instance whose own map is `wakeOwnXW` by a proved equation,
  so the premise `Q.own = wakeOwnXW T W` is discharged there and is not carried further up. -/
  self : ∀ T W : BitVec 64, Q.own = X64WakeOwnX.wakeOwnXW T W → X64HelloSelfWords.SelfWordsAtClone d.1.mem th.prom T W

end Spike.Lib.X64HelloSpawn

/-- info: 'Spike.Lib.X64HelloSpawn.pt1_startH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpawn.pt1_startH


/-- info: 'Spike.Lib.X64HelloSpawn.post_startH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSpawn.post_startH
