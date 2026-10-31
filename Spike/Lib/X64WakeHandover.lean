/-
**wake.w on x86-64: main's TCB words handed over at the clone**: the owned-word premises of
`X64WakeOwnX.post_startOXW` at the instance relation
`X64WakeInst.wakeQI` with `T := tcbM L`, `W := tcb2 L`
(`L := RuntimeLayout.ofPlaceWX hp i`) and main's own list at the clone
`own₀ = ownGXW L a st` (`st` main's state at the clone's `syscall`).

- `spPool_of_owned`: main's stack range `r0` is in the pool (`Owned`) and
  `%rsp` is `128` below its top, so `%rsp` is a pool stack (`spPool`).
- `handover_I`: `post_startOXW`'s `hQ`, `hTW`, `hT0`, `hW0`, `hcovT`,
  `hcovW` at `own₀ = ownGXW L a s` (`WakePh.clone_ownGXW` for `hT0`/`hW0`,
  `X64WakeQ.hown`, `WakePh.tcb2_ne_tcbM`, `WakeP.wakeP_own_cov`).
- `handover_clone`: `hT0`/`hW0` at the clone `ClonePre` (`hsp` by
  `spPool_of_owned`, `hpc` by its pc, `hlab` from the placement with the
  instance facts `hlo`, `hprog`).
- `post_start_I`: `post_startOXW` at `wakeQI` with those six discharged;
  the remaining arguments in `post_startOXW`'s order.

**Unlike AArch64** (forced by the x64 shape): AArch64's `post_startW` has
no owned words (A64 main reads its TCB through `tpidr_el0`, not memory), so
there is no counterpart; on x86-64 both threads own their `%fs:0` self word
and the spawner hands the worker's over at the clone.
-/
import Spike.Lib.X64WakeOwnT2
import Spike.Lib.X64WakeOwnXW
import Spike.Lib.X64WakePreA
import Spike.Lib.X64WakeQ
import Spike.Lib.X64WakeInst
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeInst

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM tcb2 ownGXW spPool)
open Spike.Lib.X64WakeOwnX (wakeOwnXW)
open SccCode (wakeCells)

/-- **A stack `128` below the top of an owned range is a pool stack.** -/
theorem spPool_of_owned {L : RuntimeLayout} {r0 : Range} {st : State} (hO : X64Consumer.Owned L.Λ r0 st)
    (htop : (st.st.1.regs.get64 .rsp).toNat + 128 = r0.lo + r0.size) (hsz : r0.size = 16384) :
    spPool L st := by
  have hs := hO.1
  simp only [Range.Sub] at hs
  show L.Λ.stackPool.lo < (st.st.1.regs.get64 .rsp).toNat ∧
    (st.st.1.regs.get64 .rsp).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size
  omega

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The handover's six facts** (see the module doc): at `wakeQI` with the
two TCB words and main's own list `ownGXW L a s` at a pool stack `s` at the
clone's pc. -/
theorem handover_I {ok : Gh → Prop} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μT : Marks}
    {M : X64WakeM0.MSide {g : Gh // ok g}} {D : X64WakeW1.WSide {g : Gh // ok g}}
    {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop} (w : {g : Gh // ok g}) {a : BitVec 64}
    {s : State}
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x)
    (hsp : spPool (Ly) s) (hpc : s.st.2 = (Ly).lab ".Lwc_main.x21" + 46) :
    (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).own =
        wakeOwnXW (tcbM (Ly)) (tcb2 (Ly)) ∧
      (⟨tcbM (Ly), 8⟩ : Loc) ≠ ⟨tcb2 (Ly), 8⟩ ∧
      ((⟨tcbM (Ly), 8⟩ : Loc), (tcbM (Ly)).setWidth 128) ∈ ownGXW (Ly) a s ∧
      ((⟨tcb2 (Ly), 8⟩ : Loc), (tcb2 (Ly)).setWidth 128) ∈ ownGXW (Ly) a s ∧
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).cov 0 ⟨tcbM (Ly), 8⟩ ∧
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).cov 1 ⟨tcb2 (Ly), 8⟩ :=
  ⟨X64WakeQ.hown, fun h => Spike.Lib.X64.WakePh.tcb2_ne_tcbM (Ly) (congrArg Loc.addr h).symm,
    (Spike.Lib.X64.WakePh.clone_ownGXW hlab hsp hpc).1, (Spike.Lib.X64.WakePh.clone_ownGXW hlab hsp hpc).2,
    WakeP.wakeP_own_cov (.inl ⟨rfl, rfl⟩), WakeP.wakeP_own_cov (.inr ⟨rfl, rfl⟩)⟩

/-- **`hT0`/`hW0` at the clone** (see the module doc): main's thread at
`ClonePre` (on the layout's executable, `hX`) owns both TCB words in
`ownGXW L a`, for every `a`. -/
theorem handover_clone (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo) (hprog : o.prog = wakeCells)
    {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {d : Cfg} {s : TermRun.Cfg}
    (h : X64WakePreA.ClonePre (Ly).Λ r0 r1 X lbl d s) (hX : ∀ st, X st → st.exe = (Ly).exe) :
    ∃ th : Thread isa, d.1.threads = #[th] ∧ ∀ a : BitVec 64,
      ((⟨tcbM (Ly), 8⟩ : Loc), (tcbM (Ly)).setWidth 128) ∈ ownGXW (Ly) a th.st ∧
      ((⟨tcb2 (Ly), 8⟩ : Loc), (tcb2 (Ly)).setWidth 128) ∈ ownGXW (Ly) a th.st := by
  obtain ⟨th, -, -, -, -, -, hth, -, hpc, -, -, -, -, -, -, -, -, -, hO, -, hXs, -, -, htop, hsz, -⟩ := h
  have hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x hx => PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hprog]; exact hx)
  have hpc' : th.st.st.2 = (Ly).lab ".Lwc_main.x21" + 46 := by
    rw [hpc, hX _ hXs]; rfl
  exact ⟨th, hth, fun a => Spike.Lib.X64.WakePh.clone_ownGXW hlab (spPool_of_owned hO htop hsz) hpc'⟩

/-- **`post_startOXW` at the instance** (see the module doc): at
`wakeQI` with the two TCB words and `own₀ = ownGXW L a th.st`, main's
thread `th` at the clone's pc (`hpc`) on a pool stack (`hsp`); the other
arguments are `post_startOXW`'s, in its order. -/
theorem post_start_I {ok : Gh → Prop} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μT : Marks}
    {M : X64WakeM0.MSide {g : Gh // ok g}} {D : X64WakeW1.WSide {g : Gh // ok g}}
    {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop} {Λ : Scc.Sem.Layout} {w : {g : Gh // ok g}}
    {a : BitVec 64}
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isa} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh}
    (hsp : spPool (Ly) th.st) (hpc : th.st.st.2 = (Ly).lab ".Lwc_main.x21" + 46)
    (hSR : (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).SR w =
      ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hpr : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem)
    (hG : MemInv ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk (ownGXW (Ly) a th.st) d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m →
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m →
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i' l, i' < 2 → ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).frz l →
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).cov i' l)
    (hfoot : ∀ i' j l, i' < 2 → j < 2 → i' ≠ j →
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).foot j l →
      ¬ ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).P w).cov i' l)
    {j : Nat}
    (hj : d.1.mem.read? ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' →
      w'.loc ≠ ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).C w).cT)
    (hPT0 : (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).PT0 w d.1.mem s.mem
      (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hPT1 : (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).PT1 w d.1.mem s.mem
      (childAfter abi d.2 0 th stack tls) s1)
    (hProt : HelloProt ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).SR w)
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).C w)
      ((wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).pT w) d.1.mem
      (retThread abi (parentPre abi d.2 0 th stack) r) (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).KR w
      (afterClone abi d 0 th stack tls r) s) :
    (wakeQI hp i (tcbM (Ly)) (tcb2 (Ly)) ok arch R1 μT M D r0 r1 passT).Post Λ
      (afterClone abi d 0 th stack tls r) s := by
  obtain ⟨hQ, hTW, hT0, hW0, hcovT, hcovW⟩ :=
    handover_I hp i (arch := arch) (R1 := R1) (μT := μT) (M := M) (D := D) (r0 := r0) (r1 := r1)
      (passT := passT) w (a := a) hlab hsp hpc
  exact X64WakeOwnX.post_startOXW hQ hTW hSR h1 hs hi hpr hmsgs hin hfits hG hb hown hT0 hW0 hcovT hcovW
    hsp0 hsp1 hs0 hs1 hfrz hfoot hj hjl hPT0 hPT1 hProt hKR

end Inst

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.spPool_of_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.spPool_of_owned

/-- info: 'Spike.Lib.X64WakeInst.handover_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.handover_I

/-- info: 'Spike.Lib.X64WakeInst.handover_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.handover_clone

/-- info: 'Spike.Lib.X64WakeInst.post_start_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.post_start_I
