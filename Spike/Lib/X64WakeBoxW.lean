/-
**The landing of wake's box into `h1`'s invariant** (x86-64): the pieces of
`Box ⊆ inv1W` (`X64WakeH1Inv.inv1W_of_segWS`) at main's `clone`.

At the `clone`'s `syscall` the segment does not step itself: the state is
`ClW`'s, so the outside move `K1W` (a refusal, `CloneErrK`) moves it, and the
refusal's return continues on the threads-abort path.

- `SegWS.kmove`: a segment of one outside move, from states `K` moves.
- `cloneSeg`: the `clone` states into the refusal path's entry, under `K1W`.
- `okb_transfer`, `okb_ms1`: the box call's premises (`Call.OKB`, the ghost
  of `bX` past the box's store) at `h0`'s memory side (`msOfA` at the
  start's labels) hold at `h1`'s (at the fresh label `l` of `n` bytes at
  `b`), the arena admitting box rows (`WakeOD.arW`): the counter word and
  the headers above `h1`'s floor are off `l`'s cells.
- `cloneInv_of_wcNS`: `CloneInv` at the clone's `syscall` from `wcNS`'s state.
- `SpawnSrc`, `src_spawn`: main's source from the box (`boxTerm`) through
  the publication and the pair to `spawnTerm`.
- `RefB`, `W1X`, `CloneP`, `hB_box`, `h1Stmt_box`: `Box ⊆ inv1W` from the
  box to the clone, the refusal and the threads abort (named premises
  `hmid`, `hseg`).
- `fwn_takeMem`, `wF_dmem`, `fS_dmem`: `Box`'s take and memory-only facts at
  `h0`'s frame conditions.

x86-64 twin of `Spike/Lib/A64WakeBoxW.lean` (same names, namespace
`Spike.Lib.X64.WakeBoxW`).

**Unlike AArch64**:
- the assembly is a parameter `asm` (first argument of `W1X`, `CloneP`,
  `hB_box`, `h1Stmt_box`, as of `X64WakeH1Inv`'s `inv1W`); `endR` is
  `WakeH1Inv.endR` (A64 `WakeSpawnR.endR`);
- no `clone_decode` here: the x86-64 call decodes from `ClonePost`
  (`WakeWc.clone_decode`, through `WcClone.wcNS_call`'s `%rax = 56`,
  `%rdi = cloneFlags`, `%rdx = %r10 = 0`);
- `c`'s cell is in `%r12` and main's `ThreadId` word in `%rbx` (A64 `x9`,
  `x10`); main's parent region is `⟨R.base, -64, 16⟩` with
  `R.base = %rsp + 64` and `R.base + 64` stack 0's top (A64 `-96`, `sp + 80`,
  `48`); `R` is the landing's region (`R.lo ≤ -320`, `16 ≤ R.hi`; A64
  `-336`, `0 ≤`), and there is no alignment conjunct (`ClonePost` has none);
- the publication is under a full fence (`PubStep .sy`,
  `X64WakeBoxDefs.boxPubSy`: the `mfence`; A64 `.st`, `dmb ishst`);
- `hprog` is `(Ly).prog = wakeCells` (the clone's `syscall` from
  `wake_svcCode`; A64 `wakeProg` and `code_of`).
-/
import Spike.Lib.X64WakeH1Inv
import Spike.Lib.X64AllocBox
import Spike.Lib.X64WakeWcMidW
import Spike.Lib.X64WakeWcInv
import Spike.Lib.X64WakeBox
import Spike.Lib.X64OwnedStackM
import Spike.Lib.Rt.X64WordsNoneP
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeSpawnAt

namespace Spike.Lib.X64.WakeBoxW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (FragS SegWS MemSide KOutS PlaceWX)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (OwnS InvS)
open Spike.Lib.X64ConsumerA (msOfA msOfA0 updN)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.AllocRow (freeR)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **A segment of one outside move**: every pair of `P` inside `W`, moved
by `K` (so no row is asked for), and every move into `Q` past a local run. -/
theorem SegWS.kmove {I : ISA} {W P Q : FragS I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
    (hW : ∀ s c fs, P s c fs → W s c fs) (hmv : ∀ s c fs, P s c fs → ∃ s', K s s')
    (hk : ∀ s c fs, P s c fs → KOutS K p Q s c fs) : SegWS W K p lbl ms P Q :=
  ⟨P, fun _ _ _ h => h, hW, fun s c fs h =>
    ⟨fun hn => (let ⟨s', hs'⟩ := hmv s c fs h; (hn s' hs').elim),
      (hk s c fs h).mono fun _ _ _ h => .inr h⟩⟩

/-- **A box call's premises across memory sides** that agree on the arena,
`G` and `mp`, admit box rows, and whose runtime words at the counter and at
the headers above `ms'`'s floor (inside `ms`'s) are runtime words of `ms'`. -/
theorem okb_transfer {ms ms' : MemSide isa} {lab : Label → Int64} {q : Call} (h : q.OKB ms lab)
    (hheap : ms'.heap = ms.heap) (hctr : ms'.ctr = ms.ctr) (hunits : ms'.units = ms.units) (hoff : ms'.off = ms.off)
    (hcells : ms'.cells = ms.cells) (hG : ms'.G = ms.G) (hmp : ms'.mp = ms.mp) (hN : ms'.newOk)
    (hrt : ms.rt (BitVec.ofNat 64 ms.ctr).toNat → ms'.rt (BitVec.ofNat 64 ms.ctr).toNat)
    (hlo : ∀ o, ms'.lo o → ms.lo o)
    (hhdr : ∀ o, ms'.lo o → o + ms.units q.n q.τ ≤ ms.cells → ms.rt (q.hdrAt ms o) → ms'.rt (q.hdrAt ms o)) :
    q.OKB ms' lab := by
  obtain ⟨⟨site, hold, n_lt, ctr, heap, room, cells, units, off, accs, rt, mp, grow, hdr⟩, -, term, ev, one⟩ := h
  have ehd : ∀ o, q.hdrAt ms' o = q.hdrAt ms o := fun o => by simp only [Call.hdrAt, hheap]
  have eu : q.u ms' = q.u ms := by simp only [Call.u, hunits]
  refine ⟨⟨?_, hold, n_lt, hctr ▸ ctr, hheap ▸ heap, hheap ▸ room, hcells ▸ cells, hunits ▸ units, hoff ▸ off,
    accs, ?_, ?_, ?_, ?_⟩, hN, term, ev, one⟩
  · exact site.imp id fun ⟨_, h⟩ => ⟨hN, h⟩
  · simpa only [hctr] using hrt rt
  · simpa only [Spike.Lib.X64.ctrLoc, hctr, hmp] using mp
  · simpa only [Spike.Lib.X64.ctrLoc, hctr, hG, eu, hcells] using grow
  · intro o hl hu
    rw [ehd, hG, hmp]
    rw [hunits, hcells] at hu
    obtain ⟨h1, h2, h3⟩ := hdr o (hlo o hl) hu
    exact ⟨hhdr o hl hu h1, h2, h3⟩

/-- **A box call's premises at `h0`'s memory side hold at `h1`'s**: the
arena's memory sides at the start's labels and at the fresh label `l` of
`n` bytes at `b` (`AllocLand`, `l` not yet placed), the arena box rows
admitting: the counter is off the arena (`Arena.OK`), so off `l`'s cells;
a header above `h1`'s floor lies above `l`'s cells (`LoOf`). -/
theorem okb_ms1 {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I I' : InvS} {L0 : Lbl} {ls0 : Lsize} {fs fs' : List TermRun.Frame}
    {l : WeakMem.AllocLabel} {b n : Nat} {lab : Label → Int64} {q : Call} (hok : ar.OK) (hN : ar.newOk)
    (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (h : q.OKB (msOfA Λ μ rd G own ar I L0 ls0 fs) lab) :
    q.OKB (msOfA Λ μ rd G own ar I' (Spike.Lib.X64ConsumerA.upd L0 l b) (updN ls0 l n) fs') lab := by
  have hrt : ∀ a, (a < b ∨ b + 8 * n ≤ a) → (¬ ∃ l' b', L0 l' = some b' ∧ (lrange ls0 l' b').contains a) →
      ¬ ∃ l' b', Spike.Lib.X64ConsumerA.upd L0 l b l' = some b' ∧ (lrange (updN ls0 l n) l' b').contains a := by
    rintro a ha h0 ⟨l', b', h1, h2⟩
    by_cases e : l' = l
    · subst e
      simp only [Spike.Lib.X64ConsumerA.upd, updN, ite_true, Option.some.injEq, lrange,
        Scc.Sem.Range.contains] at h1 h2
      omega
    · simp only [Spike.Lib.X64ConsumerA.upd, e, ite_false] at h1
      simp only [lrange, Spike.Lib.X64ConsumerA.updN, e, ite_false] at h2; exact h0 ⟨l', b', h1, h2⟩
  obtain ⟨hb1, hb2, -⟩ := hb
  refine okb_transfer h rfl rfl rfl rfl rfl rfl rfl hN (hrt _ ?_) ?_ fun o hlo _ => hrt _ ?_
  · have := hok.ctr_out; have := hok.ctr_lt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by assumption)]; simp only [msOfA, msOfA0, MemSide.ofLabels] at *
    omega
  · intro o hlo l' b' h1
    have e : l' ≠ l := by rintro rfl; simp [hl] at h1
    simpa only [lrange, Spike.Lib.X64ConsumerA.updN, e, ite_false] using
      hlo l' b' (by simp only [Spike.Lib.X64ConsumerA.upd, e, ite_false]; exact h1)
  · have hd := (hlo l b (by simp [Spike.Lib.X64ConsumerA.upd])).1
    simp only [msOfA, msOfA0, MemSide.ofLabels, updN, ite_true, lrange, freeR, Scc.Sem.Range.Disjoint] at hd ⊢
    simp only [Call.hdrAt]
    omega

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry)

/-- **The `clone` states into the refusal path** under `K1W`: inside `W`,
`ClW`'s (so a refusal moves them) and off the take site, every refusal's
return reaching `Ref` past a local run. -/
theorem cloneSeg {W P Ref : FragS isa} {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa}
    (hW : ∀ s c fs, P s c fs → W s c fs) (hcl : ∀ s c fs, P s c fs → WakeOD.ClW hp i s)
    (hna : ∀ s c fs, P s c fs → s.st.2 ≠ X64WakeOSide.aW hp i E)
    (hret : ∀ s c fs, P s c fs → ∀ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) →
      ∃ c' fs', FrameRun wakeSrc (c, fs) (c', fs') ∧ Ref (abi.ret s r) c' fs') :
    SegWS W (WakeH1Inv.K1W hp i E) wakeSrc lbl ms P Ref := by
  refine SegWS.kmove hW (fun s c fs h => ⟨_, .inr ⟨hcl s c fs h, _, .inl rfl, rfl⟩⟩) ?_
  rintro s c fs h s' (⟨hpc, -⟩ | ⟨-, r, hr, rfl⟩)
  · exact (hna s c fs h hpc).elim
  · exact hret s c fs h r hr

end Inst

end Spike.Lib.X64.WakeBoxW

namespace Spike.Lib.X64.WakeBoxW
open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64.Flow.WakeWc (CloneInv ClonePost FrG)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)

/-- **`CloneInv` at the clone's `syscall`** at `h1`'s labels (`l` at `b`):
from `wcNS`'s state, `%r12` the cell `b` and `%rbx` main's `ThreadId` word
at `tcb0`, main's stack top, its thread pointer, and the source at
`spawnTerm` with `c` bound to `l`. -/
theorem cloneInv_of_wcNS {L : RuntimeLayout} {endPc : Int64} {l : WeakMem.AllocLabel} {b : Nat} {s : State}
    {c : Ctl} {R : Region} {F₂ : MachineData → Prop} {J : AS → Ctl → Prop} {σC : AS} {t : UInt64}
    {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (hl : Spike.Lib.X64WakeLoadT.L0T L.Λ l = none)
    (hG : FrG (WakeM.wJ0 (WakeM.wNC L.lab J).J σC) fr)
    (hA : At L.exe endPc R F₂ (wcNS L.lab c (WakeWc.t2 L.lab) (WakeWc.kOf L.lab) cA m fr) s c)
    (hok : (⟨R.base, -64, 16⟩ : Region).OK)
    (hat : At L.exe endPc ⟨R.base, -64, 16⟩ F₂ ⟨cloneAt L.exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c)
    (hb : (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64)
    (hst : R.base.toNat + 64 = L.stacksA.toNat + 16384)
    (ht : t.toBitVec = L.pinA + 0#64 + 8#64) (hcA : cA.toNat = b) (hm : m.toNat = Spike.Lib.X64WakeLoadT.tcb0 L.Λ)
    (hterm : c.term = Spike.Lib.X64WakeSrcDefs.spawnTerm) (hhold : c.hold = none)
    (hc : TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (hp : ∃ rt ws, TermRun.evalAt c.env (.var "p") = some (rt, ws)) (hσ : σC.regs.get64 .rsp = R.base + 8#64) :
    CloneInv L endPc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T L.Λ) l b) s c [] := by
  have hA' := hA
  obtain ⟨-, -, -, -, σ, hAb, -, ⟨-, h12, hbx, -⟩, -⟩ := hA'
  have e12 : (s.st.1.regs.get64 .r12).toNat = b := by rw [hAb.regs, h12, hcA]
  have ebx : (s.st.1.regs.get64 .rbx).toNat = Spike.Lib.X64WakeLoadT.tcb0 L.Λ := by rw [hAb.regs, hbx, hm]
  have hne : l ≠ mainTidLbl 2 := by
    rintro rfl; simp [Spike.Lib.X64WakeLoadT.L0T, Spike.Lib.X64ConsumerA.upd] at hl
  refine ⟨rfl, J, t, l, ⟨R, F₂, σC, cA, m, fr, hG, hA, hok, hat, hb, by omega, ht, hσ⟩, hterm, hhold, hc, hme, hp,
    ?_, ?_⟩
  · simp only [Spike.Lib.X64ConsumerA.upd, ite_true]; exact congrArg some e12.symm
  · simp only [Spike.Lib.X64ConsumerA.upd, Ne.symm hne, ite_false, Spike.Lib.X64WakeLoadT.L0T, ite_true]
    exact congrArg some ebx.symm

end Spike.Lib.X64.WakeBoxW

namespace Spike.Lib.X64.WakeBoxW
open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)

/-- The facts `CloneInv` reads of main's source at the clone. -/
def SpawnSrc (l : WeakMem.AllocLabel) (c : Ctl) : Prop :=
  c.term = Spike.Lib.X64WakeSrcDefs.spawnTerm ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "p") = some (.prod (.ptr .pub .int) .tid,
      [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])

/-- **main's source from the box to the spawn**: at `boxTerm` with `o` bound
to `l`'s owned locative and `me` to main's id, the `mfence`'s publication
(`c = publish o`, `boxPubSy`) and the pair (`p = (c, me)`) reach
`spawnTerm`. -/
theorem src_spawn {p : Prog} {P : Prop} (hP : P) {c : Ctl} {l : WeakMem.AllocLabel}
    (ht : c.term = Spike.Lib.X64WakeBoxDefs.boxTerm) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])) :
    ∃ c', FenceRun p P .sy c c' ∧ SpawnSrc l c' := by
  have hpub := Spike.Lib.X64WakeBoxDefs.boxPubSy ht hh ho
  have hc : TermRun.evalAt (("c", .ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env) (.var "c") =
      some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by simp [TermRun.evalAt, TermRun.lookupE]
  have hm : TermRun.evalAt (("c", .ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env) (.var "me") =
      some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [TermRun.evalAt, TermRun.lookupE] using hme
  refine ⟨_, .pub hP hpub (.single (Spike.Lib.Form.localStep_pair rfl hc hm)), rfl, rfl, ?_, ?_, ?_⟩
  all_goals simp [TermRun.evalAt, TermRun.lookupE, Spike.Lib.X64WakeBoxDefs.boxPubCtl] at hm ⊢
  all_goals exact hm

section Inst
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64.Flow.WakeWc (FrG)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

/-- **main back from a refused `clone`** (the threads-abort segment's
entry): `abi.ret s0 r` of a refusal `r` (`ThreadsAb.CloneRef`) from a clone
state `s0` at `wake_wc_mid_hatW`'s post, the landing's region `R` (`wcNS`)
and main's parent node in `⟨R.base, -64, 16⟩`, the source at `SpawnSrc l`,
`%r12`'s cell `cA` at `b` and `%rbx`'s word `m` main's `tcb0` (as at
`CloneP`). -/
def RefB (l : WeakMem.AllocLabel) (b : Nat) : FragS isa := fun s c fs => fs = [] ∧ SpawnSrc l c ∧
  ∃ s0 r, s = abi.ret s0 r ∧ (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) ∧
  ∃ (R : Region) (F₂ : MachineData → Prop) (J : AS → Ctl → Prop) (σC : AS) (cA m : BitVec 64)
    (fr : BitVec 64 × BitVec 64) (t : UInt64),
    R.OK ∧ R.lo ≤ -320 ∧ 16 ≤ R.hi ∧ R.base.toNat + 64 = (Ly).stacksA.toNat + 16384 ∧
    FrG (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) fr ∧ t.toBitVec = (Ly).pinA + 0#64 + 8#64 ∧
    Spike.Lib.X64.KeepTP.TP t s0 ∧
    At (Ly).exe (WakeH1Inv.endR hp i) R F₂ (wcNS (Ly).lab c
      (WakeWc.t2 (Ly).lab) (WakeWc.kOf (Ly).lab) cA m fr) s0 c ∧
    (⟨R.base, -64, 16⟩ : Region).OK ∧
    At (Ly).exe (WakeH1Inv.endR hp i) ⟨R.base, -64, 16⟩ F₂
      ⟨cloneAt (Ly).exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s0 c ∧
    (R.base.toNat : Int) = (s0.st.1.regs.get64 .rsp).toNat + 64 ∧ cA.toNat = b ∧
    m.toNat = Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ

end Inst

section H1
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcClone (oW wcNS)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64WakePreA (cloneAt)
open Spike.Lib.X64.Flow.WakeWc (FrG CloneInv)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64.WakeOPremW (W1W)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

/-- `h1`'s fence `W1W ∧ X1W` (`inv1W`'s) at the label `l` of `n` bytes at `b`. -/
abbrev W1X (l : WeakMem.AllocLabel) (b n : Nat) : FragS isa := fun s c fs =>
  W1W asm hp i E Dt Ctx ls0 l b n s c fs ∧ WakeH1Inv.X1W (Ly) (X64WakeOSide.aW hp i E) (WakeH1Inv.endR hp i) l
    (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls0) l n) s c fs

/-- **main at the clone's `syscall`** (`wake_wc_mid_hatW`'s post, `RefB`'s
machine facts at the clone state itself): the source at `SpawnSrc l`, one
object, inside `W1W`, `%r12`'s cell `b`, `%rbx`'s word main's `tcb0`, and
the child's stack in private memory (`StackM`, `scc_rt_thread_init`'s
take), and the caller's `%rsp` at `wc_main`'s call `R.base + 8` (`Box`'s). -/
def CloneP (l : WeakMem.AllocLabel) (b n : Nat) : FragS isa := fun s c fs => fs = [] ∧ SpawnSrc l c ∧
  n = 1 ∧ W1W asm hp i E Dt Ctx ls0 l b n s c [] ∧
  ∃ (R : Region) (F₂ : MachineData → Prop) (J : AS → Ctl → Prop) (σC : AS) (cA m : BitVec 64)
    (fr : BitVec 64 × BitVec 64) (t : UInt64),
    R.OK ∧ R.lo ≤ -320 ∧ 16 ≤ R.hi ∧ R.base.toNat + 64 = (Ly).stacksA.toNat + 16384 ∧
    FrG (WakeM.wJ0 (WakeM.wNC (Ly).lab J).J σC) fr ∧ t.toBitVec = (Ly).pinA + 0#64 + 8#64 ∧
    Spike.Lib.X64.KeepTP.TP t s ∧
    At (Ly).exe (WakeH1Inv.endR hp i) R F₂ (wcNS (Ly).lab c (WakeWc.t2 (Ly).lab) (WakeWc.kOf (Ly).lab) cA m fr)
      s c ∧
    (⟨R.base, -64, 16⟩ : Region).OK ∧
    At (Ly).exe (WakeH1Inv.endR hp i) ⟨R.base, -64, 16⟩ F₂
      ⟨cloneAt (Ly).exe, oW, JS c cA fr.1 fr.2 t.toBitVec⟩ s c ∧
    (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 64 ∧ cA.toNat = b ∧ m.toNat = tcb0 (Ly).Λ ∧
    Spike.Lib.X64.Flow.Ret0.StackM (X64WakeOSide.r1W hp i) s.st.1 ∧ σC.regs.get64 .rsp = R.base + 8#64

/-- **`Box ⊆ inv1W`** (`WakeH1Inv.h1Stmt_of`'s `hB`): the box's states run
inside `W1X` to the clone (`hmid`), the clone's refusal (`cloneSeg`, under
`K1W`) to `RefB`, and the threads abort from there never leaves (`hseg`).

- `hprog`: the layout's program is wake's cells (the placement's certificate).
- `hna`: the clone's `syscall` is not the take site (wake's label layout).
- `hsub1`: the child's stack is in the stack pool (the layout's stacks),
  for `X1W`'s owned child stack from `CloneP`'s `StackM` (`owned_of_stackM`).
- `hmid`: from the box to `CloneP`, by `wake_wc_mid_hatW` from `bX` (its
  `Q` the box's source facts, `S := SpawnSrc` through `src_spawn`), its
  fence `WcMidW.and` of the take's (`wcMidW_k1`) and `W1W`'s
  (`wcMidW_w1`), the box call's premises at `ms1W` by `okb_ms1`, and the
  box's `n = 1`, `cA = b`, `m = tcb0`.
- `hseg`: the threads-abort segment from `RefB`. -/
theorem hB_box {ms0 : MemSide isa} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeCells)
    (hna : (cloneAt (Ly).exe).toBitVec.toNat ≠ (X64WakeOSide.aW hp i E).toBitVec.toNat)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool)
    (hmid : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
        (CloneP asm hp i E Dt Ctx ls0 l b n))
    (hseg : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (RefB hp i l b) (fun _ _ _ => False)) :
    ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ s c, WakeWc.Box (Ly) ms0 F0 l b n s c → WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0 l b n s c [] := by
  intro l b n hl hb s c hB
  haveI := (Ly).valid
  have hcode := Spike.Lib.X64.WakePh.wake_svcCode (hprog ▸ (Ly).lays) (endPc := WakeH1Inv.endR hp i) rfl
  have hA : ∀ s c fs, CloneP asm hp i E Dt Ctx ls0 l b n s c fs → s.exe = (Ly).exe ∧
      s.endPc = WakeH1Inv.endR hp i ∧ s.st.2 = cloneAt (Ly).exe := by
    rintro s c fs ⟨-, -, -, -, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, hA, -⟩
    exact ⟨hA.1, hA.2.1, WakeWc.wcNS_cloneAt hA⟩
  have hci : ∀ s c fs, CloneP asm hp i E Dt Ctx ls0 l b n s c fs →
      CloneInv (Ly) (WakeH1Inv.endR hp i) (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b) s c [] := by
    rintro s c fs ⟨-, ⟨ht, hh, hc, hme, hpp⟩, -, -, R, F₂, J, σC, cA, m, fr, t, -, -, -, hst, hG, htb, -, hA,
      hok, hat, hsp, hcA, hm, -, hσ⟩
    exact cloneInv_of_wcNS hl hG hA hok hat hsp hst htb hcA hm ht hh hc hme ⟨_, _, hpp⟩ hσ
  refine WakeH1Inv.inv1W_of_segWS asm hp i E cT Dt Ctx ls0 ((hmid l b n hl hb).seq
    (SegWS.seq (Q := RefB hp i l b) (cloneSeg hp i E ?_ ?_ ?_ ?_) (hseg l b n hl hb))) s c [] ⟨hB, rfl⟩
  · intro s c fs h
    obtain ⟨-, -, hq⟩ := hA s c fs h
    have hSM : Spike.Lib.X64.Flow.Ret0.StackM (X64WakeOSide.r1W hp i) s.st.1 := by
      obtain ⟨-, -, -, -, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, hSM, -⟩ := h; exact hSM
    have e := h.1; subst e
    refine ⟨h.2.2.2.1, fun _ => ⟨hci s c [] h, fun l' hc' => ?_,
      Spike.Lib.X64Consumer.owned_of_stackM hsub1 hSM, h.2.1.2.2.1⟩, fun ha => (hna (by rw [← hq]; exact ha)).elim⟩
    obtain ⟨-, ⟨-, -, hc, -⟩, rfl, -⟩ := h
    rw [hc] at hc'; simp [TermRun.cst, Promises.TVal.mk0] at hc'; subst hc'
    simp [Spike.Lib.X64ConsumerA.updN]
  · intro s c fs h
    obtain ⟨hs, hn, hq⟩ := hA s c fs h
    exact ⟨by unfold pcOf WakeWc.clonePc; rw [hq],
      atSyscall_of_cellAt ((hcode s hs hn).cell0 rfl rfl (by rw [hq]; rfl)),
      WakeWc.clone_decode (hci s c fs h)⟩
  · intro s c fs h e; exact hna (by rw [← (hA s c fs h).2.2, e])
  · rintro s c fs ⟨rfl, hsrc, -, -, R, F₂, J, σC, cA, m, fr, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hcA,
      hm, -⟩ r hr
    exact ⟨c, [], .refl _, rfl, hsrc, s, r, rfl, hr, R, F₂, J, σC, cA, m, fr, t, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, hcA, hm⟩

/-- **`H1Stmt` at `inv1W` from wake's box** (`hB_box`'s premises). -/
theorem h1Stmt_box {ms0 : MemSide isa} {F0 : MachineData → Prop} (hprog : (Ly).prog = wakeCells)
    (hna : (cloneAt (Ly).exe).toBitVec.toNat ≠ (X64WakeOSide.aW hp i E).toBitVec.toNat)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool)
    (hmid : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (fun s c fs => WakeWc.Box (Ly) ms0 F0 l b n s c ∧ fs = [])
        (CloneP asm hp i E Dt Ctx ls0 l b n))
    (hseg : ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      SegWS (W1X asm hp i E Dt Ctx ls0 l b n) (WakeH1Inv.K1W hp i E) X64WakeT1.wakeSrc
        (Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b)
        (WakeH1Inv.ms1W asm hp i E cT ls0 l b n) (RefB hp i l b) (fun _ _ _ => False)) :
    WakeWc.H1Stmt (W1W asm hp i E Dt Ctx ls0) (WakeH1Inv.K1W hp i E) (WakeOD.arW hp i) (L0T (Ly).Λ)
      (WakeH1Inv.ms1W asm hp i E cT ls0) (Ly) (WakeH1Inv.endR hp i) (WakeWc.Box (Ly) ms0 F0)
      (WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0) :=
  WakeH1Inv.h1Stmt_of asm hp i E cT Dt Ctx ls0 _
    (hB_box asm hp i E cT Dt Ctx ls0 hprog hna hsub1 hmid hseg)

end H1

/-! ## `Box`'s take facts at `h0`'s frame conditions (non-vacuity) -/

section Take
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0 (takeMem)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

/-- **`Box`'s `hFt` at the start's `FWN`**: the child's stack is in the
pool, off the heap, the static image and the runtime's words. -/
theorem fwn_takeMem (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (m : MachineData) (pm : _root_.Mem 64)
    (h : Spike.Lib.X64.DmemPriv.WordsNoneP (Ly).Λ m.dmem ∧ Spike.Lib.X64.Rt.rtF (Ly) m) :
    Spike.Lib.X64.DmemPriv.WordsNoneP (Ly).Λ (takeMem pm (X64WakeOSide.r1W hp i) m).dmem ∧
      Spike.Lib.X64.Rt.rtF (Ly) (takeMem pm (X64WakeOSide.r1W hp i) m) :=
  ⟨Spike.Lib.X64.Rt.wordsNoneP_takeMem (PlaceWX.wf_link_of_placeWX i hp) hsub1 h.1,
    Spike.Lib.X64.Rt.rtF_takeMem (Ly) hsub1 h.2⟩

/-- **`Box`'s `hFd` at `wc_main`'s frame condition** (`h0`'s `wF … FS …`):
memory-only parts stay memory-only. -/
theorem wF_dmem {R : Region} {D : Int} {F : MachineData → Prop} {m0 : MachineData}
    {σC : AS} (hF : ∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') :
    ∀ m m' : MachineData, m'.dmem = m.dmem → Spike.Lib.X64.Flow.WakeM.wF R D F m0 σC m →
      Spike.Lib.X64.Flow.WakeM.wF R D F m0 σC m' :=
  fun _ _ e h => ⟨hF _ _ e h.1, fun k hk hn => by rw [e]; exact h.2.1 k hk hn, h.2.2⟩

/-- **`FS` reads memory only** (`h0`'s frame condition after the switch). -/
theorem fS_dmem {L : Spike.Lib.X64.Rt.RuntimeLayout} {rS : Scc.Sem.Range} {Lsw : Int} {k0 v : BitVec 64} :
    ∀ m m' : MachineData, m'.dmem = m.dmem → Spike.Lib.X64.WakePh.MainGlue.FS L rS Lsw k0 v m →
      Spike.Lib.X64.WakePh.MainGlue.FS L rS Lsw k0 v m' :=
  fun _ _ e h => by
    simpa only [Spike.Lib.X64.WakePh.MainGlue.FS, Spike.Lib.X64.Rt.swFSL, Spike.Lib.X64.Flow.Ret0.swF,
      Spike.Lib.X64.Flow.Ret0.StackOff, Spike.Lib.X64.Flow.Ret0.CallerCells, e] using h

end Take

end Spike.Lib.X64.WakeBoxW

/-- info: 'Spike.Lib.X64.WakeBoxW.SegWS.kmove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.SegWS.kmove

/-- info: 'Spike.Lib.X64.WakeBoxW.okb_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.okb_transfer

/-- info: 'Spike.Lib.X64.WakeBoxW.okb_ms1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.okb_ms1

/-- info: 'Spike.Lib.X64.WakeBoxW.cloneSeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.cloneSeg

/-- info: 'Spike.Lib.X64.WakeBoxW.cloneInv_of_wcNS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.cloneInv_of_wcNS

/-- info: 'Spike.Lib.X64.WakeBoxW.src_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.src_spawn

/-- info: 'Spike.Lib.X64.WakeBoxW.hB_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.hB_box

/-- info: 'Spike.Lib.X64.WakeBoxW.h1Stmt_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.h1Stmt_box

/-- info: 'Spike.Lib.X64.WakeBoxW.fwn_takeMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.fwn_takeMem

/-- info: 'Spike.Lib.X64.WakeBoxW.wF_dmem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.wF_dmem

/-- info: 'Spike.Lib.X64.WakeBoxW.fS_dmem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeBoxW.fS_dmem
