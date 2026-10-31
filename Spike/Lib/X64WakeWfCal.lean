/-
**wake.w's `wc_main` callees inside `Wf`** (x86-64): the nodes of
`scc_rt_thread_reserve` (`ReserveW`) and of `scc_rt_alloc_tcb` (`TcbWG`)
as called from `wc_main` (returning to `.x19`, `.x20`) inside
`WakeWf.Wf` at any frames `fs`, owned words `own`, write tail `Dt` and move
`K`, from the nodes' `SFactsSt2` at `own` and `Dt = False` (`hst`) and
placement (`hpl`), both given per node, the nodes' pcs off the sites
(decided against the resolved sites `WakePh.okC`), the abort phases'
decided checks (`phOffW`, `siOffW`), the callee's control (`hc0`) and the
written words off the arena (`hoff*`). The `ret`-free blocks go through
`blkCn`, the silent instructions through `nodeC`.

- `htkC`, `habtC`: a pc `okC` is off the take and abort sites.
- `blkW_dt`, `nodeW_dt`: a node's `SFactsSt2` at `Dt = False` at any `Dt`.
- `blkC`: a covered block returning to `L.lab rl` inside `Wf`
  (`WakeWf.blkW_wfQ` at `instOkW`).
- `blkCn`: `blkC` at a `ret`-free block.
- `nodeC`: a silent single instruction inside `Wf` (`WakeWf.nodeW_wfQ` at
  `instOkW`) at a pc `okC`.
- `nodeCfi`: a single instruction with undefined flags inside `Wf`
  (`WakeWf.nodeW_wfQF` at `instOkW`).
- `nodeCxadd`, `nodeCst`: the counter's `lock xaddq` / a header's store
  inside `Wf` (`WakeWf.nodeW_wfXadd` / `nodeW_wfSt` at `instOkW`).
- `reserveW_wfG`: every `ReserveW` node inside `Wf`.
- `tcbWG_wfG`: every `TcbWG` node inside `Wf`.

No absolute address appears in a statement; the proofs decide the pcs at
the certificate's labels.

Where x86-64 differs from AArch64: no `hal`; a block sits at a byte offset
`k` of its label (`blockAtB`), its pcs `cellOff` bytes on, a single
instruction has a size `z` (`siOffW pfxM l k z`); a `ret`'s target is the
stack slot at `%rsp` (`blkC`'s `hret`); `pfxM` is `StartWf.pfxM`
(`.Lwc_main`). AArch64's `nodeCldop` (`ldadd`) is `nodeCxadd` (`lock
xaddq`), whose `hoff` takes the memory `m` (as `WakeWf.nodeW_wfXadd`), and
the store's address is `bAddr` (A64's `rAddr`); `nodeCfi` is new (the
length's and the header's flag-clobbering instructions, nodes of their own
on x86-64). The reserve returns to `.Lwc_main.x19` in a region with the
frame `[-40, 8]` (A64's `.sp3`, `[-48, 0]`), and its add's address is
`%rcx` (A64's `x1`); `scc_rt_alloc_tcb` has 33 nodes (A64's 15) and
returns to `.Lwc_main.x20` in a region with the frame `[-184, 8]` (A64's
`.sp4`, `[-192, 0]`). The owned words are any `own` (A64's `ownG`, with
`nodeC` and the `ret`-free blocks through `WcWf`): x86-64's `W1W` owns
`ownGXW` (`ownG` with the TCB self words). The statements are otherwise
A64's.
-/
import Spike.Lib.X64WakeStartTcbL
import Spike.Lib.X64WakeWcResWI
import Spike.Lib.X64WakeTcb2CallW
import Spike.Lib.X64WakeWcWf

namespace Spike.Lib.X64.WakePh.CalWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW cellOff okBlk SI FI stDir xaddDir bAddr arun)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (Wf RunWf)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib (Arena FragS)

set_option hygiene false in
/-- A `ret`-free block of a callee at `l + k` (`bb` its code check, `ok` its
`okBlk`, `nr` its no-`ret` lemma, `el` its label's value). -/
local macro "cblk " bb:term:max ok:term:max nr:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkCn hp hlo hΛ hlab hsite hcl $bb (by first | rfl | exact ofNat_zero' _) $ok hR (by omega)
      (by omega) h1 ?_ (by decide +kernel) $nr (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [Spike.Lib.X64.Rt.Reserve.rvN, Spike.Lib.X64.Rt.tcbNG]
    rw [$el:term]; revert j; decide +kernel))

set_option hygiene false in
/-- A silent or flag-clobbering single instruction of a callee (`lem` its
lemma, `bb` its code check, `el` its label's value). -/
local macro "cnode " lem:ident bb:term:max el:term:max : tactic =>
  `(tactic| (
    refine $lem hp hlo hΛ hlab hsite hcl $bb (by first | rfl | exact ofNat_zero' _) h1 ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2
    dsimp only [Spike.Lib.X64.Rt.Reserve.rvN, Spike.Lib.X64.Rt.tcbNG]; rw [$el:term]; decide +kernel))

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))

omit hcl in
include hlab hsite in
/-- **A pc `okC` is off the take site.** -/
theorem htkC {pc : Int64} (h : okC pc.toBitVec.toNat = true) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [StartTcb.siteT hlab hsite x hx]; intro he; rw [he] at h; exact absurd h (by decide +kernel)

include hp hlo hΛ in
/-- **A pc `okC` is off the abort sites.** -/
theorem habtC {pc : Int64} (h : okC pc.toBitVec.toNat = true) :
    ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → pc.toBitVec.toNat ≠ x :=
  WcWf.habt_of_okPcOf hp hlo (by rw [okPc_eq hΛ]; exact h)

omit hp hlo hΛ hlab hsite hcl in
/-- A block's `SFactsSt2` at `Dt = False` holds at any `Dt`. -/
theorem blkW_dt {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => let r := h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

omit hp hlo hΛ hlab hsite hcl in
/-- A node's `SFactsSt2` at `Dt = False` holds at any `Dt`. -/
theorem nodeW_dt {n : ND} (h : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n :=
  fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (h s c hA).1 (fun h => h.elim), (h s c hA).2⟩

include hp hlo hΛ hlab hsite hcl

/-- **A covered block of wakeCells returning to `L.lab rl` inside `Wf`** at
the frames `fs`: its `SFactsSt2` at `Dt = False` (`hst`, moved by `K`), its
pcs `okC` (`hokpc`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl` through the slot at `%rsp`, `hret`), its controls not `main`'s
`ret` at no frame with their runs well formed (`hJ`), its frames placed
(`hpl`). -/
theorem blkC {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk := by
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  exact Spike.Lib.X64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := fs) hI (hp ▸ hb) he hok hR hlo' hhi (blkW_dt hst)
    (fun j hj s h1 h2 h3 => (hI.off s (by rw [okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.WakeWf.phOffW_sound hlab hph) hret hcl hJ hpl

/-- **A covered `ret`-free block of wakeCells inside `Wf`** (`blkC` at its
own label, no `ret` to aim). -/
theorem blkCn {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k l blk = true) (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk :=
  blkC hp hlo hΛ hlab hsite hcl hb he hok hR hlo' hhi hst hokpc hph
    (fun _ _ _ j hj r => (Spike.Lib.X64Consumer.noRet_false hnr j hj r).elim) hJ hpl

/-- **A silent single instruction of wakeCells inside `Wf`** at a pc `okC`
(`WakeWf.nodeW_wfQ` at `instOkW`). -/
theorem nodeC {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.X64.WakeWf.nodeW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl

/-- **A single instruction with undefined flags of wakeCells inside `Wf`**
(as `nodeC`, `WakeWf.nodeW_wfQF` at `instOkW`). -/
theorem nodeCfi {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.X64.WakeWf.nodeW_wfQF (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl

/-- **The counter's `lock xaddq` of wakeCells inside `Wf`** (as `nodeC`):
its word unmapped in private memory (`ha`), off the arena and not its
counter word (`hoff`). -/
theorem nodeCxadd {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.X64.WakeWf.nodeW_wfXadd (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl ha hoff

/-- **A header's store of wakeCells inside `Wf`** (as `nodeCxadd`). -/
theorem nodeCst {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.X64.WakeWf.nodeW_wfSt (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl ha hoff

open Spike.Lib.X64.Flow.Reserve (rPro rArg rBnd rJ rRet fnL entryL okL rmwPc reserveIn rPro_ok rArg_ok rBnd_ok
  rJ_ok rRet_ok rRet_walk) in
open Spike.Lib.X64.Rt.Reserve (ResG rvN ReserveW ntA rPro_noRet rArg_noRet rBnd_noRet rJ_noRet) in
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt) in
set_option maxHeartbeats 3200000 in
/-- **`scc_rt_thread_reserve`'s nodes inside `Wf`**, called from `wc_main`
returning to `.x19` (`hra`), in a region with the frame `[-40, 8]`: each
node's `SFactsSt2` (`hst`) and placement (`hpl`), the control `q.c0` not
`main`'s `ret` at no frame with its runs well formed (`hc0`), the counter
`scc_rt_nthreads` unmapped under `F` (`hunN`) and off the arena and not its
counter word (`hoffN`). -/
theorem reserveW_wfG (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi) (q : ResG)
    (hra : q.g.ra = (L.lab ".Lwc_main.x19").toBitVec)
    (hc0 : (fs = [] → ∀ a, q.c0.term ≠ .ret a) ∧ RunWf p q.c0 fs)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hoffN : ¬ (ar.heap ≤ (ntA L.lab).toNat ∧ (ntA L.lab).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨ntA L.lab, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, ReserveW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F q i)
    (hpl : ∀ i, ReserveW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F q i) :
    ∀ i, ReserveW (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F q i := by
  obtain ⟨lF, lE, lO⟩ := resLabs
  have eF : (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199447 := hlab _ _ lF
  have eE : (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199455 := hlab _ _ lE
  have eO : (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199536 := hlab _ _ lO
  have hin := Spike.Lib.X64.Flow.WakeWc.wake_reserveIn
  simp only [reserveIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = q.c0) →
      ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e => cblk bE rPro_ok rPro_noRet eF
  case entry => cnode nodeC bA eE
  case arg => cblk bArg rArg_ok rArg_noRet eE
  case rmw =>
    have hA' : ∀ σ c, (rvN (_root_.Executable.labels L.exe).label q .rmw).J σ c → bAddr σ.regs .rcx 0 = ntA L.lab :=
      fun σ c hJ' => by
        obtain ⟨-, -, -, hc⟩ := hJ'
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hc]; first | exact BitVec.add_zero _ | simp
    refine nodeCxadd hp hlo hΛ hlab hsite hcl bRmw rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunN _ hF) (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffN)
    dsimp only [rvN, rmwPc]; rw [eE]; decide +kernel
  case bnd => cblk bBnd rBnd_ok rBnd_noRet eE
  case j => cblk bJ rJ_ok rJ_noRet eE
  case ok =>
    refine blkC hp hlo hΛ hlab hsite hcl (rl := ".Lwc_main.x19") bOk (ofNat_zero' _) rRet_ok hR (by omega)
      (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.X64Consumer.hret_of_run rRet_ok fun σ c hJ' => ?_) (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [rvN]; rw [eO]; revert j; decide +kernel
    · dsimp only [rvN] at hJ' ⊢
      rw [(rRet_walk _ _ hJ'.2).1, hra]; exact Int64.ofBitVec_toBitVec _

open Spike.Lib.X64.Flow.Ret0.AllocTcb in
open Spike.Lib.X64.Flow.Ret0 (hdrBlk_eq rmwBlk_eq) in
open Spike.Lib.X64.Rt (tcbNG TcbWG) in
set_option maxHeartbeats 6400000 in
/-- **`scc_rt_alloc_tcb`'s nodes inside `Wf`**, wake's second TCB
(`Tcb2Call.tcb2Q`) called from `wc_main` returning to `.x20` (`hra`), in a
region with the frame `[-184, 8]`: each node's `SFactsSt2` (`hst`) and
placement (`hpl`), the control `c0` (`hc0`), the counter
`scc_rt_pinned_next` (`L.pnA`) and the header word (`L.pinA + 96`)
unmapped under `F` (`hunP`, `hunH`) and off the arena and not its counter
word (`hoffP`, `hoffH`). -/
theorem tcbWG_wfG (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (g : G) (c0 : Ctl) (hra : g.ra = (L.lab ".Lwc_main.x20").toBitVec)
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧ (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 96#64) 8 = none)
    (hoffH : ¬ (ar.heap ≤ (L.pinA + 96#64).toNat ∧ (L.pinA + 96#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA + 96#64, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, TcbWG (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F
      (Tcb2Call.tcb2Q g c0) i)
    (hpl : ∀ i, TcbWG (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F
      (Tcb2Call.tcb2Q g c0) i) :
    ∀ i, TcbWG (fun s c => Wf L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F (Tcb2Call.tcb2Q g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := Tcb2W.tcb_labs hlab (L := L)
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have hin := Tcb2W.wake_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = c0) →
      ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [TcbWG] at h1 h2 ⊢
  case e => cblk bE atPro_ok Spike.Lib.X64.Rt.Tcb.atPro_noRet eFn
  case entry => cblk bEn atChk_ok Spike.Lib.X64.Rt.Tcb.atChk_noRet eEn
  case j1 => cblk bJ1 atJ1_ok Spike.Lib.X64.Rt.Tcb.atJ1_noRet eEn
  case len => cblk bL0 atL0_ok Spike.Lib.X64.Rt.Tcb.atL0_noRet eLen
  case l1 => cblk bL1 atL1_ok Spike.Lib.X64.Rt.Tcb.atL1_noRet eLen
  case l2 => cblk bL2 atL2_ok Spike.Lib.X64.Rt.Tcb.atL2_noRet eLen
  case l3 => cblk bL3 atL3_ok Spike.Lib.X64.Rt.Tcb.atL3_noRet eLen
  case l4 => cblk bL4 atL4_ok Spike.Lib.X64.Rt.Tcb.atL4_noRet eLen
  case l5 => cblk bL5 atL5_ok Spike.Lib.X64.Rt.Tcb.atL5_noRet eLen
  case l6 => cblk bL6 atL6_ok Spike.Lib.X64.Rt.Tcb.atL6_noRet eLen
  case arg => cblk bArg atArg_ok Spike.Lib.X64.Rt.Tcb.atArg_noRet eLen
  case bnd => cblk bBnd atBnd_ok Spike.Lib.X64.Rt.Tcb.atBnd_noRet eLen
  case j2 => cblk bJ2 atJ2_ok Spike.Lib.X64.Rt.Tcb.atJ2_noRet eLen
  case o1 => cblk bO1 atO1_ok Spike.Lib.X64.Rt.Tcb.atO1_noRet eOk
  case o2 => cblk bO2 atO2_ok Spike.Lib.X64.Rt.Tcb.atO2_noRet eOk
  case o3 => cblk bO3 atO3_ok Spike.Lib.X64.Rt.Tcb.atO3_noRet eOk
  case o4 => cblk bO4 atO4_ok Spike.Lib.X64.Rt.Tcb.atO4_noRet eOk
  case o5 => cblk bO5 atO5_ok Spike.Lib.X64.Rt.Tcb.atO5_noRet eOk
  case shr1 => cnode nodeCfi fShr1 eLen
  case and1 => cnode nodeCfi fAnd1 eLen
  case shr2 => cnode nodeCfi fShr2 eLen
  case and2 => cnode nodeCfi fAnd2 eLen
  case imul1 => cnode nodeCfi fImul1 eLen
  case shl1 => cnode nodeCfi fShl1 eLen
  case lea1 => cnode nodeC sLea1 eLen
  case ok => cnode nodeC sOk eOk
  case imul2 => cnode nodeCfi fImul2 eOk
  case shl2 => cnode nodeCfi fShl2 eOk
  case shl3 => cnode nodeCfi fShl3 eOk
  case or1 => cnode nodeCfi fOr1 eOk
  case rmw =>
    have hA' : ∀ σ c, (tcbNG (_root_.Executable.labels L.exe).label (Tcb2Call.tcb2Q g c0) .rmw).J σ c →
        bAddr σ.regs .rcx 0 = L.pnA := fun σ c hJ' => by
      dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ'.2.2.2, ← hpn]; first | exact BitVec.add_zero _ | simp
    refine nodeCxadd hp hlo hΛ hlab hsite hcl bRmw rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunP _ hF) (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffP)
    dsimp only [tcbNG, rmwPc]; rw [eLen]; decide +kernel
  case hdr =>
    have hA' : ∀ σ c, (tcbNG (_root_.Executable.labels L.exe).label (Tcb2Call.tcb2Q g c0) .hdr).J σ c →
        bAddr σ.regs .rcx 0 = L.pinA + 96#64 := fun σ c hJ' => by
      dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ'.2.2.2, ← hpin, ← Tcb2Call.tcb2Q_hdrA _ g c0]
      first | exact BitVec.add_zero _ | simp
    refine nodeCst hp hlo hΛ hlab hsite hcl bHdr rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunH _ hF) (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffH)
    dsimp only [tcbNG, hdrPc]; rw [eOk]; decide +kernel
  case ret =>
    refine blkC hp hlo hΛ hlab hsite hcl (rl := ".Lwc_main.x20") bRet rfl atRet_ok hR (by omega) (by omega) h1 ?_
      (by decide +kernel) (Spike.Lib.X64Consumer.hret_of_run atRet_ok fun σ c hJ' => ?_) (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [tcbNG]; rw [eOk]; revert j; decide +kernel
    · dsimp only [tcbNG] at hJ' ⊢
      rw [(atRet_walkG _ _ hJ'.2).1]; show Int64.ofBitVec g.ra = _; rw [hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.X64.WakePh.CalWf

/-- info: 'Spike.Lib.X64.WakePh.CalWf.blkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.blkC

/-- info: 'Spike.Lib.X64.WakePh.CalWf.nodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.nodeC

/-- info: 'Spike.Lib.X64.WakePh.CalWf.nodeCfi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.nodeCfi

/-- info: 'Spike.Lib.X64.WakePh.CalWf.reserveW_wfG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.reserveW_wfG

/-- info: 'Spike.Lib.X64.WakePh.CalWf.tcbWG_wfG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.tcbWG_wfG

/-- info: 'Spike.Lib.X64.WakePh.CalWf.blkCn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.CalWf.blkCn
