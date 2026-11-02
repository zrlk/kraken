/-
**hello.w's `wc_main` callees inside the root's third level `RootWX.W2H` on x86-64** (the twin of
`Spike/Lib/A64HelloCalW2.lean`; wake's x86-64 version is `Spike/Lib/X64WakeWfCal.lean`): the nodes of
`scc_rt_thread_reserve` (`ReserveW`, returning to `.x23`) and of the second `scc_rt_alloc_tcb` (`TcbWG`, returning
to `.x24`) inside `W2Hg own L ar helloSrc Dt (ClH L) Ctx lbl lsize` at any owned words `own` (`W2H L (ntA L.lab) …`
at `ownGH L (ntA L.lab)`), at no frames and no outside moves, from each node's `SFactsSt2` at `own` (`hst`, at any
move) and placement (`hpl`), the callee's control (`hc0`), and the written words unmapped under `F` and off the arena (`hun*`, `hoff*`).

- `blkC_W2H`: a covered block returning to `L.lab rl` (`StartWf.blkW_wfQH` at `instOkH`).
- `nodeC_W2H`: a silent single instruction (`WcWfX.nodeW_wfC_siX`).
- `nodeCxadd_W2H`, `nodeCst_W2H`: the counter's `lock xaddq`, a header's store (`HelloWf.nodeW_wfXaddH`,
  `nodeW_wfStH`).
- `reserveW_W2H`: every `ReserveW` node inside `W2H`.
- `tcbWG_W2H`: every `TcbWG` node of `tcb2QH` inside `W2H`.

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.

## Unlike AArch64

- As wake's x86-64 `X64WakeWfCal` against `A64WakeWfCal`: no `hal`; a block sits at a byte offset of its label
  (`blockAtB`), its pcs `cellOff` bytes on; a single instruction has a size `z` (`siOffW pfxM l k z`); a `ret`'s
  target is the stack slot at `%rsp` (`blkC_W2H`'s `hret`).
- AArch64's `nodeCldop_W2H` (`ldadd`) is `nodeCxadd_W2H` (`lock xaddq`), whose `hoff` takes the memory `m`; the
  store's address is `bAddr` (A64's `rAddr`); the length's and the header's flag-clobbering instructions are nodes
  of their own (`WcW2.nodeW_fiW2H`).
- The reserve returns to `.Lwc_main.x23` in a region with the frame `[-40, 8]` (A64's `.sp3`, `[-48, 0]`), its
  add's address `%rcx`; `scc_rt_alloc_tcb` has 33 nodes (A64's 15) and returns to `.Lwc_main.x24` in a region with
  the frame `[-184, 8]` (A64's `.sp4`, `[-192, 0]`).
- The lemmas are generic in the owned words `own` (at `RootWX.W2Hg`; A64: at `ownGH`), so that a level whose owned
  words also carry the threads' own TCB words shares them.
-/
import Spike.Lib.X64HelloWcW2
import Spike.Lib.X64HelloWcWfX
import Spike.Lib.X64WakeWfCal

namespace Spike.Lib.X64.HelloPh.CalW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW SI cellOff okBlk stDir xaddDir bAddr arun)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.RootWX (W2H W2Hg)
open Spike.Lib.X64.HelloPh.WcW2 (blkW_W2H blkW_noKH nodeW_noKH nodeW_fiW2H htk_ofC)
open Spike.Lib.X64.Flow.HelloWc (tcb2QH tcb2QH_hdrA)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64HelloSrc (helloSrc)

set_option hygiene false in
/-- A `ret`-free block of a callee at `l + k` (`bb` its code check, `ok` its `okBlk`, `el` its label's value). -/
local macro "cblk " bb:term:max ok:term:max el:term:max : tactic =>
  `(tactic| (
    refine blkW_W2H hp hlo hΛ hlab hsite $bb (by first | rfl | exact ofNat_zero' _) $ok hR (by omega)
      (by omega) h1 ?_ (by decide +kernel) (by decide) (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [Spike.Lib.X64.Rt.Reserve.rvN, Spike.Lib.X64.Rt.tcbNG]
    rw [$el:term]; revert j; decide +kernel))

set_option hygiene false in
/-- A silent or flag-clobbering single instruction of a callee (`lem` its lemma, `bb` its code check, `el` its
label's value). -/
local macro "cnode " lem:ident bb:term:max el:term:max : tactic =>
  `(tactic| (
    refine $lem hp hlo hΛ hlab hsite $bb (by first | rfl | exact ofNat_zero' _) h1 (htk_ofC hlab hsite ?_) ?_
      (by decide +kernel) (hJ _ fun _ _ h => h.1) h2 <;>
      (dsimp only [Spike.Lib.X64.Rt.Reserve.rvN, Spike.Lib.X64.Rt.tcbNG]; rw [$el:term]; decide +kernel)))

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.X64Consumer.Own} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa}
  {lbl : Lbl} {lsize : Lsize} {K : State → State → Prop} {R : Region} {F : MachineData → Prop}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at the owned words `own`, at no frames. -/
local notation "W2" => fun s c => W2Hg own L ar helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **A covered block returning to `L.lab rl` inside `W2H`** at no move (`StartWf.blkW_wfQH` at `instOkH`): its
`SFactsSt2` at `own` (`hst`, at any move), its pcs `okC` (`hokP`), its abort phases' check (`hph`,
its `ret`s to `L.lab rl` through the slot at `%rsp`, `hret`), its controls not at a `ret` with their runs well
formed (`hJ`), its frames placed (`hpl`). -/
theorem blkC_W2H {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F
      n blk)
    (hokP : ∀ j < blk.length, Spike.Lib.X64.HelloPh.okC (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW W2 (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hW := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
    (lsize := lsize) (fs := []) (Dt := Dt) (Cl := Spike.Lib.X64.HelloPh.ClH L) (lbl := lbl) (pfx := pfxM) hI
    (hp ▸ hb) he hok hR hlo' hhi (Spike.Lib.X64.WakePh.CalWf.blkW_dt hst)
    (fun j hj s _ _ h3 => (hI.off s (by
      rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokP j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret Spike.Lib.X64.HelloPh.ClH.cl
    (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact blkW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **A silent single instruction inside `W2H`** at no move (`WcWfX.nodeW_wfC_siX`): its pc off the take site
(`htk`) and `okC` (`hokP`). -/
theorem nodeC_W2H {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.X64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hW := Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfC_siX (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.X64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab hsite hb he hst htk
    (by rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP) hph Spike.Lib.X64.HelloPh.ClH.cl
    (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **The counter's `lock xaddq` inside `W2H`** (as `nodeC_W2H`): its word unmapped in private memory (`ha`), off
the arena and not its counter word (`hoff`). -/
theorem nodeCxadd_W2H {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.X64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hok : okPcOf lo helloCells L.Λ n.pc.toBitVec.toNat = true := by
    rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP
  have hW := Spike.Lib.X64.HelloWf.nodeW_wfXaddH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
    (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.X64.HelloPh.ClH L) (lbl := lbl) hI
    (hp ▸ hb) he (Spike.Lib.X64.WakePh.CalWf.nodeW_dt hst) htk
    (Spike.Lib.X64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok) (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph)
    Spike.Lib.X64.HelloPh.ClH.cl (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl ha hoff
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **A header's store inside `W2H`** (as `nodeCxadd_W2H`). -/
theorem nodeCst_W2H {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.X64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hok : okPcOf lo helloCells L.Λ n.pc.toBitVec.toNat = true := by
    rw [Spike.Lib.X64.HelloPh.okPc_eq hΛ]; exact hokP
  have hW := Spike.Lib.X64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
    (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.X64.HelloPh.ClH L) (lbl := lbl) hI
    (hp ▸ hb) he (Spike.Lib.X64.WakePh.CalWf.nodeW_dt hst) htk
    (Spike.Lib.X64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok) (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph)
    Spike.Lib.X64.HelloPh.ClH.cl (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl ha hoff
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

open Spike.Lib.X64.Flow.Reserve (fnL entryL okL rmwPc reserveIn rPro_ok rArg_ok rBnd_ok rJ_ok rRet_ok
  rRet_walk) in
open Spike.Lib.X64.Rt.Reserve (ResG rvN ReserveW) in
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt) in
set_option maxHeartbeats 3200000 in
/-- **`scc_rt_thread_reserve`'s nodes inside `W2H`**, called from `wc_main` returning to `.x23` (`hra`), in a
region with the frame `[-40, 8]`, at no move: each node's `SFactsSt2` (`hst`, at any move) and placement (`hpl`),
the control `q.c0` not at a `ret` with its runs well formed (`hc0`), the counter `scc_rt_nthreads` unmapped under
`F` (`hunN`) and off the arena and not its counter word (`hoffN`). -/
theorem reserveW_W2H (hR : R.OK) (hlo' : R.lo ≤ -40) (hhi : 8 ≤ R.hi) (q : ResG)
    (hra : q.g.ra = (L.lab ".Lwc_main.x23").toBitVec)
    (hc0 : (∀ a, q.c0.term ≠ .ret a) ∧ RunWf helloSrc q.c0 [])
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hoffN : ¬ (ar.heap ≤ (ntA L.lab).toNat ∧ (ntA L.lab).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨ntA L.lab, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, ReserveW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe
      L.endPc R F q i)
    (hpl : ∀ i, ReserveW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F q i) :
    ∀ i, ReserveW W2 (fun _ _ => False) L.exe L.endPc R F q i := by
  obtain ⟨lF, lE, lO⟩ := Spike.Lib.X64.HelloPh.resLabs
  have eF : (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 4199484 := hlab _ _ lF
  have eE : (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 4199492 := hlab _ _ lE
  have eO : (_root_.Executable.labels L.exe).label okL = Int64.ofNat 4199573 := hlab _ _ lO
  have hin := Spike.Lib.X64.Flow.HelloWc.hello_reserveIn
  simp only [reserveIn, siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = q.c0) →
      ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [] :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e => cblk bE rPro_ok eF
  case entry => cnode nodeC_W2H bA eE
  case arg => cblk bArg rArg_ok eE
  case rmw =>
    have hA' : ∀ σ c, (rvN (_root_.Executable.labels L.exe).label q .rmw).J σ c → bAddr σ.regs .rcx 0 = ntA L.lab :=
      fun σ c hJ' => by
        obtain ⟨-, -, -, hc⟩ := hJ'
        rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hc]; first | exact BitVec.add_zero _ | simp
    refine nodeCxadd_W2H hp hlo hΛ hlab hsite bRmw rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunN _ hF)
      (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffN) <;>
      (dsimp only [rvN, rmwPc]; rw [eE]; decide +kernel)
  case bnd => cblk bBnd rBnd_ok eE
  case j => cblk bJ rJ_ok eE
  case ok =>
    refine blkC_W2H hp hlo hΛ hlab hsite (rl := ".Lwc_main.x23") bOk (ofNat_zero' _) rRet_ok hR (by omega)
      (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.X64Consumer.hret_of_run rRet_ok fun σ c hJ' => ?_) (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [rvN]; rw [eO]; revert j; decide +kernel
    · dsimp only [rvN] at hJ' ⊢
      rw [(rRet_walk _ _ hJ'.2).1, hra]; exact Int64.ofBitVec_toBitVec _

open Spike.Lib.X64.Flow.Ret0.AllocTcb in
open Spike.Lib.X64.Flow.Ret0 (hdrBlk_eq rmwBlk_eq) in
open Spike.Lib.X64.Rt (tcbNG TcbWG) in
set_option maxHeartbeats 6400000 in
/-- **The second `scc_rt_alloc_tcb`'s nodes inside `W2H`** (`tcb2QH`, called from `wc_main` returning to `.x24`,
`hra`), in a region with the frame `[-184, 8]`, at no move: each node's `SFactsSt2` (`hst`, at any move) and
placement (`hpl`), the control `c0` (`hc0`), the counter `scc_rt_pinned_next` (`L.pnA`) and the header word
(`L.pinA + 104`) unmapped under `F` (`hunP`, `hunH`) and off the arena and not its counter word (`hoffP`,
`hoffH`). -/
theorem tcbWG_W2H (hR : R.OK) (hlo' : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (g : G) (c0 : Ctl) (hra : g.ra = (L.lab ".Lwc_main.x24").toBitVec)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf helloSrc c0 [])
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧ (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hoffH : ¬ (ar.heap ≤ (L.pinA + 104#64).toNat ∧ (L.pinA + 104#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA + 104#64, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, TcbWG (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc
      R F (tcb2QH g c0) i)
    (hpl : ∀ i, TcbWG (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F (tcb2QH g c0) i) :
    ∀ i, TcbWG W2 (fun _ _ => False) L.exe L.endPc R F (tcb2QH g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := Spike.Lib.X64.HelloPh.Tcb2W.tcb_labsH hlab (L := L)
  have hpn : Spike.Lib.X64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.X64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have hin := Spike.Lib.X64.Flow.HelloWc.hello_allocTcbIn
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bL0⟩, fShr1⟩, bL1⟩, fAnd1⟩, bL2⟩,
    fShr2⟩, bL3⟩, fAnd2⟩, bL4⟩, fImul1⟩, bL5⟩, fShl1⟩, bL6⟩, sLea1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, sOk⟩, bO1⟩,
    fImul2⟩, bO2⟩, fShl2⟩, bO3⟩, fShl3⟩, bO4⟩, fOr1⟩, bO5⟩, bHdr⟩, bRet⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = c0) →
      ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [] :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [TcbWG] at h1 h2 ⊢
  case e => cblk bE atPro_ok eFn
  case entry => cblk bEn atChk_ok eEn
  case j1 => cblk bJ1 atJ1_ok eEn
  case len => cblk bL0 atL0_ok eLen
  case l1 => cblk bL1 atL1_ok eLen
  case l2 => cblk bL2 atL2_ok eLen
  case l3 => cblk bL3 atL3_ok eLen
  case l4 => cblk bL4 atL4_ok eLen
  case l5 => cblk bL5 atL5_ok eLen
  case l6 => cblk bL6 atL6_ok eLen
  case arg => cblk bArg atArg_ok eLen
  case bnd => cblk bBnd atBnd_ok eLen
  case j2 => cblk bJ2 atJ2_ok eLen
  case o1 => cblk bO1 atO1_ok eOk
  case o2 => cblk bO2 atO2_ok eOk
  case o3 => cblk bO3 atO3_ok eOk
  case o4 => cblk bO4 atO4_ok eOk
  case o5 => cblk bO5 atO5_ok eOk
  case shr1 => cnode nodeW_fiW2H fShr1 eLen
  case and1 => cnode nodeW_fiW2H fAnd1 eLen
  case shr2 => cnode nodeW_fiW2H fShr2 eLen
  case and2 => cnode nodeW_fiW2H fAnd2 eLen
  case imul1 => cnode nodeW_fiW2H fImul1 eLen
  case shl1 => cnode nodeW_fiW2H fShl1 eLen
  case lea1 => cnode nodeC_W2H sLea1 eLen
  case ok => cnode nodeC_W2H sOk eOk
  case imul2 => cnode nodeW_fiW2H fImul2 eOk
  case shl2 => cnode nodeW_fiW2H fShl2 eOk
  case shl3 => cnode nodeW_fiW2H fShl3 eOk
  case or1 => cnode nodeW_fiW2H fOr1 eOk
  case rmw =>
    have hA' : ∀ σ c, (tcbNG (_root_.Executable.labels L.exe).label (tcb2QH g c0) .rmw).J σ c →
        bAddr σ.regs .rcx 0 = L.pnA := fun σ c hJ' => by
      dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ'.2.2.2, ← hpn]; first | exact BitVec.add_zero _ | simp
    refine nodeCxadd_W2H hp hlo hΛ hlab hsite bRmw rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunP _ hF)
      (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffP) <;>
      (dsimp only [tcbNG, rmwPc]; rw [eLen]; decide +kernel)
  case hdr =>
    have hA' : ∀ σ c, (tcbNG (_root_.Executable.labels L.exe).label (tcb2QH g c0) .hdr).J σ c →
        bAddr σ.regs .rcx 0 = L.pinA + 104#64 := fun σ c hJ' => by
      dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.X64.Flow.Ret0.bAddr_rcx hJ'.2.2.2, ← hpin, ← tcb2QH_hdrA _ g c0]
      first | exact BitVec.add_zero _ | simp
    refine nodeCst_W2H hp hlo hΛ hlab hsite bHdr rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => by rw [hA' σ c hJ']; exact hunH _ hF)
      (fun σ c m hJ' _ => by rw [hA' σ c hJ']; exact hoffH) <;>
      (dsimp only [tcbNG, hdrPc]; rw [eOk]; decide +kernel)
  case ret =>
    refine blkC_W2H hp hlo hΛ hlab hsite (rl := ".Lwc_main.x24") bRet rfl atRet_ok hR (by omega) (by omega) h1 ?_
      (by decide +kernel) (Spike.Lib.X64Consumer.hret_of_run atRet_ok fun σ c hJ' => ?_) (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [tcbNG]; rw [eOk]; revert j; decide +kernel
    · dsimp only [tcbNG] at hJ' ⊢
      rw [(atRet_walkG _ _ hJ'.2).1]; show Int64.ofBitVec g.ra = _; rw [hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.X64.HelloPh.CalW2

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.blkC_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.blkC_W2H

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.nodeC_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.nodeC_W2H

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.nodeCxadd_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.nodeCxadd_W2H

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.nodeCst_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.nodeCst_W2H

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.reserveW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.reserveW_W2H

/-- info: 'Spike.Lib.X64.HelloPh.CalW2.tcbWG_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.CalW2.tcbWG_W2H
