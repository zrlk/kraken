/-
**hello.w's first `scc_rt_alloc_tcb` call inside `W0` on x86-64** (the twin of
`Spike/Lib/A64HelloStartTcbL.lean`; wake's `Spike/Lib/X64WakeStartTcbL.lean` at `SccCode.helloCells`): a block
or a quiet single instruction of the call from `scc_rt_start` inside the start's level `HelloPh.StartWf.WSH` (at
the frames `[]` at `ownGH`), from its `SFacts` at the first instance (`StartTcb.blkT_ownH`, `nodeT_ownH`), the
abort phases from hello's decided checks (`HelloWf.phOffW`, `siOffW`), the rest from `StartWf.blkW_wfQH` /
`StartTi.nodeW_wfQH` / `nodeW_wfQFH` and `HelloWf.nodeW_wfXaddH` / `nodeW_wfStH`, `X0` at the callee's pcs.

- `tkTH`: a pc of the callee is off the marks' take site.
- `blkT_WSH`: a block of the call inside `WSH`.
- `nodeT_WSH`, `nodeT_WSfiH`: a quiet single instruction (an `SI`, an `FI`) of the call inside `WSH`.
- `nodeT_WSxaddH`, `nodeT_WSstH`: the counter's `lock xaddq` and the header's store inside `WSH`.

## Differences from the AArch64 version

As wake's x86-64 `StartTcbL`: no `hal`; the frame is `[-184, 8]` (`BandT`; AArch64's `[-192, 0]`); a block's
pcs are `cellOff` bytes on (AArch64's `4 * j`) and a node's successor `z` bytes on (AArch64's `4`), the
instruction at byte offset `k` of `l` (`blockAtB`); `Keep` is `%rsp`/`%rbp`; a `ret`'s target is the stack slot
at `%rsp` (`hret`); the take site is `4200314` (`StartTi.siteTH`); the spawn prefix is the x86-64 start's
(`StartWf.pfxM`). AArch64's `nodeT_WSldopH` (`ldadd`) becomes `nodeT_WSxaddH` (`lock xaddq`), its `hoff` taking
the memory `m` (as `HelloWf.nodeW_wfXaddH`); `nodeT_WSfiH` is new (the length's and the header's
flag-clobbering instructions).
-/
import Spike.Lib.X64HelloStartTcbG
import Spike.Lib.X64HelloStartTiL

namespace Spike.Lib.X64.HelloPh.StartTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk SI FI Abs stDir xaddDir xchgDir bAddr)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh.StartWf (WSH pfxM)
open Spike.Lib.X64.WakePh (inPc Keep)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.HelloPh.StartTi (siteTH)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s → X0 s)
  (hbd : BandT L R)

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

omit hp hlo hcl hc0 hpl0 hX0 hbd in
/-- A pc of the callee is off the marks' take site. -/
theorem tkTH {q : Int64} (h : PcTH q) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → q.toBitVec.toNat ≠ x := fun x hx => by
  rw [siteTH hlab hsite x hx]; unfold PcTH at h; omega

/-- **A block of the call inside `WSH`**: its `SFacts` at the first
instance (`hS`), its pcs off the sites (`hokpc`) and in the callee (`h1`), its
static `%rsp` offsets in `[-184, 8]` (`hso`), `GoodWH` where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). -/
theorem blkT_WSH {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcTH (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, -184 ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI (hp ▸ hb) hs hn
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    blkT_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inTH_of hlab (h1 j hj)), fun _ h => h⟩

/-- **A block of the call split by a return label inside `WSH`** (`m`, after
its first `jA` rows; `blockAcrossB`): as `blkT_WSH`. -/
theorem blkT_WSHA {n : ND} {blk : List (Directive × Nat)} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    (hb : Scc.Cert.Rt.X64.blockAcrossB helloCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcTH (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, -184 ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s)
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk :=
    Spike.Lib.X64.code_field_blockAcrossB hI.lays hI.endOk (hp ▸ hb) (List.take_append_drop jA blk)
      (by rw [hI.labOk]; exact he)
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    blkT_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inTH_of hlab (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the call inside `WSH`**: its `SFacts`
at the first instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc in the
callee and the next in the callee (`hpc`), its static
`%rsp` offset in `[-184, 8]` (`hso`), its abort phases' check (`hph`), its
controls `c0` (`hJ`). -/
theorem nodeT_WSH {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + Int64.ofNat z)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_ownH (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkTH hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inTH_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A quiet single instruction with undefined flags of the call inside
`WSH`** (as `nodeT_WSH`, at an `FI`: the length's and the header's
`shr`/`and`/`imul`/`shl`/`or`). -/
theorem nodeT_WSfiH {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + Int64.ofNat z)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQFH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_ownH (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkTH hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inTH_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The counter's `lock xaddq` inside `WSH`** (as `nodeT_WSH`):
`lock xaddq %r, i(%b)` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeT_WSxaddH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + Int64.ofNat z)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfXaddH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_ownH (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkTH hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inTH_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The header's store inside `WSH`** (as `nodeT_WSH`): `movq %r, i(%b)`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem nodeT_WSstH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + Int64.ofNat z)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_ownH (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkTH hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inTH_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

end Gen

end Spike.Lib.X64.HelloPh.StartTcb

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.tkTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.tkTH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.blkT_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.blkT_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSfiH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSfiH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSxaddH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSxaddH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.nodeT_WSstH
