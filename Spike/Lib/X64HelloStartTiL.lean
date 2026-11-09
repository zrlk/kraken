/-
**hello.w's `scc_rt_thread_init` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64HelloStartTiL.lean`, wake's `X64WakeStartTiL` and
`X64WakeStartTiL2` at `SccCode.helloCells`): a block or a single
instruction of the call from `scc_rt_start` (and of its nested
`scc_rt_stack_take` call) inside the start's level `HelloPh.StartWf.WSH`,
from its `SFacts` at the first instance (`StartTi.blkI_ownH`, `nodeI_ownH`,
`siteI_ownH`), the frame's low end `klo` a parameter (`StartTi.BandI`); the
phases from the decided checks at hello's threads abort phase
(`HelloWf.phOffW`, `siOffW`).

- `nodeW_wfQH`, `nodeW_wfQFH`: a quiet single instruction (an `SI`, an
  `FI`) inside `Wf` at `AcH` (hello's `WakeWf.nodeW_wfQ` / `nodeW_wfQF`).
- `tkIH`: a pc of the callees off the take site is off the marks' take site.
- `blkI_WSH`: a block of the callees inside `WSH`.
- `nodeI_WSH`, `nodeI_WSfiH`: a quiet single instruction (an `SI`, an `FI`)
  of the callees inside `WSH`.
- `nodeI_WSxaddH`, `nodeI_WSxchgH`, `nodeI_WSstH`, `nodeI_WSldH`:
  `scc_rt_stack_next`'s `lock xaddq`, the stack lock's `xchgq`, the TCB
  fields' (and the lock's release) stores and the free count's load inside
  `WSH`.
- `siteI_WSH`: the take site inside `WSH`.

## Differences from the AArch64 version

As wake's x86-64 `StartTiL` / `StartTiL2`: no `hal`; a frame's high end is
`8` (`hso`'s `n.o.sp ≤ 8`); a block's pcs are `cellOff` bytes on (A64's
`4 * j`) and a node's successor `z` bytes on (A64's `4`), the instruction
at byte offset `k` of `l` (`blockAtB`); `Keep` is `%rsp`/`%rbp`; the take
site's literal is `4200314` (A64's `2165980`, `StartTi.siteTH`); a `ret`'s
target is the stack slot at `%rsp` (`hret`; A64's `x30`); the spawn prefix
is the x86-64 start's (`StartWf.pfxM`). AArch64's `nodeI_WSldopH` (`ldadd`)
becomes `nodeI_WSxaddH` (`lock xaddq`), `nodeI_WSswpH` becomes
`nodeI_WSxchgH`, `nodeI_WSldrH` becomes `nodeI_WSldH` (`movq i(%b), %r`)
and `nodeI_WSstlrH` is `nodeI_WSstH` (the release a plain `movq`);
`nodeI_WSfiH` is new (the take's `shlq` / `shrq %cl`, flags undefined), and
the site's `nop` is `op64 (.nop 1)` of size `z`. `hoff` of the RMW nodes
takes the memory `m` (as `HelloWf.nodeW_wfXaddH`). AArch64's
`HelloWf.nodeW_wfQH` has no x86-64 counterpart in `X64HelloWfW`, so
`nodeW_wfQH` (and its `FI` form `nodeW_wfQFH`) are proved here from
`WakeWf.nodeW_wf` and `HelloWf.nodeW_phSt`, as `WakeWf.nodeW_wfQ`.
-/
import Spike.Lib.X64HelloStartTiG
import Spike.Lib.X64HelloWfW
import Spike.Lib.X64HelloStartWf

namespace Spike.Lib.X64.HelloPh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk SI FI Abs stDir xaddDir xchgDir ldDir bAddr)
open Spike.Lib.X64.WakeWf (RunWf Wf)
open Spike.Lib.X64.HelloPh.StartWf (WSH pfxM)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh (inPc Keep)
open Spike.Lib.X64.WakePh.StartTi (BandI)
open Spike.Lib.X64.HelloPh.Ti2 (PcIH PcNH inIH_of offSiteH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (op64)

section Q

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {ar : Arena} {p : Prog}
  {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {pfx : String}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {K : State → State → Prop} {fs : List TermRun.Frame}
  [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {lab : Label → Int64}
  {μ' : Marks} {own' : Spike.Lib.X64Consumer.Own} {Tk : State → Prop} {K' : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A quiet single instruction's states inside `Wf`** at the frames `fs`
and hello's threads abort phase `AcH` (`WakeWf.nodeW_wfQ` at
`HelloWf.siOff`): an instruction without an event (`hb`) whose states have
the state's facts (`hst`), its pc off the take and abort sites (`htk`,
`habt`), its next pc off both abort phases' pcs (`hph`), the control at the
node's invariant (`hJ`), the frames placed (`hpl`). -/
theorem nodeW_wfQH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : Spike.Lib.X64.HelloWf.siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx lbl lsize s c fs) K exe endPc R F n := by
  have hstep := Spike.Lib.X64.WakeWf.si_step (R := R) (F := F) hI hb he
  have hnw := Spike.Lib.X64.AllocG.nodeW_noWr_si (R := R) (F := F) hI hb he rfl
  have hl := hI.labOk
  subst hl
  have hP := Spike.Lib.X64.HelloWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine Spike.Lib.X64.WakeWf.nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨((Spike.Lib.X64.WakeWf.nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1,
      ((Spike.Lib.X64.WakeWf.nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.nodeW_noWrC hnw) (Spike.Lib.X64.WakeWf.nodeW_abortWf_off habt)

/-- **A quiet single instruction with undefined flags inside `Wf`** at
`AcH` (as `nodeW_wfQH`, at an `FI`). -/
theorem nodeW_wfQFH (hI : InstOk exe endPc cells lab μ' own' Tk K' okPc ph kp) {n : ND}
    {fi : FI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (habt : ∀ k a, μ.abortAt k = some a → n.pc.toBitVec.toNat ≠ a)
    (hph : Spike.Lib.X64.HelloWf.siOff lab pfx l k z = true)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => Wf Λ μ own ar p Dt (Spike.Lib.X64.WriteAb.Ab lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH lab pfx) Ctx lbl lsize s c fs) K exe endPc R F n := by
  have hstep := Spike.Lib.X64.WakeWf.fi_step (R := R) (F := F) hI hb he
  have hnw := Spike.Lib.X64.AllocG.nodeW_noWr_fi (R := R) (F := F) hI hb he rfl
  have hl := hI.labOk
  subst hl
  have hP := Spike.Lib.X64.HelloWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) he hph htk hstep
  refine Spike.Lib.X64.WakeWf.nodeW_wf hst (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hcl
    (fun s c hA => ⟨⟨((Spike.Lib.X64.WakeWf.nodeW_ofJ hJ) s c hA).1.1, (hpl s c hA).1,
      ((Spike.Lib.X64.WakeWf.nodeW_ofJ hJ) s c hA).1.2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.nodeW_noWrC hnw) (Spike.Lib.X64.WakeWf.nodeW_abortWf_off habt)

end Q

/-- A pc of the callees off the take site is off the marks' take site. -/
theorem tkIH {L : RuntimeLayout}
    (hsite' : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → x = 4200314) {q : Int64} (h : PcNH q) :
    ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → q.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite' x hx]; exact h.2

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandI L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

/-- **A block of the callees inside `WSH`**: its `SFacts` at the first
instance (`hS`), its pcs off the sites (`hokpc`) and in the callees off the
take site (`h1`), its static `%rsp` offsets in `[klo, 8]` (`hso`), `GoodWH`
where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). -/
theorem blkI_WSH {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcNH (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
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
    blkI_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcrossB`): as `blkI_WSH`. -/
theorem blkI_WSHA {n : ND} {blk : List (Directive × Nat)} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    (hb : Scc.Cert.Rt.X64.blockAcrossB helloCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcNH (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
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
    blkI_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the callees inside `WSH`**: its `SFacts`
at the first instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc in the
callees off the take site and the next in the callees (`hpc`), its static
`%rsp` offset in `[klo, 8]` (`hso`), its abort phases' check (`hph`), its
controls `c0` (`hJ`). -/
theorem nodeI_WSH {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := nodeW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A quiet single instruction with undefined flags of the callees inside
`WSH`** (as `nodeI_WSH`, at an `FI`: the take's `shlq` / `shrq %cl`). -/
theorem nodeI_WSfiH {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := nodeW_wfQFH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **`scc_rt_stack_next`'s `lock xaddq` inside `WSH`** (as `nodeI_WSH`):
`lock xaddq %r, i(%b)` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeI_WSxaddH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfXaddH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The stack lock's `xchgq` inside `WSH`** (as `nodeI_WSH`; AArch64's
`swp`): `xchgq %r, i(%b)` of a word unmapped in private memory (`ha`), off
the arena and not the counter word (`hoff`). -/
theorem nodeI_WSxchgH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xchgDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfXchgH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A TCB field's store inside `WSH`** (as `nodeI_WSH`): `movq %r, i(%b)`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem nodeI_WSstH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The free count's load inside `WSH`** (as `nodeI_WSH`): `movq i(%b), %r`
of a word unmapped in private memory (`ha`). -/
theorem nodeI_WSldH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(ldDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo helloCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.nodeW_wfLdH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1)) (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The take site inside `WSH`**: the `nop` (`hb`), its states' `SFacts` at
the first instance (`hS`), off the abort sites (`habt`), its successors
keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc and the next in the
callees (`hpc`), its static `%rsp` offset in `[klo, 8]` (`hso`), its abort
phases' check (`hph`), its controls `c0` (`hJ`); `X0` at the site's states
from their take range and frame (`hXs`), off it by `hX0`. -/
theorem siteI_WSH {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(op64 (.nop 1), z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
    (habt : ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → n.pc.toBitVec.toNat ≠ x)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → X0 s) :
    ∀ s c, At L.exe L.endPc R F n s c → WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.site_wfH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) (Dt := Dt) hI (hp ▸ hb) he (siteI_ownH hlab hbd hS hk hpc hso) habt
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact hpl0 _)
  intro s c hA
  have hpc' := hA.2.2.2.1
  have hx : X0 s := by
    by_cases hs : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
    · obtain ⟨-, -, -, -, σ, -, hF, -⟩ := id hA
      exact hXs s hs ((hS s c hA).site _ hsite hs).2.2.2.1 hF
    · exact hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1)) hs
  exact ⟨.inl rfl, hx, hw s c hA⟩

end Gen

end Spike.Lib.X64.HelloPh.StartTi

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQFH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeW_wfQFH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.tkIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.tkIH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.blkI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.blkI_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSfiH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSfiH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSxaddH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSxaddH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSxchgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSxchgH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSstH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.nodeI_WSldH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.nodeI_WSldH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.siteI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.siteI_WSH
