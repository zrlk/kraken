/-
**hello.w's second `scc_rt_thread_init` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64HelloTi2L.lean`, the `hatA` ti discharger, and of wake's
`X64WakeTi2L` at `SccCode.helloCells`): a block or a single instruction of
the call from `wc_main` (and of its nested `scc_rt_stack_take` call, on a
pool stack) inside the level `HelloPh.StartWf.WSH`, from its `SFactsSt` at
the second instance (`Ti2.blk2_ownH`, `node2_ownH`, `site2_ownH`), as
`StartTi.blkI_WSH` … `siteI_WSH` with the frame on the pool (`Ti2.BandP`)
and the placement from `hPl`'s frame; the phases from the decided checks at
hello's threads abort phase.

- `blk2_WSH`: a block of the callees inside `WSH`.
- `node2_WSH`, `node2_WSfiH`: a quiet single instruction (an `SI`, an `FI`)
  of the callees inside `WSH`.
- `node2_WSxaddH`, `node2_WSxchgH`, `node2_WSstH`, `node2_WSldH`:
  `scc_rt_stack_next`'s `lock xaddq`, the stack lock's `xchgq`, the TCB
  fields' (and the lock's release) stores and the free count's load inside
  `WSH`.
- `site2_WSH`: the take site inside `WSH`.

**Unlike AArch64**: as `Spike/Lib/X64HelloStartTiL.lean` (no `hal`; frame
high end `8`; `cellOff` / `z`-byte pcs; `blockAtB`; a `ret`'s target the
slot at `%rsp`; the take site's literal `4200314`). AArch64's
`node2_WSldopH` is `node2_WSxaddH`, `node2_WSswpH` is `node2_WSxchgH`,
`node2_WSldrH` is `node2_WSldH` and `node2_WSstlrH` is folded into
`node2_WSstH` (the release a plain `movq`); `node2_WSfiH` is new (the take's
`shlq` / `shrq %cl`). `site2_WSH` takes the site region's cells as wake's
`X64WakeTi2L` site lemma does.
-/
import Spike.Lib.X64HelloStartTiL
import Spike.Lib.X64HelloTi2G
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64WakeTi2L

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
open Spike.Lib.X64.WakePh.Ti2 (BandP)

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range} {Tk : State → Prop}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 [])
  (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.X64.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandP L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd

/-- **A block of the callees inside `WSH`**: its `SFactsSt` at the second
instance (`hS`), its pcs off the sites (`hokpc`) and in the callees off the
take site (`h1`), its static `%rsp` offsets in `[klo, 8]` (`hso`), `Good2bH`
where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). -/
theorem blk2_WSH {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
      Good2bH L s)
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
    Ti2.blk2_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ hF hJ' _ _ _ _ hD => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF hD), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcrossB`): as `blk2_WSH`. -/
theorem blk2_WSHA {n : ND} {blk : List (Directive × Nat)} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    (hb : Scc.Cert.Rt.X64.blockAcrossB helloCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
      Good2bH L s)
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
    Ti2.blk2_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.HelloPh.StartWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ hF hJ' _ _ _ _ hD => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF hD), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the callees inside `WSH`**: its `SFactsSt`
at the second instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc in the
callees off the take site and the next in the callees (`hpc`), its static
`%rsp` offset in `[klo, 8]` (`hso`), its abort phases' check (`hph`), its
controls `c0` (`hJ`). -/
theorem node2_WSH {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A quiet single instruction with undefined flags of the callees inside
`WSH`** (as `node2_WSH`, at an `FI`: the take's `shlq` / `shrq %cl`). -/
theorem node2_WSfiH {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **`scc_rt_stack_next`'s `lock xaddq` inside `WSH`** (as `node2_WSH`):
`lock xaddq %r, i(%b)` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem node2_WSxaddH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The stack lock's `xchgq` inside `WSH`** (as `node2_WSH`; AArch64's
`swp`): `xchgq %r, i(%b)` of a word unmapped in private memory (`ha`), off
the arena and not the counter word (`hoff`). -/
theorem node2_WSxchgH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(xchgDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A TCB field's store inside `WSH`** (as `node2_WSH`): `movq %r, i(%b)`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem node2_WSstH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The free count's load inside `WSH`** (as `node2_WSH`): `movq i(%b), %r`
of a word unmapped in private memory (`ha`). -/
theorem node2_WSldH {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(ldDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (Ti2.node2_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The take site inside `WSH`**: the `nop` (`hb`), its states' `SFactsSt` at
the second instance (`hS`), off the abort sites (`habt`), its successors
keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc and the next in the
callees (`hpc`), its static `%rsp` offset in `[klo, 8]` (`hso`), its abort
phases' check (`hph`), its controls `c0` (`hJ`); `X0` at the site's states
from their take range, frame and region cells (`hXs`), off it by `hX0`. -/
theorem site2_WSH {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB helloCells l k [(op64 (.nop 1), z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
    (habt : ∀ k x, (Spike.Lib.X64.PhRec.μ L).abortAt k = some x → n.pc.toBitVec.toNat ≠ x)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 →
      (∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) → X0 s) :
    ∀ s c, At L.exe L.endPc R F n s c → WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.HelloWf.site_wfH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) (Dt := Dt) hI (hp ▸ hb) he (Ti2.site2_ownH hlab hbd hS hk hpc hso) habt
    (Spike.Lib.X64.HelloWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)))
  intro s c hA
  have hpc' := hA.2.2.2.1
  have hx : X0 s := by
    by_cases hs : pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
    · obtain ⟨-, -, -, -, σ, hAb, hF, -⟩ := id hA
      refine hXs s hs ((hS s c hA).site _ hsite hs).2.2.2.1 hF fun k hk => ?_
      obtain ⟨j, hj, -⟩ := hAb.slot k hk
      rw [hj]; rfl
    · exact hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1)) hs
  exact ⟨.inl rfl, hx, hw s c hA⟩

end Gen
end Spike.Lib.X64.HelloPh.StartTi

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.blk2_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.blk2_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSfiH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSfiH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSxaddH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSxaddH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSxchgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSxchgH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSstH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.node2_WSldH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.node2_WSldH

/-- info: 'Spike.Lib.X64.HelloPh.StartTi.site2_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTi.site2_WSH
