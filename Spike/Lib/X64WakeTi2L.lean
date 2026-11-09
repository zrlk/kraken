/-
**wake.w's second `scc_rt_thread_init` call inside `W0`** (x86-64; twin of
`Spike/Lib/A64WakeTi2L.lean`, the `hatA` ti discharger): a block or a quiet
single instruction of the call from `wc_main` (and of its nested
`scc_rt_stack_take` call, on stack 0, a pool stack) inside the level
`StartWf.WS`, from its `SFactsSt` at the second instance (`Ti2.blk2_own`,
`node2_own`), as `StartTi.blkI_WS` / `nodeI_WS` with the frame on the pool
(`Ti2.BandP`).

- `dframe_of_callee`: memory kept off a callee's region is kept off the
  caller's.
- `blk2_WS`: a block of the callees inside `WS`.
- `node2_WS`, `node2_WSfi`: a quiet single instruction (an `SI`, an `FI`)
  of the callees inside `WS`.
- `node2_WSxadd`, `node2_WSxchg`, `node2_WSst`: `scc_rt_stack_next`'s
  `lock xaddq`, the stack lock's `xchgq` and the TCB fields' (and the lock's
  release) stores inside `WS`.

**Unlike AArch64**: as `Spike/Lib/X64WakeStartTiL.lean` (no `hal`; frame
high end `8`; `cellOff` / `z`-byte pcs; `blockAtB`; a `ret`'s target the
slot at `%rsp`; AArch64's `node2_WSldop` is `node2_WSxadd`, its `swp`
(`node2_WSswp`, `A64WakeTi2L2`) is `node2_WSxchg` here, `node2_WSfi` is
new). `dframe_of_callee` takes the callee's high end `hi'` (A64's `0`;
x86-64 callee regions end at `8`, the return address) with
`kc + hi' ≤ R.hi` (`hhi`, implied by `hkc` on AArch64).
-/
import Spike.Lib.X64WakeStartTiL
import Spike.Lib.X64WakeTi2G

namespace Spike.Lib.X64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk SI FI Abs stDir xaddDir xchgDir bAddr)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.StartWf (WS pfxM)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64.WakePh.Ti2 (BandP blk2_own node2_own)

/-- **Memory kept off a callee's region is kept off the caller's**: the
callee's frame (at `kc`, from `lo'` to `hi'`) inside the region's. -/
theorem dframe_of_callee {R : Spike.Lib.Region} {kc lo' hi' : Int} {m m' : MachineData} (hR : R.OK)
    (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (hhi : kc + hi' ≤ R.hi)
    (h : Spike.Lib.X64.DFrame (R.callee kc lo' hi') m m') : Spike.Lib.X64.DFrame R m m' := by
  have hb := Spike.Lib.Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  intro x hx hout
  refine h x hx ?_
  show (x.toNat : Int) + 8 ≤ ((R.callee kc lo' hi').base.toNat : Int) + lo' ∨
    ((R.callee kc lo' hi').base.toNat : Int) + hi' ≤ x.toNat
  omega

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range} {Tk : State → Prop}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
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

/-- **A block of the callees inside `WS`**: its `SFactsSt` at the second
instance (`hS`), its pcs off the sites (`hokpc`) and in the callees off the
take site (`h1`), its static `%rsp` offsets in `[klo, 8]` (`hso`), `Good2b`
where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). `hS` is control-blind
(`SFactsSt`): **the real control's facts enter here only**, its run facts
from `hc0` and its placement from `hpl0` at `hPl`'s frame, at the node's
control (`hJ`); the same in `node2_WS*`. -/
theorem blk2_WS {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcN (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI (hp ▸ hb) hs hn
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    blk2_own hlab hbd (StartTcb.siteT hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.WakeWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ hF hJ' _ _ _ _ hD => by rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF hD), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inI_of hlab (h1 j hj).1) (offSite hlab (h1 j hj)), fun _ h => h⟩

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcrossB`): as `blk2_WS`. -/
theorem blk2_WSA {n : ND} {blk : List (Directive × Nat)} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    (hb : Scc.Cert.Rt.X64.blockAcrossB wakeCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcN (n.pc + Int64.ofNat (cellOff blk j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 8)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk := 
    Spike.Lib.X64.code_field_blockAcrossB hI.lays hI.endOk (hp ▸ hb) (List.take_append_drop jA blk)
      (by rw [hI.labOk]; exact he)
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    blk2_own hlab hbd (StartTcb.siteT hlab hsite) hS hcode hok hR hlo' hhi h1 hso hfin
  have hw := Spike.Lib.X64.WakeWf.blkW_wfQA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.WakeWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ hF hJ' _ _ _ _ hD => by rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF hD), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inI_of hlab (h1 j hj).1) (offSite hlab (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the callees inside `WS`**: its `SFactsSt`
at the second instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `%rsp` and `%rbp` `z` bytes on (`hk`), its pc in the
callees off the take site and the next in the callees (`hpc`), its static
`%rsp` offset in `[klo, 8]` (`hso`), its abort phases' check (`hph`), its
controls `c0` (`hJ`). -/
theorem node2_WS {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A quiet single instruction with undefined flags of the callees inside
`WS`** (as `node2_WS`, at an `FI`: the take's `shlq` / `shrq %cl`). -/
theorem node2_WSfi {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfQF (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **`scc_rt_stack_next`'s `lock xaddq` inside `WS`** (as `node2_WS`):
`lock xaddq %r, i(%b)` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem node2_WSxadd {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(xaddDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfXadd (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The stack lock's `xchgq` inside `WS`** (as `node2_WS`; AArch64's
`swp`): `xchgq %r, i(%b)` of a word unmapped in private memory (`ha`), off
the arena and not the counter word (`hoff`). -/
theorem node2_WSxchg {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(xchgDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfXchg (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A TCB field's store inside `WS`** (as `node2_WS`): `movq %r, i(%b)`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem node2_WSst {n : ND} {b r : Reg64} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(stDir b i r, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt L.Λ (Spike.Lib.X64.PhRec.μ L)
        (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat z)
    (hpc : PcN n.pc ∧ PcI (n.pc + Int64.ofNat z)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (bAddr σ.regs b i).toNat ∧ (bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.X64.WakeWf.nodeW_wfSt (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
    (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.X64.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

end Gen

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.dframe_of_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.dframe_of_callee

/-- info: 'Spike.Lib.X64.WakePh.StartTi.blk2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.blk2_WS

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WS

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WSfi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WSfi

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WSxadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WSxadd

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WSxchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WSxchg

/-- info: 'Spike.Lib.X64.WakePh.StartTi.node2_WSst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.node2_WSst
