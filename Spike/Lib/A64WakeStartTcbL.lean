/-
**wake.w's first `scc_rt_alloc_tcb` call inside `W0`** (AArch64): a block
or a quiet single instruction of the call from `scc_rt_start` inside the
start's level `StartWf.WS` (`W0` at the frames `[]` at `ownG`), from its
`SFacts` at the first instance (`StartTcb.blkT_own`, `nodeT_own`), the two
abort phases from the decided checks (`phOffW`, `siOffW`), the rest from
`WakeWf.blkW_wfQ` / `nodeW_wfQ`, `X0` at the callee's pcs.

- `blkT_WS`: a block of the call inside `WS`.
- `nodeT_WS`: a quiet single instruction of the call inside `WS`.
- `nodeT_WSldop`, `nodeT_WSst`: the counter's add and the header's store
  inside `WS`.
-/
import Spike.Lib.A64WakeStartTcbG

namespace Spike.Lib.A64.WakePh.StartTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.Tcb2W (soRun)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s → X0 s)
  (hbd : BandT L R)

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

/-- **A block of the call inside `WS`**: its `SFacts` at the first instance
(`hS`), its pcs off the sites (`hokpc`) and in the callee (`h1`), its
static `sp` offsets in `[-192, 0]` (`hso`), `GoodW` where its run ends
(`hfin`), its abort phases' check (`hph`, its `ret`s to `L.lab rl`,
`hret`), its controls `c0` (`hJ`). -/
theorem blkT_WS {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcT (n.pc + Int64.ofNat (4 * j)))
    (hso : ∀ j ≤ blk.length, -192 ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s)
    (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    blkT_own hlab hbd (siteT hlab hsite) hS hcode hok hR hal hlo' hhi h1 hso hfin
  have hw := Spike.Lib.A64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.WakeWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inT_of hlab (h1 j hj)), fun _ h => h⟩

omit hp hlo hcl hc0 hpl0 hX0 hbd in
/-- A pc of the callee is off the take site. -/
theorem tkT {q : Int64} (h : PcT q) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → q.toBitVec.toNat ≠ x := fun x hx => by
  rw [siteT hlab hsite x hx]; unfold PcT at h; omega

/-- **A quiet single instruction of the call inside `WS`**: its `SFacts` at
the first instance (`hS`), its pc off the sites (`hokpc`), its successors
keeping `sp` and `x30` 4 bytes on (`hk`), its pc and the next in the callee
(`hpc`), its static `sp` offset in `[-192, 0]` (`hso`), its abort phases'
check (`hph`), its controls `c0` (`hJ`). -/
theorem nodeT_WS {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcT n.pc ∧ PcT (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    nodeT_own hlab hbd hS hk hpc hso
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hst (tkT hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inT_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The counter's add of the call inside `WS`** (as `nodeT_WS`):
`ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeT_WSldop {n : ND} {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcT n.pc ∧ PcT (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfLdop (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_own (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkT hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inT_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The header's store of the call inside `WS`** (as `nodeT_WS`):
`str Xt, [Xn, #i]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeT_WSst {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcT n.pc ∧ PcT (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat ∧
        (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfSt (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeT_own (Dt := Dt) hlab hbd hS hk hpc hso)
    (tkT hlab hsite hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inT_of hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.nodeT_WSldop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeT_WSldop

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.nodeT_WSst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeT_WSst

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.blkT_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkT_WS

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.tkT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tkT

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.nodeT_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeT_WS

end Spike.Lib.A64.WakePh.StartTcb
