/-
**wake.w's second `scc_rt_thread_init` call inside `W0`** (AArch64; the
`hatA` ti discharger): a block or a quiet single instruction of the call
from `wc_main` (and of its nested `scc_rt_stack_take` call, on stack 0, a
pool stack) inside the level `StartWf.WS`, from its `SFactsSt` at the second
instance (`Ti2.blk2_own`, `node2_own`), as `StartTi.blkI_WS` / `nodeI_WS`
with the frame on the pool (`Ti2.BandP`).

- `blk2_WS`: a block of the callees inside `WS`.
- `node2_WS`: a quiet single instruction of the callees inside `WS`.
- `node2_WSldop`, `node2_WSst`: `scc_rt_stack_next`'s add and the TCB
  fields' stores inside `WS`.
-/
import Spike.Lib.A64WakeStartTiL
import Spike.Lib.A64WakeTi2G

namespace Spike.Lib.A64.WakePh.StartTi

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
open Spike.Lib.A64.WakePh.Ti2 (BandP blk2_own node2_own)

/-- **Memory kept off a callee's region is kept off the caller's**: the
callee's frame (at `kc`, from `lo'` to `0`) inside the region's. -/
theorem dframe_of_callee {R : Spike.Lib.Region} {kc lo' : Int} {m m' : MachineData} (hR : R.OK)
    (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi)
    (h : Spike.Lib.A64.Flow.DFrame (R.callee kc lo' 0) m m') : Spike.Lib.A64.Flow.DFrame R m m' := by
  have hb := Spike.Lib.Region.callee_base (hi' := 0) hR hlo hlo0 hkc
  intro x hx hout
  refine h x hx ?_
  show (x.toNat : Int) + 8 ≤ ((R.callee kc lo' 0).base.toNat : Int) + lo' ∨
    ((R.callee kc lo' 0).base.toNat : Int) + 0 ≤ x.toNat
  omega

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandP L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd

/-- **A block of the callees inside `WS`**: its `SFactsSt` at the second
instance (`hS`), its pcs off the sites (`hokpc`) and in the callees off the
take site (`h1`), its static `sp` offsets in `[klo, 0]` (`hso`), `Good2b`
where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). `hS` is control-blind
(`SFactsSt`): **the real control's facts enter here only**, its run facts
from `hc0` and its placement from `hpl0` at `hPl`'s frame, at the node's
control (`hJ`); the same in `node2_WS*` and `site2_WS`. -/
theorem blk2_WS {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcN (n.pc + Int64.ofNat (4 * j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s)
    (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    blk2_own hlab hbd (StartTcb.siteT hlab hsite) hS hcode hok hR hal hlo' hhi h1 hso hfin
  have hw := Spike.Lib.A64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.WakeWf.phOffW_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ hF hJ' _ _ _ _ hD => by rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF hD), fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inI_of hlab (h1 j hj).1) (offSite hlab (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the callees inside `WS`**: its `SFactsSt`
at the second instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `sp` and `x30` 4 bytes on (`hk`), its pc in the callees
off the take site and the next in the callees (`hpc`), its static `sp`
offset in `[klo, 0]` (`hso`), its abort phases' check (`hph`), its controls
`c0` (`hJ`). -/
theorem node2_WS {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **`scc_rt_stack_next`'s add inside `WS`** (as `node2_WS`):
`ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem node2_WSldop {n : ND} {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfLdop (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A TCB field's store inside `WS`** (as `node2_WS`): `str Xt, [Xn, #i]`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem node2_WSst {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
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
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTi.blk2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blk2_WS

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WS

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WSldop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WSldop

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WSst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WSst

end Spike.Lib.A64.WakePh.StartTi
