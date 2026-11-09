/-
**hello.w's `scc_rt_thread_init` call inside `W0`** (AArch64,
the `hti` chain; twin of `Spike/Lib/A64WakeStartTiL.lean` and
`A64WakeStartTiL2.lean` at helloProg): a block or a single instruction of the
call from `scc_rt_start` (and of its nested `scc_rt_stack_take` call) inside
the start's level `HelloPh.StartWf.WSH`, from its `SFacts` at the first
instance (`StartTi.blkI_ownH`, `nodeI_ownH`, `siteI_ownH`), the frame's low
end `klo` a parameter (`StartTi.BandI`); the phases from the decided checks
at hello's threads abort phase (`HelloWf.phOffHC`, `siOffHC`).

- `blkI_WSH`: a block of the callees inside `WSH`.
- `nodeI_WSH`: a quiet single instruction of the callees inside `WSH`.
- `nodeI_WSldopH`, `nodeI_WSstH`: `scc_rt_stack_next`'s add and the TCB
  fields' stores inside `WSH`.
- `nodeI_WSswpH`, `nodeI_WSldrH`, `nodeI_WSstlrH`: the lock's swap, the free
  count's load and the lock's release inside `WSH`.
- `siteI_WSH`: the take site inside `WSH`.
-/
import Spike.Lib.A64HelloStartTiG
import Spike.Lib.A64HelloWfW
import Spike.Lib.A64HelloStartWf

namespace Spike.Lib.A64.HelloPh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf swpDir stlrDir)
open Spike.Lib.A64.WakePh (inPc Keep)
open Spike.Lib.A64.WakePh.Tcb2W (soRun)
open Spike.Lib.A64.WakePh.StartTi (BandI)
open Spike.Lib.A64.HelloPh.Ti2 (PcIH PcNH inIH_of offSiteH)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout}

/-- A pc of the callees off the take site is off the marks' take site. -/
theorem tkIH (hsite' : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165980) {q : Int64}
    (h : PcNH q) : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → q.toBitVec.toNat ≠ x := fun x hx => by
  rw [hsite' x hx]; exact h.2

section Gen

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandI L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd

/-- **A block of the callees inside `WSH`**: its `SFacts` at the first
instance (`hS`), its pcs off the sites (`hokpc`) and in the callees off the
take site (`h1`), its static `sp` offsets in `[klo, 0]` (`hso`), `GoodWH`
where its run ends (`hfin`), its abort phases' check (`hph`, its `ret`s to
`L.lab rl`, `hret`), its controls `c0` (`hJ`). -/
theorem blkI_WSH {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcNH (n.pc + Int64.ofNat (4 * j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    blkI_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hal hlo' hhi h1 hso hfin
  have hw := Spike.Lib.A64.HelloWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.HelloWf.phOffHC_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcross`): as `blkI_WSH`. -/
theorem blkI_WSHA {n : ND} {blk : List Directive} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    (hb : Scc.Cert.Rt.A64.blockAcross SccCode.helloProg l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (h1 : ∀ j < blk.length, PcNH (n.pc + Int64.ofNat (4 * j)))
    (hso : ∀ j ≤ blk.length, klo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode := Spike.Lib.A64.code_field_blockAcross L.lays rfl (hp ▸ hb)
    (List.take_append_drop jA blk) (q := n.pc) he
  have hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    blkI_ownH hlab hbd (siteTH hlab hsite) hS hcode hok hR hal hlo' hhi h1 hso hfin
  have hw := Spike.Lib.A64.HelloWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.HelloWf.phOffHC_sound hlab hph) hret hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (inIH_of hlab (h1 j hj).1) (offSiteH (siteLabH hlab) (h1 j hj)), fun _ h => h⟩

/-- **A quiet single instruction of the callees inside `WSH`**: its `SFacts`
at the first instance (`hS`), its pc off the sites (`hokpc`), its
successors keeping `sp` and `x30` 4 bytes on (`hk`), its pc in the callees
off the take site and the next in the callees (`hpc`), its static `sp`
offset in `[klo, 0]` (`hso`), its abort phases' check (`hph`), its controls
`c0` (`hJ`). -/
theorem nodeI_WSH {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **`scc_rt_stack_next`'s add inside `WSH`** (as `nodeI_WSH`):
`ld<op> Xs, Xt, [Xn]` of a word unmapped in private memory (`ha`), off the
arena and not the counter word (`hoff`). -/
theorem nodeI_WSldopH {n : ND} {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfLdopH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **A TCB field's store inside `WSH`** (as `nodeI_WSH`): `str Xt, [Xn, #i]`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem nodeI_WSstH {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat ∧
        (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The lock's swap inside `WSH`** (as `nodeI_WSH`): `swp<k> Xs, Xt, [Xn]`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem nodeI_WSswpH {n : ND} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [swpDir kk rs rt b] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfSwpH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The free count's load inside `WSH`** (as `nodeI_WSH`):
`ldr Xt, [Xn, #i]` of a word unmapped in private memory (`ha`). -/
theorem nodeI_WSldrH {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfLdrH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The lock's release inside `WSH`** (as `nodeI_WSH`): `stlr Xt, [Xn]` of a
word unmapped in private memory (`ha`), off the arena and not the counter
word (`hoff`). -/
theorem nodeI_WSstlrH {n : ND} {t b : XReg} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [stlrDir t b] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo SccCode.helloProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcNH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.nodeW_wfStlrH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (nodeI_ownH (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkIH (siteTH hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1.1))
    (offSiteH (siteLabH hlab) (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The take site inside `WSH`**: the `nop` (`hb`), its states' `SFacts` at
the first instance (`hS`), off the abort sites (`habt`), its successors
keeping `sp` and `x30` 4 bytes on (`hk`), its pc and the next in the
callees (`hpc`), its static `sp` offset in `[klo, 0]` (`hso`), its abort
phases' check (`hph`), its controls `c0` (`hJ`); `X0` at the site's states
from their take range and frame (`hXs`), off it by `hX0`. -/
theorem siteI_WSH {n : ND} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [.instr ⟨.W64, .NOP⟩] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
    (habt : ∀ k x, (Spike.Lib.A64.PhRec.μ L).abortAt k = some x → n.pc.toBitVec.toNat ≠ x)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 → X0 s) :
    ∀ s c, At L.exe L.endPc R F n s c → WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.HelloWf.site_wfH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) (Dt := Dt) hI (hp ▸ hb) he (siteI_ownH hlab hbd hS hk hpc hso) habt
    (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact hpl0 _)
  intro s c hA
  have hpc' := hA.2.2.2.1
  have hx : X0 s := by
    by_cases hs : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
    · obtain ⟨-, -, -, -, σ, -, hF, -⟩ := id hA
      exact hXs s hs ((hS s c hA).site _ hsite hs).2.2.2.1 hF
    · exact hX0 _ (inIH_of hlab (by rw [hpc']; exact hpc.1)) hs
  exact ⟨.inl rfl, hx, hw s c hA⟩

end Gen

end Spike.Lib.A64.HelloPh.StartTi

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.tkIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.tkIH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.blkI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.blkI_WSH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSldopH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSldopH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSstH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSswpH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSswpH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSldrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSldrH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_WSstlrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_WSstlrH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.siteI_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.siteI_WSH
