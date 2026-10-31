/-
**wake.w's `scc_rt_start` inside `W0`: the node lemmas** (x86-64; first
half of the twin of `Spike/Lib/A64WakeStartWf.lean`; split off
`Spike/Lib/X64WakeStartWf.lean` for size). The start's level `WS` and its
generic node and block obligations: a covered `ret`-free block or a single
instruction of the start inside `W0` at the frames `[]` at `ownG`, from its
`SFacts` at `ownW`, its free pcs, its decided phase checks.

- `WS`: the start's level.
- `blkW_W0S`: a covered `ret`-free block.
- `free2`, `nodeW_W0S_of`, `nodeW_W0S_step`: a node's free pcs; a node from
  its pieces; a quiet node from its step.
- `nodeW_W0S`, `nodeW_W0S_fi`, `nodeW_W0S_and`, `nodeW_W0S_reg`,
  `nodeW_W0S_svc`: an `SI`, an `FI`, `andq $k, %rsp`, a register operation,
  a `syscall`.

See `Spike/Lib/X64WakeStartWf.lean` for the deviations from AArch64.
-/
import Spike.Lib.X64WakeStartEW
import Spike.Lib.X64WakeWfG
import Spike.Lib.X64WakeWfN
import Spike.Lib.X64WakeFree
import Spike.Lib.X64WakeTcb2WLib
import Spike.Lib.X64WakeOwnGNode
import Spike.Lib.Rt.X64CallSwitch2
import Spike.Lib.Rt.X64RtMainU


namespace Spike.Lib.X64.WakePh.StartWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (blockAtB okPcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk)
open Spike.Lib.X64Consumer (Lbl Lsize SFacts CFacts noRetBlk)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2 AbSt AcSt)
open Spike.Lib.X64 (ND BlkW NodeW At CodeAt cellOff arun okBlk SI FI Abs)
open Spike.Lib.X64.WakeWf (Wf W0 RunWf)
open Spike.Lib.X64.WakePh.WcW (freeN freeAt freeBlk freeAt_pc freeAt_lab freeBlk_pc goodW_of_freeN
  site_ne_of_freeN cv inCv lab_cv)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt op64)

/-- The spawn's label prefix (`wc_main`'s local labels). -/
abbrev pfxM : String := ".Lwc_main"

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

/-- The start's level: `W0` at the frames `[]` at `ownG`, the write and
threads aborts' phases. -/
abbrev WS (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isa := fun s c =>
  W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize frM X0 s c []

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **A covered `ret`-free block of the start inside `W0`** at the frames
`[]`: its `SFacts` at the first instance (`hS`), its pcs off the sites
(`hokpc`) and free (`hfree`), `ownG` picking `ownW` where its run ends
(`hfin`), its abort phases' check (`hph`), its controls `c0` (`hJ`). -/
theorem blkW_W0S {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true)
    (hfree : freeBlk l k blk = true)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun L.lab blk ⟨n.pc, n.o, σ⟩).so m (arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s)
    (hph : Spike.Lib.X64.WakeWf.phOffW pfxM l k l blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI (hp ▸ hb) hs hn
  have hin : ∀ j < blk.length, freeN (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true :=
    fun j hj => by rw [← he]; exact freeBlk_pc hlab hfree hj
  -- `ownG` picks `ownW` along the block and at its end.
  have hag := hagW (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) hlab hcode hok hR hlo' hhi
    (fun x hx j hj => by rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab (hin j hj))
    (fun σ c _ j hj s m _ _ _ hs => goodW_of_freeN hlab (by unfold pcOf; rw [hs]; exact hin j hj))
    (fun σ c hJ' j hj s m hA h1 h2 hs => by
      rcases Nat.lt_or_ge (j + 1) blk.length with hj1 | hj1
      · refine goodW_of_freeN hlab ?_
        unfold pcOf; rw [hs, Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hj1]; exact hin (j + 1) hj1
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ' s m hA h1 h2 hs)
  have hst := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hS) hag
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  have hw := Spike.Lib.X64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hok hR hlo' hhi hst'
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.X64.WakeWf.phOffW_sound hlab hph)
    (fun _ _ _ j hj r => (Spike.Lib.X64Consumer.noRet_false hnr j hj r).elim) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.X64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (by unfold pcOf; exact hin j hj), fun _ h => h⟩

omit hp hlo hsite hcl hc0 hpl0 hX0 in
/-- The node's pc and next pc free, from `freeAt l [k, k + z]`. -/
theorem free2 {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hfree : freeAt l [k, k + z] = true) :
    freeN n.pc.toBitVec.toNat = true ∧ freeN (n.pc + Int64.ofNat z).toBitVec.toNat = true := by
  refine ⟨?_, ?_⟩
  · have := freeAt_pc hlab hfree (o := k) (by simp); rwa [he] at this
  · have := freeAt_pc hlab hfree (o := k + z) (by simp)
    rwa [Spike.Lib.X64.Flow.ofNat_add', he] at this

omit hlab hsite in
/-- **A node of the start inside `W0` from its pieces**: its `SFacts` at
the first instance (`hS`), its pc and next pc free (`hf0`, `hfz`), its pc
off the sites (`hokpc`), its abort phases (`hab`, `hac`), its writes
(`hnw`), `ownG` agreeing with `ownW` at its states and successors
(`hagr`). -/
theorem nodeW_W0S_of {n : ND}
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ n.pc.toBitVec.toNat = true)
    (hf0 : freeN n.pc.toBitVec.toNat = true)
    (hagr : NodeW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = ownW L a (phW (pcOf s')))
      (fun _ _ => False) L.exe L.endPc R F n)
    (hab : NodeW (fun s _ => AbSt (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WriteAb.Ab L.lab) s)
      (fun _ _ => False) L.exe L.endPc R F n)
    (hac : NodeW (fun s _ => AcSt (Spike.Lib.X64.PhRec.μ L) Cl (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) s)
      (fun _ _ => False) L.exe L.endPc R F n)
    (hnw : NodeW (fun s _ => ∀ L', ¬ Spike.Lib.X64ConsumerA.WrAt s L') (fun _ _ => False) L.exe L.endPc R F n)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hst := Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 hS) hagr
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hw := Spike.Lib.X64.WakeWf.nodeW_wf (ar := ar) (p := p) (Ctx := Ctx) (lbl := lbl) (lsize := lsize)
    (fs := []) hst' hab hac hcl
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨⟨fun _ => hc0.1, hpl0 _, hc0.2⟩, fun _ h => h⟩)
    (Spike.Lib.X64.WakeWf.nodeW_noWrC hnw)
    (Spike.Lib.X64.WakeWf.nodeW_abortWf_off fun j x hx => Spike.Lib.X64.PhRec.ne_of_okPcOf
      (by rw [hp, hlo]; exact hokpc) (by cases j <;> simp [Scc.Cert.Rt.X64.siteLabels]) hx)
  refine Spike.Lib.X64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-- **A quiet node of the start inside `W0`** at the frames `[]`: its
`SFacts` at the first instance (`hS`), its pc off the sites (`hokpc`), its
pc and next pc free (`hfree`), its next pc off both abort phases' pcs
(`hph`), each of its states at a cell of size `z` off `syscall` whose
leaves are `z` bytes on (`hstep`), writing nothing (`hnw`), its controls
`c0` (`hJ`). -/
theorem nodeW_W0S_step {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hnw : NodeW (fun s _ => ∀ L', ¬ Spike.Lib.X64ConsumerA.WrAt s L') (fun _ _ => False) L.exe L.endPc R F n)
    (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  obtain ⟨hf0, hfz⟩ := free2 hlab he hfree
  have htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x := fun x hx => by
    rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0
  have hag := Spike.Lib.X64.WakePh.WcW.nodeAgreeW (a := a) (n := n) (exe := L.exe) (endPc := L.endPc) (R := R)
    (F := F) hlab hsite hf0 hfz hstep
  have hP := Spike.Lib.X64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.X64.PhRec.μ L)
    (exe := L.exe) (pfx := pfxM) he (Spike.Lib.X64.WakeWf.siOffW_sound hlab hph) htk hstep
  exact nodeW_W0S_of hp hlo hcl hc0 hpl0 hX0 hS hokpc hf0 hag (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩)
    (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩) hnw hJ

/-- **A single instruction without an event of the start inside `W0`** at
the frames `[]` (`nodeW_W0S_step` at an `SI`). -/
theorem nodeW_W0S {n : ND} {si : SI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  exact nodeW_W0S_step hp hlo hlab hsite hcl hc0 hpl0 hX0 he hS hokpc hfree hph
    (Spike.Lib.X64.WakeWf.si_step hI (hp ▸ hb) he)
    (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (hp ▸ hb) he rfl) hJ

/-- **An instruction with undefined flags of the start inside `W0`** at
the frames `[]` (`xorl %ebp, %ebp`; `nodeW_W0S_step` at an `FI`). -/
theorem nodeW_W0S_fi {n : ND} {fi : FI} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(fi.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  exact nodeW_W0S_step hp hlo hlab hsite hcl hc0 hpl0 hX0 he hS hokpc hfree hph
    (Spike.Lib.X64.WakeWf.fi_step hI (hp ▸ hb) he)
    (Spike.Lib.X64.AllocG.nodeW_noWr_fi hI (hp ▸ hb) he rfl) hJ

/-- **`andq $k, %rsp` of the start inside `W0`** at the frames `[]`
(`_start`'s alignment; `nodeW_W0S_step`, its tree silent). -/
theorem nodeW_W0S_and {n : ND} {i : Int64} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(Spike.Lib.X64.andRsp i, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcell : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (Spike.Lib.X64.andRsp i) z :=
    fun s c ⟨hs, hn, _, hpc, _⟩ => Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he hs hn hpc
  refine nodeW_W0S_step hp hlo hlab hsite hcl hc0 hpl0 hX0 he hS hokpc hfree hph (fun s c hA => ?_)
    (fun s c hA => ?_) hJ
  · obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_andRsp (hcell s c hA)
    refine ⟨_, t, hcell s c hA, (by intro w w' h; cases h), hex, fun s' hu => ?_⟩
    obtain ⟨_, rfl⟩ := Spike.Lib.X64.WakeWf.silentLeaf hst hu
    rfl
  · obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_andRsp (hcell s c hA)
    refine ⟨fun L' hL => ?_, fun _ h => h⟩
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hex] at h <;> cases h <;> exact hst.elim

/-- **A register operation of the start inside `W0`** (`RegOnly`, the
switch `movq %rax, %rsp`) at the frames `[]` (`nodeW_W0S_step`). -/
theorem nodeW_W0S_reg {n : ND} {w : Width} {op : Operation w} {l : Label} {k z : Nat}
    (hop : Spike.Lib.X64.RegOnly op = true)
    (hb : blockAtB wakeCells l k [(.instr (.regular .W64 w op), z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcell : ∀ s c, At L.exe L.endPc R F n s c → CellAt s (.instr (.regular .W64 w op)) z :=
    fun s c ⟨hs, hn, _, hpc, _⟩ => Spike.Lib.X64.Rt.cellOf hI (hp ▸ hb) he hs hn hpc
  refine nodeW_W0S_step hp hlo hlab hsite hcl hc0 hpl0 hX0 he hS hokpc hfree hph (fun s c hA => ?_)
    (fun s c hA => ⟨Spike.Lib.X64ConsumerA.noWr_done (Spike.Lib.X64.exec_reg hop (hcell s c hA)), fun _ h => h⟩) hJ
  refine ⟨_, _, hcell s c hA, fun w' w'' h => ?_, Spike.Lib.X64.exec_reg hop (hcell s c hA), fun s' hl => by
    cases hl; rfl⟩
  cases h; simp [Spike.Lib.X64.RegOnly] at hop

/-- **The start's `syscall`s inside `W0`** at the frames `[]`
(`rt_sigaction`, `arch_prctl`): its `SFacts` at the first instance (`hS`),
its pc off the sites (`hokpc`), its pc and the resumption's free (`hfree`),
the resumption off both abort phases' pcs (`hph`), its controls `c0`
(`hJ`). It writes nothing; every successor is `z` bytes on with `%rsp` kept
(`keep_syscall`), so out of both phases. -/
theorem nodeW_W0S_svc {n : ND} {l : Label} {k z : Nat}
    (hb : blockAtB wakeCells l k [(op64 .syscall, z)] = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeCells L.Λ (L.lab l + Int64.ofNat k).toBitVec.toNat = true)
    (hfree : freeAt l [k, k + z] = true)
    (hph : Spike.Lib.X64.WakeWf.siOffW pfxM l k z = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  obtain ⟨hf0, hfz⟩ := free2 hlab he hfree
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc [(op64 .syscall, z)] :=
    fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI (hp ▸ hb) hs hn
  have hph' := Spike.Lib.X64.WakeWf.siOffW_sound (lab := L.lab) hlab hph
  simp only [Spike.Lib.X64.WakeWf.siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hph'
  have htk : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x := fun x hx => by
    rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0
  -- Every successor is `z` bytes on.
  have hsucc : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = true ∧
      ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → s'.st.2 = n.pc + Int64.ofNat z := by
    rintro s c ⟨hs, hn, -, hpc, -⟩
    have hc : CellAt s (op64 .syscall) z := (hcode s hs hn).cell0 rfl rfl hpc
    have hsy : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt hc
    exact ⟨hsy, fun s' h => by rw [keep_pc hc (keep_syscall hsy h), hpc]⟩
  have hag : NodeW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → ownG L a s' = ownW L a (phW (pcOf s')))
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hA
    obtain ⟨hsy, hs'⟩ := hsucc s c hA
    have hpc : s.st.2 = n.pc := hA.2.2.2.1
    refine ⟨⟨ownG_W hlab (goodW_of_freeN hlab (by unfold pcOf; rw [hpc]; exact hf0)), fun s' h => ?_⟩,
      fun _ h => h⟩
    exact ownG_W hlab (goodW_of_freeN hlab (by unfold pcOf; rw [hs' s' h]; exact hfz))
  have hab : NodeW (fun s _ => AbSt (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WriteAb.Ab L.lab) s)
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hA
    obtain ⟨hsy, hs'⟩ := hsucc s c hA
    have hpc : s.st.2 = n.pc := hA.2.2.2.1
    refine ⟨⟨fun _ h => ?_, fun _ _ call hd s' hm hab => ?_, fun _ x hx hpc' => ?_⟩, fun _ h => h⟩
    · rw [hsy] at h; cases h
    · refine (Spike.Lib.X64.WriteAb.not_ab_of_pc ?_ hab).elim
      rw [hs' s' (.inr (.inl ⟨hsy, call, hd, hm⟩))]; exact hph'.1
    · exact (htk x hx (by unfold pcOf at hpc'; rw [hpc] at hpc'; exact hpc')).elim
  have hac : NodeW (fun s _ => AcSt (Spike.Lib.X64.PhRec.μ L) Cl (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) s)
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hA
    obtain ⟨hsy, hs'⟩ := hsucc s c hA
    have hpc : s.st.2 = n.pc := hA.2.2.2.1
    refine ⟨⟨fun _ h => ?_, fun _ _ _ call hd s' hm => ?_, fun _ x hx hpc' => ?_⟩, fun _ h => h⟩
    · rw [hsy] at h; cases h
    · refine Spike.Lib.X64.ThreadsAb.not_ac_of_pc ?_
      rw [hs' s' (.inr (.inl ⟨hsy, call, hd, hm⟩))]; exact hph'.2
    · exact (htk x hx (by unfold pcOf at hpc'; rw [hpc] at hpc'; exact hpc')).elim
  exact nodeW_W0S_of hp hlo hcl hc0 hpl0 hX0 hS hokpc hf0 hag hab hac
    (Spike.Lib.X64.WakeWf.nodeW_noWr_svc hcode) hJ

end Gen

end Spike.Lib.X64.WakePh.StartWf

/-- info: 'Spike.Lib.X64.WakePh.StartWf.blkW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.blkW_W0S

/-- info: 'Spike.Lib.X64.WakePh.StartWf.free2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.free2

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_of

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_step

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_fi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_fi

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_and

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_reg

/-- info: 'Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartWf.nodeW_W0S_svc
