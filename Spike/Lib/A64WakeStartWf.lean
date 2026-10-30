/-
**wake.w's `scc_rt_start` inside `W0`** (AArch64): the
runtime's own nodes of the start, from `_start` to `bl scc_rt_main`,
inside the level before the allocation `WakeWf.W0` at the frames `[]`
(the start: a pending tail call to `main`), at wake.w's global owned-words
map `ownG`. Each node's state facts are `A64WakeStart.startEW_wake`'s at the
first instance (`ownW` at `phW`) moved to `ownG` (which picks `ownW` at
every free pc, `WcW.freeN`, and inside `scc_rt_alloc_tcb` and
`scc_rt_thread_init` off a pool stack), the two abort phases from the decided checks (`phOffW`, `siOffW`), the rest from `WakeWf.blkW_wfQ` /
`nodeW_wfQ`.

- `blkW_W0S`, `nodeW_W0S`: a covered `ret`-free block / a single
  instruction of the start inside `W0`, from its `SFacts` at `ownW`, its
  free pcs and the agreement at its end.
-/
import Spike.Lib.A64WakeWcPreWN
import Spike.Lib.A64WakeWfG

namespace Spike.Lib.A64.WakePh.StartWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (Wf W0 RunWf)
open Spike.Lib.A64.WakePh.WcW (freeN freeAt freeAt_pc freeAt_pc0 freeAt_lab goodW_of_freeN site_ne_of_freeN cv inCv
  lab_cv)
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
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

/-- The start's level: `W0` at the frames `[]` at `ownG`, the write and
threads aborts' phases. -/
abbrev WS (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isaLSE2) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isaLSE2 := fun s c =>
  W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize frM X0 s c []

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **A covered `ret`-free block of the start inside `W0`** at the frames
`[]`: its `SFacts` at the first instance (`hS`), its pcs off the sites
(`hokpc`) and free (`hfree`), `ownG` picking `ownW` where its run ends
(`hfin`), its abort phases' check (`hph`), its controls `c0` (`hJ`). -/
theorem blkW_W0S {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length,
      okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hfree : freeAt l k blk.length = true)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s)
    (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k l blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    BlkW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hin : ∀ j < blk.length, freeN (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true :=
    fun j hj => by rw [← he]; exact freeAt_pc hlab hfree hj
  -- `ownG` picks `ownW` along the block and at its end.
  have hag := hagW (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo' hhi
    (fun x hx j hj => by rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab (hin j hj))
    (fun σ c _ j hj s m _ _ _ hs => goodW_of_freeN hlab (by unfold pcOf; rw [hs]; exact hin j hj))
    (fun σ c hJ' j hj s m hA h1 h2 hs => by
      rcases Nat.lt_or_ge (j + 1) blk.length with hj1 | hj1
      · refine goodW_of_freeN hlab ?_
        unfold pcOf; rw [hs, Spike.Lib.A64.Flow.arun_pc _ hok hj1]; exact hin (j + 1) hj1
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ' s m hA h1 h2 hs)
  have hst := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hS) hag
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  have hw := Spike.Lib.A64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst'
    (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.WakeWf.phOffW_sound hlab hph)
    (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hnr j hj r hr).elim) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s σ c _ _ _ _ _ _ hJ' _ _ _ _ _ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_ hw
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  exact ⟨hX0 _ (by unfold pcOf; exact hin j hj), fun _ h => h⟩

/-- **A single instruction without an event of the start inside `W0`** at
the frames `[]`: its `SFacts` at the first instance (`hS`), its pc off the
sites (`hokpc`), its pc and next pc free (`hfree`), its abort phases'
check (`hph`), its controls `c0` (`hJ`). -/
theorem nodeW_W0S {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hfree : freeAt l k 2 = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeN n.pc.toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 0) (by decide); rwa [Spike.Lib.A64.Flow.ofNat4_zero, he] at this
  have hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 1) (by decide); rw [he] at this; exact this
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hstep := Spike.Lib.A64.WakeWf.si_step (R := R) (F := F) hI (hp ▸ hb) he
  have hag := Spike.Lib.A64.WakePh.WcW.nodeAgreeW (a := a) (n := n) (exe := L.exe) (endPc := L.endPc) (R := R)
    (F := F) hlab hsite hf0 hf4 hstep
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS) hag
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he hst'
    (fun x hx => by rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨hpl0 _, fun _ h => h⟩)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-- **The start's `svc #0` inside `W0`** at the frames `[]`: its `SFacts` at
the first instance (`hS`), its pc off the sites (`hokpc`), its pc and the
resumption's free (`hfree`), the resumption off both abort phases'
pcs (`hph`), its controls `c0` (`hJ`). It writes nothing. -/
theorem nodeW_W0S_svc {n : ND} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.svcDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hfree : freeAt l k 2 = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeN n.pc.toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 0) (by decide); rwa [Spike.Lib.A64.Flow.ofNat4_zero, he] at this
  have hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 1) (by decide); rw [he] at this; exact this
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hph' := Spike.Lib.A64.WakeWf.siOffW_sound hlab hph
  simp only [Spike.Lib.A64.WakeWf.siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hph'
  have htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x := fun x hx => by
    rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0
  have hag : NodeW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → ownG L a s' = ownW L a (phW (pcOf s')))
      (fun _ _ => False) L.exe L.endPc R F n := by
    rintro s c ⟨hs, hn, -, hpc, -⟩
    have hc : Kraken.Promising.Lower.A64.CellAt s Spike.Lib.A64.Flow.svcDir 4 :=
      (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    have hsy : abi.atSys s = true := Scc.Sem.A64.atSvc_of_cellAt hc
    refine ⟨agree_nodeW hlab (fun s' h => keep_svc hsy h)
      (goodW_of_freeN hlab (by unfold pcOf; rw [hpc]; exact hf0)) (fun s' hk => goodW_of_freeN hlab ?_),
      fun _ h => h⟩
    unfold pcOf; rw [keep_pc hc hk, hpc]; exact hf4
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS) hag
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hw := Spike.Lib.A64.WakeWf.nodeW_wf (ar := ar) (p := p) (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (fs := [])
    hst' (Spike.Lib.A64.WakeWf.nodeW_abSt_svc hcode htk fun s c hA r =>
      Spike.Lib.A64.WriteAb.not_ab_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hA.2.2.2.1]; exact hph'.1))
    (Spike.Lib.A64.WakeWf.nodeW_acSt_svc hcode htk fun s c hA => .inr fun r =>
      Spike.Lib.A64.ThreadsAb.not_ac_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hA.2.2.2.1]; exact hph'.2))
    hcl (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨⟨fun _ => hc0.1, hpl0 _, hc0.2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_noWrC (Spike.Lib.A64.WakeWf.nodeW_noWr_svc hcode))
    (Spike.Lib.A64.WakeWf.nodeW_abortWf_off fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf
      (by rw [hp, hlo]; exact hokpc) (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-- **A register operation of the start inside `W0`** (`RegOnly`, the
switch `add sp, x9, #0`) at the frames `[]`, as `nodeW_W0S`. -/
theorem nodeW_W0S_reg {n : ND} {w : RegWidth} {op : Operation w} {l : Label} {k : Nat}
    (hop : Spike.Lib.A64.Flow.RegOnly op = true)
    (hb : blockAt wakeProg l k [.instr ⟨w, op⟩] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hfree : freeAt l k 2 = true)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hf0 : freeN n.pc.toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 0) (by decide); rwa [Spike.Lib.A64.Flow.ofNat4_zero, he] at this
  have hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true := by
    have := freeAt_pc hlab hfree (j := 1) (by decide); rw [he] at this; exact this
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hcell : ∀ s c, At L.exe L.endPc R F n s c → Kraken.Promising.Lower.A64.CellAt s (.instr ⟨w, op⟩) 4 :=
    fun s c ⟨hs, hn, _, hpc, _⟩ => (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := fun s c hA =>
    ⟨_, _, hcell s c hA, fun imm h => by cases h; simp [Spike.Lib.A64.Flow.RegOnly] at hop,
      Spike.Lib.A64.Flow.exec_reg hop (hcell s c hA), fun s' hl => by cases hl; rfl⟩
  have htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x := fun x hx => by
    rw [hsite] at hx; cases hx; exact site_ne_of_freeN hlab hf0
  have hag := Spike.Lib.A64.WakePh.WcW.nodeAgreeW (a := a) (n := n) (exe := L.exe) (endPc := L.endPc) (R := R)
    (F := F) hlab hsite hf0 hf4 hstep
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS) hag
  have hst' : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n :=
    fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩
  have hP := Spike.Lib.A64.WakeWf.nodeW_phSt (Cl := Cl) (R := R) (F := F) (μ := Spike.Lib.A64.PhRec.μ L) he
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) htk hstep
  have hw := Spike.Lib.A64.WakeWf.nodeW_wf (ar := ar) (p := p) (Ctx := Ctx) (lbl := lbl) (lsize := lsize) (fs := [])
    hst' (fun s c hA => ⟨(hP s c hA).1.1, fun _ h => h⟩) (fun s c hA => ⟨(hP s c hA).1.2, fun _ h => h⟩)
    hcl (fun s c ⟨_, _, _, _, σ, _, _, hJ'⟩ => by rw [hJ σ c hJ']; exact ⟨⟨fun _ => hc0.1, hpl0 _, hc0.2⟩, fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA =>
      ⟨Spike.Lib.A64ConsumerA.noWr_done (Spike.Lib.A64.Flow.exec_reg hop (hcell s c hA)), fun _ h => h⟩)
    (Spike.Lib.A64.WakeWf.nodeW_abortWf_off fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf
      (by rw [hp, hlo]; exact hokpc) (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## The start -/

/-- `freeAt` of wakeProg, decided. -/
macro "wsfree_dec" : tactic =>
  `(tactic| (unfold freeAt freeN inCv cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel))

omit hp hlo hsite hcl hc0 hpl0 hX0 in
/-- A label of wakeProg read through `L.lab`, decided. -/
private theorem labCv (l : Label) (hs : (codeOf lo wakeProg l).isSome = true) (hb : cv l < 2 ^ 64) :
    (L.lab l).toBitVec.toNat = cv l :=
  lab_cv hlab hs hb

omit hp hlo hlab hsite hcl hc0 hpl0 hX0 in
/-- **At a callee's entry from the start on a stack off the pool**, `ownG`
picks `ownW`: the pc inside `scc_rt_alloc_tcb` or `scc_rt_thread_init`
(`hin`), `sp` at offset `-48` of a region whose address there is off the
pool (`hoffP`). -/
private theorem goodW_fn {s : State} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R ⟨-48, []⟩ m σ) (hm : s.st.1 = m)
    (hoffP : ¬ (L.Λ.stackPool.lo < (R.addr (-48)).toNat ∧
      (R.addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hin : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s ∨
      inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) : GoodW L s := by
  have hsp : m.regs.SP.toBitVec = R.addr (-48) := by rw [hA.regs]; exact hA.so .SP _ rfl
  refine .inl ⟨hin, ?_⟩
  unfold spPool; rw [hm, hsp]; exact hoffP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3200000 in
/-- **wake.w's `scc_rt_start` inside `W0`** (`StartEW`, from `_start` to
`bl scc_rt_main`) at the frames `[]` at `ownG`: every own node of the start
from `startEW_wake`'s `SFacts` at `ownW` (`blkW_W0S`, `nodeW_W0S`,
`nodeW_W0S_svc`, `nodeW_W0S_reg`), its pcs free and its phases decided. The
two callees' states are premises (`htcb`, `hti`, the thread init's take site
at the extra frame `P`); the two call blocks end at
the callees' entries on a stack whose `-48` word is off the pool
(`hoffP`). -/
theorem startEW_W0S (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {n0 k0 : BitVec 64} {D : Int}
    (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(Spike.Lib.A64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hSM : Spike.Lib.A64.Flow.FStable R (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMi : Spike.Lib.A64.Flow.FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0)
      (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMt : Spike.Lib.A64.Flow.FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (h16 : (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (Spike.Lib.A64.Flow.swR (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hL8 : D % 8 = 0)
    (hoffP : ¬ (L.Λ.stackPool.lo < (R.addr (-48)).toNat ∧
      (R.addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (htcb : ∀ g, g.ra = (L.lab ".L0_scc_rt_start.sp2").toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TcbW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F ⟨g, n0, c0⟩ i)
    {P : MachineData → Prop}
    (hti : ∀ g, g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TiW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) F (Spike.Lib.A64.Flow.Ret0.StackM rS)
        ⟨g, Spike.Lib.A64.Flow.Ret0.pinA L.lab + n0 + 8#64, k0, c0⟩ i P) :
    Spike.Lib.A64.Rt.StartEW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
      L.endPc R F rS n0 k0 c0 D P := by
  have hW := startEW_wake (a := a) (rS := rS) (lbl := lbl') hp hlo hΛ hlab hs hro hC0 hR hal hRlo hhi hFr hn0
    hrS hsub hSM hSMi hSMt hfit h16 hok hL8
  have hf : ∀ f ∈ Spike.Lib.A64.Rt.startPhTab, _ := fun f hf =>
    startW_fact hΛ (f := f) (by simp [startTabW, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo wakeProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = L.lab r := fun _ h => nomatch h
  have okB : ∀ {okP : Nat → Bool} {phf : Nat → Nat} {d : Nat → Bool} {pc ra : Int64} {blk : List Directive},
      Spike.Lib.A64Consumer.blkPh okP phf d L.lab pc ra blk = true →
      ∀ j < blk.length, okP (pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun h j hj => by
    have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have e4 : ∀ x : Int64, x + 4 + 4 + 4 + 4 = x + Int64.ofNat (4 * 4) := fun x => by
    simp only [Int64.add_assoc]; rfl
  have hrc := wake_rtCodeIn0
  have hst := hrc.start
  simp only [Spike.Lib.A64.Flow.startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨⟨-, cb0⟩, cb1⟩, cb2⟩, cb3⟩, cb4⟩ := hst
  have hcl' := hrc.call
  simp only [Spike.Lib.A64.Flow.Ret0.startCallIn, Bool.and_eq_true] at hcl'
  obtain ⟨cc, -⟩ := hcl'
  have htl := hrc.tail
  simp only [Spike.Lib.A64.Flow.Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨t0, -⟩, t2⟩, t3⟩, tsw⟩, tmain⟩ := htl
  refine ⟨?_, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, htcb⟩, ⟨?_, hti, ?_, ?_⟩, ⟨?_, fun v => ?_⟩⟩
  · -- `_start`'s branch.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := "_start") (k := 0) hrc.entry
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.Ret0.entryB_ok hR hal (by omega) (by omega) hW.e
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (startW_fact hΛ (f := .blk "_start" 0 Spike.Lib.A64.Rt.Code.Start.entryB none none)
          (by simp [startTabW, Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) (by decide) (fun _ _ h => h)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.Ret0.entryN] at hs'
    rw [Spike.Lib.A64.Flow.Ret0.entryB_run] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_lab hlab (by wsfree_dec))
  · -- The frame's setup.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := "scc_rt_start") (k := 0) cb0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Abort.b0_ok hR hal (by omega) (by omega) hW.s1.start.w0
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk "scc_rt_start" 0 Spike.Lib.A64.Abort.b0 none none) (by simp [Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) Spike.Lib.A64.Rt.StartU.b0_noRet (fun _ _ h => h)
    intro σ c _ s m _ _ _ hs'
    dsimp only at hs'
    rw [Spike.Lib.A64.Abort.b0_run, e4] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_pc0 hlab (by wsfree_dec))
  · -- The `adrp`.
    exact nodeW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (si := .adrp .X9 Spike.Lib.A64.Flow.sigign)
      (l := Spike.Lib.A64.Flow.startE) (k := 0) cb1 (Spike.Lib.A64.Flow.ofNat4_zero _) hW.s1.start.w1
      (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.A64.Flow.startE 0) (by simp [Spike.Lib.A64.Rt.startPhTab]))).1
      (by wsfree_dec) (by decide +kernel) (fun _ _ ⟨_, h, _⟩ => h)
  · -- The `add`.
    exact nodeW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (si := .addLo12 .X9 .X9 Spike.Lib.A64.Flow.sigign)
      (l := Spike.Lib.A64.Flow.startE) (k := 1) cb2 rfl hW.s1.start.w2
      (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.A64.Flow.startE 1) (by simp [Spike.Lib.A64.Rt.startPhTab]))).1
      (by wsfree_dec) (by decide +kernel) (fun _ _ ⟨_, h, _⟩ => h)
  · -- The arguments.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.startE) (k := 2) cb3
      (Spike.Lib.A64.Rt.StartU.startE2 _).symm Spike.Lib.A64.Flow.startArgs_ok hR hal (by omega) (by omega)
      hW.s1.start.w3
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.A64.Flow.startE 2 Spike.Lib.A64.Flow.startArgs none none)
          (by simp [Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) Spike.Lib.A64.Rt.StartU.startArgs_noRet (fun _ _ ⟨_, h, _⟩ => h)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.startN3] at hs'
    rw [Spike.Lib.A64.Flow.startArgs_run, Spike.Lib.A64.Rt.StartU.startE8] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_pc0 hlab (by wsfree_dec))
  · -- The system call.
    exact nodeW_W0S_svc hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.startE) (k := 8) cb4
      (Spike.Lib.A64.Rt.StartU.startE8 _).symm hW.s1.start.w4
      (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.A64.Flow.startE 8) (by simp [Spike.Lib.A64.Rt.startPhTab]))).1
      (by wsfree_dec) (by decide +kernel) (fun _ _ ⟨_, h, _⟩ => h)
  · -- The call block of `scc_rt_alloc_tcb`.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.startE) (k := 9) cc rfl
      Spike.Lib.A64.Flow.Ret0.startCall_ok hR hal (by omega) (by omega) hW.s1.blk
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.A64.Flow.startE 9 Spike.Lib.A64.Rt.Code.Start.startCall none none)
          (by simp [Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) Spike.Lib.A64.Rt.StartU.startCall_noRet (fun _ _ h => h)
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.Ret0.startN1] at hA hs'
    rw [Spike.Lib.A64.Flow.Ret0.startCall_run] at hA hs'
    refine goodW_fn hA (by rw [hs']) hoffP (.inl ?_)
    unfold inPc pcOf; rw [hs']
    refine ⟨Nat.le_refl _, ?_⟩
    show (L.lab "scc_rt_alloc_tcb").toBitVec.toNat < (L.lab "scc_rt_thread_reserve").toBitVec.toNat
    rw [labCv hlab "scc_rt_alloc_tcb" (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)
        (by unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel),
      labCv hlab "scc_rt_thread_reserve" (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)
        (by unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)]
    unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  · -- `.sp2`'s block, the call of `scc_rt_thread_init`.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.Ret0.sp2L) (k := 0) t0
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.Ret0.startCall2_ok hR hal (by omega) (by omega)
      hW.s2.b2
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.A64.Rt.Code.Start.sp2L 0 Spike.Lib.A64.Rt.Code.Start.startCall2 none none)
          (by simp [Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) Spike.Lib.A64.Rt.StartU.startCall2_noRet (fun _ _ h => h.1)
    intro σ c _ s m hA _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.Ret0.startN2] at hA hs'
    rw [Spike.Lib.A64.Flow.Ret0.startCall2_run] at hA hs'
    refine goodW_fn hA (by rw [hs']) hoffP (.inr ?_)
    unfold inPc pcOf; rw [hs']
    refine ⟨Nat.le_refl _, ?_⟩
    show (L.lab "scc_rt_thread_init").toBitVec.toNat < (L.lab "scc_rt_stack_release").toBitVec.toNat
    rw [labCv hlab "scc_rt_thread_init" (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)
        (by unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel),
      labCv hlab "scc_rt_stack_release" (by rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)
        (by unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel)]
    unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  · -- `.sp3`'s block.
    refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.Ret0.sp3L) (k := 0) t2
      (Spike.Lib.A64.Flow.ofNat4_zero _) Spike.Lib.A64.Flow.Ret0.startSw0_ok hR hal (by omega) (by omega)
      hW.s2.b3
      (okB (Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn
        (hf (.blk Spike.Lib.A64.Rt.Code.Start.sp3L 0 Spike.Lib.A64.Rt.Code.Start.startSw0 none none)
          (by simp [Spike.Lib.A64.Rt.startPhTab]))))
      (by wsfree_dec) ?_ (by decide +kernel) Spike.Lib.A64.Rt.StartU.startSw0_noRet (fun _ _ h => h.1)
    intro σ c _ s m _ _ _ hs'
    dsimp only [Spike.Lib.A64.Flow.Ret0.startN3] at hs'
    rw [Spike.Lib.A64.Flow.Ret0.startSw0_run, e4] at hs'
    exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_pc0 hlab (by wsfree_dec))
  · -- The `msr`.
    exact nodeW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (si := .msr .X10)
      (l := Spike.Lib.A64.Flow.Ret0.sp3L) (k := 4) t3 rfl hW.s2.msr
      (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab
        (hf (.step Spike.Lib.A64.Rt.Code.Start.sp3L 4) (by simp [Spike.Lib.A64.Rt.startPhTab]))).1
      (by wsfree_dec) (by decide +kernel) (fun _ _ h => h.1)
  · -- The switch.
    exact nodeW_W0S_reg hp hlo hlab hsite hcl hc0 hpl0 hX0 (by simp [Spike.Lib.A64.Flow.RegOnly])
      (l := Spike.Lib.A64.Flow.Ret0.sp3L) (k := 5) tsw rfl hW.s3.sw (swPhW hΛ hlab).sw.1
      (by wsfree_dec) (by decide +kernel) (fun _ _ h => h.1)
  · -- After the switch: `movz x29, #0; bl scc_rt_main` in the new region.
    by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA L.lab + k0 + 16384#64
    · subst hv
      refine blkW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 (l := Spike.Lib.A64.Flow.Ret0.sp3L) (k := 6) tmain rfl
        (Spike.Lib.A64.Rt.startMain_okL (-D) 0) hok h16 (Int.le_refl _) (Int.le_refl _) (hW.s3.blk _)
        (okB (swPhW hΛ hlab).main) (by wsfree_dec) ?_ (by decide +kernel)
        Spike.Lib.A64.Rt.MainU.startMain_noRet (fun _ _ h => h.1)
      intro σ c _ s m _ _ _ hs'
      dsimp only [Spike.Lib.A64.Flow.Ret0.startN6] at hs'
      rw [Spike.Lib.A64.Flow.Ret0.startMain_run] at hs'
      exact goodW_of_freeN hlab (by unfold pcOf; rw [hs']; exact freeAt_lab hlab (by wsfree_dec))
    · exact Spike.Lib.A64.Rt.blkW_ofFalse fun _ h => hv h.1.1

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartWf.blkW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_W0S

/-- info: 'Spike.Lib.A64.WakePh.StartWf.nodeW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_W0S

/-- info: 'Spike.Lib.A64.WakePh.StartWf.nodeW_W0S_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_W0S_svc

/-- info: 'Spike.Lib.A64.WakePh.StartWf.nodeW_W0S_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_W0S_reg

/-- info: 'Spike.Lib.A64.WakePh.StartWf.startEW_W0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_W0S

end Spike.Lib.A64.WakePh.StartWf
