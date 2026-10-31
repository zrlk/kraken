/-
**wake.w's global owned-words map on the threads abort path** (x86-64; the
twin of `Spike/Lib/A64WakeOwnGAb.lean`): `scc_rt_abort(5)` and
`scc_rt_abort_threads` run with the pc in `[scc_rt_abort, scc_rt_thr_worker)`,
the caller's return address `ra` in the region's word at offset `8`
throughout (`Abort.Disp.DN.nd5`, `Abort.NT`: `slot 8 = ra`) and `%rsp` in the
band `[-32, 8]` of the region (`AbP`); there `ownG` picks the instance by
`ra` and the band (`good2a_ab`, `good2b_ab`, `goodW_ab`).

- `RaOK L R p o`: at pc `p` with static offsets `o`, the return address
  word `raAddr` is the region's offset `8` (`%rsp` at `8` at the `raSp` pcs,
  at `0` at the `raSp8` pcs, `%rbp` at `0` elsewhere).
- `raAddr_of`: `raAddr` is `R.addr 8` from `RaOK` and the registers.
- `privLoad_slot`: **the return address word is the thread's own stack
  slot** — the private word `raAt` reads at `R.addr 8` is the abstract
  state's `slot 8` of the region (`Abs.slot`), the caller's frame word
  its `call` pushed; no other memory is read (`raAt_congr`).
- `AbP`: the pc on the path, `raAddr` at `R.addr 8`, the word there `ra`,
  `%rsp` in the band; `raAt_iff`: there `raAt L l` is `lab l = ra`.
- `good2a_ab`, `good2b_ab`, `goodW_ab`: where `ownG` picks each instance on
  the path.
- `abP_of`: `AbP` at a state represented at a pc of the path.
- `abP_blk`: `AbP` at a block's states and their successors, from the
  block's abstract run (pcs, `RaOK`, static `%rsp` offsets, `slot 8`).
- `keepM_syscall`: a `syscall` state's successors off the take site keep
  `%rsp`, `%rbp` and the private memory.
- `abP_node`: `AbP` at a node whose successors keep `%rsp`, `%rbp` and the
  private memory and move the pc by the cell's size.

**Unlike AArch64**: the return address is a private-memory word, not
`x30`, so `AbP` pins where `raAddr` points (`R.addr 8`, in the region) and
its value there; a node's successors must also keep the private memory
(`keepM_syscall`: the take is off the path, `hns`). The band is
`[-32, 8]` (the stubs' frames below the pushed `%rbp`, the return address
at `8`), A64's `[-48, 0]`.
-/
import Spike.Lib.X64WakeOwnGNode
import Spike.Lib.X64SpAgree

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf nextPc abi privLoad)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SpAt)
open Spike.Lib.X64 (ND BlkW NodeW At SO Abs arun cellOff okBlk CodeAt)

variable {L : RuntimeLayout} {s : State}

/-- **The return address word is at offset `8`** at pc `p` with static
offsets `o`. -/
def RaOK (L : RuntimeLayout) (p : Int64) (o : SO) : Prop :=
  (p.toBitVec.toNat ∈ raSp L → o.sp = 8) ∧
    (p.toBitVec.toNat ∉ raSp L → p.toBitVec.toNat ∈ raSp8 L → o.sp = 0) ∧
    (p.toBitVec.toNat ∉ raSp L → p.toBitVec.toNat ∉ raSp8 L → o.get .rbp = some 0)

/-- **`raAddr` is the region's offset `8`** from `RaOK` at the state's pc
and its `%rsp`, `%rbp` at their static offsets. -/
theorem raAddr_of {R : Region} {o : SO} (hra : RaOK L s.st.2 o)
    (hsp : s.st.1.regs.rsp.toBitVec = R.addr o.sp)
    (hbp : ∀ k, o.get .rbp = some k → s.st.1.regs.rbp.toBitVec = R.addr k) :
    raAddr L s = R.addr 8 := by
  obtain ⟨h1, h2, h3⟩ := hra
  have hpc : pcOf s = s.st.2.toBitVec.toNat := rfl
  unfold raAddr
  rw [hpc]
  by_cases hs : s.st.2.toBitVec.toNat ∈ raSp L
  · simp only [hs, ↓reduceIte, hsp, h1 hs]
  · by_cases hs8 : s.st.2.toBitVec.toNat ∈ raSp8 L
    · simp only [hs, hs8, ↓reduceIte, hsp, h2 hs hs8, Region.addr_add8]; rfl
    · simp only [hs, hs8, ↓reduceIte, hbp 0 (h3 hs hs8), Region.addr_add8]; rfl

/-- **The return address word is the region's slot `8`**: at a state the
abstract state `σ` represents (`Abs`), the private word at `R.addr 8` is
`σ.slot 8`, when offset `8` is a cell of the region. -/
theorem privLoad_slot {R : Region} {o : SO} {σ : Spike.Lib.X64.AS} (hA : Abs R o s.st.1 σ) (hoff : R.Off 8) :
    privLoad s (R.addr 8) = some (σ.slot 8) := by
  obtain ⟨j, h1, h2⟩ := hA.slot 8 hoff
  unfold privLoad; rw [h1, ← h2]; rfl

/-- **On the abort path with return address `ra`**: the pc in
`[scc_rt_abort, scc_rt_thr_worker)`, the return address word at `R.addr 8`
holding `ra`, `%rsp` at `R.addr k` for a `k` in `[-32, 8]`. -/
def AbP (L : RuntimeLayout) (R : Region) (ra : BitVec 64) (s : State) : Prop :=
  inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ raAddr L s = R.addr 8 ∧ privLoad s (R.addr 8) = some ra ∧
    SpAt R (-32) 8 s

/-- **On the path `raAt` is the return address**: it reads the word at
`R.addr 8` only. -/
theorem raAt_iff {R : Region} {ra : BitVec 64} (h : AbP L R ra s) (l : Label) :
    raAt L l s ↔ (L.lab l).toBitVec = ra := by
  unfold raAt; rw [h.2.1, h.2.2.1, Option.some.injEq, eq_comm]

/-- **The band on a pool stack**: every address of `[-32, 8]` of `R` in
`(pool.lo, pool.lo + pool.size]`. -/
def BandIn (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -32 ≤ k → k ≤ 8 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- **The band off the pool stacks.** -/
def BandOut (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -32 ≤ k → k ≤ 8 → ¬ (L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)

theorem spPool_of_band {R : Region} (hb : BandIn L R) (h : SpAt R (-32) 8 s) : spPool L s := by
  obtain ⟨k, h1, h2, hk⟩ := h
  unfold spPool; rw [hk]; exact hb k h1 h2

theorem not_spPool_of_band {R : Region} (hb : BandOut L R) (h : SpAt R (-32) 8 s) : ¬ spPool L s := by
  obtain ⟨k, h1, h2, hk⟩ := h
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- The two return addresses on the path differ. -/
theorem ra_ne (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab ".Lscc_rt_alloc_tcb.x5").toBitVec ≠ (L.lab ".Lwc_main.x23").toBitVec := by
  rw [hlab _ 4199245 (by rw [← codeT_eq]; decide +kernel), hlab _ 4203484 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **`ownG` picks `own2a` on the path** from `scc_rt_alloc_tcb`'s abort on a
pool stack. -/
theorem good2a_ab {R : Region} (h : AbP L R (L.lab ".Lscc_rt_alloc_tcb.x5").toBitVec s) (hb : BandIn L R) :
    Good2a L s :=
  .inr (.inr ⟨h.1, (raAt_iff h _).2 rfl, spPool_of_band hb h.2.2.2⟩)

/-- **`ownG` picks `own2b` on the path** from `wc_main`'s spawn failure. -/
theorem good2b_ab (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (h : AbP L R (L.lab ".Lwc_main.x23").toBitVec s) : Good2b L s :=
  .inr (.inr ⟨h.1, (raAt_iff h _).2 rfl, fun ⟨hx, _⟩ => ra_ne hlab ((raAt_iff h _).1 hx)⟩)

/-- **`ownG` picks `ownW` on the path** from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem goodW_ab {R : Region} {ra : BitVec 64} (h : AbP L R ra s)
    (h5 : ra = (L.lab ".Lscc_rt_alloc_tcb.x5").toBitVec → BandOut L R)
    (h23 : ra ≠ (L.lab ".Lwc_main.x23").toBitVec) : GoodW L s := by
  refine .inr (.inl ⟨h.1, fun ⟨hx, hp⟩ => ?_, fun hx => h23 ((raAt_iff h _).1 hx).symm⟩)
  exact not_spPool_of_band (h5 ((raAt_iff h _).1 hx).symm) h.2.2.2 hp

/-- **`AbP` at a state represented at a pc `p` of the path** with offsets
`o` (`RaOK`, `%rsp` in the band) and `slot 8 = ra`. -/
theorem abP_of {R : Region} {ra : BitVec 64} {o : SO} {m : MachineData} {σ : Spike.Lib.X64.AS} {p : Int64}
    (hst : s.st = (m, p)) (hA : Abs R o m σ) (hoff : R.Off 8)
    (hpc : (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
      p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hra : RaOK L p o) (hso : -32 ≤ o.sp ∧ o.sp ≤ 8) (hx : σ.slot 8 = ra) : AbP L R ra s := by
  have h1 : s.st.1 = m := by rw [hst]
  have h2 : s.st.2 = p := by rw [hst]
  have hA' : Abs R o s.st.1 σ := h1 ▸ hA
  have hsp : s.st.1.regs.rsp.toBitVec = R.addr o.sp := Spike.Lib.X64ConsumerA.rsp_of_abs hA'
  refine ⟨?_, raAddr_of (h2 ▸ hra) hsp (fun k hk => ?_), by rw [privLoad_slot hA' hoff, hx], _, hso.1, hso.2, hsp⟩
  · show _ ≤ s.st.2.toBitVec.toNat ∧ s.st.2.toBitVec.toNat < _
    rw [h2]; exact hpc
  · rw [hA'.regs]; exact hA'.so .rbp k hk

section Blk

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int} {ra : BitVec 64}

/-- **`AbP` along a block** and at its successors, from its abstract run:
each pc it reaches on the path (`hpc`), the return address word at offset
`8` (`hra`), each static `%rsp` offset in `[-32, 8]` (`hso`), `slot 8 = ra`
throughout (`hx`). -/
theorem abP_blk
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi) (hoff : R.Off 8)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hpc : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      (L.lab "scc_rt_abort").toBitVec.toNat ≤
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat <
          (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hra : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      RaOK L (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so)
    (hso : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      -32 ≤ (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ≤ 8)
    (hx : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot 8 = ra) :
    BlkW (fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s') (fun _ _ => False)
      exe endPc R F n blk := by
  refine Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns ?_ ?_
  · intro σ c hJ k hk s m hA _ _ hs
    have hp0 := Spike.Lib.X64.arun_pc (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
    have hp := hpc σ c hJ k (Nat.le_of_lt hk)
    have hr := hra σ c hJ k (Nat.le_of_lt hk)
    rw [hp0] at hp hr
    exact abP_of hs hA hoff hp hr (hso σ c hJ k (Nat.le_of_lt hk)) (hx σ c hJ k (Nat.le_of_lt hk))
  · intro σ c hJ k hk s m hA _ _ hs
    exact abP_of hs hA hoff (hpc σ c hJ (k + 1) hk) (hra σ c hJ (k + 1) hk) (hso σ c hJ (k + 1) hk)
      (hx σ c hJ (k + 1) hk)

/-- **A `syscall` state's successors off the take site keep `%rsp`, `%rbp`
and the private memory**: the kernel's resumptions write registers only. -/
theorem keepM_syscall (hs : abi.atSys s = true) (hns : ∀ a, μ.site .take = some a → pcOf s ≠ a) {s' : State}
    (h : StSucc μ s s') : Keep s s' ∧ s'.st.1.dmem = s.st.1.dmem := by
  refine ⟨keep_syscall hs h, ?_⟩
  rcases h with ⟨hs', -⟩ | ⟨-, call, -, hm⟩ | ⟨a, ha, hpc, -⟩
  · rw [hs] at hs'; cases hs'
  · cases call with
    | archSetFs x =>
      simp only [Scc.Sem.Kernel.certSuccs] at hm
      rw [List.mem_singleton.mp hm]; rfl
    | _ =>
      simp only [Scc.Sem.Kernel.certSuccs] at hm
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
      rfl
  · exact absurd hpc (hns a ha)

/-- **`AbP` at a node** and at its successors, which keep `%rsp`, `%rbp` and
the private memory and are `sz` bytes past it (`hk`: `keepM_syscall` with
`keep_pc`): its pc and the next on the path (`hpc`), the return address
word at offset `8` at both (`hra`), its static `%rsp` offset in `[-32, 8]`
(`hso`), `slot 8 = ra` (`hx`). -/
theorem abP_node {sz : Nat} (hoff : R.Off 8)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' →
      Keep s s' ∧ s'.st.1.dmem = s.st.1.dmem ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : ∀ p ∈ [n.pc, n.pc + Int64.ofNat sz], (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
      p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hra : ∀ p ∈ [n.pc, n.pc + Int64.ofNat sz], RaOK L p n.o)
    (hso : -32 ≤ n.o.sp ∧ n.o.sp ≤ 8) (hx : ∀ σ c, n.J σ c → σ.slot 8 = ra) :
    NodeW (fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hst : s.st = (s.st.1, n.pc) := by rw [← hp]
  have h0 := abP_of hst hA hoff (hpc _ (by simp)) (hra _ (by simp)) hso (hx σ c hJ)
  refine ⟨⟨h0, fun s' h => ?_⟩, fun _ h => h⟩
  obtain ⟨⟨h1, h2, -⟩, hdm, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  have hsp : s'.st.1.regs.rsp.toBitVec = R.addr n.o.sp := by
    rw [h1]; exact Spike.Lib.X64ConsumerA.rsp_of_abs hA
  refine ⟨?_, raAddr_of (by rw [h3]; exact hra _ (by simp)) hsp (fun k hk => ?_), ?_, _, hso.1, hso.2, hsp⟩
  · show _ ≤ s'.st.2.toBitVec.toNat ∧ s'.st.2.toBitVec.toNat < _
    rw [h3]; exact hpc _ (by simp)
  · rw [h2, hA.regs]; exact hA.so .rbp k hk
  · rw [← h0.2.2.1]; unfold privLoad; rw [hdm]

/-- **A block's agreement from a predicate of its states and successors**
that picks the instance. -/
theorem BlkW.agree_of {P : State → Prop} {own own' : State → List (Loc × Val)}
    (h : BlkW (fun s _ => P s ∧ ∀ s', StSucc μ s s' → P s') (fun _ _ => False) exe endPc R F n blk)
    (hP : ∀ s, P s → own' s = own s) :
    BlkW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s') (fun _ _ => False)
      exe endPc R F n blk := by
  intro s σ c he hn hd hp hA hF hJ k hk m hAm hD
  obtain ⟨⟨h1, h2⟩, h3⟩ := h s σ c he hn hd hp hA hF hJ k hk m hAm hD
  exact ⟨⟨hP _ h1, fun s' hs => hP _ (h2 s' hs)⟩, h3⟩

/-- **A node's agreement from a predicate of its states and successors**
that picks the instance. -/
theorem NodeW.agree_of {P : State → Prop} {own own' : State → List (Loc × Val)}
    (h : NodeW (fun s _ => P s ∧ ∀ s', StSucc μ s s' → P s') (fun _ _ => False) exe endPc R F n)
    (hP : ∀ s, P s → own' s = own s) :
    NodeW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨⟨h1, h2⟩, h3⟩ := h s c hAt
  exact ⟨⟨hP _ h1, fun s' hs => hP _ (h2 s' hs)⟩, h3⟩

end Blk

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.raAddr_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raAddr_of

/-- info: 'Spike.Lib.X64.WakePh.privLoad_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.privLoad_slot

/-- info: 'Spike.Lib.X64.WakePh.raAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raAt_iff

/-- info: 'Spike.Lib.X64.WakePh.spPool_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.spPool_of_band

/-- info: 'Spike.Lib.X64.WakePh.not_spPool_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.not_spPool_of_band

/-- info: 'Spike.Lib.X64.WakePh.ra_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ra_ne

/-- info: 'Spike.Lib.X64.WakePh.good2a_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.good2a_ab

/-- info: 'Spike.Lib.X64.WakePh.good2b_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.good2b_ab

/-- info: 'Spike.Lib.X64.WakePh.goodW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.goodW_ab

/-- info: 'Spike.Lib.X64.WakePh.abP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abP_of

/-- info: 'Spike.Lib.X64.WakePh.abP_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abP_blk

/-- info: 'Spike.Lib.X64.WakePh.keepM_syscall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keepM_syscall

/-- info: 'Spike.Lib.X64.WakePh.abP_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abP_node

/-- info: 'Spike.Lib.X64.WakePh.BlkW.agree_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.BlkW.agree_of

/-- info: 'Spike.Lib.X64.WakePh.NodeW.agree_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.NodeW.agree_of
