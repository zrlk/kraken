/-
**wake.w's global owned-words map on the threads abort path** (AArch64):
`scc_rt_abort(5)` and `scc_rt_abort_threads` run with the pc in
`[scc_rt_abort, scc_rt_thr_worker)`, `x30` the caller's return address `ra`
throughout (`Abort.Disp.DN.nd5`, `Abort.NT`) and `sp` in the 48 bytes below
the caller's (`AbP`); there `ownG` picks the instance by `ra` and the band
(`good2a_ab`, `good2b_ab`, `goodW_ab`).

- `AbP`: the pc on the path, `x30 = ra`, `sp` in the band.
- `good2a_ab`, `good2b_ab`, `goodW_ab`: where `ownG` picks each instance on
  the path.
- `abP_blk`: `AbP` at a block's states and their successors, from the
  block's abstract run (pcs, static `sp` offsets, `x30`).
- `abP_node`: the same at a node whose successors keep `sp` and `x30` and
  move the pc by 4 (`Keep`).
-/
import Spike.Lib.A64WakeOwnGNode
import Spike.Lib.A64SpAgree

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf nextPc abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc SpAt)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)

variable {L : RuntimeLayout} {s : State}

/-- **On the abort path with return address `ra`**: the pc in
`[scc_rt_abort, scc_rt_thr_worker)`, `x30 = ra`, `sp` at `R.addr k` for a `k`
in `[-48, 0]`. -/
def AbP (L : RuntimeLayout) (R : Region) (ra : BitVec 64) (s : State) : Prop :=
  inPc L "scc_rt_abort" "scc_rt_thr_worker" s ∧ s.st.1.regs.X30.toBitVec = ra ∧ SpAt R (-48) 0 s

/-- **The band on a pool stack**: every address of `[-48, 0]` of `R` in
`(pool.lo, pool.lo + pool.size]`. -/
def BandIn (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -48 ≤ k → k ≤ 0 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

/-- **The band off the pool stacks.** -/
def BandOut (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -48 ≤ k → k ≤ 0 → ¬ (L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)

theorem spPool_of_band {R : Region} (hb : BandIn L R) (h : SpAt R (-48) 0 s) : spPool L s := by
  obtain ⟨k, h1, h2, hk⟩ := h
  unfold spPool; rw [hk]; exact hb k h1 h2

theorem not_spPool_of_band {R : Region} (hb : BandOut L R) (h : SpAt R (-48) 0 s) : ¬ spPool L s := by
  obtain ⟨k, h1, h2, hk⟩ := h
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- The two return addresses on the path differ. -/
private theorem ra_ne (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec ≠ (L.lab ".L21_wc_main.sp11").toBitVec := by
  rw [hlab _ 2164956 (by rw [← codeT_eq]; decide +kernel), hlab _ 2169384 (by rw [← codeT_eq]; decide +kernel)]
  decide

/-- **`ownG` picks `own2a` on the path** from `scc_rt_alloc_tcb`'s abort on a
pool stack. -/
theorem good2a_ab {R : Region} (h : AbP L R (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec s) (hb : BandIn L R) :
    Good2a L s :=
  .inr (.inr ⟨h.1, h.2.1, spPool_of_band hb h.2.2⟩)

/-- **`ownG` picks `own2b` on the path** from `wc_main`'s spawn failure. -/
theorem good2b_ab (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (h : AbP L R (L.lab ".L21_wc_main.sp11").toBitVec s) : Good2b L s :=
  .inr (.inr ⟨h.1, h.2.1, fun ⟨hx, _⟩ => ra_ne hlab (hx.symm.trans h.2.1)⟩)

/-- **`ownG` picks `ownW` on the path** from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem goodW_ab {R : Region} {ra : BitVec 64} (h : AbP L R ra s)
    (h13 : ra = (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec → BandOut L R)
    (h11 : ra ≠ (L.lab ".L21_wc_main.sp11").toBitVec) : GoodW L s := by
  refine .inr (.inl ⟨h.1, fun ⟨hx, hp⟩ => ?_, fun hx => h11 (h.2.1.symm.trans hx)⟩)
  exact not_spPool_of_band (h13 (h.2.1.symm.trans hx)) h.2.2 hp

section Blk

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List Directive} {blo bhi : Int} {ra : BitVec 64}

/-- **`AbP` along a block** and at its successors, from its abstract run:
each pc it reaches on the path (`hpc`), each static `sp` offset in
`[-48, 0]` (`hso`), `x30 = ra` throughout (`hx`). -/
theorem abP_blk
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hpc : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      (L.lab "scc_rt_abort").toBitVec.toNat ≤
          (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat <
          (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hso : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      -48 ≤ (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ≤ 0)
    (hx : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.X30.toBitVec = ra) :
    BlkW (fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s') (fun _ _ => False)
      exe endPc R F n blk := by
  have habs : ∀ {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS},
      Spike.Lib.A64.Flow.Abs R o m σ → m.regs.SP.toBitVec = R.addr o.sp ∧ m.regs.X30 = σ.regs.X30 :=
    fun hA => ⟨by rw [hA.regs]; exact hA.so .SP _ rfl, by rw [hA.regs]⟩
  refine Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo hhi hns ?_ ?_
  · intro σ c hJ k hk s m hA he hn hs
    obtain ⟨h1, h2⟩ := habs hA
    have hp := hpc σ c hJ k (Nat.le_of_lt hk)
    rw [Spike.Lib.A64.Flow.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk] at hp
    have ho := hso σ c hJ k (Nat.le_of_lt hk)
    refine ⟨?_, ?_, _, ho.1, ho.2, ?_⟩
    · show _ ≤ s.st.2.toBitVec.toNat ∧ s.st.2.toBitVec.toNat < _
      rw [hs]; exact hp
    · rw [hs]; show m.regs.X30.toBitVec = ra; rw [h2]; exact hx σ c hJ k (Nat.le_of_lt hk)
    · rw [hs]; exact h1
  · intro σ c hJ k hk s m hA he hn hs
    obtain ⟨h1, h2⟩ := habs hA
    have hp := hpc σ c hJ (k + 1) hk
    have ho := hso σ c hJ (k + 1) hk
    refine ⟨?_, ?_, _, ho.1, ho.2, ?_⟩
    · show _ ≤ s.st.2.toBitVec.toNat ∧ s.st.2.toBitVec.toNat < _
      rw [hs]; exact hp
    · rw [hs]; show m.regs.X30.toBitVec = ra; rw [h2]; exact hx σ c hJ (k + 1) hk
    · rw [hs]; exact h1

/-- **`AbP` at a node** and at its successors, which keep `sp` and `x30` and
are 4 bytes past it (`hk`: `keep_si`, `keep_svc` with `keep_pc`): its pc
and the next on the path (`hpc`), its static `sp` offset in `[-48, 0]`
(`hso`), `x30 = ra` (`hx`). -/
theorem abP_node
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : ∀ p ∈ [n.pc, n.pc + 4], (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
      p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hso : -48 ≤ n.o.sp ∧ n.o.sp ≤ 0) (hx : ∀ σ c, n.J σ c → σ.regs.X30.toBitVec = ra) :
    NodeW (fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := by rw [hA.regs]; exact hA.so .SP _ rfl
  have hx30 : s.st.1.regs.X30.toBitVec = ra := by rw [hA.regs]; exact hx σ c hJ
  refine ⟨⟨⟨?_, hx30, _, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
  · show _ ≤ s.st.2.toBitVec.toNat ∧ s.st.2.toBitVec.toNat < _
    rw [hp]; exact hpc _ (by simp)
  · obtain ⟨⟨h1, h2, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
    refine ⟨?_, by rw [h2]; exact hx30, _, hso.1, hso.2, by rw [h1]; exact hsp⟩
    show _ ≤ s'.st.2.toBitVec.toNat ∧ s'.st.2.toBitVec.toNat < _
    rw [h3]; exact hpc _ (by simp)

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

/-- info: 'Spike.Lib.A64.WakePh.abP_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.abP_blk

/-- info: 'Spike.Lib.A64.WakePh.abP_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.abP_node

end Spike.Lib.A64.WakePh
