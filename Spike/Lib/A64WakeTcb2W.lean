/-
**wc_main's second `scc_rt_alloc_tcb` call inside the global owned-words
map** (AArch64): the node obligations `TcbWG` of `scc_rt_alloc_tcb` at
`tcb2Q g c0` for `SFactsSt2` at `ownG` (`tcb2W_ownG`), from the instance's
(`tcbW_postG` at `instOk2aP`, `tcbPh2a`) moved along `ownG = own2a ∘ ph2a`
where `ownG` picks `own2a` (`Good2a`: the callee's pcs on a pool stack, its
return to `.sp4`).

- `blkW_toSt2`, `nodeW_toSt2`: a node's `SFacts` as `SFactsSt2`.
- `nodeW_ownCongr2`: `BlkW.ownCongr2` for a node.
- `PcA`, `BandA`, `good2a_of`: where `Good2a` holds by the pc and `sp`.
- `good2a_blk`, `good2a_node`: `Good2a` at a block's (a node's) states and
  their successors.
- `keep_rmw`, `keep_hdr`: the counter's add and the header's store keep `sp`
  and `x30`.
- `tcb2W_ownG`: the result.
-/
import Spike.Lib.A64WakeTcb2Call
import Spike.Lib.A64WakeOwnGAgree
import Spike.Lib.A64WakeOwnGAbT
import Spike.Lib.Rt.A64CallSwitch2

namespace Spike.Lib.A64.WakePh.Tcb2W

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf nextPc abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (SFacts Lbl)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At AM SO)

/-! ### `SFacts` as `SFactsSt2`, moved along an agreeing map -/

section Congr

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own own' : Spike.Lib.A64Consumer.Own} {rS : Range}
  {Tk : State → Prop} {lbl : Lbl} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {n : ND}

/-- **A block's `SFacts` as `SFactsSt2`.** -/
theorem blkW_toSt2 {blk : List Directive}
    (h : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 Λ μ own s) K exe endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
    let r := h s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
    ⟨r.1.toSt.toSt2, r.2⟩

/-- **A node's `SFacts` as `SFactsSt2`.** -/
theorem nodeW_toSt2 (h : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n) :
    NodeW (fun s _ => SFactsSt2 Λ μ own s) K exe endPc R F n :=
  fun s c hA => let r := h s c hA; ⟨r.1.toSt.toSt2, r.2⟩

/-- **A node's states at an agreeing map** (`BlkW.ownCongr2` for a node). -/
theorem nodeW_ownCongr2 {Dt : State → Prop} (h : NodeW (fun s _ => SFactsSt2 Λ μ own s Dt) K exe endPc R F n)
    (hag : NodeW (fun s _ => own' s = own s ∧ ∀ s', StSucc μ s s' → own' s' = own s') (fun _ _ => False)
      exe endPc R F n) :
    NodeW (fun s _ => SFactsSt2 Λ μ own' s Dt) K exe endPc R F n :=
  fun s c hA => ⟨(h s c hA).1.congr (hag s c hA).1.1 (hag s c hA).1.2, (h s c hA).2⟩

end Congr

/-! ### Where `ownG` picks `own2a`, by the pc and `sp` -/

/-- **The pcs where `ownG` picks `own2a`**: `scc_rt_alloc_tcb`'s (on a pool
stack) or `wc_main`'s from `.sp4` to `.sp6`, at the canonical base. -/
def PcA (p : Int64) : Prop :=
  (2164712 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2165132) ∨
    (2169268 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2169292)

instance (p : Int64) : Decidable (PcA p) := by unfold PcA; infer_instance

/-- **`scc_rt_alloc_tcb`'s frame on a pool stack**: every address of
`[-192, 0]` of `R` in `(pool.lo, pool.lo + pool.size]`. -/
def BandA (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -192 ≤ k → k ≤ 0 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

variable {L : RuntimeLayout}

/-- **`Good2a` by the pc and `sp`.** -/
theorem good2a_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (hb : BandA L R) {s : State} (hp : PcA s.st.2) (hsp : SpAt R (-192) 0 s) : Good2a L s := by
  obtain ⟨e1, e2, -, -, e5, e6, -, -, -⟩ := labs_eq hlab (L := L)
  obtain ⟨k, h1, h2, hk⟩ := hsp
  unfold Good2a inPc pcOf
  rw [e1, e2, e5, e6]
  rcases hp with hp | hp
  · exact .inl ⟨hp, by unfold spPool; rw [hk]; exact hb k h1 h2⟩
  · exact .inr (.inl hp)

/-- The static offsets after directives (`arun`'s). -/
def soRun (ds : List Directive) (o : SO) : SO :=
  ds.foldl (fun o d => match Spike.Lib.A64.Flow.classify d with | some a => a.so o | none => o) o

theorem arun_so (lab : Label → Int64) :
    ∀ (ds : List Directive) (am : AM), (Spike.Lib.A64.Flow.arun lab ds am).so = soRun ds am.so
  | [], _ => rfl
  | d :: ds, am => by
    show (Spike.Lib.A64.Flow.arun lab ds (Spike.Lib.A64.Flow.dstep lab am d)).so = soRun ds _
    rw [arun_so lab ds]
    simp only [Spike.Lib.A64.Flow.dstep]
    split <;> simp_all [soRun]

section Blk

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List Directive} {blo bhi : Int}

/-- **`Good2a` along a block** and at its successors, from its abstract
run: each pc it reaches in `PcA` (`hpc`), each static `sp` offset in
`[-192, 0]` (`hso`), the frame on a pool stack (`hb`). -/
theorem good2a_blk (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandA L R)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hpc : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcA (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    BlkW (fun s _ => Good2a L s ∧ ∀ s', StSucc μ s s' → Good2a L s') (fun _ _ => False)
      exe endPc R F n blk := by
  have hsp : ∀ {o : SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS}, Spike.Lib.A64.Flow.Abs R o m σ →
      m.regs.SP.toBitVec = R.addr o.sp := fun hA => by rw [hA.regs]; exact hA.so .SP _ rfl
  refine Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo hhi hns ?_ ?_
  · intro σ c hJ k hk s m hA _ _ hs
    have hp := hpc σ c hJ k (Nat.le_of_lt hk)
    rw [Spike.Lib.A64.Flow.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk] at hp
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2a_of hlab hb (by rw [hs]; exact hp) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact hsp hA
  · intro σ c hJ k hk s m hA _ _ hs
    have ho := hso (k + 1) hk
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2a_of hlab hb (by rw [hs]; exact hpc σ c hJ (k + 1) hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact hsp hA

/-- **`hpc` of `good2a_blk`** from the block's pcs (`h1`) and where its
run ends (`h2`). -/
theorem hpc_of (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (h1 : ∀ k < blk.length, PcA (n.pc + Int64.ofNat (4 * k)))
    (h2 : ∀ σ c, n.J σ c → PcA (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) :
    ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcA (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc := by
  intro σ c hJ k hk
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [Spike.Lib.A64.Flow.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk]; exact h1 k hk
  · rw [List.take_length]; exact h2 σ c hJ

/-- **`Good2a` at a node** and at its successors, which keep `sp` and `x30`
and are 4 bytes past it (`hk`): its pc and the next in `PcA` (`hpc`), its
static `sp` offset in `[-192, 0]` (`hso`). -/
theorem good2a_node (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandA L R)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcA n.pc ∧ PcA (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => Good2a L s ∧ ∀ s', StSucc μ s s' → Good2a L s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := by rw [hA.regs]; exact hA.so .SP _ rfl
  refine ⟨⟨good2a_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact good2a_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

end Blk

/-! ### The successors of the counter's add and the header's store -/

section Keep

variable {μ : Marks} {s s' : State}

/-- **The counter's add `ldaddal x9, x11, [x10]`** at an unmapped word keeps
`sp` and `x30`. -/
theorem keep_rmw (hc : Kraken.Promising.Lower.A64.CellAt s Spike.Lib.A64.Flow.Ret0.AllocTcb.rmwDir 4)
    (hdc : s.decls = {}) (hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_ldop hc hdm] at htr
    cases htr
    rw [hdc, EvTree.access_empty] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **The header's store `str x9, [x10]`** at an unmapped word keeps `sp`
and `x30`. -/
theorem keep_hdr (hc : Kraken.Promising.Lower.A64.CellAt s Spike.Lib.A64.Flow.Ret0.AllocTcb.hdrDir 4)
    (hdc : s.decls = {}) {a : BitVec 64}
    (ha : BitVec.ofInt 64 ((s.st.1.regs.getXReg .X10).toBitVec.toInt + (0 : Int64).toInt) = a)
    (hdm : Mem.loadInt s.st.1.dmem a 8 = none) (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_str hc ha hdm] at htr
    cases htr
    rw [hdc, EvTree.access_empty] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

end Keep

/-! ### A block's and a node's obligations at `ownG` from the instance's -/

section Move

variable {Λ : Scc.Sem.Layout} {μ : Marks} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND}

/-- `PcA` is off the take site (`scc_rt_take_site` at `2165940`). -/
theorem pcA_ne {p : Int64} (h : PcA p) : p.toBitVec.toNat ≠ 2165940 := by
  unfold PcA at h; omega

/-- **A block of the call at `ownG`** from the instance's `SFacts`: the
block's pcs in `PcA` (`h1`), where its run ends (`h2`), its static `sp`
offsets in `[-192, 0]` (`hso`), the take site at `2165940` (`hsite`). -/
theorem blk2a (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandA L R)
    (hsite : ∀ x, μ.site .take = some x → x = 2165940) {blk : List Directive} {blo bhi : Int}
    (h : BlkW (fun s c => SFacts Λ μ (fun s => own2a L a (ph2a (pcOf s))) rS Tk lbl s c) K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcA (n.pc + Int64.ofNat (4 * k)))
    (h2 : ∀ σ c, n.J σ c → PcA (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    BlkW (fun s _ => SFactsSt2 Λ μ (ownG L a) s) K exe endPc R F n blk :=
  Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (blkW_toSt2 h)
    (BlkW.agree_of (good2a_blk hlab hb hcode hok hR hal hlo hhi
      (fun x hx k hk => by rw [hsite x hx]; exact pcA_ne (h1 k hk)) (hpc_of hok h1 h2) hso)
      fun _ hs => ownG_2a hlab hs)

/-- **A node of the call at `ownG`** from the instance's `SFacts`: its
successors keeping `sp` and `x30` 4 bytes on (`hk`), its pc and the next in
`PcA` (`hpc`), its static `sp` offset in `[-192, 0]` (`hso`). -/
theorem node2a (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandA L R)
    (h : NodeW (fun s c => SFacts Λ μ (fun s => own2a L a (ph2a (pcOf s))) rS Tk lbl s c) K exe endPc R F n)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcA n.pc ∧ PcA (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 Λ μ (ownG L a) s) K exe endPc R F n :=
  nodeW_ownCongr2 (nodeW_toSt2 h)
    (NodeW.agree_of (good2a_node hlab hb hk hpc hso) fun _ hs => ownG_2a hlab hs)

end Move

/-! ### The call's node obligations at `ownG` -/

open Spike.Lib.A64.Flow.Ret0 (TN StackM)
open Spike.Lib.A64.Flow.Ret0.AllocTcb
open Spike.Lib.A64.WakePh.Tcb2Call (tcb2Q)

/-- The labels the call's pcs are decided from, at the canonical base. -/
theorem tcb_labs (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) :
    (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 2164712 ∧ (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 2164736 ∧ (_root_.Executable.labels L.exe).label lenL = Int64.ofNat 2164756 ∧
    (_root_.Executable.labels L.exe).label okL = Int64.ofNat 2164960 ∧ (_root_.Executable.labels L.exe).label ".L21_wc_main.sp4" = Int64.ofNat 2169268 ∧
    (_root_.Executable.labels L.exe).label Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

theorem wake_allocTcbIn : allocTcbIn wakeProg = true := by decide +kernel

/-- `hso` of `blk2a` on a block at offsets `o`, decided. -/
local macro "soT " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -192 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 0
    by decide) k hk)

/-- **`scc_rt_alloc_tcb`'s node obligations at `tcb2Q g c0` inside
`SFactsSt2` at `ownG`**: `tcbW_postG` at the second call's instance
(`instOk2aP`, `tcbPh2a`), each node moved to `ownG` where it picks `own2a`
(`blk2a`, `node2a`): the frame on a pool stack (`hb`), the return to
`.sp4` (`hra`), the counter's and the header's words mapped (`hmP`, `hmH`)
and off private memory (`hunP`, `hunH`). -/
theorem tcb2W_ownG {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    {rS : Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ a)
    (hhdr : L.pinA + 80#64 + 16#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hC0 : Spike.Lib.A64Consumer.CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hb : BandA L R) (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (hra : g.ra = (L.lab ".L21_wc_main.sp4").toBitVec)
    {F : MachineData → Prop}
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) true
      ⟨Spike.Lib.A64.Rt.hdrA L.lab (tcb2Q g c0), 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Rt.hdrA L.lab (tcb2Q g c0)) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hSM : Spike.Lib.A64.Flow.FStable R (StackM rS)) :
    ∀ i, Spike.Lib.A64.Rt.TcbWG (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s)
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R (fun m => F m ∧ StackM rS m) (tcb2Q g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, eSp4, eSite⟩ := tcb_labs hlab (L := L)
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hT := Spike.Lib.A64.Rt.Tcb.tcbW_postG (instOk2aP hp hlo a hsite (rS := rS)) (fun _ => rfl)
    (hp ▸ wake_allocTcbIn) hC0 hR hal hlo' hhi (tcb2Q g c0) rfl
    (ra := fun _ => L.lab ".L21_wc_main.sp4") hra (tcbPh2a hΛ hlab hsep hhdr)
    (hpn ▸ hmP) hmH (hpn ▸ hunP) hunH hsub hSM
  have hsite' : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165940 := by
    intro x hx
    rw [hsite, show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 from eSite] at hx
    cases hx; rfl
  have hin := hp ▸ wake_allocTcbIn
  simp only [allocTcbIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := hin
  intro i
  have h := hT i
  cases i <;> dsimp only [Spike.Lib.A64.Rt.TcbWG] at h ⊢
  case e =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bE (Spike.Lib.A64.Flow.ofNat4_zero _))
      atPro_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atPro oE)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eFn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [(atPro_walkG _ _ hJ.2).1, eFn]; decide
  case entry =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bEn (Spike.Lib.A64.Flow.ofNat4_zero _))
      atChk_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atChk oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eEn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [(atChk_walkG _ _ hJ.2).1, eEn]; decide
  case j1 =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bJ1 rfl)
      atJ1_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atJ1 oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eEn]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [atJ1_run]; dsimp only; rw [eLen]; decide
  case len =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bLen (Spike.Lib.A64.Flow.ofNat4_zero _))
      atLen_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atLen oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [(atLen_walkG _ _ hJ.2).1, eLen]; decide
  case arg =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bArg rfl)
      atArg_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atArg oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [(atArg_walkG _ _ hJ.2.1 hJ.2.2).1, eLen]; decide
  case bnd =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bBnd rfl)
      atBnd_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atBnd oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢
      rw [(atBnd_walkG _ _ hJ.2.1 hJ.2.2 (by show (80#64).toNat + (lenOf hdr2).toNat ≤ 131072; decide)).1, eLen]; decide
  case j2 =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bJ2 rfl)
      atJ2_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atJ2 oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [atJ2_run]; dsimp only; rw [eOk]; decide
  case ok2 =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bO2 rfl)
      atOk_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atOk oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢; rw [(atOk_walkG _ _ hJ.2.1 hJ.2.2).1, eOk]; decide
  case ret =>
    refine blk2a hlab hb hsite' h (Spike.Lib.A64.Flow.code_of L.lays rfl bRet rfl)
      atRet_ok hR hal (by omega) (by omega) ?_ (fun σ c hJ => ?_) (soT atRet oI)
    · intro k hk; dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; revert k; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ ⊢
      rw [(atRet_walkG _ _ hJ.2).1]
      show PcA (Int64.ofBitVec g.ra)
      rw [hra, Int64.ofBitVec_toBitVec, show L.lab ".L21_wc_main.sp4" = Int64.ofNat 2169268 from eSp4]; decide
  case adrp =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bA rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      exact ⟨keep_adrp hc hs, by rw [keep_pc hc (keep_adrp hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; decide
  case add =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bA1 rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      exact ⟨keep_add hc hs, by rw [keep_pc hc (keep_add hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eLen]; decide
  case ok =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bO (Spike.Lib.A64.Flow.ofNat4_zero _) s he hn).cell
        (j := 0) rfl rfl rfl (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      exact ⟨keep_adrp hc hs, by rw [keep_pc hc (keep_adrp hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; decide
  case ok1 =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, -, hp', -⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bO1 rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      exact ⟨keep_add hc hs, by rw [keep_pc hc (keep_add hc hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG]; rw [eOk]; decide
  case rmw =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bRmw rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      have hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 = none := by
        dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ
        rw [hA.regs]; simp only [Reg64s.getXReg]; rw [hJ.2.2.2, hpn]; exact hunP _ hF.1
      exact ⟨keep_rmw hc hd hdm hs, by rw [keep_pc hc (keep_rmw hc hd hdm hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc]; rw [eLen]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc]; rw [eLen]; decide
  case hdr =>
    refine node2a hlab hb h (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩ (by dsimp only [Spike.Lib.A64.Rt.tcbNG]; decide)
    · obtain ⟨he, hn, hd, hp', σ, hA, hF, hJ⟩ := hAt
      have hc := (Spike.Lib.A64.Flow.code_of L.lays rfl bH rfl s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hp']; dsimp only [Spike.Lib.A64.Rt.tcbNG, rmwPc, hdrPc]; simp)
      dsimp only [Spike.Lib.A64.Rt.tcbNG] at hJ
      have ha : BitVec.ofInt 64 ((s.st.1.regs.getXReg .X10).toBitVec.toInt + (0 : Int64).toInt) =
          Spike.Lib.A64.Rt.hdrA L.lab (tcb2Q g c0) := by
        rw [hA.regs, ← hJ.2.2.2]; simp [Reg64s.getXReg]
      exact ⟨keep_hdr hc hd ha (hunH _ hF.1) hs, by rw [keep_pc hc (keep_hdr hc hd ha (hunH _ hF.1) hs), hp']; rfl⟩
    · dsimp only [Spike.Lib.A64.Rt.tcbNG, hdrPc]; rw [eOk]; decide
    · dsimp only [Spike.Lib.A64.Rt.tcbNG, hdrPc]; rw [eOk]; decide

/-- info: 'Spike.Lib.A64.WakePh.Tcb2W.tcb2W_ownG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcb2W_ownG

end Spike.Lib.A64.WakePh.Tcb2W
