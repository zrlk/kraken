/-
**wc_main's second `scc_rt_alloc_tcb` call inside the global owned-words
map, the tools** (x86-64; the first half of the twin of
`Spike/Lib/A64WakeTcb2W.lean`, the result in
`Spike/Lib/X64WakeTcb2W.lean`): a node's obligations at the instance's map
`own2a ∘ ph2a` moved to `ownG` where `ownG` picks `own2a` (`Good2a`: the
callee's pcs on a pool stack, its return to `.Lwc_main.x20`).

- `blkW_toSt2`, `nodeW_toSt2`: a node's `SFacts` as `SFactsSt2`.
- `nodeW_ownCongr2`: `BlkW.ownCongr2` for a node.
- `PcA`, `BandA`, `good2a_of`: where `Good2a` holds by the pc and `%rsp`.
- `good2a_blk`, `good2a_node`: `Good2a` at a block's (a node's) states and
  their successors.
- `keep_fi`, `keep_lea`, `keep_rmw`, `keep_hdr`: the length computation's
  flag-clobbering instructions, the `leaq`s, the counter's `lock xadd` and
  the header's store keep `%rsp` and `%rbp`.
- `blk2a`, `node2a`: a block's (a node's) `SFacts` at the instance's map
  as `SFactsSt2` at `ownG`.

**Unlike AArch64**: no `hal`; the band is `[-184, 8]` (the frame of 176,
the saved `%rbp`, the return address; A64's `[-192, 0]`); a block's pcs are
its pc plus `cellOff`; a node's successor is `sz` bytes on (A64's `4`);
`Keep` is `%rsp`/`%rbp` (A64's `sp`/`x30`); the extra node kinds (`FI`,
`leaq`) have their own `keep_*`.
-/
import Spike.Lib.X64WakeTcb2Call
import Spike.Lib.X64WakeOwnGAgree
import Spike.Lib.X64WakeOwnGAbT
import Spike.Lib.Rt.X64CallSwitch2

namespace Spike.Lib.X64.WakePh.Tcb2W

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf nextPc abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (SFacts Lbl)
open Spike.Lib.X64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At SO SI FI AM Abs arun cellOff okBlk CodeAt xaddDir stDir mB)
open Kraken.Promising.Lower.X64 (CellAt eaddr)

/-! ### `SFacts` as `SFactsSt2`, moved along an agreeing map -/

section Congr

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own own' : Spike.Lib.X64Consumer.Own} {rS : Range}
  {Tk : State → Prop} {lbl : Lbl} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {n : ND}

/-- **A block's `SFacts` as `SFactsSt2`.** -/
theorem blkW_toSt2 {blk : List (Directive × Nat)}
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

/-! ### Where `ownG` picks `own2a`, by the pc and `%rsp` -/

/-- **The pcs where `ownG` picks `own2a`**: `scc_rt_alloc_tcb`'s (on a pool
stack) or `wc_main`'s from `.x20` to `.x21`, at the canonical base. -/
def PcA (p : Int64) : Prop :=
  (4198992 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 4199447) ∨
    (4203372 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 4203397)

instance (p : Int64) : Decidable (PcA p) := by unfold PcA; infer_instance

/-- **`scc_rt_alloc_tcb`'s frame on a pool stack**: every address of
`[-184, 8]` of `R` in `(pool.lo, pool.lo + pool.size]`. -/
def BandA (L : RuntimeLayout) (R : Region) : Prop :=
  ∀ k, -184 ≤ k → k ≤ 8 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

variable {L : RuntimeLayout}

/-- **`Good2a` by the pc and `%rsp`.** -/
theorem good2a_of (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {R : Region}
    (hb : BandA L R) {s : State} (hp : PcA s.st.2) (hsp : SpAt R (-184) 8 s) : Good2a L s := by
  obtain ⟨e1, e2, -, -, e5, e6, -, -, -⟩ := labs_eq hlab (L := L)
  obtain ⟨k, h1, h2, hk⟩ := hsp
  unfold Good2a inPc pcOf
  rw [e1, e2, e5, e6]
  rcases hp with hp | hp
  · exact .inl ⟨hp, by unfold spPool; rw [hk]; exact hb k h1 h2⟩
  · exact .inr (.inl hp)

/-- The static offsets after directives (`arun`'s). -/
def soRun (ds : List (Directive × Nat)) (o : SO) : SO :=
  ds.foldl (fun o d => match Spike.Lib.X64.classify d.1 with | some a => a.so o | none => o) o

theorem arun_so (lab : Label → Int64) :
    ∀ (ds : List (Directive × Nat)) (am : AM), (arun lab ds am).so = soRun ds am.so
  | [], _ => rfl
  | (d, z) :: ds, am => by
    show (arun lab ds (Spike.Lib.X64.dstep lab am (d, z))).so = soRun ds _
    rw [arun_so lab ds]
    simp only [Spike.Lib.X64.dstep]
    cases Spike.Lib.X64.classify d <;> rfl

section Blk

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`Good2a` along a block** and at its successors, from its abstract
run: each pc it reaches in `PcA` (`hpc`), each static `%rsp` offset in
`[-184, 8]` (`hso`), the frame on a pool stack (`hb`). -/
theorem good2a_blk (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandA L R)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hpc : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcA (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8) :
    BlkW (fun s _ => Good2a L s ∧ ∀ s', StSucc μ s s' → Good2a L s') (fun _ _ => False)
      exe endPc R F n blk := by
  refine Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns ?_ ?_
  · intro σ c hJ k hk s m hA _ _ hs
    have hp := hpc σ c hJ k (Nat.le_of_lt hk)
    rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk] at hp
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2a_of hlab hb (by rw [hs]; exact hp) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact Spike.Lib.X64ConsumerA.rsp_of_abs hA
  · intro σ c hJ k hk s m hA _ _ hs
    have ho := hso (k + 1) hk
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2a_of hlab hb (by rw [hs]; exact hpc σ c hJ (k + 1) hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact Spike.Lib.X64ConsumerA.rsp_of_abs hA

/-- **`hpc` of `good2a_blk`** from the block's pcs (`h1`) and where its
run ends (`h2`). -/
theorem hpc_of (hok : okBlk blo bhi n.o blk = true)
    (h1 : ∀ k < blk.length, PcA (n.pc + Int64.ofNat (cellOff blk k)))
    (h2 : ∀ σ c, n.J σ c → PcA (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) :
    ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      PcA (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc := by
  intro σ c hJ k hk
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [Spike.Lib.X64.arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk]; exact h1 k hk
  · rw [List.take_length]; exact h2 σ c hJ

/-- **`Good2a` at a node** and at its successors, which keep `%rsp` and
`%rbp` and are `sz` bytes past it (`hk`): its pc and the next in `PcA`
(`hpc`), its static `%rsp` offset in `[-184, 8]` (`hso`). -/
theorem good2a_node {sz : Nat} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandA L R)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : PcA n.pc ∧ PcA (n.pc + Int64.ofNat sz)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8) :
    NodeW (fun s _ => Good2a L s ∧ ∀ s', StSucc μ s s' → Good2a L s') (fun _ _ => False)
      exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.rsp.toBitVec = R.addr n.o.sp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
  refine ⟨⟨good2a_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact good2a_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

end Blk

/-! ### The successors of the single-instruction nodes -/

section Keep

variable {μ : Marks} {s s' : State}

/-- A silent tree's leaves satisfy its predicate. -/
theorem silent_leaf {σ : Type} {P : σ → Prop} :
    ∀ {t : EvTree σ} {x : σ}, Kraken.Promising.Lower.SilentTree P t → Scc.Sem.TreeLeaf t x → P x
  | .done _, _, h, hl => hl ▸ h
  | .choose _ _, _, h, ⟨i, hl⟩ => silent_leaf (h.2 i) hl
  | .fault .., _, h, _ => h.elim
  | .load .., _, h, _ => h.elim
  | .store .., _, h, _ => h.elim
  | .rmw .., _, h, _ => h.elim
  | .fence .., _, h, _ => h.elim

/-- **An instruction with undefined flags writing `%rax`** keeps `%rsp`
and `%rbp`. -/
theorem keep_fi {fi : FI} {z : Nat} (hc : CellAt s fi.toDir z) (hrax : fi.dst = some .rax)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by cases fi <;> intro w w' h <;> cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · obtain ⟨t, ht, hsil⟩ := Spike.Lib.X64.exec_fi hc
    rw [ht] at htr
    cases htr
    obtain ⟨fl, rfl⟩ := silent_leaf hsil hl
    refine ⟨?_, ?_, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩ <;>
      cases fi <;> simp only [FI.dst, Option.some.injEq, reduceCtorEq] at hrax <;> subst hrax <;> rfl
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **`leaq L(%rip), %rax`** keeps `%rsp` and `%rbp`. -/
theorem keep_lea {L' : Label} {z : Nat} (hc : CellAt s (SI.leaRip .rax L').toDir z) (h : StSucc μ s s') :
    Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Spike.Lib.X64.exec_si hc] at htr
    cases htr; cases hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **The counter's add `lock xaddq %rax, (%rcx)`** at a word `a`
unmapped in private memory keeps `%rsp` and `%rbp`. -/
theorem keep_rmw {z : Nat} (hc : CellAt s (xaddDir .rcx 0 .rax) z) (hdc : s.decls = {}) {a : BitVec 64}
    (ha : eaddr s z (mB .rcx 0) = a) (hdm : Mem.loadInt s.st.1.dmem a 8 = none) (h : StSucc μ s s') :
    Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_xaddG_agrees (w := .W64) hc ha hdm
      (Spike.Lib.X64.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **The header's store `movq %rax, (%rcx)`** at a word `a` unmapped in
private memory keeps `%rsp` and `%rbp`. -/
theorem keep_hdr {z : Nat} (hc : CellAt s (stDir .rcx 0 .rax) z) (hdc : s.decls = {}) {a : BitVec 64}
    (ha : eaddr s z (mB .rcx 0) = a) (hdm : Mem.loadInt s.st.1.dmem a 8 = none) (h : StSucc μ s s') :
    Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_store_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨b, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

end Keep

/-! ### A block's and a node's obligations at `ownG` from the instance's -/

section Move

variable {Λ : Scc.Sem.Layout} {μ : Marks} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND}

/-- `PcA` is off the take site (`scc_rt_take_site` at `4200277`). -/
theorem pcA_ne {p : Int64} (h : PcA p) : p.toBitVec.toNat ≠ 4200277 := by
  unfold PcA at h; omega

/-- **A block of the call at `ownG`** from the instance's `SFacts`: the
block's pcs in `PcA` (`h1`), where its run ends (`h2`), its static `%rsp`
offsets in `[-184, 8]` (`hso`), the take site at `4200277` (`hsite`). -/
theorem blk2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hb : BandA L R)
    (hsite : ∀ x, μ.site .take = some x → x = 4200277) {blk : List (Directive × Nat)} {blo bhi : Int}
    (h : BlkW (fun s c => SFacts Λ μ (fun s => own2a L a (ph2a (pcOf s))) rS Tk lbl s c) K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcA (n.pc + Int64.ofNat (cellOff blk k)))
    (h2 : ∀ σ c, n.J σ c → PcA (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8) :
    BlkW (fun s _ => SFactsSt2 Λ μ (ownG L a) s) K exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (blkW_toSt2 h)
    (BlkW.agree_of (good2a_blk hlab hb hcode hok hR hlo hhi
      (fun x hx k hk => by rw [hsite x hx]; exact pcA_ne (h1 k hk)) (hpc_of hok h1 h2) hso)
      fun _ hs => ownG_2a hlab hs)

/-- **A node of the call at `ownG`** from the instance's `SFacts`: its
successors keeping `%rsp` and `%rbp` `sz` bytes on (`hk`), its pc and the
next in `PcA` (`hpc`), its static `%rsp` offset in `[-184, 8]` (`hso`). -/
theorem node2a {sz : Nat} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandA L R)
    (h : NodeW (fun s c => SFacts Λ μ (fun s => own2a L a (ph2a (pcOf s))) rS Tk lbl s c) K exe endPc R F n)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : PcA n.pc ∧ PcA (n.pc + Int64.ofNat sz)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8) :
    NodeW (fun s _ => SFactsSt2 Λ μ (ownG L a) s) K exe endPc R F n :=
  nodeW_ownCongr2 (nodeW_toSt2 h)
    (NodeW.agree_of (good2a_node hlab hb hk hpc hso) fun _ hs => ownG_2a hlab hs)

end Move

end Spike.Lib.X64.WakePh.Tcb2W

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.good2a_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.good2a_of

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.arun_so' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.arun_so

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.good2a_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.good2a_blk

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.hpc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.hpc_of

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.good2a_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.good2a_node

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.silent_leaf' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.silent_leaf

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.keep_fi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.keep_fi

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.keep_lea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.keep_lea

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.keep_rmw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.keep_rmw

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.keep_hdr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.keep_hdr

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.pcA_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.pcA_ne

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.blk2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.blk2a

/-- info: 'Spike.Lib.X64.WakePh.Tcb2W.node2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2W.node2a
