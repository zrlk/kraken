/-
**wake.w's main thread owning its own TCB word** (x86-64): main's TCB
`tcbM = pinA + 8` (the first `scc_rt_alloc_tcb` call's, at header `hdr0`
and counter `0`, `tcb1Q_tcbOf`) holds its own address from `scc_rt_thread_init`'s
first store (`movq %rax, (%rcx)` at `.x7 + 48`, 3 bytes) on; `scc_rt_park`
reads it through `%fs:0`, so main's owned words carry it from there on,
appended to `ownG`'s (`ownGX`). The worker's map is not changed.

- `tcbM`, `mOf_hdr0`, `tcb1Q_tcbOf`, `tcbM_tcbOf`: main's TCB word, as the
  first call's `tcbOf` (checked by `decide`, `mOf 2307 = 0`).
- `selfOwn L s`: main owns `tcbM` at `s`: on a pool stack at a pc from
  `scc_rt_start`'s `.x1` on (main after `scc_rt_start`'s switch; below
  `.x1`, `_start` and `scc_rt_start`'s head, never on the pool, so there
  `selfOwn` reads the pc alone), in `scc_rt_start` from `.x1` to `scc_rt_main`,
  or from `.x7 + 51` (after the store) to `scc_rt_stack_take` (the rest of
  `scc_rt_thread_init`).
- `ownS L s`: `[(tcbM, tcbM)]` where `selfOwn`, else `[]`;
  `ownGX L a s := ownG L a s ++ ownS L s`; `ownGX_2a`, `ownGX_2b`,
  `ownGX_W`: at each instance (`ownG_2a` …).
- `ownS_congr`: `ownS` reads the pc and `%rsp` only.
- `writeTree_and`, `ownUpd_append`, `ownTree_append`: an `OwnTree` stays one with words `x`
  appended, constant over the leaves, not written by the tree and at
  locations none of `ow`'s (a lone store's take, `OwnTree`'s second case,
  becomes an `OwnUpd`, its third).
- `AppOk`, `SFactsSt.appendS`, `BlkW.appendS`: the state facts and a block's states
  with an appended map (`own s ++ ownS s`), given `ownS` constant over the
  successors, no write to its words and its locations off `own`'s.
- `ownG_addr`, `tcbM_sep`, `ownS_disj`: `ownG`'s words are the four
  counters and `a`; `tcbM` is none of the counters (`PhRec.TcbSep`), so off
  `a` it is none of `ownG`'s.
-/
import Spike.Lib.X64WakeOwnGEq
import Spike.Lib.X64OwnCongr
import Spike.Lib.Rt.X64RtTcbGN

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open SccCode (wakeCells)
open Spike.Lib.Consumer1 (OwnTree OwnUpd writeTree_mono)
open Spike.Lib.X64 (BlkW ND)
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt allInv_congr)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (mOf hdr0)

/-! ## Main's TCB word -/

/-- **Main's TCB word** `scc_rt_pinned + 8`. -/
abbrev tcbM (L : RuntimeLayout) : BitVec 64 := L.pinA + 8#64

/-- The first header's `m` is `0`. -/
theorem mOf_hdr0 : mOf hdr0 <<< 3 = 0#64 := by decide

/-- **The first call's TCB** (`scc_rt_start`'s, header `hdr0`, counter
`0`): `pinned + 8`. -/
theorem tcb1Q_tcbOf (lab : Label → Int64) (g : Flow.Ret0.AllocTcb.G) (c0 : Spike.Lib.Ctl) :
    tcbOf lab ⟨g, hdr0, 0#64, c0⟩ = Flow.Ret0.pinA lab + 8#64 := by
  show Flow.Ret0.pinA lab + 0#64 + mOf hdr0 <<< 3 + 8#64 = _
  rw [mOf_hdr0, BitVec.add_zero, BitVec.add_zero]

/-- `tcb1Q_tcbOf` at a record: `tcbM`. -/
theorem tcbM_tcbOf (L : RuntimeLayout) (g : Flow.Ret0.AllocTcb.G) (c0 : Spike.Lib.Ctl) :
    tcbOf L.lab ⟨g, hdr0, 0#64, c0⟩ = tcbM L := by
  rw [tcb1Q_tcbOf, L.lab_pin]

/-! ## The appended map -/

/-- **Main owns `tcbM` at `s`**: on a pool stack at a pc from `.x1` on, in `scc_rt_start` from
`.x1` to `scc_rt_main`, or in `scc_rt_thread_init` after its first store
(`.x7 + 51` up to `scc_rt_stack_take`). -/
def selfOwn (L : RuntimeLayout) (s : State) : Prop :=
  (spPool L s ∧ (L.lab ".Lscc_rt_start.x1").toBitVec.toNat ≤ pcOf s) ∨
    inPc L ".Lscc_rt_start.x1" "scc_rt_main" s ∨
    ((L.lab ".Lscc_rt_thread_init.x7").toBitVec.toNat + 51 ≤ pcOf s ∧
      pcOf s < (L.lab "scc_rt_stack_take").toBitVec.toNat)

instance (L : RuntimeLayout) (s : State) : Decidable (selfOwn L s) := by
  unfold selfOwn; infer_instance

/-- **Main's own TCB word**, owned holding its address where `selfOwn`. -/
def ownS (L : RuntimeLayout) (s : State) : List (Loc × Val) :=
  if selfOwn L s then [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] else []

/-- **Main's owned words**: `ownG`'s and its TCB word. -/
def ownGX (L : RuntimeLayout) (a : BitVec 64) (s : State) : List (Loc × Val) :=
  ownG L a s ++ ownS L s

/-- **`ownS` reads the pc and `%rsp` only.** -/
theorem ownS_congr {L : RuntimeLayout} {s s' : State} (hpc : pcOf s' = pcOf s)
    (hsp : s'.st.1.regs.rsp = s.st.1.regs.rsp) : ownS L s' = ownS L s := by
  have h : selfOwn L s' ↔ selfOwn L s := by unfold selfOwn spPool inPc; rw [hpc, hsp]
  unfold ownS; simp only [h]

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- `ownGX` where `ownG` picks `own2a`. -/
theorem ownGX_2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : Good2a L s) :
    ownGX L a s = own2a L a (ph2a (pcOf s)) ++ ownS L s := by
  rw [ownGX, ownG_2a hlab h]

/-- `ownGX` where `ownG` picks `own2b`. -/
theorem ownGX_2b (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : Good2b L s) :
    ownGX L a s = own2b L a (ph2b (pcOf s)) ++ ownS L s := by
  rw [ownGX, ownG_2b hlab h]

/-- `ownGX` where `ownG` picks `ownW`. -/
theorem ownGX_W (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (h : GoodW L s) :
    ownGX L a s = ownW L a (phW (pcOf s)) ++ ownS L s := by
  rw [ownGX, ownG_W hlab h]

/-! ## `OwnTree` with appended words -/

/-- **Two `WriteTree`s conjoined.** -/
theorem writeTree_and {σ : Type} {G G' : Loc → Val → Prop} :
    ∀ {t : EvTree σ}, WriteTree G t → WriteTree G' t → WriteTree (fun l v => G l v ∧ G' l v) t
  | .done _, _, _ => trivial
  | .fault _, _, _ => trivial
  | .choose _ _, h, h' => fun i => writeTree_and (h i) (h' i)
  | .load _ _ _ _, h, h' => fun v => writeTree_and (h v) (h' v)
  | .store _ _ _ _ _, h, h' => ⟨⟨h.1, h'.1⟩, fun b => writeTree_and (h.2 b) (h'.2 b)⟩
  | .rmw _ _ _ _ _, h, h' => ⟨fun o v hv => ⟨h.1 o v hv, h'.1 o v hv⟩, fun v => writeTree_and (h.2 v) (h'.2 v)⟩
  | .fence _ _, h, h' => fun u => writeTree_and (h u) (h' u)

/-- **`OwnUpd` with appended words** the write is not to. -/
theorem ownUpd_append {ow ow' x : List (Loc × Val)} {L₀ : Loc} {V : Val} (h : OwnUpd ow ow' L₀ V)
    (hx : ∀ w, (L₀, w) ∉ x) : OwnUpd (ow ++ x) (ow' ++ x) L₀ V := by
  intro L' w hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases h L' w hm with h1 | ⟨hne, hm'⟩
    · exact .inl h1
    · exact .inr ⟨hne, List.mem_append_left _ hm'⟩
  · exact .inr ⟨fun he => hx w (he ▸ hm), List.mem_append_right _ hm⟩

/-- **An `OwnTree` with words `x` appended**: `ownS` is `x` at every leaf,
the tree writes none of `x`'s words, and `x`'s locations are none of
`ow`'s. A lone store's take (`OwnTree`'s second case) becomes an `OwnUpd`
(its third case) of `ow ++ x`. -/
theorem ownTree_append {σ : Type} {own ownS : σ → List (Loc × Val)} {ow x : List (Loc × Val)} {t : EvTree σ}
    (h : OwnTree own ow t) (hx : ∀ s, TreeLeaf t s → ownS s = x)
    (hw : WriteTree (fun l _ => ∀ w, (l, w) ∉ x) t) (hd : ∀ l w w', (l, w) ∈ x → (l, w') ∉ ow) :
    OwnTree (fun s => own s ++ ownS s) (ow ++ x) t := by
  rcases h with ⟨hA, hW⟩ | ⟨rfl, kr, L₀, V, s', rfl, hb, hs⟩ | ⟨kr, L₀, V, s', rfl, hb, hs⟩ |
    ⟨k, nr, L₀, op, g, rfl, hb, ⟨v0, hv0⟩, hu⟩
  · refine .inl ⟨allInv_congr (fun s hs h => ?_) hA, writeTree_mono (fun l v ⟨h1, h2⟩ w hm => ?_)
      (writeTree_and hW hw)⟩
    · show own s ++ ownS s = ow ++ x
      rw [h, hx s hs]
    · rcases List.mem_append.mp hm with hm | hm
      · exact h1 w hm
      · exact h2 w hm
  · refine .inr (.inr (.inl ⟨kr, L₀, V, s', rfl, hb, ?_⟩))
    show OwnUpd ([] ++ x) (own s' ++ ownS s') L₀ V
    rw [hs, hx s' ⟨true, rfl⟩]
    refine ownUpd_append (ow := []) (fun L' w hm => ?_) hw.1
    exact .inl (by simpa using hm)
  · refine .inr (.inr (.inl ⟨kr, L₀, V, s', rfl, hb, ?_⟩))
    show OwnUpd (ow ++ x) (own s' ++ ownS s') L₀ V
    rw [hx s' ⟨true, rfl⟩]
    exact ownUpd_append hs hw.1
  · refine .inr (.inr (.inr ⟨k, nr, L₀, op, g, rfl, hb, ⟨v0, List.mem_append_left _ hv0⟩, fun v hv => ?_⟩))
    have hL : ∀ w, (L₀, w) ∉ x := fun w hm => hd L₀ w v0 hm hv0
    have hv' : (L₀, v) ∈ ow := by
      rcases List.mem_append.mp hv with hv | hv
      · exact hv
      · exact absurd hv (hL v)
    show OwnUpd (ow ++ x) (own (g v) ++ ownS (g v)) L₀ _
    rw [hx (g v) ⟨v, rfl⟩]
    exact ownUpd_append (hu v hv') hL

/-! ## The state facts with appended words -/

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {rS : Range} {Tk : State → Prop}
  {Dt : State → Prop}

/-- **The words `ownS` may append at `s`**: constant over its successors,
not written by its instruction, at locations none of `own`'s. -/
def AppOk (μ : Marks) (own ownS : Spike.Lib.X64Consumer.Own) (s : State) : Prop :=
  (∀ s', StSucc μ s s' → ownS s' = ownS s) ∧
    (abi.atSys s = false → ∀ tree, isa.exec s = some tree → WriteTree (fun l _ => ∀ w, (l, w) ∉ ownS s) tree) ∧
    ∀ l w w', (l, w) ∈ ownS s → (l, w') ∉ own s

/-- **The state facts with appended words.** -/
theorem _root_.Spike.Lib.X64ConsumerA.SFactsSt.appendS {ownS : Spike.Lib.X64Consumer.Own}
    (h : SFactsSt Λ μ own rS Tk s Dt)
    (ha : AppOk μ own ownS s) : SFactsSt Λ μ (fun s => own s ++ ownS s) rS Tk s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he =>
    ownTree_append (h.ownInstr hns tree he) (fun s' hl => ha.1 s' (.inl ⟨hns, tree, he, hl⟩)) (ha.2.1 hns tree he)
      ha.2.2
  ownSys := fun hsy call hd s' hs' => by
    show own s' ++ ownS s' = own s ++ ownS s
    rw [h.ownSys hsy call hd s' hs', ha.1 s' (.inr (.inl ⟨hsy, call, hd, hs'⟩))]
  ownTake := fun a' ha' hpc m => by
    show own _ ++ ownS _ = own s ++ ownS s
    rw [h.ownTake a' ha' hpc m, ha.1 (abi.skip (abi.setDmem s m)) (.inr (.inr ⟨a', ha', hpc, m, rfl⟩))]
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  wrTail := h.wrTail

/-- **A block's states with appended words**, `AppOk` itself a `BlkW`. -/
theorem _root_.Spike.Lib.X64.BlkW.appendS {ownS : Spike.Lib.X64Consumer.Own} {K : State → State → Prop}
    {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc R F n blk)
    (ha : BlkW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s _ => SFactsSt Λ μ (fun s => own s ++ ownS s) rS Tk s Dt) K exe endPc R F n blk := by
  intro s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  have h1 := h s σ c he hend hd hpc hA hF hJ k hk m hAm hD
  exact ⟨h1.1.appendS (ha s σ c he hend hd hpc hA hF hJ k hk m hAm hD).1, h1.2⟩

/-! ## `tcbM` off `ownG`'s words -/

/-- **`ownG`'s words** are the four counters and `a`. -/
theorem ownG_addr {l : Loc} {w : Val} (h : (l, w) ∈ ownG L a s) :
    l.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a] := by
  let Q : List (Loc × Val) → Prop := fun xs => ∀ p ∈ xs, p.1.addr ∈ [L.pnA, L.lockA, L.freeNA, L.nextA, a]
  have hV : ∀ pb pa xb xa nb na i, Q (ownV L a pb pa xb xa nb na i) := by
    intro _ _ _ _ _ _ _ p hm
    simp only [ownV, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp
  have hW : ∀ i, Q (ownW L a i) := fun i => by rw [ownW_eq]; exact hV _ _ _ _ _ _ _
  have hI : ∀ (c : Prop) [Decidable c] (x y : List (Loc × Val)), Q x → Q y → Q (if c then x else y) := by
    intro c _ x y hx hy; split <;> assumption
  have hG : Q (ownG L a s) := by
    have h2a : ∀ i, Q (own2a L a i) := fun _ => hV _ _ _ _ _ _ _
    have h2b : ∀ i, Q (own2b L a i) := fun _ => hV _ _ _ _ _ _ _
    exact hI _ _ _ (hI _ _ _ (h2a _) (hW _)) (hI _ _ _ (hI _ _ _ (h2b _) (hW _)) (hI _ _ _ (h2a _)
      (hI _ _ _ (h2b _) (hI _ _ _ (hI _ _ _ (h2a _) (hI _ _ _ (h2b _) (hW _))) (hW _)))))
  exact hG (l, w) h

/-- **`tcbM` is none of the counters** (`PhRec.TcbSep`, `j = 1`). -/
theorem tcbM_sep (hs : PhRec.TcbSep L) : tcbM L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA] :=
  hs 1 (by decide)

/-- **`ownS`'s words are off `ownG`'s**, `tcbM` off the counters and `a`. -/
theorem ownS_disj (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) :
    ∀ l w w', (l, w) ∈ ownS L s → (l, w') ∉ ownG L a s := by
  intro l w w' hm hg
  have h1 := ownG_addr hg
  unfold ownS at hm
  split at hm
  · obtain ⟨rfl, -⟩ := List.mem_singleton.mp hm
    have h2 := tcbM_sep hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 h2
    rcases h1 with h | h | h | h | h
    · exact h2 (.inl h)
    · exact h2 (.inr (.inl h))
    · exact h2 (.inr (.inr (.inl h)))
    · exact h2 (.inr (.inr (.inr h)))
    · exact ha h
  · simp at hm

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcbM_tcbOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbM_tcbOf

/-- info: 'Spike.Lib.X64.WakePh.ownS_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownS_congr

/-- info: 'Spike.Lib.X64.WakePh.ownGX_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownGX_W

/-- info: 'Spike.Lib.X64.WakePh.ownTree_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownTree_append

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt.appendS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt.appendS

/-- info: 'Spike.Lib.X64.BlkW.appendS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.BlkW.appendS

/-- info: 'Spike.Lib.X64.WakePh.ownS_disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownS_disj
