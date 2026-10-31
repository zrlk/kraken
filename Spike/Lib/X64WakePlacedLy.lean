/-
**`wc_main`'s source placed past the box's store** (x86-64, the twin of
`Spike/Lib/A64WakePlacedLy.lean`; the `PlacedSE` half of `HMidP.wcWf`): at
every node of `WcMainW` from the reserve's call block to the clone's
`syscall`, main's source is placed (`PlacedSE`) under the labels
`upd (L0T Λ) l b` (`l` at `b`, main's id at `tcb0 Λ`), its words in main's
frame slots `-16` (the box's cell) and `-8` (main's `ThreadId`).

- `lbl_l`, `lbl_me`, `ne_of_fresh`: the labels at `l` and at main's id
  (`l ≠ mainTidLbl 2`).
- `boxPure_slots`: `BoxPure`'s facts this file takes.
- `keeps_main`: `wc_main`'s blocks past the box keep slots `-16`, `-8`.
- `MSrc`: main's source at the box (`boxTerm`, `o` at `l`) or published
  (`boxPubCtl c0 ty l`, `c` at `l`), `me` main's id;
  `placedSE_boxAt`, `placedSE_pubAt`, `placedSE_msrcAt`: placed at any two
  places.
- `blkW_slots`, `nodeW_slots`, `hs_of`: the generic block/node instance from
  a node invariant pinning `MSrc l` and the two slots' labels.
- `bl_placed` (at `rN … (QB l b) .bl`), `mid_placed` (`.x19` to the clone's
  `syscall` at every ghost with `MidPG (QB l b) c0 ty l' cA` and
  `FrMG J0 fr m`), `sp3_placed` (`.x19`'s block at `MidG`);
  `wcMainW_placed`: as `WcMainW … J0 (QB l b)` (`HMidP.wcWf`'s shape).
- `placed_at_box`: non-vacuity at `h0`'s `Box` (its ghosts meet `BoxPure`;
  the box's own state placed).

**Unlike AArch64**: main's slots are `-16`, `-8` (A64 `-72`, `-80`); the
source is not at `SpawnSrc` past the box but at `boxTerm` up to the
`mfence` and at `boxPubCtl c0 ty l` past it (the publication inside the
segment, `X64WakeWcPub`), so the placements are `placedSE_boxAt` (`o`,
`me`) and `placedSE_pubAt` (`c`, `me`) through `MSrc` (A64:
`placedSE_spawnAt` throughout); there is no fence node `f` and no `SB`
(x86-64's `WcMainW` has `bl`, `sp3`, `pre`'s four and `clone`'s six nodes;
the reserve's call block carries `QB` itself); `wcJF`'s saved `%rdi` (main's
word, `BoxPure`'s) is at `-8`. No absolute address appears in this file.
-/
import Spike.Lib.X64WakeHMid
import Spike.Lib.X64WakeSrcCtl

namespace Spike.Lib.X64.WakePh.PlacedLy

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (rN bX MidG MidPG FrG FrMG resB aN j3 WcMainW WcSp4PreW WcClonePW t2 kOf)
open Spike.Lib.X64.WakePh.WcSp4 (wcNI x20A initCall)
open Spike.Lib.X64.WakePh.WcClone (oW FrW wcN21 wcNf wcNa wcNd wcN10 wcNr x21A cloneLd nrB)
open Spike.Lib.X64.WakePh.Tcb2Call (wcN3 tcb2Call)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64WakeLoadT (L0T tcb0)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Spike.Lib.X64.WakeHMid (BoxPure QB)
open Spike.Lib.X64.WakeSrcCtl (keepsSlot arun_slot_keep placeVal_slot_abs placedSE_of_tbl rep_at)

/-- The labels past the box: `l` at `b` over the start's (`L0T`). -/
abbrev lblL (Λ : Scc.Sem.Layout) (l : WeakMem.AllocLabel) (b : Nat) : Lbl := X64ConsumerA.upd (L0T Λ) l b

theorem lbl_l (Λ : Scc.Sem.Layout) (l : WeakMem.AllocLabel) (b : Nat) : lblL Λ l b l = some b := by
  simp [X64ConsumerA.upd]

theorem lbl_me {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} (b : Nat) (hl : l ≠ mainTidLbl 2) :
    lblL Λ l b (mainTidLbl 2) = some (tcb0 Λ) := by
  simp [X64ConsumerA.upd, Ne.symm hl, L0T]

/-- A label fresh at the start (`h1`'s `hl`) is not main's id. -/
theorem ne_of_fresh {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} (hl : L0T Λ l = none) : l ≠ mainTidLbl 2 := by
  rintro rfl; simp [L0T, X64ConsumerA.upd] at hl

/-- **`BoxPure`'s facts this file takes**: main's slots in `R`, `J0`'s
`%rdi` main's id. -/
theorem boxPure_slots {L : Spike.Lib.X64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64} (h : BoxPure L F0 n R F J0 t) :
    R.Off (-16) ∧ R.Off (-8) ∧ ∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 L.Λ := by
  obtain ⟨⟨-, -, -, hlo, hhi⟩, -, -, ⟨-, hdi, -⟩, -⟩ := h
  exact ⟨⟨by decide, by omega, by omega⟩, ⟨by decide, by omega, by omega⟩, hdi⟩

/-- `wc_main`'s blocks past the box keep main's slots `-16`, `-8`. -/
theorem keeps_main : ∀ blk ∈ [resB, tcb2Call, x20A, initCall, x21A, cloneLd, nrB],
    keepsSlot (-16) oW blk = true ∧ keepsSlot (-8) oW blk = true := by
  decide +kernel

/-! ## main's source past the box -/

/-- **main's source past the box's store** at `l`: at `boxTerm` with `o`
bound to `l`'s owned locative, or published (`boxPubCtl c0 ty l`); `me`
main's id. -/
def MSrc (l : WeakMem.AllocLabel) (c : Ctl) : Prop :=
  (c.term = boxTerm ∧ (∃ ty, TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])) ∨
  ∃ c0 ty, c = boxPubCtl c0 ty l ∧
    TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])

/-- **main's source at the box placed at any two places**: `o` at `po`,
`me` at `pm`, given `lbl` puts `l` at `po`'s word and main's id at `pm`'s. -/
theorem placedSE_boxAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel} {ty : Ty}
    (po pm : Place (machine (kernel 1)).I.RegId) (ht : c.term = boxTerm)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (h1 : ∃ v, placeVal (machine (kernel 1)) s po = some v ∧ lbl l = some v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  simp only [TermRun.evalAt] at ho hme
  refine placedSE_of_tbl [("o", [.one po]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty' ws hl
    rw [ht, show exprFv boxTerm = ["o", "me"] by decide] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [ho] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hme] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty' ws hpl hl k wp wd hwp hwd
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [ho] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h1
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hme] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h2
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn'
    by_cases eo : x = "o"
    · subst eo; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne eo, beq_false_of_ne em] at hpl

/-- **main's source published placed at any two places**: at
`boxPubCtl c0 ty l`, `c` at `pc`, `me` at `pm`. -/
theorem placedSE_pubAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel}
    (pc pm : Place (machine (kernel 1)).I.RegId)
    (hme : TermRun.evalAt c0.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    (h1 : ∃ v, placeVal (machine (kernel 1)) s pc = some v ∧ lbl l = some v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s (boxPubCtl c0 ty l) [] := by
  have hc : TermRun.lookupE (boxPubCtl c0 ty l).env "c" = some (.ptr .pub ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp [boxPubCtl, TermRun.lookupE]
  have hm : TermRun.lookupE (boxPubCtl c0 ty l).env "me" = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) := by
    simpa [boxPubCtl, TermRun.evalAt, TermRun.lookupE] using hme
  refine placedSE_of_tbl [("c", [.one pc]), ("me", [.one pm])] ?_ ?_ ?_
  · intro x hx ty' ws hl
    have hfv : ∀ y ∈ exprFv (boxPubCtl c0 ty l).term, y = "c" ∨ y = "me" := by
      show ∀ y ∈ exprFv (CoreTerm.Expr.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.X64WakeSrcDefs.spawnTerm), _
      decide
    rcases hfv x hx with rfl | rfl
    · rw [hc] at hl; cases hl; exact ⟨_, rfl, by simp⟩
    · rw [hm] at hl; cases hl; exact ⟨_, rfl, by simp⟩
  · intro x pls ty' ws hpl hl k wp wd hwp hwd
    by_cases ec : x = "c"
    · subst ec; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      rw [hc] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h1
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      rw [hm] at hl; cases hl
      match k, hwp, hwd with | 0, hwp, hwd => cases hwp; cases hwd; exact rep_at h2
    · simp [List.lookup, beq_false_of_ne ec, beq_false_of_ne em] at hpl
  · intro x pls k n hpl hn'
    by_cases ec : x = "c"
    · subst ec; simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    by_cases em : x = "me"
    · subst em; simp [List.lookup] at hpl; subst hpl
      match k, hn' with | 0, hn' => cases hn'
    · simp [List.lookup, beq_false_of_ne ec, beq_false_of_ne em] at hpl

/-- **main's source past the box placed at any two places** (`MSrc`). -/
theorem placedSE_msrcAt {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {l : WeakMem.AllocLabel}
    (po pm : Place (machine (kernel 1)).I.RegId) (hsrc : MSrc l c)
    (h1 : ∃ v, placeVal (machine (kernel 1)) s po = some v ∧ lbl l = some v)
    (h2 : ∃ v, placeVal (machine (kernel 1)) s pm = some v ∧ lbl (mainTidLbl 2) = some v) :
    PlacedSE Λ lbl s c [] := by
  rcases hsrc with ⟨ht, ⟨_, ho⟩, hme⟩ | ⟨c0, ty, rfl, hme⟩
  · exact placedSE_boxAt po pm ht ho hme h1 h2
  · exact placedSE_pubAt po pm hme h1 h2

/-! ## The generic node instances -/

section Gen

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {l : WeakMem.AllocLabel} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {n : ND}

set_option hygiene false in
/-- A node invariant pinning the source at `MSrc l` and main's slots'
labels. -/
local notation "HS" => ∀ σ c, n.J σ c → MSrc l c ∧ lbl l = some (σ.slot (-16)).toNat ∧
  lbl (mainTidLbl 2) = some (σ.slot (-8)).toNat

/-- **Placed on a block keeping main's slots**. -/
theorem blkW_slots {blk : List (Directive × Nat)} (h16 : R.Off (-16)) (h8 : R.Off (-8)) (hJ : HS)
    (hk : keepsSlot (-16) n.o blk = true ∧ keepsSlot (-8) n.o blk = true) :
    BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hj k _ m hA _
  obtain ⟨hsrc, h1, h2⟩ := hJ σ c hj
  refine ⟨placedSE_msrcAt (.slot (R.addr (-16)).toNat) (.slot (R.addr (-8)).toNat) hsrc
    ⟨_, placeVal_slot_abs hA h16, ?_⟩ ⟨_, placeVal_slot_abs hA h8, ?_⟩, fun _ h => h⟩
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.1]; exact h1
  · rw [arun_slot_keep _ _ blk ⟨n.pc, n.o, σ⟩ k hk.2]; exact h2

/-- **Placed at a node**. -/
theorem nodeW_slots (h16 : R.Off (-16)) (h8 : R.Off (-8)) (hJ : HS) :
    NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, hA, -, hj⟩
  obtain ⟨hsrc, h1, h2⟩ := hJ σ c hj
  exact ⟨placedSE_msrcAt _ _ hsrc ⟨_, placeVal_slot_abs hA h16, h1⟩ ⟨_, placeVal_slot_abs hA h8, h2⟩,
    fun _ h => h⟩

/-- `HS` from the frame's words (`-16` the cell `cA`, `-8` main's word `m`)
at one source control `cX`. -/
theorem hs_of {cX : Ctl} {cA m : BitVec 64}
    (hmid : MSrc l cX ∧ lbl l = some cA.toNat ∧ lbl (mainTidLbl 2) = some m.toNat)
    (hJF : ∀ σ c, n.J σ c → c = cX ∧ σ.slot (-16) = cA ∧ σ.slot (-8) = m) : HS := by
  intro σ c hj
  obtain ⟨rfl, h1, h2⟩ := hJF σ c hj
  exact ⟨hmid.1, by rw [h1]; exact hmid.2.1, by rw [h2]; exact hmid.2.2⟩

end Gen

/-! ## `wc_main`'s nodes -/

section Ly

variable {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {lab : Label → Int64} {J0 : AS → Ctl → Prop}
  (h16 : R.Off (-16)) (h8 : R.Off (-8)) (hl : l ≠ mainTidLbl 2)
  (hJ0 : ∀ σe c, J0 σe c → σe.regs.rdi.toNat = tcb0 Λ)
include h16 h8 hl hJ0

/-- **Placed on the reserve's call block** (`rN`'s `.bl`, the box's facts
`QB l b`): `o` at slot `-16` (`bX`'s cell `b`), `me` at slot `-8` (`wcJF`'s
saved `%rdi`). -/
theorem bl_placed : BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F
    (rN ms lab R J0 (QB l b) .bl) resB :=
  blkW_slots (l := l) h16 h8
    (by
      rintro σ c ⟨⟨l', A, ⟨q, ⟨σe, hj, -, -, h8'⟩, hA16, -⟩, e1, e2, ht, -, ho, hme⟩, -⟩
      subst e1 e2
      exact ⟨.inl ⟨ht, ⟨_, ho⟩, hme⟩, by rw [lbl_l, hA16],
        by rw [lbl_me _ hl, h8']; exact congrArg some (hJ0 σe _ hj).symm⟩)
    (keeps_main resB (by simp))

omit h16 h8 in
/-- `MSrc` and the labels at a ghost of the strengthened guard
(`MidPG (QB l b) c0 ty l' cA`, `FrMG J0 fr m`). -/
theorem msrc_of {c0 : Ctl} {ty : Ty} {l' : WeakMem.AllocLabel} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hG : MidPG (QB l b) c0 ty l' cA) (hM : FrMG J0 fr m) :
    l' = l ∧ MSrc l c0 ∧ (∀ c, c = boxPubCtl c0 ty l' → MSrc l c) ∧ lblL Λ l b l = some cA.toNat ∧
      lblL Λ l b (mainTidLbl 2) = some m.toNat := by
  obtain ⟨⟨e1, e2, ht, -, ho, hme⟩, -, -, -⟩ := hG
  subst e1
  obtain ⟨σe, c, hj, -, rfl⟩ := hM
  exact ⟨rfl, .inl ⟨ht, ⟨_, ho⟩, hme⟩, fun c e => .inr ⟨c0, ty, e, hme⟩, by rw [lbl_l, e2],
    by rw [lbl_me _ hl]; exact congrArg some (hJ0 σe c hj).symm⟩

/-- **Placed on `.x19`'s block** at a ghost with `MidG (QB l b) c0 cA` and
`FrMG J0 fr m` (any `F`). -/
theorem sp3_placed {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hG : MidG (QB l b) c0 cA) (hM : FrMG J0 fr m) :
    BlkW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F
      (wcN3 lab (j3 cA m fr) c0) tcb2Call := by
  have hmid : MSrc l c0 ∧ lblL Λ l b l = some cA.toNat ∧ lblL Λ l b (mainTidLbl 2) = some m.toNat := by
    obtain ⟨l', A, ⟨e1, e2, ht, -, ho, hme⟩, hA⟩ := hG
    subst e1 e2
    obtain ⟨σe, c, hj, -, rfl⟩ := hM
    exact ⟨.inl ⟨ht, ⟨_, ho⟩, hme⟩, by rw [lbl_l, hA],
      by rw [lbl_me _ hl]; exact congrArg some (hJ0 σe c hj).symm⟩
  exact blkW_slots h16 h8 (hs_of hmid fun _ _ h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩) (keeps_main _ (by simp))

/-- **Placed from `.x20` to the clone's `syscall`** at a ghost with the
strengthened guard (`MidPG (QB l b) c0 ty l' cA`, `FrMG J0 fr m`): `WcSp4PreW`'s
four nodes and `WcClonePW`'s six (any `F`, so `F₂`'s too). -/
theorem mid_placed {c0 : Ctl} {ty : Ty} {l' : WeakMem.AllocLabel} {t k cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hG : MidPG (QB l b) c0 ty l' cA) (hM : FrMG J0 fr m) :
    WcSp4PreW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F c0 t cA m fr ∧
      WcClonePW (fun s c => PlacedSE Λ (lblL Λ l b) s c []) (fun _ _ => False) exe endPc R F c0 ty l' t k cA m fr := by
  obtain ⟨rfl, hs0, hsP, hlc, hlm⟩ := msrc_of hl hJ0 hG hM
  have hm0 := And.intro hs0 (And.intro hlc hlm)
  have hmP := And.intro (hsP _ rfl) (And.intro hlc hlm)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact blkW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1.1, h.1.2.2.1, h.1.2.2.2.1⟩) (keeps_main _ (by simp))
  · exact nodeW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1⟩)
  · exact blkW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩) (keeps_main _ (by simp))
  · exact nodeW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩)
  · exact blkW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩) (keeps_main _ (by simp))
  · exact nodeW_slots h16 h8 (hs_of hm0 fun _ _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩)
  · exact blkW_slots h16 h8 (hs_of hmP fun _ _ h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩) (keeps_main _ (by simp))
  · exact nodeW_slots h16 h8 (hs_of hmP fun _ _ h => ⟨h.1.1, h.1.2.2.2.1, h.1.2.2.2.2.1⟩)
  · exact nodeW_slots h16 h8 (hs_of hmP fun _ _ h => ⟨h.1.1.1, h.1.1.2.2.2.1, h.1.1.2.2.2.2.1⟩)
  · exact blkW_slots h16 h8 (hs_of hmP fun _ _ h => ⟨h.1.1.1, h.1.1.2.2.2.1, h.1.1.2.2.2.2.1⟩)
      (keeps_main _ (by simp))

end Ly

/-- **`WcMainW` placed** (the `PlacedSE` half of `HMidP.wcWf`): every node
at `Box`'s ghosts, `Q := QB l b`. -/
theorem wcMainW_placed {L : Spike.Lib.X64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
    {F F₂ : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64} {l : WeakMem.AllocLabel} {b : Nat}
    {exe : _root_.Executable} {endPc : Int64} {ms : MemSide isa}
    (hB : BoxPure L F0 n R F J0 t) (hl : L0T L.Λ l = none) :
    WcMainW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False) exe endPc R F F₂ ms J0
      (QB l b) := by
  obtain ⟨h16, h8, hJ0⟩ := boxPure_slots hB
  have hl' := ne_of_fresh hl
  exact ⟨bl_placed h16 h8 hl' hJ0, fun _ _ _ _ g => sp3_placed h16 h8 hl' hJ0 g.1 g.2.2,
    fun _ _ _ _ _ _ g => (mid_placed (k := 0#64) h16 h8 hl' hJ0 g.1 g.2.2).1,
    fun _ _ _ _ _ _ g => (mid_placed h16 h8 hl' hJ0 g.1 g.2.2).2⟩

/-- **Non-vacuity at the real box** (`h0`'s `Box` at wake.w's landing, `l`
fresh at the start, as `hB_box` takes it): `Box`'s ghosts meet `BoxPure`, so
`wcMainW_placed` applies there, and the box's own state is placed (`bX` at
`l`, `b` and `QB l b`'s facts: `o` at `-16`, `me` at `-8`). -/
theorem placed_at_box {L : Spike.Lib.X64.Rt.RuntimeLayout} {ms0 : MemSide isa} {F0 : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} (hBx : WakeWc.Box L ms0 F0 l b n s c)
    (hl : L0T L.Λ l = none) :
    PlacedSE L.Λ (lblL L.Λ l b) s c [] ∧ ∃ R F J0 t, BoxPure L F0 n R F J0 t ∧
      ∀ F₂ : MachineData → Prop, WcMainW (fun s c => PlacedSE L.Λ (lblL L.Λ l b) s c []) (fun _ _ => False)
        L.exe L.endPc R F F₂ ms0 J0 (QB l b) := by
  obtain ⟨R, F, J0, t, h1, h2, h3, h4, ⟨⟨-, -, -, -, σ, hA, -, q, ⟨σe, hj, -, -, h8'⟩, hA16, -⟩, -, ht⟩, hn1,
    ⟨htm, -, ho, hme⟩, -, h5⟩ := hBx
  have hB : BoxPure L F0 n R F J0 t := ⟨h1, h2, h3, h4, ht, hn1, h5⟩
  obtain ⟨h16, h8, hJ0⟩ := boxPure_slots hB
  refine ⟨placedSE_boxAt (.slot (R.addr (-16)).toNat) (.slot (R.addr (-8)).toNat) htm ho hme
    ⟨_, placeVal_slot_abs hA h16, by rw [lbl_l, hA16]⟩
    ⟨_, placeVal_slot_abs hA h8, by rw [lbl_me _ (ne_of_fresh hl), h8']; exact congrArg some (hJ0 σe _ hj).symm⟩,
    R, F, J0, t, hB, fun _ => wcMainW_placed hB hl⟩

end Spike.Lib.X64.WakePh.PlacedLy

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.keeps_main' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.keeps_main

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.placedSE_msrcAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.placedSE_msrcAt

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.bl_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.bl_placed

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.mid_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.mid_placed

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.wcMainW_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.wcMainW_placed

/-- info: 'Spike.Lib.X64.WakePh.PlacedLy.placed_at_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.PlacedLy.placed_at_box
