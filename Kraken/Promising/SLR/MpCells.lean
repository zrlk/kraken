/-
The plumbing of the MP proof (frames across a step, the invariants after a
step, the positions) and the cells that touch no resource: the writer's two
`mov`s, the reader's `cbz` and its acquire load `ldar` (a load keeps the
resource and the ghost state, `EvTree.eraseWPR_load`; the read value and the
raised read view are recorded in the reader's phase, `Seen`).
-/
import Kraken.Promising.SLR.MpInv
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

omit layout in
/-- The low word of a register set from a 32-bit load. -/
theorem low_setWidth_32 (v : Val) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 32 v := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The writer's plumbing -/

section WriterPlumbing

variable [hw : Executable.ValidLayout (layout mpWriter)]

omit hw in
/-- `FrameW` across a step that keeps `X0`, `X1` and the private memory. -/
theorem FrameW.goto {P : Params} {st : State} (h : FrameW P st) {m : MachineData} {pc : Int64}
    (h0 : m.regs.X0 = st.st.1.regs.X0) (h1 : m.regs.X1 = st.st.1.regs.X1) (hd : m.dmem = st.st.1.dmem) :
    FrameW P (MpTrees.goto st m pc) :=
  ⟨h.exe, h.decls, h.endPc, by simp [h0, h.x0], by simp [h1, h.x1], by simp [hd, h.df], by simp [hd, h.dd]⟩

/-- The writer's positions `< 4` are not the end. -/
theorem FrameW.at {P : Params} {st : State} (h : FrameW P st) {i : Nat} (hp : AtPos mpWriter st i) (hi : i < 4) :
    At mpWriter st i := by
  refine ⟨h.exe, h.decls, hp, ?_⟩
  rw [hp, h.endPc, w_addr_5]
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact Executable.addrOf_ne_of_valid (layout mpWriter) (k := i) (n := 4) hi
    (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [mpWriter]) (by
      intro l z
      rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [mpWriter])

/-- At the end the writer has halted. -/
theorem exec_end_w {P : Params} {st : State} (h : FrameW P st) (hp : AtPos mpWriter st 4) : isa.exec st = none := by
  show exec st = none
  have : st.st.2 = st.endPc := by rw [hp, h.endPc, w_addr_5]
  simp [exec, this]

/-- Position 3 has an address of its own among the writer's positions. -/
theorem atPosW_eq_3 {st : State} {i : Nat} (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)
    (h3 : AtPos mpWriter st 3) (h : AtPos mpWriter st i) : i = 3 := by
  have heq : (layout mpWriter).addrOf i = (layout mpWriter).addrOf 3 := h.symm.trans h3
  have hlt : ∀ k, k < 3 → (layout mpWriter).addrOf k ≠ (layout mpWriter).addrOf 3 := fun k hk =>
    Executable.addrOf_ne_of_valid (layout mpWriter) (k := k) (n := 3) hk
      (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [mpWriter]) (by
        intro l z
        rw [Layout.apply_snd, Layout.frag_getElem?]
        simp [mpWriter])
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact absurd heq (hlt 0 (by decide))
  · exact absurd heq (hlt 1 (by decide))
  · exact absurd heq (hlt 2 (by decide))
  · rfl
  · exact absurd heq.symm (Executable.addrOf_ne_of_valid (layout mpWriter) (k := 3) (n := 4) (by decide)
      (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [mpWriter]) (by
        intro l z
        rw [Layout.apply_snd, Layout.frag_getElem?]
        simp [mpWriter]))

end WriterPlumbing

omit layout in
/-- The positions of `PhaseW`. -/
theorem PhaseW.pos {P : Params} {i : Nat} {x2 x3 : BitVec 32} {vs : Views} {r : Res}
    (h : PhaseW P i x2 x3 vs r) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  revert h
  unfold PhaseW
  split <;> intro h <;> first | omega | exact h.elim

omit layout in
/-- `PhaseW` reads the views only through `vwOld`. -/
theorem PhaseW.congr_views {P : Params} {i : Nat} {x2 x3 : BitVec 32} {r : Res} {vs vs' : Views}
    (h : ({ vs' with vCAP := 0 } : Views) = { vs with vCAP := 0 }) :
    PhaseW P i x2 x3 vs' r = PhaseW P i x2 x3 vs r := by
  have h3 : vs'.vwOld = vs.vwOld := by simpa using congrArg Views.vwOld h
  unfold PhaseW Own1
  rw [h3]

/-- **`InvW` after a step of thread `tid`** with new memory `m`. -/
theorem invW_withThread {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} {m : Memory} (hW : WorldW P g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : FrameW P s) {i : Nat} (hp : AtPos mpWriter s i)
    (hph : PhaseW P i (BitVec.setWidth 32 s.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 s.st.1.regs.X3.toBitVec) t'.views r)
    (hpp : PrepaidProm P tid i t' m r) :
    InvW P tid cl (c.withThread tid t' m) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' m hn, ite_eq_left rfl], hst ▸ hF, i, hst ▸ hp,
    hst ▸ hph, hpp⟩

/-! ## The reader's plumbing -/

section ReaderPlumbing

variable [hr : Executable.ValidLayout (layout mpReader)]

omit hr in
/-- `FrameR` across a step that keeps `X0`, `X1` and the private memory. -/
theorem FrameR.goto {P : Params} {st : State} (h : FrameR P st) {m : MachineData} {pc : Int64}
    (h0 : m.regs.X0 = st.st.1.regs.X0) (h1 : m.regs.X1 = st.st.1.regs.X1) (hd : m.dmem = st.st.1.dmem) :
    FrameR P (MpTrees.goto st m pc) :=
  ⟨h.exe, h.decls, h.endPc, by simp [h0, h.x0], by simp [h1, h.x1], by simp [hd, h.df], by simp [hd, h.dd]⟩

/-- The reader's positions `< 4` are not the end. -/
theorem FrameR.at {P : Params} {st : State} (h : FrameR P st) {i : Nat} (hp : AtPos mpReader st i) (hi : i < 4) :
    At mpReader st i := by
  refine ⟨h.exe, h.decls, hp, ?_⟩
  rw [hp, h.endPc, r_addr_5]
  simp only [beq_eq_false_iff_ne, ne_eq]
  exact Executable.addrOf_ne_of_valid (layout mpReader) (k := i) (n := 4) hi
    (by rw [Layout.apply_snd, Layout.frag_getElem?]; simp [mpReader]) (by
      intro l z
      rw [Layout.apply_snd, Layout.frag_getElem?]
      simp [mpReader])

/-- At the end the reader has halted. -/
theorem exec_end_r {P : Params} {st : State} (h : FrameR P st) (hp : AtPos mpReader st 4) : isa.exec st = none := by
  show exec st = none
  have : st.st.2 = st.endPc := by rw [hp, h.endPc, r_addr_5]
  simp [exec, this]

/-- The start label `spin` (position 0) is the address of `ldar` (position 1). -/
theorem r_addr_1 : (layout mpReader).addrOf 1 = (layout mpReader).addrOf 0 :=
  addrOf_label (i := 0) (l := "spin") rfl

end ReaderPlumbing

omit layout in
/-- The positions of `PhaseR`. -/
theorem PhaseR.pos {P : Params} {cl : Prop} {i : Nat} {x3 x4 : BitVec 32} {m : Memory} {vs : Views}
    (h : PhaseR P cl i x3 x4 m vs) : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  revert h
  unfold PhaseR
  split <;> intro h <;> first | omega | exact h.elim

omit layout in
/-- `PhaseR` reads the views only through `vrNew` and the forwarding items. -/
theorem PhaseR.congr_views {P : Params} {cl : Prop} {i : Nat} {x3 x4 : BitVec 32} {m : Memory} {vs vs' : Views}
    (h : ({ vs' with vCAP := 0 } : Views) = { vs with vCAP := 0 }) :
    PhaseR P cl i x3 x4 m vs' = PhaseR P cl i x3 x4 m vs := by
  have h1 : vs'.vrNew = vs.vrNew := by simpa using congrArg Views.vrNew h
  have h5 : vs'.fwdb = vs.fwdb := by simpa using congrArg Views.fwdb h
  have h6 : FlFwd P vs' = FlFwd P vs := by simp only [FlFwd, Views.getFwd, h5]
  unfold PhaseR
  rw [h1, h6]

/-- **`InvR` after a step of thread `tid`** that leaves the memory alone. -/
theorem invR_withThread {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    {t t' : Thread isa} (hW : WorldR P r g) (ht : c.threads[tid]? = some t) {s : State}
    (hst : t'.st = s) (hF : FrameR P s) {i : Nat} (hp : AtPos mpReader s i)
    (hph : PhaseR P cl i (BitVec.setWidth 32 s.st.1.regs.X3.toBitVec)
      (BitVec.setWidth 32 s.st.1.regs.X4.toBitVec) c.mem t'.views) :
    InvR P tid cl (c.withThread tid t' c.mem) r g := by
  have hn := lt_size_of_get? ht
  exact ⟨hW, t', by rw [Config.withThread_get? c t' c.mem hn, ite_eq_left rfl], hst ▸ hF, i, hst ▸ hp,
    by simpa [Config.withThread] using hst ▸ hph⟩

/-! ## The writer's silent cells -/

/-- A writer cell proof in `ThreadRuleR.wp` form from a state with no own
pending promise (lifted to `ThreadRuleRX` by `mp_lift`). -/
def CellW (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl' : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), WorldW P g → c.threads[tid]? = some t → FrameW P t.st →
    AtPos mpWriter t.st i → PhaseW P i (BitVec.setWidth 32 t.st.st.1.regs.X2.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec) t.views r →
    isa.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t.prom, ts ∉ g.pend) →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvW P tid) cl' c tid r g t) r g (ctx₀ t tid c.mem)

section WriterSilent

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- `mov w2, #1` (position 0 → 1). -/
theorem wpW_mov2 {P : Params} {A : Arch} {tid : Nat} : CellW P A tid 0 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex _ _ _
  rw [exec_w_mov2 t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← PhaseW.congr_views hv] at hph
  refine invW_withThread (i := 1) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_ (fun h => absurd h (by decide))
  simp only [PhaseW] at hph ⊢
  exact ⟨hph, by simp [Reg64s.setXReg]⟩

/-- `mov w3, #1` (position 2 → 3). -/
theorem wpW_mov3 {P : Params} {A : Arch} {tid : Nat} : CellW P A tid 2 := by
  intro cl' c r g rF t tree hW ht hF hp hph hex _ _ _
  rw [exec_w_mov3 t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← PhaseW.congr_views hv] at hph
  refine invW_withThread (i := 3) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_ (fun _ h => absurd (hph.1.symm.trans h) (by decide))
  simp only [PhaseW] at hph ⊢
  exact ⟨.inl hph, by simp [Reg64s.setXReg]⟩

end WriterSilent

/-! ## The reader's cells without resources -/

/-- A reader cell proof (`ThreadRuleR.wp` with `InvR` unfolded). -/
def CellR (P : Params) (A : Arch) (tid : Nat) (i : Nat) : Prop :=
  ∀ {cl : Prop} {c : Config isa} {r : Res} {g : Ghost} (rF : Nat → Res) (t : Thread isa)
    (tree : EvTree isa.State), WorldR P r g → c.threads[tid]? = some t → FrameR P t.st →
    AtPos mpReader t.st i → PhaseR P cl i (BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec)
      (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec) c.mem t.views →
    isa.exec t.st = some tree →
    tree.EraseWPR A tid (instrViews t (isa.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvR P tid) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

section ReaderCells

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- `cbz w3, spin` (position 2 → 1 on a zero low word, → 3 otherwise). -/
theorem wpR_cbz {P : Params} {A : Arch} {tid : Nat} : CellR P A tid 2 := by
  intro cl c r g rF t tree hW ht hF hp hph hex
  rw [exec_r_cbz t.st (hF.at hp (by decide))] at hex
  cases hex
  refine WpPostR.silent fun t' hst _ hv => ?_
  rw [← PhaseR.congr_views hv] at hph
  have hF' := hF.goto (m := t.st.st.1) (pc := if BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec = 0#32 then
    (layout mpReader).addrOf 1 else (layout mpReader).addrOf 3) rfl rfl rfl
  by_cases hz : BitVec.setWidth 32 t.st.st.1.regs.X3.toBitVec = 0#32
  · refine invR_withThread (i := 1) hW ht hst hF' (by simp [AtPos, hz]) ?_
    simp only [PhaseR] at hph ⊢
    exact hph.1
  · refine invR_withThread (i := 3) hW ht hst hF' (by simp [AtPos, hz]) ?_
    simp only [PhaseR] at hph ⊢
    exact ⟨hph.1, hph.2 hz⟩

/-- `ldar w3, [x0]` (position 1 → 2): an acquire load, not forwarded
(`FlFwd`), so the read view rises to the message read; a non-zero low word
records the message (`Seen`). -/
theorem wpR_ldar {P : Params} {A : Arch} {tid : Nat} (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : CellR P A tid 1 := by
  intro cl c r g rF t tree hW ht hF hp hph hex
  rw [exec_r_ldar t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex
  cases hex
  simp only [PhaseR] at hph
  refine EvTree.eraseWPR_load fun x hx => ?_
  obtain ⟨hm, hpr⟩ := readSuccs_memProm A _ hx
  have hrv := SpinCommon.readSuccs_acq_le hx hA1 hA2 fun f hf _ => by rw [hph] at hf; cases hf
  obtain ⟨tr, val, rfl, -, hrd, -, -⟩ := (mem_readSuccs A).mp hx
  refine WpPostR.noWrite hm hpr fun t' hst _ hv => ?_
  refine invR_withThread (i := 2) hW ht hst (hF.goto (by simp [Reg64s.setXReg]) (by simp [Reg64s.setXReg]) rfl)
    rfl ?_
  simp only [PhaseR]
  have h5 : t'.views.fwdb = (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .acq false
      P.Fl false tr val).views.fwdb := by simpa using congrArg Views.fwdb hv
  have h1 : t'.views.vrNew = (readNext A (instrViews t (isa.deps t.st)) (ctx₀ t tid c.mem) .acq false
      P.Fl false tr val).views.vrNew := by simpa using congrArg Views.vrNew hv
  refine ⟨?_, fun hnz => ⟨tr, val, hrd, ?_, by rw [h1]; exact hrv.1⟩⟩
  · have he : t'.views.getFwd P.Fl = t.views.getFwd P.Fl := by
      simp only [Views.getFwd, h5]; rfl
    show t'.views.getFwd P.Fl = none
    rw [he]; exact hph
  · have : BitVec.setWidth 32 (t.st.st.1.regs.setXReg XReg.X3
        (BitVec.setWidth 64 (BitVec.setWidth 32 val))).X3.toBitVec = BitVec.setWidth 32 val := by
      simp only [Reg64s.setXReg]; exact low_setWidth_32 val
    rw [this] at hnz
    exact hnz

end ReaderCells

end Kraken.Promising.SLR.Mp
