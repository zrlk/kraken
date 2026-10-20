/-
**Message passing: the specification side**. What both MP routes (the old hand-proved rules
and `EnvG`) use about the start, the initial ghost and the end, without the
old rules' proofs (`MpWriter`/`MpReader`/`MpRule`, `MpPure`, `MpConcrete`):

- `MpPublic.StartW`/`StartR`, `ghostParams`, `ghostParams_mpLocs`,
  `StartW.frame`/`StartR.frame` (from `MpPublic`);
- `Mp.mpGhost` (+ `mpGhost_rel_Fl`/`_rel_ne`, `pend_mpGhost`),
  `writerFrac` (+ lemmas), `writerRes`, `readerRes`, `mpRes`,
  `total_mpInit(_q/_acq)`, `erase_mpInit` (from `MpInit`);
- `Mp.WorldR.mono` (from `MpRule`);
- `Mp.slot_of_seen` (from `MpReader`);
- `Mp.mp_final` (from `MpAdequacy`).
-/
import Kraken.Promising.SLR.MpInv
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.InitGhost
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.MpPublic

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Mp

section Start

variable [layout : _root_.Layout]

/-- The writer at its start, with flag address `f` and data address `d`: it
runs the laid-out `mpWriter` from its first instruction to the end of its
text, without declarations (so its accesses are the 4-byte words `⟨f, 4⟩`,
`⟨d, 4⟩`), with `X0 = f`, `X1 = d`, and neither word in its private data
memory. -/
structure StartW (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout mpWriter
  decls : s.decls = {}
  endPc : s.endPc = (layout mpWriter).addrOf 5
  pc : s.st.2 = (layout mpWriter).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

/-- The reader at its start (the label `spin`), as `StartW`. -/
structure StartR (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout mpReader
  decls : s.decls = {}
  endPc : s.endPc = (layout mpReader).addrOf 5
  pc : s.st.2 = (layout mpReader).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

/-- The parameters with the ghost token chosen. -/
def ghostParams (f d : BitVec 64) : Params where
  f := f
  d := d
  W := ⟨0, 5⟩

omit layout in
theorem ghostParams_mpLocs {f d : BitVec 64} (hfd : f ≠ d) : MpLocs (ghostParams f d) where
  fd := hfd
  wf h := by have := congrArg Loc.bytes h; simp [ghostParams] at this
  wd h := by have := congrArg Loc.bytes h; simp [ghostParams] at this

theorem StartW.frame {f d : BitVec 64} {s : State} (h : StartW f d s) :
    FrameW (ghostParams f d) s ∧ AtPos mpWriter s 0 :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.df, h.dd⟩, h.pc⟩

theorem StartR.frame {f d : BitVec 64} {s : State} (h : StartR f d s) :
    FrameR (ghostParams f d) s ∧ AtPos mpReader s 0 :=
  ⟨⟨h.exe, h.decls, h.endPc, h.x0, h.x1, h.df, h.dd⟩, h.pc⟩

end Start

end Kraken.Promising.SLR.MpPublic

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Spinlock

section Init

/-! ## The initial ghost and resources -/

/-- **The initial ghost of MP.** -/
def mpGhost (P : Params) : Ghost where
  rel x := if x = P.Fl then P.φ else Pred.emp
  acqTab := [P.φ]
  u := []
  relMsgs := []
  pend := []
  upd _ := []
  claims := []

theorem mpGhost_rel_Fl {P : Params} : (mpGhost P).rel P.Fl = P.φ := by simp [mpGhost]

theorem mpGhost_rel_ne {P : Params} {x : Loc} (h : x ≠ P.Fl) : (mpGhost P).rel x = Pred.emp := by
  simp [mpGhost, h]

theorem pend_mpGhost {P : Params} : ∀ ts, ts ∉ (mpGhost P).pend := fun _ h => by cases h

/-- The writer's initial fractions: all of `Dt`, `Fl` and `W`. -/
def writerFrac (P : Params) (x : Loc) : Rat := if x = P.Dt ∨ x = P.Fl ∨ x = P.W then 1 else 0

theorem writerFrac_nonneg (P : Params) (x : Loc) : 0 ≤ writerFrac P x := by
  unfold writerFrac; split <;> decide

theorem writerFrac_le_one (P : Params) (x : Loc) : writerFrac P x ≤ 1 := by
  unfold writerFrac; split <;> decide

/-- The writer's initial resource. -/
def writerRes (m : Memory) (P : Params) : Res := Res.initOf m (writerFrac P) (writerFrac_nonneg P)

/-- The reader's initial resource: the acquire id `0` of `Fl`. -/
def readerRes (P : Params) : Res := ⟨fun _ => Perm.unit, fun x ι => if x = P.Fl ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: thread `0` the writer, thread `1` the
reader. -/
def mpRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then writerRes m P else if i = 1 then readerRes P else Res.unit

/-! ## Initial erasure -/

variable {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- The initial total: the writer's and the reader's resources. -/
theorem total_mpInit (P : Params) (m : Memory) :
    total (mpRes m P) (mpGhost P) (Config.init [sW, sR] initMem) = (writerRes m P).op (readerRes P) := by
  simp only [total, Config.init_size, threadsRes, Ghost.slotsRes, mpGhost, List.map_nil, Res.prod_nil, Res.op_unit,
    List.length_cons, List.length_nil]
  show Res.prod [mpRes m P 0, mpRes m P 1] = _
  simp [mpRes, Res.op_unit]

theorem total_mpInit_q (P : Params) (m : Memory) (x : Loc) :
    ((total (mpRes m P) (mpGhost P) (Config.init [sW, sR] initMem)).wr x).q = writerFrac P x := by
  rw [total_mpInit]
  show writerFrac P x + 0 = _
  exact Rat.add_zero _

theorem total_mpInit_acq (P : Params) (m : Memory) (x : Loc) (ι : PredId) :
    (total (mpRes m P) (mpGhost P) (Config.init [sW, sR] initMem)).acq x ι = if x = P.Fl ∧ ι = 0 then 1 else 0 := by
  rw [total_mpInit]
  show 0 + _ = _
  exact Nat.zero_add _

/-- **Initial erasure of MP** (initial flag value `0`). -/
theorem erase_mpInit (P : Params) (T : Nat → Prop)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal P.Fl = 0) :
    Erase (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P) T (Config.init [sW, sR] initMem) := by
  have hq := total_mpInit_q (sW := sW) (sR := sR) (initMem := initMem) P (Config.init [sW, sR] initMem).mem
  have ha := total_mpInit_acq (sW := sW) (sR := sR) (initMem := initMem) P (Config.init [sW, sR] initMem).mem
  have hids : ∀ x, (mpGhost P).acqIds
      (total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P) (Config.init [sW, sR] initMem)).acq x =
        if x = P.Fl then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (mpGhost P).acqTab.length = 1 from rfl, List.range_one]
    by_cases hx : x = P.Fl <;> simp [hx, ha]
  have hA : ∀ x ι, 1 ≤ (total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P)
      (Config.init [sW, sR] initMem)).acq x ι → ι < [P.φ].length := by
    intro x ι h
    rw [ha] at h
    split at h
    · next he => rw [he.2]; exact Nat.zero_lt_one
    · exact absurd h (by decide)
  have hR : ∀ x v m V r, ((mpGhost P).rel x).P v m V r → Pred.SepList ((mpGhost P).acqPreds
      (total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P) (Config.init [sW, sR] initMem)).acq x ++
      (mpGhost P).updPreds x) v m V r := by
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    simp only [Ghost.updPreds, mpGhost, List.map_nil, List.append_nil]
    by_cases hx : x = P.Fl
    · subst hx
      rw [mpGhost_rel_Fl] at h
      simp only [↓reduceIte, List.map_cons, List.map_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · rw [mpGhost_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil]
      exact h
  have hWr : ∀ x, 0 < ((total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P)
      (Config.init [sW, sR] initMem)).wr x).q → ∀ p, ((total (mpRes (Config.init [sW, sR] initMem).mem P)
        (mpGhost P) (Config.init [sW, sR] initMem)).wr x).X p ↔
          p = ((Config.init [sW, sR] initMem).mem.initVal x, 0) := by
    intro x hpos p
    rw [total_mpInit] at hpos ⊢
    show (0 < writerFrac P x ∧ p = _) ∨ False ↔ _
    have : 0 < writerFrac P x := by
      have h2 : ((writerRes (Config.init [sW, sR] initMem).mem P).op (readerRes P)).wr x =
        ((writerRes (Config.init [sW, sR] initMem).mem P).wr x).op Perm.unit := rfl
      rw [h2, Perm.op_unit] at hpos
      exact hpos
    simp [this]
  have hP : ∀ x, Pred.Pure ((mpGhost P).rel x) ((Config.init [sW, sR] initMem).mem.initVal x) := by
    intro x
    by_cases hx : x = P.Fl
    · subst hx
      rw [mpGhost_rel_Fl, hF0]
      exact flagPred_pure (by decide)
    · rw [mpGhost_rel_ne hx]; exact Pred.emp_pure _
  have hV : (total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhost P)
      (Config.init [sW, sR] initMem)).valid :=
    ⟨fun x => by rw [hq]; exact writerFrac_le_one P x, fun x ι => by rw [ha]; split <;> decide⟩
  -- `mpGhost P` is `initGhost` with no release-mode location
  exact erase_initGhost (rel := (mpGhost P).rel) (acqTab := [P.φ]) (rls := []) T List.nodup_nil hV hA hR hWr
    (fun x _ => hP x) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)

end Init

/-! ## The reader's world along `Ghost.Le` -/

theorem WorldR.mono {P : Params} {r : Res} {g g₁ : Ghost} (h : WorldR P r g) (hle : g.Le g₁) : WorldR P r g₁ := by
  obtain ⟨hF, ι, hι, hφ, hacq⟩ := h
  refine ⟨by rw [hle.rel]; exact hF, ι, Nat.lt_of_lt_of_le hι hle.acqTab.length_le, ?_, hacq⟩
  rw [← hφ]
  exact Ghost.acqPred_of_prefix hle.acqTab hι

/-! ## Acquire ids and acquirable slots -/

section Slot

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **The slot of a seen flag message**: if the total holds the acquire id
`ι` of `Fl` (predicate `φ`), a flag message with a non-zero low word carries
a slot for `ι` satisfying `Good` at the message's timestamp. -/
theorem slot_of_seen {P : Params} (E : Erase rF g T c) (hrel : g.rel P.Fl = P.φ) {ι : PredId}
    (hι : g.acqPred ι = P.φ) (hacq : (total rF g c).acq P.Fl ι = 1) {ts : Time} {v : Val}
    (hrd : c.mem.read? P.Fl ts = some v) (hv : BitVec.setWidth 32 v ≠ 0) :
    ∃ s ∈ g.u, s.key = (P.Fl, ts) ∧ s.id = ι ∧ Good P.Dt ts s.res := by
  have hrm : (P.Fl, ts) ∈ g.relMsgs := Classical.byContradiction fun hn => by
    have := E.pure P.Fl ts v hrd hn
    rw [hrel] at this
    exact flagPred_impure hv this
  obtain ⟨s, hs, hkey, hid⟩ := (E.slotsDom (P.Fl, ts) ι).mpr ⟨hrm, .inl hacq⟩
  have hP := E.slotsPred s hs v (by rw [hkey]; exact hrd)
  rw [hid, hι, hkey] at hP
  exact ⟨s, hs, hkey, hid, hP hv⟩

end Slot

/-- **The final argument**: from erasure at a final configuration of two
threads whose final resources satisfy `MpPost P 1`. -/
theorem mp_final {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hrel : g.rel P.Fl = P.φ) (hB : ∀ tid, c.Done tid → MpPost P 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal P.Dt = 1#128 := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hR : ∃ j, j < c.threads.size ∧ ReaderDone P 1 c ∧
      ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = P.φ ∧ (rF j).acq P.Fl ι = 1 := by
    rcases hB 0 (Config.final_done hf h0) with hw0 | hr0
    · rcases hB 1 (Config.final_done hf h1) with hw1 | hr1
      · have := E.q_add_le_one h0 h1 (by decide) P.W
        exfalso
        grind
      · exact ⟨1, h1, hr1⟩
    · exact ⟨0, h0, hr0⟩
  obtain ⟨j, hj, ⟨hx4, ts, v, hrd, hv⟩, ι, -, hφ, hacq⟩ := hR
  have hacqT : (total rF g c).acq P.Fl ι = 1 := by
    have h1 := sub_acq_le (sub_total_thread (rF := rF) (g := g) hj) P.Fl ι
    have h2 := E.valid.2 P.Fl ι
    omega
  obtain ⟨s, hs, -, -, hq, ts', hX, hmax, -⟩ := slot_of_seen E hrel hφ hacqT hrd hv
  obtain ⟨hpos, hXT, hmaxT⟩ := total_max_of_slot E hs hq hX hmax
  exact ⟨hx4, E.finalVal_of_max hf hpos hXT hmaxT⟩

end Kraken.Promising.SLR.Mp
