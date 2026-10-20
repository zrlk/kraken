/-
**Message passing on x64, the specification**: the x64 copy of MP's parameters, resource predicates, initial ghost and
resources, initial erasure and final argument (`SLR/MpInv.lean`,
`SLR/MpInit.lean`, `SLR/MpReader.lean`'s `slot_of_seen`,
`SLR/MpAdequacy.lean`'s `mp_final`). Those files import the AArch64 MP
programs and ISA, so they cannot serve an x64 proof; the content is
ISA-neutral except for `ReaderDone`/`MpPost` (the reader's result register)
and the ISA of `erase_mpInit`/`mp_final`.

Differences from the AArch64 MP:
- the data value is `42` (the x64 writer is `mov [d], 42; mov [f], 1`), in
  `Good` and `Own1`;
- the reader's result is the low word of `rbx` (`ReaderDone`).

Everything up to `ReaderDone` can be hoisted (with the data value
as a parameter) and shared with `SLR/MpInv.lean`.
-/
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.InitGhost
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.Theorem1Final
import Kraken.Promising.X64

namespace Kraken.Promising.X64.EnvG.Mp

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.Spinlock

/-! ## Parameters and predicates -/

/-- MP's parameters: the flag and data addresses (4-byte words) and the
writer's ghost token. -/
structure Params where
  f : BitVec 64
  d : BitVec 64
  W : Loc

namespace Params

/-- The flag word. -/
abbrev Fl (P : Params) : Loc := ⟨P.f, 4⟩

/-- The data word. -/
abbrev Dt (P : Params) : Loc := ⟨P.d, 4⟩

end Params

/-- The locations are distinct. -/
structure MpLocs (P : Params) : Prop where
  fd : P.f ≠ P.d
  wf : P.W ≠ P.Fl
  wd : P.W ≠ P.Dt

theorem MpLocs.fl_dt {P : Params} (h : MpLocs P) : P.Fl ≠ P.Dt := fun he => h.fd (congrArg Loc.addr he)

/-- The data value the writer publishes. -/
abbrev dataVal : Val := 42#128

/-- The published state: all of `Dt`, whose maximal write is `(42, ts)` with
`ts ≤ V`. -/
def Good (Dt : Loc) (V : View) (r : Res) : Prop :=
  (r.wr Dt).q = 1 ∧ ∃ ts, (r.wr Dt).X (dataVal, ts) ∧ (∀ p, (r.wr Dt).X p → p.2 ≤ ts) ∧ ts ≤ V

/-- **The flag's release and acquire predicate**: `Good` at a non-zero low
word (the reader tests the 32-bit value it loaded). -/
def flagPred (Dt : Loc) : Pred where
  P v _ V r := BitVec.setWidth 32 v ≠ 0 → Good Dt V r
  mono _ _ _ _ _ _ h := h

/-- The flag's predicate for these parameters. -/
abbrev Params.φ (P : Params) : Pred := flagPred P.Dt

theorem flagPred_pure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v = 0) : Pred.Pure (flagPred Dt) v :=
  fun _ _ h => absurd hv h

theorem flagPred_impure {Dt : Loc} {v : Val} (hv : BitVec.setWidth 32 v ≠ 0) : ¬ Pred.Pure (flagPred Dt) v :=
  fun h => by
    have := (h default 0 hv).1
    simp [Res.unit, Perm.unit] at this

/-- Before the data store: all of `Dt` (only the initial write), all of `W`,
a share of `Fl`. -/
def Own0 (P : Params) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ (∀ p, (r.wr P.Dt).X p → p.2 = 0) ∧ 1 ≤ (r.wr P.W).q ∧ 0 < (r.wr P.Fl).q

/-- After the data store: all of `Dt` with maximal write `(42, ts)`, `ts` at
or below `vwOld`, all of `W`, a share of `Fl`. -/
def Own1 (P : Params) (vs : Views) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ (∃ ts, (r.wr P.Dt).X (dataVal, ts) ∧ (∀ p, (r.wr P.Dt).X p → p.2 ≤ ts) ∧ ts ≤ vs.vwOld) ∧
    1 ≤ (r.wr P.W).q ∧ 0 < (r.wr P.Fl).q

/-- The writer's world facts: the flag's release predicate is `φ`, the
data's is pure. -/
def WorldW (P : Params) (g : Ghost) : Prop := g.rel P.Fl = P.φ ∧ ∀ v, Pred.Pure (g.rel P.Dt) v

/-- The reader's world facts: the flag's release predicate is `φ`, and the
reader holds an acquire id of `Fl` with predicate `φ`. -/
def WorldR (P : Params) (r : Res) (g : Ghost) : Prop :=
  g.rel P.Fl = P.φ ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = P.φ ∧ r.acq P.Fl ι = 1

/-! ### Generic over the flag predicate

The reader's side of MP (world facts, postcondition, final argument, and in
`X64MpSmoke`/`X64MpVCGen`/`X64MpLink` the VCs, the reader table and `hB`)
uses only two facts of the flag predicate, collected in `FlagLaw`: it is
impure at a non-zero low word, and it gives `Good` there. The `…G` names
below take the predicate `φ` and its `FlagLaw`; `flagPred` (here) and
`MpInc.flagPredI` (`X64MpIncSpec.lean`) are the instances, and the
`flagPred`/`flagPredI` copies are re-proved from them. -/

/-- **The laws of a flag predicate** used by the reader: impure at a
non-zero low word, and `Good` there. -/
structure FlagLaw (Dt : Loc) (φ : Pred) : Prop where
  impure : ∀ {v : Val}, BitVec.setWidth 32 v ≠ 0 → ¬ Pred.Pure φ v
  good : ∀ {v : Val} {m : Memory} {V : View} {r : Res}, BitVec.setWidth 32 v ≠ 0 → φ.P v m V r → Good Dt V r

theorem flagPred_law (Dt : Loc) : FlagLaw Dt (flagPred Dt) := ⟨flagPred_impure, fun hv h => h hv⟩

/-- The writer's world facts for the flag predicate `φ` (`WorldW` is the
instance at `P.φ`). -/
def WorldWG (P : Params) (φ : Pred) (g : Ghost) : Prop := g.rel P.Fl = φ ∧ ∀ v, Pred.Pure (g.rel P.Dt) v

/-- The reader's world facts for the flag predicate `φ` (`WorldR` is the
instance at `P.φ`). -/
def WorldRG (P : Params) (φ : Pred) (r : Res) (g : Ghost) : Prop :=
  g.rel P.Fl = φ ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φ ∧ r.acq P.Fl ι = 1

theorem WorldRG.mono {P : Params} {φ : Pred} {r : Res} {g g' : Ghost} (h : WorldRG P φ r g) (hle : g.Le g') :
    WorldRG P φ r g' := by
  obtain ⟨hF, ι, hι, hφ, hacq⟩ := h
  refine ⟨by rw [hle.rel]; exact hF, ι, Nat.lt_of_lt_of_le hι hle.acqTab.length_le, ?_, hacq⟩
  rw [← hφ]
  exact Ghost.acqPred_of_prefix hle.acqTab hι

theorem WorldR.mono {P : Params} {r : Res} {g g' : Ghost} (h : WorldR P r g) (hle : g.Le g') : WorldR P r g' :=
  WorldRG.mono (φ := P.φ) h hle

/-! ## The postcondition -/

/-- The reader `rd` has loaded `42` into `ebx`, and the memory has a flag
message with a non-zero low word. -/
def ReaderDone (P : Params) (rd : Nat) (c : Config isa) : Prop :=
  (∃ t, c.threads[rd]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
    ∃ ts v, c.mem.read? P.Fl ts = some v ∧ BitVec.setWidth 32 v ≠ 0

/-- **The shared postcondition** (`NPSafe`'s `B`): the writer's token, or the
reader's result with its acquire id. -/
def MpPost (P : Params) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    (ReaderDone P rd c ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = P.φ ∧ r.acq P.Fl ι = 1)

/-- The shared postcondition for the flag predicate `φ` (`MpPost` is the
instance at `P.φ`). -/
def MpPostG (P : Params) (φ : Pred) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    (ReaderDone P rd c ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φ ∧ r.acq P.Fl ι = 1)

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

section Init

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

/-! ## The final argument -/

section Slot

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **The slot of a seen flag message**, for any flag predicate `φ` with
`FlagLaw`: if the total holds the acquire id `ι` of `Fl` (predicate `φ`), a
flag message with a non-zero low word carries a slot for `ι` satisfying
`Good` at the message's timestamp. -/
theorem slot_of_seenG {P : Params} {φ : Pred} (hφ : FlagLaw P.Dt φ) (E : Erase rF g T c) (hrel : g.rel P.Fl = φ)
    {ι : PredId} (hι : g.acqPred ι = φ) (hacq : (total rF g c).acq P.Fl ι = 1) {ts : Time} {v : Val}
    (hrd : c.mem.read? P.Fl ts = some v) (hv : BitVec.setWidth 32 v ≠ 0) :
    ∃ s ∈ g.u, s.key = (P.Fl, ts) ∧ s.id = ι ∧ Good P.Dt ts s.res := by
  have hrm : (P.Fl, ts) ∈ g.relMsgs := Classical.byContradiction fun hn => by
    have := E.pure P.Fl ts v hrd hn
    rw [hrel] at this
    exact hφ.impure hv this
  obtain ⟨s, hs, hkey, hid⟩ := (E.slotsDom (P.Fl, ts) ι).mpr ⟨hrm, .inl hacq⟩
  have hP := E.slotsPred s hs v (by rw [hkey]; exact hrd)
  rw [hid, hι, hkey] at hP
  exact ⟨s, hs, hkey, hid, hφ.good hv hP⟩

/-- **The slot of a seen flag message**: if the total holds the acquire id
`ι` of `Fl` (predicate `φ`), a flag message with a non-zero low word carries
a slot for `ι` satisfying `Good` at the message's timestamp. -/
theorem slot_of_seen {P : Params} (E : Erase rF g T c) (hrel : g.rel P.Fl = P.φ) {ι : PredId}
    (hι : g.acqPred ι = P.φ) (hacq : (total rF g c).acq P.Fl ι = 1) {ts : Time} {v : Val}
    (hrd : c.mem.read? P.Fl ts = some v) (hv : BitVec.setWidth 32 v ≠ 0) :
    ∃ s ∈ g.u, s.key = (P.Fl, ts) ∧ s.id = ι ∧ Good P.Dt ts s.res :=
  slot_of_seenG (flagPred_law _) E hrel hι hacq hrd hv

end Slot

/-- **The final argument**, for any flag predicate `φ` with `FlagLaw`: from
erasure at a final configuration of two threads whose final resources
satisfy `MpPostG P φ 1`, the reader's `ebx` and the data word's final value
are `42`. -/
theorem mp_finalG {P : Params} {φ : Pred} (hφ : FlagLaw P.Dt φ) {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hrel : g.rel P.Fl = φ) (hB : ∀ tid, c.Done tid → MpPostG P φ 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal P.Dt = dataVal := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hR : ∃ j, j < c.threads.size ∧ ReaderDone P 1 c ∧
      ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φ ∧ (rF j).acq P.Fl ι = 1 := by
    rcases hB 0 (Config.final_done hf h0) with hw0 | hr0
    · rcases hB 1 (Config.final_done hf h1) with hw1 | hr1
      · have := E.q_add_le_one h0 h1 (by decide) P.W
        exfalso
        grind
      · exact ⟨1, h1, hr1⟩
    · exact ⟨0, h0, hr0⟩
  obtain ⟨j, hj, ⟨hx4, ts, v, hrd, hv⟩, ι, -, hφι, hacq⟩ := hR
  have hacqT : (total rF g c).acq P.Fl ι = 1 := by
    have h1 := sub_acq_le (sub_total_thread (rF := rF) (g := g) hj) P.Fl ι
    have h2 := E.valid.2 P.Fl ι
    omega
  obtain ⟨s, hs, -, -, hq, ts', hX, hmax, -⟩ := slot_of_seenG hφ E hrel hφι hacqT hrd hv
  obtain ⟨hpos, hXT, hmaxT⟩ := total_max_of_slot E hs hq hX hmax
  exact ⟨hx4, E.finalVal_of_max hf hpos hXT hmaxT⟩

/-- **The final argument**: from erasure at a final configuration of two
threads whose final resources satisfy `MpPost P 1`, the reader's `ebx` and
the data word's final value are `42`. -/
theorem mp_final {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hrel : g.rel P.Fl = P.φ) (hB : ∀ tid, c.Done tid → MpPost P 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal P.Dt = dataVal :=
  mp_finalG (flagPred_law _) E hf hsize hrel hB

end Kraken.Promising.X64.EnvG.Mp
