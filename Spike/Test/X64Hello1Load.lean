/-
**`hello1.w`'s load facts on x86-64** (the premises of `correctKA` about
the canonical load of `hello1.w`'s text at its layout `hello1Λ`, given the
parse equations `hpa`, `hd`), for `hello1_correctKA`
(`Spike/Test/X64Hello1CorrectA.lean`):

- `hello1_clear`: the Linux entry state is clear of the layout;
  `hello1_loadEq`: the load is `loadProg`'s at `initOf`'s words
  (`load_of_parsed`, `loadParsed_of_loadOk` with `hello1Λ_load`, at the
  listing's label offsets);
  `hello1_hload` (`hload`), `hello1_init` (the load's initial words);
- `hello1_himg` (`himg`, at the code labels `codeLabel`: `hello1Λ_image`),
  `hello1_hss` (`hss`: no static label), `hello1_hfr0` (`hfr0`);
- the loaded thread at the code's start, phase `13` (`ph_threadAt`): not in
  the take's phase (`hello1_htk0`, for the producer's `Inst.Tk`), owning the four
  counters at `0` (`hello1_hown0`, for the producer's `Inst.own`), their
  initial values `0` by the runtime's `rtInitOk` (`hello1_rtInit`);
- the value invariant `FixG Fix m0` at the canonical load's memory `m0`
  (`hello1M0`): `hello1_hG0` (`hG0`, any `Fix`), `hello1_hGpl` (`hGpl`,
  every fixed word off the heap and `.data`).

**The parse equations stay hypotheses**: `cellsOf hello1Asm = some
hello1Cells` and `dataSections hello1Asm.text = some hello1Secs` run Kraken's
parser on the text, whose `String` operations do not reduce in the kernel
(even `"a\tb".splitOn "\t"` is stuck: `String` is byte-array backed, its
splitting well-founded), so `decide +kernel` cannot decide them at any
memory; they are checked by `#guard parsesTo` at elaboration, the trust boundary
`hello1_marks` already takes.
-/
import Spike.Lib.X64Hello1I
import Spike.Lib.AllocInv
import Scc.Cert.Rt.RtInitX64
import Scc.Sem.FixInv

namespace Spike.Test.X64Hello1Load

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer (T)
open SccCode (hello1Asm hello1Λ hello1Cells hello1Secs)

/-- The Linux entry state is clear of `hello1Λ`. -/
theorem hello1_clear : Entry.linux.clear hello1Λ = true := by decide +kernel

/-- **The canonical load of `hello1.w`**, given the parse. -/
theorem hello1_loadEq (hpa : cellsOf hello1Asm = some hello1Cells)
    (hd : dataSections hello1Asm.text = some hello1Secs) :
    T.load hello1Asm hello1Λ = some (loadProg (kernel 1) Entry.linux hello1Λ hello1Cells
      (loadSyms hello1Λ hello1Secs.rodata) (Scc.Cert.Rt.X64.initOf hello1Λ hello1Cells hello1Secs)) :=
  (load_of_parsed (kernel 1) Entry.linux hello1Λ hpa hd).trans
    (Scc.Cert.Link.X64.loadParsed_of_loadOk SccCode.hello1Λ_load hello1_clear)

/-- `hload`. -/
theorem hello1_hload (hpa : cellsOf hello1Asm = some hello1Cells)
    (hd : dataSections hello1Asm.text = some hello1Secs) : ∃ t0, T.load hello1Asm hello1Λ = some t0 :=
  ⟨_, hello1_loadEq hpa hd⟩

/-- **The load's memory**: `initOf`'s initial words, no message. -/
theorem hello1_init (hpa : cellsOf hello1Asm = some hello1Cells)
    (hd : dataSections hello1Asm.text = some hello1Secs) {t0 : T.M.Cfg} (h : T.load hello1Asm hello1Λ = some t0) :
    t0.1.mem.init = Scc.Cert.Rt.X64.initOf hello1Λ hello1Cells hello1Secs ∧ t0.1.mem.msgs = #[] := by
  rw [hello1_loadEq hpa hd] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- `himg`, at the code labels. -/
theorem hello1_himg : Scc.Cert.Link.imageOk hello1Λ hello1Secs (Scc.Sem.X64.codeLabel hello1Λ.code.lo hello1Cells) = true :=
  SccCode.hello1Λ_image

/-- `hss`: the static link places no label. -/
theorem hello1_hss {code : String → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {name : WeakMem.AllocLabel → String} : StaticSyms hello1Λ hello1Secs code lsize name :=
  .of_none fun _ => rfl

/-- `hfr0`: no label placed. -/
theorem hello1_hfr0 (base n : Nat) : Spike.Lib.AllocInv.FreshInv hello1Λ.static base n 0 0 :=
  Spike.Lib.AllocInv.FreshInv.init base n 0

/-! ## The loaded thread -/

open Spike.Lib.X64.Flow.Hello1.Inst (ph own ownOf Tk)

/-- The loaded thread. -/
noncomputable abbrev s0h : State := threadAt Entry.linux hello1Λ.code.lo hello1Cells (loadSyms hello1Λ hello1Secs.rodata)

/-- **The loaded thread's phase** is `13`: the counters' first phases and
before the take. -/
theorem ph_threadAt : ph (pcOf s0h) = 13 := by
  decide +kernel

/-- `htk0`, for the producer's `Inst.Tk`. -/
theorem hello1_htk0 : ¬ Tk s0h := by
  unfold Tk; rw [ph_threadAt]; decide

/-- **The runtime's words start at `0`** in `hello1.w`'s load. -/
theorem hello1_rtInit : Scc.Cert.Rt.X64.rtInitOk hello1Λ hello1Cells hello1Secs = true := by decide +kernel

/-- The runtime counters' addresses in `hello1.w`'s link. -/
theorem rtA_pn : Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_pinned_next" = 6291472#64 := by decide +kernel
theorem rtA_next : Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_next" = 6291488#64 := by decide +kernel
theorem rtA_lock : Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_lock" = 6291496#64 := by decide +kernel
theorem rtA_freeN : Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_free_n" = 6291504#64 := by decide +kernel

/-- The four counters are runtime words. -/
theorem counters_rt : ∀ a ∈ [6291472#64, 6291496#64, 6291504#64, 6291488#64],
    a ∈ Scc.Cert.Rt.X64.rtWords (Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_pinned")
      (Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_pinned_next")
      (Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_next")
      (Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_lock")
      (Scc.Cert.Rt.X64.rtA hello1Λ hello1Cells hello1Secs "scc_rt_stack_free_n") := by
  rw [rtA_pn, rtA_next, rtA_lock, rtA_freeN]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  unfold Scc.Cert.Rt.X64.rtWords
  rcases ha with rfl | rfl | rfl | rfl <;> simp

/-- `hown0`, for the producer's `Inst.own` (at any frames): the loaded
thread owns the four counters at `0`, their initial values. -/
theorem hello1_hown0 (hpa : cellsOf hello1Asm = some hello1Cells)
    (hd : dataSections hello1Asm.text = some hello1Secs) :
    ∀ t0, T.load hello1Asm hello1Λ = some t0 →
      Spike.Lib.Consumer1.OwnInit ((fun s (_ : List TermRun.Frame) => own s) s0h []) t0.1.mem := by
  intro t0 h L v hm
  have hz : ∀ a ∈ [6291472#64, 6291496#64, 6291504#64, 6291488#64], t0.1.mem.initVal ⟨a, 8⟩ = 0 :=
    fun a ha => Scc.Cert.Rt.X64.initVal_rt_of_rtInitOk hello1_rtInit (hello1_init hpa hd h).1 (counters_rt a ha)
  simp only [own, ph_threadAt, ownOf] at hm
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, (hz _ (by simp)).trans (by decide)⟩
  · exact ⟨rfl, (hz _ (by simp)).trans (by decide)⟩
  · exact ⟨rfl, (hz _ (by simp)).trans (by decide)⟩
  · exact ⟨rfl, (hz _ (by simp)).trans (by decide)⟩

/-! ## The value invariant -/

/-- **The canonical load's memory**: `initOf`'s words, no message. -/
noncomputable def hello1M0 : Memory := { init := Scc.Cert.Rt.X64.initOf hello1Λ hello1Cells hello1Secs, msgs := #[] }

/-- `hG0` for the fixed words `Fix` at the load's memory. -/
theorem hello1_hG0 (hpa : cellsOf hello1Asm = some hello1Cells)
    (hd : dataSections hello1Asm.text = some hello1Secs) (Fix : List (Nat × Val)) :
    ∀ t0, T.load hello1Asm hello1Λ = some t0 → MemInv (FixG Fix hello1M0) t0.1.mem := fun _ h =>
  memInv_fixG_load (hello1_init hpa hd h).1 (hello1_init hpa hd h).2

/-- `hGpl` for fixed words off the heap and `.data`, below `2^64`. -/
theorem hello1_hGpl {Fix : List (Nat × Val)} {m0 : Memory}
    (hFix : ∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a) :
    ∀ a v, hello1Λ.heap.contains a ∨ hello1Λ.data.contains a → FixG Fix m0 (wordLoc a) v := by
  intro a v ha a' w hm he
  exfalso
  obtain ⟨hlt, hh, hdt⟩ := hFix a' w hm
  have hw := SccCode.hello1Λ_wf.inSpace
  have hd' := hw _ (by simp [Layout.regions] : hello1Λ.data ∈ hello1Λ.regions)
  have hh' := hw _ (by simp [Layout.regions] : hello1Λ.heap ∈ hello1Λ.regions)
  simp only [Range.InSpace, Range.contains] at hd' hh' ha hh hdt
  have hb := congrArg (fun L : Loc => L.addr.toNat) he
  simp only [wordLoc, BitVec.toNat_ofNat] at hb
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt] at hb
  subst hb
  omega

end Spike.Test.X64Hello1Load
