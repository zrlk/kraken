/-
**Concrete instance of `VecPublish.x64_publish_movdqa_verbatim`**: the `.kl`
runner's own configuration for `publish_movdqa.kl`.

- `codeMatches`: the `.kl`'s `code` block parses to `publishCodeV`.
- `runnerMatches`: the runner's prepared configuration
  (`Kraken.Litmus.X64.prepareProgram`) is `Config.init [pubW0, pubR1]
  pubInitMemV` in everything the theorem reads: both threads run
  `publishImageV` laid out by `pubLayoutV` (text at `0x100000`, one byte per
  instruction, `rec` at `0x1000000`), thread `0` from `writer` to `done`
  with `xmm0 = v1`, `xmm1 = v2`, thread `1` from `reader` to `done`, both
  with the runner's declarations `{⟨rec, 16⟩}` (`pubDeclsV`), registers and
  empty private memory; the initial memory is `⟨rec, 16⟩ = 0`.
- `x64_publish_movdqa_verbatim_concrete`: in every final configuration
  reachable from that configuration (any architecture), `1:xmm2` is `0`,
  `v1` or `v2`; `x64_publish_movdqa_verbatim_concrete_faultFree`: no
  reachable configuration has a faulting step. Every hypothesis by
  `decide`/`rfl`/`simp`.
-/
import Kraken.Promising.SLR.EnvG.X64VecPublish
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.Litmus.X64

namespace Kraken.Promising.X64.EnvG.VecPublish.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.VecPublish Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG

/-! ## The runner's layout and configuration -/

/-- The cell sizes of the runner's executable for `publish_movdqa.kl`:
labels 0, instructions 1 (text from `0x100000` to `0x100005`), then the
padding up to `rec` at `0x1000000`. -/
def pubSizesV : List Nat := [0, 1, 1, 1, 0, 1, 1, 0, 0x1000000 - 0x100005, 0]

/-- The runner's layout of the image. -/
@[reducible] def pubLayoutV : _root_.Layout :=
  { start := 0x100000, size := fun i => pubSizesV[i]?.getD 0 }

instance pubValidV : Executable.ValidLayout (pubLayoutV publishImageV) :=
  validLayout_of_cells _ (by decide) (by decide)

/-- The runner's declarations: `rec` is a 16-byte (`__int128`) location. -/
def pubDeclsV : Decls := { locs := [⟨0x1000000, 16⟩], unsizedDefault := false }

/-- A thread as the runner prepares it: the image, pc `pc`, end `done`
(`0x100005`), vector registers `zmms`, empty private memory, the runner's
declarations. -/
def pubThreadV (pc : Int64) (zmms : RegZmms) : X64.State where
  exe := pubLayoutV publishImageV
  endPc := 0x100000 + 5
  st := ({ ({} : MachineData) with zmms }, pc)
  decls := pubDeclsV

/-- The writer: from `writer` (`0x100000`), `xmm0 = v1`, `xmm1 = v2`. -/
def pubW0 : X64.State :=
  pubThreadV 0x100000 ((({} : MachineData).zmms.set512 .mm0 (pubV1.setWidth 512)).set512 .mm1 (pubV2.setWidth 512))

/-- The reader: from `reader` (`0x100003`). -/
def pubR1 : X64.State := pubThreadV (0x100000 + 3) ({} : MachineData).zmms

/-- The initial memory: `rec = 0` (16 bytes). -/
def pubInitMemV : List (Loc × Val) := [(⟨0x1000000, 16⟩, 0)]

/-! ## The `.kl` file -/

/-- The `.kl` source. -/
def pubKl : String := include_str "../../../Examples/LockFree/X64/publish_movdqa.kl"

/-- The `code` block of the `.kl` parses to `publishCodeV`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == publishCodeV
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches pubKl

/-- The runner's configuration: threads `pubW0` and `pubR1` (executable,
pc, end, registers, vector registers, private memory, declarations, no
promise) and the initial memory `pubInitMemV` with no message. -/
def runnerMatches (src : String) : Bool :=
  let same (t : Thread isa) (s : X64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.zmms == s.st.1.zmms && t.st.st.1.dmem == s.st.1.dmem &&
      t.st.decls == s.decls && t.prom.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.X64.prepareProgram with
  | .error _ => false
  | .ok pr => (match pr.config.threads.toList with
    | [t0, t1] => same t0 pubW0 && same t1 pubR1
    | _ => false) && pr.config.mem.init == pubInitMemV && pr.config.mem.msgs.isEmpty

/-- info: true -/
#guard_msgs in
#eval runnerMatches pubKl

/-! ## The instance -/

section
attribute [local instance] pubLayoutV

/-- A label's address from its position in the image. -/
theorem labP_at {x : Label} (i : Nat) (hd : publishImageV.drop i = Program.fromLabel publishImageV x := by decide)
    (hne : Program.fromLabel publishImageV x ≠ [] := by decide) :
    labP x = (pubLayoutV publishImageV).addrOf i :=
  Program.label_addrOf_drop publishImageV_wf.nodup hd hne

theorem symP_rec : symP "rec" = 0x1000000 := by
  show (labP "rec").toBitVec = _; rw [labP_at 9]; decide

theorem labP_done_v : labP "done" = 0x100000 + 5 := by rw [labP_at 7]; decide

theorem pubW0_start : PubStartW pubDeclsV pubW0 :=
  ⟨rfl, labP_done_v.symm, rfl, by show (0x100000 : Int64) = labP "writer"; rw [labP_at 0]; decide,
    by decide, by decide, Split.empty _⟩

theorem pubR1_start : PubStartR pubDeclsV pubR1 :=
  ⟨rfl, labP_done_v.symm, rfl, by show (0x100000 + 3 : Int64) = labP "reader"; rw [labP_at 4]; decide,
    Split.empty _⟩

theorem pubDeclsV_agrees : pubDeclsV.AgreesAt (symP "rec") 16 := by
  rw [symP_rec]; rfl

theorem pubRec_aligned : isAligned 16 (symP "rec") = true := by
  rw [symP_rec]; decide

theorem pubInit_threads {tid : Nat} {t : Thread isa}
    (ht : (Config.init [pubW0, pubR1] pubInitMemV : Config isa).threads[tid]? = some t) :
    [pubW0, pubR1][tid]? = some t.st := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
  obtain ⟨st, hst, rfl⟩ := ht
  exact hst

theorem pubInit_w (t : Thread isa)
    (ht : (Config.init [pubW0, pubR1] pubInitMemV : Config isa).threads[0]? = some t) :
    PubStartW pubDeclsV t.st := by
  have h := pubInit_threads ht
  simp only [List.getElem?_cons_zero] at h
  rw [← Option.some.inj h]; exact pubW0_start

theorem pubInit_r (tid : Nat) (t : Thread isa) (hne : tid ≠ 0)
    (ht : (Config.init [pubW0, pubR1] pubInitMemV : Config isa).threads[tid]? = some t) :
    PubStartR pubDeclsV t.st := by
  have h := pubInit_threads ht
  match tid, hne, h with
  | 1, _, h =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h
    rw [← Option.some.inj h]; exact pubR1_start
  | n + 2, _, h => simp at h

theorem pubInit_mem : ∀ p ∈ (Config.init [pubW0, pubR1] pubInitMemV : Config isa).mem.init,
    pubG (symP "rec") p.1 p.2 := by
  simp only [Config.init_mem, pubInitMemV, List.mem_singleton]
  rintro p rfl _
  exact .inl rfl

end

/-- **`publish_movdqa.kl` verbatim, in the runner's configuration**: in
every final configuration reachable from the runner's start (any
architecture), `1:xmm2` is `0`, `v1 = 0x10000000000000001` or
`v2 = 0x20000000000000002`: the record is never torn. -/
theorem x64_publish_movdqa_verbatim_concrete {A : Arch} {fuel : Nat} {c : Config isa}
    (hc : Reachable A fuel (Config.init [pubW0, pubR1] pubInitMemV) c) (hf : c.final = true) :
    ∀ t, c.threads[1]? = some t → PubVal (t.st.st.1.zmms.get (.xmm .mm2)) :=
  x64_publish_movdqa_verbatim (layout := pubLayoutV) pubRec_aligned (ds := fun _ => pubDeclsV)
    (fun _ => pubDeclsV_agrees) rfl pubInit_mem pubInit_w pubInit_r hc hf

/-- **No reachable configuration of the runner's start has a faulting
step.** -/
theorem x64_publish_movdqa_verbatim_concrete_faultFree {A : Arch} {fuel : Nat} :
    Config.FaultFree A fuel (Config.init [pubW0, pubR1] pubInitMemV : Config isa) :=
  x64_publish_movdqa_verbatim_faultFree (layout := pubLayoutV) pubRec_aligned (ds := fun _ => pubDeclsV)
    (fun _ => pubDeclsV_agrees) rfl pubInit_mem pubInit_w pubInit_r

end Kraken.Promising.X64.EnvG.VecPublish.Concrete

#print axioms Kraken.Promising.X64.EnvG.VecPublish.Concrete.x64_publish_movdqa_verbatim_concrete
#print axioms Kraken.Promising.X64.EnvG.VecPublish.Concrete.x64_publish_movdqa_verbatim_concrete_faultFree
