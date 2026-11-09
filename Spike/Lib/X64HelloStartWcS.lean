/-
**hello.w on x86-64: the start's level with frames, `wc_rodata`'s allocation landing and the setup's call of
`rodata`** (the twin of `Spike/Lib/A64HelloStartWcS.lean`'s live part).

- `WSg`: the start's level with frames at an own map `own`, `HelloWf.WSHFg own` as a level with frames
  (`WSg own … s c fs = WSHFg own … fs s c` by `rfl`; the root takes `ownGHXW`).
- `xa_post`: the allocator's fresh-label landing `Ea` in its region is at `wc_rodata`'s `.x15` (`HelloRd.pN .s0`)
  under `scc_rt_main`'s frame, at any entry invariant `J0` of `wc_rodata` (`Hello1.hello1_main_xa_post` at hello's
  labels).
- `rdJH`, `rdJH_run`, `rdJH_back`: the source at `rodata`'s first allocation after the setup's call, its entry
  state kept (`HelloRdCf.setup_call_run`).

**Where this differs from AArch64** (forced by the x86-64 shape):
- `xa_post`'s landing is `wc_rodata`'s `.x15` (AArch64: `.L19_wc_rodata.sp0`). The allocator's return address is
  `rN .call`'s `slot (-48)`, which the call pushed (AArch64: `x30`). `HelloRd.rN` takes `wc_rodata`'s region
  (`mR R`, for `%rbp`), and `pN` has no fence node, so no `J5` (AArch64: `J5` after the fence). The call keeps
  `wc_rodata`'s frame outside the allocator's region up to `8` (`CKept (mR R) (-48) (-160) 8`; AArch64: `0`).
  `.x15`'s node knows `%rbp` at the saved `%rbp`, so `xa_post` asks it of `Jp` (`hbp`).
- `mNC` takes the region `R` (it records `%rbp = R.addr (-8)`), so `rdJH` takes it too.
- `hello_start_wc_segWS` and `hxa_of_post` are not twinned: they are dead in hello.
-/
import Spike.Lib.X64HelloAllocWSF
import Spike.Lib.X64HelloMainGlueS

namespace Spike.Lib.X64.HelloPh.StartWcS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.HelloWf (WSHFg)
open Spike.Lib.X64 (At enter leave CKept Abs)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mNC aR)
open Spike.Lib.X64.Flow.HelloRd (rN pN)
open Spike.Lib.X64.Alloc (Ea)
open Spike.Lib (Arena FragS FrameRun)
/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **The start's level with frames at an own map `own`**: `W0` at `own`, `PhRec.μ L`, the write abort phase and
hello's threads abort phase `AcH … pfxM`. The root takes it at `ownGHXW`. -/
abbrev WSg (own : State → List (Loc × Val)) (L : RuntimeLayout) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) : FragS isa :=
  fun s c fs => Spike.Lib.X64.WakeWf.W0 L.Λ (Spike.Lib.X64.PhRec.μ L) own ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab)
    Cl (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab Spike.Lib.X64.HelloPh.StartWf.pfxM) Ctx lbl lsize frM X0 s c fs

/-- `WSg own` is `WSHFg own` at the frames, by definition. -/
example (own : Spike.Lib.X64Consumer.Own) (L : RuntimeLayout) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) (s : State)
    (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) :
    WSg own L ar p Dt Cl Ctx lbl lsize frM X0 s c fs ↔ WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs s c :=
  Iff.rfl

/-! ## The allocator's fresh-label landing at any `wc_rodata` entry invariant -/

section Bridge

variable {ms : Spike.Lib.MemSide isa} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region}
  {F : MachineData → Prop}

/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.x15`** (`Hello1.hello1_main_xa_post` at any entry
invariant `J0` of `wc_rodata`, per caller's state `σC`): from the continuation `Ea` in the allocator's region,
under a frame condition `F'` the call hands it, the state is at `pN .s0` of an invariant `Jp` every landing's
state left to `wc_rodata` satisfies (`hJp`), whose `%rbp` is at the saved `%rbp` (`hbp`). -/
theorem xa_post {J0 J1 : FAS → FAS → Ctl → Prop} {Jp Jp' J1' J2 J2' J3 J4 : FAS → Ctl → Prop}
    {m0 : MachineData} {σC : FAS} {q : AG ms (_root_.Executable.labels exe).label} {F' : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b w : Nat}
    (hFF : ∀ m, F' m → mF R F m0 σC m)
    (hkeep : ∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label (mR R) (J0 σC) (J1 σC) .call).J σ c ∧
      (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 8 mC m)
    (hJp : ∀ σx σ c0 c, (Ea ms q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R) (J0 σC) (J1 σC) .call).J σ c0 →
      (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    (hbp : ∀ σ c, Jp σ c → σ.regs.get64 .rbp = (mR R).addr (-8))
    {s : State} {c : Ctl} (h : At exe endPc (aR (mR R)) F' (Ea ms q.1 l b w) s c) :
    At exe endPc (mR R) (mF R F m0 σC) (pN (_root_.Executable.labels exe).label Jp Jp' J1' J2 J2' J3 J4 .s0)
      s c := by
  have h' := Spike.Lib.X64.at_leave (R := mR R) (kb := -48) (lo' := -160) (hi' := 8)
    (P := fun σ => ∃ c0, (rN (_root_.Executable.labels exe).label (mR R) (J0 σC) (J1 σC) .call).J σ c0 ∧
      (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σ', hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  have h40 : At exe endPc (mR R) (mF R F m0 σC)
      ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x0", ⟨-40, []⟩, Jp⟩ s c := by
    refine ⟨he, hn, hdc, ?_, _, hA, hD, hJp σx σ' c0 c hJx h1 h2⟩
    rw [hpc]
    show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".Lwc_rodata.x0"
    rw [← h2.2.2.1]
    show Int64.ofBitVec (σ'.slot (-48 + 0)) = _
    rw [show (-48 : Int) + 0 = -48 by decide, h1.2.2.2.2.2, Spike.Lib.int64_ofBitVec_toBitVec]
  exact Spike.Lib.X64.Flow.Hello1.At.rbp_addr h40 hbp

end Bridge

/-! ## The source after the setup's call of `rodata` -/

/-- **The source at `rodata`'s first allocation after the setup's call**, `scc_rt_main`'s state at the call kept
(`mNC`'s invariant at some control). -/
def rdJH (lab : Label → Int64) (R : Spike.Lib.Region) (J : FAS → Ctl → Prop) (σ : FAS) (c : Ctl) : Prop :=
  c = Spike.Lib.X64HelloRodataSrc.rdCN ∧ ∃ c', (mNC lab R J).J σ c'

/-- **The setup's call of `rodata` and its first steps** from `mNC`'s invariant, whose controls are the setup
start in `env` (`hJ`, `hu`): `rdJH` under `HelloRdCf.frH env` (`HelloRdCf.setup_call_run`). -/
theorem rdJH_run {lab : Label → Int64} {R : Spike.Lib.Region} {J : FAS → Ctl → Prop} {env : TermRun.Env}
    (hJ : ∀ σ c, J σ c → c = ⟨Scc.Sem.SrcSem.setupTerm, env, none⟩)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, [])) :
    ∀ σ c, (mNC lab R J).J σ c → ∃ c', FrameRun Spike.Lib.X64HelloSrc.helloSrc (c, [])
      (c', [Spike.Lib.X64HelloRdCf.frH env]) ∧ rdJH lab R J σ c' := by
  intro σ c h
  obtain ⟨σe, hJe, -⟩ := id h
  refine ⟨_, ?_, rfl, c, h⟩
  rw [hJ σe c hJe]
  exact Spike.Lib.X64HelloRdCf.setup_call_run hu

/-- **`rdJH`'s states are `mNC`'s** at some control. -/
theorem rdJH_back {lab : Label → Int64} {R : Spike.Lib.Region} {J : FAS → Ctl → Prop} :
    ∀ σ c', rdJH lab R J σ c' → ∃ c, (mNC lab R J).J σ c :=
  fun _ _ h => h.2

end Spike.Lib.X64.HelloPh.StartWcS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.StartWcS.xa_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS.xa_post

/-- info: 'Spike.Lib.X64.HelloPh.StartWcS.rdJH_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS.rdJH_run

/-- info: 'Spike.Lib.X64.HelloPh.StartWcS.rdJH_back' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartWcS.rdJH_back
