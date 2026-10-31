/-
**The counter row of wake's start segment** (AArch64; `OpenW.hctr0`): the
context `Ctx` of `W0W` is the box's two arena writes, `scc_rt_alloc`'s
counter add for a box call the start makes (`CtrAt`, the calls `Gc`) or the box store (`St`, writing no
counter word). At the counter add the consumer's `CtrRow` holds at the
start's memory side, landing in `I2`'s `inv0` disjunct, given that the
allocator's next node `n4` (the old count held) is in `inv0` (`hland`, from
the start segment's tail).

- `ctrRow_ndS`: `ctrRow_nd` at any allocation site (`AllocSite`, as
  `ctr_ndWS`).
- `ctrRow_allocS_n4`: at `scc_rt_alloc`'s counter add for a call at its
  site premises (`Call.OKS`), landing exactly at `n4`.
- `CtrOk`: the counter add's call facts (a box call, a stable frame
  condition with the counter unmapped).
- `CtrAt`, `CtxW`: the context.
- `ctrRow_xa`: `CtrRow` reads no `xa`.
- `hctr0_of`: `OpenW.hctr0`'s shape.
-/
import Spike.Lib.A64CtrRow
import Spike.Lib.A64AllocBox
import Spike.Lib.A64SegInstA
import Spike.Lib.FrameNew

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64ConsumerA (CtrRow)

variable {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`CtrRow` at a state of the counter's add node** at any allocation
site (`ctrRow_nd` with the site `AllocSite ms.newOk`, as `ctr_ndWS`). -/
theorem ctrRow_ndS {n : ND} {k : RmwKind} {rs rt b : XReg} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldopDir .ADD k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr ∧ ms.rt (BitVec.ofNat 64 ms.ctr).toNat ∧
      ms.mp (ctrLoc ms) true ∧ Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none ∧
      ∃ (x : String) (τ : Ty) (e : Expr) (nn : Nat), AllocSite ms.newOk c x nn τ e ∧ c.hold = none ∧
        σ.regs.getRegOrZr (.low (.reg rs) .W64) = BitVec.ofNat 64 (ms.units nn τ) ∧
        ∀ old : Val, ms.G (ctrLoc ms) old → (old.setWidth 64).toNat ≤ ms.cells → ms.lo (old.setWidth 64).toNat →
          ms.G (ctrLoc ms) ((old.setWidth 64 + BitVec.ofNat 64 (ms.units nn τ)).setWidth 128) ∧
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt (old.setWidth 64) σ⟩
            (holdCtr ms c (old.setWidth 64)))
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) :
    CtrRow ms (Next exe endPc R F N E) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (ldopDir .ADD k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hrt, hmp, hdm, x, τ, e, nn, hs, hh, hrs, hX⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = BitVec.ofNat 64 ms.ctr := by rw [hA.regs]; exact hb
  have hex := exec_ldop hc (by rw [hb']; exact hdm)
  rw [hb', access_agrees (agrees_of_decls hdc _ _)] at hex
  refine ⟨k, _, _, x, τ, e, nn, hex, hrt, hmp, hs, hh, fun old => ?_, fun old hG _ hle hlo => ?_⟩
  · rw [hA.regs, hrs, add_apply]
  obtain ⟨hG', hL⟩ := hX old hG hle hlo
  refine ⟨hG', ?_⟩
  have hA' : Abs R (n.o.kill rt)
      { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) }
      (ldStep rt (old.setWidth 64) σ) := by
    refine ⟨by simp only [ldStep, hA.regs], hA.status, ?_, hA.slot⟩
    exact hA.so.killZ (.low (.reg rt) .W64) (old.setWidth 64)
  have hD' : F { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } :=
    hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg rt) .W64) (old.setWidth 64) },
        n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨y, hy.at he hn hdc hA' hD'⟩

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.WakeCtr

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks)
open Scc.Sem.A64 (abi)
open Spike.Lib (Region FrameRun MemSide Arena FragS)
open Spike.Lib.A64ConsumerA (CtrRow PendA WrAt msOfA I2)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Flow (At Next FStable)
open Spike.Lib.A64.Alloc (Call Code N)

variable {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {q : Call}

/-- **`CtrRow` at `scc_rt_alloc`'s counter add landing at `n4`** for a call
at its site premises (`hq`: a buffer or a box), the counter unmapped under
the stable frame condition (`hF`, `hmem`). -/
theorem ctrRow_allocS_n4 (hF : FStable R F) (hq : q.OKS ms (_root_.Executable.labels exe).label)
    (hcode : Code ms q exe endPc) (hmem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none)
    {s : State} {c : Ctl} (hAt : At exe endPc R F (N (_root_.Executable.labels exe).label ms q .rmw) s c) :
    CtrRow ms (Next exe endPc R F (fun _ : Unit => N (_root_.Executable.labels exe).label ms q .n4)
      (fun x : Empty => x.elim)) s c :=
  Spike.Lib.A64.Flow.ctrRow_ndS hF (fun s he hn => hcode.rmw s he hn) (fun m σ c hA hD hJ => by
    obtain ⟨⟨rfl, hF, hn28⟩, h10, h9⟩ := hJ
    exact ⟨h10, hq.rt, hq.mp, hmem _ hD, q.x, q.τ, q.e, q.n, hq.site, hq.hold,
      by rw [Spike.Lib.A64.Alloc.getRegOrZr_x]; exact h9, fun old hG hle hlo =>
        ⟨hq.grow old hG hle, .inl ⟨(), rfl, rfl, _, rfl, hle, hF, hn28, rfl, hlo⟩⟩⟩) hAt

/-- **The counter add's call facts**: a box call (`Call.OKB`), the frame
condition stable in the allocator's region with the counter unmapped. -/
structure CtrOk (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop where
  okb : q.OKB ms lab
  fst : FStable R F
  mem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none

/-- **The counter add's states** of the start (no frames): `scc_rt_alloc`'s
`rmw` node for a call `Gc` admits (the start's own calls) with `CtrOk`, at a
memory side `ms0` that is `ref` but for `xa`. -/
def CtrAt (ref : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call),
    ms0 = { ref with xa := ms0.xa } ∧ Gc ms0 R F q ∧ CtrOk ms0 (_root_.Executable.labels exe).label R F q ∧
    At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c

/-- **`W0W`'s context**: the counter add (`CtrAt`) or the box's store `St`. -/
def CtxW (ref : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop) (St : FragS isaLSE2) : FragS isaLSE2 :=
  fun s c fs => CtrAt ref exe endPc Gc s c fs ∨ St s c fs

/-- **`CtrRow` reads no `xa`.** -/
theorem ctrRow_xa {ms ms' : MemSide isaLSE2} {X : Spike.Lib.Frag isaLSE2} {s : State} {c : Ctl}
    (h : CtrRow ms X s c) (he : ms' = { ms with xa := ms'.xa }) : CtrRow ms' X s c := by
  have h' : CtrRow { ms with xa := ms'.xa } X s c := h
  rw [← he] at h'
  exact h'

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Spike.Lib.A64ConsumerS.OwnS} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
  {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {p : Prog} {St : FragS isaLSE2}
  {Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop}

/-- **`OpenW.hctr0` at `Ctx := CtxW`** (the reference side `msOfA` at no
fragment, at `L0`, `ls0`): the store `St` writes no counter (`hSt`); at the
counter add the frame run stays put (a box `new`) and `ctrRow_allocS_n4`
gives the row, its landing at `n4` in `inv0` (`hland`, for the calls `Gc`
admits), so in `I2`'s first disjunct. `inv0` itself is not used. -/
theorem hctr0_of (hcode : ∀ ms0 q, Code ms0 q exe endPc)
    (hSt : ∀ s c fs, St s c fs → ¬ WrAt s ar.ctrLoc)
    (hland : ∀ (ms0 : MemSide isaLSE2) R F q,
      ms0 = { msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 [] with xa := ms0.xa } → Gc ms0 R F q →
      CtrOk ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .n4) s c → inv0 s c []) :
    ∀ s c fs, inv0 s c fs →
      CtxW (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) L0 ls0 []) exe endPc Gc St s c fs →
      WrAt s ar.ctrLoc → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 fs')
        (fun s' c'' => PendA p (I2 ar L0 ls0 inv0 inv1) L0 ls0 s' c'' fs') s c' := by
  intro s c fs _ hC hW c' fs' hr _
  obtain ⟨rfl, ms0, R, F, q, hms, hGc, hok, hAt⟩ := hC.resolve_right fun hS => hSt s c fs hS hW
  have hc : c = q.c0 := by obtain ⟨-, -, -, -, σ, -, -, ⟨h, -⟩, -⟩ := hAt; exact h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.FrameNew.FrameRun.eq_of_new hr (by rw [hc]; exact hok.okb.term.choose_spec))
  have hrow := ctrRow_allocS_n4 hok.fst hok.okb.toS (hcode ms0 q) hok.mem hAt
  refine ctrRow_xa ?_ (show _ = { ms0 with xa := _ } by rw [hms]; rfl)
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => ?_, _, _, .refl _, .inl ⟨rfl, rfl, ?_⟩⟩
  · revert h; rw [hc]; intro h
    have h2 : q.c0.term = .ret a := h
    rw [hok.okb.term.choose_spec] at h2
    cases h2
  · rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
    · exact hland ms0 R F q hms hGc hok _ _ hj
    · exact y.elim

end Spike.Lib.A64.WakeCtr

/-- info: 'Spike.Lib.A64.Flow.ctrRow_ndS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.ctrRow_ndS

/-- info: 'Spike.Lib.A64.WakeCtr.ctrRow_allocS_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.ctrRow_allocS_n4

/-- info: 'Spike.Lib.A64.WakeCtr.ctrRow_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.ctrRow_xa

/-- info: 'Spike.Lib.A64.WakeCtr.hctr0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.hctr0_of
