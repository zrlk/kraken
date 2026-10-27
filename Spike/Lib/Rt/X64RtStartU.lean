/-
**`scc_rt_start`'s states inside `W` on x86-64, for any placed output**
(`startAllUW_gen`): the obligations `StartAllUW` (`Spike/Lib/Rt/X64Segs.lean`)
of `scc_rt_start` at the record `RuntimeLayout.ofPlaceOK h i` of an output
passing `placeOK`, at any write tail `Dt`: up to `.x0` (`St0W`: the entry's
four nodes, the call block, `scc_rt_alloc_tcb` by `tcbW_gen`), from `.x0` to
the switch (`X0W`: the block, `scc_rt_thread_init` by `tiW_gen`, the block
after it, `arch_prctl`'s `syscall` and the block before the switch), and
from the switch on as given (`SwUW`). The twin of
`Spike/Lib/Rt/A64RtStartU.lean`.

- **The code**: the placed program's checks (`rtCodeIn_of_ok`): `startIn`,
  `startCallIn`, `startCall2In`, `startTailIn` and the callees'.
- **The phase facts**: `startPhTab`'s rows (`startFact_ofPlaceOK`), and the
  callees' records (`tcbPh_ofPlaceOK`, `tiPh_ofPlaceOK`, `takePh_ofPlaceOK`);
  the nodes before `.x1` are in phase `13` or `12`, before the take.
- **The words**: the record's, mapped (`words_mapped`) and unmapped under the
  frame condition (`rtF`); the TCB's owned at no phase (`tcbSep`); `.rodata`
  off the pool (`rodata_stackPool_disjoint_ofPlaceOK`), the take's premise,
  discharged here.
- **The stack range**: off the region (`hout`), so kept by the writes of the
  region and of its two callees' (`stackM_stable`, `out_callee`).
- **The write tail**: the generic lemmas give `SFacts` at the default write
  tail (no `write` before the switch); any `Dt` follows (`SFacts.dt_mono`,
  lifted through the obligations by `blkW_wmono` … `tiW_wmono`).
- **Unlike AArch64**: `scc_rt_start` runs in `_start`'s call's callee region,
  so the region holds the return address above its frame (`8 ≤ R.hi`), and
  every callee's region holds its own (`R.callee (-48 - 0) lo' 8`); no
  16-alignment.
- **At any tail** (`startTiAtW_gen`): the `scc_rt_thread_init` step without
  the bare tail, at its return point `tiOf o.place.tail` (`TiWAt`), from
  `rtCodeTi_of_placeOKAt`, `tiPhAt_ofPlaceOK` and `takePhAt_ofPlaceOK`; and
  from `.x0` to the switch (`x0WAt_gen`: `X0WAt`, `X0W` with `TiWAt`; at a
  bare tail `X0W` by `X0WAt.toX0W`, `x0W_of_bare`); up to `.x0`
  (`st0W_gen`); whole (`startAllUWAt_gen`: `StartAllUWAt`, the switch's part
  `SwUW` as given, which does not depend on the tail; at a bare tail
  `StartAllUW` by `StartAllUWAt.toStartAllUW`, `startAllUW_of_bare`).
- **Oracle**: at `ret0`'s placed record (`Spike/Test/X64RtStartU.lean`).
-/
import Spike.Lib.Rt.X64RtPhRec
import Spike.Lib.Rt.X64EntryOfPlaceOK
import Spike.Lib.Rt.X64StartArith

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA
  St0W X0W x0L x1L startCall startCall2 startFs startSw startCall_ok startCall2_ok startFs_ok startSw_ok
  startCallIn startCall2In startTailIn stackM_stable)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

namespace StartU

/-! ## A larger `W` -/

section WMono

variable {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F M : MachineData → Prop}

/-- A block obligation in a larger `W`. -/
theorem blkW_wmono (hW : ∀ s c, W s c → W' s c) {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW W K exe endPc R F n blk) : BlkW W' K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJ k hk m hA' hD =>
    have h' := h s σ c he hn hd hpc hA hF hJ k hk m hA' hD
    ⟨hW _ _ h'.1, h'.2⟩

/-- A node obligation in a larger `W`. -/
theorem nodeW_wmono (hW : ∀ s c, W s c → W' s c) {n : ND} (h : NodeW W K exe endPc R F n) :
    NodeW W' K exe endPc R F n :=
  fun s c hA => ⟨hW _ _ (h s c hA).1, (h s c hA).2⟩

/-- `scc_rt_alloc_tcb`'s obligations in a larger `W`. -/
theorem tcbW_wmono (hW : ∀ s c, W s c → W' s c) {q : TcbG} {i : TN} (h : TcbW W K exe endPc R F q i) :
    TcbW W' K exe endPc R F q i := by
  cases i <;> dsimp only [TcbW] at h ⊢ <;> first | exact blkW_wmono hW h | exact nodeW_wmono hW h

/-- `scc_rt_stack_take`'s obligations in a larger `W`. -/
theorem takeW_wmono (hW : ∀ s c, W s c → W' s c) {q : TakeG} {i : TK} (h : TakeW W K exe endPc R F M q i) :
    TakeW W' K exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h ⊢ <;>
    first
    | exact blkW_wmono hW h
    | exact nodeW_wmono hW h
    | exact fun s c hA => hW _ _ (h s c hA)

/-- `scc_rt_thread_init`'s obligations in a larger `W`. -/
theorem tiW_wmono (hW : ∀ s c, W s c → W' s c) {q : TiG} {i : TI} (h : TiW W K exe endPc R F M q i) :
    TiW W' K exe endPc R F M q i := by
  cases i <;> dsimp only [TiW] at h ⊢ <;>
    first
    | exact blkW_wmono hW h
    | exact nodeW_wmono hW h
    | exact fun g hg j => takeW_wmono hW (h g hg j)

/-- `scc_rt_thread_init`'s obligations at the return point `x` in a larger `W`. -/
theorem tiWAt_wmono (hW : ∀ s c, W s c → W' s c) {q : TiG} {x : Label} {i : TI}
    (h : TiWAt W K exe endPc R F M q x i) : TiWAt W' K exe endPc R F M q x i := by
  cases i <;> dsimp only [TiWAt] at h ⊢ <;>
    first
    | exact blkW_wmono hW h
    | exact nodeW_wmono hW h
    | exact fun g hg j => takeW_wmono hW (h g hg j)

end WMono

/-! ## `scc_rt_start`'s facts -/

theorem xStart0_noRet : noRetBlk xStart0 = true := by rfl
theorem xStartArgs_noRet : noRetBlk xStartArgs = true := by rfl
theorem startCall_noRet : noRetBlk startCall = true := by rfl
theorem startCall2_noRet : noRetBlk startCall2 = true := by rfl
theorem startFs_noRet : noRetBlk startFs = true := by rfl
theorem startSw_noRet : noRetBlk startSw = true := by rfl

/-- **A pc in a phase with bit 3 set** (before the take): no take there. -/
theorem noTk_of_ph {L : RuntimeLayout} {p : Int64} {v : Nat} (hp : PhRec.ph L p.toBitVec.toNat = v)
    (hv : v / 8 % 2 = 1) : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ PhRec.Tk L s := by
  intro s hs hT
  unfold PhRec.Tk at hT
  rw [hs, hp] at hT
  omega

/-- The system call's pc. -/
theorem startE41 (lab : Label → Int64) : lab startE + 7 + 34 = lab startE + Int64.ofNat 41 := by
  rw [Int64.add_assoc]; rfl

/-- **The first TCB's six fields** are words of the TCB. -/
theorem tcb_fld {L : RuntimeLayout} {a : BitVec 64} (ha : a ∈ Ti.tiAddrs (pinA L.lab + 0#64 + 8#64)) :
    ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j) := by
  rw [show pinA L.lab = L.pinA from L.lab_pin, BitVec.add_zero] at ha
  simp only [Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨2, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨3, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨4, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨5, by decide, by rw [BitVec.add_assoc]; rfl⟩
  · exact ⟨6, by decide, by rw [BitVec.add_assoc]; rfl⟩

end StartU

/-! ## From `.x0` to the switch at any return point -/

/-- **`X0W` at the return point `x` inside `scc_rt_thread_init`**: as `X0W`,
with `scc_rt_thread_init`'s obligations `TiWAt … x` (`X0W`'s at `.x7`,
`X0WAt.toX0W`). -/
structure X0WAt (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Range) (n0 k0 : BitVec 64) (c0 : Ctl) (x : Label) : Prop where
  b0 : BlkW W K exe endPc R F (Flow.Ret0.startN2R (_root_.Executable.labels exe).label n0 c0) startCall2
  ti : ∀ g, g.ra = ((_root_.Executable.labels exe).label x1L).toBitVec → ∀ i,
    TiWAt W K exe endPc (R.callee (-48 - 0) (-248) 8) F (StackM rS)
    ⟨g, pinA (_root_.Executable.labels exe).label + n0 + 8#64, k0, c0⟩ x i
  fs : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN3 (_root_.Executable.labels exe).label n0 k0 c0) startFs
  sys : NodeW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN4 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0)
  sw : BlkW W K exe endPc R (fun m => F m ∧ StackM rS m)
    (Flow.Ret0.startN5 (_root_.Executable.labels exe).label (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0) startSw

section X0WAt

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl}

/-- `X0WAt` at `.x7` is `X0W`. -/
theorem X0WAt.toX0W (h : X0WAt W K exe endPc R F rS n0 k0 c0 Code.Ti.x7L) : X0W W K exe endPc R F rS n0 k0 c0 :=
  ⟨h.b0, fun g hg i => tiWAt_x7 (W := W) i ▸ h.ti g hg i, h.fs, h.sys, h.sw⟩

/-- `X0W` is `X0WAt` at `.x7`. -/
theorem _root_.Spike.Lib.X64.Flow.Ret0.X0W.toAt (h : X0W W K exe endPc R F rS n0 k0 c0) :
    X0WAt W K exe endPc R F rS n0 k0 c0 Code.Ti.x7L :=
  ⟨h.b0, fun g hg i => (tiWAt_x7 (W := W) i).symm ▸ h.ti g hg i, h.fs, h.sys, h.sw⟩

theorem x0WAt_x7_iff :
    X0WAt W K exe endPc R F rS n0 k0 c0 Code.Ti.x7L ↔ X0W W K exe endPc R F rS n0 k0 c0 :=
  ⟨X0WAt.toX0W, X0W.toAt⟩

/-- **`StartAllUW` at the return point `x` inside `scc_rt_thread_init`**: as
`StartAllUW`, from `.x0` to the switch by `X0WAt … x` (`StartAllUW`'s at
`.x7`, `StartAllUWAt.toStartAllUW`); the switch's part `SwUW` does not
depend on `x`. -/
structure StartAllUWAt (W : Frag isa) (K : State → State → Prop) (p : Prog)
    (lbl : Lbl) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (rS : Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) (x : Label) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0WAt W K exe endPc R F rS n0 k0 c0 x
  s3 : SwUW W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post

section StartAllUWAt

variable {p : Prog} {lbl : Lbl} {ms : MemSide isa} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
  {Post : Ctl → BitVec 64 → Prop}

/-- `StartAllUWAt` at `.x7` is `StartAllUW`. -/
theorem StartAllUWAt.toStartAllUW
    (h : StartAllUWAt W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post Code.Ti.x7L) :
    StartAllUW W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post :=
  ⟨h.s1, h.s2.toX0W, h.s3⟩

/-- `StartAllUW` is `StartAllUWAt` at `.x7`. -/
theorem StartAllUW.toAt (h : StartAllUW W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post) :
    StartAllUWAt W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post Code.Ti.x7L :=
  ⟨h.s1, h.s2.toAt, h.s3⟩

theorem startAllUWAt_x7_iff :
    StartAllUWAt W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post Code.Ti.x7L ↔
      StartAllUW W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post :=
  ⟨StartAllUWAt.toStartAllUW, StartAllUW.toAt⟩

end StartAllUWAt

end X0WAt

/-! ## The obligations -/

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option maxHeartbeats 1600000 in
open StartU PhRecOf PhOfTab in
/-- **`scc_rt_start`'s states are inside `SFacts … Dt`** at the record of an
output passing `placeOK` (`h`, at the immediates `i`) with a bare tail
(`hs`), at any write tail
`Dt`, in any region holding its frame and its callees' below and the return
address above (`hR` … `hhi`), with the source control `c0` (`hC0`, its
facts), the frame condition giving the runtime's words unloaded (`hFr`), the
first TCB (`hn0`) and the first stack `rS` (`hrS`) in the pool (`hsub`) off
the region (`hout`), and the switch's and `scc_rt_main`'s obligations
(`hs3`). -/
theorem startAllUW_gen
    {p : Prog} {lbl : Lbl} {ms : MemSide isa} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop} (hs : o.place.tail = .bare)
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hs3 : SwUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F ms rS n0 k0 c0 L mc D ZU Post := by
  subst hn0
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hW : ∀ s c, SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c →
      SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hpn : pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  have hlk : lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hfr : freeNA (Ly).lab = (Ly).freeNA := (Ly).lab_freeN
  have hnx : nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  have h0 : ∃ j < 7, (Ly).pinA + 0#64 = (Ly).pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hfit := fitS_of_sub (Ly) hsub
  have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have ho1 := Flow.Ret0.Inst.out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide)
    (by omega) (by omega) hout
  have ho2 := Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8)
    (by show (-248 : Int) ≤ _; omega) (by decide) (by show (-48 - 0 : Int) < 8; omega)
    (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
  have hSM := stackM_stable hfit hout
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hrc.call
  simp only [startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have hcl2 := hrc.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, -⟩, -⟩, -⟩ := htl
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩, ⟨?_, fun g hg j => ?_, ?_, ?_, ?_⟩, hs3⟩
  · -- The frame's setup.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat_zero' _) xStart0_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 xStart0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStart0_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide)))
  · -- The handler's `lea`.
    have hs := step_of_factOk hl (hf (.step startE 0 7) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := siSig) (p := (Ly).lab startE + Int64.ofNat 0) hI cbSi rfl
      (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The arguments.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cbArgs rfl xStartArgs_ok hR
      (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 7 xStartArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStartArgs_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 7 13) (by simp [startPhTab]))) (by decide)))
  · -- `rt_sigaction`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step startE 41 2) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_syscall_pre (p := (Ly).lab startE + Int64.ofNat 41) hI cbSys rfl
      (startE41 (Ly).lab) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 41 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, Flow.Ret0.Inst.startS2_rax]; decide))
  · -- The call block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl startCall_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 43 Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 43 13) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_alloc_tcb`.
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    exact tcbW_wmono hW (tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' (by show (-184 : Int) ≤ -184; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPh_ofPlaceOK h i)
      (by rw [hpn]; exact ((Ly).words_mapped _ (Ly).pn_mem).1)
      (by rw [hpin]; exact PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact PhRec.rtF_tcb (hFr m hm) h0) j)
  · -- `.x0`'s block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc2 (ofNat_zero' _) startCall2_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x0L 0 Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall2_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph Code.Start.x0L 0 12) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_thread_init`.
    exact tiW_wmono hW (tiW_gen hI (fun _ => rfl) hrc.ti hC0 hR1 (by show (-248 : Int) ≤ -248; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPh_ofPlaceOK h i hs)
      (fun _ ha => PhRec.mapped_tcb (tcb_fld ha))
      (fun _ ha m hm => PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => PhRec.tcb_not_own (tcbSep h i) (tcb_fld ha))
      hsub (stackM_stable hfit ho1) (stackM_stable hfit ho2) hrc.take (takePh_ofPlaceOK h i hs)
      (by rw [hlk]; exact ((Ly).words_mapped _ (Ly).lock_mem).1)
      (by rw [hfr]; exact ((Ly).words_mapped _ (Ly).freeN_mem).2.1)
      (by rw [hnx]; exact ((Ly).words_mapped _ (Ly).next_mem).1)
      (fun m hm => by rw [hlk]; exact PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnx]; exact PhRec.rtF_next (hFr m hm))
      hrS (rodata_stackPool_disjoint_ofPlaceOK h i) j)
  · -- `.x1`'s block.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI tFs (ofNat_zero' _) startFs_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 0 Code.Start.startFs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startFs_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM)
  · -- `arch_prctl`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step Code.Start.x1L 18 2) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_syscall_post (p := (Ly).lab x1L + Int64.ofNat 18) hI tSys rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub (fun _ _ hJ => by rw [hJ.2.1]; decide))
  · -- The block before the switch.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI tSw rfl startSw_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 20 Code.Start.startSw none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startSw_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM)

set_option maxHeartbeats 1600000 in
open StartU PhRecOf in
/-- **`scc_rt_thread_init`'s states (and its take's) are inside `SFacts … Dt`
at any tail**: `startAllUW_gen`'s `scc_rt_thread_init` step without the bare
tail, its return point inside `scc_rt_thread_init` at `tiOf o.place.tail`
(`TiWAt`; at a bare tail this is `TiW`, by `tiWAt_x7`). The premises are
`startAllUW_gen`'s for this step. -/
theorem startTiAtW_gen
    {lbl : Lbl} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {k0 : BitVec 64}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    ∀ g, g.ra = ((Ly).lab x1L).toBitVec → ∀ j,
      TiWAt (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
        (PhRec.K (Ly) rS) (Ly).exe (Ly).endPc (R.callee (-48 - 0) (-248) 8) F (StackM rS)
        ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ (tiOf o.place.tail) j := by
  intro g hg j
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCodeTi_of_placeOKAt h
  have hW : ∀ s c, SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c →
      SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hlk : lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hfr : freeNA (Ly).lab = (Ly).freeNA := (Ly).lab_freeN
  have hnx : nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  have hfit := fitS_of_sub (Ly) hsub
  have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have ho1 := Flow.Ret0.Inst.out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide)
    (by omega) (by omega) hout
  have ho2 := Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8)
    (by show (-248 : Int) ≤ _; omega) (by decide) (by show (-48 - 0 : Int) < 8; omega)
    (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
  exact tiWAt_wmono hW (tiWAt_gen hI (fun _ => rfl) hrc.ti hC0 hR1 (by show (-248 : Int) ≤ -248; omega)
    (by show (8 : Int) ≤ 8; omega) ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPhAt_ofPlaceOK h i)
    (fun _ ha => PhRec.mapped_tcb (tcb_fld ha))
    (fun _ ha m hm => PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
    (fun _ ha => PhRec.tcb_not_own (tcbSep h i) (tcb_fld ha))
    hsub (stackM_stable hfit ho1) (stackM_stable hfit ho2) hrc.take (takePhAt_ofPlaceOK h i)
    (by rw [hlk]; exact ((Ly).words_mapped _ (Ly).lock_mem).1)
    (by rw [hfr]; exact ((Ly).words_mapped _ (Ly).freeN_mem).2.1)
    (by rw [hnx]; exact ((Ly).words_mapped _ (Ly).next_mem).1)
    (fun m hm => by rw [hlk]; exact PhRec.rtF_lock (hFr m hm))
    (fun m hm => by rw [hfr]; exact PhRec.rtF_freeN (hFr m hm))
    (fun m hm => by rw [hnx]; exact PhRec.rtF_next (hFr m hm))
    hrS (rodata_stackPool_disjoint_ofPlaceOK h i) j)

set_option maxHeartbeats 1600000 in
open StartU PhRecOf PhOfTab in
/-- **`scc_rt_start` from `.x0` to the switch at any tail** (`X0WAt` at
`tiOf o.place.tail`): `startAllUW_gen`'s `X0W` part without the bare tail,
the code from `rtCodeTi_of_placeOKAt`, the `scc_rt_thread_init` step by
`startTiAtW_gen`. At a bare tail, `X0WAt.toX0W` gives `X0W`. -/
theorem x0WAt_gen
    {lbl : Lbl} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {k0 : BitVec 64}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    X0WAt (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 (tiOf o.place.tail) := by
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCodeTi_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hW : ∀ s c, SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c →
      SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hfit := fitS_of_sub (Ly) hsub
  have hSM := stackM_stable hfit hout
  have hcl2 := hrc.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, -⟩, -⟩, -⟩ := htl
  refine ⟨?_, startTiAtW_gen h i hC0 hR hlo hhi hFr hrS hsub hout, ?_, ?_, ?_⟩
  · -- `.x0`'s block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc2 (ofNat_zero' _) startCall2_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x0L 0 Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall2_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph Code.Start.x0L 0 12) (by simp [startPhTab]))) (by decide)))
  · -- `.x1`'s block.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI tFs (ofNat_zero' _) startFs_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 0 Code.Start.startFs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startFs_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM)
  · -- `arch_prctl`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step Code.Start.x1L 18 2) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_syscall_post (p := (Ly).lab x1L + Int64.ofNat 18) hI tSys rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub (fun _ _ hJ => by rw [hJ.2.1]; decide))
  · -- The block before the switch.
    exact blkW_wmono hW (blkW_post (dead := fun _ => false) (ra := 0) hI tSw rfl startSw_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 20 Code.Start.startSw none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startSw_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM)

/-- `x0WAt_gen` at a bare tail: `X0W`. -/
theorem x0W_of_bare
    {lbl : Lbl} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {k0 : BitVec 64} (hs : o.place.tail = .bare)
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    X0W (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 := by
  have h' := x0WAt_gen h i (Dt := Dt) hC0 hR hlo hhi hFr hrS hsub hout
  rw [hs] at h'
  exact h'.toX0W

set_option maxHeartbeats 1600000 in
open StartU PhRecOf PhOfTab in
/-- **`scc_rt_start` up to `.x0` at any tail** (`St0W`): `startAllUW_gen`'s
`St0W` part without the bare tail, the code from `rtCodeTi_of_placeOKAt`. -/
theorem st0W_gen
    {lbl : Lbl} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region} {F : MachineData → Prop}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m) :
    St0W (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F 0#64 c0 := by
  have hI := PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCodeTi_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hW : ∀ s c, SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c →
      SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt :=
    fun _ _ hs => hs.dt_mono fun _ h => h.elim
  have hpn : pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  have h0 : ∃ j < 7, (Ly).pinA + 0#64 = (Ly).pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hrc.call
  simp only [startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩
  · -- The frame's setup.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat_zero' _) xStart0_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 xStart0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStart0_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide)))
  · -- The handler's `lea`.
    have hs := step_of_factOk hl (hf (.step startE 0 7) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_si_pre (si := siSig) (p := (Ly).lab startE + Int64.ofNat 0) hI cbSi rfl
      (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2)
  · -- The arguments.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cbArgs rfl xStartArgs_ok hR
      (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 7 xStartArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStartArgs_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 7 13) (by simp [startPhTab]))) (by decide)))
  · -- `rt_sigaction`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step startE 41 2) (by simp [startPhTab]))
    exact nodeW_wmono hW (nodeW_syscall_pre (p := (Ly).lab startE + Int64.ofNat 41) hI cbSys rfl
      (startE41 (Ly).lab) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 41 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, Flow.Ret0.Inst.startS2_rax]; decide))
  · -- The call block.
    exact blkW_wmono hW (blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl startCall_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 43 Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_of_ph (ph_of_factOk hl (hf (.ph startE 43 13) (by simp [startPhTab]))) (by decide)))
  · -- `scc_rt_alloc_tcb`.
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    exact tcbW_wmono hW (tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' (by show (-184 : Int) ≤ -184; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPh_ofPlaceOK h i)
      (by rw [hpn]; exact ((Ly).words_mapped _ (Ly).pn_mem).1)
      (by rw [hpin]; exact PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact PhRec.rtF_tcb (hFr m hm) h0) j)

/-- **`scc_rt_start`'s states are inside `SFacts … Dt` at any tail**
(`StartAllUWAt` at `tiOf o.place.tail`): `startAllUW_gen` without the bare
tail (`st0W_gen`, `x0WAt_gen`, the switch's part `hs3` as given). At a bare
tail, `StartAllUWAt.toStartAllUW` gives `StartAllUW` (`startAllUW_of_bare`). -/
theorem startAllUWAt_gen
    {p : Prog} {lbl : Lbl} {ms : MemSide isa} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hs3 : SwUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUWAt (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F ms rS n0 k0 c0 L mc D ZU Post (tiOf o.place.tail) := by
  subst hn0
  exact ⟨st0W_gen h i hC0 hR hlo hhi hFr, x0WAt_gen h i hC0 hR hlo hhi hFr hrS hsub hout, hs3⟩

/-- `startAllUWAt_gen` at a bare tail: `StartAllUW` (`startAllUW_gen`'s
statement). -/
theorem startAllUW_of_bare
    {p : Prog} {lbl : Lbl} {ms : MemSide isa} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop} (hs : o.place.tail = .bare)
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hs3 : SwUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUW (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F ms rS n0 k0 c0 L mc D ZU Post := by
  have h' := startAllUWAt_gen h i hC0 hR hlo hhi hFr hn0 hrS hsub hout hs3
  rw [hs] at h'
  exact h'.toStartAllUW

end Start

end Spike.Lib.X64.Rt
