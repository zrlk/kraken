/-
**The caller's source placed in `scc_rt_alloc`, at any frame** (hello.w,
AArch64; the frame-generic twin of
`A64WakePlacedAlloc`): at every node of an allocator called from a function
of frame `-fr` (its region `R.callee fr (-160) 0`, the call context
`CtxG … fr Jn q`), the caller's source is placed (`PlacedSE`) as at the
call. The allocator's nodes keep the source's term and environment
(`PlacedAlloc.allocN_ctl`, `placedSE_congr`: wake's, program independent),
and a caller slot `k` at the frame's bottom or above (`fr ≤ k`; `k > 0`
allowed, a cell of the caller's caller) sits outside the callee's region,
kept (`CKept`, `DFrame`), there the call state's.

The instances are `wc_main`'s box call (frame 144, `WcCtxH`, `wARH`; the
root's `HelloRootPrem.halloc`) and `wc_rodata`'s buffer call (frame 48,
`HelloRd.RdCtx`, `Hello1.aR`; `rdPreW_WSH` premise `hpl.alloc`).
What placing the source needs from the call state is a premise (`hP`):
wake's `allocW_placed_new` is its instance at main's id in slot `-80`.

- `CtxG`: the allocator's call context at frame `fr`, call-node invariant
  `Jn` (`WcCtxH`, `RdCtx` unfold to it).
- `placeVal_slot_keptG`: a caller slot `k ≥ fr` across the call.
- `allocW_placedG`: the generic statement.
- `allocW_placed_wcH`, `allocW_placed_rdH`: at `wc_main`'s and
  `wc_rodata`'s calls.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakePlacedAlloc
import Spike.Lib.A64HelloWcPre
import Spike.Lib.A64HelloRodata

namespace Spike.Lib.A64.HelloPh.PlacedAlloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Alloc (Call AllocW N)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.WakePh.PlacedAlloc (placedSE_congr allocN_ctl)

/-- **The allocator's call context at frame `fr`** in the caller's region
`R` at the memory `m`: a caller state `mC`, `σC` at offsets `⟨fr, []⟩` at
the call node (`Jn`), entering the allocator at `q`'s entry, the caller's
cells outside the allocator's region as at the call. -/
def CtxG (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (fr : Int) (Jn : Flow.AS → Ctl → Prop)
    (q : Call) (m : MachineData) : Prop :=
  ∃ mC σC c, Flow.Abs R ⟨fr, []⟩ mC σC ∧ Jn σC c ∧ (N lab ms q .e).J (enter fr σC) c ∧ CKept R fr (-160) 0 mC m

/-- **A caller slot across the allocator's call**: below the callee's region
(`R.callee fr (-160) 0`), a cell `k ≥ fr` of the caller's frame `R` is as
at the call (`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_keptG {R : Region} {fr : Int} {o : Flow.SO} {m1 m' : MachineData} {σC : Flow.AS} {s : State}
    (hA : Flow.Abs R o m1 σC) (hK : CKept R fr (-160) 0 m1 m') (hD : Flow.DFrame (R.callee fr (-160) 0) m' s.st.1)
    (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : fr ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee fr (-160) 0).Off (k - fr) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have hf := Region.addr_toNat_of hR (k := fr) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hK k hk hc, hj, hv]

section Gen

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isaLSE2} {Jn : Flow.AS → Ctl → Prop} {q : Call} {fr k : Int}

set_option hygiene false in
/-- The allocator's frame condition at the call, frame `fr`. -/
local notation "FA" => fun m => F m ∧ Ret0.CallerCells R fr (-160) 0 m ∧
  CtxG ms (_root_.Executable.labels exe).label R fr Jn q m

set_option hygiene false in
/-- The source at the call placed, given the call state's slot `k` (at a
call-node state `σC` at control `q.c0`). -/
local notation "HP" => ∀ σC, (∃ mC, Flow.Abs R ⟨fr, []⟩ mC σC) → Jn σC q.c0 → ∀ s : State,
  placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat → PlacedSE Λ lbl s q.c0 []

/-- At a state of the allocator whose memory is outside its region as at
`m'` (a node's), with `FA m'`: the caller's source placed. -/
theorem placed_inG (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi) (hk : R.Off k)
    (hk' : fr ≤ k) (hP : HP) {m' : MachineData} (hF : FA m') {s : State}
    (hD : Flow.DFrame (R.callee fr (-160) 0) m' s.st.1) : PlacedSE Λ lbl s q.c0 [] := by
  obtain ⟨-, -, mC, σC, c, hA, hJ, ⟨rfl, -⟩, hK⟩ := hF
  exact hP σC ⟨mC, hA⟩ hJ s (placeVal_slot_keptG hA hK hD hR hlo hfr hhi hk hk')

/-- **The caller's source placed at every node of `scc_rt_alloc`**, called
at frame `fr` (the generic `hpl` of `allocW_WSH`). -/
theorem allocW_placedG (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi) (hk : R.Off k)
    (hk' : fr ≤ k) (hP : HP) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee fr (-160) 0) FA := by
  have hB : ∀ i blk, BlkW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee fr (-160) 0) FA
      (N (_root_.Executable.labels exe).label ms q i) blk := by
    intro i blk s σ c _ _ _ _ _ hF hj _ _ m _ hD
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (placed_inG (s := { s with st := (m, _) }) hR hlo hfr hhi hk hk' hP hF hD),
      fun _ h => h⟩
  have hN : ∀ i, NodeW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee fr (-160) 0) FA
      (N (_root_.Executable.labels exe).label ms q i) := by
    rintro i s c ⟨-, -, -, -, σ, -, hF, hj⟩
    obtain ⟨ht, he⟩ := allocN_ctl i σ c hj
    exact ⟨placedSE_congr ht he (placed_inG hR hlo hfr hhi hk hk' hP hF (Flow.DFrame.refl _ _)), fun _ h => h⟩
  exact ⟨hB _ _, hB _ _, hB _ _, hN _, hN _, hB _ _, hN _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hB _ _, hN _,
    hN _, hB _ _, hN _, hB _ _, hN _⟩

end Gen

section Inst

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isaLSE2} {J0 J1 : Flow.AS → Ctl → Prop} {q : Call} {k : Int}

/-- **`wc_main`'s box call** (frame 144, `WcCtxH`, `wARH`; the root's
`HelloRootPrem.halloc` at `q`): `allocW_placedG` at `fr = -144`. -/
theorem allocW_placed_wcH (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) (hk : R.Off k) (hk' : -144 ≤ k)
    (hP : ∀ σC, (∃ mC, Flow.Abs R ⟨-144, []⟩ mC σC) →
      (HelloWc.wNH (_root_.Executable.labels exe).label J0 J1 .call).J σC q.c0 →
      ∀ s : State, placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat →
        PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (HelloWc.wARH R)
      (fun m => F m ∧ Ret0.CallerCells R (-144) (-160) 0 m ∧
        HelloWc.WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m) :=
  allocW_placedG hR hlo (by decide) hhi hk hk' hP

/-- **`wc_rodata`'s buffer call** (frame 48, `HelloRd.RdCtx`, `Hello1.aR`;
`rdPreW_WSH` premise `hpl.alloc` at `q`): `allocW_placedG` at
`fr = -48`. -/
theorem allocW_placed_rdH (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hk : R.Off k) (hk' : -48 ≤ k)
    (hP : ∀ σC, (∃ mC, Flow.Abs R ⟨-48, []⟩ mC σC) →
      (HelloRd.rN (_root_.Executable.labels exe).label J0 J1 .call).J σC q.c0 →
      ∀ s : State, placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat →
        PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (Hello1.aR R)
      (fun m => F m ∧ Ret0.CallerCells R (-48) (-160) 0 m ∧
        HelloRd.RdCtx ms (_root_.Executable.labels exe).label R J0 J1 q m) :=
  allocW_placedG hR hlo (by decide) hhi hk hk' hP

end Inst

end Spike.Lib.A64.HelloPh.PlacedAlloc

/-- info: 'Spike.Lib.A64.HelloPh.PlacedAlloc.placeVal_slot_keptG' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedAlloc.placeVal_slot_keptG

/-- info: 'Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placedG' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placedG

/-- info: 'Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placed_wcH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placed_wcH

/-- info: 'Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placed_rdH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placed_rdH
